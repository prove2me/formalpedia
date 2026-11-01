-- Prove2me | Definitions.Def_HousingImprove_ttcProg
-- name    : HousingImprove_ttcProg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:58.979633+00:00
-- url     : https://prove2.me/theorems/4df2d610-b686-4046-b8df-2ac25d21c70c
-- title:
--   TTC for partial-order preferences, as a charged program
-- statement:
--   The program `ttcProg` implements the variant of Top Trading Cycles of Appendix A for a housing market presented by its Hasse diagrams, run on a set $W$ of agents (the submarket $H_W$). For each agent $a\in W$ it maintains the set $U(a)$ of **undominated choices**: the houses $b\in A(a)\cap W$ still in the market with no house of the market above $b$ in $\prec_a$. It grows a path along arcs $(a,b)$ with $b\in U(a)$ until the path closes a cycle; the agents of the cycle trade along it and leave the market, and the path continues from its last remaining agent.
--
--   The sets $U(a)$ are maintained as on p.30: when an agent leaves the market, its occurrences as an undominated choice are replaced by the houses just below it that have no house of the market above them, found by counting, for each vertex of $H_a$, the out-neighbours that are not yet exhausted.
--
--   **Formalization Note** The diagrams are first renumbered as flat node arrays (`preprocess`); the result is read off as a function `Fin n → Fin n` whose values outside $W$ carry no meaning. Where the page adds "those in-neighbors of $a$ in $H_b$ which have no out-neighbor still present in the market", the program also passes through in-neighbours that have already left the market (a vertex is exhausted once it and everything above it have left), which the page's sentence omits.
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, Appendix A, pp.29–30 (TTC for partial order preferences, implementation in linear time)

import Mathlib
import Definitions.Def_HousingImprove_HassePres
import Definitions.Def_HousingImprove_Prog

namespace HousingImprove

/-- The Hasse diagrams `H_a` stored with **flat node numbers**: the vertices of `H_a` are the nodes
`off[a], …, off[a+1] − 1`; node `v` is the house `gid[v]` in the diagram of agent `own[v]`, with
out-neighbours `upF[v]` and in-neighbours `dnF[v]` (nodes of the same diagram). `M = Σ_a |A(a)|`. -/
structure Flat where
  /-- The number of nodes, `Σ_a |A(a)|`. -/
  M : ℕ
  /-- `off[a]` is the first node of `H_a`; `off[n] = M`. -/
  off : Array ℕ
  /-- The house (agent) at a node. -/
  gid : Array ℕ
  /-- The agent whose diagram a node belongs to. -/
  own : Array ℕ
  /-- Out-neighbours of a node. -/
  upF : Array (Array ℕ)
  /-- In-neighbours of a node. -/
  dnF : Array (Array ℕ)

/-- The number of cells of a list, counted by one pass (cost `|l|`). -/
def lengthP {α : Type} (l : List α) : Prog ℕ :=
  forL l 0 fun k _ => opn 1 (k + 1)

/-- Read the input once and build the flat representation (cost `O(n + |H|)`). A scratch array
`pos` of `n` cells maps the houses of `A(a)` to their local positions while `H_a` is processed;
the `up` lists are then translated into node numbers. -/
def preprocess {n : ℕ} (I : HassePres n) : Prog Flat := do
  let off ← alloc (n + 1) 0
  let (off, M) ← forL (List.finRange n) (off, 0) fun (off, m) a => do
    let len ← lengthP (I.verts a)
    let m' ← opn 1 (m + len)
    let off ← wr off (a.val + 1) m'
    pure (off, m')
  let pos ← alloc n 0
  let gid ← alloc M 0
  let own ← alloc M 0
  let upF ← alloc M (#[] : Array ℕ)
  let dnF ← alloc M (#[] : Array ℕ)
  let (_, gid, own, upF, dnF) ← forL (List.finRange n) (pos, gid, own, upF, dnF)
    fun (pos, gid, own, upF, dnF) a => do
      let o ← rd off a.val 0
      let (pos, gid, own, _) ← forL (I.verts a) (pos, gid, own, 0) fun (pos, gid, own, i) b => do
        let pos ← wr pos b.val i
        let gid ← wr gid (o + i) b.val
        let own ← wr own (o + i) a.val
        opn 1 (pos, gid, own, i + 1)
      let (upF, dnF, _) ← forL (I.verts a) (upF, dnF, 0) fun (upF, dnF, i) b => do
        let (upF, dnF) ← forL (I.up a b) (upF, dnF) fun (upF, dnF) c => do
          let j ← rd pos c.val 0
          let upF ← pushAt upF (o + i) (o + j)
          let dnF ← pushAt dnF (o + j) (o + i)
          pure (upF, dnF)
        opn 1 (upF, dnF, i + 1)
      pure (pos, gid, own, upF, dnF)
  pure { M := M, off := off, gid := gid, own := own, upF := upF, dnF := dnF }

/-- The state of the TTC variant of Appendix A (p.30). -/
structure TTCSt where
  /-- Agents still in the market. -/
  present : Array Bool
  /-- For each node: the number of its out-neighbours that are not yet exhausted (a node is
  exhausted when its house and every house above it in the diagram have left the market). -/
  cnt : Array ℕ
  /-- `Ust[a]`: a stack holding the undominated choices `U(a)` of agent `a` (plus stale entries,
  popped lazily). -/
  Ust : Array (Array ℕ)
  /-- `occ[b]`: the nodes with house `b` that were put on some `U`-stack ("a list of all occurrences
  of `b` as someone's undominated choice"). -/
  occ : Array (Array ℕ)
  /-- Nodes whose count reached `0` and that still have to be settled. -/
  work : Array ℕ

/-- Settle every node on the worklist: a node whose count is `0` goes on its agent's `U`-stack if its
house is present, and is otherwise exhausted, decrementing the counts of its in-neighbours. -/
def ttcSettle (F : Flat) (fuel : ℕ) (st : TTCSt) : Prog TTCSt :=
  whileF fuel st fun st => do
    let (top, work) ← pop st.work
    match top with
    | none => pure none
    | some v => do
      let h ← rd F.gid v 0
      let pr ← rd st.present h false
      if pr then
        let a ← rd F.own v 0
        let Ust ← pushAt st.Ust a v
        let occ ← pushAt st.occ h v
        pure (some { st with work := work, Ust := Ust, occ := occ })
      else
        let ins ← rd F.dnF v #[]
        let (cnt, work) ← forL ins.toList (st.cnt, work) fun (cnt, work) w => do
          let c ← rd cnt w 0
          let cnt ← wr cnt w (c - 1)
          if c - 1 = 0 then
            let work ← push work w
            pure (cnt, work)
          else opn 1 (cnt, work)
        pure (some { st with cnt := cnt, work := work })

/-- Remove agent `b` from the market: every node with house `b` on a `U`-stack of a present agent
is exhausted ("Whenever an agent `a` is deleted from the market, we find all agents `b` such that
`a ∈ U(b)`, and we update `U(b)`", p.30), and the worklist is settled. -/
def ttcRemove (F : Flat) (fuel : ℕ) (st : TTCSt) (b : ℕ) : Prog TTCSt := do
  let present ← wr st.present b false
  let os ← rd st.occ b #[]
  let (cnt, work) ← forL os.toList (st.cnt, st.work) fun (cnt, work) v => do
    let a ← rd F.own v 0
    let pa ← rd present a false
    if pa then
      let ins ← rd F.dnF v #[]
      forL ins.toList (cnt, work) fun (cnt, work) w => do
        let c ← rd cnt w 0
        let cnt ← wr cnt w (c - 1)
        if c - 1 = 0 then
          let work ← push work w
          pure (cnt, work)
        else opn 1 (cnt, work)
    else opn 1 (cnt, work)
  ttcSettle F fuel { st with present := present, cnt := cnt, work := work }

/-- The path-growing state of TTC: the current path, membership in it, the successor of each agent
(its house in the computed allocation once its cycle is recorded), and a scan pointer. -/
structure TTCPath where
  /-- The `TTCSt` data structures. -/
  st : TTCSt
  /-- The current path, as a stack of agents. -/
  path : Array ℕ
  /-- Membership in the current path. -/
  onPath : Array Bool
  /-- `nxt[a]`: the agent `a` points to (its allocated house once its cycle is removed). -/
  nxt : Array ℕ
  /-- The next agent to try as the start of a new path. -/
  ptr : ℕ

/-- **TTC for partial orders** (Appendix A, pp.29–30) on the agents `a` with `inW[a] = true`, on the
flat diagrams `F` of `n` agents: maintain `U(a)` and grow a path along arcs `(a, b)` with
`b ∈ U(a)` until it closes a cycle; record the cycle, remove its agents, and continue from the last
agent of the path. Returns `nxt`, whose entry at `a ∈ W` is the house `a` obtains. -/
def ttcCore (n : ℕ) (F : Flat) (fuel : ℕ) (inW : Array Bool) : Prog (Array ℕ) := do
  let cnt ← alloc F.M 0
  let Ust ← alloc n (#[] : Array ℕ)
  let occ ← alloc n (#[] : Array ℕ)
  let st0 : TTCSt := { present := inW, cnt := cnt, Ust := Ust, occ := occ, work := #[] }
  -- initial undominated choices of every agent in `W`
  let st ← forL (List.range n) st0 fun st a => do
    let w ← rd inW a false
    if w then
      let o ← rd F.off a 0
      let o' ← rd F.off (a + 1) 0
      let st ← forL (List.range (o' - o)) st fun st i => do
        let outs ← rd F.upF (o + i) #[]
        let k ← lengthP outs.toList
        let cnt ← wr st.cnt (o + i) k
        if k = 0 then
          let work ← push st.work (o + i)
          pure { st with cnt := cnt, work := work }
        else opn 1 { st with cnt := cnt }
      ttcSettle F fuel st
    else opn 1 st
  let onPath ← alloc n false
  let nxt ← alloc n 0
  let fin ← whileF fuel ({ st := st, path := #[], onPath := onPath, nxt := nxt, ptr := 0 } : TTCPath)
    fun S => do
      match S.path.back? with
      | none => do
        -- start a new path at the next agent still in the market
        let ptr ← whileF fuel S.ptr fun ptr => do
          if ptr < n then
            let pr ← rd S.st.present ptr false
            if pr then pure none else opn 1 (some (ptr + 1))
          else opn 1 none
        if ptr < n then
          let path ← push S.path ptr
          let onPath ← wr S.onPath ptr true
          pure (some { S with path := path, onPath := onPath, ptr := ptr })
        else pure none
      | some cur => do
        tick 1
        -- the top of `U(cur)`, after popping houses that left the market
        let stk0 ← rd S.st.Ust cur #[]
        let stk ← whileF fuel stk0 fun stk => do
          match stk.back? with
          | none => opn 1 none
          | some v => do
            let h ← rd F.gid v 0
            let pr ← rd S.st.present h false
            if pr then pure none
            else
              let (_, stk) ← pop stk
              pure (some stk)
        let Ust ← wr S.st.Ust cur stk
        let S := { S with st := { S.st with Ust := Ust } }
        match stk.back? with
        | none => pure none
        | some v => do
          let next ← rd F.gid v 0
          let nxt ← wr S.nxt cur next
          let onp ← rd S.onPath next false
          if onp then
            -- a cycle: pop it from the path and remove its agents from the market
            let (path, onPath, st, _) ← whileF fuel (S.path, S.onPath, S.st, false)
              fun (path, onPath, st, done) => do
                if done then pure none
                else
                  let (top, path) ← pop path
                  match top with
                  | none => pure none
                  | some x => do
                    let onPath ← wr onPath x false
                    let st ← ttcRemove F fuel st x
                    pure (some (path, onPath, st, x = next))
            pure (some { S with path := path, onPath := onPath, st := st, nxt := nxt })
          else
            let path ← push S.path next
            let onPath ← wr S.onPath next true
            pure (some { S with path := path, onPath := onPath, nxt := nxt })
  pure fin.nxt

/-- The fuel given to every loop of the programs of this mission: an upper bound, computed from the
input size, on the number of iterations of any loop. It only guarantees termination; the cost
counts the iterations actually performed. -/
def fuelOf {n : ℕ} (I : HassePres n) : ℕ := 16 * (I.size + n + 1)

/-- Read an array of agent numbers as a function `Fin n → Fin n` (cost `n`). -/
def readOut (n : ℕ) (A : Array ℕ) : Prog (Fin n → Fin n) := do
  tick n
  pure fun a => if h : A.getD a.val 0 < n then ⟨A.getD a.val 0, h⟩ else a

/-- **TTC in linear time** (Appendix A, p.30), run on the submarket `H_W` with
`W = {a | w a = true}`, from the presentation `I` of `H`. The result is the allocation of `H_W` on
`W` (its value outside `W` carries no meaning). -/
def ttcProg {n : ℕ} (I : HassePres n) (w : Fin n → Bool) : Prog (Fin n → Fin n) := do
  let F ← preprocess I
  let inW ← alloc n false
  let inW ← forL (List.finRange n) inW fun inW a => wr inW a.val (w a)
  let nxt ← ttcCore n F (fuelOf I) inW
  readOut n nxt

end HousingImprove


