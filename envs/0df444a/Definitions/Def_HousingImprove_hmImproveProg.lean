-- Prove2me | Definitions.Def_HousingImprove_hmImproveProg
-- name    : HousingImprove_hmImproveProg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:29:23.555803+00:00
-- url     : https://prove2.me/theorems/e2b3924c-e272-4cdf-a531-e7a88a72a2be
-- title:
--   Algorithm HM-Improve, as a charged program
-- statement:
--   The program `hmImproveProg I I' X p` implements Algorithm HM-Improve. Given presentations $I$ of $H$ and $I'$ of a $p$-improvement $H'$, a core allocation $X$ of $H$ and the agent $p$, it
--
--   1. decides for each agent $a$ whether $a\in Q$, i.e. $a\neq p$ and $X(a)\prec'_a p$, and builds the **envy region** of $a$: the houses strictly above $Y(a)$ in $\widetilde H$, with in-degree counts inside the region;
--   2. initializes $Y=X\setminus\{(q,X(q))\}\cup\{(q,\tilde q)\}$ and $R=\emptyset$;
--   3. iterates Steps 1–3: sources are examined from a stack; a source entered by a live envy arc $(s,u)$ is handled by Step 2(a) or 2(b), and a source not entered is set aside, since envy arcs are only ever deleted; when no source remains to examine, Step 3 is applied to a set-aside source outside $V$; the iteration stops when no such source remains;
--   4. runs TTC on the irrelevant agents of $N$ and outputs $X'$ by the rule of p.13.
--
--   When agent $s$ moves to a better house $u$, its envy region is updated by deleting the old root and then, repeatedly, any vertex other than $u$ with no in-neighbour left; each vertex and each arc of $H_s$ is processed once over the run.
--
--   **Formalization Note** $H'$ is read only through the out- and in-lists of $p$ in $H'_a$, after a scan of the vertex list of $H'_a$ that locates $p$; elsewhere the orders of $H$ and $H'$ agree (clauses (i) and (iii)), so $H$'s diagrams are used. This matters because $|H'|$ can be of order $|H|^2$. The early exit of Algorithm 1, line 1 (return $X$ if it is already in the core of $H'$), is omitted, and $Q$ is computed over all agents other than $p$.
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, §4.1, pp.11–13, Algorithm 1 (p.14) and the proof of Lemma 4, p.18

import Mathlib
import Definitions.Def_HousingImprove_ttcProg

namespace HousingImprove

/-- The state of the charged implementation of HM-Improve (Schlotter, Biró, Fleiner,
arXiv:2110.06875v3, §4.1, pp.12–13, and the proof of Lemma 4, p.18). Agents of `Ñ` are numbered
`0, …, n − 1` (the agents of `N`) and `n + q` (the new agent `q̃`, for `q ∈ Q`). -/
structure HMSt where
  /-- `inQ[a]`: `a ∈ Q`, i.e. `a ≠ p` and `X(a) ≺'_a p`. -/
  inQ : Array Bool
  /-- `Y[a]`: the head of the arc of the sub-allocation leaving `a`, if any (`2n` cells). -/
  Y : Array (Option ℕ)
  /-- `Yin[b]`: the tail of the arc of the sub-allocation entering `b`, if any (`2n` cells). -/
  Yin : Array (Option ℕ)
  /-- `R[a]`: `a` is irrelevant (`2n` cells; also set for the unused numbers `n + a`, `a ∉ Q`). -/
  R : Array Bool
  /-- `inReg[v]`: node `v` of the diagram of `s = own[v]` lies strictly above `Y(s)` in `≺̃_s`, so that
  `(s, gid[v])` is an arc of the envy graph while `s ∉ R`. -/
  inReg : Array Bool
  /-- For a node of the region of its agent: the number of its in-neighbours in the region or at the
  root (the node of `Y(s)`). -/
  cnt : Array ℕ
  /-- `rootN[s]`: the node of `Y(s)` in the diagram of `s`; `none` while `Y(s)` is `p` (or `s̃`) and
  the region is entered through the list `vroot[s]`. -/
  rootN : Array (Option ℕ)
  /-- The out-neighbours, as nodes of `H_s`, of the position of `p` in `H'_s`. -/
  vroot : Array (Array ℕ)
  /-- `inL[u]`: the possible arcs entering `u ∈ N`: a node `v < M` of the diagram of `own[v]` with
  `gid[v] = u` stands for the arc `(own[v], u)`; `M + q` stands for the arc `(q̃, p)`. -/
  inL : Array (Array ℕ)
  /-- `inP[u]`: how many entries of `inL[u]` are known to be dead. -/
  inP : Array ℕ
  /-- Sources not yet examined. -/
  active : Array ℕ
  /-- Sources outside `V` found not entered by any arc of the envy graph. -/
  blocked : Array ℕ

/-- An entry of `inL[u]` is **alive** if it still is an arc of the envy graph: a region node of an
agent not in `R`, or an arc `(q̃, p)` with `q̃` a sink. Dead entries stay dead. -/
def hmAlive (n M : ℕ) (F : Flat) (S : HMSt) (e : ℕ) : Prog Bool := do
  if e < M then
    let r ← rd S.inReg e false
    let s ← rd F.own e 0
    let rs ← rd S.R s true
    opn 1 (r && !rs)
  else
    let y ← rd S.Y (n + (e - M)) none
    let rq ← rd S.R (n + (e - M)) true
    opn 1 (y.isNone && !rq)

/-- Move the root of agent `s` to the node `e` (the proof of Lemma 4, p.18, "deleting an arc from
[the envy graph] when it ceases to be `Y`-augmenting"): delete the old root, then repeatedly delete
any region node other than `e` with no in-neighbour left; the nodes left are those above `e`. Each
node is deleted once and each arc is decremented once over a whole run. -/
def hmAdvance (F : Flat) (fuel : ℕ) (S : HMSt) (s e : ℕ) : Prog HMSt := do
  let r ← rd S.rootN s none
  let outs ← match r with
    | none => rd S.vroot s #[]
    | some v => rd F.upF v #[]
  let dec := fun (cw : Array ℕ × Array ℕ) (w : ℕ) => do
    let (cnt, work) := cw
    let c ← rd cnt w 0
    let cnt ← wr cnt w (c - 1)
    if c - 1 = 0 ∧ w ≠ e then
      let work ← push work w
      pure (cnt, work)
    else opn 2 (cnt, work)
  let (cnt, work) ← forL outs.toList (S.cnt, #[]) dec
  let (cnt, _, inReg) ← whileF fuel (cnt, work, S.inReg) fun (cnt, work, inReg) => do
    let (top, work) ← pop work
    match top with
    | none => pure none
    | some v => do
      let inReg ← wr inReg v false
      let outs ← rd F.upF v #[]
      let (cnt, work) ← forL outs.toList (cnt, work) dec
      pure (some (cnt, work, inReg))
  let inReg ← wr inReg e false
  let rootN ← wr S.rootN s (some e)
  pure { S with cnt := cnt, inReg := inReg, rootN := rootN }

/-- The per-agent initialization of HM-Improve for agent `a` (Algorithm 1, lines 2–3, and the
initialization on p.12): decide `a ∈ Q`, set the root of `a`'s envy region (the node of `X(a)`, or the
position of `p` in `H'_a`, which `ã` takes for `a ∈ Q`), mark the region (the houses strictly above
the root), count in-degrees inside it, and record each region node in the in-list of its house.

`X(a) ≺'_a p` is decided from the in-list of `p` in `H'_a` and a search upwards from `X(a)` in `H_a`:
the order of `H'_a` off `p` is that of `H_a`. The up-set of `p` in `H'_a` is entered through the
out-list of `p` in `H'_a` and continued along `H_a`. `H'` is read only there, after a scan of the
vertex list of `H'_a` that locates `p`. -/
def hmInitAgent {n : ℕ} (I I' : HassePres n) (X : Fin n → Fin n) (p : Fin n) (F : Flat)
    (fuel : ℕ) (pos mem mark : Array ℕ) (vis : Array Bool) (S : HMSt) (a : Fin n) :
    Prog (Array ℕ × Array ℕ × Array ℕ × Array Bool × HMSt) := do
  let o ← rd F.off a.val 0
  let stamp := a.val + 1
  let (pos, mem, _) ← forL (I.verts a) (pos, mem, 0) fun (pos, mem, i) b => do
    let pos ← wr pos b.val i
    let mem ← wr mem b.val stamp
    opn 1 (pos, mem, i + 1)
  -- the node of a house of `A(a)`, if it is one
  let nodeOf := fun (mem pos : Array ℕ) (c : ℕ) => do
    let m ← rd mem c 0
    if m = stamp then
      let j ← rd pos c 0
      opn 1 (some (o + j))
    else opn 1 none
  let xa ← opn 1 (X a)
  -- locate `p` in the vertex list of `H'_a`
  let foundP ← forL (I'.verts a) false fun f b => opn 1 (f || decide (b = p))
  let upP ← opn 1 (if foundP then I'.up a p else [])
  let dnP ← opn 1 (if foundP then I'.down a p else [])
  let viaP ← forL upP #[] fun acc c => do
    match ← nodeOf mem pos c.val with
    | some v => push acc v
    | none => opn 1 acc
  let xnode ← nodeOf mem pos xa.val
  -- `a ∈ Q` iff `a ≠ p`, `X(a) ≠ p` and some house covered by `p` in `H'_a` is `X(a)` or above it
  let (q, mark, vis) ← do
    if decide (a = p) ∨ decide (xa = p) then opn 2 (false, mark, vis)
    else
      let mark ← forL dnP mark fun mark c => wr mark c.val stamp
      match xnode with
      | none => opn 1 (false, mark, vis)
      | some x0 => do
        let vis ← wr vis x0 true
        let (_, vis, hit) ← whileF fuel (#[x0], vis, false) fun (stk, vis, hit) => do
          let (top, stk) ← pop stk
          match top with
          | none => pure none
          | some v => do
            let h ← rd F.gid v 0
            let mk ← rd mark h 0
            let outs ← rd F.upF v #[]
            let (stk, vis) ← forL outs.toList (stk, vis) fun (stk, vis) w => do
              let seen ← rd vis w true
              if seen then opn 1 (stk, vis)
              else
                let vis ← wr vis w true
                let stk ← push stk w
                pure (stk, vis)
            opn 1 (some (stk, vis, hit || decide (mk = stamp)))
        pure (hit, mark, vis)
  let inQ ← wr S.inQ a.val q
  -- the root of the region: the node of `X(a)`, or the position of `p` in `H'_a`
  let useP := q || decide (xa = p ∧ a ≠ p)
  let rootN ← wr S.rootN a.val (if useP then none else xnode)
  let vroot ← wr S.vroot a.val (if useP then viaP else #[])
  let outs0 ← if useP then opn 1 viaP else
    match xnode with
    | some x0 => rd F.upF x0 #[]
    | none => opn 1 #[]
  -- the region: everything reachable from the root's out-neighbours
  let (inReg, stk) ← forL outs0.toList (S.inReg, #[]) fun (inReg, stk) w => do
    let seen ← rd inReg w true
    if seen then opn 1 (inReg, stk)
    else
      let inReg ← wr inReg w true
      let stk ← push stk w
      pure (inReg, stk)
  let (_, inReg, region) ← whileF fuel (stk, inReg, (#[] : Array ℕ)) fun (stk, inReg, region) => do
    let (top, stk) ← pop stk
    match top with
    | none => pure none
    | some v => do
      let region ← push region v
      let outs ← rd F.upF v #[]
      let (inReg, stk) ← forL outs.toList (inReg, stk) fun (inReg, stk) w => do
        let seen ← rd inReg w true
        if seen then opn 1 (inReg, stk)
        else
          let inReg ← wr inReg w true
          let stk ← push stk w
          pure (inReg, stk)
      pure (some (stk, inReg, region))
  -- in-degrees inside the region and from the root
  let incr := fun (cnt : Array ℕ) (w : ℕ) => do
    let c ← rd cnt w 0
    wr cnt w (c + 1)
  let cnt ← forL outs0.toList S.cnt incr
  let cnt ← forL region.toList cnt fun cnt v => do
    let outs ← rd F.upF v #[]
    forL outs.toList cnt incr
  -- the possible arcs entering each house
  let inL ← forL region.toList S.inL fun inL v => do
    let h ← rd F.gid v 0
    pushAt inL h v
  pure (pos, mem, mark, vis,
    { S with inQ := inQ, rootN := rootN, vroot := vroot, inReg := inReg, cnt := cnt, inL := inL })

/-- One iteration of the main loop of HM-Improve (Steps 1–3, p.12), or `none` when it stops.
Sources are examined from the stack `active`; a source with an alive entering arc is handled by
Step 2(a) or 2(b); a source not entered goes to `blocked` (arcs of the envy graph are only ever
deleted, so it is never entered again). When `active` is empty, every source outside `V` is in
`blocked` and none is entered, so Step 3 applies to the top of `blocked`. The loop stops when both
stacks are empty, i.e. `U \ V = ∅`, which means `U = V`. -/
def hmIter (n : ℕ) (F : Flat) (fuel : ℕ) (S : HMSt) : Prog (Option HMSt) := do
  let (top, active) ← pop S.active
  match top with
  | some u => do
    let S := { S with active := active }
    let ru ← rd S.R u true
    let yin ← rd S.Yin u none
    if ru || yin.isSome then opn 1 (some S)
    else if n ≤ u then
      -- a new agent `q̃` is entered by no arc
      let y ← rd S.Y u none
      if y.isNone then opn 1 (some S)
      else
        let blocked ← push S.blocked u
        pure (some { S with blocked := blocked })
    else
      let L ← rd S.inL u #[]
      let k0 ← rd S.inP u 0
      -- skip the dead entries of `inL[u]`
      let k ← whileF fuel k0 fun k => do
        if k < L.size then
          let e ← rd L k 0
          let al ← hmAlive n F.M F S e
          if al then pure none else opn 1 (some (k + 1))
        else opn 1 none
      let inP ← wr S.inP u k
      let S := { S with inP := inP }
      if k < L.size then
        let e ← rd L k 0
        if e < F.M then
          -- Step 2(a): `s = own[e]` moves from `u' = Y(s)` to `u`
          let s ← rd F.own e 0
          let u' ← rd S.Y s none
          let Y ← wr S.Y s (some u)
          let Yin ← wr S.Yin u (some s)
          let Yin ← match u' with
            | some w => wr Yin w none
            | none => opn 1 Yin
          let S ← hmAdvance F fuel { S with Y := Y, Yin := Yin } s e
          let active ← match u' with
            | some w => push S.active w
            | none => opn 1 S.active
          pure (some { S with active := active })
        else
          -- Step 2(b): the sink `q̃ = n + (e - M)` takes the arc `(q̃, p)`
          let qt ← opn 2 (n + (e - F.M))
          let Y ← wr S.Y qt (some u)
          let Yin ← wr S.Yin u (some qt)
          let qin ← rd Yin qt none
          let rq ← rd S.R qt true
          let blocked ← if qin.isNone && !rq then push S.blocked qt else opn 1 S.blocked
          pure (some { S with Y := Y, Yin := Yin, blocked := blocked })
      else
        let blocked ← push S.blocked u
        pure (some { S with blocked := blocked })
  | none => do
    let (top, blocked) ← pop S.blocked
    match top with
    | none => pure none
    | some u => do
      let S := { S with blocked := blocked }
      let ru ← rd S.R u true
      let yin ← rd S.Yin u none
      let y ← rd S.Y u none
      match y with
      | some u' =>
        if ru || yin.isSome then opn 1 (some S)
        else
          -- Step 3: `u` becomes irrelevant and `(u, u')` is deleted
          let R ← wr S.R u true
          let Y ← wr S.Y u none
          let Yin ← wr S.Yin u' none
          let active ← push S.active u'
          pure (some { S with R := R, Y := Y, Yin := Yin, active := active })
      | none => opn 1 (some S)

/-- The initialization and the iteration of HM-Improve (steps 1–3 of `hmImproveProg`): the flat
diagrams of `H` and the final state. -/
def hmMain {n : ℕ} (I I' : HassePres n) (X : Fin n → Fin n) (p : Fin n) :
    Prog (Flat × HMSt) := do
  let fuel := fuelOf I
  let F ← preprocess I
  let pos ← alloc n 0
  let mem ← alloc n 0
  let mark ← alloc n 0
  let vis ← alloc F.M false
  let S0 : HMSt :=
    { inQ := ← alloc n false, Y := ← alloc (2 * n) none, Yin := ← alloc (2 * n) none,
      R := ← alloc (2 * n) false, inReg := ← alloc F.M false, cnt := ← alloc F.M 0,
      rootN := ← alloc n none, vroot := ← alloc n #[], inL := ← alloc n #[],
      inP := ← alloc n 0, active := #[], blocked := #[] }
  let (_, _, _, _, S) ← forL (List.finRange n) (pos, mem, mark, vis, S0)
    fun (pos, mem, mark, vis, S) a => hmInitAgent I I' X p F fuel pos mem mark vis S a
  -- initialization of `Y`, the sources, and the arcs `(q̃, p)`
  let S ← forL (List.finRange n) S fun S a => do
    let q ← rd S.inQ a.val false
    let xa ← opn 1 (X a).val
    if q then
      let Y ← wr S.Y a.val (some (n + a.val))
      let Yin ← wr S.Yin (n + a.val) (some a.val)
      let active ← push S.active xa
      let inL ← pushAt S.inL p.val (F.M + a.val)
      pure { S with Y := Y, Yin := Yin, active := active, inL := inL }
    else
      let Y ← wr S.Y a.val (some xa)
      let Yin ← wr S.Yin xa (some a.val)
      let R ← wr S.R (n + a.val) true
      pure { S with Y := Y, Yin := Yin, R := R }
  -- the iteration
  let S ← whileF fuel S (hmIter n F fuel)
  pure (F, S)

/-- **Algorithm HM-Improve** (Schlotter, Biró, Fleiner, arXiv:2110.06875v3, §4.1, Algorithm 1,
pp.12–13), as a charged program. Input: the presentations `I` of `H` and `I'` of `H'`, the core
allocation `X` of `H` and the agent `p`. Output: the allocation `X'`.

1. Build the flat diagrams of `H` and, for each agent, its envy region and `a ∈ Q` (`hmInitAgent`).
2. Initialization (p.12): `Y = X \ {(q, X(q)) : q ∈ Q} ∪ {(q, q̃) : q ∈ Q}`, `R = ∅`; the sources
   `X(q)`, `q ∈ Q`, are put on `active`; each `(q̃, p)` is recorded as a possible arc entering `p`.
3. The iteration, Steps 1–3 (`hmIter`).
4. TTC (Appendix A) on the irrelevant agents of `N`, run on `H`'s diagrams (on `R ∩ N`, which
   excludes `p`, the orders of `H` and `H'` agree), and the output rule of p.13: `X'(a) = X_R(a)`
   on `R ∩ N`, `X'(a) = Y(a)` otherwise, with `q̃` read as `p`.

**Formalization Note.** `Q` is `{a ≠ p : X(a) ≺'_a p}` (Algorithm 1, line 2, with the `q_i` all
agents); line 1 of Algorithm 1 (return `X` if it is already in the core of `H'`) is omitted, as the
proof of Theorem 2 does not use it. `H'` is read only through the lists `I'.up a p`, `I'.down a p`
and a scan of `I'.verts a`, never elsewhere: `|H'|` can be of order `|H|²`. -/
def hmImproveProg {n : ℕ} (I I' : HassePres n) (X : Fin n → Fin n) (p : Fin n) :
    Prog (Fin n → Fin n) := do
  let fuel := fuelOf I
  let (F, S) ← hmMain I I' X p
  -- TTC on `R ∩ N`, and the output
  let inW ← alloc n false
  let inW ← forL (List.range n) inW fun inW a => do
    let r ← rd S.R a false
    wr inW a r
  let XR ← ttcCore n F fuel inW
  let out ← alloc n 0
  let out ← forL (List.range n) out fun out a => do
    let r ← rd S.R a false
    if r then
      let b ← rd XR a 0
      wr out a b
    else
      let y ← rd S.Y a none
      match y with
      | some b => if n ≤ b then wr out a p.val else wr out a b
      | none => wr out a a
  readOut n out

end HousingImprove


