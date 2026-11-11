-- Prove2me | Definitions.Def_AutobiddingGSP_Approximation_MembershipCircuit
-- name    : AutobiddingGSP_Approximation_MembershipCircuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:28:37.306352+00:00
-- url     : https://prove2.me/theorems/929dead8-4ea5-4289-8db7-5e66d68c2992
-- title:
--   The PL pseudo-circuits of §§4–5 for ABE-B and ABE-R, and the equilibrium read off a fixed point
-- statement:
--   `groups A` lists the value groups $g_1,\dots,g_T$ (owner, value, multiplicity) in lexicographic order; items of a group are ordered by original index.
--
--   `memCircuit A m γ` is the explicit gate list of the paper's circuit: multiplier nodes $\alpha_i$ (nodes $0..n-1$), group bids, for each step $t\ge2$ a sorting network for earlier bids, the Heaviside outputs $y_{t,j}$, residuals, insertion probabilities and cumulative probabilities; a sorting network producing $E_0\le\dots\le E_Q$, $w_h$, $u_h$ (if $T=1$: $E=(0,1)$, $Q=1$); for every $h$: selectors $z_{h,t,r}\in H(\min\{u_h-F_{t,r-1},F_{t,r}-u_h\})$, $\sigma_h(t)=\sum_r rz_{h,t,r}$, position layers $\mathrm{Idx}_{h,t}$, precedence bits $\beta_{h,s,t}$, item positions $\mathrm{ItemIdx}_{h,t,\ell}=\sum_{s\ne t}m_{g_s}\beta_{h,s,t}+\ell$, $N_{h,t}=\min(\{T\}\cup\{\beta_{h,t,s}\mathrm{Idx}_{h,s}+(1-\beta_{h,t,s})T:\iota(g_s)\ne\iota(g_t)\})$, $J_{h,t}=\sum_sb_sH(\tfrac12-|\mathrm{Idx}_{h,s}-N_{h,t}|)$; then
--
--   * **budget**: $p_{h,t,\ell}=\sum_{s,k}c_kb_sH(\tfrac12-|\mathrm{Idx}_{h,s}-N_{h,t}|)H(\tfrac12-|\mathrm{ItemIdx}_{h,t,\ell}-k|)$, $P_{h,i}$, $\hat q_{h,i}\in w_hD_\aleph(P_{h,i}/(U_i/\aleph))(U_i/\aleph)$ with $U_i=\sum_{\iota(g)=i}m_gv_g$ and $\aleph$ the least power of two $\ge\max\{1,\max_iU_i/(\gamma B_i)\}$, $\hat P_i=\sum_h\hat q_{h,i}$, update $\tilde\alpha_i=\max\{0,\min\{1,\alpha_i+(1-\gamma)B_i-\hat P_i\}\}$;
--   * **ROI**: $S_{h,t}=\sum_{\ell,k}c_kw_hH(\tfrac12-|\mathrm{ItemIdx}_{h,t,\ell}-k|)$, $\hat q_{h,t}\in(A_0v_{g_t}/\aleph)S_{h,t}D_\aleph(J_{h,t}/(A_0v_{g_t}/\aleph))$ with $\aleph$ the least power of two $\ge A_0/\gamma$, $\hat P_i$, $V_i=\sum v_{g_t}S_{h,t}$, update $\tilde\alpha_i=\max\{1,\min\{A_0,\alpha_i+(1-\gamma)V_i-\hat P_i\}\}$.
--
--   The node of $\alpha_i$ is the output of its update, so a fixed point has $\tilde\alpha=\alpha$. Sorting networks are insertion networks of comparators. `decodeAlpha` reads $\alpha$; `decodePi` reads $\pi(a)=\sum_hw_h\,[\text{every item's }\mathrm{ItemIdx}_h\text{ equals its 1-based rank in }a]$.
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], §4.1–4.2, pp. 11–17; §5.1–5.3, pp. 22–25 (PDF 11–25)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_AutobiddingGSP_Approximation_Model
import Definitions.Def_AutobiddingGSP_Approximation_Search
import Definitions.Def_AutobiddingGSP_Approximation_PLCircuit

namespace AutobiddingGSP.Approximation

open QAlgorithms.LocalHamiltonian

/-- A value group (§4, pp. 11–12): the owner `ι(g)` (0-based bidder), the common value `v_g` and
the multiplicity `m_g` of the items of that bidder with that value. -/
structure Grp where
  owner : ℕ
  val : ℚ
  mult : ℕ

/-- **The value groups** `g_1, …, g_T` in the lexicographic insertion order of their indices
`(i, j)` (§4, pp. 11–12): for each bidder in turn, its distinct values in decreasing order (the
values of a well-formed auction are listed nonincreasingly), each with its multiplicity. -/
def groups (A : Auction) : List Grp :=
  (List.range A.vals.length).flatMap (fun i =>
    let l := A.vals.getD i []
    l.dedup.map (fun v => (⟨i, v, l.count v⟩ : Grp)))

/-- The group (0-based index in `groups A`) and the 1-based place `ℓ` inside it of the item `j` of
bidder `i`, using the fixed internal order of each group by increasing original item index
(§4, p. 12). -/
def itemGroup (A : Auction) (i j : ℕ) : ℕ × ℕ :=
  let l := A.vals.getD i []
  let v := l.getD j 0
  ((groups A).findIdx (fun g => g.owner == i && g.val == v), (l.take j).count v + 1)

/-- The state monad in which circuits are built: the gates emitted so far. -/
abbrev BM := StateM (Array PGate)

/-- Emit a gate; returns the number of its node. -/
def emit (g : PGate) : BM ℕ := do
  let s ← get
  set (s.push g)
  pure s.size

/-- Replace the gate of node `k`. -/
def setGate (k : ℕ) (g : PGate) : BM Unit := modify (fun s => s.set! k g)

/-- A comparator `(x, y) ↦ (max{x, y}, min{x, y})` (§4.1, p. 12). -/
def cmpx (x y : ℕ) : BM (ℕ × ℕ) := do
  let hi ← emit (PGate.max x y)
  let lo ← emit (PGate.min x y)
  pure (hi, lo)

/-- Insert a node into a nonincreasingly sorted list of nodes by a chain of comparators. -/
def insertDesc : List ℕ → ℕ → BM (List ℕ)
  | [], x => pure [x]
  | d :: ds, x => do
    let (hi, lo) ← cmpx d x
    let rest ← insertDesc ds lo
    pure (hi :: rest)

/-- **A sorting network** (insertion network of comparators): its outputs are the nonincreasing
rearrangement of its inputs. -/
def sortDesc : List ℕ → BM (List ℕ)
  | [] => pure []
  | x :: xs => do
    let s ← sortDesc xs
    insertDesc s x

/-- `|x − y|` by max gates. -/
def absDiff (x y : ℕ) : BM ℕ := do
  let p ← emit (PGate.lin [(1, x), (-1, y)] 0)
  let q ← emit (PGate.lin [(-1, x), (1, y)] 0)
  emit (PGate.max p q)

/-- `|x − k|` for a constant `k`, by max gates. -/
def absDiffConst (x : ℕ) (k : ℚ) : BM ℕ := do
  let p ← emit (PGate.lin [(1, x)] (-k))
  let q ← emit (PGate.lin [(-1, x)] k)
  emit (PGate.max p q)

/-- The minimum of a node and a list of nodes, by min gates. -/
def minChain (start : ℕ) (xs : List ℕ) : BM ℕ :=
  xs.foldlM (fun acc x => emit (PGate.min acc x)) start

/-- The smallest power of two `ℵ = 2^d` with `ℵ ≥ x` (for `x ≥ 1`). -/
def pow2Ceil (x : ℚ) : ℕ := 2 ^ Nat.clog 2 ⌈x⌉₊

/-- **The PL pseudo-circuit of §§4–5** for the auction `A`, the constraint model `m` and the
precision `γ` (pp. 12–25). Nodes `0, …, n − 1` are the multipliers `α_i`; each is the output of its
update gate (§5.2 p. 23, §5.3 p. 25), so that a fixed point satisfies `α̃ = α`. In order:

* group bids `b_t = v_{g_t} α_{ι(g_t)}`;
* if `T ≥ 2`, for each step `t ≥ 2`: a sorting network for the earlier bids, the Heaviside
  outputs `y_{t,j}`, residuals `R_{t,j}`, insertion probabilities `ρ_{t,r}` and cumulative
  probabilities `F_{t,r}`; then a sorting network for all `F` entries (`E_0 ≤ ⋯ ≤ E_Q`), and
  `w_h`, `u_h` (§4.1, pp. 12–15). If `T = 1` there is no insertion step: `E = (0, 1)`, `Q = 1`;
* for every `h ∈ [Q]`: the selectors `z_{h,t,r}`, positions `σ_h(t) = ∑_r r z_{h,t,r}` and the
  position layers `Idx_{h,t}` (with `Idx_{h,1} = 0` when `T = 1`), the precedence bits `β_{h,s,t}`,
  item positions `ItemIdx_{h,t,ℓ}`, next-other-bidder positions `N_{h,t}` and prices `J_{h,t}`
  (§4.1–4.2, pp. 16–17, with the products of §5.1, p. 22, as `y·H(x)` pseudogates); then
  - budget: item payments `p_{h,t,ℓ} = ∑_{s,k} c_k b_s H(½ − |Idx_{h,s} − N_{h,t}|)
    H(½ − |ItemIdx_{h,t,ℓ} − k|)` and `P_{h,i}` (§5.1, p. 22);
  - ROI: `S_{h,t} = ∑_{ℓ,k} c_k w_h H(½ − |ItemIdx_{h,t,ℓ} − k|)` (§5.3, p. 24);
* budget: `q̂_{h,i} ∈ w_h D_ℵ(P_{h,i}/(U_i/ℵ)) (U_i/ℵ)` with `U_i = ∑_{g : ι(g) = i} m_g v_g` and
  `ℵ` the least power of two `≥ max{1, max_i U_i/(γ B_i)}`, `P̂_i = ∑_h q̂_{h,i}`, and
  `α̃_i = max{0, min{1, α_i + (1 − γ)B_i − P̂_i}}` (§5.2, pp. 22–23);
* ROI: `q̂_{h,t} ∈ (A v_{g_t}/ℵ) S_{h,t} D_ℵ(J_{h,t}/(A v_{g_t}/ℵ))` with `A = A₀` and `ℵ` the
  least power of two `≥ A/γ`, `P̂_i = ∑_{h, ι(g_t) = i} q̂_{h,t}`,
  `V_i = ∑_{h, ι(g_t) = i} v_{g_t} S_{h,t}`, and `α̃_i = max{1, min{A, α_i + (1 − γ)V_i − P̂_i}}`
  (§5.3, pp. 24–25).

Returns the nodes `w_1, …, w_Q` and, for every `h`, bidder `i` and item `j`, the node
`ItemIdx_{h,t,ℓ}` of that item.

**Formalization Note** The sorting networks are insertion networks of comparators (the paper's
"a sorting network, i.e., AKS"; every sorting network has the same outputs). Sums of several terms
are single `lin` gates (composites of the paper's addition and constant-multiplication gates);
`Σ_ℓ p_{h,t,ℓ}` is one `lin` gate per group. -/
def memCircuitM (A : Auction) (m : Model) (γ : ℚ) : BM (List ℕ × List (List (List ℕ))) := do
  let n := A.vals.length
  let G := groups A
  let T := G.length
  let gr : ℕ → Grp := fun t => G.getD t ⟨0, 0, 0⟩
  -- the multiplier nodes `0, …, n − 1` (their update gates are set at the end)
  for _ in List.range n do
    let _ ← emit (PGate.const 0)
  -- group bids
  let mut bN : Array ℕ := #[]
  for t in List.range T do
    bN := bN.push (← emit (PGate.lin [((gr t).val, (gr t).owner)] 0))
  -- insertion probabilities, cumulative probabilities, sorted entries
  let mut Fs : Array (Array ℕ) := #[#[]]
  let mut E : List ℕ := []
  if 2 ≤ T then
    for t in List.range' 1 (T - 1) do
      let d ← sortDesc ((List.range t).map (fun s => bN.getD s 0))
      let mut R ← emit (PGate.const 1)
      let mut rhos : Array ℕ := #[]
      for dj in d do
        let diff ← emit (PGate.lin [(1, bN.getD t 0), (-1, dj)] 0)
        let y ← emit (PGate.heav diff)
        let rho ← emit (PGate.min R y)
        rhos := rhos.push rho
        R ← emit (PGate.lin [(1, R), (-1, rho)] 0)
      rhos := rhos.push R
      let mut F ← emit (PGate.const 0)
      let mut Ft : Array ℕ := #[F]
      for rho in rhos do
        F ← emit (PGate.lin [(1, F), (1, rho)] 0)
        Ft := Ft.push F
      Fs := Fs.push Ft
    let Edesc ← sortDesc (Fs.toList.flatMap Array.toList)
    E := Edesc.reverse
  else
    let e0 ← emit (PGate.const 0)
    let e1 ← emit (PGate.const 1)
    E := [e0, e1]
  let Q := E.length - 1
  let eN : ℕ → ℕ := fun h => E.getD h 0
  let mut wN : Array ℕ := #[]
  let mut uN : Array ℕ := #[]
  for h in List.range' 1 Q do
    wN := wN.push (← emit (PGate.lin [(1, eN h), (-1, eN (h - 1))] 0))
    uN := uN.push (← emit (PGate.lin [(1 / 2, eN (h - 1)), (1 / 2, eN h)] 0))
  -- per interval `h`
  let mut payH : Array (Array ℕ) := #[]
  let mut sH : Array (Array ℕ) := #[]
  let mut jH : Array (Array ℕ) := #[]
  let mut items : List (List (List ℕ)) := []
  for hh in List.range Q do
    let u := uN.getD hh 0
    let w := wN.getD hh 0
    let mut idx : Array ℕ := #[]
    if 2 ≤ T then
      let s0 ← emit (PGate.const 0)
      let mut sel : Array ℕ := #[s0]
      for t in List.range' 1 (T - 1) do
        let Ft := Fs.getD t #[]
        let mut zs : List (ℚ × ℕ) := []
        for r in List.range (t + 1) do
          let a ← emit (PGate.lin [(1, u), (-1, Ft.getD r 0)] 0)
          let b ← emit (PGate.lin [(1, Ft.getD (r + 1) 0), (-1, u)] 0)
          let mn ← emit (PGate.min a b)
          let z ← emit (PGate.heav mn)
          zs := zs ++ [((r : ℚ), z)]
        sel := sel.push (← emit (PGate.lin zs 0))
      for t in List.range T do
        let mut cur := sel.getD t 0
        for k in List.range (T - t - 1) do
          let arg ← emit (PGate.lin [(1, cur), (-1, sel.getD (t + k + 1) 0)] (1 / 2))
          let hv ← emit (PGate.heav arg)
          cur ← emit (PGate.lin [(1, cur), (1, hv)] 0)
        idx := idx.push cur
    else
      let z0 ← emit (PGate.const 0)
      idx := #[z0]
    let iN : ℕ → ℕ := fun t => idx.getD t 0
    -- precedence bits `β_{h,s,t} ∈ H(Idx_{h,t} − Idx_{h,s} − 1/2)` (stored at `[s][t]`)
    let mut bx : Array (Array ℕ) := #[]
    let mut be : Array (Array ℕ) := #[]
    for s in List.range T do
      let mut rx : Array ℕ := #[]
      let mut re : Array ℕ := #[]
      for t in List.range T do
        if s ≠ t then
          let x ← emit (PGate.lin [(1, iN t), (-1, iN s)] (-1 / 2))
          rx := rx.push x
          re := re.push (← emit (PGate.heav x))
        else
          rx := rx.push 0
          re := re.push 0
      bx := bx.push rx
      be := be.push re
    let bxN : ℕ → ℕ → ℕ := fun s t => (bx.getD s #[]).getD t 0
    let beN : ℕ → ℕ → ℕ := fun s t => (be.getD s #[]).getD t 0
    -- item positions `ItemIdx_{h,t,ℓ} = ∑_{s ≠ t} m_{g_s} β_{h,s,t} + ℓ`
    let mut II : Array (Array ℕ) := #[]
    for t in List.range T do
      let mut row : Array ℕ := #[]
      for l in List.range' 1 (gr t).mult do
        let ts := ((List.range T).filter (fun s => s ≠ t)).map (fun s => (((gr s).mult : ℚ), beN s t))
        row := row.push (← emit (PGate.lin ts (l : ℚ)))
      II := II.push row
    -- `N_{h,t}` and the price terms `b_s H(1/2 − |Idx_{h,s} − N_{h,t}|)`, `J_{h,t}`
    let mut jterm : Array (Array ℕ) := #[]
    let mut Jt : Array ℕ := #[]
    for t in List.range T do
      let start ← emit (PGate.const (T : ℚ))
      let mut cands : List ℕ := []
      for s in List.range T do
        if (gr s).owner ≠ (gr t).owner then
          let prod ← emit (PGate.mulHeav (bxN t s) (iN s))
          let cand ← emit (PGate.lin [(1, prod), (-(T : ℚ), beN t s)] (T : ℚ))
          cands := cands ++ [cand]
      let N ← minChain start cands
      let mut row : Array ℕ := #[]
      for s in List.range T do
        let dd ← absDiff (iN s) N
        let x1 ← emit (PGate.lin [(-1, dd)] (1 / 2))
        row := row.push (← emit (PGate.mulHeav x1 (bN.getD s 0)))
      jterm := jterm.push row
      Jt := Jt.push (← emit (PGate.lin (row.toList.map (fun z => ((1 : ℚ), z))) 0))
    -- CTR selectors, payments (budget) or probability-weighted CTRs (ROI)
    let mut payGroup : Array ℕ := #[]
    let mut St : Array ℕ := #[]
    for t in List.range T do
      let mut terms : List (ℚ × ℕ) := []
      for l in List.range (gr t).mult do
        let ii := (II.getD t #[]).getD l 0
        for k in List.range' 1 A.K do
          let dk ← absDiffConst ii (k : ℚ)
          let x2 ← emit (PGate.lin [(-1, dk)] (1 / 2))
          match m with
          | Model.budget =>
            for s in List.range T do
              let pr ← emit (PGate.mulHeav x2 ((jterm.getD t #[]).getD s 0))
              terms := terms ++ [(A.ctr.getD (k - 1) 0, pr)]
          | Model.roi =>
            let sw ← emit (PGate.mulHeav x2 w)
            terms := terms ++ [(A.ctr.getD (k - 1) 0, sw)]
      match m with
      | Model.budget => payGroup := payGroup.push (← emit (PGate.lin terms 0))
      | Model.roi => St := St.push (← emit (PGate.lin terms 0))
    match m with
    | Model.budget =>
      let mut row : Array ℕ := #[]
      for i in List.range n do
        let ts := ((List.range T).filter (fun t => (gr t).owner = i)).map
          (fun t => ((1 : ℚ), payGroup.getD t 0))
        row := row.push (← emit (PGate.lin ts 0))
      payH := payH.push row
    | Model.roi =>
      sH := sH.push St
      jH := jH.push Jt
    items := items ++ [(List.range n).map (fun i =>
      (List.range (A.vals.getD i []).length).map (fun j =>
        let p := itemGroup A i j
        (II.getD p.1 #[]).getD (p.2 - 1) 0))]
  -- discretized payments and multiplier updates
  let Bud : ℕ → ℚ := fun i => A.budgets.getD i 0
  let U : ℕ → ℚ := fun i => (A.vals.getD i []).sum
  let mut upd : Array ℕ := #[]
  match m with
  | Model.budget =>
    let aleph := pow2Ceil (((List.range n).map (fun i => U i / (γ * Bud i))).foldr max 1)
    for i in List.range n do
      let mut qs : List (ℚ × ℕ) := []
      for hh in List.range Q do
        let q ← emit (PGate.mulDisc aleph (U i / aleph) ((payH.getD hh #[]).getD i 0) (wN.getD hh 0))
        qs := qs ++ [(1, q)]
      let Phat ← emit (PGate.lin qs 0)
      let inner ← emit (PGate.lin [(1, i), (-1, Phat)] ((1 - γ) * Bud i))
      let c0 ← emit (PGate.const 0)
      let c1 ← emit (PGate.const 1)
      let mn ← emit (PGate.min c1 inner)
      upd := upd.push (← emit (PGate.max c0 mn))
  | Model.roi =>
    let A0 := A.capA0
    let aleph := pow2Ceil (A0 / γ)
    for i in List.range n do
      let mut qs : List (ℚ × ℕ) := []
      let mut vs : List (ℚ × ℕ) := []
      for hh in List.range Q do
        for t in List.range T do
          if (gr t).owner = i then
            let S := (sH.getD hh #[]).getD t 0
            let J := (jH.getD hh #[]).getD t 0
            let q ← emit (PGate.mulDisc aleph (A0 * (gr t).val / aleph) J S)
            qs := qs ++ [(1, q)]
            vs := vs ++ [((gr t).val, S)]
      let Phat ← emit (PGate.lin qs 0)
      let V ← emit (PGate.lin vs 0)
      let inner ← emit (PGate.lin [(1, i), (1 - γ, V), (-1, Phat)] 0)
      let c1 ← emit (PGate.const 1)
      let cA ← emit (PGate.const A0)
      let mn ← emit (PGate.min cA inner)
      upd := upd.push (← emit (PGate.max c1 mn))
  for i in List.range n do
    setGate i (PGate.lin [(1, upd.getD i 0)] 0)
  pure (wN.toList, items)

/-- The circuit of §§4–5 with its designated outputs: the gate list, the nodes `w_1, …, w_Q` and,
for every `h`, bidder `i` and item `j`, the node of that item's position `ItemIdx`. The multiplier
nodes are `0, …, n − 1`. -/
structure MemCircuit where
  gates : List PGate
  wNodes : List ℕ
  itemNodes : List (List (List ℕ))

/-- The circuit of §§4–5 (`memCircuitM`, run from the empty gate list). -/
def memCircuit (A : Auction) (m : Model) (γ : ℚ) : MemCircuit :=
  let r := (memCircuitM A m γ).run #[]
  ⟨r.2.toList, r.1.1, r.1.2⟩

/-- A list of naturals in binary. -/
def encNatList (l : List ℕ) : List Bool := encBin l.length ++ l.flatMap encBin

/-- The binary code of the circuit with its designated output nodes. -/
def encMemCircuit (C : MemCircuit) : List Bool :=
  encPGates C.gates ++ encNatList C.wNodes ++
    encBin C.itemNodes.length ++ C.itemNodes.flatMap (fun l => encBin l.length ++ l.flatMap encNatList)

/-- The multiplier profile read off a circuit state (§4.3, p. 18: the circuit outputs `α̃`). -/
def decodeAlpha (A : Auction) (v : ℕ → ℝ) : Fin A.n → ℝ := fun i => v i.val

/-- **The randomized allocation read off a circuit state** (`π̃ = (w_h, ItemIdx_h)_{h ∈ [Q]}`, §4.3,
p. 18): `π(a) = ∑_h w_h · [every item `x` has `ItemIdx_h(x) = rank_a(x)`]`, ranks 1-based. -/
noncomputable def decodePi (A : Auction) (C : MemCircuit) (v : ℕ → ℝ) : A.Alloc → ℝ := by
  classical
  exact fun a => ((C.wNodes.zip C.itemNodes).map (fun p => v p.1 *
    if (∀ x : A.Item, v ((p.2.getD x.1.val []).getD x.2.val 0) = ((a.symm x).val : ℝ) + 1) then 1 else 0)).sum

end AutobiddingGSP.Approximation


