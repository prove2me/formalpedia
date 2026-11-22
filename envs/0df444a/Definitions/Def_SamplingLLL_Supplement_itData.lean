-- Prove2me | Definitions.Def_SamplingLLL_Supplement_itData
-- name    : SamplingLLL_Supplement_itData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:48:22.596476+00:00
-- url     : https://prove2.me/theorems/e000d932-1053-4979-9f48-14859695bff5
-- title:
--   Independent transversals: the instance and the sampler and FPRAS of Appendix B
-- statement:
--   **Instance.** Blocks $V_1,\dots,V_n$ (nonempty, disjoint), each with a rational probability distribution $\pi_i$ (uniform in Theorem 2.13(i)), and a graph $J$ on $V=\bigsqcup_i V_i$. A selection $y$ picks one vertex from each block; it is an **independent transversal** when the chosen vertices are pairwise non-adjacent (Definition 2.12). The number of independent transversals, the product weight $\prod_i\pi_i(y_i)$ and the probability that the $\pi$-selection is independent are defined by finite sums.
--
--   **The transversal CSP.** $X_i\in V_i$ with law $\pi_i$, and one atomic bad event $\{X_i=u,\ X_j=v\}$ for every edge $uv$ with $u\in V_i$, $v\in V_j$, $i\neq j$. Edges inside a block and edges whose bad event has zero mass are deleted first.
--
--   **The procedure of Appendix B**, as data for the base mission's execution machinery:
--
--   1. the Prim compatible exploration of B.1 and its conservative collar, restored block by block (B.2);
--   2. the budgets $B_{(A,uv)}=\beta\,\pi_i(u)\pi_j(v)/(\phi_i(A)\phi_j(A))$ with $\kappa=473/2500$, $\beta=9\kappa(1-\kappa)=8628939/6250000$ and block potentials $\phi_i(A)=1-(\kappa/\Delta_i)\sum_{uv\in A,\,u\in V_i}\pi_i(u)$ ((16), (17), (29));
--   3. the proposal of B.3 with the parent edge excluded, $\alpha=8053/50000$, activation probability $\alpha/(d+\alpha)$ with $d=\Delta-1$, slot padding $2d$ at the contracted root and $d$ elsewhere, and its rejection rules; for $\Delta=1$ the root edge with probability one;
--   4. the exact local operation of B.3 and B.7.
--
--   The degree bounds $\Delta_i$ are the maximum degree of the kept graph (parts (i), (ii)) or, in a bipartite host, the maximum degree on the side of block $i$ (part (iii), B.8). The sampler is sequential insertion of the kept edges; the FPRAS estimates the probability that the selection is independent, and in the uniform case the counter multiplies it by $\prod_i|V_i|$.
--
--   **Formalization Note** Block $V_i$ is $\{0,\dots,b_i\}$. The degree bounds used by the algorithm are computed after the deletions and are at least $1$; they do not exceed the bounds given in Theorem 2.13. The module has no declaration named `itData` at top level; the data is `Blocks.itData`.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Definition 2.12 and Theorem 2.13, p.9; Appendix B.1–B.4, B.7, B.8, pp.25–34

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_Common

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL.Supplement

open Proc

/-! # Independent transversals: the instance of Theorem 2.13 and the procedure of Appendix B

Source: Achlioptas, *Counting and Sampling by Local Repair*, STOC 2027 submission (manuscript sha256
7a943167…), Definition 2.12 and Theorem 2.13, p.9; Appendix B.1–B.4, B.7, B.8, pp.25–34. -/

/-- Blocks `V_1, …, V_n`, block `V_i = Fin (b i + 1)` (blocks of a partition are nonempty), each carrying a
rational probability distribution `π_i` (Theorem 2.13(ii); the uniform law in (i)). -/
structure Blocks (n : ℕ) where
  /-- `|V_i| = b i + 1`. -/
  b : Fin n → ℕ
  /-- The distribution `π_i` on `V_i`. -/
  π : (i : Fin n) → Fin (b i + 1) → ℚ
  π_nonneg : ∀ i x, 0 ≤ π i x
  π_sum : ∀ i, ∑ x, π i x = 1

variable {n : ℕ}

namespace Blocks

variable (W : Blocks n)

/-- The vertex set `V = ⊔_i V_i`; a vertex is a block index with a position in the block. -/
abbrev Vtx : Type := Σ i : Fin n, Fin (W.b i + 1)

/-- A selection of one vertex from each block. -/
abbrev Sel : Type := (i : Fin n) → Fin (W.b i + 1)

/-- The uniform blocks of Theorem 2.13(i): `π_i(v) = 1/|V_i|`. -/
def uniform (b : Fin n → ℕ) : Blocks n where
  b := b
  π i _ := 1 / (b i + 1 : ℚ)
  π_nonneg i _ := by positivity
  π_sum i := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp

variable (J : SimpleGraph W.Vtx) [DecidableRel J.Adj]

/-- Definition 2.12, p.9: the selection `y` is an independent transversal of `J`: the chosen vertices
`(i, y_i)` are pairwise non-adjacent. -/
def IsIT (y : W.Sel) : Prop := ∀ i j : Fin n, ¬ J.Adj ⟨i, y i⟩ ⟨j, y j⟩

instance (y : W.Sel) : Decidable (W.IsIT J y) := by unfold IsIT; infer_instance

/-- The number of independent transversals. -/
def numIT : ℕ := (Finset.univ.filter fun y : W.Sel => W.IsIT J y).card

/-- The product weight `∏_i π_i(y_i)` of a selection. -/
def selWeight (y : W.Sel) : ℚ := ∏ i, W.π i (y i)

/-- The probability that the independent selection by `π` is an independent transversal. -/
def probIT : ℚ := ∑ y : W.Sel, if W.IsIT J y then W.selWeight y else 0

/-! ## The transversal CSP (Appendix B, p.26; B.7, p.32) -/

/-- The edges kept by the algorithm, each oriented from its lower to its higher block: edges inside one
block are deleted (p.26), and so are edges whose bad event has zero product mass (B.7, p.32). -/
def keptEdges : Finset (W.Vtx × W.Vtx) :=
  Finset.univ.filter fun p => p.1.1 < p.2.1 ∧ J.Adj p.1 p.2 ∧ 0 < W.π p.1.1 p.1.2 * W.π p.2.1 p.2.2

/-- The fixed edge order: the kept edges as a list. -/
noncomputable def elist : List (W.Vtx × W.Vtx) := (W.keptEdges J).toList

/-- The number of constraints. -/
noncomputable def M : ℕ := (W.elist J).length

/-- The edge of a constraint. -/
noncomputable def edge (a : Fin (W.M J)) : W.Vtx × W.Vtx := (W.elist J).get a

/-- The vertex of a vertex pair lying in block `i`, if any. -/
def atBlock (p : W.Vtx × W.Vtx) (i : Fin n) : Option (Fin (W.b i + 1)) :=
  if h : p.1.1 = i then some (h ▸ p.1.2) else if h' : p.2.1 = i then some (h' ▸ p.2.2) else none

/-- The transversal CSP: `X_i ∈ V_i` with law `π_i`, and for the edge `e = uv`, `u ∈ V_i`, `v ∈ V_j`,
`Bad_e = {X_i = u, X_j = v}` (p.26). -/
noncomputable def itCSP : AtomicCSP n (W.M J) where
  dom := W.b
  lam := W.π
  lam_nonneg := W.π_nonneg
  lam_sum := W.π_sum
  word a i := W.atBlock (W.edge J a) i

/-- The degree of a vertex in the kept graph. -/
noncomputable def kdeg (u : W.Vtx) : ℕ :=
  (Finset.univ.filter fun a : Fin (W.M J) => (W.edge J a).1 = u ∨ (W.edge J a).2 = u).card

/-- The maximum degree `∆` after the deletions, at least `1` (B.1, p.26; B.7, p.32). -/
noncomputable def kmaxDeg : ℕ := Finset.univ.fold max 1 (W.kdeg J)

/-- In a bipartite host with block sides `side` (`true` is side `A`), the maximum degree `∆_X` on the side
`X` of block `i` after the deletions, at least `1` (B.8, p.33). -/
noncomputable def sideDeg (side : Fin n → Bool) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun u : W.Vtx => side u.1 = side i).fold max 1 (W.kdeg J)

/-! ## The procedure of Appendix B, for a degree bound `Δ_i` per block

The uniform and weighted cases (i), (ii) use `Δ_i = ∆` for every block; the bipartite case (iii) uses
`Δ_i = ∆_X` for the side `X` of block `i`. -/

/-- `κ = 473/2500` (16). -/
def kappa : ℚ := 473 / 2500
/-- `β = 9κ(1−κ) = 8628939/6250000` (16). -/
def betaIT : ℚ := 8628939 / 6250000
/-- `α = 8053/50000` (22). -/
def alphaIT : ℚ := 8053 / 50000

/-- The discovered vertices of an accepted edge set: their endpoints. -/
noncomputable def discovered (Y : Finset (Fin (W.M J))) : Finset W.Vtx :=
  Y.biUnion fun a => {(W.edge J a).1, (W.edge J a).2}

/-- The represented blocks `S_T`. -/
noncomputable def represented (Y : Finset (Fin (W.M J))) : Finset (Fin n) :=
  (W.discovered J Y).image Sigma.fst

/-- The Prim exploration of B.1, p.26: among unqueried edges of the task family with exactly one endpoint
discovered and the other endpoint in a new block, query the least one. -/
noncomputable def primNext (S : Finset (Fin (W.M J))) (_c : Fin (W.M J)) : NextQuery (W.M J) :=
  fun Y N => (List.finRange (W.M J)).find? fun a =>
    decide (a ∈ S ∧ a ∉ Y ∧ a ∉ N ∧
      (((W.edge J a).1 ∈ W.discovered J Y ∧ (W.edge J a).2.1 ∉ W.represented J Y) ∨
       ((W.edge J a).2 ∈ W.discovered J Y ∧ (W.edge J a).1.1 ∉ W.represented J Y)))

/-- The record has mass zero (B.1, p.26): an unqueried edge of the task family joins two discovered
vertices. -/
def itDead (S : Finset (Fin (W.M J))) (t : Leaf (W.M J)) : Prop :=
  ∃ a ∈ S, a ∉ t.1 ∧ a ∉ t.2 ∧ (W.edge J a).1 ∈ W.discovered J t.1 ∧
    (W.edge J a).2 ∈ W.discovered J t.1

noncomputable instance (S : Finset (Fin (W.M J))) (t : Leaf (W.M J)) : Decidable (W.itDead J S t) := by
  classical
  unfold itDead; infer_instance

/-- The conservative collar's complement `R_T`: the edges of the task family with no endpoint in a
represented block (B.1, p.26). -/
noncomputable def itR (S : Finset (Fin (W.M J))) (_c : Fin (W.M J)) (t : Leaf (W.M J)) :
    Finset (Fin (W.M J)) :=
  S.filter fun a => (W.edge J a).1.1 ∉ W.represented J t.1 ∧ (W.edge J a).2.1 ∉ W.represented J t.1

/-- The collar `D_T` in the block-by-block restoration order of B.2, p.27: blocks of `S_T` in index order;
at the stage of block `i`, every still-missing edge of `D_T` incident to `V_i`, in edge order. -/
noncomputable def itRestore (S : Finset (Fin (W.M J))) (c : Fin (W.M J)) (t : Leaf (W.M J)) :
    List (Fin (W.M J)) :=
  (List.finRange n).foldl (fun acc i =>
    if i ∈ W.represented J t.1 then
      acc ++ (List.finRange (W.M J)).filter fun a =>
        decide (a ∈ S ∧ a ∉ W.itR J S c t ∧ ((W.edge J a).1.1 = i ∨ (W.edge J a).2.1 = i) ∧ a ∉ acc)
    else acc) []

open Classical in
/-- The local event `E_T` on the represented blocks: each represented block takes its discovered vertex,
and the record has positive mass (B.1, p.26). -/
noncomputable def itEvent (S : Finset (Fin (W.M J))) (_c : Fin (W.M J)) (t : Leaf (W.M J))
    (x : W.Sel) : Bool :=
  decide (¬ W.itDead J S t ∧ ∀ i ∈ W.represented J t.1, some (x i) = (W.itCSP J).pin t.1 i)

/-- `ϕ_i(A) = 1 − (κ/Δ_i) Σ_{uv∈A, u∈V_i} π_i(u)` ((29), p.32; (17) in the uniform case; B.8, p.33),
charged. -/
noncomputable def phiC (Δ : Fin n → ℕ) (A : Finset (Fin (W.M J))) (i : Fin n) : CQ :=
  csub (cq 1) (cmul (cdiv (cq kappa) (cq (Δ i)))
    (csum (((List.finRange (W.M J)).filter fun a => a ∈ A).filterMap fun a =>
      ((W.itCSP J).word a i).map fun w => cq (W.π i w))))

/-- The budget `B_{(A,uv)} = β π_i(u) π_j(v) / (ϕ_i(A) ϕ_j(A))` ((17), p.27; B.7, p.32; B.8, p.33),
charged. -/
noncomputable def budgetC (Δ : Fin n → ℕ) (A : Finset (Fin (W.M J))) (a : Fin (W.M J)) : CQ :=
  let u := (W.edge J a).1
  let v := (W.edge J a).2
  cdiv (cmul (cmul (cq betaIT) (cq (W.π u.1 u.2))) (cq (W.π v.1 v.2)))
    (cmul (W.phiC J Δ A u.1) (W.phiC J Δ A v.1))

/-- The other endpoint of an edge from `w`. -/
noncomputable def other (a : Fin (W.M J)) (w : W.Vtx) : W.Vtx :=
  if (W.edge J a).1 = w then (W.edge J a).2 else (W.edge J a).1

/-- The slot list of a vertex `w` reached by the edge `pe` (B.3, p.28): its incident kept edges other
than `pe`, in edge order, padded with `none` to `Δ_{block w} − 1` slots. -/
noncomputable def slots (Δ : Fin n → ℕ) (w : W.Vtx) (pe : Fin (W.M J)) : List (Option (Fin (W.M J))) :=
  let real := ((List.finRange (W.M J)).filter fun a =>
    decide (a ≠ pe ∧ ((W.edge J a).1 = w ∨ (W.edge J a).2 = w))).map some
  real ++ List.replicate (Δ w.1 - 1 - real.length) none

/-- The proposal state: the queue of vertices to visit with their parent edges, the represented blocks,
the accepted edges, and the probability of the coins so far. -/
abbrev PState (W : Blocks n) (J : SimpleGraph W.Vtx) [DecidableRel J.Adj] : Type :=
  List (W.Vtx × Fin (W.M J)) × Finset (Fin n) × Finset (Fin (W.M J)) × ℚ

/-- The coins of one vertex's slots (B.3, p.28): each slot is activated independently with probability
`p = α/(d + α)`, `d = Δ_{block w} − 1`. An activated slot rejects (`none`) when it is padding, an edge outside
the task family `A`, or leads to an already represented block (a repeated vertex or block); otherwise its
other endpoint joins the queue. -/
noncomputable def slotCoins (A : Finset (Fin (W.M J))) (L : ℕ) (w : W.Vtx) (p : ℚ) :
    List (Option (Fin (W.M J))) → PState W J → Proc (Option (PState W J))
  | [], st => pure (some st)
  | e :: l, (Qu, Bl, Y, q) => do
    tick (L ^ 2)
    let act ← ratCoin p
    if act then do
      let q' ← qmul q p
      match e with
      | none => pure none
      | some a =>
        if a ∈ A ∧ (W.other J a w).1 ∉ Bl then
          slotCoins A L w p l (Qu ++ [(W.other J a w, a)], insert (W.other J a w).1 Bl, insert a Y, q')
        else pure none
    else do
      let np ← qsub 1 p
      let q' ← qmul q np
      slotCoins A L w p l (Qu, Bl, Y, q')

/-- Visit the queue in order, at most `k` vertices; every visited vertex draws all its slot coins. -/
noncomputable def visit (Δ : Fin n → ℕ) (A : Finset (Fin (W.M J))) (L : ℕ) :
    ℕ → PState W J → Proc (Option (PState W J))
  | 0, st => pure (some st)
  | _ + 1, ([], Bl, Y, q) => pure (some ([], Bl, Y, q))
  | k + 1, ((w, pe) :: Qu, Bl, Y, q) => do
    tick (L ^ 3)
    let d : ℚ := ((Δ w.1 : ℚ) - 1)
    let den ← qadd d alphaIT
    let p ← qdiv alphaIT den
    match ← slotCoins W J A L w p (W.slots J Δ w pe) (Qu, Bl, Y, q) with
    | none => pure none
    | some st => visit Δ A L k st

/-- The proposal `q_ι` of B.3, p.28 (with the side-dependent activation of B.8, p.33): contract the root
edge `c = u₀v₀`, visit `u₀` and `v₀` and then every activated child, in slot order; reject as above, and
reject a zero-mass record or one whose Prim replay on its accepted edge set does not return that set. At
most `n` vertices are visited, since blocks never repeat. When `Δ = 1` there are no slots and the root edge
is proposed with probability one. -/
noncomputable def itPropose (Δ : Fin n → ℕ) (L : ℕ) (S : Finset (Fin (W.M J))) (c : Fin (W.M J)) :
    Proc (Option (Leaf (W.M J) × ℚ)) := do
  let u₀ := (W.edge J c).1
  let v₀ := (W.edge J c).2
  match ← W.visit J Δ S L (n + 1) ([(u₀, c), (v₀, c)], {u₀.1, v₀.1}, {c}, 1) with
  | none => pure none
  | some (_, _, Y, q) =>
    tick ((W.M J + 1) * L ^ 3)
    let t := leafOf (W.primNext J S c) c Y
    if t.1 = Y ∧ ¬ W.itDead J S t then pure (some (t, q)) else pure none

/-- `acc ∏_{j∈l} s_j` with `s_j = 1 − B_j` for the child tasks `j` of a list, charged. -/
noncomputable def sChildren (Δ : Fin n → ℕ) :
    List (Finset (Fin (W.M J)) × Fin (W.M J)) → ℚ → Proc ℚ
  | [], acc => pure acc
  | j :: l, acc => do
    let B ← charge (W.budgetC J Δ j.1 j.2)
    let s ← qsub 1 B
    let acc' ← qmul acc s
    sChildren Δ l acc'

/-- The exact local operation (B.3, p.29; B.7, p.32): thin by `a_T / [B_ι q_ι(T) ∏_{j∈C_T} s_j]`, the
left side of (25), where `a_T = ∏_{i∈S_T} π_i(u_i)` ((13), (28)); on success install the discovered vertex in
each represented block (`0` elsewhere). A zero-mass record is rejected. -/
noncomputable def itLocal (Δ : Fin n → ℕ) (L : ℕ) (S : Finset (Fin (W.M J))) (c : Fin (W.M J))
    (t : Leaf (W.M J)) (q : ℚ) : Proc (Option W.Sel) := do
  tick (L ^ 3)
  if W.itDead J S t then pure none else do
    let a ← (W.itCSP J).uProd t.1
      ((List.finRange n).filter fun i => i ∈ W.represented J t.1) 1
    let B ← charge (W.budgetC J Δ S c)
    let d0 ← qmul B q
    let den ← W.sChildren J Δ (chain (W.itRestore J S c t) (W.itR J S c t)) d0
    let ratio ← qdiv a den
    let keep ← ratCoin ratio
    if keep then do
      tick L
      pure (some fun i => ((W.itCSP J).pin t.1 i).getD 0)
    else pure none

/-- The input length: the blocks, the graph (two indices of `Nat.size |V|` bits per ordered adjacent pair),
the weights, and `n` bits for the block sides of (iii). -/
noncomputable def itInputSize : ℕ :=
  n + Fintype.card W.Vtx +
    (Finset.univ.filter fun p : W.Vtx × W.Vtx => J.Adj p.1 p.2).card *
      (2 * (Fintype.card W.Vtx).size + 1) +
    (∑ i, ∑ x, bits (W.π i x)) + n

/-- The application data of Appendix B for the degree bounds `Δ`: charges `L³` per search step, `L` per
constraint test and per configuration move, `L = itInputSize`. -/
noncomputable def itData (Δ : Fin n → ℕ) : ExecData (W.itCSP J).toCSP where
  next := W.primNext J
  rest := W.itR J
  restore := W.itRestore J
  vars _ _ t := W.represented J t.1
  event := W.itEvent J
  budget A a := (W.budgetC J Δ A a).1
  budgetCost A a := (W.budgetC J Δ A a).2
  propose := W.itPropose J Δ (W.itInputSize J)
  localOp := W.itLocal J Δ (W.itInputSize J)
  stepCost := W.itInputSize J ^ 3
  testCost := W.itInputSize J
  moveCost := W.itInputSize J

/-- The degree bounds of parts (i), (ii): `∆` after the deletions, for every block. -/
noncomputable def DeltaAll : Fin n → ℕ := fun _ => W.kmaxDeg J

/-- The degree bounds of part (iii): `∆_X` after the deletions, for the side `X` of the block. -/
noncomputable def DeltaSide (side : Fin n → Bool) : Fin n → ℕ := W.sideDeg J side

/-- The perfect sampler of Theorem 2.13 for the degree bounds `Δ`: sequential insertion of the kept edges
from independent draws `X_i ∼ π_i`. -/
noncomputable def itSampler (Δ : Fin n → ℕ) : Proc W.Sel := (W.itData J Δ).sampler

/-- The FPRAS for the probability that the selection is independent, with the work cap
`K ((L + bits ε + 1) ⌈1/ε⌉)^d` of p.25. -/
noncomputable def itFpras (Δ : Fin n → ℕ) (K d : ℕ) (ε : ℚ) : Proc ℚ :=
  (W.itData J Δ).fpras (K * ((W.itInputSize J + bits ε + 1) * ⌈(1 / ε : ℚ)⌉₊) ^ d) ε

/-- The FPRAS for the number of independent transversals in the uniform case (p.30): the estimate of the
probability times `∏_i |V_i|`, by one charged multiplication. -/
noncomputable def itCount (Δ : Fin n → ℕ) (K d : ℕ) (ε : ℚ) : Proc ℚ := do
  let z ← W.itFpras J Δ K d ε
  qmul z (∏ i, (W.b i + 1 : ℚ))

end Blocks

end SamplingLLL.Supplement


