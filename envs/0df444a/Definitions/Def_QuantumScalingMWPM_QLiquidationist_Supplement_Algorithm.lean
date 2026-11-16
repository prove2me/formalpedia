-- Prove2me | Definitions.Def_QuantumScalingMWPM_QLiquidationist_Supplement_Algorithm
-- name    : QuantumScalingMWPM_QLiquidationist_Supplement_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:23:46.962389+00:00
-- url     : https://prove2.me/theorems/7a2117af-3945-4c48-bb43-ddc3a34938a5
-- title:
--   QLIQUIDATIONIST scaling, liquidation, quantum search, dummies and finalization
-- statement:
--   Let $G$ be a simple graph on $n$ vertices, with arbitrary integer edge weights $\widehat w$ and a threshold $\tau$. This module defines QLIQUIDATIONIST as a concrete transition system, using the published graph, blossom, and quantum path-search definitions.
--
--   To process signed weights, set $a=\min(0,\min_{e\in E}\widehat w(e))$, taking $a=0$ when there are no edges, and use $\widehat w(e)-a$. Let $N$ be the maximum shifted edge weight, with $N=0$ on an empty edge set. Choose the valid strict bound $W=N+1$, set $\overline w=(\lfloor n/2\rfloor+1)(\widehat w-a)$, and use
--   $$L=\left\lceil\log_2((\lfloor n/2\rfloor+1)W)\right\rceil.$$
--   This preserves every signed input and the relative weight of every perfect matching; the strict bound preserves the most significant bit at powers of two.
--
--   The initial state has empty matching and blossom family and zero weights and duals. Every scale resets the matching, performs $w\leftarrow2(w'+b_i)$, $y\leftarrow2y'+3$, $z\leftarrow2z'$, liquidates large inherited blossoms, reweights by subtracting endpoint duals and resets vertex duals, then liquidates the small inherited blossoms. Each maximal old small blossom is processed in any order: PQSEARCH under Criterion 1 starts from its free vertices of maximum dual value $Y$ and stops after its first augmentation step or $Y-Y'$ dual adjustments, where $Y'$ is the next free dual value clamped below by zero.
--
--   FREEVERTEXREDUCTION makes exactly $\tau$ calls of the published QSEARCHONE. Both of its Algorithm 1 executions are expanded into the published transitions, including every correct quantum search answer. The path lifting, augmentation, rebasing, promotion, dual updates and root dissolution are exactly those of the published routine. Thus internal nontermination or a stuck search is visible to the correctness statement.
--
--   Perfection deletes free old dummies and pairs every remaining free original vertex with a new dummy of dual $\tau$ through a zero-weight matched edge. After the last scale all dummies are deleted, their partners become free, and Criterion 3 Edmonds searches continue until every original vertex is matched. The output mate array is restricted to the original vertices.
--
--   All choices left free by the source remain free: small-blossom order, augmenting paths, maximal shrinking sequences, enumeration orders, and correct search answers. States contain only working data and control information. Optimality, dual invariants, progress and termination are theorem obligations, not fields of an assumed model.
--
--   **Formalization Note** A fixed carrier of $n(L+1)$ slots supplies one fresh dummy slot per original vertex per scale. Absent slots are isolated; their searches have no effect on present vertices. Duals are integers; liquidation divides even reachable blossom duals by two exactly. The first five classical scale actions are combined into one transition because they have no nondeterministic choices affecting the resulting state.
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), §4.1, pp. 23–25; Figure 3 p. 7, Algorithms 1–2 pp. 14–15, §§3.3–3.5 pp. 20–22. Ran Duan, Seth Pettie, Hsin-Hao Su, Scaling Algorithms for Weighted Matching in General Graphs, ACM TALG 14(1):8 (2018), DOI 10.1145/3155301; delegated procedures read in author version arXiv:1411.1919v6 (9 October 2017), https://arxiv.org/abs/1411.1919v6, §1.1 footnote 1 p. 2, Figure 2 p. 8, §3 pp. 11–12, Figure 5 p. 13.

import Mathlib
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_Supplement_EdmondsSearch
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_PathSearch

/-!
# QLIQUIDATIONIST (§4.1) as a nondeterministic transition system

Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), §4.1,
pp. 23–25; the procedures the page delegates to Duan, Pettie and Su [13] ("performed exactly as
described by Duan, Pettie, and Su in [13]", p. 25) are taken from R. Duan, S. Pettie, H.-H. Su,
*Scaling algorithms for weighted matching in general graphs*, arXiv:1411.1919v6 (the author version of ACM TALG 14(1):8,
2018; DOI 10.1145/3155301): Figure 2 (EdmondsSearch, p. 8), Criteria 1–3 (p. 7), Figure 5 (Liquidationist, p. 13),
§3 (pp. 11–12), footnote 1 (p. 2).

**The algorithm.** Input: a simple graph `G` on `Fin n`, integer weights `ŵ`, a threshold `τ`.
* *Preprocessing.* If some edge weight is negative, every weight is shifted by `min_e ŵ(e)`
  ([13], footnote 1, p. 2: "we can simply subtract `min_e ŵ(e)` from every edge weight"); the
  shift changes every perfect matching's weight by the same amount. `w̄ = (n/2 + 1)ŵ` on the shifted
  weights (p. 23); `N` is the largest shifted edge weight; choose the valid strict bound `W = N + 1`.
  `L = ⌈log₂((n/2 + 1)W)⌉`, so every `w̄(e)` has at most `L` bits, including at powers of two; `b_i(e)` is bit `L − i` of `w̄(e)` (bit 1 the
  most significant).
* Initially `y ← 0, z ← 0, w ← 0, Ω ← ∅` (p. 24). Each scale `i = 1, …, L` (pp. 24–25, [13] Fig. 5):
  1. *Initialization and scaling:* `M ← ∅`, `Ω′ ← Ω`, `Ω ← ∅`, `w(e) ← 2(w′(e) + b_i(e))`,
     `y(u) ← 2y′(u) + 3`, `z(B′) ← 2z′(B′)`;
  2. *large-blossom liquidation:* `y(u) += z(B)/2` for `u ∈ B` for every old `B` with `|B| ≥ τ`;
  3. *reweighting:* `w(u, v) ← w(u, v) − y(u) − y(v)`, then `y ← 0`;
  4. *SMALLBLOSSOMLIQUIDATION:* liquidate the remaining (small) old blossoms; then for each maximal
     old small blossom `B′`, while `Y = max{y(u) : u ∈ B′ free} > 0`, run PQSEARCH(`F`) under
     Criterion 1 from `F = {u ∈ B′ free : y(u) = Y}` until an augmentation or until `Y − Y′` dual
     adjustments, `Y′ = max(0, max{y(u) : u ∈ B′ \ F free})` ([13] Fig. 5, step 6);
  5. *FREEVERTEXREDUCTION:* exactly `τ` calls of the published `QSearchOne` (Criterion 2);
  6. *Perfection:* delete the free dummy vertices; for every remaining free `u` add a dummy `û` with
     `y(û) = τ`, `w(u, û) = 0`, `(u, û)` matched.
  After the last scale all dummies are deleted and PQSEARCH (Criterion 3) is called from the set of
  free vertices until it is empty (FINALIZATION).
* *PQSEARCH* is EdmondsSearch of [13] Figure 2 (PQSEARCH is "an implementation of EdmondsSearch",
  p. 9; its priority queue only affects running time): repeat Augmentation (while an eligible
  augmenting path from a free `F`-vertex exists in `Ĝ_elig = G_elig/Ω`, augment along its lift),
  Blossom Shrinking (a maximal set of nested blossoms on `V̂_out`), Dual Adjustment (`y ∓ 1` on
  `V_out`/`V_in`, `z ± 2` on root blossoms inside `V_out`/`V_in`), Blossom Dissolution (repeatedly
  dissolve root blossoms with `z = 0`); halt after the first Augmentation step that augments.

**Nondeterminism.** Every choice [13] leaves free is a nondeterministic step: which augmenting
path is taken, which maximal blossom family is shrunk, the order of the maximal small blossoms,
the enumeration order `ord` of each `QSearchOne` call, and every answer of every quantum search,
which ranges over the correct answers only (the published `QSearchOne` / `Alg1Step`: a marked
item whenever one exists, `⊥` only when none exists). Statements quantify over every run.

**Formalization Note.**
* No subroutine is assumed to return: both Algorithm 1 executions inside every `QSearchOne`
  are expanded into their published `Alg1Step` transitions. Progress and absence of infinite runs
  therefore include these internal quantum-search choices.
* The valid bound `W = N + 1` is chosen from the finite input; this avoids dropping a top bit
  at powers of two. It imposes no restriction on the original signed integer weights.
* *Vertices.* All graphs of the run live on `Fin (nV G ŵ)`, `nV = n(L + 1)`: indices `< n` are the
  vertices of `G`; index `n·i + u` is the dummy `û` created for `u` at scale `i`. `dum` is the set
  of dummies currently present; the graph `scaleGraph G dum` has the edges of `G` and the pendant
  edges `(u, û)`, `û ∈ dum`. Slots of absent dummies are isolated vertices: no path or edge
  touches them, and the only effect of their presence on a `QSearchOne` call is that they are
  labelled as trivial free OUT roots and their `y` changes (reset to `τ` when the dummy is
  created); no state of a present vertex depends on them.
* Duals are integers (`y : Fin N → ℤ`, `z : Finset (Fin N) → ℤ`, as in [13] Property 1(1)); `z(B)/2`
  is `Int` division, exact on the even values `z` takes ([13] Lemma 3.1). Off the blossom family
  `z` is `0`, so after step 4's liquidations `z ≡ 0`.
* Weights `w` and the bits `b_i` are functions on all unordered pairs; only pairs that are edges
  of the current graph are ever read (every eligibility criterion requires an edge).
-/

namespace QuantumScalingMWPM.QLiquidationist.Supplement

open scoped Classical
open QuantumScalingMWPM.QLiquidationist

noncomputable section

variable {n N : ℕ}

/-! ### Input preprocessing and scales -/

/-- The shift `min(0, min_{e ∈ E} ŵ(e))`: `0` for nonnegative weights, else the least weight
([13], footnote 1). -/
def weightShift (G : SimpleGraph (Fin n)) (ŵ : Sym2 (Fin n) → ℤ) : ℤ :=
  G.edgeFinset.fold min 0 ŵ

/-- The shifted weights `ŵ(e) − min(0, min ŵ)`, nonnegative on the edges. -/
def shiftedWeight (G : SimpleGraph (Fin n)) (ŵ : Sym2 (Fin n) → ℤ) : Sym2 (Fin n) → ℤ :=
  fun e => ŵ e - weightShift G ŵ

/-- `N`: the largest shifted edge weight (`0` without edges). -/
def weightBound (G : SimpleGraph (Fin n)) (ŵ : Sym2 (Fin n) → ℤ) : ℕ :=
  (G.edgeFinset.fold max 0 (shiftedWeight G ŵ)).toNat

/-- The extended weights `w̄(e) = (n/2 + 1)·ŵ(e)` (p. 23) of the shifted weights. -/
def extWeight (G : SimpleGraph (Fin n)) (ŵ : Sym2 (Fin n) → ℤ) : Sym2 (Fin n) → ℤ :=
  fun e => ((n / 2 : ℕ) + 1 : ℤ) * shiftedWeight G ŵ e

/-- The number of scales `L = ⌈log₂((n/2 + 1)W)⌉`, choosing the valid bound `W = N + 1`
for the shifted input. The strict bound preserves the leading bit at powers of two. -/
def numScales (G : SimpleGraph (Fin n)) (ŵ : Sym2 (Fin n) → ℤ) : ℕ :=
  Nat.clog 2 ((n / 2 + 1) * (weightBound G ŵ + 1))

/-- The vertex slots of the run: `n` vertices of `G` and `n` dummy slots per scale. -/
def nV (G : SimpleGraph (Fin n)) (ŵ : Sym2 (Fin n) → ℤ) : ℕ := n * (numScales G ŵ + 1)

theorem le_nV (G : SimpleGraph (Fin n)) (ŵ : Sym2 (Fin n) → ℤ) : n ≤ nV G ŵ :=
  Nat.le_mul_of_pos_right n (Nat.succ_pos _)

/-- The vertices of `G` are the slots `0, …, n − 1`. -/
def emb (G : SimpleGraph (Fin n)) (ŵ : Sym2 (Fin n) → ℤ) : Fin n → Fin (nV G ŵ) :=
  Fin.castLE (le_nV G ŵ)

/-- Extend a function on pairs of vertices of `G` to all pairs of slots (`0` off `G`'s vertices). -/
def origPairLift (n : ℕ) (f : Sym2 (Fin n) → ℤ) : Sym2 (Fin N) → ℤ :=
  Sym2.lift ⟨fun a b => if h : a.val < n ∧ b.val < n then f s(⟨a.val, h.1⟩, ⟨b.val, h.2⟩) else 0,
    by
      intro a b
      dsimp only
      by_cases h : a.val < n ∧ b.val < n
      · have h' : b.val < n ∧ a.val < n := ⟨h.2, h.1⟩
        rw [dif_pos h, dif_pos h', Sym2.eq_swap]
      · have h' : ¬ (b.val < n ∧ a.val < n) := fun h' => h ⟨h'.2, h'.1⟩
        rw [dif_neg h, dif_neg h']⟩

/-- The bit `b_i(e)` of scale `i` (`1 ≤ i ≤ L`): bit `L − i` of `w̄(e)`; `0` on dummy edges. -/
def scaleBits (G : SimpleGraph (Fin n)) (ŵ : Sym2 (Fin n) → ℤ) (i : ℕ) :
    Sym2 (Fin (nV G ŵ)) → ℤ :=
  origPairLift n fun e =>
    if Nat.testBit (extWeight G ŵ e).toNat (numScales G ŵ - i) then 1 else 0

/-! ### Graphs with dummy vertices -/

/-- The graph `G_i` of a scale: the edges of `G` on the slots `< n` and a pendant edge from the
owner `u` to every present dummy `û ∈ dum` (slot index `≡ u mod n`, `≥ n`). -/
def scaleGraph (G : SimpleGraph (Fin n)) (dum : Finset (Fin N)) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun a b =>
    (∃ h : a.val < n ∧ b.val < n, G.Adj ⟨a.val, h.1⟩ ⟨b.val, h.2⟩) ∨
    (b ∈ dum ∧ n ≤ b.val ∧ a.val < n ∧ a.val = b.val % n)

/-- The dummy slot `n·i + u` created for the vertex `u` at scale `i`. -/
def slot (n : ℕ) (i : ℕ) (v : Fin N) : Fin N :=
  ⟨(n * i + v.val) % N, Nat.mod_lt _ (Nat.zero_lt_of_lt v.isLt)⟩

/-- The owner `u` of a dummy slot. -/
def owner (n : ℕ) (d : Fin N) : Fin N :=
  ⟨d.val % n, lt_of_le_of_lt (Nat.mod_le _ _) d.isLt⟩

/-! ### State -/

/-- Program counter: start of a scale, step 6 (small blossoms), inside a PQSEARCH, FREEVERTEX
REDUCTION, Perfection, FINALIZATION, halted. -/
inductive Phase where
  | scaleStart
  | small
  | search
  | fvr
  | qpath1
  | qpath3
  | perf
  | final
  | done
  deriving DecidableEq

/-- The state of a run. `todo`: maximal old small blossoms still to process in step 6. Inside a
PQSEARCH: `F` its source set, `crit3` the eligibility criterion (`false`: Criterion 1, `true`:
Criterion 3), `lim` the bound on dual adjustments (`Y − Y′` in step 6, none in FINALIZATION),
`nadj` the dual adjustments done, `found` whether the current Augmentation step has augmented,
`ret` the phase to return to. `calls`: `QSearchOne` calls done in FREEVERTEXREDUCTION.
`qOrd` and `q` store the enumeration order and current published Algorithm 1 state in Tasks 1/3. -/
structure QLState (N : ℕ) where
  M : Mate N
  fam : Family N
  y : Fin N → ℤ
  z : Finset (Fin N) → ℤ
  w : Sym2 (Fin N) → ℤ
  dum : Finset (Fin N)
  scale : ℕ
  pc : Phase
  todo : List (Finset (Fin N))
  F : Finset (Fin N)
  crit3 : Bool
  lim : Option ℕ
  nadj : ℕ
  found : Bool
  ret : Phase
  calls : ℕ
  qOrd : Finset (Fin N) → List (Fin N)
  q : Alg1State N

/-- Initially `y ← 0, z ← 0, w ← 0, Ω ← ∅`, `M = ∅`, no dummies (p. 24). -/
def qlInit (N : ℕ) : QLState N where
  M := fun _ => none
  fam := []
  y := fun _ => 0
  z := fun _ => 0
  w := fun _ => 0
  dum := ∅
  scale := 0
  pc := .scaleStart
  todo := []
  F := ∅
  crit3 := false
  lim := none
  nadj := 0
  found := false
  ret := .done
  calls := 0
  qOrd := Finset.toList
  q := alg1Init []

/-! ### Steps 1–5 of a scale -/

/-- `Σ_{B ∈ Ω, u ∈ B} z(B)/2`: the increase of `y(u)` when the blossoms of `Ω` are liquidated. -/
def liquidAmt (Ω : Family N) (z : Finset (Fin N) → ℤ) (u : Fin N) : ℤ :=
  ((Ω.filter fun B => decide (u ∈ B.verts)).map fun B => z B.verts / 2).sum

/-- Initialization and scaling, large-blossom liquidation, reweighting and the liquidation of the
small old blossoms (pp. 24–25; [13] Fig. 5 steps 1–5), with the list of maximal old small
blossoms for step 6. -/
def scaleSetup (τ : ℕ) (bits : Sym2 (Fin N) → ℤ) (s : QLState N) : QLState N :=
  let Ω' := s.fam
  let w2 : Sym2 (Fin N) → ℤ := fun e => 2 * (s.w e + bits e)
  let y2 : Fin N → ℤ := fun u => 2 * s.y u + 3
  let z2 : Finset (Fin N) → ℤ := fun S => 2 * s.z S
  let large := Ω'.filter fun B => decide (τ ≤ B.verts.card)
  let small := Ω'.filter fun B => decide (B.verts.card < τ)
  let y3 : Fin N → ℤ := fun u => y2 u + liquidAmt large z2 u
  let w4 : Sym2 (Fin N) → ℤ :=
    Sym2.lift ⟨fun u v => w2 s(u, v) - y3 u - y3 v, by intro u v; dsimp only; rw [Sym2.eq_swap]; ring⟩
  let y5 : Fin N → ℤ := fun u => liquidAmt small z2 u
  let maxSmall := ((small.filter fun B : BRec N =>
      decide (∀ B' ∈ small, B.verts ⊆ B'.verts → B'.verts = B.verts)).map BRec.verts).dedup
  { s with M := fun _ => none, fam := [], w := w4, y := y5, z := fun _ => 0, todo := maxSmall,
           pc := .small }

/-! ### Perfection and FINALIZATION -/

/-- Perfection at scale `s.scale` (p. 25): free dummies are deleted; every free vertex `u` of `G`
gets the dummy `û = slot u`, `y(û) = τ`, `w(u, û) = 0`, `(u, û)` matched. -/
def perfection (n : ℕ) (τ : ℕ) (s : QLState N) : QLState N :=
  let i := s.scale
  let keep := s.dum.filter fun d => s.M d ≠ none
  let freeO := Finset.univ.filter fun v : Fin N => v.val < n ∧ s.M v = none
  let new := freeO.image (slot n i)
  { s with
    dum := keep ∪ new
    M := fun v => if v ∈ freeO then some (slot n i v) else if v ∈ new then some (owner n v)
      else s.M v
    y := fun v => if v ∈ new then (τ : ℤ) else s.y v
    w := fun e => if ∃ v ∈ freeO, e = s(v, slot n i v) then 0 else s.w e
    pc := .scaleStart }

/-- Start of FINALIZATION: all dummies are deleted (their partners become free). -/
def finalStart (n : ℕ) (s : QLState N) : QLState N :=
  { s with
    M := fun v => match s.M v with
      | some u => if v.val < n ∧ u.val < n then some u else none
      | none => none
    dum := ∅
    pc := .final }

/-- The free vertices of `B` (`M[u] = ⊥`). -/
def freeIn (M : Mate N) (B : Finset (Fin N)) : Finset (Fin N) := B.filter fun u => M u = none

/-! ### The transition system -/

/-- One step of QLIQUIDATIONIST on `(G, ŵ)` with threshold `τ`. -/
inductive QLStep (G : SimpleGraph (Fin n)) (ŵ : Sym2 (Fin n) → ℤ) (τ : ℕ) :
    QLState (nV G ŵ) → QLState (nV G ŵ) → Prop
  /-- Start of scale `i = s.scale + 1 ≤ L`: steps 1–5. -/
  | nextScale (s : QLState (nV G ŵ)) (order : List (Finset (Fin (nV G ŵ)))) :
      s.pc = .scaleStart → s.scale < numScales G ŵ →
      order.Perm (scaleSetup τ (scaleBits G ŵ (s.scale + 1)) s).todo →
      QLStep G ŵ τ s
        { scaleSetup τ (scaleBits G ŵ (s.scale + 1)) { s with scale := s.scale + 1 }
          with todo := order }
  /-- After the last scale: delete all dummies and enter FINALIZATION. -/
  | toFinal (s : QLState (nV G ŵ)) :
      s.pc = .scaleStart → numScales G ŵ ≤ s.scale →
      QLStep G ŵ τ s (finalStart n s)
  /-- Step 6: the current maximal old small blossom has no free vertex with `y > 0`. -/
  | smallPop (s : QLState (nV G ŵ)) (B : Finset (Fin (nV G ŵ))) (rest) :
      s.pc = .small → s.todo = B :: rest → (freeIn s.M B).fold max 0 s.y ≤ 0 →
      QLStep G ŵ τ s { s with todo := rest }
  /-- Step 6 is finished: switch to FREEVERTEXREDUCTION. -/
  | smallEnd (s : QLState (nV G ŵ)) :
      s.pc = .small → s.todo = [] →
      QLStep G ŵ τ s { s with pc := .fvr, calls := 0 }
  /-- Step 6: `Y = max{y(u) : u ∈ B′ free} > 0`; run PQSEARCH(`F`) under Criterion 1 for at most
  `Y − Y′` dual adjustments. -/
  | smallSearch (s : QLState (nV G ŵ)) (B : Finset (Fin (nV G ŵ))) (rest) :
      s.pc = .small → s.todo = B :: rest → 0 < (freeIn s.M B).fold max 0 s.y →
      QLStep G ŵ τ s
        { s with pc := .search,
                 F := (freeIn s.M B).filter fun u => s.y u = (freeIn s.M B).fold max 0 s.y,
                 crit3 := false,
                 lim := some ((freeIn s.M B).fold max 0 s.y -
                   ((freeIn s.M B).filter fun u => s.y u ≠ (freeIn s.M B).fold max 0 s.y).fold
                     max 0 s.y).toNat,
                 nadj := 0, found := false, ret := .small }
  /-- PQSEARCH, Augmentation: augment along (the lift of) an eligible augmenting path from `F`. -/
  | augment (s : QLState (nV G ŵ)) (P : List (Fin (nV G ŵ) × Fin (nV G ŵ))) :
      s.pc = .search →
      IsEligAugFromF (scaleGraph G s.dum)
        (EligC s.crit3 (scaleGraph G s.dum) s.w s.fam s.y s.z) s.M s.fam s.F P →
      QLStep G ŵ τ s
        { s with M := QLiquidationist.augment s.M (liftG s.fam P),
                 fam := rebase (QLiquidationist.augment s.M (liftG s.fam P)) s.fam,
                 found := true }
  /-- PQSEARCH halts after the first Augmentation step that augmented. -/
  | halt (s : QLState (nV G ŵ)) :
      s.pc = .search → s.found = true →
      (¬ ∃ P, IsEligAugFromF (scaleGraph G s.dum)
        (EligC s.crit3 (scaleGraph G s.dum) s.w s.fam s.y s.z) s.M s.fam s.F P) →
      QLStep G ŵ τ s { s with pc := s.ret }
  /-- PQSEARCH with no augmenting path: Blossom Shrinking (a maximal contraction sequence `news`),
  Dual Adjustment, Blossom Dissolution; return when the bound `lim` is reached. -/
  | dual (s : QLState (nV G ŵ)) (news : Family (nV G ŵ)) :
      s.pc = .search → s.found = false →
      (¬ ∃ P, IsEligAugFromF (scaleGraph G s.dum)
        (EligC s.crit3 (scaleGraph G s.dum) s.w s.fam s.y s.z) s.M s.fam s.F P) →
      IsContractionSeqF (scaleGraph G s.dum)
        (EligC s.crit3 (scaleGraph G s.dum) s.w s.fam s.y s.z) s.M s.F s.fam news →
      (∀ u v,
        IsOutF (scaleGraph G s.dum) (EligC s.crit3 (scaleGraph G s.dum) s.w s.fam s.y s.z) s.M
          (s.fam ++ news) s.F u →
        IsOutF (scaleGraph G s.dum) (EligC s.crit3 (scaleGraph G s.dum) s.w s.fam s.y s.z) s.M
          (s.fam ++ news) s.F v →
        rootSet (s.fam ++ news) u ≠ rootSet (s.fam ++ news) v → s.M u ≠ some v →
        ¬ EligC s.crit3 (scaleGraph G s.dum) s.w s.fam s.y s.z u v) →
      QLStep G ŵ τ s
        (let E := EligC s.crit3 (scaleGraph G s.dum) s.w s.fam s.y s.z
         let Φ := s.fam ++ news
         let isOut := IsOutF (scaleGraph G s.dum) E s.M Φ s.F
         let isIn := IsInF (scaleGraph G s.dum) E s.M Φ s.F
         let z' := adjustZ Φ (zAfterPromotion news s.z) isOut isIn
         { s with y := adjustY s.y isOut isIn, z := z', fam := dissolveAll Φ z',
                  nadj := s.nadj + 1,
                  pc := if s.lim = some (s.nadj + 1) then s.ret else .search })
  /-- Start the next QSearchOne call with any valid enumeration order. -/
  | fvrStart (s : QLState (nV G ŵ))
      (ord : Finset (Fin (nV G ŵ)) → List (Fin (nV G ŵ))) :
      s.pc = .fvr → s.calls < τ → ValidOrd ord →
      QLStep G ŵ τ s { s with pc := .qpath1, qOrd := ord, q := alg1Init s.fam }
  /-- One published Algorithm 1 step of Task 1. All search answers are correct by Alg1Step. -/
  | task1Step (s : QLState (nV G ŵ)) (t : Alg1State (nV G ŵ)) :
      s.pc = .qpath1 → s.q.done = false →
      Alg1Step (scaleGraph G s.dum) s.w s.M s.y s.fam s.qOrd s.q t →
      QLStep G ŵ τ s { s with q := t }
  /-- Task 2: lift and augment the paths, rebase the family, then start Task 3. -/
  | task2 (s : QLState (nV G ŵ)) :
      s.pc = .qpath1 → s.q.done = true →
      QLStep G ŵ τ s
        (let M₂ := augmentAll s.M (s.q.psi.map (liftG s.fam))
         let Ω₂ := rebase M₂ s.fam
         { s with M := M₂, fam := Ω₂, pc := .qpath3, q := alg1Init Ω₂ })
  /-- One published Algorithm 1 step of Task 3. -/
  | task3Step (s : QLState (nV G ŵ)) (t : Alg1State (nV G ŵ)) :
      s.pc = .qpath3 → s.q.done = false →
      Alg1Step (scaleGraph G s.dum) s.w s.M s.y s.fam s.qOrd s.q t →
      QLStep G ŵ τ s { s with q := t }
  /-- Finish the published QSearchOne: promote the temporary family, initialize the new z-values,
  adjust the duals using Task 3's labels and dissolve zero-valued roots. -/
  | task45 (s : QLState (nV G ŵ)) :
      s.pc = .qpath3 → s.q.done = true →
      QLStep G ŵ τ s
        (let news := s.q.fam.drop s.fam.length
         let isOut := fun v => s.q.uio v = .out
         let isIn := fun v => s.q.uio v = .inn
         let z₄ := adjustZ s.q.fam (zAfterPromotion news s.z) isOut isIn
         { s with y := adjustY s.y isOut isIn, z := z₄,
                  fam := dissolveZero s.q.fam z₄, pc := .fvr, calls := s.calls + 1 })
  /-- FREEVERTEXREDUCTION is finished after `τ` calls. -/
  | fvrEnd (s : QLState (nV G ŵ)) :
      s.pc = .fvr → τ ≤ s.calls →
      QLStep G ŵ τ s { s with pc := .perf }
  /-- Perfection, then the next scale. -/
  | perf (s : QLState (nV G ŵ)) :
      s.pc = .perf →
      QLStep G ŵ τ s (perfection n τ s)
  /-- FINALIZATION: no free vertex remains; halt. -/
  | finEnd (s : QLState (nV G ŵ)) :
      s.pc = .final → (∀ v : Fin (nV G ŵ), v.val < n → s.M v ≠ none) →
      QLStep G ŵ τ s { s with pc := .done }
  /-- FINALIZATION: PQSEARCH under Criterion 3 from the set of free vertices. -/
  | finSearch (s : QLState (nV G ŵ)) :
      s.pc = .final → (∃ v : Fin (nV G ŵ), v.val < n ∧ s.M v = none) →
      QLStep G ŵ τ s
        { s with pc := .search,
                 F := Finset.univ.filter fun v : Fin (nV G ŵ) => v.val < n ∧ s.M v = none,
                 crit3 := true, lim := none, nadj := 0, found := false, ret := .final }

/-- `s` is a state of some run of QLIQUIDATIONIST. -/
def QLReach (G : SimpleGraph (Fin n)) (ŵ : Sym2 (Fin n) → ℤ) (τ : ℕ) (s : QLState (nV G ŵ)) :
    Prop :=
  Relation.ReflTransGen (QLStep G ŵ τ) (qlInit (nV G ŵ)) s

/-- The output of a halted run: the mate array restricted to the vertices of `G`. -/
def qlOutput (G : SimpleGraph (Fin n)) (ŵ : Sym2 (Fin n) → ℤ) (s : QLState (nV G ŵ)) : Mate n :=
  fun v => match s.M (emb G ŵ v) with
    | some u => if h : u.val < n then some ⟨u.val, h⟩ else none
    | none => none

/-! ### Sanity checks -/

/-- On the vertices of `G` the scale graph is `G` itself, whatever dummies are present. -/
example (G : SimpleGraph (Fin n)) (ŵ : Sym2 (Fin n) → ℤ) (dum : Finset (Fin (nV G ŵ)))
    (a b : Fin n) : (scaleGraph G dum).Adj (emb G ŵ a) (emb G ŵ b) ↔ G.Adj a b := by
  simp only [scaleGraph, SimpleGraph.fromRel_adj, emb, Fin.val_castLE]
  constructor
  · rintro ⟨-, (⟨h, hab⟩ | ⟨-, hb, -⟩) | (⟨h, hba⟩ | ⟨-, ha, -⟩)⟩
    · exact hab
    · exact absurd b.isLt (by omega)
    · exact hba.symm
    · exact absurd a.isLt (by omega)
  · intro h
    refine ⟨fun he => G.ne_of_adj h (Fin.castLE_injective _ he), Or.inl (Or.inl ⟨⟨a.isLt, b.isLt⟩, h⟩)⟩

/-- A dummy slot of scale `i ≥ 1` is owned by its vertex: `owner (slot i u) = u`. -/
example (n N i : ℕ) (u : Fin N) (hu : u.val < n) (hN : n * i + u.val < N) :
    owner n (slot n i u) = u := by
  ext
  simp only [owner, slot, Nat.mod_eq_of_lt hN]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hu]

/-- With largest shifted weight 2 on four vertices, choose W = 3: L = ceil(log₂ 9) = 4. -/
example : Nat.clog 2 ((4 / 2 + 1) * (2 + 1)) = 4 := by decide

/-- The empty graph has no vertex slots at all. -/
example (ŵ : Sym2 (Fin 0) → ℤ) : nV (⊥ : SimpleGraph (Fin 0)) ŵ = 0 := by simp [nV]

end

end QuantumScalingMWPM.QLiquidationist.Supplement


