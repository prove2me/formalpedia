-- Prove2me | Definitions.Def_HypergraphUnreliability_FPRAS_Contraction
-- name    : HypergraphUnreliability_FPRAS_Contraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:42.875483+00:00
-- url     : https://prove2.me/theorems/c4f7d36c-9467-4a77-b20f-58209c73603b
-- title:
--   The marked contraction process with paired heads, its safe and absorbing variants, and the terminal reward
-- statement:
--   A **marked state** $x$ is a partition of the original vertices into blocks, each with one distinguished original vertex, its **representative**; $R(x)$ is the set of representatives and $K(x)=|R(x)|$. Initially all blocks are singletons.
--
--   Each original edge $e$ has two labeled copies. Its current **endpoints** are the blocks meeting $e$, and it is a **nonloop** if there are at least two. For a nonloop, copy $0$ has the endpoint with the smallest representative as **head** and copy $1$ the one with the largest. A **contraction** merges all endpoints and retains the head representative. The rule depends only on the state and the copy label.
--
--   With positive rates $r$, each nonloop copy of $e$ has rate $r_e/2$. For a pair $w$ of original vertices, a copy is **safe** if its contraction retains both labels of $w$ and **killing** otherwise; $s_w(x)$ and $\kappa_w(x)$ are the total safe and killing rates.
--
--   1. The **original process** $P$ has every nonloop copy at its rate, rates adding when labels induce the same transition.
--   2. The **safe process** $Q_w$ retains safe copies and suppresses killing ones; all labels are reexamined at every new state.
--   3. The **absorbing process** $R_w$ retains safe copies and moves a live state to a cemetery at rate $\kappa_w(x)-\Lambda$; the cemetery is absorbing.
--
--   The **terminal reward** is $g(x)=\binom n2/\binom{K(x)}2$ at a live state and $g=0$ at the cemetery, and the estimator (5.2) for a protected pair $w$ is
--   $$X=\frac{\binom n2}{\binom{K(X_T)}{2}}\exp\Bigl(-\int_0^T\kappa_w(X_t)\,dt\Bigr).$$
--
--   The unit-rate process of §§3–8 is the case $r\equiv1$, and the weighted process of §9.3 is the case $r=r^\prime$.
--
--   **Formalization Note** A marked state is stored as the map sending each vertex to its representative, as in the proof of Lemma 8.2. A live state with $K\le1$ is never reached by $R_w$ or $Q_w$; there the division by zero gives $0$.
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), §3, p. 5; §4, pp. 5–6; Definition 6.1, p. 7; §9.3, p. 14

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Hypergraph
import Definitions.Def_HypergraphUnreliability_FPRAS_JumpChain

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

/-- A marked state: a partition of the original vertices into blocks, each with one distinguished
original vertex, its representative (§3, p. 5). It is stored as the map sending each vertex to the
representative of its block, as in the proof of Lemma 8.2 (p. 11). -/
abbrev MarkedState (n : ℕ) := {f : Fin n → Fin n // ∀ v, f (f v) = f v}

/-- An unordered pair of original vertices. -/
abbrev VertexPair (n : ℕ) := {w : Finset (Fin n) // w.card = 2}

namespace MarkedState

variable {n : ℕ}

/-- The initial state, all blocks singletons. -/
def init : MarkedState n := ⟨id, fun _ => rfl⟩

/-- The representative set `R(x)`. -/
def reps (x : MarkedState n) : Finset (Fin n) := Finset.univ.image x.1

/-- The number `K(x) = |R(x)|` of blocks. -/
def K (x : MarkedState n) : ℕ := (reps x).card

/-- The block partition of `x`, forgetting the marks. -/
def blocks (x : MarkedState n) : Setoid (Fin n) := Setoid.ker x.1

/-- The block represented by `a`. -/
def block (x : MarkedState n) (a : Fin n) : Finset (Fin n) := Finset.univ.filter (fun v => x.1 v = a)

end MarkedState

namespace LabeledHypergraph

variable {n : ℕ} {E : Type}

/-- The current endpoints of `e` in `x`, each block named by its representative. -/
def endpoints (H : LabeledHypergraph n E) (x : MarkedState n) (e : E) : Finset (Fin n) :=
  (H.inc e).image x.1

/-- The edge is a nonloop in the quotient: it has at least two endpoints. -/
def IsNonloop (H : LabeledHypergraph n E) (x : MarkedState n) (e : E) : Prop :=
  2 ≤ (H.endpoints x e).card

/-- The head of a copy among a nonempty endpoint set: copy `false` (the source's copy 0) has the
smallest representative as head, copy `true` (copy 1) the largest (§3, p. 5). The rule depends only
on the marked state and the copy label. -/
def headOf (ep : Finset (Fin n)) (h : ep.Nonempty) (c : Bool) : Fin n :=
  if c then ep.max' h else ep.min' h

theorem headOf_mem (ep : Finset (Fin n)) (h : ep.Nonempty) (c : Bool) : headOf ep h c ∈ ep := by
  unfold headOf
  split
  · exact Finset.max'_mem _ _
  · exact Finset.min'_mem _ _

/-- The contraction by the copy `(e, c)`: all endpoints of `e` merge, and the merged block retains
the head representative (§3, p. 5). For a loop the marked state is unchanged. -/
def contract (H : LabeledHypergraph n E) (x : MarkedState n) (e : E) (c : Bool) : MarkedState n :=
  ⟨fun v =>
      if hv : x.1 v ∈ H.endpoints x e then
        headOf (H.endpoints x e) ⟨_, hv⟩ c
      else x.1 v,
    by
      intro v
      have hfix : ∀ u ∈ H.endpoints x e, x.1 u = u := by
        intro u hu
        obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hu
        exact x.2 z
      by_cases hv : x.1 v ∈ H.endpoints x e
      · have hne : (H.endpoints x e).Nonempty := ⟨_, hv⟩
        have hh := headOf_mem (H.endpoints x e) hne c
        simp only [dif_pos hv]
        rw [dif_pos (by rw [hfix _ hh]; exact hh)]
      · simp only [dif_neg hv]
        rw [dif_neg (by rw [x.2 v]; exact hv), x.2 v]⟩

/-- The copy `(e, c)` is safe for the pair `w` in `x`: it is a nonloop copy whose contraction retains
both labels of `w` as representatives (§4, p. 5). -/
def IsSafe (H : LabeledHypergraph n E) (w : VertexPair n) (x : MarkedState n) (e : E) (c : Bool) :
    Prop :=
  H.IsNonloop x e ∧ w.1 ⊆ MarkedState.reps (H.contract x e c)

/-- The copy `(e, c)` is killing for `w` in `x`: it is a nonloop copy whose contraction deletes a
label of `w`. -/
def IsKilling (H : LabeledHypergraph n E) (w : VertexPair n) (x : MarkedState n) (e : E) (c : Bool) :
    Prop :=
  H.IsNonloop x e ∧ ¬ w.1 ⊆ MarkedState.reps (H.contract x e c)

variable [Fintype E] {R : Type} [Field R]

/-- The total safe rate `s_w(x)`: each safe copy of `e` has rate `r e / 2` ((4.1), p. 5, and §9.3,
p. 14; the unit-rate process is `r = 1`). -/
def safeRate (H : LabeledHypergraph n E) (r : E → R) (w : VertexPair n) (x : MarkedState n) : R :=
  ∑ e, ∑ c : Bool, if H.IsSafe w x e c then r e / 2 else 0

/-- The total killing rate `κ_w(x)` ((4.1), p. 5, and §9.3, p. 14). -/
def killRate (H : LabeledHypergraph n E) (r : E → R) (w : VertexPair n) (x : MarkedState n) : R :=
  ∑ e, ∑ c : Bool, if H.IsKilling w x e c then r e / 2 else 0

/-- The original process `P` (Definition 3.1, p. 5; §9.3, p. 14): every nonloop labeled copy of `e`
contracts at rate `r e / 2`, and rates add when distinct labels induce the same transition. -/
def originalRate (H : LabeledHypergraph n E) (r : E → R) (x y : MarkedState n) : R :=
  ∑ e, ∑ c : Bool, if H.IsNonloop x e ∧ H.contract x e c = y then r e / 2 else 0

/-- The safe process `Q_w` (Definition 4.2, p. 6; §9.3, p. 14): each safe copy keeps its rate, killing
copies are suppressed, and suppressed copies are reexamined at every new state. -/
def safeProcessRate (H : LabeledHypergraph n E) (r : E → R) (w : VertexPair n)
    (x y : MarkedState n) : R :=
  ∑ e, ∑ c : Bool, if H.IsSafe w x e c ∧ H.contract x e c = y then r e / 2 else 0

/-- The normalized absorbing process `R_w` (Definition 6.1, p. 7; §9.3, p. 14), on the live states
`some x` and the cemetery `none`: safe transitions keep their rates, a live state moves to the
cemetery at rate `κ_w(x) - Λ`, and the cemetery is absorbing. -/
def absorbingRate (H : LabeledHypergraph n E) (r : E → R) (Λ : R) (w : VertexPair n) :
    Option (MarkedState n) → Option (MarkedState n) → R
  | some x, some y => H.safeProcessRate r w x y
  | some x, none => H.killRate r w x - Λ
  | none, _ => 0

end LabeledHypergraph

/-- The terminal reward `g`: `N / binom(K(x), 2)` at a live state `x` and `0` at the cemetery
((6.3), p. 7), with `N = binom(n, 2)`. A live state reached by `R_w` has `K ≥ 2`; at `K ≤ 1` (never
reached) the division by zero yields `0`. -/
def terminalReward {n : ℕ} {R : Type} [Field R] : Option (MarkedState n) → R
  | some x => ((n.choose 2 : ℕ) : R) / ((MarkedState.K x).choose 2 : ℕ)
  | none => 0

/-- The estimator (5.2), p. 7, for the protected pair `w`: `N / binom(K(X_T), 2)` times
`exp(-∫₀^T κ_w(X_t) dt)`. -/
def estimatorX {n : ℕ} {E : Type} [Fintype E] (H : LabeledHypergraph n E) (r : E → ℝ) (T : ℝ)
    (w : VertexPair n) (path : JumpPath (MarkedState n)) : ℝ :=
  ((n.choose 2 : ℕ) : ℝ) / ((MarkedState.K path.last).choose 2 : ℕ) *
    Real.exp (-JumpPath.pathIntegral (H.killRate r w) T path)

/-- The average over the uniformly chosen initial pair. -/
def pairAverage {n : ℕ} (f : VertexPair n → ℝ) : ℝ :=
  ((n.choose 2 : ℕ) : ℝ)⁻¹ * ∑ w, f w

end HypergraphUnreliability.FPRAS


