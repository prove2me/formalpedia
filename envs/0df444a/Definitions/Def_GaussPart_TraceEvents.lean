-- Prove2me | Definitions.Def_GaussPart_TraceEvents
-- name    : GaussPart_TraceEvents
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:31:00.016724+00:00
-- url     : https://prove2.me/theorems/70c6064c-a29f-40c4-8c49-2f8eb9a8cd38
-- title:
--   Masses and success events on traces of Algorithm 1
-- statement:
--   For a trace and a probability measure $Q$ on $\mathbb R^d$ ($P=N(0,I_d)$):
--   1. $\mathrm{mass}(\mathcal C)=\sum_{R\in\mathcal C}Q(R)$; the population tail $\Pr_{x\sim Q\mid R}[v\cdot x\ge s]$; the law of the $V_R^\perp$ projection of $Q\mid R$ in an orthonormal basis; the cells of $\mathcal U_t$ with $Q(R)\le\xi$;
--   2. the parts of the success event $\Omega$ of the proof of Theorem 3.1 (p.26), every empirical tail used for validation is within $\varepsilon$ of the population tail at every threshold; every executed split is $\kappa$-Gaussian good; every mass estimate of an active cell is within $\varepsilon$ of $Q(R)$; every None of the finder satisfies item 2 of Corollary C.1 on $V_R^\perp$; every returned direction satisfies item 1 (discrepancy at least $\Delta/4$ against $\mathbb E[Z^\ell]$ in some degree); every Reject satisfies the contrapositive of item 3 (some Hermite moment tensor of the $V_R^\perp$ projection has Frobenius norm above $H$).
--
--   **Formalization Note** Except for the None event, the events are imposed only on cells of positive $Q$-mass, where $Q\mid R$ is defined; this asks for less than the page. The None event is imposed on every certified cell; under the mass event a certified cell has $Q(R)>\xi/4>0$.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), proof of Theorem 3.1, p.26 (PDF p.28); Lemmas 3.7, 3.10, p.21–23; Corollary C.1, p.73

import Mathlib
import Definitions.Def_GaussPart_Trace
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_GaussPart_FinderObjects

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace GaussPart

/-- `∑_{R ∈ cells} Q(R)`, by list position. -/
noncomputable def mass {d : ℕ} (Q : Measure (Vec d)) (cells : List (Cell d)) : ℝ :=
  (cells.map fun R => (Q (cellSet R)).toReal).sum

/-- `Pr_{x∼Q|R}[v · x ≥ s]`, the population upper tail of `v · x` on `R`. -/
noncomputable def condTail {d : ℕ} (Q : Measure (Vec d)) (R : Cell d) (v : Vec d) (s : ℝ) : ℝ :=
  (ProbabilityTheory.cond Q (cellSet R) {x | s ≤ ⟪v, x⟫}).toReal

/-- The law of the `V_R^⊥` projection of `Q | R`, in the coordinates of an orthonormal basis of
`V_R^⊥`: the finder's input (Algorithm 1, line 11, p.19). -/
noncomputable def projLaw {d n : ℕ} (Q : Measure (Vec d)) (R : Cell d)
    (b : OrthonormalBasis (Fin n) ℝ (constraintSpace R)ᗮ) : Measure (Vec n) :=
  (ProbabilityTheory.cond Q (cellSet R)).map
    fun x => b.repr ((constraintSpace R)ᗮ.orthogonalProjectionOnto x)

namespace Trace

variable {d : ℕ}

/-- The cells of `U_t` with `Q(R) ≤ ξ`: `B_t` of Lemma 3.10 (p.23), by true mass. -/
noncomputable def lowMassCells (Q : Measure (Vec d)) (tr : Trace d) (t : ℕ) (ξ : ℝ) :
    List (Cell d) :=
  open Classical in ((tr.U t).map Prod.fst).filter fun R => (Q (cellSet R)).toReal ≤ ξ

/-- The empirical CDF event of the success event `Ω` (proof of Theorem 3.1, p.26, PDF p.28): at every
validation stage through iteration `L`, on a cell of positive `Q`-mass, the empirical tail is within
`ε` of `Pr_{x∼Q|R}[v · x ≥ s]` at every threshold.

**Formalization Note.** Only cells of positive `Q`-mass are constrained, since `Q | R` is undefined
otherwise. This asks for less than the event on the page. -/
def TailsAccurate (Q : Measure (Vec d)) (K : Knobs) (tr : Trace d) (ε : ℝ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ K.L → ∀ e ∈ tr t, 0 < Q (cellSet e.cell) →
    match e.action with
    | .failed v F => ∀ s, |F s - condTail Q e.cell v s| ≤ ε
    | .split v F _ _ => ∀ s, |F s - condTail Q e.cell v s| ≤ ε
    | _ => True

/-- "Every executed split is `κ`-Gaussian good" (Lemma 3.10, p.23), on the cells of positive `Q`-mass:
the Bernoulli pair of `v · x ≥ s` under `N(0, 1)` and `Q | R` has squared Hellinger distance at
least `κ`. -/
def SplitsGood (Q : Measure (Vec d)) (K : Knobs) (tr : Trace d) (κ : ℝ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ K.L → ∀ e ∈ tr t, 0 < Q (cellSet e.cell) →
    match e.action with
    | .split v _ s _ => κ ≤ hellingerSq (gaussianTail s) (condTail Q e.cell v s)
    | _ => True

/-- The mass event of `Ω` (p.26): every mass estimate of a non-terminal cell has error at most `ε`. -/
def EstimatesAccurate (Q : Measure (Vec d)) (K : Knobs) (tr : Trace d) (ε : ℝ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ K.L → ∀ e ∈ tr t, e.tag = Tag.active →
    |e.est - (Q (cellSet e.cell)).toReal| ≤ ε

/-- Conclusion 2 of Corollary C.1 at every certified cell: the distribution matches directional
moments with the standard Gaussian to slack `Δ`, on `V_R^⊥`. -/
def FinderNoneSound (Q : Measure (Vec d)) (K : Knobs) (tr : Trace d) (k : ℕ) (Δ : ℝ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ K.L → ∀ e ∈ tr t,
    match e.action with
    | .certified => ∀ v ∈ (constraintSpace e.cell)ᗮ, ‖v‖ = 1 → ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ k →
        |∫ x, ⟪v, x⟫ ^ ℓ ∂(ProbabilityTheory.cond Q (cellSet e.cell)) - gaussianMoment ℓ| ≤ Δ
    | _ => True

/-- Conclusion 1 of Corollary C.1 at every returned direction, on the cells of positive `Q`-mass: some
degree `ℓ ∈ [k]` has `|E_{Q|R}[(v · x)^ℓ] − E[Z^ℓ]| ≥ Δ/4`. -/
def FinderDirSound (Q : Measure (Vec d)) (K : Knobs) (tr : Trace d) (k : ℕ) (Δ : ℝ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ K.L → ∀ e ∈ tr t, 0 < Q (cellSet e.cell) →
    let conclusion (v : Vec d) : Prop := ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ k ∧
      Δ / 4 ≤ |∫ x, ⟪v, x⟫ ^ ℓ ∂(ProbabilityTheory.cond Q (cellSet e.cell)) - gaussianMoment ℓ|
    match e.action with
    | .failed v _ => conclusion v
    | .split v _ _ _ => conclusion v
    | _ => True

/-- Conclusion 3 of Corollary C.1 at every rejected cell of positive `Q`-mass: since the finder
rejected, some Hermite moment tensor of the `V_R^⊥` projection of `Q | R` has Frobenius norm above
`H`. -/
def FinderRejectSound (Q : Measure (Vec d)) (K : Knobs) (tr : Trace d) (k : ℕ) (H : ℝ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ K.L → ∀ e ∈ tr t, 0 < Q (cellSet e.cell) →
    match e.action with
    | .rejected => ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℝ (constraintSpace e.cell)ᗮ) (i : ℕ),
        1 ≤ i ∧ i ≤ k ∧ H < frobeniusNorm (hermiteMoment (projLaw Q e.cell b) i)
    | _ => True

end Trace

end GaussPart


