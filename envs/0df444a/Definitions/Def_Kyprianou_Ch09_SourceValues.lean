-- Prove2me | Definitions.Def_Kyprianou_Ch09_SourceValues
-- name    : Kyprianou_Ch09_SourceValues
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:17:51.807506+00:00
-- url     : https://prove2.me/theorems/8214d24a-9fe3-4ad5-9cab-59e5e1dc89c7
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner SourceValues
-- statement:
--   Discounted optimal-stopping values, regularity hypotheses and one-sided smooth-fit definitions. This source Definition module provides the actual declarations: putGain, russianGain, russianValue, russianGameGain, russianGameValue, putGameValue, RegularAbove, RegularBelow, SmoothFitAt, AppellPolynomialFamily, AppellExistenceUniqueness. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceCore
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09.B1

/-- Perpetual put reward, measured in log-price coordinates. -/
noncomputable def putGain (K z : ℝ) : ℝ := max (K - Real.exp z) 0

/-- Direct continuous Russian reward under a finite stopping time. -/
noncomputable def russianGain {Ω : Type} (X : ℝ≥0 → Ω → ℝ)
    (q x : ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ :=
  match τ ω with
  | ⊤ => 0
  | (t : ℝ≥0) =>
    Real.exp (-q * (t : ℝ) +
      max x (pathSupAt X t ω))

/-- Source 9.11 maximises over a.s.-finite admissible stopping times. -/
noncomputable def russianValue {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (q x : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ τ : Ω → WithTop ℝ≥0,
    AdmissibleFiniteStop P F τ ∧ z = ∫ ω, russianGain X q x τ ω ∂P}

/-- The source Russian-game stopping payoff pays the maximiser on ties,
including simultaneous infinite stops. The penalty is paid only when the
minimiser strictly precedes the maximiser. -/
noncomputable def russianGameGain {Ω : Type}
    (X : ℝ≥0 → Ω → ℝ) (q x δ : ℝ)
    (τ σ : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ :=
  if τ ω ≤ σ ω then russianGain X q x τ ω else
    match σ ω with
    | ⊤ => 0
    | (t : ℝ≥0) =>
        Real.exp (-q * (t : ℝ)) *
          (Real.exp (max x (pathSupAt X t ω)) +
            δ * Real.exp (X t ω))

/-- Dynkin game lower value using genuine stopping times and the minimiser's
infimum, rather than a witness supplied with the asserted value. -/
noncomputable def russianGameValue {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (q x δ : ℝ) : ℝ :=
  sSup {a : ℝ | ∃ τ : Ω → WithTop ℝ≥0, AdmissibleStop F τ ∧
    a = sInf {b : ℝ | ∃ σ : Ω → WithTop ℝ≥0,
      AdmissibleStop F σ ∧ b = ∫ ω, russianGameGain X q x δ τ σ ω ∂P}}

/-- The lower game payoff is the put and the upper is put plus penalty. -/
noncomputable def putGameValue {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (K δ x : ℝ)
    (terminalG terminalH : Ω → ℝ) : ℝ :=
  sSup {a : ℝ | ∃ τ : Ω → WithTop ℝ≥0, AdmissibleStop F τ ∧
    a = sInf {b : ℝ | ∃ σ : Ω → WithTop ℝ≥0,
      AdmissibleStop F σ ∧ b =
        ∫ ω, gameGain X (putGain K) (fun z => putGain K z + δ)
          0 x terminalG terminalH τ σ ω ∂P}}

/-- Upward regularity at zero for the actual process. -/
def RegularAbove {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
    ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧ 0 < X t ω

/-- Downward regularity at zero for the actual process. -/
def RegularBelow {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
    ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧ X t ω < 0

/-- Candidate derivative continuity from each side is tested without
silently identifying the two one-sided values. -/
def SmoothFitAt (v : ℝ → ℝ) (a : ℝ) : Prop :=
  DifferentiableWithinAt ℝ v (Set.Iic a) a ∧
  DifferentiableWithinAt ℝ v (Set.Ici a) a ∧
  derivWithin v (Set.Iic a) a = derivWithin v (Set.Ici a) a

/-- The polynomial definition and nth-moment centring are separate from
the translated mean-value property which Lemma 9.8 must establish. -/
def AppellPolynomialFamily {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ)
    (n : ℕ) (Q : ℕ → Polynomial ℝ) : Prop :=
  (Q 0 = 1) ∧
  (∀ k : ℕ, k < n →
    (Q (k + 1)).derivative = Polynomial.C (k + 1 : ℝ) * Q k) ∧
  (∀ k : ℕ, 1 ≤ k → k ≤ n →
    Integrable (fun ω => (Q k).eval (Y ω)) P ∧
    (∫ ω, (Q k).eval (Y ω) ∂P) = 0)

/-- The source's uniqueness and existence are independently Open.
No member of this family is assumed to satisfy the desired lemma. -/
def AppellExistenceUniqueness : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (n : ℕ) (hn : 1 ≤ n),
      (∀ᵐ ω ∂P, 0 ≤ Y ω) →
      Integrable (fun ω => (Y ω) ^ n) P →
      ∃ Q : ℕ → Polynomial ℝ,
        AppellPolynomialFamily P Y n Q ∧
        ∀ R : ℕ → Polynomial ℝ,
          AppellPolynomialFamily P Y n R →
          ∀ k : ℕ, k ≤ n → R k = Q k

end Kyprianou.Ch09.B1


