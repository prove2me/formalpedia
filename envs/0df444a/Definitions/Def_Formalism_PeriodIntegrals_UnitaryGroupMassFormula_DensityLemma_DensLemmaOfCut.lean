-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_DensLemmaOfCut
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_DensLemmaOfCut
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:16:47.866455+00:00
-- url     : https://prove2.me/theorems/a84682e9-980b-4147-aa24-913f3cf6b40b
-- title:
--   Dens Lemma Of Cut
-- statement:
--   Definitions and structural lemmas for Dens Lemma Of Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/DensLemmaOfCut.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace PI.UnitaryGroupMassFormula.DLm
section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
def HasRun (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (i j : ℕ) : Prop :=
  1 ≤ i ∧ i < j ∧ j ≤ r + 1 ∧
    (∀ l : Fin (r + 2), l.val + 1 = i → Dmin k r D.z D.z' γ l ≠ 0) ∧
    (∀ l : Fin (r + 2), i ≤ l.val → l.val < j → Dmin k r D.z D.z' γ l = 0) ∧
    (∀ l : Fin (r + 2), l.val = j → Dmin k r D.z D.z' γ l ≠ 0)
def Hyps (CV : ℕ) (D : B.RealPlaceData k r Wp Wq) (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  1 ≤ r ∧ 0 < ε ∧ (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A ∧ mmV CV r ≤ mm ∧ B.InCC A mm F' ∧
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) ∧ (∀ g ∈ bigPos D, B.JF D F' g = 0)
end
def RunExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r),
    0 < Gf k r D.z D.z' γ → 1 ≤ zc D γ → ∃ i j : ℕ, HasRun D γ i j
def DownJ (CV : ℕ) : Prop :=
  StepAdm CV → ∀ m : ℕ, ZeroUpTo CV m →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (θ : B.SS k r → ℝ) (i j : ℕ),
    B.IsHaarOn (Rset γ) μR → Hyps CV D A ε mm F' →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ ≤ m + 1 → HasRun D γ i j → j ≤ r → admitted D γ μR θ →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS →
    orbI D γ θ F' = 0
def DownTop (CV : ℕ) : Prop :=
  StepAdm CV → ∀ m : ℕ, ZeroUpTo CV m →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (θ : B.SS k r → ℝ) (i : ℕ),
    B.IsHaarOn (Rset γ) μR → Hyps CV D A ε mm F' →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ ≤ m + 1 → HasRun D γ i (r + 1) → admitted D γ μR θ →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS →
    orbI D γ θ F' = 0
def AdmExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (μR : Measure (Mt k r)),
    B.IsHaarOn (Rset γ) μR → IsRelevant D γ → 0 < Gf k r D.z D.z' γ → ∃ θ : B.SS k r → ℝ, admitted D γ μR θ
def AdmConv (CV : ℕ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (θ : B.SS k r → ℝ),
    B.IsHaarOn (Rset γ) μR →
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → admitted D γ μR θ →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS
def BigTheta : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ),
    B.IsHaarOn (Rset γ) μR → IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ = 0 → admitted D γ μR θ →
    ∃ c : ℝ, 0 < c ∧ ∀ p, D.inSS p → θ p = c
def BigOf (CV : ℕ) : Prop := BigTheta → B.JtauOne → StepBig CV
end PI.UnitaryGroupMassFormula.DLm


