-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_ExactSecondDegreeZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_ExactSecondDegreeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:53.948808+00:00
-- url     : https://prove2.me/theorems/f636a33b-97ef-4477-9787-7c0c3abc1b39
-- title:
--   Exact Second Degree Zero
-- statement:
--   Definitions and structural lemmas for Exact Second Degree Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/ExactSecondDegreeZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_YHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EagonNorthcottZ
open MvPolynomial PI.EagonNorthcott
def Anti : Prop := ∀ (D : ℕ) (t u : Fin D → P D) (ω : W D), K t (K u ω) = - K u (K t ω)
def Sq : Prop := ∀ (D : ℕ) (t : Fin D → P D) (ω : W D), K t (K t ω) = 0
def KLin : Prop := ∀ (D : ℕ) (t : Fin D → P D) (ω η : W D), K t (ω - η) = K t ω - K t η ∧ K t (-ω) = - K t ω
def GrLin : Prop := ∀ (D a j : ℕ) (ω η : W D), Gr a j ω → Gr a j η → Gr a j (ω - η) ∧ Gr a j (-ω)
def GrX : Prop := ∀ (D a j : ℕ) (ω : W D), Gr a (j + 1) ω → Gr a j (K xs ω)
def GrY : Prop := ∀ (D a j : ℕ) (ω : W D), Gr a (j + 1) ω → Gr (a + 1) j (K ys ω)
def AugK : Prop := ∀ (D : ℕ) (η : W D), mu (K xs η ∅) = mu (K ys η ∅)
def ExX : Prop := ∀ (D a j : ℕ) (ω : W D), Gr a (j + 1) ω → K xs ω = 0 → ∃ ζ, Gr a (j + 2) ζ ∧ K xs ζ = ω
def ExY : Prop := ∀ (D a j : ℕ) (ω : W D), Gr (a + 1) (j + 1) ω → K ys ω = 0 → ∃ θ, Gr a (j + 2) θ ∧ K ys θ = ω
def ExYz : Prop := ∀ (D j : ℕ) (ω : W D), Gr 0 (j + 1) ω → K ys ω = 0 → ω = 0
def ExactSecondDegreeZero : Prop := ∀ (D a : ℕ) (ω : W D), Gr (a + 1) 0 ω → ∃ θ, Gr a 1 θ ∧ K ys θ = ω
def Aug0 : Prop := ∀ (D : ℕ) (ω : W D), Gr 0 0 ω → mu (ω ∅) = 0 → ω = 0
def Main : Prop := ∀ (D a j : ℕ) (ω : W D), Gr a (j + 1) ω → K ys ω = 0 → K xs ω = 0 →
  ∃ η, Gr a (j + 2) η ∧ K ys η = 0 ∧ K xs η = ω
def EagonNorthcottIntegralExactness : Prop := ∀ (D a : ℕ) (ω : W D), Gr a 0 ω → mu (ω ∅) = 0 → ∃ η, Gr a 1 η ∧ K ys η = 0 ∧ K xs η = ω
def Frame : Prop := ∀ D a : ℕ, ∃ (n : ℕ → ℕ) (e : Fin (n 0) → Fin D → ℕ)
    (C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)) (Φ : ∀ j, (Fin (n j) → S D) → W D),
  Shape D a n e C ∧ (∀ j, Function.Injective (Φ j)) ∧ (∀ j, Φ j 0 = 0) ∧
    (∀ j ω, (∃ v, Φ j v = ω) ↔ (Gr a j ω ∧ K ys ω = 0)) ∧
    (∀ j v, Φ j (dmap (X : Fin D → S D) (C j) v) = K xs (Φ (j + 1) v)) ∧
    ∀ v, aug (X : Fin D → S D) e v = mu (Φ 0 v ∅)
def AugRange : Prop := ∀ (D a m : ℕ) (e : Fin m → Fin D → ℕ), (∀ α : Fin D → ℕ, α ∈ Set.range e ↔ ∑ i, α i = a) →
  LinearMap.range (aug (X : Fin D → S D) e) = Ideal.span (Set.range (X : Fin D → S D)) ^ a
end PI.EagonNorthcottZ


