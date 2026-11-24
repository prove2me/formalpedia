-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ZuckDualOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ZuckDualOf
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:56:05.02895+00:00
-- url     : https://prove2.me/theorems/61f92ab8-88bb-427e-9186-a8e6008d2b48
-- title:
--   Zuck Dual Of
-- statement:
--   Definitions and structural lemmas for Zuck Dual Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ZuckDualOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_DSExist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
structure Fam (n : ℕ) where
  Hs : Fin n → Type
  [nH : ∀ s, NormedAddCommGroup (Hs s)]
  [iH : ∀ s, InnerProductSpace ℂ (Hs s)]
  [cH : ∀ s, CompleteSpace (Hs s)]
  σs : ∀ s, Matrix (Fin n) (Fin n) ℂ → (Hs s →L[ℂ] Hs s)
attribute [instance] Fam.nH Fam.iH Fam.cH
def Ineq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam lam' : Fin n → ℝ), vNormSq ε (lowK ε lam) ≠ vNormSq ε (lowK ε lam') →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
      IsDS ε lam' σ' → ¬ ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ x, U (σ g x) = σ' g (U x)
def ToSum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ F : Fam n, (∀ s, IsHCParam (μ + Pi.single s 1) → IsDS ε (μ + Pi.single s 1) (F.σs s)) →
    ∀ (v w : H) (x y : Fin n → ℂ), IsKFin ε σ v → IsKFin ε σ w →
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, F.Hs (sI i)),
      (∀ i, IsHCParam (μ + Pi.single (sI i) 1) ∧ IsKFin ε (F.σs (sI i)) (vI i) ∧ IsKFin ε (F.σs (sI i)) (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ g v⟫_ℂ * (star y ⬝ᵥ (g *ᵥ x)) = ∑ i, ⟪wI i, F.σs (sI i) g (vI i)⟫_ℂ
def OfSum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ (s : Fin n), IsHCParam (μ + Pi.single s 1) →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsDS ε (μ + Pi.single s 1) σ' →
    ∀ v w : H', IsKFin ε σ' v → IsKFin ε σ' w →
    ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → H) (xI yI : ι → Fin n → ℂ),
      (∀ i, IsKFin ε σ (vI i) ∧ IsKFin ε σ (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ' g v⟫_ℂ = ∑ i, ⟪wI i, σ g (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (g *ᵥ xI i))
def ToSumd : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ F : Fam n, (∀ s, IsHCParam (μ - Pi.single s 1) → IsDS ε (μ - Pi.single s 1) (F.σs s)) →
    ∀ (v w : H) (x y : Fin n → ℂ), IsKFin ε σ v → IsKFin ε σ w →
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, F.Hs (sI i)),
      (∀ i, IsHCParam (μ - Pi.single (sI i) 1) ∧ IsKFin ε (F.σs (sI i)) (vI i) ∧ IsKFin ε (F.σs (sI i)) (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ g v⟫_ℂ * (star y ⬝ᵥ (g⁻¹ *ᵥ x)) = ∑ i, ⟪wI i, F.σs (sI i) g (vI i)⟫_ℂ
def OfSumd : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ (s : Fin n), IsHCParam (μ - Pi.single s 1) →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsDS ε (μ - Pi.single s 1) σ' →
    ∀ v w : H', IsKFin ε σ' v → IsKFin ε σ' w →
    ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → H) (xI yI : ι → Fin n → ℂ),
      (∀ i, IsKFin ε σ (vI i) ∧ IsKFin ε σ (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ' g v⟫_ℂ = ∑ i, ⟪wI i, σ g (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (g⁻¹ *ᵥ xI i))
def NormNe : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ), IsHCParam μ → ∀ s s' : Fin n, s ≠ s' →
    vNormSq ε (lowK ε (μ + Pi.single s 1)) ≠ vNormSq ε (lowK ε (μ + Pi.single s' 1)) ∧
    vNormSq ε (lowK ε (μ - Pi.single s 1)) ≠ vNormSq ε (lowK ε (μ - Pi.single s' 1))
end PI.ZuckTensorWork
end


