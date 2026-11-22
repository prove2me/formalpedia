-- Prove2me | Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
-- name    : Formalism_JacquetSubsetSums_SeparationTR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:17.414159+00:00
-- url     : https://prove2.me/theorems/bc5bba30-c0fd-4d45-bc95-6600995b6814
-- title:
--   Separation TR
-- statement:
--   Definitions and structural lemmas for Separation TR, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/JacquetSubsetSums/SeparationTR.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
import Definitions.Def_Formalism_JacquetSubsetSums_JacquetSubsetSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.PacketSums
def SeparationTR : Prop :=
  ∀ (HH : Type) (r : ℕ) (Sg Pu : Type) [Fintype Sg] [Fintype Pu]
    (chr : Sg → HH → ℂ) (Ex : Pu → (Multiplicative (Fin r → ℤ) →* ℂ) →₀ ℂ)
    (trI : Pu → (Fin r → ℤ) → ℂ) (cst : (Fin r → ℤ) → ℂ) (m m' : Sg → Pu → ℕ),
    LinearIndependent ℂ chr → LinearIndependent ℂ Ex →
    (∀ a, StrictAnti a → cst a ≠ 0) →
    (∀ π a, StrictAnti a →
      trI π a = cst a * ((Ex π).sum fun χ z => z * χ (Multiplicative.ofAdd a))) →
    (∀ h a, StrictAnti a →
      (∑ σ, ∑ π, (m σ π : ℂ) * chr σ h * trI π a) = ∑ σ, ∑ π, (m' σ π : ℂ) * chr σ h * trI π a) →
    m = m'
def LatticeCut : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]
    (L : Submodule (𝓞 K) V), Submodule.IsLattice K L → ∀ A : Submodule K V,
      (L ⊓ A.restrictScalars (𝓞 K)).FG ∧
      Submodule.span K ((L ⊓ A.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = A ∧
      finrank (𝓞 K) ↥(L ⊓ A.restrictScalars (𝓞 K)) = finrank K A
def RankExport : Prop :=
  ∀ (K : Type) [Field K] (D : ℕ) (J : Type) (d : J → ℕ) (Ix : Type) [Fintype Ix]
    (Ep : Ix → Submodule K (Fin D → K)) (Wp : ∀ j, Ix → Submodule K (Fin (d j) → K)),
    iSupIndep Ep → (⨆ p, Ep p) = ⊤ → (∀ j, iSupIndep (Wp j)) → (∀ j, (⨆ p, Wp j p) = ⊤) →
    ∀ (m : Ix → ℕ) (m' : J → Ix → ℕ) (n : Ix → ℕ),
    (∀ p, finrank K (Ep p) = m p * n p) → (∀ j p, finrank K (Wp j p) = m' j p * n p) →
    (∀ j p, n p ≠ 0 → m' j p = m p) →
    ∀ ι : Matrix (Fin D) (Fin D) K, IsUnit ι.det →
    ∀ θ : ∀ j, Matrix (Fin (d j)) (Fin (d j)) K, (∀ j, IsUnit (θ j).det) →
      (∀ j, d j = D) ∧ D = ∑ p, m p * n p ∧
      iSupIndep (fun p => (Ep p).comap ι.mulVecLin) ∧
      (⨆ p, (Ep p).comap ι.mulVecLin) = ⊤ ∧
      (∀ j, iSupIndep fun p => (Wp j p).comap (θ j).mulVecLin) ∧
      (∀ j, (⨆ p, (Wp j p).comap (θ j).mulVecLin) = ⊤) ∧
      ∀ j p, finrank K ((Ep p).comap ι.mulVecLin) = finrank K ((Wp j p).comap (θ j).mulVecLin)
def SpecDetMult : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v : InfinitePlace K) (D : ℕ)
    (XQ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
    (∀ u, IsUnit (XQ u).det) → (∀ u, IsUnit (XE u).det) →
    ∀ ι : Matrix (Fin D) (Fin D) K, IsUnit ι.det →
    ∀ (J : Type) [Fintype J] (d : J → ℕ)
      (XT XW : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ),
    (∀ j u, IsUnit (XT j u).det) → (∀ j u, IsUnit (XW j u).det) →
    ∀ θ : ∀ j, Matrix (Fin (d j)) (Fin (d j)) K, (∀ j, IsUnit (θ j).det) →
    ∀ (Ix : Type) [Fintype Ix] (Ep : Ix → Submodule K (Fin D → K))
      (Wp : ∀ j, Ix → Submodule K (Fin (d j) → K)),
    iSupIndep Ep → (⨆ p, Ep p) = ⊤ → (∀ j, iSupIndep (Wp j)) → (∀ j, (⨆ p, Wp j p) = ⊤) →
    ∀ (m : Ix → ℕ) (m' : J → Ix → ℕ) (n : Ix → ℕ),
    (∀ p, finrank K (Ep p) = m p * n p) → (∀ j p, finrank K (Wp j p) = m' j p * n p) →
    (∀ j p, n p ≠ 0 → m' j p = m p) →
    ∀ (s : ℝ) (lam : J → Ix → ℝ),
    (∀ p, ∀ x : Fin D → K, ι.mulVec x ∈ Ep p → ∀ y : Fin D → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XE v (ι.mulVec x) (ι.mulVec y) =
        ((s * ∏ j, lam j p : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XQ v x y) →
    (∀ j p, ∀ x : Fin (d j) → K, (θ j).mulVec x ∈ Wp j p → ∀ y : Fin (d j) → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (d j))) (XW j) v ((θ j).mulVec x) ((θ j).mulVec y) =
        ((lam j p : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (d j))) (XT j) v x y) →
      (∀ j, d j = D) ∧
      Formalism.DivisionValues.detRatio XQ XE ι v = s ^ D * ∏ j, Formalism.DivisionValues.detRatio (XT j) (XW j) (θ j) v
end Formalism.PacketSums


