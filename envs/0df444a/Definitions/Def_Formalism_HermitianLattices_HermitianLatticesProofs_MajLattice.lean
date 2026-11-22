-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:18.330496+00:00
-- url     : https://prove2.me/theorems/126b0f04-e781-42b7-9c71-9c601a571293
-- title:
--   Maj Lattice
-- statement:
--   Definitions and structural lemmas for Maj Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajLattice.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CommonMajorizingLattice
import Definitions.Def_Lemmata_GeneralBFactSecondRest_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open scoped Matrix
noncomputable section
namespace Formalism.HermitianLatticesTheory
section MajLatticeAux
variable {K : Type*} [Field K] [NumberField K]
end MajLatticeAux
section MajLatticeMain
variable {K V ι : Type*} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] [AddCommGroup V]
  [Module K V] [Fintype ι] [DecidableEq ι]
def majLattice_u (z : ι → mixedSpace K) (v : InfinitePlace K) : ι → ℂ :=
  fun i => (z i).2 ⟨v, IsTotallyComplex.isComplex v⟩
def majLattice_Traw (X : InfinitePlace K → Matrix ι ι ℂ) :
    (ι → mixedSpace K) →ₗ[ℝ] (InfinitePlace K × ι × Fin 2 → ℝ) where
  toFun z p := if p.2.2 = 0 then (((X p.1)⁻¹ *ᵥ majLattice_u z p.1) p.2.1).re
    else (((X p.1)⁻¹ *ᵥ majLattice_u z p.1) p.2.1).im
  map_add' z z' := by
    funext p
    have : majLattice_u (z + z') p.1 = majLattice_u z p.1 + majLattice_u z' p.1 := rfl
    simp only [this, Matrix.mulVec_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' r z := by
    funext p
    have : majLattice_u (r • z) p.1 = r • majLattice_u z p.1 := rfl
    simp only [this, Matrix.mulVec_smul, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp
def majLattice_alt (X : InfinitePlace K → Matrix ι ι ℂ) :
    (ι → mixedSpace K) →ₗ[ℝ] EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (InfinitePlace K × ι × Fin 2 → ℝ)).symm.toLinearMap ∘ₗ
    majLattice_Traw X
theorem majLattice_T_injective (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) : Function.Injective (majLattice_alt X) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hu : ∀ v, majLattice_u z v = 0 := by
    intro v
    have hw : (X v)⁻¹ *ᵥ majLattice_u z v = 0 := by
      funext i
      have h0 := congrArg (fun w => w (v, i, 0)) hz
      have h1 := congrArg (fun w => w (v, i, 1)) hz
      simp [majLattice_alt, majLattice_Traw] at h0 h1
      exact Complex.ext h0 h1
    have := congrArg (fun w => X v *ᵥ w) hw
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v)] using this
  funext i
  refine Prod.ext (funext fun w => absurd w.2
    (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _))) (funext fun w => ?_)
  simpa [majLattice_u] using congrFun (hu w.1) i
theorem majLattice_finrank :
    finrank ℝ (ι → mixedSpace K) =
      finrank ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) := by
  have hc : nrComplexPlaces K = Fintype.card (InfinitePlace K) := by
    classical
    rw [nrComplexPlaces]
    convert Fintype.card_congr (Equiv.subtypeUnivEquiv (IsTotallyComplex.isComplex (K := K)))
  rw [finrank_euclideanSpace, Module.finrank_pi_fintype]
  simp only [mixedEmbedding.finrank, IsTotallyComplex.finrank, hc, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Fintype.card_prod, Fintype.card_fin]
  ring
def majLattice_B (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) :
    Basis (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ
      (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :=
  (Pi.basis fun _ : ι => latticeBasis K).map
    (LinearMap.linearEquivOfInjective (majLattice_alt X) (majLattice_T_injective X hX)
      majLattice_finrank)
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end MajLatticeMain
end Formalism.HermitianLatticesTheory


