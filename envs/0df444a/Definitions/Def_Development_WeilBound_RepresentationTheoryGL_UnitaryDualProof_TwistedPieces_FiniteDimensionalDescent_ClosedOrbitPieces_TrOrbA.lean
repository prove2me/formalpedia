-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbA
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:58.735325+00:00
-- url     : https://prove2.me/theorems/a4f2ce37-7513-43af-a327-c4564406596b
-- title:
--   Tr Orb A
-- statement:
--   Definitions and structural lemmas for Tr Orb A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/TrOrbA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
universe u
open Classical in

def pidem (A : Type*) [CommRing A] [IsArtinianRing A] [IsReduced A] (I : MaximalSpectrum A) : A :=
  (IsArtinianRing.equivPi A).symm (Pi.single I 1)
section idem
open Classical
variable {A : Type*} [CommRing A] [IsArtinianRing A] [IsReduced A]
theorem equivPi_pidem (I J : MaximalSpectrum A) :
    IsArtinianRing.equivPi A (pidem A I) J = Pi.single (M := fun I : MaximalSpectrum A => A ⧸ I.asIdeal) I 1 J := by
  rw [pidem, AlgEquiv.apply_symm_apply]
theorem pidem_mul (I J : MaximalSpectrum A) : pidem A I * pidem A J = if I = J then pidem A I else 0 := by
  apply (IsArtinianRing.equivPi A).injective
  funext L
  split_ifs with h
  · subst h
    rw [map_mul, Pi.mul_apply, equivPi_pidem]
    by_cases hL : L = I
    · subst hL; simp
    · simp [Pi.single_apply, hL]
  · rw [map_mul, Pi.mul_apply, equivPi_pidem, equivPi_pidem, map_zero, Pi.zero_apply]
    by_cases hL : L = I
    · subst hL; simp [Pi.single_apply, Ne.symm h]
    · simp [Pi.single_apply, hL]
theorem sum_pidem [Fintype (MaximalSpectrum A)] : ∑ I, pidem A I = 1 := by
  apply (IsArtinianRing.equivPi A).injective
  funext L
  rw [map_sum, Finset.sum_apply, map_one, Pi.one_apply]
  simp_rw [equivPi_pidem]
  simp [Pi.single_apply]
end idem
def piece {A : Type*} (M : Type*) [CommRing A] [AddCommGroup M] [Module A M] (e : A) : Submodule A M :=
  LinearMap.range (LinearMap.lsmul A M e)
section dec
open Classical
variable {A : Type*} [CommRing A] [IsArtinianRing A] [IsReduced A] [Fintype (MaximalSpectrum A)]
theorem pidem_smul_piece (P : Type*) [AddCommGroup P] [Module A P] (I J : MaximalSpectrum A) {y : P}
    (hy : y ∈ piece P (pidem A I)) : pidem A J • y = if J = I then y else 0 := by
  obtain ⟨m, rfl⟩ := hy
  rw [LinearMap.lsmul_apply, smul_smul, pidem_mul]
  split_ifs with h
  · subst h; rfl
  · exact zero_smul A m
def decomp (P : Type*) [AddCommGroup P] [Module A P] : P ≃ₗ[A] ∀ I : MaximalSpectrum A, piece P (pidem A I) where
  toFun m I := ⟨pidem A I • m, m, rfl⟩
  map_add' m m' := by funext I; ext; simp [smul_add]
  map_smul' a m := by funext I; ext; simp [smul_comm (pidem A I) a m]
  invFun x := ∑ I, (x I : P)
  left_inv m := by
    simp only
    rw [← Finset.sum_smul, sum_pidem, one_smul]
  right_inv x := by
    funext J
    ext
    simp only [Finset.smul_sum]
    rw [Finset.sum_eq_single J]
    · rw [pidem_smul_piece P J J (x J).2, if_pos rfl]
    · intro I _ hI
      rw [pidem_smul_piece P I J (x I).2, if_neg (Ne.symm hI)]
    · intro h; exact absurd (Finset.mem_univ J) h
end dec
section rep
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] {N : ℕ}
@[nolint unusedArguments]
def Rep (_ρ : A →ₐ[k] Matrix (Fin N) (Fin N) k) : Type _ := Fin N → k
variable (ρ : A →ₐ[k] Matrix (Fin N) (Fin N) k)
instance : AddCommGroup (Rep ρ) := inferInstanceAs (AddCommGroup (Fin N → k))
instance : Module k (Rep ρ) := inferInstanceAs (Module k (Fin N → k))
instance : FiniteDimensional k (Rep ρ) := inferInstanceAs (FiniteDimensional k (Fin N → k))
instance : Module A (Rep ρ) :=
  Module.compHom (Fin N → k) ((Matrix.toLinAlgEquiv' (R := k) (n := Fin N)).toAlgHom.comp ρ).toRingHom
theorem rep_smul (a : A) (v : Rep ρ) : a • v = (ρ a *ᵥ (v : Fin N → k) : Fin N → k) := rfl
instance : IsScalarTower k A (Rep ρ) := ⟨fun c a v => by
  rw [rep_smul, rep_smul, map_smul]
  exact Matrix.smul_mulVec _ _ _⟩
end rep
end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb


