-- Prove2me | solution 1 for AutomorphicForm.exists_nat_principalLevel_inf_finiteAdelicGL2Subgroup_subset_of_mem_nhds_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/043b704f-05e6-5727-8857-3664f602bccf

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Theorems.Thm_NumberField_AdelicLevel_exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_nat_principalLevel_inf_finiteAdelicGL2Subgroup_subset_of_mem_nhds_one

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace Ws31
namespace LevelBasis

open Topology AutomorphicForm NumberField.AdelicLevel

variable (K : Type) [Field K] [NumberField K]

theorem idealBound_le_exp_neg_of_pow_dvd {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) {n : ℕ}
    (h : v.asIdeal ^ n ∣ N) : idealBound (𝓞 K) N v ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  rw [idealBound_of_ne_bot hN, WithZero.exp_le_exp, neg_le_neg_iff]
  have hirr : Irreducible (Associates.mk v.asIdeal) := Associates.irreducible_mk.mpr v.irreducible
  have h1 := Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr (show N ≠ 0 from hN)) hirr
    (Associates.mk_le_mk_of_dvd h)
  rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr (show v.asIdeal ≠ 0 from v.ne_bot)) hirr,
    Associates.count_self hirr, mul_one] at h1
  exact_mod_cast h1

theorem weyl_conj_apply (g : AdelicGL2 (𝓞 K) K) :
    (((weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      !![(g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1, (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0;
         (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1, (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0] := by
  have hw : ((weyl (𝓞 K) K : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = !![0, 1; 1, 0] := rfl
  have hwi : (((weyl (𝓞 K) K)⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = !![0, 1; 1, 0] := rfl
  rw [Units.val_mul, Units.val_mul, hw, hwi, Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)),
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem entries_of_mem_principalLevel {N : Ideal (𝓞 K)} {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ principalLevel (𝓞 K) K N) :
    (∀ i j, ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K ∧
      (((g⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K) ∧
    (∀ i j, ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
        ∈ idealBall (𝓞 K) K N ∧
      (((g⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
        ∈ idealBall (𝓞 K) K N) := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨h, hh, hgh⟩ := Subgroup.mem_map.mp h2

  have hconj : (weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K = h := by
    have : (MulAut.conj (weyl (𝓞 K) K)).toMonoidHom h = g := hgh
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [← this]; group
  have hL : glFin (𝓞 K) K g ∈ finiteLevelOne (𝓞 K) K N := h1
  have hR : glFin (𝓞 K) K ((weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K) ∈ finiteLevelOne (𝓞 K) K N := by rw [hconj]; exact hh
  obtain ⟨hLg, hLgi⟩ := hL
  obtain ⟨hRg, hRgi⟩ := hR

  have eg : ∀ i j, ((glFin (𝓞 K) K g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix _ _ _) i j =
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 := fun i j => rfl
  have egi : ∀ i j, (((glFin (𝓞 K) K g)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix _ _ _) i j =
      (((g⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 := fun i j => by rw [← map_inv]; rfl
  have hwg := weyl_conj_apply K g
  have hwgi : ((((weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K)⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      !![((g⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1, ((g⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0;
         ((g⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1, ((g⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0] := by
    have : ((weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K)⁻¹ = (weyl (𝓞 K) K)⁻¹ * g⁻¹ * weyl (𝓞 K) K := by
      have hww : (weyl (𝓞 K) K)⁻¹ = weyl (𝓞 K) K := Units.ext rfl
      rw [mul_inv_rev, mul_inv_rev, inv_inv, hww, mul_assoc]
    rw [this]; exact weyl_conj_apply K (g⁻¹)
  have eR : ∀ i j, ((glFin (𝓞 K) K ((weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K) : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix _ _ _) i j =
      ((((weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 := fun i j => rfl
  have eRi : ∀ i j, (((glFin (𝓞 K) K ((weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K))⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix _ _ _) i j =
      (((((weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K)⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 :=
    fun i j => by rw [← map_inv]; rfl
  refine ⟨fun i j => ⟨?_, ?_⟩, fun i j => ⟨?_, ?_⟩⟩
  · have := hLg.integral i j; rwa [eg] at this
  · have := hLgi.integral i j; rwa [egi] at this
  · fin_cases i <;> fin_cases j
    ·
      have := hRg.lowerRight; rw [eR, hwg] at this; simpa using this
    ·
      have := hRg.lowerLeft; rw [eR, hwg] at this; simpa using this
    · have := hLg.lowerLeft; rw [eg] at this; simpa using this
    · have := hLg.lowerRight; rw [eg] at this; simpa using this
  · fin_cases i <;> fin_cases j
    · have := hRgi.lowerRight; rw [eRi, hwgi] at this; simpa using this
    · have := hRgi.lowerLeft; rw [eRi, hwgi] at this; simpa using this
    · have := hLgi.lowerLeft; rw [egi] at this; simpa using this
    · have := hLgi.lowerRight; rw [egi] at this; simpa using this

theorem main
    (K : Type) [Field K] [NumberField K]
    (V : Set (AdelicGL2 (𝓞 K) K)) (_hV : V ∈ 𝓝 (1 : AdelicGL2 (𝓞 K) K)) :
    ∃ m : ℕ, ((principalLevel (𝓞 K) K (Ideal.span {((m + 1 : ℕ) : 𝓞 K)}) ⊓ finiteAdelicGL2Subgroup K :
        Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) ⊆ V := by
  classical
  obtain ⟨T, e, hTe⟩ := NumberField.AdelicLevel.exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one K V _hV

  set N : Ideal (𝓞 K) := ∏ v ∈ T, v.asIdeal ^ e with hN
  have hN0 : N ≠ ⊥ := by
    rw [hN]; exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot
  have hdvd : ∀ v ∈ T, v.asIdeal ^ e ∣ N := fun v hv => by rw [hN]; exact Finset.dvd_prod_of_mem _ hv
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Ideal.absNorm N = m + 1 :=
    Nat.exists_eq_add_one_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hN0) |>.imp fun m h => h
  refine ⟨m, fun g hg => ?_⟩
  have hgP : g ∈ principalLevel (𝓞 K) K (Ideal.span {((m + 1 : ℕ) : 𝓞 K)}) := hg.1
  have hgF : g ∈ finiteAdelicGL2Subgroup K := hg.2

  have hle : Ideal.span {((m + 1 : ℕ) : 𝓞 K)} ≤ N := by
    rw [Ideal.span_le, Set.singleton_subset_iff, ← hm]; exact Ideal.absNorm_mem N
  have hM0 : Ideal.span {((m + 1 : ℕ) : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast Nat.succ_ne_zero m
  have hbd : ∀ v ∈ T, idealBound (𝓞 K) (Ideal.span {((m + 1 : ℕ) : 𝓞 K)}) v ≤ WithZero.exp (-(e : ℤ)) :=
    fun v hv => idealBound_le_exp_neg_of_pow_dvd K hM0 v ((hdvd v hv).trans (Ideal.dvd_iff_le.mpr hle))
  obtain ⟨hint, hcong⟩ := entries_of_mem_principalLevel K hgP
  refine hTe g ((mem_finiteAdelicGL2Subgroup_iff K g).mp hgF) (fun v i j => ⟨(hint i j).1 v, (hint i j).2 v⟩) ?_
  intro v hv i j
  have h1 : ∀ (x : FiniteAdeleRing (𝓞 K) K), x ∈ idealBall (𝓞 K) K (Ideal.span {((m + 1 : ℕ) : 𝓞 K)}) →
      Valued.v (x v) ≤ WithZero.exp (-(e : ℤ)) := fun x hx => (hx v).trans (hbd v hv)
  have hone : ∀ i j : Fin 2, ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) v =
      (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
    intro i j; fin_cases i <;> fin_cases j <;> rfl
  refine ⟨?_, ?_⟩
  · have := h1 _ (hcong i j).1; rwa [coe_sub_apply, hone] at this
  · have := h1 _ (hcong i j).2; rwa [coe_sub_apply, hone] at this

end Ws31.LevelBasis

end

open Topology AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (V : Set (AdelicGL2 (𝓞 K) K)) (_hV : V ∈ 𝓝 (1 : AdelicGL2 (𝓞 K) K)) :
    ∃ m : ℕ, ((principalLevel (𝓞 K) K (Ideal.span {((m + 1 : ℕ) : 𝓞 K)}) ⊓ finiteAdelicGL2Subgroup K :
        Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) ⊆ V :=
  Ws31.LevelBasis.main K V _hV

end S_AutomorphicForm_exists_nat_principalLevel_inf_finiteAdelicGL2Subgroup_subset_of_mem_nhds_one
end P2MW
export P2MW.S_AutomorphicForm_exists_nat_principalLevel_inf_finiteAdelicGL2Subgroup_subset_of_mem_nhds_one (solution)
