-- Prove2me | Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_TorusProjIsOpenQuotientMap
-- name    : Formalism_LatticeTheta_LatticeThetaProofs_TorusProjIsOpenQuotientMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:03:23.205347+00:00
-- url     : https://prove2.me/theorems/413f74a1-386c-45ba-a9c8-f1beca9c2437
-- title:
--   Torus Proj Is Open Quotient Map
-- statement:
--   Definitions and structural lemmas for Torus Proj Is Open Quotient Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/TorusProjIsOpenQuotientMap.lean

import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_InnerDualVecBasis
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_FundamentalDomainEqPreimage
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
open MeasureTheory Set Complex
open scoped RealInnerProductSpace
noncomputable section
namespace Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def torusProj (ι : Type*) : (ι → ℝ) → UnitAddTorus ι := fun t i => (t i : UnitAddCircle)
theorem torusProj_isOpenQuotientMap : IsOpenQuotientMap (torusProj ι) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
theorem torusProj_surjective : Function.Surjective (torusProj ι) := by
  intro θ
  choose t ht using fun i => QuotientAddGroup.mk_surjective (θ i)
  exact ⟨t, funext ht⟩
theorem torusProj_eq (s t : ι → ℝ) (h : torusProj ι s = torusProj ι t) :
    ∃ n : ι → ℤ, t = s + fun i => (n i : ℝ) := by
  have hi : ∀ i, ∃ k : ℤ, t i = s i + (k : ℝ) := by
    intro i
    have h1 := congrFun h i
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp h1)
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    linarith
  choose n hn using hi
  exact ⟨n, funext fun i => by simp [hn i]⟩
theorem equivFunL_symm_eq (e : Module.Basis ι ℝ V) (t : ι → ℝ) :
    e.equivFunL.symm t = ∑ i, t i • e i := by
  first
  | exact e.equivFun_symm_apply t
  | simp [Module.Basis.equivFunL, Module.Basis.equivFun_symm_apply]
theorem periodic_comp (e : Module.Basis ι ℝ V) (G : V → ℂ)
    (hper : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x)
    (s : ι → ℝ) (n : ι → ℤ) :
    G (e.equivFunL.symm (s + fun i => (n i : ℝ))) = G (e.equivFunL.symm s) := by
  rw [map_add, add_comm]
  apply hper
  rw [equivFunL_symm_eq]
  refine Submodule.sum_mem _ fun i _ => ?_
  show ((n i : ℝ)) • e i ∈ _
  rw [Int.cast_smul_eq_zsmul ℝ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
def torusFun (e : Module.Basis ι ℝ V) (G : V → ℂ) : UnitAddTorus ι → ℂ :=
  fun θ => G (e.equivFunL.symm (Function.surjInv (torusProj_surjective (ι := ι)) θ))
theorem torusFun_proj (e : Module.Basis ι ℝ V) (G : V → ℂ)
    (hper : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x) (t : ι → ℝ) :
    torusFun e G (torusProj ι t) = G (e.equivFunL.symm t) := by
  obtain ⟨n, hn⟩ := torusProj_eq _ t
    (Function.surjInv_eq (torusProj_surjective (ι := ι)) (torusProj ι t))
  have h1 := periodic_comp e G hper (Function.surjInv (torusProj_surjective (ι := ι)) (torusProj ι t)) n
  rw [← hn] at h1
  exact h1.symm
theorem torusFun_continuous (e : Module.Basis ι ℝ V) (G : V → ℂ) (hG : Continuous G)
    (hper : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x) :
    Continuous (torusFun e G) := by
  rw [torusProj_isOpenQuotientMap.isQuotientMap.continuous_iff]
  have h1 : torusFun e G ∘ torusProj ι = fun t => G (e.equivFunL.symm t) :=
    funext (torusFun_proj e G hper)
  rw [h1]
  exact hG.comp e.equivFunL.symm.continuous
def torusFunC (e : Module.Basis ι ℝ V) (G : V → ℂ) (hG : Continuous G)
    (hper : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x) :
    C(UnitAddTorus ι, ℂ) :=
  ⟨torusFun e G, torusFun_continuous e G hG hper⟩
end Formalism.H


