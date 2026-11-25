-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T08:43:52.826641+00:00
-- url     : https://prove2.me/theorems/2a127ae4-8ef7-4870-a3e2-da6cefbe66de
-- title:
--   PTilde Vanish Cone
-- statement:
--   Definitions and structural lemmas for PTilde Vanish Cone, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishCone.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
section ConeE
variable (S : Type u) [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
def ConeE (_S : Type u) (_x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] : Type v := ℤ →₀ E
instance : AddCommGroup (ConeE S x E) := inferInstanceAs (AddCommGroup (ℤ →₀ E))
instance : Module Ω (ConeE S x E) := inferInstanceAs (Module Ω (ℤ →₀ E))
instance : Module S (ConeE S x E) := inferInstanceAs (Module S (ℤ →₀ E))
def coeffE (c : ℤ) : ConeE S x E →ₗ[S] E := Finsupp.lapply c
def singleE (c : ℤ) : E →ₗ[S] ConeE S x E := Finsupp.lsingle c
variable {S x E}
theorem coneE_ext {w w' : ConeE S x E} (h : ∀ d, coeffE S x E d w = coeffE S x E d w') : w = w' :=
  Finsupp.ext h
theorem coeffE_singleE_same (c : ℤ) (v : E) : coeffE S x E c (singleE S x E c v) = v :=
  Finsupp.single_eq_same
theorem coeffE_singleE_ne {c d : ℤ} (h : c ≠ d) (v : E) : coeffE S x E d (singleE S x E c v) = 0 :=
  Finsupp.single_eq_of_ne h.symm
theorem coeffE_omega_smul (a : Ω) (w : ConeE S x E) (c : ℤ) : coeffE S x E c (a • w) = a • coeffE S x E c w :=
  rfl
def suppE (w : ConeE S x E) : Finset ℤ := Finsupp.support (show ℤ →₀ E from w)
theorem sum_singleE (w : ConeE S x E) : ∑ c ∈ suppE w, singleE S x E c (coeffE S x E c w) = w :=
  Finsupp.sum_single (show ℤ →₀ E from w)
variable (S x E)
def shiftE : Multiplicative ℤ →* Module.End Ω (ConeE S x E) where
  toFun n := (Finsupp.domLCongr (M := E) (R := Ω) (Equiv.addRight n.toAdd)).toLinearMap
  map_one' := LinearMap.ext fun w => Finsupp.ext fun c => by
    change (Finsupp.equivMapDomain (Equiv.addRight (0 : ℤ)) (show ℤ →₀ E from w)) c = (show ℤ →₀ E from w) c
    rw [Finsupp.equivMapDomain_apply]
    simp only [Equiv.addRight_symm_apply, neg_zero, add_zero]
  map_mul' a b := LinearMap.ext fun w => Finsupp.ext fun c => by
    change (Finsupp.equivMapDomain (Equiv.addRight (a.toAdd + b.toAdd)) (show ℤ →₀ E from w)) c =
      (Finsupp.equivMapDomain (Equiv.addRight a.toAdd)
        (Finsupp.equivMapDomain (Equiv.addRight b.toAdd) (show ℤ →₀ E from w))) c
    rw [Finsupp.equivMapDomain_apply, Finsupp.equivMapDomain_apply, Finsupp.equivMapDomain_apply]
    simp only [Equiv.addRight_symm_apply]
    congr 1
    abel
variable {S x E} in
theorem coeffE_shiftE (n : ℤ) (w : ConeE S x E) (c : ℤ) :
    coeffE S x E c (shiftE S x E (Multiplicative.ofAdd n) w) = coeffE S x E (c - n) w := by
  change (Finsupp.equivMapDomain (Equiv.addRight n) (show ℤ →₀ E from w)) c = _
  rw [Finsupp.equivMapDomain_apply]
  simp only [Equiv.addRight_symm_apply]
  rfl
def lpActE : LaurentPolynomial Ω →ₐ[Ω] Module.End Ω (ConeE S x E) :=
  AddMonoidAlgebra.lift Ω (Module.End Ω (ConeE S x E)) ℤ (shiftE S x E)
def coneE : Poly S N →+* Module.End Ω (ConeE S x E) :=
  (lpActE S x E).toRingHom.comp ((ConeLaurent.toLP S x).comp (coneLaurent S x))
instance : Module (Poly S N) (ConeE S x E) := Module.compHom _ (coneE S x E)
variable {S x E}
theorem coneE_smul (p : Poly S N) (w : ConeE S x E) : p • w = coneE S x E p w := rfl
theorem coeffE_smul_of_isHomogeneous {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e)
    (w : ConeE S x E) (c : ℤ) : coeffE S x E c (f • w) = aeval x f • coeffE S x E (c - e) w := by
  rw [coneE_smul]
  change coeffE S x E c (lpActE S x E (ConeLaurent.toLP S x (coneLaurent S x f)) w) = _
  rw [coneLaurent_of_isHomogeneous hf, ConeLaurent.toLaurent_ofLaurent, lpActE, AddMonoidAlgebra.lift_single,
    LinearMap.smul_apply, coeffE_omega_smul, coeffE_shiftE]
theorem coneE_C (s : S) (w : ConeE S x E) : coneE S x E (C s) w = s • w := by
  refine coneE_ext fun d => ?_
  have h := coeffE_smul_of_isHomogeneous (x := x) (isHomogeneous_C (Fin (N + 1)) s) w d
  rw [coneE_smul] at h
  rw [h, aeval_C, Nat.cast_zero, sub_zero, algebraMap_smul, map_smul]
instance : IsScalarTower S (Poly S N) (ConeE S x E) where
  smul_assoc s p w := by
    rw [Algebra.smul_def, mul_smul, MvPolynomial.algebraMap_eq]
    exact coneE_C s (p • w)
end ConeE
section SubE
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E)
def FinGradedSub.coneSubE : Submodule (Poly S N) (ConeE S x E) where
  carrier := {w | ∀ c, coeffE S x E c w ∈ M.piece c}
  add_mem' ha hb c := by rw [map_add]; exact add_mem (ha c) (hb c)
  zero_mem' c := by rw [map_zero]; exact zero_mem _
  smul_mem' p w hw c := by
    change coeffE S x E c (p • w) ∈ M.piece c
    rw [← sum_homogeneousComponent p, Finset.sum_smul, map_sum]
    refine Submodule.sum_mem _ fun e _ => ?_
    rw [coeffE_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous e p)]
    have := M.smul_mem e (c - e) _ _ (homogeneousComponent_isHomogeneous e p) (hw (c - e))
    rwa [sub_add_cancel] at this
theorem FinGradedSub.singleE_mem_coneSubE {c : ℤ} {v : E} (hv : v ∈ M.piece c) :
    singleE S x E c v ∈ M.coneSubE := fun d => by
  by_cases h : c = d
  · subst h; rw [coeffE_singleE_same]; exact hv
  · rw [coeffE_singleE_ne h]; exact zero_mem _
def FinGradedSub.conePieceE (a : ℤ) : Submodule S M.coneSubE where
  carrier := {m | ∀ d, d ≠ a → coeffE S x E d (m : ConeE S x E) = 0}
  add_mem' ha hb d hd := by rw [Submodule.coe_add, map_add, ha d hd, hb d hd, add_zero]
  zero_mem' d _ := by rw [Submodule.coe_zero, map_zero]
  smul_mem' s m hm d hd := by rw [Submodule.coe_smul_of_tower, map_smul, hm d hd, smul_zero]
theorem FinGradedSub.eq_singleE_of_mem_conePieceE {a : ℤ} {m : M.coneSubE} (hm : m ∈ M.conePieceE a) :
    (m : ConeE S x E) = singleE S x E a (coeffE S x E a m) := by
  refine coneE_ext fun d => ?_
  by_cases h : a = d
  · subst h; rw [coeffE_singleE_same]
  · rw [coeffE_singleE_ne h, hm d (Ne.symm h)]
theorem FinGradedSub.singleE_mem_conePieceE {c : ℤ} {v : E} (hv : v ∈ M.piece c) :
    (⟨singleE S x E c v, M.singleE_mem_coneSubE hv⟩ : M.coneSubE) ∈ M.conePieceE c :=
  fun _ hd => coeffE_singleE_ne (Ne.symm hd) v
def FinGradedSub.coneGradedE : GradedPMod S N M.coneSubE where
  piece := M.conePieceE
  isInternal := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
    · refine iSupIndep_def.mpr fun a => Submodule.disjoint_def.mpr fun m hm hm' => ?_
      have h0 : coeffE S x E a (m : ConeE S x E) = 0 := by
        have hle : (⨆ (j : ℤ) (_ : j ≠ a), M.conePieceE j) ≤
            LinearMap.ker ((coeffE S x E a).comp ((M.coneSubE.subtype).restrictScalars S)) :=
          iSup₂_le fun j hj m hm => hm a (Ne.symm hj)
        exact hle hm'
      apply Subtype.ext
      rw [M.eq_singleE_of_mem_conePieceE hm, h0, map_zero]
      rfl
    · refine eq_top_iff.mpr fun m _ => ?_
      have hm : m = ∑ c ∈ suppE (m : ConeE S x E),
          (⟨singleE S x E c (coeffE S x E c m), M.singleE_mem_coneSubE (m.2 c)⟩ : M.coneSubE) := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        exact (sum_singleE (m : ConeE S x E)).symm
      rw [hm]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.mem_iSup_of_mem c (M.singleE_mem_conePieceE (m.2 c))
  smul_mem d c p m hp hm e he := by
    change coeffE S x E e (p • (m : ConeE S x E)) = 0
    rw [coeffE_smul_of_isHomogeneous hp, hm (e - d) (by omega), smul_zero]
end SubE
end
end GroundTheory.Heights₂.Heights.Kleiman


