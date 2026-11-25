-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqCech
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqCech
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:38:51.69033+00:00
-- url     : https://prove2.me/theorems/bfb97399-bb05-4f48-b219-68bdcabcca7b
-- title:
--   PTwin Eq Cech
-- statement:
--   Definitions and structural lemmas for PTwin Eq Cech, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqCech.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltBis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_Generated_equiv_67711faab90f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedMod_equiv_bab59235570c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_IsGradedHom_equiv_a15063e9bd3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_PrimeFiltration_equiv_055a468f012b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_bundleA_equiv_9a6f65d8882f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRingI_equiv_6c221ab935ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRing_equiv_3295007ad279
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_dimCl_equiv_c39cbd206b03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lineX_equiv_6acfbe997019
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lmul_equiv_a9ac80d74948
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lpow_equiv_da141a3f94b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_polyGraded_equiv_07714b7c3c16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_equiv_51d02eb19002
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_equiv_61178bbb85a9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
namespace GradedCech
variable (S : Type) [CommRing S] (N : ℕ)
theorem exists_monomial_of_mem_monos {I : Finset (Fin (N + 1))} {s : Poly S N}
    (hs : s ∈ Kleiman.monos (S := S) I) :
    ∃ k : Fin (N + 1) →₀ ℕ, k.support ⊆ I ∧ s = monomial k 1 := by
  classical
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨Finsupp.single i 1, ?_, rfl⟩
    intro j hj
    rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hj
    subst hj
    exact_mod_cast hi
  | one => exact ⟨0, by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, Finsupp.support_add.trans (Finset.union_subset ha hb), by rw [monomial_mul, one_mul]⟩
theorem isHomogeneous_Xprod_pow (I : Finset (Fin (N + 1))) (n : ℕ) :
    (IndefiniteRowSideFullHecke.Kleiman.Xprod S N I ^ n).IsHomogeneous (I.card * n) := by
  have h := IsHomogeneous.prod (R := S) I (fun i => (X i : Poly S N)) (fun _ => 1)
    (fun i _ => isHomogeneous_X S i)
  rw [Finset.sum_const, smul_eq_mul, mul_one] at h
  exact h.pow n
theorem exists_mul_eq_Xprod_pow [Nontrivial S] {I : Finset (Fin (N + 1))} {s : Poly S N}
    (hs : s ∈ Kleiman.monos (S := S) I) {e : ℕ} (he : s.IsHomogeneous e) :
    ∃ (n : ℕ) (t : Poly S N) (d : ℕ), t.IsHomogeneous d ∧ e + d = I.card * n ∧
      s * t = IndefiniteRowSideFullHecke.Kleiman.Xprod S N I ^ n := by
  classical
  obtain ⟨k, hk, rfl⟩ := exists_monomial_of_mem_monos S N hs
  have hke : k.degree = e :=
    (isHomogeneous_monomial (1 : S) rfl).inj_right he (by rw [Ne, monomial_eq_zero]; exact one_ne_zero)
  set D : Fin (N + 1) →₀ ℕ := ∑ i ∈ I, Finsupp.single i e with hD
  have hkD : k ≤ D := by
    intro j
    rw [hD, Finsupp.finsetSum_apply]
    by_cases hj : j ∈ I
    · rw [Finset.sum_eq_single j (fun b _ hb => Finsupp.single_eq_of_ne hb.symm) (fun h => (h hj).elim),
        Finsupp.single_eq_same, ← hke]
      exact Finsupp.le_degree j k
    · have : k j = 0 := Finsupp.notMem_support_iff.mp (fun h => hj (hk h))
      rw [this]
      exact Nat.zero_le _
  have hprod : IndefiniteRowSideFullHecke.Kleiman.Xprod S N I ^ e = monomial D 1 := by
    rw [IndefiniteRowSideFullHecke.Kleiman.Xprod, ← Finset.prod_pow, hD, monomial_sum_one]
    exact Finset.prod_congr rfl fun i _ => X_pow_eq_monomial
  have hst : monomial k (1 : S) * monomial (D - k) 1 = IndefiniteRowSideFullHecke.Kleiman.Xprod S N I ^ e := by
    rw [monomial_mul, one_mul, add_tsub_cancel_of_le hkD, hprod]
  refine ⟨e, monomial (D - k) 1, (D - k).degree, isHomogeneous_monomial 1 rfl, ?_, hst⟩
  have h1 := (he.mul (isHomogeneous_monomial (1 : S) (d := D - k) rfl))
  rw [hst] at h1
  refine h1.inj_right (isHomogeneous_Xprod_pow S N I e) ?_
  rw [hprod, Ne, monomial_eq_zero]
  exact one_ne_zero
variable (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
def locEquiv (I : Finset (Fin (N + 1))) : IndefiniteRowSideFullHecke.Kleiman.LocM S N M I ≃ₗ[S] Kleiman.LocMod S N M I where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' a x := (algebraMap_smul (Poly S N) a x).symm
  left_inv _ := rfl
  right_inv _ := rfl
theorem mem_locPiece_iff (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (c : ℤ) (I : Kleiman.StdCell N)
    (x : IndefiniteRowSideFullHecke.Kleiman.LocM S N M I.1) :
    x ∈ IndefiniteRowSideFullHecke.Kleiman.locPiece S N M G I.1 c ↔
      locEquiv S N M I.1 x ∈ Kleiman.degLoc (gradedEquiv S N M G) c I := by
  have key : (IndefiniteRowSideFullHecke.Kleiman.locPiece S N M G I.1 c).map (locEquiv S N M I.1 : _ →ₗ[S] _) =
      Kleiman.degLoc (gradedEquiv S N M G) c I := by
    rw [IndefiniteRowSideFullHecke.Kleiman.locPiece, Submodule.map_span, Kleiman.degLoc]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨_, ⟨n, m, hm, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨m, ⟨IndefiniteRowSideFullHecke.Kleiman.Xprod S N I.1 ^ n,
        pow_mem (IndefiniteRowSideFullHecke.Kleiman.Xprod_mem_denoms S N I.1) n⟩, c + n * I.1.card, I.1.card * n, hm,
        isHomogeneous_Xprod_pow S N I.1 n, by push_cast; ring, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨m, s, a, e, hm, hs, hae, rfl⟩
      rcases subsingleton_or_nontrivial S with hS | hS
      · have hP : Subsingleton (Poly S N) :=
          ⟨fun p q => MvPolynomial.ext _ _ fun _ => Subsingleton.elim _ _⟩
        have hm0 : m = 0 := by
          rw [← one_smul (Poly S N) m, Subsingleton.elim (1 : Poly S N) 0, zero_smul]
        subst hm0
        rw [LocalizedModule.zero_mk]
        exact zero_mem _
      · obtain ⟨n, t, d, ht, hed, hst⟩ := exists_mul_eq_Xprod_pow S N s.2 hs
        have hdeg : a + (d : ℤ) = c + (n : ℤ) * (I.1.card : ℤ) := by
          have h := congrArg (Nat.cast (R := ℤ)) hed
          push_cast at h
          linarith
        have htm : t • m ∈ G.piece (c + n * I.1.card) := by
          rw [← hdeg]
          exact (gradedEquiv S N M G).smul_mem d a t m ht hm
        refine Submodule.subset_span ⟨IndefiniteRowSideFullHecke.Kleiman.locFrac S N M I.1 (t • m) n, ⟨n, t • m, htm, rfl⟩, ?_⟩
        change (LocalizedModule.mk (t • m) ⟨IndefiniteRowSideFullHecke.Kleiman.Xprod S N I.1 ^ n,
          pow_mem (IndefiniteRowSideFullHecke.Kleiman.Xprod_mem_denoms S N I.1) n⟩ : LocalizedModule (Kleiman.monos (S := S) I.1) M) =
          LocalizedModule.mk m s
        refine LocalizedModule.mk_eq.2 ⟨1, ?_⟩
        simp only [one_smul, Submonoid.smul_def]
        rw [← mul_smul, hst]
  rw [← key, Submodule.mem_map_equiv]
  rfl
theorem cechD_apply_pos {ι k : Type} [CommRing k] [LinearOrder ι] (C : IndefiniteRowSideFullHecke.Kleiman.CechSystem ι k)
    (v : ∀ I, C.V I) (J : Finset ι) (h : C.good J) :
    IndefiniteRowSideFullHecke.Kleiman.cechD C v J =
      ∑ j ∈ J, IndefiniteRowSideFullHecke.Kleiman.cechSign J j • C.res (Finset.erase_subset j J) (v (J.erase j)) := by
  simp only [IndefiniteRowSideFullHecke.Kleiman.cechD, LinearMap.pi_apply, if_pos h, LinearMap.sum_apply]
  rfl
theorem cechD_apply_neg {ι k : Type} [CommRing k] [LinearOrder ι] (C : IndefiniteRowSideFullHecke.Kleiman.CechSystem ι k)
    (v : ∀ I, C.V I) (J : Finset ι) (h : ¬ C.good J) : IndefiniteRowSideFullHecke.Kleiman.cechD C v J = 0 := by
  simp only [IndefiniteRowSideFullHecke.Kleiman.cechD, LinearMap.pi_apply, if_neg h]
  rfl
variable {S N M}
def extC (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (c : ℤ) (i : ℕ) :
    Kleiman.Cech.Cochain (Kleiman.locSys S N M) i →ₗ[S] (∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I) :=
  LinearMap.pi fun I => if h : I.Nonempty ∧ I.card = i + 1 then
      (locEquiv S N M I).symm.toLinearMap ∘ₗ
        LinearMap.proj (R := S) (φ := fun J : Kleiman.Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i =>
          Kleiman.LocMod S N M J.1.1) ⟨⟨I, h.1, Finset.subset_univ I⟩, h.2⟩
    else 0
def resC (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (c : ℤ) (i : ℕ) :
    (∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I) →ₗ[S] Kleiman.Cech.Cochain (Kleiman.locSys S N M) i :=
  LinearMap.pi fun J => (locEquiv S N M J.1.1).toLinearMap ∘ₗ LinearMap.proj J.1.1
variable (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (c : ℤ)
theorem extC_apply_pos {i : ℕ} (v : Kleiman.Cech.Cochain (Kleiman.locSys S N M) i)
    (I : Finset (Fin (N + 1))) (h : I.Nonempty ∧ I.card = i + 1) :
    extC G c i v I = (locEquiv S N M I).symm (v ⟨⟨I, h.1, Finset.subset_univ I⟩, h.2⟩) := by
  simp only [extC, LinearMap.pi_apply, dif_pos h]
  rfl
theorem extC_apply_neg {i : ℕ} (v : Kleiman.Cech.Cochain (Kleiman.locSys S N M) i)
    (I : Finset (Fin (N + 1))) (h : ¬ (I.Nonempty ∧ I.card = i + 1)) : extC G c i v I = 0 := by
  simp only [extC, LinearMap.pi_apply, dif_neg h]
  rfl
theorem resC_apply {i : ℕ} (w : ∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I)
    (J : Kleiman.Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) :
    resC G c i w J = locEquiv S N M J.1.1 (w J.1.1) := rfl
theorem resC_extC {i : ℕ} (v : Kleiman.Cech.Cochain (Kleiman.locSys S N M) i) :
    resC G c i (extC G c i v) = v := by
  funext J
  rw [resC_apply G c, extC_apply_pos G c v J.1.1 ⟨J.1.2.1, J.2⟩]
  rfl
theorem mem_cechC_iff {i : ℕ} (w : ∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I) :
    w ∈ IndefiniteRowSideFullHecke.Kleiman.cechC (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) i ↔
      ∀ I, (I.Nonempty ∧ I.card = i + 1 → w I ∈ (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).piece I) ∧
        (¬ (I.Nonempty ∧ I.card = i + 1) → w I = 0) := by
  constructor
  · intro hw I
    have hI := hw I (Set.mem_univ I)
    beta_reduce at hI
    split_ifs at hI with h
    · exact ⟨fun _ => hI, fun h' => (h' h).elim⟩
    · exact ⟨fun h' => (h h').elim, fun _ => (Submodule.mem_bot S).1 hI⟩
  · intro hw
    rw [IndefiniteRowSideFullHecke.Kleiman.cechC, Submodule.mem_pi]
    intro I _
    split_ifs with h
    · exact (hw I).1 h
    · exact (Submodule.mem_bot S).2 ((hw I).2 h)
theorem extC_resC {i : ℕ} (w : ∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I)
    (hw : w ∈ IndefiniteRowSideFullHecke.Kleiman.cechC (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) i) :
    extC G c i (resC G c i w) = w := by
  funext I
  by_cases h : I.Nonempty ∧ I.card = i + 1
  · rw [extC_apply_pos G c _ I h]
    rfl
  · rw [extC_apply_neg G c _ I h, (((mem_cechC_iff G c w).1 hw I).2 h)]
theorem extC_mem {i : ℕ} (v : Kleiman.Cech.Cochain (Kleiman.locSys S N M) i)
    (hv : v ∈ Kleiman.Cech.Cdeg (Kleiman.locSys S N M) (Kleiman.degLoc (gradedEquiv S N M G) c) i) :
    extC G c i v ∈ IndefiniteRowSideFullHecke.Kleiman.cechC (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) i := by
  rw [mem_cechC_iff]
  intro I
  refine ⟨fun h => ?_, fun h => extC_apply_neg G c v I h⟩
  rw [extC_apply_pos G c v I h]
  exact (mem_locPiece_iff S N M G c ⟨I, h.1, Finset.subset_univ I⟩ _).2
    (hv ⟨⟨I, h.1, Finset.subset_univ I⟩, h.2⟩ (Set.mem_univ _))
theorem resC_mem {i : ℕ} (w : ∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I)
    (hw : w ∈ IndefiniteRowSideFullHecke.Kleiman.cechC (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) i) :
    resC G c i w ∈ Kleiman.Cech.Cdeg (Kleiman.locSys S N M) (Kleiman.degLoc (gradedEquiv S N M G) c) i :=
  fun J _ => (mem_locPiece_iff S N M G c J.1 _).1 (((mem_cechC_iff G c w).1 hw J.1.1).1 ⟨J.1.2.1, J.2⟩)
theorem cechD_extC {i : ℕ} (v : Kleiman.Cech.Cochain (Kleiman.locSys S N M) i) :
    IndefiniteRowSideFullHecke.Kleiman.cechD (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) (extC G c i v) =
      extC G c (i + 1) (Kleiman.Cech.d (Kleiman.locSys S N M) Kleiman.locResS i v) := by
  funext J
  by_cases hJ : J.Nonempty
  · have hg : (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).good J := hJ
    refine (cechD_apply_pos _ _ J hg).trans ?_
    by_cases hc : J.card = i + 1 + 1
    · rw [extC_apply_pos G c _ J ⟨hJ, hc⟩, Kleiman.Cech.d_apply, map_sum, ← Finset.sum_coe_sort J]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj : (J.erase j).Nonempty ∧ (J.erase j).card = i + 1 := by
        rw [Finset.card_erase_of_mem j.2, hc]
        refine ⟨Finset.card_pos.mp ?_, rfl⟩
        rw [Finset.card_erase_of_mem j.2, hc]
        omega
      rw [extC_apply_pos G c _ _ hj, map_zsmul]
      rfl
    · rw [extC_apply_neg G c _ J (fun h => hc h.2)]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hne : ¬ ((J.erase j).Nonempty ∧ (J.erase j).card = i + 1) := by
        rintro ⟨-, h⟩
        have h1 := Finset.card_erase_of_mem hj
        have h2 := Finset.card_pos.mpr hJ
        omega
      rw [extC_apply_neg G c _ _ hne, map_zero, smul_zero]
  · have hg : ¬ (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).good J := hJ
    rw [cechD_apply_neg _ _ J hg, extC_apply_neg G c _ J (fun h => hJ h.1)]
def zEquiv (i : ℕ) :
    IndefiniteRowSideFullHecke.Kleiman.gradedZ S N M G i c ≃ₗ[S]
      Kleiman.Cech.cocyDeg (Kleiman.locSys S N M) (Kleiman.degLoc (gradedEquiv S N M G) c)
        Kleiman.locResS i where
  toFun w := ⟨resC G c i w.1, by
    refine ⟨LinearMap.mem_ker.2 ?_, resC_mem G c w.1 w.2.1⟩
    have h := cechD_extC G c (resC G c i w.1)
    rw [extC_resC G c w.1 w.2.1, LinearMap.mem_ker.mp w.2.2] at h
    have h' := congrArg (resC G c (i + 1)) h
    rw [resC_extC G c, map_zero] at h'
    exact h'.symm⟩
  invFun v := ⟨extC G c i v.1, extC_mem G c v.1 v.2.2,
    LinearMap.mem_ker.2 (by rw [cechD_extC G c, LinearMap.mem_ker.mp v.2.1, map_zero])⟩
  map_add' x y := Subtype.ext (map_add (resC G c i) x.1 y.1)
  map_smul' a x := Subtype.ext (map_smul (resC G c i) a x.1)
  left_inv w := Subtype.ext (extC_resC G c w.1 w.2.1)
  right_inv v := Subtype.ext (resC_extC G c v.1)
theorem zEquiv_map_bdry (i : ℕ) :
    ((IndefiniteRowSideFullHecke.Kleiman.cechB (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) i).comap
        (IndefiniteRowSideFullHecke.Kleiman.cechZ (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) i).subtype).map
        (zEquiv G c i : IndefiniteRowSideFullHecke.Kleiman.gradedZ S N M G i c →ₗ[S] _) =
      (Kleiman.Cech.bdryDeg (Kleiman.locSys S N M) (Kleiman.degLoc (gradedEquiv S N M G) c)
        Kleiman.locResS i).comap
        (Kleiman.Cech.cocyDeg (Kleiman.locSys S N M) (Kleiman.degLoc (gradedEquiv S N M G) c)
          Kleiman.locResS i).subtype := by
  ext y
  rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
  change extC G c i y.1 ∈ IndefiniteRowSideFullHecke.Kleiman.cechB (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) i ↔
    y.1 ∈ Kleiman.Cech.bdryDeg (Kleiman.locSys S N M) (Kleiman.degLoc (gradedEquiv S N M G) c)
      Kleiman.locResS i
  cases i with
  | zero =>
    simp only [IndefiniteRowSideFullHecke.Kleiman.cechB, Kleiman.Cech.bdryDeg, Submodule.mem_bot]
    constructor
    · intro h
      have h' := congrArg (resC G c 0) h
      rwa [resC_extC G c, map_zero] at h'
    · intro h
      rw [h, map_zero]
  | succ i =>
    simp only [IndefiniteRowSideFullHecke.Kleiman.cechB, Kleiman.Cech.bdryDeg, Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, hwy⟩
      refine ⟨resC G c i w, resC_mem G c w hw, ?_⟩
      have h := cechD_extC G c (resC G c i w)
      rw [extC_resC G c w hw, hwy] at h
      have h' := congrArg (resC G c (i + 1)) h
      rw [resC_extC G c, resC_extC] at h'
      exact h'.symm
    · rintro ⟨t, ht, hty⟩
      exact ⟨extC G c i t, extC_mem G c t ht, by rw [cechD_extC G c, hty]⟩
def hEquiv (i : ℕ) :
    IndefiniteRowSideFullHecke.Kleiman.gradedH S N M G i c ≃ₗ[S] Kleiman.cohom (gradedEquiv S N M G) i c :=
  Submodule.Quotient.equiv _ _ (zEquiv G c i) (zEquiv_map_bdry G c i)
end GradedCech
end
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq


