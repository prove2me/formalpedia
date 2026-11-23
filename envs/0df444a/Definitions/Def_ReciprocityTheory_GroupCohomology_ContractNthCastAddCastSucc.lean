-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_ContractNthCastAddCastSucc
-- name    : ReciprocityTheory_GroupCohomology_ContractNthCastAddCastSucc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:36.112744+00:00
-- url     : https://prove2.me/theorems/2d30d814-0a13-46e2-a6ea-0be0bcd6cd5f
-- title:
--   Contract Nth Cast Add Cast Succ
-- statement:
--   Definitions and structural lemmas for Contract Nth Cast Add Cast Succ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ContractNthCastAddCastSucc.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_Z_apply
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_H
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_add
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_d
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_neg
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_sub
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_zero
import Theorems.Thm_ReciprocityTheory_Gal_dn_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.Z_apply
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.comp_f
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_H
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_f
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_add
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_d
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_neg
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_smul
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_sub
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_zero


set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal
noncomputable section
universe u
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
section S1
variable {G : Type u} [Group G]
theorem prod_ofFn_eq_partialProd {n : ℕ} (f : Fin n → G) : (List.ofFn f).prod = Fin.partialProd f (Fin.last n) := by
  simp only [Fin.partialProd, Fin.val_last]
  rw [List.take_of_length_le (by simp)]
theorem prod_ofFn_contractNth {m : ℕ} (h : Fin (m + 1) → G) (j : Fin m) :
    (List.ofFn (Fin.contractNth j.castSucc (· * ·) h)).prod = (List.ofFn h).prod := by
  rw [prod_ofFn_eq_partialProd, prod_ofFn_eq_partialProd, Fin.partialProd_contractNth]
  simp only [Function.comp_apply]
  congr 1
  ext
  simp [Fin.succAbove]
theorem apply_eq_of_val_eq {n : ℕ} (g : Fin n → G) {i j : Fin n} (h : (i : ℕ) = j) : g i = g j :=
  congrArg g (Fin.ext h)
theorem mul_eq_mul_of_val_eq {n : ℕ} (g : Fin n → G) {i j k l : Fin n} (h : (i : ℕ) = j) (h' : (k : ℕ) = l) :
    g i * g k = g j * g l := by rw [apply_eq_of_val_eq g h, apply_eq_of_val_eq g h']
variable {p q : ℕ} (e : p + 1 + q = p + q + 1) (g : Fin (p + q + 1) → G)
theorem contractNth_castAdd_castSucc (j i : Fin p) : (Fin.castAdd (q + 1) j).contractNth (· * ·) g (Fin.castAdd q i) =
    (Fin.castSucc j).contractNth (· * ·) (fun i : Fin (p + 1) => g (Fin.cast e (Fin.castAdd q i))) i := by
  simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_castAdd]
  split_ifs <;> first | omega | exact apply_eq_of_val_eq g (by simp <;> omega) | exact mul_eq_mul_of_val_eq g (by simp <;> omega) (by simp <;> omega)
theorem contractNth_castAdd_natAdd (j : Fin p) (k : Fin q) : (Fin.castAdd (q + 1) j).contractNth (· * ·) g (Fin.natAdd p k) =
    g (Fin.natAdd p k).succ := by
  simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_castAdd, Fin.val_natAdd]
  split_ifs <;> first | omega | exact apply_eq_of_val_eq g (by simp <;> omega) | exact mul_eq_mul_of_val_eq g (by simp <;> omega) (by simp <;> omega)
theorem contractNth_natAdd_castAdd (k : Fin (q + 1)) (i : Fin p) : (Fin.natAdd p k).contractNth (· * ·) g (Fin.castAdd q i) =
    g (Fin.castAdd (q + 1) i) := by
  simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_castAdd, Fin.val_natAdd]
  split_ifs <;> first | omega | exact apply_eq_of_val_eq g (by simp <;> omega) | exact mul_eq_mul_of_val_eq g (by simp <;> omega) (by simp <;> omega)
theorem contractNth_natAdd_natAdd (k : Fin (q + 1)) (l : Fin q) : (Fin.natAdd p k).contractNth (· * ·) g (Fin.natAdd p l) =
    k.contractNth (· * ·) (fun j : Fin (q + 1) => g (Fin.natAdd p j)) l := by
  simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_castAdd, Fin.val_natAdd]
  split_ifs <;> first | omega | exact apply_eq_of_val_eq g (by simp <;> omega) | exact mul_eq_mul_of_val_eq g (by simp <;> omega) (by simp <;> omega)
theorem cast_castAdd_succ (i : Fin p) : g (Fin.cast e (Fin.castAdd q i.succ)) = g (Fin.castAdd q i).succ :=
  apply_eq_of_val_eq g (by simp)
theorem cast_natAdd_succ (j : Fin q) : g (Fin.cast e (Fin.natAdd (p + 1) j)) = g (Fin.natAdd p j).succ :=
  apply_eq_of_val_eq g (by simp; omega)
theorem contractNth_last_cast : (Fin.last p).contractNth (· * ·) (fun i : Fin (p + 1) => g (Fin.cast e (Fin.castAdd q i))) =
    fun i => g (Fin.castAdd (q + 1) i) := by
  funext i
  simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_castAdd, Fin.val_last]
  split_ifs <;> first | omega | exact apply_eq_of_val_eq g (by simp <;> omega) | exact mul_eq_mul_of_val_eq g (by simp <;> omega) (by simp <;> omega)
theorem cast_castAdd_zero : g (Fin.cast e (Fin.castAdd q 0)) = g 0 := apply_eq_of_val_eq g (by simp)
theorem prod_ofFn_cast_zero : (List.ofFn fun i : Fin (p + 1) => g (Fin.cast e (Fin.castAdd q i))).prod =
    g 0 * (List.ofFn fun i : Fin p => g (Fin.castAdd q i).succ).prod := by
  rw [List.ofFn_succ, List.prod_cons, cast_castAdd_zero e g]
  simp only [cast_castAdd_succ e g]
theorem prod_ofFn_cast_last : (List.ofFn fun i : Fin (p + 1) => g (Fin.cast e (Fin.castAdd q i))).prod =
    (List.ofFn fun i : Fin p => g (Fin.castAdd (q + 1) i)).prod * g (Fin.natAdd p (0 : Fin (q + 1))) := by
  rw [List.ofFn_succ', List.prod_concat]
  congr 1
  all_goals first | exact apply_eq_of_val_eq g (by simp) | (congr 1; funext i; exact apply_eq_of_val_eq g (by simp)) | (congr 2; funext i; exact apply_eq_of_val_eq g (by simp))
end S1
section S2
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
theorem cupProduct_abelian_identity {V : Type*} [AddCommGroup V] {a b s1 s1' s2 s2' l f : V} (h0 : s1 = s1') (h1 : a = b) (h2 : s2 = s2')
    (h3 : l + f = 0) : a + (s1 + s2) = b + (s1' + l) + (f + s2') := by
  subst h0 h1 h2
  rw [eq_neg_of_add_eq_zero_left h3]
  abel
theorem cupProduct_leibniz {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) (f : (Fin p → G) → M.V)
    (f' : (Fin q → G) → N.V) (g : Fin (p + q + 1) → G) :
    dn P.rho (p + q) (cupFun b p q f f') g =
    cupFun b (p + 1) q (dn M.rho p f) f' (fun i => g (i.cast (by omega))) +
      (-1 : R) ^ p • cupFun b p (q + 1) f (dn N.rho q f') g := by
  have e : p + 1 + q = p + q + 1 := by omega
  simp only [dn_apply, cupFun, map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_add, Finset.smul_sum, smul_smul]
  rw [Fin.sum_univ_castSucc (n := p)]
  rw [show ∀ F : Fin (p + q + 1) → P.V, ∑ j, F j = ∑ j : Fin p, F (Fin.castAdd (q + 1) j) +
    ∑ k : Fin (q + 1), F (Fin.natAdd p k) from fun F => Fin.sum_univ_add (a := p) (b := q + 1) F]
  simp only [contractNth_castAdd_castSucc e g, contractNth_castAdd_natAdd g, contractNth_natAdd_castAdd g, contractNth_natAdd_natAdd g, cast_castAdd_succ e g, cast_natAdd_succ e g, contractNth_last_cast e g, cast_castAdd_zero e g,
    prod_ofFn_contractNth, Fin.val_castAdd, Fin.val_castSucc, Fin.val_natAdd, Fin.val_last]
  refine cupProduct_abelian_identity rfl ?_ ?_ ?_
  · rw [prod_ofFn_cast_zero e g, map_mul, Module.End.mul_apply, b.equiv]
  · exact Finset.sum_congr rfl fun x _ => by rw [← pow_add, add_assoc]
  · have hu : (fun j : Fin q => g (Fin.natAdd p j).succ) = fun i => g (Fin.natAdd p i.succ) :=
      funext fun j => apply_eq_of_val_eq g (by simp <;> omega)
    rw [prod_ofFn_cast_last e g, map_mul, Module.End.mul_apply, hu, pow_succ, mul_neg_one, neg_smul, neg_add_cancel]
end S2
section S3
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
theorem cupProduct_continuous {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) {f : (Fin p → G) → M.V}
    {f' : (Fin q → G) → N.V} (hf : Continuous f) (hf' : Continuous f') :
    Continuous (cupFun b p q f f') := by
  have hpr : Continuous fun g : Fin (p + q) → G => (List.ofFn fun i => g (Fin.castAdd q i)).prod := by
    simp only [List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ => continuous_apply _
  exact b.cont.comp (f := fun g : Fin (p + q) → G => (f fun i => g (Fin.castAdd q i),
      N.rho (List.ofFn fun i => g (Fin.castAdd q i)).prod (f' fun j => g (Fin.natAdd p j))))
    ((hf.comp (continuous_pi fun i => continuous_apply _)).prodMk
      (N.cont.comp (f := fun g : Fin (p + q) → G => ((List.ofFn fun i => g (Fin.castAdd q i)).prod,
        f' fun j => g (Fin.natAdd p j)))
        (hpr.prodMk (hf'.comp (continuous_pi fun j => continuous_apply _)))))
theorem cochain_add_val (M : TRep R G) (n : ℕ) (x y : M.coch.X n) : (x + y).1 = x.1 + y.1 := rfl
theorem cochain_smul_val (M : TRep R G) (n : ℕ) (r : R) (x : M.coch.X n) : (r • x).1 = r • x.1 := rfl
theorem cochain_zero_val (M : TRep R G) (n : ℕ) : (0 : M.coch.X n).1 = 0 := rfl
def cupCoch {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) :
    M.coch.X p →ₗ[R] N.coch.X q →ₗ[R] P.coch.X (p + q) :=
  LinearMap.mk₂ R (fun x y => ⟨cupFun b p q x.1 y.1, cupProduct_continuous b p q x.2 y.2⟩)
    (fun x x' y => Subtype.ext (funext fun g => by simp [cupFun, cochain_add_val, cochain_smul_val] <;> rfl))
    (fun r x y => Subtype.ext (funext fun g => by simp [cupFun, cochain_add_val, cochain_smul_val] <;> rfl))
    (fun x y y' => Subtype.ext (funext fun g => by simp [cupFun, cochain_add_val, cochain_smul_val] <;> rfl))
    (fun r x y => Subtype.ext (funext fun g => by simp [cupFun, cochain_add_val, cochain_smul_val] <;> rfl))
theorem cupCoch_val {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) (x : M.coch.X p) (y : N.coch.X q) :
    (cupCoch b p q x y).1 = cupFun b p q x.1 y.1 := rfl
theorem cochain_differential_val (M : TRep R G) (n : ℕ) (z : M.coch.X n) : (M.coch.d n z).1 = dn M.rho n z.1 := rfl
theorem mem_coboundaries_of_eq_d {P : TRep R G} {m n : ℕ} (h : m = n + 1) (z : P.coch.X m) (w : P.coch.X n)
    (hz : ∀ g, z.1 g = dn P.rho n w.1 fun i => g (Fin.cast h.symm i)) : z ∈ P.coch.B m := by
  subst h
  exact ⟨w, Subtype.ext (funext fun g => (hz g).symm)⟩
theorem cupProduct_coboundary_left {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) (x : M.coch.X p)
    (hx : x ∈ M.coch.B p) (y : N.coch.X q) (hy : N.coch.d q y = 0) :
    cupCoch b p q x y ∈ P.coch.B (p + q) := by
  rcases p with _ | p
  · have h0 : x = 0 := (Submodule.mem_bot R).1 hx
    subst h0
    rw [map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  · obtain ⟨u, rfl⟩ := hx
    have hy' : dn N.rho q y.1 = 0 := congrArg Subtype.val hy
    refine mem_coboundaries_of_eq_d (by omega) _ (cupCoch b p q u y) fun g => ?_
    rw [cupCoch_val, cupCoch_val, cochain_differential_val, cupProduct_leibniz, hy']
    simp [cupFun]
theorem cupProduct_coboundary_right {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) (x : M.coch.X p)
    (hx : M.coch.d p x = 0) (y : N.coch.X q) (hy : y ∈ N.coch.B q) :
    cupCoch b p q x y ∈ P.coch.B (p + q) := by
  rcases q with _ | q
  · have h0 : y = 0 := (Submodule.mem_bot R).1 hy
    subst h0
    rw [map_zero]
    exact Submodule.zero_mem _
  · obtain ⟨v, rfl⟩ := hy
    have hx' : dn M.rho p x.1 = 0 := congrArg Subtype.val hx
    refine mem_coboundaries_of_eq_d (n := p + q) rfl _ ((-1 : R) ^ p • cupCoch b p q x v) fun g => ?_
    rw [cupCoch_val, cochain_differential_val, cochain_smul_val, cupCoch_val, map_smul, Pi.smul_apply, cupProduct_leibniz, hx']
    simp only [cupFun, Pi.zero_apply, map_zero, LinearMap.zero_apply, zero_add, smul_smul, ← mul_pow,
      mul_neg_one, neg_neg, one_pow, one_smul]
    rfl
end S3
section S4
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
theorem cupProduct_cocycle {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) (x : M.coch.X p)
    (hx : M.coch.d p x = 0) (y : N.coch.X q) (hy : N.coch.d q y = 0) :
    P.coch.d (p + q) (cupCoch b p q x y) = 0 := by
  have hx' : dn M.rho p x.1 = 0 := congrArg Subtype.val hx
  have hy' : dn N.rho q y.1 = 0 := congrArg Subtype.val hy
  refine Subtype.ext (funext fun g => ?_)
  rw [cochain_differential_val, cupCoch_val, cupProduct_leibniz, hx', hy', cochain_zero_val]
  simp [cupFun]
def cupCocyc {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) :
    M.coch.Z p →ₗ[R] N.coch.Z q →ₗ[R] P.coch.Z (p + q) :=
  LinearMap.mk₂ R (fun x y => ⟨cupCoch b p q x.1 y.1,
      LinearMap.mem_ker.2 (cupProduct_cocycle b p q x.1 (LinearMap.mem_ker.1 x.2) y.1 (LinearMap.mem_ker.1 y.2))⟩)
    (fun x x' y => Subtype.ext (by simp))
    (fun r x y => Subtype.ext (by simp))
    (fun x y y' => Subtype.ext (by simp))
    (fun r x y => Subtype.ext (by simp))
def cupCoh {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) : M.H p →ₗ[R] N.H q →ₗ[R] P.H (p + q) :=
  LinearMap.liftQ₂ _ _ ((cupCocyc b p q).compr₂ (Submodule.mkQ _))
    (fun x hx => LinearMap.mem_ker.2 (LinearMap.ext fun y => by
      rw [LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      exact cupProduct_coboundary_left b p q x.1 hx y.1 (LinearMap.mem_ker.1 y.2)))
    (fun y hy => LinearMap.mem_ker.2 (LinearMap.ext fun x => by
      rw [LinearMap.flip_apply, LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      exact cupProduct_coboundary_right b p q x.1 (LinearMap.mem_ker.1 x.2) y.1 hy))
end S4
section S5
end S5
end
end ReciprocityTheory.Coh


