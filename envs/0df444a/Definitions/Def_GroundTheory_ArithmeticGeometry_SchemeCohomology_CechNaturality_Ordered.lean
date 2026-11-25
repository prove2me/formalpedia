-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Ordered
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Ordered
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:45.596411+00:00
-- url     : https://prove2.me/theorems/f85f78c1-6ece-4c3c-a9c9-f667108d70ca
-- title:
--   Ordered
-- statement:
--   Definitions and structural lemmas for Ordered, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Ordered.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_rho
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_boundary_homotopy
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_eq_of_supported
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_hmt_mem
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_lin_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_ordIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_rangeIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_rho_mem
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_rho_of_strictMono
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_strictMono_of_fin_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u
variable {X : TopCat.{u}} {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
lemma inter_le_of_range {m n : ℕ} {i : Fin m → ι} {j : Fin n → ι}
    (h : Set.range j ⊆ Set.range i) : inter U i ≤ inter U j := by
  intro x hx
  rw [mem_inter_iff] at hx ⊢
  intro a
  obtain ⟨b, hb⟩ := h ⟨a, rfl⟩
  rw [← hb]
  exact hx b
def leSet {m n : ℕ} (i : Fin (n + 1) → ι) : Set (Fin (m + 1) → ι) := {j | inter U i ≤ inter U j}
variable {U} in
lemma mem_leSet {m n : ℕ} {i : Fin (n + 1) → ι} {j : Fin (m + 1) → ι} :
    j ∈ leSet U i ↔ inter U i ≤ inter U j := Iff.rfl
lemma rangeIn_subset_leSet {m n : ℕ} (i : Fin (n + 1) → ι) :
    rangeIn (n := m) (Set.range i) ⊆ leSet U i :=
  fun _ hj => mem_leSet.2 (inter_le_of_range U (mem_rangeIn.1 hj))
noncomputable def cval {m n : ℕ} (σ : Cochain P U m) (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) :
    P.obj (op (inter U i)) :=
  open Classical in if h : inter U i ≤ inter U j then res P h (σ j) else 0
lemma cval_of_le {m n : ℕ} (σ : Cochain P U m) (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : inter U i ≤ inter U j) : cval P U σ i j = res P h (σ j) := dif_pos h
noncomputable def cev {m n : ℕ} (σ : Cochain P U m) (i : Fin (n + 1) → ι) :
    Chain ι m →+ P.obj (op (inter U i)) :=
  Finsupp.liftAddHom fun j => zmultiplesHom _ (cval P U σ i j)
lemma cev_single {m n : ℕ} (σ : Cochain P U m) (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) (z : ℤ) :
    cev P U σ i (Finsupp.single j z) = z • cval P U σ i j := by
  rw [cev, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]
lemma cev_self {n : ℕ} (σ : Cochain P U n) (i : Fin (n + 1) → ι) :
    cev P U σ i (Finsupp.single i 1) = σ i := by
  rw [cev_single, one_smul, cval_of_le P U σ i i le_rfl, res_refl]
lemma cev_add {m n : ℕ} (σ τ : Cochain P U m) (i : Fin (n + 1) → ι) (c : Chain ι m) :
    cev P U (σ + τ) i c = cev P U σ i c + cev P U τ i c := by
  have : cev P U (σ + τ) i = cev P U σ i + cev P U τ i := by
    refine Finsupp.addHom_ext fun j z => ?_
    rw [AddMonoidHom.add_apply, cev_single, cev_single, cev_single, ← smul_add]
    congr 1
    by_cases h : inter U i ≤ inter U j
    · rw [cval_of_le P U _ i j h, cval_of_le P U _ i j h, cval_of_le P U _ i j h, Pi.add_apply, map_add]
    · simp only [cval, h, dif_neg, not_false_eq_true, add_zero]
  exact congrArg (fun L => L c) this
lemma cev_zero {m n : ℕ} (i : Fin (n + 1) → ι) (c : Chain ι m) : cev P U (0 : Cochain P U m) i c = 0 := by
  have h := cev_add P U (0 : Cochain P U m) 0 i c
  rw [add_zero] at h
  simpa using h
lemma res_cev {m n p : ℕ} (σ : Cochain P U m) {i : Fin (n + 1) → ι} {i' : Fin (p + 1) → ι}
    (h : inter U i ≤ inter U i') {c : Chain ι m} (hc : c ∈ Finsupp.supported ℤ ℤ (leSet U i')) :
    res P h (cev P U σ i' c) = cev P U σ i c := by
  refine eq_of_supported ((res P h).comp (cev P U σ i')) (cev P U σ i) (fun j hj z => ?_) hc
  rw [AddMonoidHom.comp_apply, cev_single, cev_single, map_zsmul,
    cval_of_le P U σ i' j (mem_leSet.1 hj), cval_of_le P U σ i j (h.trans (mem_leSet.1 hj)), res_res]
lemma cev_d {m n : ℕ} (σ : Cochain P U m) (i : Fin (n + 1) → ι) {c : Chain ι (m + 1)}
    (hc : c ∈ Finsupp.supported ℤ ℤ (leSet U i)) :
    cev P U (d P U m σ) i c = cev P U σ i (bd m c) := by
  refine eq_of_supported (cev P U (d P U m σ) i) ((cev P U σ i).comp (bd m)) (fun j hj z => ?_) hc
  rw [AddMonoidHom.comp_apply, cev_single, cval_of_le P U _ i j (mem_leSet.1 hj), d_apply, map_sum,
    Finset.smul_sum, bd_single, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_zsmul, res_res, cev_single]
  rw [cval_of_le P U σ i _ ((mem_leSet.1 hj).trans (inter_le_comp U j k.succAbove)), smul_comm]
lemma lin_bd_single {m n : ℕ} (f : (Fin (m + 1) → ι) → Chain ι n) (i : Fin (m + 2) → ι) :
    lin f (bd m (Finsupp.single i 1)) = ∑ k : Fin (m + 2), ((-1 : ℤ) ^ (k : ℕ)) • f (i ∘ k.succAbove) := by
  rw [bd_single, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, lin_single, one_smul]
noncomputable def hstar [LinearOrder ι] (n : ℕ) : Cochain P U (n + 1) →+ Cochain P U n where
  toFun σ i := cev P U σ i (hmt n i)
  map_zero' := funext fun i => cev_zero P U i _
  map_add' σ τ := funext fun i => cev_add P U σ τ i _
lemma hstar_apply [LinearOrder ι] (n : ℕ) (σ : Cochain P U (n + 1)) (i : Fin (n + 1) → ι) :
    hstar P U n σ i = cev P U σ i (hmt n i) := rfl
abbrev OCochain [LinearOrder ι] (n : ℕ) : Type (max w u) :=
  ∀ i : {i : Fin (n + 1) → ι // StrictMono i}, P.obj (op (inter U i.1))
section Ordered
variable [LinearOrder ι]
noncomputable def od (n : ℕ) : OCochain P U n →+ OCochain P U (n + 1) where
  toFun τ i := ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
    res P (inter_le_comp U i.1 k.succAbove) (τ ⟨i.1 ∘ k.succAbove, i.2.comp (Fin.strictMono_succAbove k)⟩)
  map_zero' := funext fun i => by simp
  map_add' τ τ' := funext fun i => by simp [Finset.sum_add_distrib, smul_add]
lemma od_apply (n : ℕ) (τ : OCochain P U n) (i : {i : Fin (n + 2) → ι // StrictMono i}) :
    od P U n τ i = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      res P (inter_le_comp U i.1 k.succAbove)
        (τ ⟨i.1 ∘ k.succAbove, i.2.comp (Fin.strictMono_succAbove k)⟩) := rfl
def toOrd (n : ℕ) : Cochain P U n →+ OCochain P U n where
  toFun σ i := σ i.1
  map_zero' := rfl
  map_add' _ _ := rfl
lemma toOrd_d (n : ℕ) (σ : Cochain P U n) : od P U n (toOrd P U n σ) = toOrd P U (n + 1) (d P U n σ) := by
  funext i
  rw [od_apply]
  exact (d_apply P U n σ i.1).symm
def oleSet {m n : ℕ} (i : Fin (n + 1) → ι) : Set (Fin (m + 1) → ι) :=
  {j | StrictMono j ∧ inter U i ≤ inter U j}
variable {U} in
lemma mem_oleSet {m n : ℕ} {i : Fin (n + 1) → ι} {j : Fin (m + 1) → ι} :
    j ∈ oleSet U i ↔ StrictMono j ∧ inter U i ≤ inter U j := Iff.rfl
lemma ordIn_subset_oleSet {m n : ℕ} (i : Fin (n + 1) → ι) :
    ordIn (n := m) (Set.range i) ⊆ oleSet U i :=
  fun _ hj => mem_oleSet.2 ⟨(mem_ordIn.1 hj).1, inter_le_of_range U (mem_ordIn.1 hj).2⟩
noncomputable def cvalO {m n : ℕ} (τ : OCochain P U m) (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) :
    P.obj (op (inter U i)) :=
  open Classical in
  if h : StrictMono j ∧ inter U i ≤ inter U j then res P h.2 (τ ⟨j, h.1⟩) else 0
lemma cvalO_of {m n : ℕ} (τ : OCochain P U m) (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (hj : StrictMono j) (h : inter U i ≤ inter U j) : cvalO P U τ i j = res P h (τ ⟨j, hj⟩) :=
  dif_pos ⟨hj, h⟩
noncomputable def cevO {m n : ℕ} (τ : OCochain P U m) (i : Fin (n + 1) → ι) :
    Chain ι m →+ P.obj (op (inter U i)) :=
  Finsupp.liftAddHom fun j => zmultiplesHom _ (cvalO P U τ i j)
lemma cevO_single {m n : ℕ} (τ : OCochain P U m) (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (z : ℤ) : cevO P U τ i (Finsupp.single j z) = z • cvalO P U τ i j := by
  rw [cevO, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]
lemma cevO_add {m n : ℕ} (τ τ' : OCochain P U m) (i : Fin (n + 1) → ι) (c : Chain ι m) :
    cevO P U (τ + τ') i c = cevO P U τ i c + cevO P U τ' i c := by
  have : cevO P U (τ + τ') i = cevO P U τ i + cevO P U τ' i := by
    refine Finsupp.addHom_ext fun j z => ?_
    rw [AddMonoidHom.add_apply, cevO_single, cevO_single, cevO_single, ← smul_add]
    congr 1
    by_cases h : StrictMono j ∧ inter U i ≤ inter U j
    · rw [cvalO_of P U _ i j h.1 h.2, cvalO_of P U _ i j h.1 h.2, cvalO_of P U _ i j h.1 h.2,
        Pi.add_apply, map_add]
    · simp only [cvalO, h, dif_neg, not_false_eq_true, add_zero]
  exact congrArg (fun L => L c) this
lemma cevO_zero {m n : ℕ} (i : Fin (n + 1) → ι) (c : Chain ι m) :
    cevO P U (0 : OCochain P U m) i c = 0 := by
  have h := cevO_add P U (0 : OCochain P U m) 0 i c
  rw [add_zero] at h
  simpa using h
lemma res_cevO {m n p : ℕ} (τ : OCochain P U m) {i : Fin (n + 1) → ι} {i' : Fin (p + 1) → ι}
    (h : inter U i ≤ inter U i') {c : Chain ι m} (hc : c ∈ Finsupp.supported ℤ ℤ (oleSet U i')) :
    res P h (cevO P U τ i' c) = cevO P U τ i c := by
  refine eq_of_supported ((res P h).comp (cevO P U τ i')) (cevO P U τ i) (fun j hj z => ?_) hc
  obtain ⟨hjm, hjle⟩ := mem_oleSet.1 hj
  rw [AddMonoidHom.comp_apply, cevO_single, cevO_single, map_zsmul, cvalO_of P U τ i' j hjm hjle,
    cvalO_of P U τ i j hjm (h.trans hjle), res_res]
lemma cevO_od {m n : ℕ} (τ : OCochain P U m) (i : Fin (n + 1) → ι) {c : Chain ι (m + 1)}
    (hc : c ∈ Finsupp.supported ℤ ℤ (oleSet U i)) :
    cevO P U (od P U m τ) i c = cevO P U τ i (bd m c) := by
  refine eq_of_supported (cevO P U (od P U m τ) i) ((cevO P U τ i).comp (bd m))
    (fun j hj z => ?_) hc
  obtain ⟨hjm, hjle⟩ := mem_oleSet.1 hj
  rw [AddMonoidHom.comp_apply, cevO_single, cvalO_of P U _ i j hjm hjle, od_apply, map_sum,
    Finset.smul_sum, bd_single, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_zsmul, res_res, cevO_single]
  rw [cvalO_of P U τ i _ (hjm.comp (Fin.strictMono_succAbove k))
    (hjle.trans (inter_le_comp U j k.succAbove)), smul_comm]
lemma cevO_toOrd {m n : ℕ} (σ : Cochain P U m) (i : Fin (n + 1) → ι) {c : Chain ι m}
    (hc : c ∈ Finsupp.supported ℤ ℤ (oleSet U i)) :
    cevO P U (toOrd P U m σ) i c = cev P U σ i c := by
  refine eq_of_supported _ _ (fun j hj z => ?_) hc
  obtain ⟨hjm, hjle⟩ := mem_oleSet.1 hj
  rw [cevO_single, cev_single, cvalO_of P U _ i j hjm hjle, cval_of_le P U σ i j hjle]
  rfl
noncomputable def fromOrd (n : ℕ) : OCochain P U n →+ Cochain P U n where
  toFun τ i := cevO P U τ i (rho n i)
  map_zero' := funext fun i => cevO_zero P U i _
  map_add' τ τ' := funext fun i => cevO_add P U τ τ' i _
lemma fromOrd_apply (n : ℕ) (τ : OCochain P U n) (i : Fin (n + 1) → ι) :
    fromOrd P U n τ i = cevO P U τ i (rho n i) := rfl
lemma rho_mem_oleSet (n : ℕ) (i : Fin (n + 1) → ι) :
    rho n i ∈ Finsupp.supported ℤ ℤ (oleSet U i) :=
  Finsupp.supported_mono (ordIn_subset_oleSet U i) (rho_mem n i)
theorem toOrd_fromOrd (n : ℕ) (τ : OCochain P U n) : toOrd P U n (fromOrd P U n τ) = τ := by
  funext i
  change cevO P U τ i.1 (rho n i.1) = τ i
  rw [rho_of_strictMono n i.1 i.2, cevO_single, one_smul, cvalO_of P U τ i.1 i.1 i.2 le_rfl,
    res_refl]
theorem d_fromOrd (n : ℕ) (τ : OCochain P U n) :
    d P U n (fromOrd P U n τ) = fromOrd P U (n + 1) (od P U n τ) := by
  funext i
  rw [d_apply, fromOrd_apply, cevO_od P U τ i (rho_mem_oleSet U (n + 1) i), bd_rho, lin_bd_single,
    map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, fromOrd_apply, res_cevO P U τ (inter_le_comp U i k.succAbove)
    (rho_mem_oleSet U n _)]
lemma fromOrd_toOrd_zero (σ : Cochain P U 0) : fromOrd P U 0 (toOrd P U 0 σ) = σ := by
  funext i
  change cevO P U (toOrd P U 0 σ) i (Finsupp.single i 1) = σ i
  rw [cevO_single, one_smul, cvalO_of P U _ i i (strictMono_of_fin_one i) le_rfl, res_refl]
  rfl
theorem d_hstar_add (n : ℕ) (σ : Cochain P U (n + 1)) :
    d P U n (hstar P U n σ) + hstar P U (n + 1) (d P U (n + 1) σ) =
      σ - fromOrd P U (n + 1) (toOrd P U (n + 1) σ) := by
  funext i
  have hm : hmt (n + 1) i ∈ Finsupp.supported ℤ ℤ (leSet U i) :=
    Finsupp.supported_mono (rangeIn_subset_leSet U i) (hmt_mem (n + 1) i)
  have hsum : d P U n (hstar P U n σ) i = cev P U σ i (lin (hmt n) (bd n (Finsupp.single i 1))) := by
    rw [d_apply, lin_bd_single, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, hstar_apply, res_cev P U σ (inter_le_comp U i k.succAbove)
      (Finsupp.supported_mono (rangeIn_subset_leSet U _) (hmt_mem n _))]
  rw [Pi.add_apply, Pi.sub_apply, hsum, hstar_apply, cev_d P U σ i hm, fromOrd_apply,
    cevO_toOrd P U σ i (rho_mem_oleSet U (n + 1) i), ← map_add,
    add_comm (lin (hmt n) (bd n (Finsupp.single i 1))), boundary_homotopy, map_sub, cev_self]
noncomputable def ococycles (n : ℕ) : AddSubgroup (OCochain P U n) := (od P U n).ker
noncomputable def ocoboundaries : (n : ℕ) → AddSubgroup (OCochain P U n)
  | 0 => ⊥
  | n + 1 => (od P U n).range
abbrev ocechH (n : ℕ) : Type (max w u) :=
  ococycles P U n ⧸ (ocoboundaries P U n).addSubgroupOf (ococycles P U n)
noncomputable def toOrdCocycles (n : ℕ) : cocycles P U n →+ ococycles P U n :=
  AddMonoidHom.codRestrict ((toOrd P U n).comp (cocycles P U n).subtype) (ococycles P U n)
    fun σ => AddMonoidHom.mem_ker.2 (by
      change od P U n (toOrd P U n σ.1) = 0
      rw [toOrd_d, (mem_cocycles σ.1).1 σ.2, map_zero])
noncomputable def fromOrdCocycles (n : ℕ) : ococycles P U n →+ cocycles P U n :=
  AddMonoidHom.codRestrict ((fromOrd P U n).comp (ococycles P U n).subtype) (cocycles P U n)
    fun τ => (mem_cocycles _).2 (by
      change d P U n (fromOrd P U n τ.1) = 0
      rw [d_fromOrd, AddMonoidHom.mem_ker.1 τ.2, map_zero])
noncomputable def toOrdH (n : ℕ) : cechH P U n →+ ocechH P U n :=
  QuotientAddGroup.map _ _ (toOrdCocycles P U n) (by
    intro σ hσ
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    rw [AddSubgroup.mem_addSubgroupOf] at hσ
    cases n with
    | zero =>
      rw [coboundaries_zero, AddSubgroup.mem_bot] at hσ
      change toOrd P U 0 σ.1 ∈ ocoboundaries P U 0
      rw [hσ, map_zero]
      exact AddSubgroup.zero_mem _
    | succ n =>
      rw [coboundaries_succ] at hσ
      obtain ⟨τ, hτ⟩ := AddMonoidHom.mem_range.1 hσ
      change toOrd P U (n + 1) σ.1 ∈ (od P U n).range
      exact ⟨toOrd P U n τ, by rw [toOrd_d, hτ]⟩)
noncomputable def fromOrdH (n : ℕ) : ocechH P U n →+ cechH P U n :=
  QuotientAddGroup.map _ _ (fromOrdCocycles P U n) (by
    intro τ hτ
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    rw [AddSubgroup.mem_addSubgroupOf] at hτ
    cases n with
    | zero =>
      change τ.1 ∈ (⊥ : AddSubgroup (OCochain P U 0)) at hτ
      rw [AddSubgroup.mem_bot] at hτ
      change fromOrd P U 0 τ.1 ∈ coboundaries P U 0
      rw [hτ, map_zero]
      exact AddSubgroup.zero_mem _
    | succ n =>
      change τ.1 ∈ (od P U n).range at hτ
      obtain ⟨ρ, hρ⟩ := AddMonoidHom.mem_range.1 hτ
      change fromOrd P U (n + 1) τ.1 ∈ coboundaries P U (n + 1)
      rw [coboundaries_succ]
      exact ⟨fromOrd P U n ρ, by rw [d_fromOrd, hρ]⟩)
lemma toOrdH_fromOrdH (n : ℕ) (x : ocechH P U n) : toOrdH P U n (fromOrdH P U n x) = x := by
  induction x using QuotientAddGroup.induction_on with
  | H τ =>
    change (QuotientAddGroup.mk (toOrdCocycles P U n (fromOrdCocycles P U n τ)) : ocechH P U n) =
      QuotientAddGroup.mk τ
    congr 1
    exact Subtype.ext (toOrd_fromOrd P U n τ.1)
lemma fromOrdH_toOrdH (n : ℕ) (x : cechH P U n) : fromOrdH P U n (toOrdH P U n x) = x := by
  induction x using QuotientAddGroup.induction_on with
  | H σ =>
    change (QuotientAddGroup.mk (fromOrdCocycles P U n (toOrdCocycles P U n σ)) : cechH P U n) =
      QuotientAddGroup.mk σ
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    change -fromOrd P U n (toOrd P U n σ.1) + σ.1 ∈ coboundaries P U n
    cases n with
    | zero =>
      rw [fromOrd_toOrd_zero, neg_add_cancel]
      exact AddSubgroup.zero_mem _
    | succ n =>
      have h := d_hstar_add P U n σ.1
      rw [(mem_cocycles σ.1).1 σ.2, map_zero, add_zero] at h
      rw [neg_add_eq_sub, ← h, coboundaries_succ]
      exact AddMonoidHom.mem_range.2 ⟨_, rfl⟩
noncomputable def cechHOrderedEquiv (n : ℕ) : cechH P U n ≃+ ocechH P U n where
  toFun := toOrdH P U n
  invFun := fromOrdH P U n
  left_inv := fromOrdH_toOrdH P U n
  right_inv := toOrdH_fromOrdH P U n
  map_add' := map_add _
end Ordered
end GroundTheory.Arith.SchemeCoh


