-- Prove2me | solution 1 for AlgebraicCurve.pointHt_mul_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4dd93293-80a3-56a3-867e-43b306235145

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_pointHt_mul_eq_add

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 480000
set_option maxHeartbeats 6400000

open AlgebraicCurve

noncomputable section

namespace P2MRowS

section Pivot

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}

theorem exists_forall_ord_le (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) :
    ∃ i : Fin r, ∀ j : Fin r, v.ord (s i) ≤ v.ord (s j) := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => v.ord (s i)) Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

theorem ord_pivot_le (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (j : Fin r) :
    v.ord (s (pivotIndex s v hr)) ≤ v.ord (s j) := by
  classical
  have hex := exists_forall_ord_le hr s v
  have : pivotIndex s v hr = Classical.choose hex := by rw [pivotIndex, dif_pos hex]
  rw [this]
  exact Classical.choose_spec hex j

theorem evalVec_apply (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (i : Fin r) :
    evalVec s v i = v.evalAt (s i * (s (pivotIndex s v hr))⁻¹) := by
  rw [evalVec]
  simp only [dif_pos hr]

theorem evalVec_pivot (hr : 0 < r) (s : Fin r → F) (hs : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) : evalVec s v (pivotIndex s v hr) = 1 := by
  rw [evalVec_apply hr, mul_inv_cancel₀ (hs _), Place.evalAt_one]

theorem evalVec_ne_zero (hr : 0 < r) (s : Fin r → F) (hs : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) : evalVec s v ≠ 0 := by
  intro h
  have := congrFun h (pivotIndex s v hr)
  rw [evalVec_pivot hr s hs v] at this
  exact one_ne_zero this

theorem ratio_pivot_mem (hr : 0 < r) (s : Fin r → F) (hs : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) (i : Fin r) :
    s i * (s (pivotIndex s v hr))⁻¹ ∈ v.toValuationSubring :=
  v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs i) (inv_ne_zero (hs _)))
    (by rw [v.ord_mul (hs i) (inv_ne_zero (hs _)), v.ord_inv]; linarith [ord_pivot_le hr s v i])

end Pivot

section AbsHeight

theorem normLogHeight_eq_of_le (E E' : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : E ≤ E')
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ E'] {ι : Type} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) (hx : ∀ i, x i ∈ E) :
    (Module.finrank ℚ E : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hx i⟩ : E))
      = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h (hx i)⟩ : E')) :=
  (Height.inv_finrank_mul_logHeight_inclusion (K := E) (L := E') h (fun i => (⟨x i, hx i⟩ : E))).symm

theorem absLogHeight_eq_of_mem {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    (E' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E'] (h : ∀ i, x i ∈ E') :
    absLogHeight x = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h i⟩ : E')) := by
  have hle : IntermediateField.adjoin ℚ (Set.range x) ≤ E' :=
    IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  haveI := finiteDimensional_adjoin_range x
  exact normLogHeight_eq_of_le _ E' hle x (fun i => IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩)

theorem absLogHeight_smul {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    {c : AlgebraicClosure ℚ} (hc : c ≠ 0) : absLogHeight (c • x) = absLogHeight x := by
  set E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (insert c (Set.range x)) with hE'
  haveI : FiniteDimensional ℚ E' :=
    IntermediateField.finiteDimensional_adjoin fun y _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y).isIntegral
  have hcE : c ∈ E' := IntermediateField.subset_adjoin ℚ _ (Set.mem_insert c _)
  have hx' : ∀ i, x i ∈ E' := fun i =>
    IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem c ⟨i, rfl⟩)
  have hcx : ∀ i, (c • x) i ∈ E' := fun i => by
    rw [Pi.smul_apply, smul_eq_mul]; exact mul_mem hcE (hx' i)
  rw [absLogHeight_eq_of_mem (c • x) E' hcx, absLogHeight_eq_of_mem x E' hx']
  congr 1
  convert Height.logHeight_smul_eq_logHeight (fun i => (⟨x i, hx' i⟩ : E')) (c := ⟨c, hcE⟩) ?_ using 2
  all_goals first
    | exact fun h0 => hc (by simpa using congrArg Subtype.val h0)
    | (funext i; apply Subtype.ext; simp [Pi.smul_apply, smul_eq_mul])

theorem absLogHeight_mul_eq_add {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (x : ι → AlgebraicClosure ℚ) (y : κ → AlgebraicClosure ℚ) (hx : x ≠ 0) (hy : y ≠ 0)
    (e : μ ≃ ι × κ) :
    absLogHeight (fun m => x (e m).1 * y (e m).2) = absLogHeight x + absLogHeight y := by
  set E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (Set.range x ∪ Set.range y) with hE'
  haveI : FiniteDimensional ℚ E' :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
  have hxE : ∀ i, x i ∈ E' := fun i => IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)
  have hyE : ∀ j, y j ∈ E' := fun j => IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨j, rfl⟩)
  have hpE : ∀ m, x (e m).1 * y (e m).2 ∈ E' := fun m => mul_mem (hxE _) (hyE _)
  rw [absLogHeight_eq_of_mem _ E' hpE, absLogHeight_eq_of_mem x E' hxE, absLogHeight_eq_of_mem y E' hyE,
    ← mul_add]
  congr 1
  have hx' : (fun i => (⟨x i, hxE i⟩ : E')) ≠ 0 := by
    intro h; apply hx; funext i; simpa using congrArg Subtype.val (congrFun h i)
  have hy' : (fun j => (⟨y j, hyE j⟩ : E')) ≠ 0 := by
    intro h; apply hy; funext j; simpa using congrArg Subtype.val (congrFun h j)
  have hfun : (fun m => (⟨x (e m).1 * y (e m).2, hpE m⟩ : E'))
      = (fun q : ι × κ => (⟨x q.1, hxE q.1⟩ : E') * (⟨y q.2, hyE q.2⟩ : E')) ∘ e := by
    funext m
    apply Subtype.ext
    rfl
  rw [hfun, Height.logHeight_comp_equiv e, Height.logHeight_fun_mul_eq hx' hy']

end AbsHeight

section Product

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {a b : ℕ}

theorem main (ha : 0 < a) (hb : 0 < b) (s : Fin a → F) (s' : Fin b → F)
    (hs : ∀ i, s i ≠ 0) (hs' : ∀ j, s' j ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) :
    pointHt (fun k : Fin (a * b) => s (finProdFinEquiv.symm k).1 * s' (finProdFinEquiv.symm k).2) v
      = pointHt s v + pointHt s' v := by
  set e : Fin (a * b) ≃ Fin a × Fin b := finProdFinEquiv.symm with he
  set p : Fin (a * b) → F := fun k => s (e k).1 * s' (e k).2 with hp
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have hpne : ∀ m, p m ≠ 0 := fun m => mul_ne_zero (hs _) (hs' _)

  set k := pivotIndex s v ha with hk
  set k' := pivotIndex s' v hb with hk'
  set K := pivotIndex p v hab with hK
  set i₀ := (e K).1 with hi₀
  set j₀ := (e K).2 with hj₀
  have hpK : p K = s i₀ * s' j₀ := rfl
  have hkk' : p (e.symm (k, k')) = s k * s' k' := by
    simp only [hp, Equiv.apply_symm_apply]

  have h1 : v.ord (p K) ≤ v.ord (s k) + v.ord (s' k') := by
    have := ord_pivot_le hab p v (e.symm (k, k'))
    rwa [hkk', v.ord_mul (hs k) (hs' k')] at this
  have h2 : v.ord (p K) = v.ord (s i₀) + v.ord (s' j₀) := by
    rw [hpK, v.ord_mul (hs _) (hs' _)]
  have h3 : v.ord (s k) ≤ v.ord (s i₀) := ord_pivot_le ha s v i₀
  have h4 : v.ord (s' k') ≤ v.ord (s' j₀) := ord_pivot_le hb s' v j₀
  have hki : v.ord (s k) = v.ord (s i₀) := by linarith
  have hkj : v.ord (s' k') = v.ord (s' j₀) := by linarith

  set u : F := (s k * (s i₀)⁻¹) * (s' k' * (s' j₀)⁻¹) with hu
  have hune : u ≠ 0 :=
    mul_ne_zero (mul_ne_zero (hs _) (inv_ne_zero (hs _))) (mul_ne_zero (hs' _) (inv_ne_zero (hs' _)))
  have hord_u : v.ord u = 0 := by
    rw [hu, v.ord_mul (mul_ne_zero (hs _) (inv_ne_zero (hs _))) (mul_ne_zero (hs' _) (inv_ne_zero (hs' _))),
      v.ord_mul (hs _) (inv_ne_zero (hs _)), v.ord_mul (hs' _) (inv_ne_zero (hs' _)), v.ord_inv, v.ord_inv]
    linarith
  have humem : u ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hune hord_u.ge
  set c : AlgebraicClosure ℚ := v.evalAt u with hc
  have hcne : c ≠ 0 := v.evalAt_ne_zero_of_ord_eq_zero hv hune hord_u

  have hev : evalVec p v = c • fun m => evalVec s v (e m).1 * evalVec s' v (e m).2 := by
    funext m
    rw [Pi.smul_apply, smul_eq_mul, evalVec_apply hab p v m, evalVec_apply ha s v, evalVec_apply hb s' v,
      ← hK, ← hk, ← hk']
    have hfield : p m * (p K)⁻¹ = (s (e m).1 * (s k)⁻¹) * (s' (e m).2 * (s' k')⁻¹) * u := by
      rw [hpK, hu]
      simp only [hp]
      field_simp [hs (e m).1, hs' (e m).2, hs i₀, hs' j₀, hs k, hs' k']
    rw [hfield, v.evalAt_mul_of_mem hv (mul_mem (ratio_pivot_mem ha s hs v _) (ratio_pivot_mem hb s' hs' v _)) humem,
      v.evalAt_mul_of_mem hv (ratio_pivot_mem ha s hs v _) (ratio_pivot_mem hb s' hs' v _), ← hc]
    ring

  show absLogHeight (evalVec p v) = absLogHeight (evalVec s v) + absLogHeight (evalVec s' v)
  rw [hev, absLogHeight_smul _ hcne]
  exact absLogHeight_mul_eq_add (evalVec s v) (evalVec s' v)
    (evalVec_ne_zero ha s hs v) (evalVec_ne_zero hb s' hs' v) e

end Product

end P2MRowS

end

open P2MRowS in
theorem solution {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (s : Fin a → F) (s' : Fin b → F)
    (hs : ∀ i, s i ≠ 0) (hs' : ∀ j, s' j ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) :
    pointHt (fun k : Fin (a * b) => s (finProdFinEquiv.symm k).1 * s' (finProdFinEquiv.symm k).2) v
      = pointHt s v + pointHt s' v :=
  P2MRowS.main ha hb s s' hs hs' v hv

end S_AlgebraicCurve_pointHt_mul_eq_add
end P2MW
export P2MW.S_AlgebraicCurve_pointHt_mul_eq_add (solution)
