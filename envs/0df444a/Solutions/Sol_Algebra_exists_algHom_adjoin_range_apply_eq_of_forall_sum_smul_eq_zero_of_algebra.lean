-- Prove2me | solution 1 for Algebra.exists_algHom_adjoin_range_apply_eq_of_forall_sum_smul_eq_zero_of_algebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3d2404f6-4732-5869-af9d-b00f847e8fcd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_sum_smul_eq_zero_of_algebra

set_option autoImplicit false

theorem solution
    {K : Type*} [Field K] {F : Type*} [CommRing F] [Algebra K F]
    (L : Type*) [CommRing L] [Algebra K L]
    {ι : Type*} (t : ι → F) (a : ι → L)
    (hone : ∃ i₀, t i₀ = 1 ∧ a i₀ = 1)
    (hmul : ∀ i j, ∃ k, t k = t i * t j ∧ a k = a i * a j)
    (hcons : ∀ (n : ℕ) (idx : Fin n → ι) (c : Fin n → K),
      ∑ l, c l • t (idx l) = 0 → ∑ l, c l • a (idx l) = 0) :
    ∃ χ : ↥(Algebra.adjoin K (Set.range t)) →ₐ[K] L,
      ∀ i, χ ⟨t i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ = a i := by
  classical
  obtain ⟨i₀, ht₀, ha₀⟩ := hone
  set S : Subalgebra K F := Algebra.adjoin K (Set.range t) with hS

  have hclos : ((Submonoid.closure (Set.range t)) : Set F) = Set.range t := by
    let M : Submonoid F :=
      { carrier := Set.range t
        mul_mem' := by
          rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
          obtain ⟨k, hk, -⟩ := hmul i j
          exact ⟨k, hk⟩
        one_mem' := ⟨i₀, ht₀⟩ }
    show ((Submonoid.closure (M : Set F)) : Set F) = (M : Set F)
    rw [Submonoid.closure_eq]
  have hSspan : S.toSubmodule = Submodule.span K (Set.range t) := by
    rw [hS, Algebra.adjoin_eq_span, hclos]

  let Lt : (ι →₀ K) →ₗ[K] F := Finsupp.linearCombination K t
  let La : (ι →₀ K) →ₗ[K] L := Finsupp.linearCombination K a
  have hLt : ∀ l : ι →₀ K, Lt l = ∑ i ∈ l.support, l i • t i := fun l => by
    simp only [Lt, Finsupp.linearCombination_apply, Finsupp.sum]
  have hLa : ∀ l : ι →₀ K, La l = ∑ i ∈ l.support, l i • a i := fun l => by
    simp only [La, Finsupp.linearCombination_apply, Finsupp.sum]

  have hker : LinearMap.ker Lt ≤ LinearMap.ker La := by
    intro l hl
    rw [LinearMap.mem_ker] at hl ⊢
    rw [hLt] at hl
    rw [hLa]
    let e := l.support.equivFin
    have h1 : ∑ m : Fin l.support.card, l (e.symm m : ι) • t (e.symm m : ι) = ∑ i ∈ l.support, l i • t i := by
      rw [← Finset.sum_coe_sort l.support (fun i => l i • t i)]
      exact Fintype.sum_equiv e.symm (fun m => l (e.symm m : ι) • t (e.symm m : ι)) (fun i => l (i : ι) • t (i : ι)) (fun _ => rfl)
    have h2 : ∑ m : Fin l.support.card, l (e.symm m : ι) • a (e.symm m : ι) = ∑ i ∈ l.support, l i • a i := by
      rw [← Finset.sum_coe_sort l.support (fun i => l i • a i)]
      exact Fintype.sum_equiv e.symm (fun m => l (e.symm m : ι) • a (e.symm m : ι)) (fun i => l (i : ι) • a (i : ι)) (fun _ => rfl)
    rw [← h2]
    exact hcons _ (fun m => (e.symm m : ι)) (fun m => l (e.symm m : ι)) (by rw [h1, hl])
  have hrange : LinearMap.range Lt = S.toSubmodule := by
    rw [hSspan]; exact Finsupp.range_linearCombination K
  have hmemS : ∀ s : ↥S, (s : F) ∈ LinearMap.range Lt := fun s => by rw [hrange]; exact s.2

  let φ₀ : ((ι →₀ K) ⧸ LinearMap.ker Lt) →ₗ[K] L := (LinearMap.ker Lt).liftQ La hker
  let eqv := Lt.quotKerEquivRange
  let φ : ↥S →ₗ[K] L :=
    { toFun := fun s => φ₀ (eqv.symm ⟨(s : F), hmemS s⟩)
      map_add' := fun x y => by
        rw [← map_add φ₀, ← map_add eqv.symm]; rfl
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← map_smul φ₀, ← map_smul eqv.symm]; rfl }
  have hφ : ∀ (s : ↥S) (l : ι →₀ K), (s : F) = Lt l → φ s = La l := by
    intro s l hsl
    show φ₀ (eqv.symm ⟨(s : F), hmemS s⟩) = La l
    have : eqv.symm ⟨(s : F), hmemS s⟩ = Submodule.Quotient.mk l := by
      rw [LinearEquiv.symm_apply_eq]
      apply Subtype.ext
      show (s : F) = (Lt.quotKerEquivRange (Submodule.Quotient.mk l) : F)
      rw [LinearMap.quotKerEquivRange_apply_mk]
      exact hsl
    rw [this]
    exact Submodule.liftQ_apply _ _ l
  let v : ι → ↥S := fun i => ⟨t i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  have hφv : ∀ i, φ (v i) = a i := by
    intro i
    rw [hφ (v i) (Finsupp.single i 1) ?_]
    · simp [La, Finsupp.linearCombination_single]
    · simp [Lt, v, Finsupp.linearCombination_single]

  have hval : LinearMap.range (S.val.toLinearMap) = S.toSubmodule := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩; exact s.2
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have hv : Submodule.span K (Set.range v) = ⊤ := by
    apply Submodule.map_injective_of_injective (f := S.val.toLinearMap) (fun x y h => Subtype.ext h)
    rw [Submodule.map_span, Submodule.map_top, hval, hSspan, ← Set.range_comp]
    rfl

  have hmul' : ∀ x y : ↥S, φ (x * y) = φ x * φ y := by
    let B₁ : ↥S →ₗ[K] ↥S →ₗ[K] L := (LinearMap.mul K ↥S).compr₂ φ
    let B₂ : ↥S →ₗ[K] ↥S →ₗ[K] L := (LinearMap.mul K L).compl₁₂ φ φ
    have hB : B₁ = B₂ := by
      refine LinearMap.ext_on_range hv (fun i => LinearMap.ext_on_range hv (fun j => ?_))
      obtain ⟨k, hk, hak⟩ := hmul i j
      have hvk : v i * v j = v k := Subtype.ext hk.symm
      show φ (v i * v j) = φ (v i) * φ (v j)
      rw [hvk, hφv, hφv, hφv, hak]
    intro x y
    have := congrArg (fun B : ↥S →ₗ[K] ↥S →ₗ[K] L => B x y) hB
    exact this
  have hone' : φ 1 = 1 := by
    have : (1 : ↥S) = v i₀ := Subtype.ext ht₀.symm
    rw [this, hφv, ha₀]
  exact ⟨AlgHom.ofLinearMap φ hone' hmul', hφv⟩

end S_Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_sum_smul_eq_zero_of_algebra
end P2MW
export P2MW.S_Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_sum_smul_eq_zero_of_algebra (solution)
