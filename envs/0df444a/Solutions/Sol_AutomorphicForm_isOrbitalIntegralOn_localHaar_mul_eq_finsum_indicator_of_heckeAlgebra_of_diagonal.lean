-- Prove2me | solution 1 for AutomorphicForm.isOrbitalIntegralOn_localHaar_mul_eq_finsum_indicator_of_heckeAlgebra_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9ea5c80c-130d-594e-a2c7-2a92c78dc4c0

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Theorems.Thm_AutomorphicForm_IsOrbitalIntegralOn_unique_of_isRegularSemisimple
import Theorems.Thm_LocalGL2_iwasawa_decomposition_diag
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_isOrbitalIntegralOn_localHaar_mul_eq_finsum_indicator_of_heckeAlgebra_of_diagonal

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

section Unipotent

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private noncomputable def unipOf (y : v.adicCompletion K) : GL (Fin 2) (v.adicCompletion K) where
  val := !![1, y; 0, 1]
  inv := !![1, -y; 0, 1]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

private theorem coe_unipOf (y : v.adicCompletion K) :
    (unipOf y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![1, y; 0, 1] := rfl

private theorem coe_unipOf_inv (y : v.adicCompletion K) :
    ((unipOf y)⁻¹ : GL (Fin 2) (v.adicCompletion K)) = (unipOf (-y) : GL (Fin 2) (v.adicCompletion K)) :=
  Units.ext rfl

private theorem unipOf_mul (y z : v.adicCompletion K) : unipOf y * unipOf z = unipOf (y + z) :=
  Units.ext <| by simp [coe_unipOf, add_comm]

private theorem unipOf_zero : (unipOf (0 : v.adicCompletion K)) = 1 :=
  Units.ext <| by simp [coe_unipOf, Matrix.one_fin_two]

private noncomputable def diagOf (a b : (v.adicCompletion K)ˣ) : GL (Fin 2) (v.adicCompletion K) where
  val := !![(a : v.adicCompletion K), 0; 0, (b : v.adicCompletion K)]
  inv := !![((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), 0; 0,
    ((b⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

private theorem coe_diagOf (a b : (v.adicCompletion K)ˣ) :
    (diagOf a b : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(a : v.adicCompletion K), 0; 0, (b : v.adicCompletion K)] := rfl

private theorem coe_diagOf_inv (a b : (v.adicCompletion K)ˣ) :
    (((diagOf a b)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), 0; 0,
        ((b⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)] := rfl

private theorem unipOf_mul_diagOf (a b : (v.adicCompletion K)ˣ) (z w : v.adicCompletion K)
    (hw : (a : v.adicCompletion K) * w = z * b) : unipOf z * diagOf a b = diagOf a b * unipOf w :=
  Units.ext <| by simp [coe_unipOf, coe_diagOf, hw]

private theorem inv_mul_mul_unipOf (α β : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (c : v.adicCompletion K) (hc : (α : v.adicCompletion K) * c = α - β) (w : v.adicCompletion K) :
    (unipOf w)⁻¹ * γ * unipOf w = γ * unipOf (c * w) := by
  have hcw : (α : v.adicCompletion K) * (c * w) = α * w + -(w * β) := by
    rw [← mul_assoc, hc]
    ring
  refine Units.ext ?_
  simp [coe_unipOf_inv, coe_unipOf, hγ, hcw]

private theorem eq_mul_unipOf_of_upper (α β : (v.adicCompletion K)ˣ) (γ g : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (h10 : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)
    (h00 : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = α)
    (h11 : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = β) :
    g = γ * unipOf ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 / (α : v.adicCompletion K)) := by
  refine Units.ext ?_
  rw [Units.val_mul, hγ, coe_unipOf, Matrix.mul_fin_two, mul_div_cancel₀ _ α.ne_zero]
  conv_lhs => rw [Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))]
  rw [h10, h00, h11]
  simp

private theorem mul_unipOf_upper (α β : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)]) (y : v.adicCompletion K) :
    ((γ * unipOf y : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
    ((γ * unipOf y : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = α ∧
    ((γ * unipOf y : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = β := by
  simp [Units.val_mul, hγ, coe_unipOf]

end Unipotent

section IntegralSubgroup

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem mem_integralSubgroup_iff (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) ↔
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
        ∈ v.adicCompletionIntegers K := by
  rw [LocalGL2.mem_integralSubgroup_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => ((y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j).2,
      fun i j => (((y⁻¹ : GL (Fin 2) (v.adicCompletionIntegers K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j).2⟩
  · rintro ⟨h, h'⟩
    let A : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K) := fun i j => ⟨_, h i j⟩
    let B : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K) := fun i j => ⟨_, h' i j⟩
    have hA : A.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
      ext i j
      rfl
    have hB : B.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
        ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
      ext i j
      rfl
    have hinj : Function.Injective fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K) =>
        M.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
      intro M N hMN
      ext i j : 2
      exact congrArg (fun P : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) => P i j) hMN
    have hAB : A * B = 1 := by
      apply hinj
      show (A * B).map _ = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).map _
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    have hBA : B * A = 1 := by
      apply hinj
      show (B * A).map _ = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).map _
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

private theorem coe_integralSubgroup_eq (v : HeightOneSpectrum (𝓞 K)) :
    ((LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
        Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) =
      AutomorphicForm.localIntegralSet K v := by
  ext g
  rw [SetLike.mem_coe, mem_integralSubgroup_iff, AutomorphicForm.mem_localIntegralSet]

private theorem unipOf_mem {y : v.adicCompletion K} (hy : y ∈ v.adicCompletionIntegers K) :
    unipOf y ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
  rw [mem_integralSubgroup_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_unipOf]
    fin_cases i <;> fin_cases j <;> simp [hy]
  · rw [coe_unipOf_inv, coe_unipOf]
    fin_cases i <;> fin_cases j <;> simp [hy]

private theorem mem_of_unipOf_mem {y : v.adicCompletion K}
    (h : unipOf y ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) :
    y ∈ v.adicCompletionIntegers K := by
  rw [mem_integralSubgroup_iff] at h
  simpa [coe_unipOf] using h.1 0 1

private theorem unipOf_mem_iff (y : v.adicCompletion K) :
    unipOf y ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) ↔
      y ∈ v.adicCompletionIntegers K :=
  ⟨mem_of_unipOf_mem, unipOf_mem⟩

private theorem mk_mul_unipOf_eq_iff (g : GL (Fin 2) (v.adicCompletion K)) (y z : v.adicCompletion K) :
    (QuotientGroup.mk (g * unipOf y) : GL (Fin 2) (v.adicCompletion K) ⧸
        LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) =
      QuotientGroup.mk (g * unipOf z) ↔ -y + z ∈ v.adicCompletionIntegers K := by
  rw [QuotientGroup.eq, mul_inv_rev, mul_assoc, inv_mul_cancel_left, coe_unipOf_inv, unipOf_mul, unipOf_mem_iff]

private theorem mk_unipOf_eq_iff (y z : v.adicCompletion K) :
    (QuotientGroup.mk (unipOf y) : GL (Fin 2) (v.adicCompletion K) ⧸
        LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) =
      QuotientGroup.mk (unipOf z) ↔ -y + z ∈ v.adicCompletionIntegers K := by
  simpa using mk_mul_unipOf_eq_iff 1 y z

private theorem coe_diagOf_mul_unipOf (a b : (v.adicCompletion K)ˣ) (z : v.adicCompletion K) :
    ((diagOf a b * unipOf z : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(a : v.adicCompletion K), a * z; 0, (b : v.adicCompletion K)] := by
  rw [Units.val_mul, coe_diagOf, coe_unipOf, Matrix.mul_fin_two]
  simp

private theorem coe_diagOf_mul_unipOf_inv (a b : (v.adicCompletion K)ˣ) (z : v.adicCompletion K) :
    (((diagOf a b * unipOf z)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K),
          -(z * ((b⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K));
        0, ((b⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)] := by
  rw [mul_inv_rev, coe_unipOf_inv, Units.val_mul, coe_unipOf, coe_diagOf_inv, Matrix.mul_fin_two]
  simp

private theorem diagOf_mem_iff (a b : (v.adicCompletion K)ˣ) :
    diagOf a b ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) ↔
      ((a : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧ (b : v.adicCompletion K) ∈ v.adicCompletionIntegers K) ∧
        ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
          ((b⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  rw [mem_integralSubgroup_iff, coe_diagOf, coe_diagOf_inv]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨⟨by simpa using h 0 0, by simpa using h 1 1⟩, by simpa using h' 0 0, by simpa using h' 1 1⟩
  · rintro ⟨⟨ha, hb⟩, ha', hb'⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [ha, hb]
    · rw [Units.val_inv_eq_inv_val] at ha' hb'
      fin_cases i <;> fin_cases j <;> simp [ha', hb']

private theorem diagOf_mul_unipOf_mem_iff (a b : (v.adicCompletion K)ˣ) (z : v.adicCompletion K) :
    diagOf a b * unipOf z ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) ↔
      diagOf a b ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) ∧
        z ∈ v.adicCompletionIntegers K := by
  constructor
  · intro h
    have h' := (mem_integralSubgroup_iff _).1 h
    rw [coe_diagOf_mul_unipOf, coe_diagOf_mul_unipOf_inv] at h'
    have hd : diagOf a b ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
      rw [diagOf_mem_iff]
      exact ⟨⟨by simpa using h'.1 0 0, by simpa using h'.1 1 1⟩, by simpa using h'.2 0 0, by simpa using h'.2 1 1⟩
    refine ⟨hd, mem_of_unipOf_mem ?_⟩
    have hu := mul_mem (inv_mem hd) h
    rwa [inv_mul_cancel_left] at hu
  · rintro ⟨hd, hz⟩
    exact mul_mem hd (unipOf_mem hz)

private theorem diagOf_mul_diagOf (a b a' b' : (v.adicCompletion K)ˣ) :
    diagOf a b * diagOf a' b' = diagOf (a * a') (b * b') :=
  Units.ext <| by simp [coe_diagOf]

end IntegralSubgroup

section Centralizer

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem exists_eq_diagOf_of_mem_centralizer (α β : (v.adicCompletion K)ˣ) (hαβ : (α : v.adicCompletion K) ≠ β)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    {t : GL (Fin 2) (v.adicCompletion K)}
    (ht : t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :
    ∃ a b : (v.adicCompletion K)ˣ, t = diagOf a b := by
  rw [Subgroup.mem_centralizer_singleton_iff] at ht
  have hmat := congrArg Units.val ht
  rw [Units.val_mul, Units.val_mul, hγ, Matrix.eta_fin_two (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)),
    Matrix.mul_fin_two, Matrix.mul_fin_two] at hmat
  have h01 : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 * β =
      α * (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 := by
    simpa using congrFun (congrFun hmat 0) 1
  have h10 : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 * α =
      β * (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 := by
    simpa using congrFun (congrFun hmat 1) 0
  have hr : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 := by
    by_contra hr
    exact hαβ (mul_right_cancel₀ hr (by rw [← h01, mul_comm])).symm
  have hs : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by
    by_contra hs
    exact hαβ (mul_left_cancel₀ hs (by rw [h10, mul_comm]))
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero t
  rw [Matrix.det_fin_two, hr, zero_mul, sub_zero] at hdet
  refine ⟨Units.mk0 _ (left_ne_zero_of_mul hdet), Units.mk0 _ (right_ne_zero_of_mul hdet), Units.ext ?_⟩
  rw [coe_diagOf, Units.val_mk0, Units.val_mk0]
  conv_lhs => rw [Matrix.eta_fin_two (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))]
  rw [hr, hs]

private theorem diagOf_mem_centralizer (α β : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)]) (a b : (v.adicCompletion K)ˣ) :
    diagOf a b ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Units.ext <| by simp [coe_diagOf, hγ, mul_comm]

private theorem isRegularSemisimple_of_diag (α β : (v.adicCompletion K)ˣ) (hαβ : (α : v.adicCompletion K) ≠ β)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)]) :
    AutomorphicForm.IsRegularSemisimple γ := by
  rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero, hγ, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  have h : ((α : v.adicCompletion K) + β) ^ 2 - 4 * ((α : v.adicCompletion K) * β - 0 * 0) =
      ((α : v.adicCompletion K) - β) ^ 2 := by ring
  rw [h]
  exact pow_ne_zero 2 (sub_ne_zero.2 hαβ)

end Centralizer

section Spherical

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem hecke_apply_eq_of_mk_eq
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    {g h : GL (Fin 2) (v.adicCompletion K)}
    (hgh : (QuotientGroup.mk g : GL (Fin 2) (v.adicCompletion K) ⧸
        LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) = QuotientGroup.mk h) :
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) g = (f : GL (Fin 2) (v.adicCompletion K) → ℂ) h := by
  rw [QuotientGroup.eq] at hgh
  rw [← HeckePair.apply_mul_right f hgh g, mul_inv_cancel_left]

private theorem hecke_apply_out
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (g : GL (Fin 2) (v.adicCompletion K)) :
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out (QuotientGroup.mk g : GL (Fin 2) (v.adicCompletion K) ⧸
      LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))) =
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) g :=
  hecke_apply_eq_of_mk_eq f (QuotientGroup.out_eq' _)

private theorem hecke_isLocallyConstant
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
    IsLocallyConstant (f : GL (Fin 2) (v.adicCompletion K) → ℂ) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' AutomorphicForm.localIntegralSet K v, ?_, ?_, fun y hy => ?_⟩
  · exact (AutomorphicForm.isOpen_localIntegralSet K v).preimage (continuous_const.mul continuous_id)
  · show x⁻¹ * x ∈ AutomorphicForm.localIntegralSet K v
    rw [inv_mul_cancel]
    exact AutomorphicForm.one_mem_localIntegralSet K v
  · have hu : x⁻¹ * y ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
      rw [← SetLike.mem_coe, coe_integralSubgroup_eq]
      exact hy
    rw [← HeckePair.apply_mul_right f hu x, mul_inv_cancel_left]

private theorem hecke_measurable
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
    Measurable[AutomorphicForm.glBorelOf (v.adicCompletion K)] (f : GL (Fin 2) (v.adicCompletion K) → ℂ) := by
  letI := AutomorphicForm.glBorelOf (v.adicCompletion K)
  haveI := AutomorphicForm.borelSpace_glBorelOf (v.adicCompletion K)
  exact (hecke_isLocallyConstant f).continuous.measurable

private theorem hecke_bounded
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
    ∃ C : ℝ, ∀ g : GL (Fin 2) (v.adicCompletion K), ‖(f : GL (Fin 2) (v.adicCompletion K) → ℂ) g‖ ≤ C := by
  refine ⟨∑ c ∈ (HeckePair.finite_cosets f).toFinset, ‖(f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)‖,
    fun g => ?_⟩
  by_cases hg : (f : GL (Fin 2) (v.adicCompletion K) → ℂ) g = 0
  · rw [hg, norm_zero]
    exact Finset.sum_nonneg fun c _ => norm_nonneg _
  · have hmem : (QuotientGroup.mk g : GL (Fin 2) (v.adicCompletion K) ⧸
        LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ∈
          (HeckePair.finite_cosets f).toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact Set.mem_image_of_mem _ hg
    calc ‖(f : GL (Fin 2) (v.adicCompletion K) → ℂ) g‖
        = ‖(f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out
            (QuotientGroup.mk g : GL (Fin 2) (v.adicCompletion K) ⧸
              LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)))‖ := by
          rw [hecke_apply_out]
      _ ≤ _ := Finset.single_le_sum (f := fun c => ‖(f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)‖)
          (fun c _ => norm_nonneg _) hmem

private theorem hecke_mul_unipOf_add_of_mem
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (γ : GL (Fin 2) (v.adicCompletion K)) (y : v.adicCompletion K) {o : v.adicCompletion K}
    (ho : o ∈ v.adicCompletionIntegers K) :
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (y + o)) =
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf y) := by
  rw [← unipOf_mul, ← mul_assoc, HeckePair.apply_mul_right f (unipOf_mem ho)]

private theorem hecke_mul_unipOf_add_mul_of_mem
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (α β : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (c : v.adicCompletion K) (hc : (α : v.adicCompletion K) * c = α - β) (y : v.adicCompletion K)
    {o : v.adicCompletion K} (ho : o ∈ v.adicCompletionIntegers K) :
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (y + c * o)) =
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf y) := by
  rw [add_comm, ← unipOf_mul, ← mul_assoc, ← inv_mul_mul_unipOf α β γ hγ c hc o, mul_assoc, mul_assoc,
    HeckePair.apply_left_mul f (inv_mem (unipOf_mem ho)), unipOf_mul, add_comm]
  exact hecke_mul_unipOf_add_of_mem f γ y ho

private theorem hecke_conj_eq
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (α β : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (c : v.adicCompletion K) (hc : (α : v.adicCompletion K) * c = α - β) (a b : (v.adicCompletion K)ˣ)
    (w : v.adicCompletion K) {k : GL (Fin 2) (v.adicCompletion K)}
    (hk : k ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) :
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) ((diagOf a b * unipOf w * k)⁻¹ * γ * (diagOf a b * unipOf w * k)) =
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (c * w)) := by
  have hd : diagOf a b * γ = γ * diagOf a b :=
    (Subgroup.mem_centralizer_singleton_iff.1 (diagOf_mem_centralizer α β γ hγ a b))
  have hd' : ∀ x : GL (Fin 2) (v.adicCompletion K), (diagOf a b)⁻¹ * (γ * (diagOf a b * x)) = γ * x := fun x => by
    rw [← mul_assoc γ, ← hd, mul_assoc, inv_mul_cancel_left]
  have hkey : (diagOf a b * unipOf w * k)⁻¹ * γ * (diagOf a b * unipOf w * k) =
      k⁻¹ * ((unipOf w)⁻¹ * γ * unipOf w) * k := by
    simp only [mul_inv_rev, mul_assoc, hd']
  rw [hkey, inv_mul_mul_unipOf α β γ hγ c hc w, HeckePair.apply_mul_right f hk,
    HeckePair.apply_left_mul f (inv_mem hk)]

end Spherical

section Classes

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private noncomputable abbrev intAdd (v : HeightOneSpectrum (𝓞 K)) : AddSubgroup (v.adicCompletion K) :=
  (v.adicCompletionIntegers K).toSubring.toAddSubgroup

private theorem mem_intAdd {x : v.adicCompletion K} : x ∈ intAdd v ↔ x ∈ v.adicCompletionIntegers K := Iff.rfl

private theorem exists_out_mk_eq_add (y : v.adicCompletion K) :
    ∃ o ∈ v.adicCompletionIntegers K,
      Quotient.out (QuotientAddGroup.mk y : v.adicCompletion K ⧸ intAdd v) = y + o := by
  obtain ⟨o, ho⟩ := QuotientAddGroup.mk_out_eq_mul (s := intAdd v) y
  exact ⟨o, o.2, ho⟩

private theorem exists_ne_zero_forall_mul_mem (s : Finset (v.adicCompletion K)) :
    ∃ D ∈ v.adicCompletionIntegers K, D ≠ 0 ∧ ∀ z ∈ s, D * z ∈ v.adicCompletionIntegers K := by
  classical
  let d : v.adicCompletion K → v.adicCompletion K := fun z => if z ∈ v.adicCompletionIntegers K then 1 else z⁻¹
  have hne : ∀ z : v.adicCompletion K, z ∉ v.adicCompletionIntegers K → z ≠ 0 := fun z hz h0 => hz (by
    rw [h0]
    exact zero_mem _)
  have hd_mem : ∀ z, d z ∈ v.adicCompletionIntegers K := fun z => by
    by_cases hz : z ∈ v.adicCompletionIntegers K
    · simp only [d, if_pos hz]
      exact one_mem _
    · simp only [d, if_neg hz]
      exact ((v.adicCompletionIntegers K).mem_or_inv_mem z).resolve_left hz
  have hd_ne : ∀ z, d z ≠ 0 := fun z => by
    by_cases hz : z ∈ v.adicCompletionIntegers K
    · simp only [d, if_pos hz]
      exact one_ne_zero
    · simp only [d, if_neg hz]
      exact inv_ne_zero (hne z hz)
  have hdz : ∀ z, d z * z ∈ v.adicCompletionIntegers K := fun z => by
    by_cases hz : z ∈ v.adicCompletionIntegers K
    · simp only [d, if_pos hz, one_mul]
      exact hz
    · simp only [d, if_neg hz, inv_mul_cancel₀ (hne z hz)]
      exact one_mem _
  refine ⟨∏ z ∈ s, d z, prod_mem fun z _ => hd_mem z, Finset.prod_ne_zero_iff.2 fun z _ => hd_ne z, fun z hz => ?_⟩
  rw [← Finset.mul_prod_erase s d hz, mul_right_comm]
  exact mul_mem (hdz z) (prod_mem fun y _ => hd_mem y)

private noncomputable def scaleClass {c' : v.adicCompletion K} (hc' : c' ∈ v.adicCompletionIntegers K) :
    v.adicCompletion K ⧸ intAdd v →+ v.adicCompletion K ⧸ intAdd v where
  toFun q := QuotientAddGroup.mk (c' * Quotient.out q)
  map_zero' := by
    have h0 : Quotient.out (0 : v.adicCompletion K ⧸ intAdd v) ∈ intAdd v :=
      (QuotientAddGroup.eq_zero_iff _).1 (QuotientAddGroup.out_eq' 0)
    exact (QuotientAddGroup.eq_zero_iff _).2 (mem_intAdd.2 (mul_mem hc' (mem_intAdd.1 h0)))
  map_add' q q' := by
    show (QuotientAddGroup.mk (c' * Quotient.out (q + q')) : v.adicCompletion K ⧸ intAdd v) =
      QuotientAddGroup.mk (c' * Quotient.out q) + QuotientAddGroup.mk (c' * Quotient.out q')
    have h : -Quotient.out (q + q') + (Quotient.out q + Quotient.out q') ∈ intAdd v := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq',
        QuotientAddGroup.out_eq']
    have h' : -(c' * Quotient.out (q + q')) + (c' * Quotient.out q + c' * Quotient.out q') =
        c' * (-Quotient.out (q + q') + (Quotient.out q + Quotient.out q')) := by ring
    rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq, h']
    exact mem_intAdd.2 (mul_mem hc' (mem_intAdd.1 h))

private theorem scaleClass_apply {c' : v.adicCompletion K} (hc' : c' ∈ v.adicCompletionIntegers K)
    (q : v.adicCompletion K ⧸ intAdd v) :
    scaleClass hc' q = (QuotientAddGroup.mk (c' * Quotient.out q) : v.adicCompletion K ⧸ intAdd v) :=
  rfl

private theorem scaleClass_mk {c' : v.adicCompletion K} (hc' : c' ∈ v.adicCompletionIntegers K)
    (x : v.adicCompletion K) :
    scaleClass hc' (QuotientAddGroup.mk x) = (QuotientAddGroup.mk (c' * x) : v.adicCompletion K ⧸ intAdd v) := by
  rw [scaleClass_apply]
  obtain ⟨o, ho, hout⟩ := exists_out_mk_eq_add x
  have h' : -(c' * (x + o)) + c' * x = -(c' * o) := by ring
  rw [hout, QuotientAddGroup.eq, h']
  exact neg_mem (mem_intAdd.2 (mul_mem hc' ho))

private theorem scaleClass_surjective {c' : v.adicCompletion K} (hc' : c' ∈ v.adicCompletionIntegers K)
    (hc0 : c' ≠ 0) : Function.Surjective (scaleClass hc') := by
  intro r
  refine ⟨QuotientAddGroup.mk (c'⁻¹ * Quotient.out r), ?_⟩
  rw [scaleClass_mk, mul_inv_cancel_left₀ hc0, QuotientAddGroup.out_eq']

private noncomputable def divClass (c' : v.adicCompletion K) :
    v.adicCompletionIntegers K →+ v.adicCompletion K ⧸ intAdd v where
  toFun o := QuotientAddGroup.mk ((o : v.adicCompletion K) / c')
  map_zero' := by simp
  map_add' o o' := by simp [add_div]

private theorem divClass_apply (c' : v.adicCompletion K) (o : v.adicCompletionIntegers K) :
    divClass (v := v) c' o = (QuotientAddGroup.mk ((o : v.adicCompletion K) / c') : v.adicCompletion K ⧸ intAdd v) :=
  rfl

private theorem range_divClass {c' : v.adicCompletion K} (hc' : c' ∈ v.adicCompletionIntegers K) (hc0 : c' ≠ 0) :
    (divClass (v := v) c').range = (scaleClass hc').ker := by
  ext q
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker, scaleClass_apply, QuotientAddGroup.eq_zero_iff, mem_intAdd]
  constructor
  · rintro ⟨o, rfl⟩
    obtain ⟨t, ht, hout⟩ := exists_out_mk_eq_add ((o : v.adicCompletion K) / c')
    rw [divClass_apply, hout, mul_add, mul_div_cancel₀ _ hc0]
    exact add_mem o.2 (mul_mem hc' ht)
  · intro h
    refine ⟨⟨c' * Quotient.out q, h⟩, ?_⟩
    rw [divClass_apply]
    show (QuotientAddGroup.mk (c' * Quotient.out q / c') : v.adicCompletion K ⧸ intAdd v) = q
    rw [mul_div_cancel_left₀ _ hc0, QuotientAddGroup.out_eq']

private theorem ker_divClass {c' : v.adicCompletion K} (hc' : c' ∈ v.adicCompletionIntegers K) (hc0 : c' ≠ 0) :
    (divClass (v := v) c').ker =
      (Ideal.span {(⟨c', hc'⟩ : v.adicCompletionIntegers K)} : Ideal (v.adicCompletionIntegers K)).toAddSubgroup := by
  ext o
  rw [AddMonoidHom.mem_ker, divClass_apply, QuotientAddGroup.eq_zero_iff, mem_intAdd, Submodule.mem_toAddSubgroup,
    Ideal.mem_span_singleton]
  constructor
  · intro h
    exact Dvd.intro ⟨(o : v.adicCompletion K) / c', h⟩ (Subtype.ext (mul_div_cancel₀ _ hc0))
  · rintro ⟨t, ht⟩
    have ht' : (o : v.adicCompletion K) = c' * (t : v.adicCompletion K) := congrArg Subtype.val ht
    rw [ht', mul_div_cancel_left₀ _ hc0]
    exact t.2

private theorem integers_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Integers (v.adicCompletionIntegers K) :=
  Valuation.valuationSubring.integers (v := Valued.v)

private theorem exp_pow_nat (a : ℤ) : ∀ n : ℕ, WithZero.exp a ^ n = WithZero.exp ((n : ℤ) * a)
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, exp_pow_nat a n, ← WithZero.exp_add]
    congr 1
    push_cast
    ring

private theorem valued_irreducible (v : HeightOneSpectrum (𝓞 K)) {ϖ : v.adicCompletionIntegers K}
    (hϖ : Irreducible ϖ) : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  have hint := integers_adicCompletionIntegers v
  have hϖ0 : Valued.v (ϖ : v.adicCompletion K) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 fun h => hϖ.ne_zero (Subtype.ext h)
  apply le_antisymm
  · have hlt := hint.valuation_irreducible_lt_one hϖ
    simp only [ValuationSubring.algebraMap_apply] at hlt
    rw [← WithZero.exp_log hϖ0] at hlt ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    exact WithZero.exp_le_exp.2 (by omega)
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    have hπv : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
      rw [v.valuedAdicCompletion_eq_valuation' π, hπ]
    have hπmem : (π : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hπv, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.2 (by omega)
    have hmax : (⟨(π : v.adicCompletion K), hπmem⟩ : v.adicCompletionIntegers K) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hint.isUnit_iff_valuation_eq_one,
        ValuationSubring.algebraMap_apply]
      show ¬ Valued.v (π : v.adicCompletion K) = 1
      rw [hπv, ← WithZero.exp_zero, WithZero.exp_inj]
      omega
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmax
    have hle := hint.le_of_dvd hmax
    simp only [ValuationSubring.algebraMap_apply] at hle
    rwa [← hπv]

private theorem span_singleton_eq_maximalIdeal_pow {c' : v.adicCompletion K} (hc' : c' ∈ v.adicCompletionIntegers K)
    (k : ℕ) (hk : Valued.v c' = WithZero.exp (-(k : ℤ))) :
    (Ideal.span {(⟨c', hc'⟩ : v.adicCompletionIntegers K)} : Ideal (v.adicCompletionIntegers K)) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ k := by
  have hint := integers_adicCompletionIntegers v
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hϖk : Valued.v ((ϖ ^ k : v.adicCompletionIntegers K) : v.adicCompletion K) = WithZero.exp (-(k : ℤ)) := by
    rw [SubmonoidClass.coe_pow, map_pow, valued_irreducible v hϖ, exp_pow_nat]
    congr 1
    ring
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  apply le_antisymm
  · rw [Ideal.span_singleton_le_span_singleton]
    refine hint.dvd_iff_le.2 ?_
    show Valued.v c' ≤ Valued.v ((ϖ ^ k : v.adicCompletionIntegers K) : v.adicCompletion K)
    rw [hk, hϖk]
  · rw [Ideal.span_singleton_le_span_singleton]
    refine hint.dvd_iff_le.2 ?_
    show Valued.v ((ϖ ^ k : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ Valued.v c'
    rw [hk, hϖk]

private theorem natCard_residueField (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = Ideal.absNorm v.asIdeal := by
  let g : 𝓞 K →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    (IsLocalRing.residue (v.adicCompletionIntegers K)).comp (algebraMap (𝓞 K) (v.adicCompletionIntegers K))
  let g' : 𝓞 K ⧸ v.asIdeal →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    Ideal.Quotient.lift v.asIdeal g fun a ha => AdelicHaar.residue_algebraMap_eq_zero_of_mem (𝓞 K) K v ha
  have hsurj : Function.Surjective g' := by
    intro x
    obtain ⟨a, ha⟩ := AdelicHaar.residue_algebraMap_surjective (𝓞 K) K v x
    exact ⟨Ideal.Quotient.mk _ a, by rw [Ideal.Quotient.lift_mk]; exact ha⟩
  have hker : v.asIdeal = RingHom.ker g :=
    Ideal.IsMaximal.eq_of_le (inferInstance : v.asIdeal.IsMaximal) (RingHom.ker_ne_top g) fun a ha => by
      rw [RingHom.mem_ker]
      exact AdelicHaar.residue_algebraMap_eq_zero_of_mem (𝓞 K) K v ha
  have hinj : Function.Injective g' :=
    RingHom.lift_injective_of_ker_le_ideal v.asIdeal _ hker.ge
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Equiv.ofBijective g' ⟨hinj, hsurj⟩)).symm

private theorem absNorm_ne_zero (v : HeightOneSpectrum (𝓞 K)) : Ideal.absNorm v.asIdeal ≠ 0 :=
  Ideal.absNorm_ne_zero_of_nonZeroDivisors ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

private theorem natCard_ker_scaleClass {c' : v.adicCompletion K} (hc' : c' ∈ v.adicCompletionIntegers K) (k : ℕ)
    (hk : Valued.v c' = WithZero.exp (-(k : ℤ))) :
    Nat.card (scaleClass hc').ker = Ideal.absNorm v.asIdeal ^ k := by
  have hc0 : c' ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact WithZero.exp_ne_zero hk.symm
  rw [← range_divClass hc' hc0, ← AddSubgroup.index_ker, ker_divClass hc' hc0]
  change Submodule.cardQuot (Ideal.span {(⟨c', hc'⟩ : v.adicCompletionIntegers K)}) = _
  rw [span_singleton_eq_maximalIdeal_pow hc' k hk,
    cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field (v.adicCompletionIntegers K)), Submodule.cardQuot_apply]
  exact congrArg (· ^ k) (natCard_residueField v)

private theorem natCard_preimage_scaleClass {c' : v.adicCompletion K} (hc' : c' ∈ v.adicCompletionIntegers K)
    (hc0 : c' ≠ 0) (r : v.adicCompletion K ⧸ intAdd v) :
    Nat.card (scaleClass hc' ⁻¹' {r}) = Nat.card (scaleClass hc').ker := by
  obtain ⟨q₀, rfl⟩ := scaleClass_surjective hc' hc0 r
  refine Nat.card_congr
    { toFun := fun q => ⟨q.1 - q₀, ?_⟩
      invFun := fun z => ⟨z.1 + q₀, ?_⟩
      left_inv := fun q => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun z => Subtype.ext (add_sub_cancel_right _ _) }
  · have hq : scaleClass hc' q.1 = scaleClass hc' q₀ := q.2
    rw [AddMonoidHom.mem_ker, map_sub, hq, sub_self]
  · show scaleClass hc' (z.1 + q₀) = scaleClass hc' q₀
    rw [map_add, AddMonoidHom.mem_ker.1 z.2, zero_add]

private theorem finite_ker_scaleClass {c' : v.adicCompletion K} (hc' : c' ∈ v.adicCompletionIntegers K) (k : ℕ)
    (hk : Valued.v c' = WithZero.exp (-(k : ℤ))) : Finite (scaleClass hc').ker :=
  Nat.finite_of_card_ne_zero (by
    rw [natCard_ker_scaleClass hc' k hk]
    exact pow_ne_zero k (absNorm_ne_zero v))

private theorem finite_setOf_mul_out_mem {D : v.adicCompletion K} (hDmem : D ∈ v.adicCompletionIntegers K)
    (hD : D ≠ 0) :
    {q : v.adicCompletion K ⧸ intAdd v | D * Quotient.out q ∈ v.adicCompletionIntegers K}.Finite := by
  have hD0 : Valued.v D ≠ 0 := (Valuation.ne_zero_iff _).2 hD
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Valued.v D = WithZero.exp (-(k : ℤ)) := by
    have hle : WithZero.log (Valued.v D) ≤ 0 := by
      have h1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hDmem
      rw [← WithZero.exp_log hD0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
      exact h1
    refine ⟨(-WithZero.log (Valued.v D)).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hD0]
  haveI := finite_ker_scaleClass hDmem k hk
  have hsub : {q : v.adicCompletion K ⧸ intAdd v | D * Quotient.out q ∈ v.adicCompletionIntegers K} =
      ((scaleClass hDmem).ker : Set (v.adicCompletion K ⧸ intAdd v)) := by
    ext q
    rw [Set.mem_setOf_eq, SetLike.mem_coe, AddMonoidHom.mem_ker, scaleClass_apply, QuotientAddGroup.eq_zero_iff,
      mem_intAdd]
  rw [hsub]
  exact Set.toFinite _

private theorem finsum_out_mul_eq_pow_mul (ψ : v.adicCompletion K → ℂ)
    (hψ : ∀ y : v.adicCompletion K, ∀ o ∈ v.adicCompletionIntegers K, ψ (y + o) = ψ y)
    (hfin : (Function.support fun q : v.adicCompletion K ⧸ intAdd v => ψ (Quotient.out q)).Finite)
    {c' : v.adicCompletion K} (hc' : c' ∈ v.adicCompletionIntegers K) (k : ℕ)
    (hk : Valued.v c' = ((Multiplicative.ofAdd (-(k : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ∑ᶠ q : v.adicCompletion K ⧸ intAdd v, ψ (c' * Quotient.out q) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ k * ∑ᶠ q : v.adicCompletion K ⧸ intAdd v, ψ (Quotient.out q) := by
  classical
  have hk' : Valued.v c' = WithZero.exp (-(k : ℤ)) := hk
  have hc0 : c' ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk'
    exact WithZero.exp_ne_zero hk'.symm

  have hbar : ∀ q : v.adicCompletion K ⧸ intAdd v, ψ (c' * Quotient.out q) = ψ (Quotient.out (scaleClass hc' q)) := by
    intro q
    rw [scaleClass_apply]
    obtain ⟨o, ho, hout⟩ := exists_out_mk_eq_add (c' * Quotient.out q)
    rw [hout, hψ _ o ho]
  haveI := finite_ker_scaleClass hc' k hk'
  have hfib : ∀ r : v.adicCompletion K ⧸ intAdd v, (scaleClass hc' ⁻¹' {r}).Finite := fun r =>
    Set.finite_coe_iff.1 (Nat.finite_of_card_ne_zero (by
      rw [natCard_preimage_scaleClass hc' hc0, natCard_ker_scaleClass hc' k hk']
      exact pow_ne_zero k (absNorm_ne_zero v)))
  set S : Finset (v.adicCompletion K ⧸ intAdd v) := hfin.toFinset with hS
  set P : Finset (v.adicCompletion K ⧸ intAdd v) := (hfin.preimage' fun r _ => hfib r).toFinset with hP
  have hmemP : ∀ q, q ∈ P ↔ scaleClass hc' q ∈ S := fun q => by
    rw [hP, Set.Finite.mem_toFinset, Set.mem_preimage, hS, Set.Finite.mem_toFinset]
  have hsuppS : (Function.support fun q : v.adicCompletion K ⧸ intAdd v => ψ (Quotient.out q)) ⊆ ↑S := by
    intro q hq
    rw [Finset.mem_coe, hS, Set.Finite.mem_toFinset]
    exact hq
  have hfibre_card : ∀ r ∈ S, (P.filter fun q => scaleClass hc' q = r).card = Ideal.absNorm v.asIdeal ^ k := by
    intro r hr
    have hset : ((P.filter fun q => scaleClass hc' q = r : Finset _) : Set (v.adicCompletion K ⧸ intAdd v)) =
        scaleClass hc' ⁻¹' {r} := by
      ext q
      simp only [Finset.coe_filter, hmemP, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      rw [h]
      exact hr
    rw [← natCard_ker_scaleClass hc' k hk', ← natCard_preimage_scaleClass hc' hc0 r, ← hset, Finset.coe_sort_coe,
      Nat.card_eq_finsetCard]
  calc ∑ᶠ q : v.adicCompletion K ⧸ intAdd v, ψ (c' * Quotient.out q)
      = ∑ᶠ q : v.adicCompletion K ⧸ intAdd v, ψ (Quotient.out (scaleClass hc' q)) := finsum_congr hbar
    _ = ∑ q ∈ P, ψ (Quotient.out (scaleClass hc' q)) := by
      refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
      rw [Finset.mem_coe, hmemP, hS, Set.Finite.mem_toFinset]
      exact hq
    _ = ∑ r ∈ S, ∑ q ∈ P with scaleClass hc' q = r, ψ (Quotient.out (scaleClass hc' q)) :=
      (Finset.sum_fiberwise_of_maps_to (fun q hq => (hmemP q).1 hq) _).symm
    _ = ∑ r ∈ S, (Ideal.absNorm v.asIdeal : ℂ) ^ k * ψ (Quotient.out r) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.sum_congr rfl (g := fun _ => ψ (Quotient.out r)) fun q hq => by rw [(Finset.mem_filter.1 hq).2],
        Finset.sum_const, hfibre_card r hr, nsmul_eq_mul, Nat.cast_pow]
    _ = (Ideal.absNorm v.asIdeal : ℂ) ^ k * ∑ᶠ q : v.adicCompletion K ⧸ intAdd v, ψ (Quotient.out q) := by
      rw [← Finset.mul_sum, finsum_eq_sum_of_support_subset _ hsuppS]

private theorem finsum_out_mul_eq_zpow_mul (ψ : v.adicCompletion K → ℂ)
    (hψ : ∀ y : v.adicCompletion K, ∀ o ∈ v.adicCompletionIntegers K, ψ (y + o) = ψ y)
    (hfin : (Function.support fun q : v.adicCompletion K ⧸ intAdd v => ψ (Quotient.out q)).Finite)
    (c : v.adicCompletion K)
    (hψc : ∀ y : v.adicCompletion K, ∀ o ∈ v.adicCompletionIntegers K, ψ (y + c * o) = ψ y) (m : ℤ)
    (hm : Valued.v c = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ∑ᶠ q : v.adicCompletion K ⧸ intAdd v, ψ (c * Quotient.out q) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ m * ∑ᶠ q : v.adicCompletion K ⧸ intAdd v, ψ (Quotient.out q) := by
  have hm' : Valued.v c = WithZero.exp (-m) := hm
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hm'
    exact WithZero.exp_ne_zero hm'.symm
  rcases le_or_gt 0 m with hm0 | hm0
  ·
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k := ⟨m.toNat, (Int.toNat_of_nonneg hm0).symm⟩
    have hc : c ∈ v.adicCompletionIntegers K := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hm', ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.2 (by omega)
    rw [zpow_natCast]
    exact finsum_out_mul_eq_pow_mul ψ hψ hfin hc k hm
  ·
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m = -k := ⟨(-m).toNat, by rw [Int.toNat_of_nonneg (by omega), neg_neg]⟩
    subst hk
    have hcinv : Valued.v c⁻¹ = WithZero.exp (-(k : ℤ)) := by
      rw [map_inv₀, hm', ← WithZero.exp_neg]
      congr 1
      ring
    have hc : c⁻¹ ∈ v.adicCompletionIntegers K := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hcinv, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.2 (by omega)

    have hψ' : ∀ y : v.adicCompletion K, ∀ o ∈ v.adicCompletionIntegers K, ψ (c * (y + o)) = ψ (c * y) := by
      intro y o ho
      rw [mul_add, hψc _ o ho]
    have hfin' : (Function.support fun q : v.adicCompletion K ⧸ intAdd v => ψ (c * Quotient.out q)).Finite := by
      refine (hfin.image (scaleClass hc)).subset fun q hq => ?_
      refine ⟨QuotientAddGroup.mk (c * Quotient.out q), ?_, ?_⟩
      · obtain ⟨o, ho, hout⟩ := exists_out_mk_eq_add (c * Quotient.out q)
        show ψ (Quotient.out (QuotientAddGroup.mk (c * Quotient.out q) : v.adicCompletion K ⧸ intAdd v)) ≠ 0
        rw [hout, hψ _ o ho]
        exact hq
      · rw [scaleClass_mk, inv_mul_cancel_left₀ hc0, QuotientAddGroup.out_eq']
    have h := finsum_out_mul_eq_pow_mul (fun y => ψ (c * y)) hψ' hfin' hc k hcinv
    simp only [mul_inv_cancel_left₀ hc0] at h
    have hN : ((Ideal.absNorm v.asIdeal : ℂ) ^ k) ≠ 0 :=
      pow_ne_zero k (Nat.cast_ne_zero.2 (absNorm_ne_zero v))
    rw [zpow_neg, zpow_natCast, h, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

end Classes

section Cosets

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private noncomputable def upperCoset (γ : GL (Fin 2) (v.adicCompletion K)) (q : v.adicCompletion K ⧸ intAdd v) :
    GL (Fin 2) (v.adicCompletion K) ⧸ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  QuotientGroup.mk (γ * unipOf (Quotient.out q))

private theorem upperCoset_mk (γ : GL (Fin 2) (v.adicCompletion K)) (y : v.adicCompletion K) :
    upperCoset γ (QuotientAddGroup.mk y) = QuotientGroup.mk (γ * unipOf y) := by
  obtain ⟨o, ho, hout⟩ := exists_out_mk_eq_add (v := v) y
  rw [upperCoset, hout, mk_mul_unipOf_eq_iff]
  simpa using neg_mem ho

private theorem upperCoset_injective (γ : GL (Fin 2) (v.adicCompletion K)) : Function.Injective (upperCoset γ) := by
  intro q q' h
  rw [upperCoset, upperCoset, mk_mul_unipOf_eq_iff] at h
  rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq]
  exact h

private theorem range_upperCoset (α β : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)]) :
    Set.range (upperCoset γ) =
      {c : GL (Fin 2) (v.adicCompletion K) ⧸
          LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
        ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = (α : v.adicCompletion K) ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = (β : v.adicCompletion K)} := by
  ext c
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨h10, h00, h11⟩ := mul_unipOf_upper α β γ hγ (Quotient.out q)
    exact ⟨γ * unipOf (Quotient.out q), rfl, h10, h00, h11⟩
  · rintro ⟨g, rfl, h10, h00, h11⟩
    refine ⟨QuotientAddGroup.mk ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 / (α : v.adicCompletion K)), ?_⟩
    rw [upperCoset_mk, ← eq_mul_unipOf_of_upper α β γ g hγ h10 h00 h11]

private theorem finsum_indicator_eq
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (α β : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)]) :
    ∑ᶠ c : GL (Fin 2) (v.adicCompletion K) ⧸
        LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
      Set.indicator
        {c : GL (Fin 2) (v.adicCompletion K) ⧸
            LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
          ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = (α : v.adicCompletion K) ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = (β : v.adicCompletion K)}
        (fun c => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)) c =
      ∑ᶠ q : v.adicCompletion K ⧸ intAdd v,
        (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (Quotient.out q)) := by
  rw [← finsum_mem_def, ← range_upperCoset α β γ hγ, finsum_mem_range (upperCoset_injective γ)]
  exact finsum_congr fun q => hecke_apply_out f _

private theorem finite_support_out
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (γ : GL (Fin 2) (v.adicCompletion K)) :
    (Function.support fun q : v.adicCompletion K ⧸ intAdd v =>
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (Quotient.out q))).Finite := by
  refine (HeckePair.finite_cosets f).preimage (upperCoset_injective γ).injOn |>.subset ?_
  intro q hq
  exact Set.mem_image_of_mem _ hq

end Cosets

section Section

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private def sliceSet (v : HeightOneSpectrum (𝓞 K)) (D : v.adicCompletion K) : Set (GL (Fin 2) (v.adicCompletion K)) :=
  {g | ∃ y : v.adicCompletion K, D * y ∈ v.adicCompletionIntegers K ∧
    (unipOf y)⁻¹ * g ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)}

private theorem mem_sliceSet {D : v.adicCompletion K} {g : GL (Fin 2) (v.adicCompletion K)} :
    g ∈ sliceSet v D ↔ ∃ y : v.adicCompletion K, D * y ∈ v.adicCompletionIntegers K ∧
      (unipOf y)⁻¹ * g ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  Iff.rfl

private theorem continuous_unipOf : Continuous (unipOf : v.adicCompletion K → GL (Fin 2) (v.adicCompletion K)) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [Function.comp_def, coe_unipOf] <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    show Continuous fun y : v.adicCompletion K => (!![1, -y; 0, 1] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem isCompact_sliceSet {D : v.adicCompletion K} (hD : D ≠ 0) : IsCompact (sliceSet v D) := by
  have hX : IsCompact {y : v.adicCompletion K | D * y ∈ v.adicCompletionIntegers K} := by
    have himage : {y : v.adicCompletion K | D * y ∈ v.adicCompletionIntegers K} =
        (fun o : v.adicCompletion K => D⁻¹ * o) '' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
      ext y
      constructor
      · intro hy
        exact ⟨D * y, hy, inv_mul_cancel_left₀ hD y⟩
      · rintro ⟨o, ho, rfl⟩
        show D * (D⁻¹ * o) ∈ v.adicCompletionIntegers K
        rw [← mul_assoc, mul_inv_cancel₀ hD, one_mul]
        exact ho
    rw [himage]
    exact (isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)).image
      (continuous_const.mul continuous_id)
  have himg : sliceSet v D =
      (fun p : v.adicCompletion K × GL (Fin 2) (v.adicCompletion K) => unipOf p.1 * p.2) ''
        ({y : v.adicCompletion K | D * y ∈ v.adicCompletionIntegers K} ×ˢ AutomorphicForm.localIntegralSet K v) := by
    ext g
    constructor
    · intro hg
      obtain ⟨y, hy, hg⟩ := mem_sliceSet.1 hg
      refine ⟨(y, (unipOf y)⁻¹ * g), Set.mem_prod.2 ⟨hy, ?_⟩, mul_inv_cancel_left _ _⟩
      rw [← coe_integralSubgroup_eq v]
      exact hg
    · rintro ⟨⟨y, u⟩, hyu, rfl⟩
      obtain ⟨hy, hu⟩ := Set.mem_prod.1 hyu
      refine mem_sliceSet.2 ⟨y, hy, ?_⟩
      show (unipOf y)⁻¹ * (unipOf y * u) ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)
      rw [inv_mul_cancel_left, ← SetLike.mem_coe, coe_integralSubgroup_eq v]
      exact hu
  rw [himg]
  exact (hX.prod (AutomorphicForm.isCompact_localIntegralSet K v)).image
    ((continuous_unipOf.comp continuous_fst).mul continuous_snd)

private theorem mem_sliceSet_iff {D : v.adicCompletion K} (A B : (v.adicCompletion K)ˣ) {w : v.adicCompletion K}
    (hw : D * w ∈ v.adicCompletionIntegers K) {k : GL (Fin 2) (v.adicCompletion K)}
    (hk : k ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) :
    diagOf A B * unipOf w * k ∈ sliceSet v D ↔
      diagOf A B ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
  constructor
  · intro h
    obtain ⟨y, -, hy⟩ := mem_sliceSet.1 h
    rw [← mul_assoc, mul_mem_cancel_right hk, coe_unipOf_inv, ← mul_assoc,
      unipOf_mul_diagOf A B (-y) (-y * B / A) (mul_div_cancel₀ _ A.ne_zero), mul_assoc, unipOf_mul,
      diagOf_mul_unipOf_mem_iff] at hy
    exact hy.1
  · intro hd
    obtain ⟨⟨hA, -⟩, -, hB'⟩ := (diagOf_mem_iff A B).1 hd
    refine mem_sliceSet.2
      ⟨w * ((A : v.adicCompletion K) * ((B⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)), ?_, ?_⟩
    · rw [← mul_assoc]
      exact mul_mem hw (mul_mem hA hB')
    · have hw' : (A : v.adicCompletion K) * (-w) =
          -(w * ((A : v.adicCompletion K) * ((B⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K))) * B := by
        simp only [neg_mul, mul_neg, mul_assoc, Units.inv_mul, mul_one]
        ring
      rw [← mul_assoc, mul_mem_cancel_right hk, coe_unipOf_inv, ← mul_assoc,
        unipOf_mul_diagOf A B _ (-w) hw', mul_assoc, unipOf_mul, neg_add_cancel, unipOf_zero, mul_one]
      exact hd

private theorem isOpen_preimage_val (γ : GL (Fin 2) (v.adicCompletion K)) :
    IsOpen (Subtype.val ⁻¹' (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
      Set (GL (Fin 2) (v.adicCompletion K))) :
        Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))) := by
  rw [coe_integralSubgroup_eq v]
  exact (AutomorphicForm.isOpen_localIntegralSet K v).preimage continuous_subtype_val

private theorem integral_indicator_sliceSet (α β : (v.adicCompletion K)ˣ) (hαβ : (α : v.adicCompletion K) ≠ β)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ) τ)
    (mτ : ℝ) (hmτ_pos : 0 < mτ)
    (hmτ : τ (Subtype.val ⁻¹' (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
      Set (GL (Fin 2) (v.adicCompletion K)))) = ENNReal.ofReal mτ)
    (D : v.adicCompletion K) (a b : (v.adicCompletion K)ˣ) (w : v.adicCompletion K)
    (hw : D * w ∈ v.adicCompletionIntegers K) {k : GL (Fin 2) (v.adicCompletion K)}
    (hk : k ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) :
    ∫ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
        (sliceSet v D).indicator (fun _ => mτ⁻¹)
          ((t : GL (Fin 2) (v.adicCompletion K)) * (diagOf a b * unipOf w * k)) ∂τ
      = 1 := by
  letI := AutomorphicForm.centralizerBorel (v.adicCompletion K) γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) := ⟨rfl⟩
  haveI := hτ

  let d : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) :=
    ⟨diagOf a b, diagOf_mem_centralizer α β γ hγ a b⟩

  have hpt : ∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
      (sliceSet v D).indicator (fun _ => mτ⁻¹) ((t : GL (Fin 2) (v.adicCompletion K)) * (diagOf a b * unipOf w * k)) =
        ((fun s => d * s) ⁻¹' (Subtype.val ⁻¹'
          (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
            Set (GL (Fin 2) (v.adicCompletion K))))).indicator (fun _ => mτ⁻¹) t := by
    intro t
    obtain ⟨a', b', ht⟩ := exists_eq_diagOf_of_mem_centralizer α β hαβ γ hγ t.2
    have hmem : (t : GL (Fin 2) (v.adicCompletion K)) * (diagOf a b * unipOf w * k) ∈ sliceSet v D ↔
        t ∈ (fun s => d * s) ⁻¹' (Subtype.val ⁻¹'
          (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
            Set (GL (Fin 2) (v.adicCompletion K)))) := by
      simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.coe_mul]
      rw [ht, ← mul_assoc, ← mul_assoc, diagOf_mul_diagOf, mem_sliceSet_iff _ _ hw hk]
      show _ ↔ diagOf a b * diagOf a' b' ∈ _
      rw [diagOf_mul_diagOf, mul_comm a, mul_comm b]
    by_cases h : (t : GL (Fin 2) (v.adicCompletion K)) * (diagOf a b * unipOf w * k) ∈ sliceSet v D
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.1 h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h (hmem.2 h')]
  have hS := (isOpen_preimage_val (v := v) γ).measurableSet
  have hmeas : Measurable fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) => d * s :=
    (continuous_const.mul continuous_id).measurable
  simp_rw [hpt]
  rw [integral_indicator_const _ (hS.preimage hmeas), measureReal_def, ← Measure.map_apply hmeas hS,
    map_mul_left_eq_self τ d, hmτ, ENNReal.toReal_ofReal hmτ_pos.le, smul_eq_mul,
    mul_inv_cancel₀ hmτ_pos.ne']

private def unipCoset (y : v.adicCompletion K) : Set (GL (Fin 2) (v.adicCompletion K)) :=
  (fun x => (unipOf y)⁻¹ * x) ⁻¹' (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
    Set (GL (Fin 2) (v.adicCompletion K)))

private theorem mem_unipCoset {y : v.adicCompletion K} {x : GL (Fin 2) (v.adicCompletion K)} :
    x ∈ unipCoset y ↔
      (unipOf y)⁻¹ * x ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  Iff.rfl

private theorem isOpen_unipCoset (y : v.adicCompletion K) : IsOpen (unipCoset y) := by
  unfold unipCoset
  rw [coe_integralSubgroup_eq v]
  exact (AutomorphicForm.isOpen_localIntegralSet K v).preimage (continuous_const.mul continuous_id)

private theorem localHaar_unipCoset (y : v.adicCompletion K) : AutomorphicForm.localHaar K v (unipCoset y) = 1 := by
  letI := AutomorphicForm.localGLBorel K v
  haveI := AutomorphicForm.borelSpace_localGLBorel K v
  haveI := AutomorphicForm.isHaarMeasure_localHaar K v
  have hU : MeasurableSet (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
      Set (GL (Fin 2) (v.adicCompletion K))) := by
    rw [coe_integralSubgroup_eq v]
    exact (AutomorphicForm.isOpen_localIntegralSet K v).measurableSet
  have hmeas : Measurable fun x : GL (Fin 2) (v.adicCompletion K) => (unipOf y)⁻¹ * x :=
    (continuous_const.mul continuous_id).measurable
  rw [unipCoset, ← Measure.map_apply hmeas hU, map_mul_left_eq_self (AutomorphicForm.localHaar K v),
    coe_integralSubgroup_eq v, AutomorphicForm.localHaar_localIntegralSet]

private theorem integral_mul_indicator_sliceSet
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (α β : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (c : v.adicCompletion K) (hc : (α : v.adicCompletion K) * c = α - β) (mτ : ℝ) {D : v.adicCompletion K}
    (hDmem : D ∈ v.adicCompletionIntegers K) (hD : D ≠ 0)
    (hDc : ∀ w : v.adicCompletion K, (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (c * w)) ≠ 0 →
      D * w ∈ v.adicCompletionIntegers K) :
    ∫ x : GL (Fin 2) (v.adicCompletion K),
        (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (x⁻¹ * γ * x) *
          (((sliceSet v D).indicator (fun _ => mτ⁻¹) x : ℝ) : ℂ)
          ∂(AutomorphicForm.localHaar K v) =
      (mτ⁻¹ : ℂ) * ∑ᶠ q : v.adicCompletion K ⧸ intAdd v,
        (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (c * Quotient.out q)) := by
  letI := AutomorphicForm.localGLBorel K v
  haveI := AutomorphicForm.borelSpace_localGLBorel K v
  set Xfin : Finset (v.adicCompletion K ⧸ intAdd v) := (finite_setOf_mul_out_mem hDmem hD).toFinset with hXfin

  have hF : ∀ x u : GL (Fin 2) (v.adicCompletion K),
      u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) →
        (f : GL (Fin 2) (v.adicCompletion K) → ℂ) ((x * u)⁻¹ * γ * (x * u)) =
          (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (x⁻¹ * γ * x) := by
    intro x u hu
    simp only [mul_inv_rev, mul_assoc]
    rw [HeckePair.apply_left_mul f (inv_mem hu), ← mul_assoc γ x u, ← mul_assoc x⁻¹ (γ * x) u,
      HeckePair.apply_mul_right f hu]
  have hFn : ∀ w : v.adicCompletion K,
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) ((unipOf w)⁻¹ * γ * unipOf w) =
        (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (c * w)) := fun w => by
    rw [inv_mul_mul_unipOf α β γ hγ c hc w]

  have hpt : ∀ x : GL (Fin 2) (v.adicCompletion K),
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (x⁻¹ * γ * x) *
          (((sliceSet v D).indicator (fun _ => mτ⁻¹) x : ℝ) : ℂ) =
        ∑ q ∈ Xfin, (unipCoset (Quotient.out q)).indicator
          (fun _ => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (c * Quotient.out q)) * ((mτ⁻¹ : ℝ) : ℂ))
          x := by
    intro x
    by_cases hx : x ∈ sliceSet v D
    · obtain ⟨y, hy, hyx⟩ := mem_sliceSet.1 hx
      obtain ⟨o, ho, hout⟩ := exists_out_mk_eq_add y
      have hxq : x ∈ unipCoset (Quotient.out (QuotientAddGroup.mk y : v.adicCompletion K ⧸ intAdd v)) := by
        rw [mem_unipCoset, hout, ← unipOf_mul, mul_inv_rev, mul_assoc]
        exact mul_mem (inv_mem (unipOf_mem ho)) hyx
      have hq_mem : (QuotientAddGroup.mk y : v.adicCompletion K ⧸ intAdd v) ∈ Xfin := by
        rw [hXfin, Set.Finite.mem_toFinset]
        show D * Quotient.out (QuotientAddGroup.mk y : v.adicCompletion K ⧸ intAdd v) ∈ v.adicCompletionIntegers K
        rw [hout, mul_add]
        exact add_mem hy (mul_mem hDmem ho)
      have huniq : ∀ q ∈ Xfin, q ≠ (QuotientAddGroup.mk y : v.adicCompletion K ⧸ intAdd v) →
          x ∉ unipCoset (Quotient.out q) := by
        intro q _ hq hxq'
        apply hq
        have h1 := mul_mem (mem_unipCoset.1 hxq') (inv_mem (mem_unipCoset.1 hxq))
        rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at h1
        rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' (QuotientAddGroup.mk y), QuotientAddGroup.eq]
        exact (mk_unipOf_eq_iff _ _).1 (QuotientGroup.eq.2 h1)
      rw [Finset.sum_eq_single (QuotientAddGroup.mk y) (fun q hq hne => Set.indicator_of_notMem (huniq q hq hne) _)
          (fun h => absurd hq_mem h), Set.indicator_of_mem hxq, Set.indicator_of_mem hx]
      congr 1
      rw [← hFn, ← hF (unipOf (Quotient.out (QuotientAddGroup.mk y : v.adicCompletion K ⧸ intAdd v))) _
        (mem_unipCoset.1 hxq), mul_inv_cancel_left]
    · rw [Set.indicator_of_notMem hx, Complex.ofReal_zero, mul_zero]
      symm
      refine Finset.sum_eq_zero fun q hq => Set.indicator_of_notMem (fun hxq => hx ?_) _
      rw [hXfin, Set.Finite.mem_toFinset] at hq
      exact mem_sliceSet.2 ⟨Quotient.out q, hq, mem_unipCoset.1 hxq⟩
  have hint : ∀ q ∈ Xfin, Integrable ((unipCoset (Quotient.out q)).indicator
      (fun _ => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (c * Quotient.out q)) * ((mτ⁻¹ : ℝ) : ℂ)))
        (AutomorphicForm.localHaar K v) := fun q _ => by
    rw [integrable_indicator_iff (isOpen_unipCoset _).measurableSet]
    exact integrableOn_const (by rw [localHaar_unipCoset]; exact ENNReal.one_ne_top)
  have hsupp : (Function.support fun q : v.adicCompletion K ⧸ intAdd v =>
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (c * Quotient.out q))) ⊆ ↑Xfin := by
    intro q hq
    rw [hXfin, Set.Finite.coe_toFinset]
    exact hDc _ hq
  have hterm : ∀ q : v.adicCompletion K ⧸ intAdd v,
      ∫ x : GL (Fin 2) (v.adicCompletion K), (unipCoset (Quotient.out q)).indicator
          (fun _ => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (c * Quotient.out q)) * ((mτ⁻¹ : ℝ) : ℂ))
          x ∂(AutomorphicForm.localHaar K v) =
        (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (c * Quotient.out q)) * ((mτ⁻¹ : ℝ) : ℂ) := by
    intro q
    rw [integral_indicator_const _ (isOpen_unipCoset (Quotient.out q)).measurableSet, measureReal_def,
      localHaar_unipCoset, ENNReal.toReal_one, one_smul]
  simp_rw [hpt]
  rw [integral_finsetSum _ hint, Finset.sum_congr rfl fun q _ => hterm q, ← Finset.sum_mul,
    finsum_eq_sum_of_support_subset _ hsupp, Complex.ofReal_inv]
  ring

private theorem exists_eq_diagOf_mul_unipOf_mul (x : GL (Fin 2) (v.adicCompletion K)) :
    ∃ (a b : (v.adicCompletion K)ˣ) (w : v.adicCompletion K) (k : GL (Fin 2) (v.adicCompletion K)),
      k ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) ∧
        x = diagOf a b * unipOf w * k := by
  obtain ⟨z, a₁, a₂, k, hk, hx⟩ :=
    LocalGL2.iwasawa_decomposition_diag (v.adicCompletionIntegers K) (v.adicCompletion K) x
  refine ⟨a₁, a₂, z * a₂ / a₁, k, hk, ?_⟩
  rw [← unipOf_mul_diagOf a₁ a₂ z _ (mul_div_cancel₀ _ a₁.ne_zero)]
  exact Units.ext hx

end Section

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (α β : (v.adicCompletion K)ˣ) (m : ℤ)
    (hm : Valued.v ((1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K)) =
      ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ) τ)
    (mτ : ℝ)
    (hmτ : τ (Subtype.val ⁻¹' (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
      Set (GL (Fin 2) (v.adicCompletion K)))) = ENNReal.ofReal mτ)
    (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegralOn (v.adicCompletion K) (AutomorphicForm.localHaar K v) γ τ
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) I) :
    (mτ : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-m) * I =
      ∑ᶠ c : GL (Fin 2) (v.adicCompletion K) ⧸
          LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
        Set.indicator
          {c : GL (Fin 2) (v.adicCompletion K) ⧸
              LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
            ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = (α : v.adicCompletion K) ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = (β : v.adicCompletion K)}
          (fun c => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)) c := by

  set c : v.adicCompletion K := 1 - (β : v.adicCompletion K) / (α : v.adicCompletion K) with hc_def
  have hc : (α : v.adicCompletion K) * c = α - β := by
    rw [hc_def, mul_sub, mul_one, mul_div_cancel₀ _ α.ne_zero]
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hm
    exact WithZero.coe_ne_zero hm.symm
  have hαβ : (α : v.adicCompletion K) ≠ β := by
    intro h
    apply hc0
    apply mul_left_cancel₀ α.ne_zero
    rw [hc, mul_zero, h, sub_self]

  have hmτ_pos : 0 < mτ := by
    letI := AutomorphicForm.centralizerBorel (v.adicCompletion K) γ
    haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) := ⟨rfl⟩
    haveI := hτ
    have hopen : IsOpen (Subtype.val ⁻¹' (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
        Set (GL (Fin 2) (v.adicCompletion K))) :
          Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))) := by
      rw [coe_integralSubgroup_eq]
      exact (AutomorphicForm.isOpen_localIntegralSet K v).preimage continuous_subtype_val
    have hpos := hopen.measure_pos τ ⟨1, by simp⟩
    rw [hmτ] at hpos
    exact ENNReal.ofReal_pos.1 hpos

  obtain ⟨D, hDmem, hD0, hDc⟩ : ∃ D ∈ v.adicCompletionIntegers K, D ≠ 0 ∧
      ∀ w : v.adicCompletion K, (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (c * w)) ≠ 0 →
        D * w ∈ v.adicCompletionIntegers K := by
    classical
    obtain ⟨D, hDmem, hD0, hD⟩ := exists_ne_zero_forall_mul_mem
      (insert c⁻¹ ((finite_support_out f γ).toFinset.image fun q => c⁻¹ * Quotient.out q))
    refine ⟨D, hDmem, hD0, fun w hw => ?_⟩
    obtain ⟨o, ho, hout⟩ := exists_out_mk_eq_add (c * w)
    have hq : (QuotientAddGroup.mk (c * w) : v.adicCompletion K ⧸ intAdd v) ∈ (finite_support_out f γ).toFinset := by
      simp only [Set.Finite.mem_toFinset, Function.mem_support]
      rw [hout, hecke_mul_unipOf_add_of_mem f γ _ ho]
      exact hw
    have h1 : D * (c⁻¹ * Quotient.out (QuotientAddGroup.mk (c * w) : v.adicCompletion K ⧸ intAdd v)) ∈
        v.adicCompletionIntegers K :=
      hD _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hq))
    have h2 : D * c⁻¹ ∈ v.adicCompletionIntegers K := hD _ (Finset.mem_insert_self _ _)
    rw [hout, mul_add, ← mul_assoc c⁻¹ c w, inv_mul_cancel₀ hc0, one_mul, mul_add] at h1
    have h3 : D * (c⁻¹ * o) ∈ v.adicCompletionIntegers K := by
      rw [← mul_assoc]
      exact mul_mem h2 ho
    simpa using sub_mem h1 h3

  have hsec : AutomorphicForm.IsOrbitalIntegralOn (v.adicCompletion K) (AutomorphicForm.localHaar K v) γ τ
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ)
      ((mτ⁻¹ : ℂ) * ∑ᶠ q : v.adicCompletion K ⧸ intAdd v,
        (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (c * Quotient.out q))) := by
    simp only [AutomorphicForm.IsOrbitalIntegralOn, AutomorphicForm.IsSectionFnOn]
    refine ⟨fun x => (sliceSet v D).indicator (fun _ => mτ⁻¹) x, ⟨fun x => ?_, ?_, ?_, fun x hx => ?_⟩, ?_⟩
    · exact Set.indicator_nonneg (fun _ _ => (inv_nonneg.2 hmτ_pos.le)) x
    · letI := AutomorphicForm.glBorelOf (v.adicCompletion K)
      haveI := AutomorphicForm.borelSpace_glBorelOf (v.adicCompletion K)
      exact measurable_const.indicator (isCompact_sliceSet hD0).isClosed.measurableSet
    · exact HasCompactSupport.intro (isCompact_sliceSet hD0) fun x hx => Set.indicator_of_notMem hx _
    · obtain ⟨a, b, w, k, hk, rfl⟩ := exists_eq_diagOf_mul_unipOf_mul x
      rw [hecke_conj_eq f α β γ hγ c hc a b w hk] at hx
      exact integral_indicator_sliceSet α β hαβ γ hγ τ hτ mτ hmτ_pos hmτ D a b w (hDc w hx) hk
    · exact (integral_mul_indicator_sliceSet f α β γ hγ c hc mτ hDmem hD0 hDc).symm

  have hIeq : I = (mτ⁻¹ : ℂ) * ∑ᶠ q : v.adicCompletion K ⧸ intAdd v,
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (c * Quotient.out q)) :=
    AutomorphicForm.IsOrbitalIntegralOn.unique_of_isRegularSemisimple (v.adicCompletion K)
      (AutomorphicForm.localHaar K v) (AutomorphicForm.isHaarMeasure_localHaar K v) γ
      (isRegularSemisimple_of_diag α β hαβ γ hγ) τ hτ (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hecke_measurable f)
      (hecke_bounded f) hI hsec

  have hcount : ∑ᶠ q : v.adicCompletion K ⧸ intAdd v,
        (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (c * Quotient.out q)) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ m * ∑ᶠ q : v.adicCompletion K ⧸ intAdd v,
        (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (Quotient.out q)) :=
    finsum_out_mul_eq_zpow_mul (fun y => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf y))
      (fun y o ho => hecke_mul_unipOf_add_of_mem f γ y ho) (finite_support_out f γ) c
      (fun y o ho => hecke_mul_unipOf_add_mul_of_mem f α β γ hγ c hc y ho) m hm
  rw [finsum_indicator_eq f α β γ hγ, hIeq, hcount]
  have hq : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hmτ0 : (mτ : ℂ) ≠ 0 := by exact_mod_cast hmτ_pos.ne'
  rw [zpow_neg]
  field_simp

end S_AutomorphicForm_isOrbitalIntegralOn_localHaar_mul_eq_finsum_indicator_of_heckeAlgebra_of_diagonal
end P2MW
export P2MW.S_AutomorphicForm_isOrbitalIntegralOn_localHaar_mul_eq_finsum_indicator_of_heckeAlgebra_of_diagonal (solution)
