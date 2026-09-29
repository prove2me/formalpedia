-- Prove2me | solution 1 for AutomorphicForm.exists_nhds_forall_exists_pow_eq_of_isRegularSemisimple
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ecf1fda2-2723-5917-8530-85b378c087f7

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_nhds_forall_exists_pow_eq_of_isRegularSemisimple

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped Topology

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "localCentralizer IsRegularSemisimple"
p2m_open "AutomorphicForm"

namespace Roots

section Core

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] [CompleteSpace 𝔸]

open scoped RightActions in

theorem exists_localInverse_pow (n : ℕ) (hn : (n : 𝕜) ≠ 0) :
    ∃ G : 𝔸 → 𝔸, G 1 = 1 ∧ ContinuousAt G 1 ∧ (∀ᶠ y in 𝓝 (1 : 𝔸), G y ^ n = y) ∧
      ∃ S : Set 𝔸, (1 : 𝔸) ∈ S ∧ IsOpen S ∧ Set.InjOn (fun x : 𝔸 => x ^ n) S := by

  obtain ⟨e, he⟩ : ∃ e : 𝔸 ≃L[𝕜] 𝔸, (e : 𝔸 →L[𝕜] 𝔸) = (n : 𝕜) • ContinuousLinearMap.id 𝕜 𝔸 :=
    ⟨ContinuousLinearEquiv.equivOfInverse ((n : 𝕜) • ContinuousLinearMap.id 𝕜 𝔸)
      ((n : 𝕜)⁻¹ • ContinuousLinearMap.id 𝕜 𝔸)
      (fun x => by simp [smul_smul, mul_inv_cancel₀ hn])
      (fun x => by simp [smul_smul, inv_mul_cancel₀ hn]), rfl⟩
  have hp : HasStrictFDerivAt (fun x : 𝔸 => x ^ n) (e : 𝔸 →L[𝕜] 𝔸) 1 := by
    have h := hasStrictFDerivAt_pow' (𝕜 := 𝕜) n (x := (1 : 𝔸))
    have hderiv : (∑ i ∈ Finset.range n, (1 : 𝔸) ^ (n.pred - i) •> ContinuousLinearMap.id 𝕜 𝔸 <• (1 : 𝔸) ^ i) =
        (e : 𝔸 →L[𝕜] 𝔸) := by
      rw [he]
      ext x
      simp [Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
    rw [hderiv] at h
    exact h
  refine ⟨HasStrictFDerivAt.localInverse _ e 1 hp, ?_, ?_, ?_,
    (HasStrictFDerivAt.toOpenPartialHomeomorph _ hp).source, HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hp,
    (HasStrictFDerivAt.toOpenPartialHomeomorph _ hp).open_source, ?_⟩
  · have h := HasStrictFDerivAt.localInverse_apply_image hp
    rwa [one_pow] at h
  · have h := HasStrictFDerivAt.localInverse_continuousAt hp
    rwa [one_pow] at h
  · have h := HasStrictFDerivAt.eventually_right_inverse hp
    rwa [one_pow] at h
  · have h := (HasStrictFDerivAt.toOpenPartialHomeomorph _ hp).injOn
    rwa [HasStrictFDerivAt.toOpenPartialHomeomorph_coe] at h

theorem exists_nhds_forall_commute_exists_pow_eq (n : ℕ) (hn : (n : 𝕜) ≠ 0) (g : 𝔸ˣ) :
    ∀ V' ∈ 𝓝 (1 : 𝔸ˣ), ∃ W ∈ 𝓝 (1 : 𝔸ˣ), ∀ a ∈ W, Commute (a : 𝔸) g →
      ∃ β : 𝔸ˣ, β ∈ V' ∧ Commute (β : 𝔸) g ∧ β ^ n = a := by
  intro V' hV'
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  obtain ⟨G, hG1, hGc, hright, S, hS1, hSo, hinj⟩ := exists_localInverse_pow (𝕜 := 𝕜) (𝔸 := 𝔸) n hn

  have hval : Filter.Tendsto (fun a : 𝔸ˣ => (a : 𝔸)) (𝓝 1) (𝓝 1) := by
    simpa using (Units.continuous_val (M := 𝔸)).tendsto (1 : 𝔸ˣ)
  have hinv : Filter.Tendsto (fun a : 𝔸ˣ => ((a⁻¹ : 𝔸ˣ) : 𝔸)) (𝓝 1) (𝓝 1) := by
    simpa using (Units.continuous_coe_inv (M := 𝔸)).tendsto (1 : 𝔸ˣ)
  have hGa : Filter.Tendsto (fun a : 𝔸ˣ => G (a : 𝔸)) (𝓝 1) (𝓝 1) := by
    have h := hGc.tendsto.comp hval
    rwa [hG1] at h
  have hB : Filter.Tendsto (fun a : 𝔸ˣ => (G (a : 𝔸), MulOpposite.op (G (a : 𝔸) ^ (n - 1) * ((a⁻¹ : 𝔸ˣ) : 𝔸))))
      (𝓝 1) (𝓝 (Units.embedProduct 𝔸 1)) := by
    rw [Units.embedProduct_apply, Units.val_one, inv_one, Units.val_one, MulOpposite.op_one]
    refine hGa.prodMk_nhds ?_
    have h := ((hGa.pow (n - 1)).mul hinv)
    rw [one_pow, one_mul] at h
    have h2 := (MulOpposite.continuous_op (M := 𝔸)).tendsto (1 : 𝔸)
    rw [MulOpposite.op_one] at h2
    exact h2.comp h

  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV'
  obtain ⟨O, hO, hOV⟩ := hV'

  have hW1 : {a : 𝔸ˣ | (G (a : 𝔸), MulOpposite.op (G (a : 𝔸) ^ (n - 1) * ((a⁻¹ : 𝔸ˣ) : 𝔸))) ∈ O} ∈ 𝓝 (1 : 𝔸ˣ) :=
    hB hO
  have hW2 : {a : 𝔸ˣ | G (a : 𝔸) ^ n = (a : 𝔸)} ∈ 𝓝 (1 : 𝔸ˣ) := hval hright
  have hW3 : {a : 𝔸ˣ | G (a : 𝔸) ∈ S} ∈ 𝓝 (1 : 𝔸ˣ) := hGa (hSo.mem_nhds hS1)
  have hW4 : {a : 𝔸ˣ | (g : 𝔸) * G (a : 𝔸) * ((g⁻¹ : 𝔸ˣ) : 𝔸) ∈ S} ∈ 𝓝 (1 : 𝔸ˣ) := by
    have hc : Continuous fun x : 𝔸 => (g : 𝔸) * x * ((g⁻¹ : 𝔸ˣ) : 𝔸) := by fun_prop
    have h1 : (fun x : 𝔸 => (g : 𝔸) * x * ((g⁻¹ : 𝔸ˣ) : 𝔸)) ⁻¹' S ∈ 𝓝 (1 : 𝔸) := by
      refine hc.continuousAt.preimage_mem_nhds ?_
      rw [mul_one, Units.mul_inv]
      exact hSo.mem_nhds hS1
    exact hGa h1
  refine ⟨_, Filter.inter_mem (Filter.inter_mem hW1 hW2) (Filter.inter_mem hW3 hW4), ?_⟩
  rintro a ⟨⟨ha1, ha2⟩, ha3, ha4⟩ hag
  simp only [Set.mem_setOf_eq] at ha1 ha2 ha3 ha4

  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : 𝔸, B₀ = G (a : 𝔸) := ⟨_, rfl⟩
  rw [← hB₀] at ha1 ha2 ha3 ha4
  have hpow : B₀ ^ n = (a : 𝔸) := ha2

  have hconj : (fun x : 𝔸 => x ^ n) ((g : 𝔸) * B₀ * ((g⁻¹ : 𝔸ˣ) : 𝔸)) = (a : 𝔸) := by
    show ((g : 𝔸) * B₀ * ((g⁻¹ : 𝔸ˣ) : 𝔸)) ^ n = (a : 𝔸)
    rw [Units.conj_pow, hpow, ← hag.eq, Units.mul_inv_cancel_right]
  have hcomm : Commute B₀ (g : 𝔸) := by
    have h : B₀ = (g : 𝔸) * B₀ * ((g⁻¹ : 𝔸ˣ) : 𝔸) := hinj ha3 ha4 (hpow.trans hconj.symm)
    have h2 : B₀ * (g : 𝔸) = (g : 𝔸) * B₀ := by
      conv_lhs => rw [h]
      rw [Units.inv_mul_cancel_right]
    exact h2

  have hcomma : Commute B₀ ((a⁻¹ : 𝔸ˣ) : 𝔸) := by
    have h : Commute B₀ (a : 𝔸) := by
      rw [← hpow]
      exact Commute.pow_right (Commute.refl B₀) n
    exact h.units_inv_right
  have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn0)

  let β : 𝔸ˣ := ⟨B₀, B₀ ^ (n - 1) * ((a⁻¹ : 𝔸ˣ) : 𝔸), by
      rw [← mul_assoc, ← pow_succ', hsucc, hpow, Units.mul_inv], by
      rw [mul_assoc, hcomma.symm.eq, ← mul_assoc, ← pow_succ, hsucc, hpow, Units.mul_inv]⟩
  refine ⟨β, ?_, hcomm, ?_⟩
  · apply hOV
    show Units.embedProduct 𝔸 β ∈ O
    exact ha1
  · exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hpow)

end Core

section Commutant

variable {R : Type*} [CommRing R]

theorem exists_eq_smul_one_add_smul_of_commute (g m : Matrix (Fin 2) (Fin 2) R)
    (hg : IsUnit (g.trace ^ 2 - 4 * g.det)) (hm : m * g = g * m) :
    ∃ x y : R, m = x • (1 : Matrix (Fin 2) (Fin 2) R) + y • g := by
  obtain ⟨u, hu⟩ := hg
  have hinv : (↑u⁻¹ : R) * ((g 0 0 + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) = 1 := by
    have h := u.inv_mul
    rwa [hu, Matrix.trace_fin_two, Matrix.det_fin_two] at h
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h10 := congrFun (congrFun hm 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  refine ⟨m 0 0 - (↑u⁻¹ : R) * ((g 0 0 - g 1 1) * (m 0 0 - m 1 1) + 2 * (g 0 1 * m 1 0 + g 1 0 * m 0 1)) * g 0 0,
    (↑u⁻¹ : R) * ((g 0 0 - g 1 1) * (m 0 0 - m 1 1) + 2 * (g 0 1 * m 1 0 + g 1 0 * m 0 1)), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Fin.zero_eta, Fin.mk_one, Fin.isValue, if_true, if_false, mul_one, mul_zero, zero_add, one_ne_zero,
    zero_ne_one]
  · ring
  · linear_combination (-(m 0 1)) * hinv + (-((↑u⁻¹ : R) * (g 0 0 - g 1 1))) * h01 + (2 * (↑u⁻¹ : R) * g 0 1) * h00
  · linear_combination (-(m 1 0)) * hinv + ((↑u⁻¹ : R) * (g 0 0 - g 1 1)) * h10 + (-(2 * (↑u⁻¹ : R) * g 1 0)) * h00
  · linear_combination (m 0 0 - m 1 1) * hinv + (2 * (↑u⁻¹ : R) * g 0 1) * h10 + (-(2 * (↑u⁻¹ : R) * g 1 0)) * h01

end Commutant

section Local

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem exists_norm_ne_one : ∃ x : v.adicCompletion K, x ≠ 0 ∧ ‖x‖ ≠ 1 := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K v
  obtain ⟨d, hvd⟩ : ∃ d : v.adicCompletion K, Valued.v d = WithZero.exp (-1 : ℤ) :=
    ⟨_, (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π).trans hπ⟩
  refine ⟨d, fun h => ?_, ne_of_lt ?_⟩
  · rw [h, map_zero] at hvd
    exact WithZero.exp_ne_zero hvd.symm
  · rw [Valued.toNormedField.norm_lt_one_iff, hvd, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

theorem scalar_mul_comm (c : (v.adicCompletion K)ˣ) (g : GL (Fin 2) (v.adicCompletion K)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (c : v.adicCompletion K) (fun r => Commute.all _ r) _).eq

end Local

end Roots

end AutomorphicForm

end

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_nhds_forall_exists_pow_eq_of_isRegularSemisimple.AutomorphicForm"

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (c : (v.adicCompletion K)ˣ) (n : ℕ) (hn : 0 < n) :
    ∀ V' ∈ nhds (1 : GL (Fin 2) (v.adicCompletion K)),
      ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (v.adicCompletion K)),
        ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ →
          ∃ β : GL (Fin 2) (v.adicCompletion K), β ∈ V' ∧
            (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ∈
              Algebra.adjoin (v.adicCompletion K) {(γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))} ∧
            β ^ n = (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ := by
  intro V' hV'
  haveI : CharZero (v.adicCompletion K) :=
    (RingHom.charZero_iff (algebraMap K (v.adicCompletion K)).injective).1 inferInstance
  letI : NontriviallyNormedField (v.adicCompletion K) :=
    NontriviallyNormedField.ofNormNeOne (Roots.exists_norm_ne_one K v)
  have hnK : (n : v.adicCompletion K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  obtain ⟨W₁, hW₁, hroot⟩ :=
    @Roots.exists_nhds_forall_commute_exists_pow_eq (v.adicCompletion K) _ (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
      _ _ (by exact (inferInstance : CompleteSpace (Fin 2 → Fin 2 → v.adicCompletion K))) n hnK γ₀ V' hV'

  have hzc : Commute (Matrix.GeneralLinearGroup.scalar (Fin 2) c) γ₀ := Roots.scalar_mul_comm K v c γ₀
  have hshift : (fun γ : GL (Fin 2) (v.adicCompletion K) => (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ) ⁻¹' W₁ ∈
      nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (v.adicCompletion K)) := by
    refine (continuous_const_mul (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹).continuousAt.preimage_mem_nhds ?_
    rwa [inv_mul_cancel]
  refine ⟨_, hshift, fun γ hγ hγc => ?_⟩

  have hγc' : Commute γ γ₀ := ((Subgroup.mem_centralizer_iff.1 hγc) γ₀ rfl).symm
  have hcommU : Commute ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ) γ₀ := Commute.mul_left hzc.inv_left hγc'
  have hcomm : Commute (((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    have h := congrArg Units.val hcommU.eq
    rwa [Units.val_mul, Units.val_mul] at h
  obtain ⟨β, hβV, hβc, hβn⟩ := hroot _ hγ hcomm
  refine ⟨β, hβV, ?_, hβn⟩
  obtain ⟨x, y, hxy⟩ := Roots.exists_eq_smul_one_add_smul_of_commute _ _ hγ₀ hβc.eq
  rw [hxy]
  exact add_mem (Subalgebra.smul_mem _ (Subalgebra.one_mem _) x)
    (Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) y)

end S_AutomorphicForm_exists_nhds_forall_exists_pow_eq_of_isRegularSemisimple
end P2MW
export P2MW.S_AutomorphicForm_exists_nhds_forall_exists_pow_eq_of_isRegularSemisimple (solution)
