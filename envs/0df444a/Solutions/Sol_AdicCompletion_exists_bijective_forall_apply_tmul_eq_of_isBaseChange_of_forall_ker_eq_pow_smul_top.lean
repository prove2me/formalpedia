-- Prove2me | solution 1 for AdicCompletion.exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/9fac8d6c-22a0-5884-b57b-f6751f29b514

import Mathlib
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Theorems.Thm_AdicCompletion_isAdicComplete_map_algebraMap_of_fg
import Theorems.Thm_IsAdicComplete_of_module_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top

set_option autoImplicit false

universe u v w

open TensorProduct

namespace W7bAux

section generic

variable {C : Type u} [CommRing C] (J : Ideal C)

theorem mem_pow_smul_top_of_evalₐ_eq_zero (hJ : J.FG) (k : ℕ) (z : AdicCompletion J C)
    (hz : AdicCompletion.evalₐ J k z = 0) : z ∈ (J ^ k • ⊤ : Submodule C (AdicCompletion J C)) := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective J C z
  rw [AdicCompletion.evalₐ_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
  rw [AdicCompletion.pow_smul_top_eq_ker_eval hJ, LinearMap.mem_ker, AdicCompletion.eval_apply,
    AdicCompletion.mk_apply_coe, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.smul_eq_mul, Ideal.mul_top]
  exact hz

theorem sub_of_mem_pow_smul_top (hJ : J.FG) (k : ℕ) (r : AdicCompletion J C) (c : C)
    (hr : AdicCompletion.evalₐ J k r = Ideal.Quotient.mk (J ^ k) c) :
    r - AdicCompletion.of J C c ∈ (J ^ k • ⊤ : Submodule C (AdicCompletion J C)) :=
  mem_pow_smul_top_of_evalₐ_eq_zero J hJ k _ (by rw [map_sub, AdicCompletion.evalₐ_of, hr, sub_self])

theorem sub_of_mem_map_pow (hJ : J.FG) (k : ℕ) (r : AdicCompletion J C) (c : C)
    (hr : AdicCompletion.evalₐ J k r = Ideal.Quotient.mk (J ^ k) c) :
    r - AdicCompletion.of J C c ∈ (J.map (algebraMap C (AdicCompletion J C))) ^ k := by
  have h := sub_of_mem_pow_smul_top J hJ k r c hr
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow] at h
  exact h

theorem of_eq_algebraMap (c : C) : AdicCompletion.of J C c = algebraMap C (AdicCompletion J C) c := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]

theorem of_smul {L : Type v} [AddCommGroup L] [Module C L] [Module (AdicCompletion J C) L]
    [IsScalarTower C (AdicCompletion J C) L] (c : C) (x : L) : AdicCompletion.of J C c • x = c • x := by
  rw [of_eq_algebraMap, algebraMap_smul]

theorem smul_mem_pow_smul_top {L : Type v} [AddCommGroup L] [Module C L] [Module (AdicCompletion J C) L]
    [IsScalarTower C (AdicCompletion J C) L] (k : ℕ) (z : AdicCompletion J C)
    (hz : z ∈ (J ^ k • ⊤ : Submodule C (AdicCompletion J C))) (x : L) :
    z • x ∈ (J ^ k • ⊤ : Submodule C L) := by
  induction hz using Submodule.smul_induction_on' with
  | smul a ha s _ => rw [smul_assoc]; exact Submodule.smul_mem_smul ha Submodule.mem_top
  | add y z _ _ hy hz => rw [add_smul]; exact Submodule.add_mem _ hy hz

theorem apply_smul_eq (hJ : J.FG) {L : Type v} [AddCommGroup L] [Module C L] [Module (AdicCompletion J C) L]
    [IsScalarTower C (AdicCompletion J C) L] {P : Type w} [AddCommGroup P] [Module C P]
    (n : ℕ) (p : L →ₗ[C] P) (hpk : LinearMap.ker p = J ^ (n + 1) • (⊤ : Submodule C L))
    (r : AdicCompletion J C) (c : C) (hr : AdicCompletion.evalₐ J (n + 1) r = Ideal.Quotient.mk (J ^ (n + 1)) c)
    (x : L) : p (r • x) = c • p x := by
  have h2 := smul_mem_pow_smul_top J (n + 1) _ (sub_of_mem_pow_smul_top J hJ (n + 1) r c hr) x
  rw [← hpk, LinearMap.mem_ker, sub_smul, map_sub, sub_eq_zero] at h2
  rw [h2, of_smul, LinearMap.map_smul]

end generic

section flev

variable {B₀ : Type u} [CommRing B₀] {B : Type u} [CommRing B] [Algebra B₀ B] (I₀ : Ideal B₀)

theorem map_of_eq
    (f : AdicCompletion I₀ B₀ →+* AdicCompletion (I₀.map (algebraMap B₀ B)) B)
    (hf : ∀ b : B₀, f (algebraMap B₀ (AdicCompletion I₀ B₀) b)
      = algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B) (algebraMap B₀ B b)) (b : B₀) :
    f (AdicCompletion.of I₀ B₀ b) = AdicCompletion.of _ B (algebraMap B₀ B b) := by
  rw [of_eq_algebraMap, of_eq_algebraMap]; exact hf b

theorem evalₐ_map_eq (hI₀ : I₀.FG)
    (f : AdicCompletion I₀ B₀ →+* AdicCompletion (I₀.map (algebraMap B₀ B)) B)
    (hf : ∀ b : B₀, f (algebraMap B₀ (AdicCompletion I₀ B₀) b)
      = algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B) (algebraMap B₀ B b))
    (k : ℕ) (r : AdicCompletion I₀ B₀) (b : B₀) (hr : AdicCompletion.evalₐ I₀ k r = Ideal.Quotient.mk (I₀ ^ k) b) :
    AdicCompletion.evalₐ (I₀.map (algebraMap B₀ B)) k (f r) =
      Ideal.Quotient.mk ((I₀.map (algebraMap B₀ B)) ^ k) (algebraMap B₀ B b) := by
  have h1 := sub_of_mem_pow_smul_top I₀ hI₀ k r b hr
  have hz : ∀ z ∈ (I₀ ^ k • ⊤ : Submodule B₀ (AdicCompletion I₀ B₀)),
      AdicCompletion.evalₐ (I₀.map (algebraMap B₀ B)) k (f z) = 0 := by
    intro z hz
    induction hz using Submodule.smul_induction_on' with
    | smul a ha s _ =>
      rw [Algebra.smul_def, map_mul, map_mul, ← of_eq_algebraMap, map_of_eq I₀ f hf,
        AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem.2 (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha),
        zero_mul]
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, add_zero]
  have := hz _ h1
  rw [map_sub, map_sub, sub_eq_zero, map_of_eq I₀ f hf, AdicCompletion.evalₐ_of] at this
  exact this

end flev

end W7bAux

open W7bAux

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    {B₀ : Type u} [CommRing B₀] {B : Type u} [CommRing B] [Algebra B₀ B] [IsNoetherianRing B]
    (I₀ : Ideal B₀) (hI₀ : I₀.FG)
    (M₀ : ℕ → Type v) [∀ n, AddCommGroup (M₀ n)] [∀ n, Module B₀ (M₀ n)]
    (t₀ : ∀ n : ℕ, M₀ (n + 1) →ₗ[B₀] M₀ n)
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module B (M n)] [∀ n, Module B₀ (M n)]
    [∀ n, IsScalarTower B₀ B (M n)]
    (t : ∀ n : ℕ, M (n + 1) →ₗ[B] M n)
    (κ : ∀ n : ℕ, M₀ n →ₗ[B₀] M n) (hκ : ∀ n : ℕ, IsBaseChange B (κ n))
    (hκt : ∀ (n : ℕ) (x : M₀ (n + 1)), t n (κ (n + 1) x) = κ n (t₀ n x))

    (L₀ : Type v) [AddCommGroup L₀] [Module B₀ L₀] [Module (AdicCompletion I₀ B₀) L₀]
    [IsScalarTower B₀ (AdicCompletion I₀ B₀) L₀] [Module.Finite (AdicCompletion I₀ B₀) L₀]
    (pr₀ : ∀ n : ℕ, L₀ →ₗ[B₀] M₀ n)
    (hpr₀c : ∀ (n : ℕ) (x : L₀), t₀ n (pr₀ (n + 1) x) = pr₀ n x)
    (hpr₀i : ∀ x : L₀, (∀ n : ℕ, pr₀ n x = 0) → x = 0)
    (hpr₀t : ∀ m : ∀ n : ℕ, M₀ n, (∀ n : ℕ, t₀ n (m (n + 1)) = m n) → ∃ x : L₀, ∀ n : ℕ, pr₀ n x = m n)
    (hpr₀s : ∀ n : ℕ, Function.Surjective (pr₀ n))
    (hpr₀k : ∀ n : ℕ, LinearMap.ker (pr₀ n) = I₀ ^ (n + 1) • (⊤ : Submodule B₀ L₀))

    (L : Type v) [AddCommGroup L] [Module B L] [Module (AdicCompletion (I₀.map (algebraMap B₀ B)) B) L]
    [IsScalarTower B (AdicCompletion (I₀.map (algebraMap B₀ B)) B) L]
    [Module.Finite (AdicCompletion (I₀.map (algebraMap B₀ B)) B) L]
    (pr : ∀ n : ℕ, L →ₗ[B] M n)
    (hprc : ∀ (n : ℕ) (x : L), t n (pr (n + 1) x) = pr n x)
    (hpri : ∀ x : L, (∀ n : ℕ, pr n x = 0) → x = 0)
    (hprt : ∀ m : ∀ n : ℕ, M n, (∀ n : ℕ, t n (m (n + 1)) = m n) → ∃ x : L, ∀ n : ℕ, pr n x = m n)
    (hprs : ∀ n : ℕ, Function.Surjective (pr n))
    (hprk : ∀ n : ℕ, LinearMap.ker (pr n) = (I₀.map (algebraMap B₀ B)) ^ (n + 1) • (⊤ : Submodule B L))

    (f : AdicCompletion I₀ B₀ →+* AdicCompletion (I₀.map (algebraMap B₀ B)) B)
    (hf : ∀ b : B₀, f (algebraMap B₀ (AdicCompletion I₀ B₀) b)
      = algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B) (algebraMap B₀ B b)) :
    letI := f.toAlgebra
    ∃ e : AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀
        →ₗ[AdicCompletion (I₀.map (algebraMap B₀ B)) B] L,
      Function.Bijective e ∧
      ∀ (n : ℕ) (x₀ : L₀), pr n (e ((1 : AdicCompletion (I₀.map (algebraMap B₀ B)) B) ⊗ₜ x₀)) = κ n (pr₀ n x₀) := by
  have hI : (I₀.map (algebraMap B₀ B)).FG := IsNoetherian.noetherian _
  letI algR : Algebra (AdicCompletion I₀ B₀) (AdicCompletion (I₀.map (algebraMap B₀ B)) B) := f.toAlgebra

  letI modL : Module (AdicCompletion I₀ B₀) L := Module.compHom L f
  haveI towL : IsScalarTower (AdicCompletion I₀ B₀) (AdicCompletion (I₀.map (algebraMap B₀ B)) B) L :=
    ⟨fun r₀ r x => by rw [Algebra.smul_def, mul_smul]; rfl⟩

  have huniq : ∀ x y : L, (∀ n, pr n x = pr n y) → x = y := fun x y h =>
    sub_eq_zero.1 (hpri _ (fun n => by rw [map_sub, h n, sub_self]))

  have key : ∀ x₀ : L₀, ∃ x : L, ∀ n, pr n x = κ n (pr₀ n x₀) := fun x₀ =>
    hprt (fun n => κ n (pr₀ n x₀)) (fun n => by rw [hκt, hpr₀c])
  choose lam hlam using key
  have hof : ∀ b₀ : B₀, f (AdicCompletion.of I₀ B₀ b₀) = AdicCompletion.of _ B (algebraMap B₀ B b₀) :=
    map_of_eq I₀ f hf
  let Λ : L₀ →ₗ[AdicCompletion I₀ B₀] L :=
    { toFun := lam
      map_add' := fun x y => huniq _ _ (fun n => by rw [map_add, hlam, hlam, hlam, map_add, map_add])
      map_smul' := fun r₀ x₀ => huniq _ _ (fun n => by
        obtain ⟨b₀, hb₀⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I₀ (n + 1) r₀)
        rw [hlam, apply_smul_eq I₀ hI₀ n (pr₀ n) (hpr₀k n) r₀ b₀ hb₀.symm, map_smul, RingHom.id_apply]
        show _ = pr n (f r₀ • lam x₀)
        rw [apply_smul_eq (I₀.map (algebraMap B₀ B)) hI n (pr n) (hprk n) (f r₀) (algebraMap B₀ B b₀)
          (evalₐ_map_eq I₀ hI₀ f hf (n + 1) r₀ b₀ hb₀.symm), hlam, algebraMap_smul]) }
  have hΛ : ∀ x₀ n, pr n (Λ x₀) = κ n (pr₀ n x₀) := fun x₀ n => hlam x₀ n
  let e : AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀ →ₗ[AdicCompletion (I₀.map (algebraMap B₀ B)) B] L := Λ.liftBaseChange (AdicCompletion (I₀.map (algebraMap B₀ B)) B)
  have hetm : ∀ (r : AdicCompletion (I₀.map (algebraMap B₀ B)) B) (x₀ : L₀), e (r ⊗ₜ x₀) = r • Λ x₀ := fun r x₀ =>
    LinearMap.liftBaseChange_tmul _ _ _ _
  have he1 : ∀ x₀ : L₀, e ((1 : AdicCompletion (I₀.map (algebraMap B₀ B)) B) ⊗ₜ x₀) = Λ x₀ := fun x₀ => by rw [hetm, one_smul]
  haveI : IsAdicComplete ((I₀.map (algebraMap B₀ B)).map (algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B))) (AdicCompletion (I₀.map (algebraMap B₀ B)) B) := AdicCompletion.isAdicComplete_map_algebraMap_of_fg _ hI
  refine ⟨e, ⟨?_, ?_⟩, fun n x₀ => by rw [he1, hΛ]⟩
  ·
    haveI : IsNoetherianRing (AdicCompletion (I₀.map (algebraMap B₀ B)) B) := AdicCompletion.isNoetherianRing_of_isNoetherianRing _
    haveI hcpl : IsAdicComplete ((I₀.map (algebraMap B₀ B)).map (algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B))) (AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀) := IsAdicComplete.of_module_finite _ _

    have hlev : ∀ (n : ℕ) (y : AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀), pr n (e y) = 0 →
        y ∈ (((I₀.map (algebraMap B₀ B)).map (algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B))) ^ (n + 1) • ⊤ : Submodule (AdicCompletion (I₀.map (algebraMap B₀ B)) B) (AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀)) := by
      intro n
      let N : Submodule (AdicCompletion (I₀.map (algebraMap B₀ B)) B) (AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀) := ((I₀.map (algebraMap B₀ B)).map (algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B))) ^ (n + 1) • ⊤
      letI mBQ : Module B ((AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀) ⧸ N) := Module.compHom ((AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀) ⧸ N) (algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B))
      letI mB₀Q : Module B₀ ((AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀) ⧸ N) := Module.compHom ((AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀) ⧸ N) (algebraMap B₀ (AdicCompletion (I₀.map (algebraMap B₀ B)) B))
      letI sBQ : SMul B ((AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀) ⧸ N) := mBQ.toDistribMulAction.toMulAction.toSMul
      letI sB₀Q : SMul B₀ ((AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀) ⧸ N) := mB₀Q.toDistribMulAction.toMulAction.toSMul
      haveI towQ : @IsScalarTower B₀ B ((AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀) ⧸ N) _ sBQ sB₀Q := ⟨fun b₀ b q => by
        show algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B) (b₀ • b) • q =
          algebraMap B₀ (AdicCompletion (I₀.map (algebraMap B₀ B)) B) b₀ • (algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B) b • q)
        rw [Algebra.smul_def, map_mul, mul_smul, IsScalarTower.algebraMap_apply B₀ B (AdicCompletion (I₀.map (algebraMap B₀ B)) B)]⟩

      have hone : ∀ (b₀ : B₀) (x₀ : L₀), (1 : AdicCompletion (I₀.map (algebraMap B₀ B)) B) ⊗ₜ[AdicCompletion I₀ B₀] (b₀ • x₀) =
          algebraMap B₀ (AdicCompletion (I₀.map (algebraMap B₀ B)) B) b₀ • ((1 : AdicCompletion (I₀.map (algebraMap B₀ B)) B) ⊗ₜ[AdicCompletion I₀ B₀] x₀) := fun b₀ x₀ => by
        rw [← of_smul I₀ b₀ x₀, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
          RingHom.algebraMap_toAlgebra, hof, IsScalarTower.algebraMap_apply B₀ B (AdicCompletion (I₀.map (algebraMap B₀ B)) B),
          ← of_eq_algebraMap, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      let g₀ : L₀ →ₗ[B₀] (AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀) ⧸ N :=
        { toFun := fun x₀ => N.mkQ ((1 : AdicCompletion (I₀.map (algebraMap B₀ B)) B) ⊗ₜ x₀)
          map_add' := fun x y => by rw [TensorProduct.tmul_add, map_add]
          map_smul' := fun b₀ x₀ => by
            show N.mkQ ((1 : AdicCompletion (I₀.map (algebraMap B₀ B)) B) ⊗ₜ (b₀ • x₀)) = algebraMap B₀ (AdicCompletion (I₀.map (algebraMap B₀ B)) B) b₀ • N.mkQ ((1 : AdicCompletion (I₀.map (algebraMap B₀ B)) B) ⊗ₜ x₀)
            rw [← map_smul, hone] }
      have hg₀ : ∀ x₀, g₀ x₀ = N.mkQ ((1 : AdicCompletion (I₀.map (algebraMap B₀ B)) B) ⊗ₜ x₀) := fun _ => rfl

      have hker : LinearMap.ker (pr₀ n) ≤ LinearMap.ker g₀ := by
        rw [hpr₀k]
        intro x₀ hx₀
        rw [LinearMap.mem_ker, hg₀, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        induction hx₀ using Submodule.smul_induction_on' with
        | smul a ha y _ =>
          rw [hone]
          refine Submodule.smul_mem_smul ?_ Submodule.mem_top
          rw [IsScalarTower.algebraMap_apply B₀ B (AdicCompletion (I₀.map (algebraMap B₀ B)) B), ← Ideal.map_pow, ← Ideal.map_pow]
          exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
        | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hy hz

      let ν : M₀ n →ₗ[B₀] (AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀) ⧸ N :=
        ((LinearMap.ker (pr₀ n)).liftQ g₀ hker).comp ((pr₀ n).quotKerEquivOfSurjective (hpr₀s n)).symm.toLinearMap
      have hν : ∀ x₀, ν (pr₀ n x₀) = g₀ x₀ := fun x₀ => by
        show ((LinearMap.ker (pr₀ n)).liftQ g₀ hker) (((pr₀ n).quotKerEquivOfSurjective (hpr₀s n)).symm (pr₀ n x₀)) = g₀ x₀
        have : ((pr₀ n).quotKerEquivOfSurjective (hpr₀s n)).symm (pr₀ n x₀) = Submodule.Quotient.mk x₀ :=
          (LinearEquiv.symm_apply_eq _).2 (by rw [LinearMap.quotKerEquivOfSurjective_apply_mk])
        rw [this, Submodule.liftQ_apply]
      let μ : M n →ₗ[B] (AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀) ⧸ N := (hκ n).lift ν
      have hμ : ∀ m₀, μ (κ n m₀) = ν m₀ := (hκ n).lift_eq ν

      have hcmp : ∀ y, μ (pr n (e y)) = N.mkQ y := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp only [LinearMap.map_zero]
        | tmul r x₀ =>
          obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (I₀.map (algebraMap B₀ B)) (n + 1) r)
          rw [hetm, apply_smul_eq (I₀.map (algebraMap B₀ B)) hI n (pr n) (hprk n) r b hb.symm, hΛ, LinearMap.map_smul, hμ, hν, hg₀]
          show AdicCompletion.of (I₀.map (algebraMap B₀ B)) B b • N.mkQ ((1 : AdicCompletion (I₀.map (algebraMap B₀ B)) B) ⊗ₜ x₀) = _
          rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Submodule.mkQ_apply, Submodule.mkQ_apply,
            Submodule.Quotient.eq, ← TensorProduct.sub_tmul, ← mul_one (AdicCompletion.of (I₀.map (algebraMap B₀ B)) B b - r), ← smul_eq_mul,
            ← TensorProduct.smul_tmul']
          refine Submodule.smul_mem_smul ?_ Submodule.mem_top
          rw [← neg_mem_iff, neg_sub]
          exact sub_of_mem_map_pow (I₀.map (algebraMap B₀ B)) hI (n + 1) r b hb.symm
        | add y z hy hz => simp only [map_add, hy, hz]
      intro y hy
      have := hcmp y
      rw [hy, LinearMap.map_zero, eq_comm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
    intro y z hyz
    rw [← sub_eq_zero]
    apply IsHausdorff.haus hcpl.toIsHausdorff (y - z)
    intro n
    rw [SModEq.sub_mem, sub_zero]
    cases n with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact Submodule.mem_top
    | succ n => exact hlev n (y - z) (by rw [map_sub, map_sub, hyz, sub_self])
  ·
    rw [← LinearMap.range_eq_top]
    have h0 : ∀ m : M 0, ∃ y ∈ LinearMap.range e, pr 0 y = m := by
      intro m
      induction m using (hκ 0).inductionOn with
      | zero => exact ⟨0, Submodule.zero_mem _, LinearMap.map_zero _⟩
      | tmul m₀ =>
        obtain ⟨x₀, rfl⟩ := hpr₀s 0 m₀
        exact ⟨e ((1 : AdicCompletion (I₀.map (algebraMap B₀ B)) B) ⊗ₜ x₀), ⟨_, rfl⟩, by rw [he1, hΛ]⟩
      | smul b m hm =>
        obtain ⟨y, hy, rfl⟩ := hm
        refine ⟨AdicCompletion.of (I₀.map (algebraMap B₀ B)) B b • y, Submodule.smul_mem _ _ hy, ?_⟩
        rw [of_smul, LinearMap.map_smul]
      | add m₁ m₂ h₁ h₂ =>
        obtain ⟨y₁, hy₁, rfl⟩ := h₁
        obtain ⟨y₂, hy₂, rfl⟩ := h₂
        exact ⟨y₁ + y₂, Submodule.add_mem _ hy₁ hy₂, map_add _ _ _⟩
    have htop : (⊤ : Submodule (AdicCompletion (I₀.map (algebraMap B₀ B)) B) L) ≤ LinearMap.range e ⊔ ((I₀.map (algebraMap B₀ B)).map (algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B))) • ⊤ := by
      intro x _
      obtain ⟨y, hy, hyx⟩ := h0 (pr 0 x)
      have hx : x - y ∈ (((I₀.map (algebraMap B₀ B)).map (algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B))) • ⊤ : Submodule (AdicCompletion (I₀.map (algebraMap B₀ B)) B) L) := by
        have h1 : x - y ∈ LinearMap.ker (pr 0) := by rw [LinearMap.mem_ker, map_sub, hyx, sub_self]
        rw [hprk 0, zero_add, pow_one] at h1
        have h2 : (((I₀.map (algebraMap B₀ B)).map (algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B))) ^ 1 • (⊤ : Submodule (AdicCompletion (I₀.map (algebraMap B₀ B)) B) L)).restrictScalars B = (I₀.map (algebraMap B₀ B)) ^ 1 • ⊤ := by
          rw [← Ideal.map_pow, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
        rw [pow_one, pow_one] at h2
        rw [← Submodule.restrictScalars_mem B, h2]
        exact h1
      rw [show x = y + (x - y) by abel]
      exact Submodule.add_mem_sup hy hx
    exact top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsAdicComplete.le_jacobson_bot _) htop)

end S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top
end P2MW
export P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top (solution)
