-- Prove2me | solution 1 for AlgebraicGeometry.AdmissibleAlgebra.forall_pow_smul_mem_range_rTensor_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/de23fe8b-d82d-52d1-a6b2-dad532115d2b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_forall_pow_smul_mem_range_rTensor_of_flat

set_option autoImplicit false

open TensorProduct

universe u v w

namespace W2A

theorem pow_smul_eq_zero_of_flat_of_forall
    {B : Type u} [CommRing B] {Q : Type v} [AddCommGroup Q] [Module B Q] (t : B) (e : ℕ)
    (h : ∀ q : Q, (∃ k : ℕ, t ^ k • q = 0) → t ^ e • q = 0)
    (S : Type v) [AddCommGroup S] [Module B S] [Module.Flat B S]
    (x : Q ⊗[B] S) (hx : ∃ k : ℕ, t ^ k • x = 0) : t ^ e • x = 0 := by
  obtain ⟨k, hk⟩ := hx

  let T : Submodule B Q := Submodule.torsionBy B Q (t ^ e)
  have hT : ∀ q : Q, q ∈ T ↔ t ^ e • q = 0 := fun q => Submodule.mem_torsionBy_iff _ _
  have hinj1 : ∀ q : Q ⧸ T, t • q = 0 → q = 0 := by
    intro q hq
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective T q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hT, ← mul_smul, ← pow_succ] at hq
    rw [Submodule.Quotient.mk_eq_zero, hT]
    exact h q ⟨e + 1, hq⟩
  have hinjS : Function.Injective (LinearMap.rTensor S (t • (LinearMap.id : (Q ⧸ T) →ₗ[B] (Q ⧸ T)))) := by
    apply Module.Flat.rTensor_preserves_injective_linearMap
    intro q q' hqq'
    rw [← sub_eq_zero]
    apply hinj1
    rw [smul_sub, sub_eq_zero]
    simpa using hqq'
  rw [LinearMap.rTensor_smul, LinearMap.rTensor_id] at hinjS
  have hinjk : ∀ (m : ℕ) (y : (Q ⧸ T) ⊗[B] S), t ^ m • y = 0 → y = 0 := by
    intro m
    induction m with
    | zero => intro y hy; rwa [pow_zero, one_smul] at hy
    | succ m ih =>
      intro y hy
      rw [pow_succ', mul_smul] at hy
      have key : (t • (LinearMap.id : (Q ⧸ T) ⊗[B] S →ₗ[B] (Q ⧸ T) ⊗[B] S)) (t ^ m • y) =
          (t • (LinearMap.id : (Q ⧸ T) ⊗[B] S →ₗ[B] (Q ⧸ T) ⊗[B] S)) 0 := by
        simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_zero]
        exact hy
      exact ih y (hinjS key)

  have hex := Module.Flat.rTensor_exact S (LinearMap.exact_subtype_mkQ T)
  have hx0 : LinearMap.rTensor S T.mkQ x = 0 := by
    apply hinjk k
    rw [← map_smul, hk, map_zero]
  obtain ⟨τ, rfl⟩ := (hex _).1 hx0
  rw [← map_smul]

  have hzero : t ^ e • (LinearMap.id : (↥T ⊗[B] S) →ₗ[B] (↥T ⊗[B] S)) = 0 := by
    rw [← LinearMap.rTensor_id S ↥T, ← LinearMap.rTensor_smul]
    have : t ^ e • (LinearMap.id : ↥T →ₗ[B] ↥T) = 0 := by
      ext ⟨q, hq⟩
      rw [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply]
      show t ^ e • q = 0
      exact (hT q).1 hq
    rw [this, LinearMap.rTensor_zero]
  have hτ := congrArg (fun φ => φ τ) hzero
  simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply] at hτ
  rw [hτ, map_zero]

end W2A

theorem solution
    {B : Type u} [CommRing B] {M N P : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    [AddCommGroup P] [Module B P] (f : M →ₗ[B] N) (g : N →ₗ[B] P) (hfg : g.comp f = 0) (t : B) (e : ℕ)
    (h : ∀ n : N, g n = 0 → (∃ k : ℕ, t ^ k • n ∈ LinearMap.range f) → t ^ e • n ∈ LinearMap.range f)
    (S : Type v) [AddCommGroup S] [Module B S] [Module.Flat B S]
    (n : N ⊗[B] S) (hn : LinearMap.rTensor S g n = 0) (hk : ∃ k : ℕ, t ^ k • n ∈ LinearMap.range (LinearMap.rTensor S f)) :
    t ^ e • n ∈ LinearMap.range (LinearMap.rTensor S f) := by
  obtain ⟨k, hk⟩ := hk

  let K : Submodule B N := LinearMap.ker g
  have hfK : ∀ m : M, f m ∈ K := fun m => by
    have := LinearMap.congr_fun hfg m
    simp at this
    exact this
  let f' : M →ₗ[B] ↥K := LinearMap.codRestrict K f hfK
  have hιf' : K.subtype.comp f' = f := LinearMap.ext fun m => rfl

  have hQ : ∀ q : ↥K ⧸ LinearMap.range f', (∃ k : ℕ, t ^ k • q = 0) → t ^ e • q = 0 := by
    intro q ⟨k', hk'⟩
    obtain ⟨⟨n₀, hn₀⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hk' ⊢
    obtain ⟨m, hm⟩ := LinearMap.mem_range.1 hk'
    have h1 : t ^ k' • n₀ ∈ LinearMap.range f :=
      LinearMap.mem_range.2 ⟨m, by rw [← hιf', LinearMap.comp_apply, hm]; rfl⟩
    obtain ⟨m', hm'⟩ := LinearMap.mem_range.1 (h n₀ (LinearMap.mem_ker.1 hn₀) ⟨k', h1⟩)
    exact LinearMap.mem_range.2 ⟨m', Subtype.ext hm'⟩

  have hexK : Function.Exact (LinearMap.rTensor S K.subtype) (LinearMap.rTensor S g) :=
    Module.Flat.rTensor_exact S (LinearMap.exact_iff.2 (K.range_subtype).symm)
  have hexQ : Function.Exact (LinearMap.rTensor S f') (LinearMap.rTensor S (LinearMap.range f').mkQ) :=
    Module.Flat.rTensor_exact S (LinearMap.exact_iff.2 (Submodule.ker_mkQ (LinearMap.range f')))
  have hinjι : Function.Injective (LinearMap.rTensor S K.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ K.injective_subtype
  have hcomp : LinearMap.rTensor S f = (LinearMap.rTensor S K.subtype).comp (LinearMap.rTensor S f') := by
    rw [← LinearMap.rTensor_comp, hιf']

  obtain ⟨κ, rfl⟩ := (hexK n).1 hn
  obtain ⟨μ, hμ⟩ := LinearMap.mem_range.1 hk
  rw [hcomp, LinearMap.comp_apply, ← map_smul] at hμ
  have hμ' : LinearMap.rTensor S f' μ = t ^ k • κ := hinjι hμ
  have hx : t ^ k • LinearMap.rTensor S (LinearMap.range f').mkQ κ = 0 := by
    rw [← map_smul, ← hμ']
    exact hexQ.apply_apply_eq_zero μ
  have hτ := W2A.pow_smul_eq_zero_of_flat_of_forall t e hQ S _ ⟨k, hx⟩
  rw [← map_smul] at hτ
  obtain ⟨μ', hμ''⟩ := (hexQ _).1 hτ
  exact LinearMap.mem_range.2 ⟨μ', by rw [hcomp, LinearMap.comp_apply, hμ'', map_smul]⟩

end S_AlgebraicGeometry_AdmissibleAlgebra_forall_pow_smul_mem_range_rTensor_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_forall_pow_smul_mem_range_rTensor_of_flat (solution)
