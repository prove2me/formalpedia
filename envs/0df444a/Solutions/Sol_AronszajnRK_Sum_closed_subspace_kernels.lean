-- Prove2me | solution 1 for AronszajnRK.Sum.closed_subspace_kernels
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:36:11.192977+00:00
-- url     : https://prove2.me/submissions/6230547d-5793-4851-a14b-b2932f11ab05

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Sum_IsReproducingKernelOn

open RKHS
open scoped InnerProductSpace

/-! # Closed subspaces of an RKHS (Aronszajn §2 (7))

If `F` has a reproducing kernel `K`, so does every closed linear subspace `F'`, and the
kernels of complementary subspaces add up to `K`. -/

namespace ClosedSubAux

/-- The reproducing kernel of a subspace is unique. -/
lemma uniq_kernel {X : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (S : Submodule ℂ H) (k₁ k₂ : X → H)
    (h₁ : AronszajnRK.Sum.IsReproducingKernelOn S k₁)
    (h₂ : AronszajnRK.Sum.IsReproducingKernelOn S k₂) : k₁ = k₂ := by
  funext y
  have hsub : k₁ y - k₂ y ∈ S := S.sub_mem (h₁.1 y) (h₂.1 y)
  have horth : ∀ f ∈ S, ⟪k₁ y - k₂ y, f⟫_ℂ = 0 := by
    intro f hf
    rw [inner_sub_left (𝕜 := ℂ), h₂.2 y f hf, h₁.2 y f hf, sub_self]
  have hzero := horth _ hsub
  exact sub_eq_zero.mp (inner_self_eq_zero (𝕜 := ℂ).mp hzero)

/-- Any reproducing kernel of a complete subspace is the projection of the kernel function. -/
lemma kernel_is_projection {X : Type*} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    (S : Submodule ℂ H) [S.HasOrthogonalProjection] (k : X → H)
    (hk : AronszajnRK.Sum.IsReproducingKernelOn S k) (y : X) :
    k y = S.starProjection (kerFun H y 1) := by
  have hproj : AronszajnRK.Sum.IsReproducingKernelOn S
      (fun y => S.starProjection (kerFun H y 1)) :=
    ⟨fun y => S.starProjection_apply_mem _, fun y f hf => by
      have hz : ⟪kerFun H y 1 - S.starProjection (kerFun H y 1), f⟫_ℂ = 0 :=
        S.starProjection_inner_eq_zero (kerFun H y 1) f hf
      have h1 : ⟪S.starProjection (kerFun H y 1), f⟫_ℂ = ⟪kerFun H y 1, f⟫_ℂ :=
        (calc ⟪kerFun H y 1, f⟫_ℂ
            = ⟪(kerFun H y 1 - S.starProjection (kerFun H y 1))
                + S.starProjection (kerFun H y 1), f⟫_ℂ := by
                rw [sub_add_cancel]
          _ = ⟪kerFun H y 1 - S.starProjection (kerFun H y 1), f⟫_ℂ
              + ⟪S.starProjection (kerFun H y 1), f⟫_ℂ := inner_add_left _ _ _
          _ = ⟪S.starProjection (kerFun H y 1), f⟫_ℂ := by rw [hz, zero_add]).symm
      rw [h1, RKHS.kerFun_inner]
      simp⟩
  have h := uniq_kernel S k _ hk hproj
  rw [h]

end ClosedSubAux

open ClosedSubAux

theorem solution {X : Type*} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    (F' : Submodule ℂ H) (hF' : IsClosed (F' : Set H)) :
    (∃ k' : X → H, AronszajnRK.Sum.IsReproducingKernelOn F' k') ∧
    ∀ k' k'' : X → H, AronszajnRK.Sum.IsReproducingKernelOn F' k' → AronszajnRK.Sum.IsReproducingKernelOn F'ᗮ k'' →
      ∀ x y : X, k' y x + k'' y x = AronszajnRK.Sum.kernelFn H x y := by
  constructor
  · refine ⟨fun y => F'.starProjection (kerFun H y 1), ?_⟩
    constructor
    · intro y; exact F'.starProjection_apply_mem _
    · intro y f hf
      have hz : ⟪kerFun H y 1 - F'.starProjection (kerFun H y 1), f⟫_ℂ = 0 :=
        F'.starProjection_inner_eq_zero (kerFun H y 1) f hf
      have h1 : ⟪F'.starProjection (kerFun H y 1), f⟫_ℂ = ⟪kerFun H y 1, f⟫_ℂ :=
        (calc ⟪kerFun H y 1, f⟫_ℂ
            = ⟪(kerFun H y 1 - F'.starProjection (kerFun H y 1))
                + F'.starProjection (kerFun H y 1), f⟫_ℂ := by
                rw [sub_add_cancel]
          _ = ⟪kerFun H y 1 - F'.starProjection (kerFun H y 1), f⟫_ℂ
              + ⟪F'.starProjection (kerFun H y 1), f⟫_ℂ := inner_add_left _ _ _
          _ = ⟪F'.starProjection (kerFun H y 1), f⟫_ℂ := by rw [hz, zero_add]).symm
      rw [h1, RKHS.kerFun_inner]
      simp
  · intro k' k'' hk' hk'' x y
    -- both kernels are the corresponding orthogonal projections of the kernel function
    have h1 : k' y = F'.starProjection (kerFun H y 1) :=
      kernel_is_projection F' k' hk' y
    have h2 : k'' y = F'ᗮ.starProjection (kerFun H y 1) :=
      kernel_is_projection F'ᗮ k'' hk'' y
    have h3 : F'.starProjection (kerFun H y 1) + F'ᗮ.starProjection (kerFun H y 1)
        = kerFun H y 1 := by
      rw [F'.starProjection_orthogonal_val]
      abel
    show k' y x + k'' y x = AronszajnRK.Sum.kernelFn H x y
    have h4 : k' y + k'' y = kerFun H y 1 := by rw [h1, h2, h3]
    have h5 : (k' y) x + (k'' y) x = (kerFun H y 1) x := by
      have := congrArg (fun (u : H) => u x) h4
      simpa using this
    rw [h5, RKHS.kerFun_apply]
    rfl
