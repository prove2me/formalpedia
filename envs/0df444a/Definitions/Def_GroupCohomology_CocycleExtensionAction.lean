-- Prove2me | Definitions.Def_GroupCohomology_CocycleExtensionAction
-- name    : GroupCohomology_CocycleExtensionAction
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:15.754727+00:00
-- url     : https://prove2.me/theorems/6bd77e1d-3c4b-4927-8f87-b8118c850318
-- title:
--   The representation extension attached to a one-cocycle
-- statement:
--   Let $ρ$ be a local Galois representation on an $𝔽_p$-module $W$ and let $c$ be a one-cocycle. The file defines the additive Galois action on $W×𝔽_p$ by $$σ·(w,a)=(ρ(σ)w+a c(σ),a).$$ This realizes the cocycle as an extension of the trivial one-dimensional representation by $W$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_GroupCohomology_FiniteFlatCocycle
set_option autoImplicit false

namespace groupCohomology

/-- The additive local representation attached to a one-cocycle, with constant
one-dimensional quotient. Its underlying additive group is `W × ZMod p`. -/
noncomputable def cocycleExtensionAction (p : ℕ) [Fact p.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (ρ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W)
    (c : cocycles₁ (Rep.of ρ)) :
    DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (W × ZMod p) where
  smul σ x := (ρ σ x.1 + x.2 • c σ, x.2)
  one_smul x := by
    apply Prod.ext
    · change ρ 1 x.1 + x.2 • c 1 = x.1
      have hc1 : c 1 = 0 := cocycles₁_map_one c
      rw [hc1, smul_zero, add_zero, map_one]
      rfl
    · rfl
  mul_smul σ τ x := by
    ext
    · change ρ (σ * τ) x.1 + x.2 • c (σ * τ) =
        ρ σ (ρ τ x.1 + x.2 • c τ) + x.2 • c σ
      have hcmul : c (σ * τ) = ρ σ (c τ) + c σ :=
        (mem_cocycles₁_iff _).mp c.property σ τ
      rw [hcmul]
      simp [map_mul, Module.End.mul_apply, smul_add, add_assoc]
    · rfl
  smul_zero σ := by
    apply Prod.ext
    · change ρ σ 0 + (0 : ZMod p) • c σ = 0
      rw [map_zero, zero_smul, add_zero]
    · rfl
  smul_add σ x y := by
    ext
    · change ρ σ (x.1 + y.1) + (x.2 + y.2) • c σ =
        (ρ σ x.1 + x.2 • c σ) + (ρ σ y.1 + y.2 • c σ)
      rw [map_add, add_smul]
      abel
    · rfl

end groupCohomology


