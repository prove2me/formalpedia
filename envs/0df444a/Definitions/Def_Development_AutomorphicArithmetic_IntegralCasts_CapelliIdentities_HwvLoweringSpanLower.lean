-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HwvLoweringSpanLower
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HwvLoweringSpanLower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:56:47.122603+00:00
-- url     : https://prove2.me/theorems/192e5ab4-c44b-420b-8a7e-f886711d53f5
-- title:
--   Hwv Lowering Span Lower
-- statement:
--   Definitions and structural lemmas for Hwv Lowering Span Lower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HwvLoweringSpanLower.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk30.GLOps.{u_2, u_3} :
    ℕ → (K : Type u_2) → (V : Type u_3) → [inst : Field K] → [inst_1 : AddCommGroup V] → [_root_.Module K V] → Type u_3 :=
    fun (n : ℕ) (K : Type u_2) (V : Type u_3) [Field K] [AddCommGroup V] [_root_.Module K V] ↦
      Fin n → Fin n → Module.End K V
noncomputable def UpperTheory.Reformulated.B.Qk30.loweringMonoid.{u_1, u_2} :
    {n : ℕ} →
      {K : Type u_1} →
        {V : Type u_2} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qk30.GLOps n K V → Submonoid (Module.End K V) :=
    fun {n : ℕ} {K : Type u_1} {V : Type u_2} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) ↦
      Submonoid.closure {g : Module.End K V | ∃ (c : Fin n), ∃ d < c, g = E c d}
noncomputable def UpperTheory.Reformulated.B.Qk30.weightSp.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qk30.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) (mu : Fin n → ℤ) ↦
      ⨅ (a : Fin n), LinearMap.ker (E a a - (↑(mu a) : K) • (1 : Module.End K V))
noncomputable def UpperTheory.Reformulated.B.Qk30.IsHWV.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qk30.GLOps n K V → (Fin n → ℤ) → V → Prop :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) (lam : Fin n → ℤ) (v : V) ↦
      v ≠ (0 : V) ∧ v ∈ UpperTheory.Reformulated.B.Qk30.weightSp E lam ∧ ∀ (a b : Fin n), a < b → (E a b : V → V) v = (0 : V)
noncomputable def UpperTheory.Reformulated.B.Qk30.hwvLoweringSpan.{u_1, u_2} :
    {n : ℕ} →
      {K : Type u_1} →
        {V : Type u_2} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qk30.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_1} {V : Type u_2} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) (mu : Fin n → ℤ) ↦
      Submodule.span K
        {x : V | ∃ u ∈ UpperTheory.Reformulated.B.Qk30.loweringMonoid E, ∃ (w : V), UpperTheory.Reformulated.B.Qk30.IsHWV E mu w ∧ x = (u : V → V) w}


