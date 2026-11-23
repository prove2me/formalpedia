-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_DoubleSumReduceSecond
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_DoubleSumReduceSecond
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:31.698796+00:00
-- url     : https://prove2.me/theorems/2e23e02e-2d39-4574-81de-4281886748a1
-- title:
--   Double Sum Reduce Second
-- statement:
--   Definitions and structural lemmas for Double Sum Reduce Second, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/DoubleSumReduceSecond.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace UpperTheory.Reformulated.B.P6.r26a
open scoped HSub SubNegMonoid AddGroup AddGroupWithOne Ring HMul Distrib OfNat Zero MulZeroClass Finset Semiring Fin Complex AddCommGroup Module Module.End
noncomputable def PositivityTheory.D.DSIC.KRel :
    {n : ℕ} → {A : Type} → [inst_h0 : Ring A] → (Fin n → Bool) → (Fin n → Fin n → A) → Prop :=
  fun {n : ℕ} {A : Type} {inst_f0 : Ring A} (ε_h1 : Fin n → Bool) (F : Fin n → Fin n → A) ↦ ∀ (a b c d : Fin n), ε_h1 a = ε_h1 b → ε_h1 c = ε_h1 d → F a b * F c d - F c d * F a b = (if b = c then F a d else OfNat.ofNat (nat_lit 0)) - if d = a then F c b else OfNat.ofNat (nat_lit 0)
noncomputable def Formalism.REAL.CasK.{u_1} :
    {A : Type u_1} → [inst_h0 : Ring A] → {n : ℕ} → (Fin n → Bool) → (Fin n → Fin n → A) → A :=
  fun {A : Type u_1} {inst_f1 : Ring A} {n : ℕ} (ε_h1 : Fin n → Bool) (E : Fin n → Fin n → A) ↦ ∑ a : Fin n, ∑ b : Fin n, if ε_h1 a = ε_h1 b then E a b * E b a else OfNat.ofNat (nat_lit 0)
end UpperTheory.Reformulated.B.P6.r26a


