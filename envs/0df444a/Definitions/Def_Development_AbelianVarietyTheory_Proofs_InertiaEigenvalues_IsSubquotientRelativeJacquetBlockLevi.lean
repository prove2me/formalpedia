-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientRelativeJacquetBlockLevi
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientRelativeJacquetBlockLevi
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:10:03.365055+00:00
-- url     : https://prove2.me/theorems/a902a735-4680-4f74-99de-909808d34249
-- title:
--   Is Subquotient Relative Jacquet Block Levi
-- statement:
--   Definitions and structural lemmas for Is Subquotient Relative Jacquet Block Levi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientRelativeJacquetBlockLevi.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InSupportOfIsSubquotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages GlobalTheory.InertSupp
namespace GlobalTheory.JacStagesExact
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def relJacMap (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) V}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) W} (f : σ.IntertwiningMap τ) :
    (relJacD e' σ).IntertwiningMap (relJacD e' τ) :=
  twistMap (jacquetMap f _ _ _) _
end GlobalTheory.JacStagesExact


