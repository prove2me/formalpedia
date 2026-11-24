-- Prove2me | Definitions.Def_ReciprocityTheory_ThetaSummability_RealCoinvariants_GlRelZero
-- name    : ReciprocityTheory_ThetaSummability_RealCoinvariants_GlRelZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:24.710932+00:00
-- url     : https://prove2.me/theorems/69706448-63b5-4699-a69d-cd26c2986df0
-- title:
--   Gl Rel Zero
-- statement:
--   Definitions and structural lemmas for Gl Rel Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/RealCoinvariants/GlRelZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ThetaSummability.Real
section Defs
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
def GlRel {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) : Prop :=
  ∀ a b c d : Fin n, E a b * E c d - E c d * E a b =
    (if b = c then E a d else 0) - (if d = a then E c b else 0)
def FamComm {n N : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (E' : Fin N → Fin N → Module.End ℂ M) :
    Prop :=
  ∀ a b k l, E a b * E' k l = E' k l * E a b
structure IsCCR {X : Type*} [DecidableEq X] (α β : X → Module.End ℂ M) : Prop where
  β_α : ∀ x y, β x * α y - α y * β x = if x = y then 1 else 0
  α_α : ∀ x y, α x * α y = α y * α x
  β_β : ∀ x y, β x * β y = β y * β x
variable {n N : ℕ}
def oscL (α β : Fin n × Fin N → Module.End ℂ M) (c : ℂ) (a b : Fin n) : Module.End ℂ M :=
  (∑ k, α (a, k) * β (b, k)) + if a = b then c • (1 : Module.End ℂ M) else 0
def oscR (α β : Fin n × Fin N → Module.End ℂ M) (c : ℂ) (k l : Fin N) : Module.End ℂ M :=
  (∑ a, α (a, k) * β (a, l)) + if k = l then c • (1 : Module.End ℂ M) else 0
def signTwist {m : ℕ} (s : Fin m → ℂ) (E : Fin m → Fin m → Module.End ℂ M) (a b : Fin m) :
    Module.End ℂ M :=
  (s a * s b) • E a b
end Defs
def sgn {m : ℕ} (ε : Fin m → Bool) (a : Fin m) : ℂ := if ε a then 1 else -1
end ReciprocityTheory.ThetaSummability.Real


