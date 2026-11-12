-- Prove2me | Definitions.Def_APF_B07b_DeclaredInput
-- name    : APF_B07b_DeclaredInput
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-06T20:54:40.624057+00:00
-- url     : https://prove2.me/theorems/ab5c295e-0868-497c-a40e-9983d899eb9c
-- title:
--   Declared input — B07b — BW — Boundary Weight; cost-spectrum non-degeneracy
-- statement:
--   The admissibility cost is non-degenerate on the admissible set: the cost spectrum is rich enough that, generically, configurations are separated by their total costs rather than identified.
-- source:
--   FOUNDATION_INPUTS.json revision 2026-10-04.1 SHA256 bb3b59f6011dd70c5d34c9c830ab65aad0a224b11e26d4d438c4e1ab2ad445c4; controlling USER_DIRECTION_Clean_Spine_2026-10-04.md B07b author clarification 2026-10-05 SHA256 318cf147a625227899c19ba6bb35f7fcdddf012d5e6a1a8e9d64ab61b0fb40b1. Author: Unique minimum; Unique. Existence and uniqueness are explicit on the full original domain; historical generic prose remains preserved. No A2 tie-measurement result is assumed.

import Mathlib.Data.Real.Basic

/-! B07b declared input, basis revision 2026-10-04.1 with the author's
2026-10-05 clarification in USER_DIRECTION_Clean_Spine_2026-10-04.md:
"Unique minimum"; "Unique. We are investigating the ability of A2 to measure ties."
The unqualified uniqueness below is authorized by that clarification, not
asserted to follow from Paper0 v6.2.56's older generic wording (3328-3335).

Interface is the FULL original interface domain (rho,Gamma). Configuration i
is the ORIGINAL configuration universe at that interface. originalAdmissible i
is EXACTLY the source A(rho,Gamma), not a selected subset or a set of minima.
totalCost i is the ORIGINAL total admissibility cost on those configurations,
with the SAME bindings as B07a A2Selection (Paper0:3454-3461,3468-3481,3507-3515).
These are source-vocabulary bindings, exposed for cold fidelity review; a
freely supplied data instance does not certify the physical commitment.

BWUniqueMinimum states existence AND uniqueness of a total-cost minimizer at
every original interface. Existence is explicit, not inferred from at-most-one.
B07a separately places the actual realized configuration at an attained minimum
on these same source bindings; it is not imported or replaced by this input.
No genericRegime, all-pair cost injectivity, cost-list witness, optimizer,
held-domain premise, or result about A2 measuring or resolving ties is assumed.
This defines the declared input predicate; it is not a proof of that input.
-/
set_option autoImplicit false
namespace APFB07b

def IsMinimum
    {Configuration : Type*} (originalAdmissible : Configuration → Prop)
    (totalCost : Configuration → ℝ) (G : Configuration) : Prop :=
  originalAdmissible G ∧ ∀ H, originalAdmissible H → totalCost G ≤ totalCost H

def BWUniqueMinimum
    {Interface : Type*} {Configuration : Interface → Type*}
    (originalAdmissible : (i : Interface) → Configuration i → Prop)
    (totalCost : (i : Interface) → Configuration i → ℝ) : Prop :=
  ∀ i, ∃ G, IsMinimum (originalAdmissible i) (totalCost i) G ∧
    ∀ H, IsMinimum (originalAdmissible i) (totalCost i) H → H = G

end APFB07b


