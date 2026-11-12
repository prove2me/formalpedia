-- Prove2me | Definitions.Def_APF_B07a_DeclaredInput
-- name    : APF_B07a_DeclaredInput
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-06T20:54:34.505468+00:00
-- url     : https://prove2.me/theorems/e9968cbd-3ed6-429b-b2fa-4a5ef446aa17
-- title:
--   Declared input — B07a — A2 — realization at the admissible cost minimum
-- statement:
--   Realization is the minimum-cost admissible configuration.
-- source:
--   APF Reconstruction Spine/FOUNDATION_INPUTS.json; revision 2026-10-04.1; SHA-256 bb3b59f6011dd70c5d34c9c830ab65aad0a224b11e26d4d438c4e1ab2ad445c4; declared input B07a.

import Mathlib.Data.Real.Basic

/-! Full A2 input, revision 2026-10-04.1, not a theorem on an arbitrary set.
Interface is the entire original interface domain (rho,Gamma). Configuration i
is its original configuration universe; originalAdmissible i is EXACTLY the
source A(rho,Gamma), fixed by the keystone and its other adopted conditions,
not a selected subset. totalCost i is the ORIGINAL total admissibility cost
(sum of distinction costs in the adopted Paper0 statement), never a surrogate.
realized i is the actual realized configuration at that SAME interface.
These bindings are explicit source vocabulary exposed to cold fidelity review.
No data instance on a freely supplied set establishes the physical input.
Source: author-pinned Paper0 v6.2.56:3454-3458,3468-3481,3491-3515.
A2 locates the actual configuration at an attained minimum; no optimizer,
search, held-domain faithfulness, CompleteRoot, or uniqueness law is asserted.
-/
set_option autoImplicit false
namespace APFB07a

def A2Selection
    {Interface : Type*} {Configuration : Interface → Type*}
    (originalAdmissible : (i : Interface) → Configuration i → Prop)
    (totalCost : (i : Interface) → Configuration i → ℝ)
    (realized : (i : Interface) → Configuration i) : Prop :=
  ∀ i, originalAdmissible i (realized i) ∧
    ∀ G, originalAdmissible i G → totalCost i (realized i) ≤ totalCost i G

end APFB07a


