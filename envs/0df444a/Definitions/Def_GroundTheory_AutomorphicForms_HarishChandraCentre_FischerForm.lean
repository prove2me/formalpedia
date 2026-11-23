-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
-- name    : GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:37.163849+00:00
-- url     : https://prove2.me/theorems/02eb964b-b32d-4aea-b5b4-b81e218b7730
-- title:
--   Fischer Form
-- statement:
--   Definitions and structural lemmas for Fischer Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {σ : Type*}
def mfact (m : σ →₀ ℕ) : ℕ := m.prod fun _ k => k.factorial
noncomputable def fischer (f g : MvPolynomial σ ℂ) : ℂ :=
  ∑ m ∈ g.support, (mfact m : ℂ) * star (coeff m f) * coeff m g
end GroundTheory.Automorphic.HarishChandra


