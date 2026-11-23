-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:10.616571+00:00
-- url     : https://prove2.me/theorems/ae047dea-1ab8-44bd-8336-d1e584868e99
-- title:
--   GBTwist
-- statement:
--   Definitions and structural lemmas for GBTwist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBTwist.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
namespace PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
namespace TW
variable {n : ℕ}
def Lc (y : E n) : ℂ := ((Real.log (dP y) : ℝ) : ℂ)
def W (z : ℂ) (y : E n) : ℂ := Complex.exp (-z * Lc y)
def om (k l : Fin n) : E n → ℂ := Dkl k l Lc
def sh (c : ℕ → E n → ℂ) : ℕ → E n → ℂ
  | 0 => fun _ => 0
  | j + 1 => c j
def TD (k l : Fin n) (c : ℕ → E n → ℂ) : ℕ → E n → ℂ :=
  fun j y => Dkl k l (c j) y - om k l y * sh c j y
def TDelta (c : ℕ → E n → ℂ) : ℕ → E n → ℂ := fun j y =>
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((List.finRange n).foldr (fun k c' => TD k (σ k) c') c) j y
end TW
end PositivityTheory.Rg.Sw.WR.K.GB


