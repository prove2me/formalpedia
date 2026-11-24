-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DerivationConstantVanishes
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DerivationConstantVanishes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:08.262365+00:00
-- url     : https://prove2.me/theorems/51712232-7f94-42f7-b1c2-9d1a7c64fb16
-- title:
--   Derivation Constant Vanishes
-- statement:
--   Definitions and structural lemmas for Derivation Constant Vanishes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DerivationConstantVanishes.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
namespace CommPf
def cc (s : ℂ) (b : Bool) : ℂ := if b then Complex.I * s else -(Complex.I * s)
def al (m : ℕ) (b : Bool) : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X
def k0 (s : ℂ) (b : Bool) : Fm n := MvPolynomial.C (Polynomial.C (-(cc s b)))
def mm (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : Fm n := k0 s b * (MvPolynomial.C (al m b) * yv b l k)
def dl (s : ℂ) (b : Bool) (k l : Fin n) : Derivation (Polynomial ℂ) (Fm n) (Fm n) :=
  MvPolynomial.mkDerivation (Polynomial ℂ)
    (fun v => if v.1 = b then k0 s b * (yv b v.2.1 k * yv b l v.2.2) else 0)
end CommPf
end PositivityTheory.Rg.Sw.SP


