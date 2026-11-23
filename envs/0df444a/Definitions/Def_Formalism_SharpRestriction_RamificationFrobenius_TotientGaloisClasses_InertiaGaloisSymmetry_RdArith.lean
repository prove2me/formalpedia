-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:07.936804+00:00
-- url     : https://prove2.me/theorems/4008bbbb-5eca-487e-ba2d-0f4e127f23c2
-- title:
--   Rd Arith
-- statement:
--   Definitions and structural lemmas for Rd Arith, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
namespace Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]
def KK (N : ℕ) [NeZero N] (f : ℕ) : Finset (ZMod N)ˣ := univ.filter fun u => (u : ZMod N).val ≡ 1 [MOD f]
open Classical in

def rho (U : Subgroup (ZMod N)ˣ) (f : ℕ) : ℝ :=
  (((KK N f).filter fun u => u ∉ U).card : ℝ) * f.totient / N.totient
end Formalism.HC.Der.Rd
end


