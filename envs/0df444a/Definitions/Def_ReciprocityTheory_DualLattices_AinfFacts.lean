-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
-- name    : ReciprocityTheory_DualLattices_AinfFacts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:42.806826+00:00
-- url     : https://prove2.me/theorems/a1091be7-b10b-4081-b4a3-6e6b0aeee419
-- title:
--   Ainf Facts
-- statement:
--   Definitions and structural lemmas for Ainf Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AinfFacts.lean

import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
namespace ReciprocityTheory.PGsh
namespace Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
abbrev A := WittVector p (PreTilt O p)
def root (ε : PreTilt O p) (k : ℕ) : PreTilt O p := (frobeniusEquiv (PreTilt O p) p).symm^[k] ε
def xi (ε : PreTilt O p) : A p O := ∑ i ∈ Finset.range p, teichmuller p (root p O ε 1) ^ i
def nu (ε : PreTilt O p) : A p O := teichmuller p (root p O ε 1) - 1
variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε
end Ainf
end ReciprocityTheory.PGsh


