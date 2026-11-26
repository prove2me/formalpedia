-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
-- name    : CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:05:18.137074+00:00
-- url     : https://prove2.me/theorems/e1c8861b-ceb7-5419-a53a-05009bbaaf17
-- title:
--   Sharp Central Renyi Pullback
-- statement:
--   Definitions and structural lemmas for Sharp Central Renyi Pullback, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real
noncomputable section
def activeMixtureIndices
    {iota : Type*} {alpha : iota → Type*}
    (U : Finset iota) (W : ∀ i, Finset (alpha i)) : Finset iota := by
  classical
  exact U.filter fun i => (W i).Nonempty
def shellAdmissibleLengthSet
    (M N : ℕ) (theta eta : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (M + 1)).filter fun s =>
    CentralRenyiAdmissible N s theta eta
def admissibleCohortIndices
    (M s : ℕ) (theta eta : ℝ) : Finset (Fin M) := by
  classical
  exact (Finset.univ : Finset (Fin M)).filter (fun u : Fin M =>
    CentralRenyiAdmissible (M - (u : ℕ)) s theta eta)
def sharpCentralRenyiLargeShellConstant
    (C theta eta transport D : ℝ) : ℝ :=
  C + 2 + 4 * ((eta * Real.log 2 / 16)⁻¹) +
    (2 * (3 : ℝ) ^ theta * centralMomentConstant theta eta) *
      ((2 : ℝ) ^ (1 + theta) *
        (((1 - centralRenyiAbsorption theta transport) *
          centralRenyiRate theta D / (1 + theta)) ^ (-(1 + theta))))
end
end FixedTotal
end CollatzEndpointTransport


