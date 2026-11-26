-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
-- name    : CollatzEndpointTransport_Linear_CentralRenyiPullback
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:04:37.922928+00:00
-- url     : https://prove2.me/theorems/13898291-0fb2-4305-8e4e-8466ec273175
-- title:
--   Central Renyi Pullback
-- statement:
--   Definitions and structural lemmas for Central Renyi Pullback, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
local instance centralPullbackSourceCodeDecidableEq (M : ℕ) :
    DecidableEq (SourceCode M) := Classical.decEq _
def centralLevelSourceSet
    (M s : ℕ) (theta eta : ℝ) : Finset (SourceCode M) := by
  classical
  exact (sourceOddLevel M s).filter fun x =>
    x ∈ centralSourceSet M theta eta
def centralLevelPairImage
    (M s : ℕ) (theta eta : ℝ) : Finset (SourceCode M) := by
  classical
  exact ((Finset.univ : Finset (Fin M)).sigma
    (centralLevelCohortSet M s theta eta)).image
      (fun p => (Sum.inr p : SourceCode M))
def centralSourceEndpointBad
    (S : Set ℕ) (M : ℕ) (theta eta : ℝ) :
    Finset (SourceCode M) := by
  classical
  exact (centralSourceSet M theta eta).filter fun x =>
    sourceEndpoint x ∉ S
def centralLevelBadEndpointSet
    (S : Set ℕ) (M s : ℕ) (theta eta : ℝ) : Finset ℕ := by
  classical
  exact (centralLevelEndpointSet M s theta eta).filter fun y => y ∉ S
def centralLevelBadMass
    (S : Set ℕ) (M s : ℕ) (theta eta : ℝ) : ℕ := by
  classical
  exact ((centralLevelSourceSet M s theta eta).filter fun x =>
    sourceEndpoint x ∉ S).card
def centralRenyiRate (theta D : ℝ) : ℝ :=
  theta / (1 + theta) * OptimizedLinearPullback.psi D
def centralRenyiNormalizedRate (theta D : ℝ) : ℝ :=
  centralRenyiRate theta D / (Real.log 2 * D)
def centralRenyiAsymptoticRate (theta : ℝ) : ℝ :=
  theta / (1 + theta) *
    (Real.log 3 / (2 * Real.log 2))
def centralRenyiAbsorption (theta transport : ℝ) : ℝ :=
  (transport + centralRenyiAsymptoticRate theta) /
    (2 * centralRenyiAsymptoticRate theta)
def centralRenyiShellRate (theta transport D : ℝ) : ℝ :=
  centralRenyiAbsorption theta transport * centralRenyiRate theta D
def centralRenyiNormalizedShellRate
    (theta transport D : ℝ) : ℝ :=
  centralRenyiShellRate theta transport D / (Real.log 2 * D)
def centralRenyiDiscardDepth (eta : ℝ) (M : ℕ) : ℕ :=
  ⌊eta * M / 8⌋₊
def centralRenyiStartupScale (theta eta : ℝ) : ℝ :=
  max 4 <| max (4 / eta) <|
    max (2 / (1 / 2 - eta)) <|
      max (4 + 4 * eta / centralRenyiGap theta eta)
        (1 / (Real.log 2 / Real.log 3 - (1 / 2 + eta)))
def centralRenyiThreshold (theta D : ℝ) (M : ℕ) : ℝ :=
  Real.exp
    ((OptimizedLinearPullback.psi D / (1 + theta)) * M)
def centralRenyiLargeShellConstant
    (C theta eta transport D : ℝ) : ℝ :=
  C + 2 +
    4 * ((eta * Real.log 2 / 16)⁻¹) +
    (3 : ℝ) ^ theta * centralMomentConstant theta eta *
      (64 * ((((1 - centralRenyiAbsorption theta transport) *
        centralRenyiRate theta D / 6)⁻¹) ^ 6))
def centralRenyiStartupIndex (theta eta : ℝ) : ℕ :=
  ⌈centralRenyiStartupScale theta eta⌉₊
def centralRenyiShellConstant
    (C theta eta transport D : ℝ) : ℝ :=
  centralRenyiLargeShellConstant C theta eta transport D +
    Real.exp (centralRenyiShellRate theta transport D *
      centralRenyiStartupIndex theta eta)
def centralRenyiPullbackConstant
    (C theta eta transport D : ℝ) : ℝ :=
  2 * centralRenyiShellConstant C theta eta transport D /
    (2 * Real.exp (-centralRenyiShellRate theta transport D) - 1)
def centralRenyiInverseRateFactor (theta transport : ℝ) : ℝ :=
  ((6 / (1 - centralRenyiAbsorption theta transport)) *
    (centralRenyiAbsorption theta transport /
      (transport * Real.log 2))) ^ 6
def centralRenyiStageShellConstant
    (theta eta transport : ℝ) : ℝ :=
  4 + 4 * ((eta * Real.log 2 / 16)⁻¹) +
    Real.exp ((eta ^ 2 / 8) * centralRenyiStartupIndex theta eta) +
    (3 : ℝ) ^ theta * centralMomentConstant theta eta *
      (64 * centralRenyiInverseRateFactor theta transport)
def centralRenyiDenominatorFloor (eta : ℝ) : ℝ :=
  2 * Real.exp (-(eta ^ 2 / 8)) - 1
def centralRenyiStageConstant
    (theta eta transport : ℝ) : ℝ :=
  2 * centralRenyiStageShellConstant theta eta transport /
    centralRenyiDenominatorFloor eta
end
end FixedTotal
end CollatzEndpointTransport


