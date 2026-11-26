-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
-- name    : CollatzEndpointTransport_Linear_CentralRenyiShell
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:58:16.796493+00:00
-- url     : https://prove2.me/theorems/af50fcc9-dd70-5ae5-8c44-1e1e7627ff2e
-- title:
--   Central Renyi Shell
-- statement:
--   Definitions and structural lemmas for Central Renyi Shell, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real
noncomputable section
end
end FixedTotal
end CollatzEndpointTransport
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real
noncomputable section
local instance centralEndpointCompositionDecidableEq (N : ℕ) :
    DecidableEq (Composition N) :=
  Classical.decEq _
def cohortRenyiSourceMoment
    (M : ℕ) (u : Fin M) (s : ℕ) (theta : ℝ) : ℝ :=
  ((3 : ℝ) ^ s) ^ theta *
    ∑ c ∈ fixedSet (M - (u : ℕ)) s,
      ((mapFiberCardAt
        (fixedSet (M - (u : ℕ)) s)
        (cohortEndpoint u) c : ℕ) : ℝ) ^ theta
end
end FixedTotal
end CollatzEndpointTransport
set_option maxHeartbeats 4000000
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real
noncomputable section
local instance centralShellCompositionDecidableEq (N : ℕ) :
    DecidableEq (Composition N) :=
  Classical.decEq _
def CentralRenyiAdmissible
    (N s : ℕ) (theta eta : ℝ) : Prop :=
  1 < N ∧ 1 < s ∧ s < N ∧
  InCentralRenyiWindow N s eta ∧
  2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1) ∧
  (1 / 2 : ℝ) ≤
    (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N
local instance centralRenyiAdmissibleDecidable
    (N s : ℕ) (theta eta : ℝ) :
    Decidable (CentralRenyiAdmissible N s theta eta) :=
  Classical.propDecidable _
def centralLevelCohortSet
    (M s : ℕ) (theta eta : ℝ) (u : Fin M) :
    Finset (Composition (M - (u : ℕ))) := by
  classical
  exact if CentralRenyiAdmissible (M - (u : ℕ)) s theta eta then
    fixedSet (M - (u : ℕ)) s
  else ∅
def centralLevelEndpointSet
    (M s : ℕ) (theta eta : ℝ) : Finset ℕ :=
  mixedTargetSet (Finset.univ : Finset (Fin M))
    (centralLevelCohortSet M s theta eta) (fun u => cohortEndpoint u)
def centralLevelFiberCard
    (M s : ℕ) (theta eta : ℝ) (y : ℕ) : ℕ :=
  mixedFiberCard (Finset.univ : Finset (Fin M))
    (centralLevelCohortSet M s theta eta) (fun u => cohortEndpoint u) y
def centralLevelRenyiInformation
    (M s : ℕ) (theta eta : ℝ) : ℝ :=
  (((3 : ℝ) ^ (s + 1)) ^ theta /
      (((sourceOddLevel M s).card : ℝ) ^ theta)) *
    ∑ y ∈ centralLevelEndpointSet M s theta eta,
      (centralLevelFiberCard M s theta eta y : ℝ) ^ (1 + theta)
def centralEndpointInformation
    (M : ℕ) (theta eta : ℝ) : ℝ :=
  (∑ s ∈ Finset.range (M + 1),
      centralLevelRenyiInformation M s theta eta) /
    (2 : ℝ) ^ M
end
end FixedTotal
end CollatzEndpointTransport
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real
noncomputable section
def centralSourceSet
    (M : ℕ) (theta eta : ℝ) : Finset (SourceCode M) := by
  classical
  exact Finset.univ.filter fun x =>
    match x with
    | Sum.inl _ => False
    | Sum.inr p =>
        CentralRenyiAdmissible (M - (p.1 : ℕ)) p.2.length theta eta
def centralDiscardedSourceSet
    (M : ℕ) (theta eta : ℝ) : Finset (SourceCode M) :=
  Finset.univ \ centralSourceSet M theta eta
def sourceParityTail
    (M : ℕ) (t : ℝ) : Finset (SourceCode M) := by
  classical
  exact Finset.univ.filter fun x =>
    sourceCodeOddCount x ≤ Terras.parityLowerCutoff t M ∨
      M - Terras.parityLowerCutoff t M ≤ sourceCodeOddCount x
def sourceRealParityTail
    (M : ℕ) (t : ℝ) : Finset (SourceCode M) := by
  classical
  exact Finset.univ.filter fun x =>
    t * M < |(sourceCodeOddCount x : ℝ) - (M : ℝ) / 2|
def sourceLateFirstOdd
    (M K : ℕ) : Finset (SourceCode M) := by
  classical
  exact Finset.univ.filter fun x =>
    match x with
    | Sum.inl _ => True
    | Sum.inr p => K ≤ (p.1 : ℕ)
end
end FixedTotal
end CollatzEndpointTransport
namespace CollatzEndpointTransport
namespace FixedTotal
open scoped Real
noncomputable section
end
end FixedTotal
end CollatzEndpointTransport


