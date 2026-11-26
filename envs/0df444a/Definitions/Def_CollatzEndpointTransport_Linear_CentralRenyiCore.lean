-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
-- name    : CollatzEndpointTransport_Linear_CentralRenyiCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:29:06.060327+00:00
-- url     : https://prove2.me/theorems/9ebaad35-f887-4133-ab03-980bcd758891
-- title:
--   Central Renyi Core
-- statement:
--   Definitions and structural lemmas for Central Renyi Core, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne


set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open scoped Real
noncomputable section
def centralRenyiAlpha (theta : ℝ) : ℝ :=
  ((2 : ℝ) ^ theta - 1) / ((3 : ℝ) ^ theta - 1)
def centralRenyiGap (theta eta : ℝ) : ℝ :=
  centralRenyiAlpha theta - (1 / 2 + eta)
def centralRenyiPiStar (theta eta : ℝ) : ℝ :=
  centralRenyiAlpha theta - centralRenyiGap theta eta / 2
def centralRenyiRatio (theta pi : ℝ) : ℝ :=
  (3 : ℝ) ^ theta * pi / ((2 : ℝ) ^ theta - 1 + pi)
@[simp]
theorem centralRenyiAlpha_one :
    centralRenyiAlpha 1 = 1 / 2 := by
  norm_num [centralRenyiAlpha]
@[simp]
theorem centralRenyiRatio_one_half_one :
    centralRenyiRatio 1 (1 / 2) = 1 := by
  norm_num [centralRenyiRatio]
def unrestrictedReverseSpendRatio (theta : ℝ) : ℝ :=
  (3 : ℝ) ^ theta / ((2 : ℝ) ^ (1 + theta) - 1)
@[simp]
theorem unrestrictedReverseSpendRatio_one :
    unrestrictedReverseSpendRatio 1 = 1 := by
  norm_num [unrestrictedReverseSpendRatio]
end
end FixedTotal
end CollatzEndpointTransport
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
noncomputable section
end
end FixedTotal
end CollatzEndpointTransport
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
local instance centralMomentCompositionDecidableEq (N : ℕ) :
    DecidableEq (Composition N) :=
  Classical.decEq _
def fixedRenyiNumerator (N s : ℕ) (theta : ℝ) : ℝ :=
  ((3 ^ s : ℕ) : ℝ) ^ theta *
    ∑ a : Fin (3 ^ s),
      (fixedFiberCard N s a : ℝ) *
        (fixedFiberCard N s a : ℝ) ^ theta
def fixedRenyiMoment (N s : ℕ) (theta : ℝ) : ℝ :=
  fixedRenyiNumerator N s theta /
    ((fixedSet N s).card : ℝ) ^ (1 + theta)
def fixedLiftMoment (N s : ℕ) (theta : ℝ) : ℝ :=
  ∑ c ∈ fixedSet N s,
    (((3 ^ s + syracuseNumerator c : ℕ) : ℝ) ^ theta)
end
end FixedTotal
end CollatzEndpointTransport
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
def scaledBinomialMass (n k j : ℕ) : ℕ :=
  n.choose j * k ^ j * (n - k) ^ (n - j)
end FixedTotal
end CollatzEndpointTransport
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped NNReal
noncomputable section
local instance terminalCompositionDecidableEq (N : ℕ) :
    DecidableEq (Composition N) :=
  Classical.decEq _
def terminalBlocks {N : ℕ} (c : Composition N) (r : ℕ) : List ℕ :=
  c.blocks.drop (c.length - r)
def initialBlocks {N : ℕ} (c : Composition N) (r : ℕ) : List ℕ :=
  c.blocks.take (c.length - r)
def reverseSpend {N : ℕ} (c : Composition N) (r : ℕ) : ℕ :=
  (terminalBlocks c r).sum
theorem initialBlocks_length
    {N : ℕ} (c : Composition N) (r : ℕ) :
    (initialBlocks c r).length = c.length - r := by
  unfold initialBlocks
  rw [List.length_take]
  change min (c.blocks.length - r) c.blocks.length = c.blocks.length - r
  exact min_eq_left (Nat.sub_le _ _)
def initialComposition
    {N : ℕ} (c : Composition N) (r : ℕ) :
    Composition (N - reverseSpend c r) where
  blocks := initialBlocks c r
  blocks_pos := by
    intro i hi
    exact c.blocks_pos (List.mem_of_mem_take hi)
  blocks_sum := by
    have hsum := List.sum_take_add_sum_drop c.blocks (c.length - r)
    rw [c.blocks_sum] at hsum
    unfold initialBlocks reverseSpend terminalBlocks
    omega
@[simp]
theorem initialComposition_length
    {N : ℕ} (c : Composition N) (r : ℕ) :
    (initialComposition c r).length = c.length - r := by
  change (initialBlocks c r).length = c.length - r
  exact initialBlocks_length c r
def terminalFiber (N s r : ℕ) (d : List ℕ) : Finset (Composition N) :=
  (fixedSet N s).filter fun c => terminalBlocks c r = d
theorem mem_terminalFiber_iff
    {N s r : ℕ} {d : List ℕ} {c : Composition N} :
    c ∈ terminalFiber N s r d ↔
      c.length = s ∧ terminalBlocks c r = d := by
  simp [terminalFiber, fixedSet]
def castComposition {A B : ℕ} (h : A = B) (c : Composition A) : Composition B :=
  h ▸ c
@[simp]
theorem castComposition_blocks
    {A B : ℕ} (h : A = B) (c : Composition A) :
    (castComposition h c).blocks = c.blocks := by
  subst B
  rfl
@[simp]
theorem castComposition_length
    {A B : ℕ} (h : A = B) (c : Composition A) :
    (castComposition h c).length = c.length := by
  subst B
  rfl
def terminalPrefixMap
    {N s r : ℕ} (d : List ℕ)
    (c : {c : Composition N // c ∈ terminalFiber N s r d}) :
    FixedComposition (N - d.sum) (s - r) := by
  have hc := (mem_terminalFiber_iff.mp c.2)
  have hspend : reverseSpend c.1 r = d.sum := by
    unfold reverseSpend
    rw [hc.2]
  let p : Composition (N - reverseSpend c.1 r) := initialComposition c.1 r
  have htotal : N - reverseSpend c.1 r = N - d.sum := by rw [hspend]
  have hlength : p.length = s - r := by
    simpa [p, hc.1] using initialComposition_length c.1 r
  refine ⟨castComposition htotal p, ?_⟩
  simpa using hlength
def fixedBlockSet (D r : ℕ) : Finset (List ℕ) :=
  (fixedSet D r).image fun c => c.blocks
def terminalPatternImage (N s r : ℕ) : Finset (List ℕ) :=
  (fixedSet N s).image fun c => terminalBlocks c r
def terminalPatternSet (N s r D : ℕ) : Finset (List ℕ) :=
  (terminalPatternImage N s r).filter fun d => d.sum = D
end
end FixedTotal
end CollatzEndpointTransport


