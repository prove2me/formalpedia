-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
-- name    : CollatzEndpointTransport_Linear_CentralRenyiReverse
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:33:50.577867+00:00
-- url     : https://prove2.me/theorems/0d16f583-cdb7-5228-ad72-3c0ef97d2ba6
-- title:
--   Central Renyi Reverse
-- statement:
--   Definitions and structural lemmas for Central Renyi Reverse, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat
def reverseLiftNumerator : List ℕ → ℕ
  | [] => 1
  | _k :: ks => 3 * reverseLiftNumerator ks + 2 ^ ks.sum
end FixedTotal
end CollatzEndpointTransport
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat
open Finset
open scoped NNReal
noncomputable section
def normalizedReverseLift (ks : List ℕ) : ℝ≥0 :=
  (reverseLiftNumerator ks : ℝ≥0) / ((2 : ℝ≥0) ^ ks.sum)
def reverseMomentMajorant (theta : ℝ) : List ℕ → ℝ≥0
  | [] => 1
  | k :: ks =>
      (1 + (3 : ℝ≥0) ^ theta * reverseMomentMajorant theta ks) /
        (((2 : ℝ≥0) ^ k) ^ theta)
def reverseMomentTerm (theta : ℝ) (ks : List ℕ) (i : ℕ) : ℝ≥0 :=
  ((3 : ℝ≥0) ^ theta) ^ i /
    (((2 : ℝ≥0) ^ (ks.take (i + 1)).sum) ^ theta)
def reverseMomentSeries (theta : ℝ) (ks : List ℕ) : ℝ≥0 :=
  (∑ i ∈ range ks.length, reverseMomentTerm theta ks i) +
    ((3 : ℝ≥0) ^ theta) ^ ks.length /
      (((2 : ℝ≥0) ^ ks.sum) ^ theta)
end
end FixedTotal
end CollatzEndpointTransport
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section
def centralSeparatorProportion (N s : ℕ) : ℝ :=
  ((s - 1 : ℕ) : ℝ) / (N - 1 : ℕ)
def realReverseMomentTerm
    (theta : ℝ) {N : ℕ} (c : Composition N) (r : ℕ) : ℝ :=
  (((3 : ℝ) ^ theta) ^ (r - 1)) /
    (((2 : ℝ) ^ reverseSpend c r) ^ theta)
def realTerminalPatternTerm (theta : ℝ) (r : ℕ) (d : List ℕ) : ℝ :=
  (((3 : ℝ) ^ theta) ^ (r - 1)) /
    (((2 : ℝ) ^ d.sum) ^ theta)
def realTerminalSpendTerm (theta : ℝ) (r D : ℕ) : ℝ :=
  (((3 : ℝ) ^ theta) ^ (r - 1)) /
    (((2 : ℝ) ^ D) ^ theta)
def fixedReverseTermSum (N s : ℕ) (theta : ℝ) (r : ℕ) : ℝ :=
  ∑ c ∈ fixedSet N s, realReverseMomentTerm theta c r
end
end FixedTotal
end CollatzEndpointTransport
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real
noncomputable section
def centralReverseTailRatio (theta pi : ℝ) : ℝ :=
  (1 - pi) / (2 : ℝ) ^ theta
end
end FixedTotal
end CollatzEndpointTransport
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section
def fixedReverseNonterminalSum
    (N s : ℕ) (theta : ℝ) : ℝ :=
  ∑ r ∈ Ico 1 s, fixedReverseTermSum N s theta r
def realReverseMajorant {N : ℕ} (theta : ℝ) (c : Composition N) : ℝ :=
  (reverseMomentMajorant theta c.blocks.reverse : ℝ)
def fixedReverseMajorantAverage
    (N s : ℕ) (theta : ℝ) : ℝ :=
  (∑ c ∈ fixedSet N s, realReverseMajorant theta c) /
    ((fixedSet N s).card : ℝ)
end
end FixedTotal
end CollatzEndpointTransport
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section
def fixedLengthProbability (N s : ℕ) : ℝ :=
  ((fixedSet N s).card : ℝ) / (2 : ℝ) ^ (N - 1)
end
end FixedTotal
end CollatzEndpointTransport
namespace CollatzEndpointTransport
namespace FixedTotal
open scoped Real
noncomputable section
def InCentralRenyiWindow (N s : ℕ) (eta : ℝ) : Prop :=
  |(s : ℝ) - ((N : ℝ) + 1) / 2| ≤ eta * N
end
end FixedTotal
end CollatzEndpointTransport
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real
noncomputable section
def fixedSourceWeight (N s : ℕ) : ℝ :=
  ((fixedSet N s).card : ℝ) / (2 : ℝ) ^ N
def centralLengthSet (N : ℕ) (eta : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun s => InCentralRenyiWindow N s eta
def centralMomentConstant (theta eta : ℝ) : ℝ :=
  4 * ((3 : ℝ) ^ (-theta) /
      (1 - centralRenyiRatio theta (centralRenyiPiStar theta eta)) + 2)
end
end FixedTotal
end CollatzEndpointTransport


