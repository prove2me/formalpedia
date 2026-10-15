-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle027
-- name    : ThreeSum1960614_Machine_Bundle027
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:12:32.593743+00:00
-- url     : https://prove2.me/theorems/e21fe6d2-c5da-4f95-843d-0d11f46e0610
-- title:
--   Wanted-record decoding, occurrence source banks, and suffix catalogs
-- statement:
--   This bundle connects physical wanted-pair indices to their original combinatorial labels. A valid left index $i<3N$ determines an input position $i\bmod N$ and one of three lifts $\lfloor i/N\rfloor$; the right index identifies an unchanged global output record. Membership in the wanted family is the corresponding exact modular divisibility condition. Stored interleaved pair cells retain both indices, including distinct positions with equal integer keys.
--
--   For natural local scale $h$ and block count $J$, source-bank rows follow the big-endian radix expansion of their physical index. There are $s_h^J$ occurrence rows, where $s_h$ is the local schedule size. The batch and catalog programs construct both retained suffix-source families once per occurrence row and preserve the original-band histograms and cover data. Their stored predicates identify every bank's two source-stage tables and header pointers.
--
--   A suffix catalog is a contiguous family of box tables indexed by actual pairs of prefix masks. Its setup computes its own table stride, and its query host computes the local query mask and lifting factor from a power table. The wanted decoder reads a stored pair, recovers the left position and lift, decodes all output rows, and stores the occurrence-only bank index. Coverage interfaces connect actual emitted pairs back to the guarded wanted labels.
--
--   The shared prefix-key interface represents a length-$k$ prefix as $k$ ordered disjoint balanced row pairs. It constructs the corresponding global left and right masks and source functions for finite source sets and integer-valued inputs. Explicit time and word functions retain the costs of decoding and bank construction.
--
--   These definitions preserve the exact occurrence and output ordering needed to share source banks and suffix tables across reporting queries in the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/WantedRecordOrder.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/BlockSourceOccurrenceOrder.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBlockSourceBatch.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingSuffixBoxes.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingSuffixCatalog.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingSuffixQueryHost.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightWantedDecode.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/WantedRecordCoverage.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBlockSourceBatchProgram.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBlockSourceCatalog.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingSuffixCatalogSetup.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostPrefixCatalog.lean

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightBlockSourceBatch
end ThreeSum.LightBlockSourceBatch
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightBlockSourceBatchProgram
end ThreeSum.LightBlockSourceBatchProgram
namespace ThreeSum.LightBlockSourceCatalog
end ThreeSum.LightBlockSourceCatalog
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixBoxes
end ThreeSum.LightReportingSuffixBoxes
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightReportingSuffixCatalogSetup
end ThreeSum.LightReportingSuffixCatalogSetup
namespace ThreeSum.LightReportingSuffixQueryHost
end ThreeSum.LightReportingSuffixQueryHost
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightWantedDecode
end ThreeSum.LightWantedDecode
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.OutputDecodeOccurrenceCode
end ThreeSum.OutputDecodeOccurrenceCode
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.RawAKeyLists
end ThreeSum.RawAKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostQueryBounds
end ThreeSum.ReportingHostQueryBounds
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.WantedRecordCoverage
end ThreeSum.WantedRecordCoverage
namespace ThreeSum.WantedRecordOrder
end ThreeSum.WantedRecordOrder
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LayerCounts
end ThreeSum1960614.Machine.ThreeSum.LayerCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchProgram
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchProgram
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalogSetup
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalogSetup
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryHost
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryHost
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightWantedDecode
end ThreeSum1960614.Machine.ThreeSum.LightWantedDecode
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
end ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostQueryBounds
end ThreeSum1960614.Machine.ThreeSum.ReportingHostQueryBounds
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.WantedRecordCoverage
end ThreeSum1960614.Machine.ThreeSum.WantedRecordCoverage
namespace ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder
end ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder

namespace ThreeSum1960614.Machine

/-!
# Original wanted labels behind the interleaved pair indices

Left indices recover the A-incidence position and its lift. Right indices
recover the unchanged global output record. The maps retain distinct source
positions even when their integer key values coincide.
-/

namespace ThreeSum.WantedRecordOrder
open _root_.ThreeSum.WantedRecordOrder


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum.RawAKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000







def label {xs : List ℤ} (h J i j : ℕ) (hi : i < 3*xs.length) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (Fin xs.length) :=
  (⟨i%xs.length,Nat.mod_lt _ (_root_.ThreeSum.WantedRecordOrder.input_length_pos hi)⟩,
    (⟨i/xs.length,(Nat.div_lt_iff_lt_mul (_root_.ThreeSum.WantedRecordOrder.input_length_pos hi)).mpr hi⟩,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.output h J j))

theorem mem_wanted_iff {M h J i j : ℕ} {P shift : ℤ} {xs : List ℤ}
    (hi : i < 3*xs.length) (hj : j < _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.label h J i j hi ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.wanted M P xs h J shift ↔
      (M : ℤ) ∣ (_root_.ThreeSum.RawAKeyLists.keys P xs).getD i 0+shift-(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalKeys h J).getD j 0 := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.mem_wanted,_root_.ThreeSum.WantedRecordOrder.key_getD hi,
    _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.original_global_key (show j < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J from hj)]
  rfl







theorem segment_pair {μ : ℕ → ℤ} {base k : ℕ} {ps : List (ℕ × ℕ)}
    (H : _root_.ThreeSum1960614.Machine.Light.Seg μ base (_root_.ThreeSum.WantedPairs.cells ps)) (hk : k < ps.length) :
    μ (base+2*k)=((ps.getD k (0,0)).1 : ℤ) ∧
      μ (base+2*k+1)=((ps.getD k (0,0)).2 : ℤ) := by
  have h0 : 2*k < (_root_.ThreeSum.WantedPairs.cells ps).length := by rw [_root_.ThreeSum.WantedPairs.cells_length]; omega
  have h1 : 2*k+1 < (_root_.ThreeSum.WantedPairs.cells ps).length := by rw [_root_.ThreeSum.WantedPairs.cells_length]; omega
  constructor
  · rw [← _root_.ThreeSum.WantedRecordOrder.cells_getD_left, List.getD_eq_getElem _ _ h0]
    exact H _ h0
  · rw [← _root_.ThreeSum.WantedRecordOrder.cells_getD_right,List.getD_eq_getElem _ _ h1, Nat.add_assoc]
    exact H _ h1

end ThreeSum.WantedRecordOrder

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact source-bank order and reuse by decoded global outputs

A source-bank row is the big-endian radix expansion of its physical index.
Its representative carries a fixed legal output subset solely to reuse the
original source definitions. No output-subset choice enters the stored row
or the source function. The actual global-output decoder supplies exactly
the bank index needed by a query.
-/

namespace ThreeSum.BlockSourceOccurrenceOrder
open _root_.ThreeSum.BlockSourceOccurrenceOrder


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum.OutputDecodeOccurrenceCode
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration

def occurrences (h J k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J := fun j =>
  ⟨(_root_.ThreeSum.OutputDecodeOrder.indices (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) J k).getD j.val 0,_root_.ThreeSum.OutputDecodeOrder.indices_getD_lt (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.schedule_pos h) j.isLt⟩

def representative (h J k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J :=
  fun j => (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.occurrences h J k j,(_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.blockDefault h).2)











end ThreeSum.BlockSourceOccurrenceOrder

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual shared source-stage catalog over occurrence vectors

One loop iteration constructs one retained bank and its two header pointers.
The original-band histograms and local-cover data are read throughout and
preserved. The semantic occurrence-row contract labels an ordinary physical
array; it does not assume any source-stage computation or output-subset loop.
-/

namespace ThreeSum.LightBlockSourceBatch
open _root_.ThreeSum.LightBlockSourceBatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

structure BankAt {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J : ℕ} (μ : ℕ → ℤ) (base count cut i : ℕ) (P shift : ℤ)
    (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) : Prop where
  left : _root_.ThreeSum.LightZetaStages.StoredThrough μ (_root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count (J*(464*h)) cut i) cut
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource P B b q) (J*(464*h))
  right : _root_.ThreeSum.LightZetaStages.StoredThrough μ (_root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count (J*(464*h)) cut i) cut
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource P shift A a q) (J*(464*h))
  headerLeft : μ (base+2*i) = (_root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count (J*(464*h)) cut i : ℤ)
  headerRight : μ (base+2*i+1) = (_root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count (J*(464*h)) cut i : ℤ)





def body (pStep : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 23 (_root_.ThreeSum1960614.Machine.Light.v 16) (
    _root_.ThreeSum1960614.Machine.Light.Stmt.call pStep [_root_.ThreeSum1960614.Machine.Light.v 0,_root_.ThreeSum1960614.Machine.Light.v 1,_root_.ThreeSum1960614.Machine.Light.v 2,_root_.ThreeSum1960614.Machine.Light.v 3,_root_.ThreeSum1960614.Machine.Light.v 4,_root_.ThreeSum1960614.Machine.Light.v 5,_root_.ThreeSum1960614.Machine.Light.v 6,((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 23) (_root_.ThreeSum1960614.Machine.Light.v 0))),
      _root_.ThreeSum1960614.Machine.Light.v 8,_root_.ThreeSum1960614.Machine.Light.v 9,_root_.ThreeSum1960614.Machine.Light.v 10,_root_.ThreeSum1960614.Machine.Light.v 11,_root_.ThreeSum1960614.Machine.Light.v 12,_root_.ThreeSum1960614.Machine.Light.v 13,_root_.ThreeSum1960614.Machine.Light.v 14,_root_.ThreeSum1960614.Machine.Light.v 15,_root_.ThreeSum1960614.Machine.Light.v 16,_root_.ThreeSum1960614.Machine.Light.v 17,_root_.ThreeSum1960614.Machine.Light.v 18,_root_.ThreeSum1960614.Machine.Light.v 19,_root_.ThreeSum1960614.Machine.Light.v 20,_root_.ThreeSum1960614.Machine.Light.v 21,_root_.ThreeSum1960614.Machine.Light.v 22,_root_.ThreeSum1960614.Machine.Light.v 23] 24)

def time (count h J cut : ℕ) : ℕ := count*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.time h J cut+200)+20

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pStep : ℕ
  step : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.Procs P pStep
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.body pStep)

def Inv {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (μ : ℕ → ℤ) (h J cut occ maps candidates histL histR sourceHistL sourceHistR base count : ℕ)
    (p shift : ℤ) (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ)
    (q : ℕ → _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [J,464*h,h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h,cut,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,occ,maps,candidates,
      histL,histR,sourceHistL,sourceHistR,base,_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut,count,
      _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count,_root_.ThreeSum.LightBlockSourceBatchLayout.stride (J*(464*h)) cut,_root_.ThreeSum.LightBlockSourceBatchLayout.maskBase base count (J*(464*h)) cut,
      _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase base count (J*(464*h)) cut,_root_.ThreeSum.LightBlockSourceBatchLayout.rowOut base count (J*(464*h)) cut,
      _root_.ThreeSum.LightBlockSourceBatchLayout.work base count (J*(464*h)) cut,i,r],ν⟩ ∧
    (∀ j < i, _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.BankAt ν base count cut j p shift B b A a (q j)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν base

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightBlockSourceBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual shrinking-suffix box preprocessing for an original valid block prefix -/

namespace ThreeSum.LightReportingSuffixBoxes
open _root_.ThreeSum.LightReportingSuffixBoxes


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

def localLeaf {h J k : ℕ} (hk : k ≤ J) (pMod shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) : Finset (Fin (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)) → ℤ :=
  _root_.ThreeSum.ReportingHostSuffix.leafWeight (_root_.ThreeSum.ReportingHostSuffix.block_fit hk) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource pMod B b q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource pMod shift C c q)
    (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))
    (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))





end ThreeSum.LightReportingSuffixBoxes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual construction of a contiguous suffix-box catalog

Each input record is a physical pair of global prefix masks. The host invokes
complete suffix-local setup for every record, writes the corresponding table
pointer, and retains every previous table. The table stride is the exact
local-width storage size; the following setup host computes it explicitly.
-/

namespace ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum.ReportingHostQueryBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostQueryBounds

set_option maxHeartbeats 1800000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



def roundBody (pSetup : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 19 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.v 18)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 20 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.v 18)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 21 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 18) (_root_.ThreeSum1960614.Machine.Light.v 15)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSetup [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17] 22) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.v 18)) (_root_.ThreeSum1960614.Machine.Light.v 21))))))

def body (pSetup : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt := _root_.ThreeSum1960614.Machine.Light.Stmt.for 18 (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog.roundBody pSetup)

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog.body 29]



def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (preL preR : ℕ → Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (cut boxCut stage cL cR baseL baseR inL inR n ptrBase boxBase maskBase work j : ℕ)
    (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (a b addr r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [W,cut,boxCut,stage,cL,cR,V,offset,baseL,baseR,inL,inR,n,
      ptrBase,boxBase,_root_.ThreeSum.LightReportingSuffixCatalog.stride V boxCut,maskBase,work,j,a,b,addr,r],μ'⟩ ∧
    (∀ i < j, μ' (ptrBase+i) = (boxBase+i*_root_.ThreeSum.LightReportingSuffixCatalog.stride V boxCut : ℤ)) ∧
    (∀ i < j, _root_.ThreeSum.LightBoxStages.StoredThrough μ' (boxBase+i*_root_.ThreeSum.LightReportingSuffixCatalog.stride V boxCut) boxCut
      (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage (preL i) (preR i)) V) ∧
    _root_.ThreeSum1960614.Machine.Light.Kept μ μ' ptrBase





end ThreeSum.LightReportingSuffixCatalog

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Complete suffix-local querying from the physical global query mask

The host computes the local query mask by a bounded bit scan, reads the
lifting factor from its own power table, and executes the complete local-box
sparse query. No local-mask conversion or power table is supplied by a caller.
-/

namespace ThreeSum.LightReportingSuffixQueryHost
open _root_.ThreeSum.LightReportingSuffixQueryHost


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

def body (pLower pQuery : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLower [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 17] 18) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 19 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 17) (_root_.ThreeSum1960614.Machine.Light.v 8)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pQuery [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17] 0)))

def suffix : _root_.ThreeSum1960614.Machine.Light.Program := [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixLower.body 17 20,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryHost.body 29 28]
def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.program ++ _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryHost.suffix






end ThreeSum.LightReportingSuffixQueryHost

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Decode an actual emitted wanted-pair cell

The host loads the two physical indices, splits the left index into its
incidence position and lift, and decodes the right index into the original
occurrence and Q-mask rows. Its four-cell header retains both source labels
and the occurrence-only bank index. Division is the verified binary routine.
-/

namespace ThreeSum.LightWantedDecode
open _root_.ThreeSum.LightWantedDecode


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

/-- Pair array, pair slot, incidence count, block count, schedule count,
layer count, retained layer masks, destination, and scratch pointer. -/
def body (pDivide pDecode : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 1))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDivide [_root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 8] 11) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 9) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.v 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDecode [_root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.k 4), _root_.ThreeSum1960614.Machine.Light.v 8] 13) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 12)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 11)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.v 10)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.k 3)) (_root_.ThreeSum1960614.Machine.Light.v 13)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 13)))))))))))



def word (V N h J : ℕ) : ℕ :=
  _root_.ThreeSum.LightOutputDecode.word V (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J (2^(464*h))+
    4*V+4*N+32





structure Stored (ν : ℕ → ℤ) (dst N h J i j : ℕ) : Prop where
  position : ν dst=((i%N : ℕ) : ℤ)
  liftIndex : ν (dst+1)=((i/N : ℕ) : ℤ)
  outputIndex : ν (dst+2)=(j : ℤ)
  bankIndex : ν (dst+3)=(_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j : ℤ)
  rows : _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.Rows ν (dst+4) h J j

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {pairs slot N h J masks dst work i j V : ℕ}



def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.body 3 0]







end ThreeSum.LightWantedDecode

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Completeness of the physical wanted-record array

The pair array produced by the selected-offset join covers every original
guarded wanted label. Conversely every stored pair selects such a label.
These statements concern the actual emitted array, including duplicate
integer keys at different source positions.
-/

namespace ThreeSum.WantedRecordCoverage
open _root_.ThreeSum.WantedRecordCoverage


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.WantedRecordOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000



theorem output_pair {μ : ℕ → ℤ} {free M P h J slot : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free M (_root_.ThreeSum.LightGuardedWanted.left P xs)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J) (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) shift)
    (hk : slot < (μ free).toNat) :
    ∃ i j, ∃ hi : i < 3*xs.length,
      j < _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J ∧
      μ (_root_.ThreeSum.LightWantedSetup.pairBase free (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) M+2*slot)=(i : ℤ) ∧
      μ (_root_.ThreeSum.LightWantedSetup.pairBase free (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) M+2*slot+1)=(j : ℤ) ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.label h J i j hi ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.wanted M P xs h J shift := by
  rcases H with ⟨hcount,_,_,_,ps,hlen,_,hmem,hseg⟩
  have hk' : slot < ps.length := by rw [hlen]; simpa only [hcount,Int.toNat_natCast] using hk
  let p := ps.getD slot (0,0)
  have hp : p ∈ ps := by
    rw [show p=ps[slot] from List.getD_eq_getElem _ _ hk']
    exact List.getElem_mem hk'
  have hb := (hmem p.1 p.2).mp hp
  have hread := _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.segment_pair hseg hk'
  refine ⟨p.1,p.2,hb.1,hb.2.1,hread.1,hread.2,?_⟩
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.mem_wanted_iff hb.1 hb.2.1).mpr hb.2.2



end ThreeSum.WantedRecordCoverage

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Closed actual source-bank catalog program

The existing 41-procedure library is retained unchanged. Two host procedures
are appended with their actual call indices, giving a fixed 43-procedure
program. The table contains no source-function oracle and no Q enumeration.
-/

namespace ThreeSum.LightBlockSourceBatchProgram
open _root_.ThreeSum.LightBlockSourceBatchProgram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram.program ++
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.body 0,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.body 41]









end ThreeSum.LightBlockSourceBatchProgram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructed occurrence rows and their shared source banks

The first call constructs every big-endian occurrence row from its physical
bank index. The second call builds the two retained original source-stage
families once for that row. Original-band histograms and selected cover data
remain available throughout. No array of complete output records is read.
-/

namespace ThreeSum.LightBlockSourceCatalog
open _root_.ThreeSum.LightBlockSourceCatalog


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

def count (h J : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h^J

def body (pRows pBatch : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pRows [_root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 22] 24) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBatch [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 22] 24))

def time (h J cut : ℕ) : ℕ :=
  _root_.ThreeSum.LightSourceOccurrenceArray.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) J+
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) h J cut+400





structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pRows : ℕ
  pDigits : ℕ
  pDivide : ℕ
  pBatch : ℕ
  rows : P[pRows]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceOccurrenceArray.body pDigits)
  digits : P[pDigits]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits.body pDivide)
  divide : P[pDivide]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.body
  batch : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.Procs P pBatch
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.body pRows pBatch)

def Stored {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (μ : ℕ → ℤ) (h J base cut : ℕ) (P shift : ℤ)
    (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ) : Prop :=
  ∀ i < _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J, _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.BankAt μ base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) cut i P shift B b A a
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J i)



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightBlockSourceCatalog

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Suffix catalog construction computes its own physical table stride -/

namespace ThreeSum.LightReportingSuffixCatalogSetup
open _root_.ThreeSum.LightReportingSuffixCatalogSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

def body (pSize pCatalog : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSize [_root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 16] 17) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 17))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCatalog [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16] 0)))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalogSetup.body 9 30]







end ThreeSum.LightReportingSuffixCatalogSetup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact prefix catalog keys and sharing for fixed source occurrences

A catalog key consists only of the first k ordered disjoint balanced row
pairs. Its exact cardinality is (microOutputs*microPartitions)^k. Neither the
remaining output rows nor the wanted A-index enter a local box table once
the global occurrence vector is fixed.
-/

namespace ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum.ReportingHostPrefixCatalog


open _root_.Finset
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LayerCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.LayerCounts
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

set_option linter.unusedSectionVars false

abbrev Prefix (h k : ℕ) := Fin k → _root_.ThreeSum.LocalGraph.Edge (464*h) h



def leftRows {h J k : ℕ} (p : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) : Fin J → Finset (Fin (464*h)) :=
  fun i => if hi : i.val < k then (p ⟨i.val,hi⟩).val.1 else ∅

def rightRows {h J k : ℕ} (p : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) : Fin J → Finset (Fin (464*h)) :=
  fun i => if hi : i.val < k then (p ⟨i.val,hi⟩).val.2 else ∅

def leftSet {h J k : ℕ} (p : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) : Finset (Fin (J*(464*h))) :=
  _root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftRows p)

def rightSet {h J k : ℕ} (p : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) : Finset (Fin (J*(464*h))) :=
  _root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightRows p)





def ofValidPrefix {h J k : ℕ} (hk : k ≤ J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix q k pre) : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k :=
  fun i =>
    let j : Fin J := ⟨i.val,i.isLt.trans_le hk⟩
    ⟨(_root_.ThreeSum.StoredReporting.prefixRows pre j,_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q j \ _root_.ThreeSum.StoredReporting.prefixRows pre j),by
      have hu := hp.2 j i.isLt
      have hQ : (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q j).card = 2*h := _root_.ThreeSum.LayerCounts.mem_vertices.mp (q j).2.property
      apply _root_.ThreeSum.LayerCounts.mem_edgeSet.mpr
      refine ⟨hu.2,?_,disjoint_sdiff_self_right⟩
      rw [Finset.card_sdiff_of_subset hu.1,hQ,hu.2]
      omega⟩





section Sources

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

def leftSourceOf {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (P : ℤ) (B : Finset β) (b : β → ℤ) :
    Finset (Fin (J*(464*h))) → ℤ :=
  _root_.ThreeSum.SubsetTransport.reindex (_root_.ThreeSum.BlockIndex.coordEquiv J (464*h)) (fun S => (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights o P B b S : ℤ))

def rightSourceOf {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (P shift : ℤ) (C : Finset γ) (c : γ → ℤ) :
    Finset (Fin (J*(464*h))) → ℤ :=
  _root_.ThreeSum.SubsetTransport.reindex (_root_.ThreeSum.BlockIndex.coordEquiv J (464*h)) (fun S => (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights o P shift C c S : ℤ))















end Sources

end ThreeSum.ReportingHostPrefixCatalog

end ThreeSum1960614.Machine


