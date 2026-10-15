-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle016
-- name    : ThreeSum1960614_Machine_Bundle016
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:39:29.526434+00:00
-- url     : https://prove2.me/theorems/a9e08bf1-95ae-407d-a70d-f5cba86ca1fb
-- title:
--   Concrete global key arrays, local parameters, and compact enumeration programs
-- statement:
--   This bundle connects literal memory arrays to the combinatorial block encoding. For natural local scale $h$ and block count $J$, local output records enumerate every schedule occurrence together with every $2h$-subset of $464h$ coordinates. Global records are their length-$J$ Cartesian tuples. If $s_h$ is the local schedule length and $c_h=\binom{464h}{2h}$, their exact count is
--   $$|\mathcal R_{h,J}|=s_h^Jc_h^J.$$
--   The global integer-key list is exactly the list obtained by applying the positional encoding to these records, retaining separate incidences even when their integer keys coincide. Compact source-array indices are transported to the same block-coordinate system.
--
--   For an input size $n\in\mathbb N$ and real constants $C,B$, the hierarchy envelope is $(\mu(n)+1)\exp(\mu(n)(\log2)C+B)$, where $\mu(n)$ is the executable inner size. The initial hierarchy cap is the ceiling of $40409899r/10^9$ at natural depth parameter $r$.
--
--   The finite Light programs build the three sorted-band owner tables, pack physical block masks into global row-major masks, construct both raw endpoint-hash arrays from selected maps, and generate the color of every original input position. Other programs decode a coloring-parameter slot, enumerate successive compact downset layers, construct raw hashes, residue codes and histograms, compute signed local output-key rows, and expand masks into Boolean coordinate rows. Local parameter initialization constructs the graph counts, selects the deterministic prime, and computes the separable bucket cap; explicit functions record time, space, and word requirements. Procedure-table structures identify all called bodies.
--
--   Loop invariants specify the completed array prefixes, shared power tables, and cells preserved outside output and scratch. These interfaces connect actual enumerations and stored coefficients to the hash, hierarchy, and coloring quantities charged in the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/BlockSourceTableLayout.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/GlobalKeyEnumeration.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/HierarchyScales.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandEnumeration.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBlockMasks.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBlockSourceHashes.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightColorArray.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightColorParameters.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightDownsetEnumeration.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightHashHistogram.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLocalKeyRow.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLocalParameters.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightMaskBitTable.lean

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
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
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
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
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
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
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
import Mathlib.Tactic.IntervalCases
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

namespace Filter
end Filter
namespace Light
end Light
namespace Real
end Real
namespace Set
end Set
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceTableLayout
end ThreeSum.BlockSourceTableLayout
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.HierarchyScales
end ThreeSum.HierarchyScales
namespace ThreeSum.LightBandEnumeration
end ThreeSum.LightBandEnumeration
namespace ThreeSum.LightBlockMasks
end ThreeSum.LightBlockMasks
namespace ThreeSum.LightBlockSourceHashes
end ThreeSum.LightBlockSourceHashes
namespace ThreeSum.LightColorArray
end ThreeSum.LightColorArray
namespace ThreeSum.LightColorParameters
end ThreeSum.LightColorParameters
namespace ThreeSum.LightDownsetEnumeration
end ThreeSum.LightDownsetEnumeration
namespace ThreeSum.LightHashHistogram
end ThreeSum.LightHashHistogram
namespace ThreeSum.LightLocalKeyRow
end ThreeSum.LightLocalKeyRow
namespace ThreeSum.LightLocalParameters
end ThreeSum.LightLocalParameters
namespace ThreeSum.LightMaskBitTable
end ThreeSum.LightMaskBitTable
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
end ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceTableLayout
end ThreeSum1960614.Machine.ThreeSum.BlockSourceTableLayout
namespace ThreeSum1960614.Machine.ThreeSum.ColorParameters
end ThreeSum1960614.Machine.ThreeSum.ColorParameters
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.HierarchyScales
end ThreeSum1960614.Machine.ThreeSum.HierarchyScales
namespace ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockMasks
end ThreeSum1960614.Machine.ThreeSum.LightBlockMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes
namespace ThreeSum1960614.Machine.ThreeSum.LightColorArray
end ThreeSum1960614.Machine.ThreeSum.LightColorArray
namespace ThreeSum1960614.Machine.ThreeSum.LightColorParameters
end ThreeSum1960614.Machine.ThreeSum.LightColorParameters
namespace ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightHashHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHashHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalKeyRow
end ThreeSum1960614.Machine.ThreeSum.LightLocalKeyRow
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalParameters
end ThreeSum1960614.Machine.ThreeSum.LightLocalParameters
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskBitTable
end ThreeSum1960614.Machine.ThreeSum.LightMaskBitTable
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch

namespace ThreeSum1960614.Machine

/-! # Compact source arrays in the unchanged block-query coordinate system -/

namespace ThreeSum.BlockSourceTableLayout
open _root_.ThreeSum.BlockSourceTableLayout


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding

def sets (h J cut i : ℕ) : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h)) :=
  _root_.ThreeSum.BlockIndex.unindexSet (_root_.ThreeSum.SourceTableLayout.setAt (J*(464*h)) cut i)









end ThreeSum.BlockSourceTableLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Literal global-output records behind the radix key array

Local records use the verified layer enumerator's order and retain every
schedule occurrence. Cartesian extension enumerates each original global
output once. Mapping to integers may introduce equal values; the key array
retains all of those separate incidences.
-/

namespace ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.GlobalKeyEnumeration


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.RadixKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000

def layerRecord (h : ℕ) (i : Fin ((464*h).choose (2*h))) :
    {Q // Q ∈ _root_.ThreeSum.LayerCounts.vertices (464*h) (2*h)} :=
  ⟨_root_.ThreeSum.LocalMaskGraph.setAt (464*h) (2*h) i,
    _root_.ThreeSum.LayerCounts.mem_vertices.mpr (_root_.ThreeSum.LocalMaskGraph.setAt_card i.isLt)⟩





def layers (h : ℕ) := List.ofFn (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layerRecord h)

theorem layers_length (h : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layers h).length=_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layers,_root_.ThreeSum.LocalCoverBounds.outputCount]





def localRecords (h : ℕ) : List (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.OutputBlock h) :=
  (List.finRange (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)).product (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layers h)

theorem localRecords_length (h : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localRecords h).length=_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h := by
  calc
    _ = (List.finRange (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)).length*(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layers h).length :=
      List.length_product _ _
    _ = _ := by rw [List.length_finRange,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layers_length]





def localKeys (h : ℕ) : List ℤ := (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localRecords h).map _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockKey





def globalRecords (h J : ℕ) : List (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) :=
  (_root_.ThreeSum.RadixKeyLists.tuples (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localRecords h) J).attach.map fun xs =>
    _root_.ThreeSum.GlobalKeyEnumeration.tupleOfList xs.val ((_root_.ThreeSum.RadixKeyLists.mem_tuples _ _ _).mp xs.property).1

theorem globalRecords_length (h J : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).length=_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h^J*_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h^J := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords,_root_.ThreeSum.RadixKeyLists.tuples_length,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localRecords_length,mul_pow]





def globalKeys (h J : ℕ) : List ℤ :=
  _root_.ThreeSum.RadixKeyLists.values (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localKeys h) J

/-- Exact array identity, not merely equality of the set of key values. -/
theorem globalKeys_eq_map (h J : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalKeys h J=(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).map _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalKeys,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localKeys,_root_.ThreeSum.RadixKeyLists.values_eq_map]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords
  rw [List.map_map]
  symm
  calc
    _ = (_root_.ThreeSum.RadixKeyLists.tuples (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localRecords h) J).attach.map
        (fun xs => _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockKey xs.val) := by
      apply List.map_congr_left
      intro xs _
      simp only [Function.comp_def,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey,_root_.ThreeSum.GlobalKeyEnumeration.ofFn_tupleOfList]
    _ = _ := by simp









end ThreeSum.GlobalKeyEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Finite sums and asymptotic bounds for the actual hierarchy

The finite box and query counts are summed over the executable depth range.
The only envelopes introduced here are explicit elementary functions of the
already constructed integer `mu`; all growth rates are proved from Scales.
-/

namespace ThreeSum.HierarchyScales
open _root_.ThreeSum.HierarchyScales


open _root_.Filter
open _root_.Set
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Switch
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open scoped _root_.Topology
open scoped _root_.BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def initialCap (r : ℕ) : ℕ := (40409899*r) ⌈/⌉ 1000000000













noncomputable section

def hierarchyEnvelope (C B : ℝ) (n : ℕ) : ℝ :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n + 1 : ℝ) * Real.exp ((_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) * Real.log 2 * C + B)































def unroundedBandCount (n : ℕ) : ℝ := (n : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n













end
end ThreeSum.HierarchyScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A closed machine program listing all relevant sorted-band candidates

The program computes its own binary width and power table, then executes
exactly the three rectangular owner tables. Every table cell contains an
interval lookup result (index plus one, zero for a miss). The source arrays
remain intact. The coverage theorem below connects these actual memory cells
to every relevant triple, and hence to every exact equation in the bands.
-/

namespace ThreeSum.LightBandEnumeration
open _root_.ThreeSum.LightBandEnumeration


set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

def At (μ : ℕ → ℤ) (lo hi : ℕ) (A : _root_.ThreeSum.BandEnumeration.Family) : Prop :=
  (∀ i < A.size, μ (lo+i) = A.lower i) ∧
  (∀ i < A.size, μ (hi+i) = A.upper i)










def Tables (μ : ℕ → ℤ) (dst : ℕ) (A B C : _root_.ThreeSum.BandEnumeration.Family) : Prop :=
  (∀ j < B.size, ∀ k < C.size,
    μ (dst+j*C.size+k) =
      (_root_.ThreeSum.LightBandLookup.result A.lower A.upper A.size (C.lower k-B.upper j) : ℤ)) ∧
  (∀ i < A.size, ∀ j < B.size,
    μ (dst+B.size*C.size+i*B.size+j) =
      (_root_.ThreeSum.LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j) : ℤ)) ∧
  (∀ i < A.size, ∀ k < C.size,
    μ (dst+B.size*C.size+A.size*B.size+i*C.size+k) =
      (_root_.ThreeSum.LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i) : ℤ))

/-- Arguments: six endpoint pointers, three band counts, output base. -/
def body (pClog pPowers pTable : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 7)) (_root_.ThreeSum1960614.Machine.Light.v 8))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 8))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 7))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 8))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.v 11))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.v 12))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 15) (_root_.ThreeSum1960614.Machine.Light.v 13))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pClog [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 1)] 17) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 16, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 17) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.k 2] 18) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pTable [_root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.k 1)] 18) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pTable [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.k 1] 18) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pTable [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.k 1)] 18) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.v 12)) (_root_.ThreeSum1960614.Machine.Light.v 13)))))))))))))))



structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pClog : ℕ
  pPowers : ℕ
  pTable : ℕ
  pRow : ℕ
  pLookup : ℕ
  pSearch : ℕ
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.body pClog pPowers pTable)
  clog : P[pClog]? = some _root_.ThreeSum1960614.Machine.Light.clog2Body
  powers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody
  table : P[pTable]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.body pRow)
  row : P[pRow]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.rowBody pLookup)
  lookup : P[pLookup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.body pSearch)
  search : P[pSearch]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.searchBody pSearch)































end ThreeSum.LightBandEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Packing physical block masks into global row-major coordinates

The fixed program builds a power table, scales every input row mask by its
block position, writes the global row masks, and returns their union mask.
Only linear scans and polynomial scratch are used.
-/

namespace ThreeSum.LightBlockMasks
open _root_.ThreeSum.LightBlockMasks


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

def roundBody : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 9))) (_root_.ThreeSum1960614.Machine.Light.v 7))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 9)) (_root_.ThreeSum1960614.Machine.Light.v 10)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 10))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 6))))))

def nonemptyBody (pPowers : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 4, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.k 2] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 9 (_root_.ThreeSum1960614.Machine.Light.v 0) _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.roundBody) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 8)))))))

/-- Block count, row width, physical input masks, packed-mask output, scratch. -/
def body (pPowers : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 0))) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.nonemptyBody pPowers) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))



def Inv {J L : ℕ} (μ : ℕ → ℤ) (rows : Fin J → Finset (Fin L))
    (src dst work : ℕ) (powRet : ℤ) (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [J,L,src,dst,work,powRet,2^L,2^(j*L),_root_.ThreeSum.BlockMaskLayout.prefixMask rows j,j,r],μ'⟩ ∧
    _root_.ThreeSum1960614.Machine.Light.SegN μ' dst ((_root_.ThreeSum.BlockMaskLayout.packedMasks rows).take j) ∧ _root_.ThreeSum.LightSubsetAddress.Powers μ' work L ∧
    _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst J



def program : _root_.ThreeSum1960614.Machine.Light.Program := [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.body 1,_root_.ThreeSum1960614.Machine.Light.powTableBody]





end ThreeSum.LightBlockMasks

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing both raw endpoint arrays from selected block maps

The program constructs radix-weighted coefficient rows itself, then hashes
each stored subset in both orientations. Both endpoint arrays and the
coefficient rows are retained. The final specialization identifies the
results with the original block encoding, preserving occurrence indices.
-/

namespace ThreeSum.LightBlockSourceHashes
open _root_.ThreeSum.LightBlockSourceHashes


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

/-- Arguments: J, L, radix, occurrences, maps, coefficient-zero,
coefficient-one, masks, left output, right output, mask count, scratch. -/
def body (pCoefficients pHashes : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCoefficients [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 11] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHashes [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 1), _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 11] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHashes [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 1), _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 11] 12)))







structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pCoefficients : ℕ
  pPowers : ℕ
  pScale : ℕ
  pHashes : ℕ
  pOneHot : ℕ
  coefficients : P[pCoefficients]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.body pPowers pScale)
  powers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody
  scale : P[pScale]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightScaleArray.body
  hashes : P[pHashes]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskHashes.body pPowers pOneHot)
  onehot : P[pOneHot]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOneHot.body pOneHot)
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes.body pCoefficients pHashes)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











end ThreeSum.LightBlockSourceHashes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Building the color of every original array position

The program constructs its own binary-power table and evaluates one selected
two-coordinate coloring on every index. No index-bit or coloring oracle is
part of the input. Memory outside the output colors and scratch is preserved.
-/

namespace ThreeSum.LightColorArray
open _root_.ThreeSum.LightColorArray


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

set_option maxHeartbeats 1200000

def body (pPowers pColor : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 9, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.k 2] 10) (_root_.ThreeSum1960614.Machine.Light.Stmt.for 11 (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pColor [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 9] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 11)) (_root_.ThreeSum1960614.Machine.Light.v 12)))))



def Inv {W : ℕ} (μ : ℕ → ℤ) (p : _root_.ThreeSum.Coloring.Parameter W)
    (n dst work : ℕ) (powRet : ℤ) (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [W,n,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      dst,work,powRet,j,r],ν⟩ ∧
    (∀ i < j, ν (dst+i) = (_root_.ThreeSum.LightColorIndex.color p i : ℤ)) ∧
    _root_.ThreeSum.LightSubsetAddress.Powers ν work W ∧ _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν work dst n

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightColorArray

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Execute one coloring-parameter slot

Five exact scalar divisions recover the two binary coordinates and four
ternary colors. Only six output cells are written, so the outer color loop
can reuse this record. The complete family has only polynomially many slots
in the binary index width.
-/

namespace ThreeSum.LightColorParameters
open _root_.ThreeSum.LightColorParameters


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters

set_option maxHeartbeats 1600000
set_option maxRecDepth 9000

def body (pDivide : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDivide [_root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.k 3] 3) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDivide [_root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.k 3] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDivide [_root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.k 3] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDivide [_root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.k 3] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDivide [_root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 0] 7) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 6) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 0)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 5) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 4) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 1) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 7)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 8)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.v 9)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 3)) (_root_.ThreeSum1960614.Machine.Light.v 10)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 4)) (_root_.ThreeSum1960614.Machine.Light.v 11)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 5)) (_root_.ThreeSum1960614.Machine.Light.v 12)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 2))))))))))))))))))





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d W t free : ℕ} {μ : ℕ → ℤ}









end ThreeSum.LightColorParameters

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Sequential enumeration of a compact downset

This routine invokes the guarded layer enumerator for the successive
cardinalities. Each layer starts immediately after the preceding layer;
the only traversal besides the emitted masks is polynomial in the bit
width. All power-table reads are shared across the layer calls.
-/

namespace ThreeSum.LightDownsetEnumeration
open _root_.ThreeSum.LightDownsetEnumeration


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}













def roundBody (pEnum : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEnum [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.k 0, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 5), _root_.ThreeSum1960614.Machine.Light.v 3] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 6))))

def body (pEnum : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 4 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.roundBody pEnum)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 5))))



def Inv (μ : ℕ → ℤ) (L cut dst powers j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [L,cut,dst,powers,j,_root_.ThreeSum.SubsetAddress.layerOffset L j,r],μ'⟩ ∧
    _root_.ThreeSum1960614.Machine.Light.SegN μ' dst (_root_.ThreeSum.LightDownsetEnumeration.layers L j) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (_root_.ThreeSum.SubsetAddress.layerOffset L j)









end ThreeSum.LightDownsetEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# One-hot mask hashes through actual residues and bucket counts

The complete wrapper constructs raw hashes, canonical residue codes, and
the histogram. Both code and histogram arrays are retained for the later
pair-trimming pass; every earlier input cell is preserved.
-/

namespace ThreeSum.LightHashHistogram
open _root_.ThreeSum.LightHashHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light



def body (pHashes pResidues pHist : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHashes [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 9] 10) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pResidues [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.k 1] 10) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHist [_root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 8] 10)))







structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pHashes : ℕ
  pPowers : ℕ
  pOneHot : ℕ
  pResidues : ℕ
  pEmod : ℕ
  pHist : ℕ
  pFill : ℕ
  hashes : P[pHashes]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskHashes.body pPowers pOneHot)
  powers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody
  onehot : P[pOneHot]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOneHot.body pOneHot)
  residues : P[pResidues]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residuesBody pEmod)
  emod : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody
  hist : P[pHist]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogramBody pFill)
  fill : P[pFill]? = some _root_.ThreeSum1960614.Machine.Light.fillBody
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightHashHistogram.body pHashes pResidues pHist)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightHashHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Computing one complete row of signed local output keys

For every stored output mask, this fixed program sums the true and false
coefficients outside that mask and subtracts the two sums. It constructs
its own zero row and powers table. Both input coefficient rows and the
literal output-mask enumeration remain intact.
-/

namespace ThreeSum.LightLocalKeyRow
open _root_.ThreeSum.LightLocalKeyRow


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

/-- Width, masks, mask count, false coefficients, true coefficients, free. -/
def body (pFill pHashes pLinear : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 0))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 2))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 2))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pFill [_root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.k 0] 9) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHashes [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 8] 9) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHashes [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 8] 9) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLinear [_root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 2, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.k 1)] 9) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 6)))))))))





structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pFill : ℕ
  pHashes : ℕ
  pPowers : ℕ
  pHash : ℕ
  pLinear : ℕ
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalKeyRow.body pFill pHashes pLinear)
  fill : P[pFill]? = some _root_.ThreeSum1960614.Machine.Light.fillBody
  hashes : P[pHashes]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskHashes.body pPowers pHash)
  powers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody
  hash : P[pHash]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOneHot.body pHash)
  linear : P[pLinear]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linearBody

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightLocalKeyRow

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Complete local integer parameter initialization

From the microblock half-size this program constructs the graph counts,
selects the deterministic prime, and computes the exact separable bucket
cap. The first six output cells are the graph counts; the next two contain
the prime and cap. Scratch may be reused by every stage.
-/

namespace ThreeSum.LightLocalParameters
open _root_.ThreeSum.LightLocalParameters


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

def numerator (h : ℕ) : ℕ :=
  4*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+_root_.ThreeSum.LocalCoverBounds.vertexCount (464*h) h)+_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h-1

def values (h : ℕ) : List ℤ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values h ++ [(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ),_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h]

def body (pCounts pPrime pDiv : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCounts [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2] 3) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPrime [_root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 2] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 4) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 5))) (_root_.ThreeSum1960614.Machine.Light.v 4)) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDiv [_root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 4] 7) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 6)) (_root_.ThreeSum1960614.Machine.Light.v 4)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 7)) (_root_.ThreeSum1960614.Machine.Light.v 7)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 4)))))))))

def time (h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.time h+
  _root_.ThreeSum.LightSelectedPrime.time (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h)+
  _root_.ThreeSum.LightSmallDivide.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.numerator h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)+200

def space (work h : ℕ) : ℕ :=
  max (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.space work h) (_root_.ThreeSum.LightSelectedPrime.space work (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h))

def word (h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.word h+
  _root_.ThreeSum.LightSelectedPrime.word (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h)+20*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+_root_.ThreeSum.LocalCoverBounds.vertexCount (464*h) h+1)

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pCounts : ℕ
  pPrime : ℕ
  pDiv : ℕ
  counts : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.Procs P pCounts
  prime : _root_.ThreeSum1960614.Machine.ThreeSum.LightSelectedPrime.Procs P pPrime
  divide : P[pDiv]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.body pCounts pPrime pDiv)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightLocalParameters

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Constructing all Boolean coordinate rows for an enumerated mask list -/

namespace ThreeSum.LightMaskBitTable
open _root_.ThreeSum.LightMaskBitTable


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1000000

def body (pBits : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 5 (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBits [_root_.ThreeSum1960614.Machine.Light.v 0,_root_.ThreeSum1960614.Machine.Light.M (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 5))),((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 0))),_root_.ThreeSum1960614.Machine.Light.v 4] 6)



def Inv (μ : ℕ → ℤ) (mask : ℕ → ℕ)
    (L masks dst n work i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨_root_.Light.frame [L,masks,dst,n,work,i,r],μ'⟩ ∧
    (∀ j < i, ∀ a < L, μ' (dst+j*L+a) = (_root_.ThreeSum.LightMaskBits.bit L (mask j) a : ℤ)) ∧
    _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst (n*L)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightMaskBitTable

end ThreeSum1960614.Machine


