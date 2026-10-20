-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_CompressionDecoder
-- name    : OAI_Analysis_MetricEntropy_CompressionDecoder
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:03:29.721038+00:00
-- url     : https://prove2.me/theorems/bb51e243-ced0-4275-a4cf-2d8ac6affc9a
-- title:
--   Decoding a compression code into an approximating function
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. A nonnegative column weighting $\mu$ with $\sum_y\mu_y\le1$ on columns $y=(v_y,T_y)$ gives the profile mixture $x\mapsto\sum_y\mu_y\varphi_h(d_{T_y}(x,v_y))$; compression approximates all such mixtures uniformly by a list whose size does not depend on the number of rows. Let $L_i$ be label maps with a fixed-label system $(\mathrm{enc},\mathrm{rep})$ with $q$ codes.
--
--   1. **Decoder.** A code with common index $i$, label codes $c_{j,k}$ and weight codes $w_{j,k,T}$ decodes to
--   $$
--   x\mapsto\sum_{j<h}\gamma_h(j)\sum_{k<s}\sum_{T\subseteq\{1..u\}}\delta\,w_{j,k,T}\ \mathbf 1\bigl[d_T(x,\mathrm{rep}_i(c_{j,k}))\le2j+1\bigr],
--   $$
--   with mesh $\delta=\theta/(s2^u)$. Only shared label data and the code enter, not the original centres or weights.
--   2. **Compression list.** The image of all codes under the decoder, a finite family of functions on $X$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/CompressionDecoder.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/CompressionDecoder.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MetricEntropyDuality mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover
import Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionTuples
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteProductCounting
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionSampling
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricMultiplicity
import Definitions.Def_OAI_Analysis_MetricEntropy_FormPolynomials
import Definitions.Def_OAI_Analysis_MetricEntropy_PolynomialZeroBound
import Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Definitions.Def_OAI_Analysis_MetricEntropy_LogProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_GraphProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteFieldRows
import Definitions.Def_OAI_Analysis_MetricEntropy_GreedyPivots
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionLevels
import Definitions.Def_OAI_Analysis_MetricEntropy_ProfileMixtures
import Definitions.Def_OAI_Analysis_MetricEntropy_LabelEncoding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionCode
import Definitions.Def_OAI_Analysis_MetricEntropy_WeightRounding

namespace OAI

universe uX uLabel

/-!
# The fixed decoded family of compression approximants

The decoder uses only shared partition data, fixed label representatives, and
the finite code. Original column centers and coefficient vectors are absent
from its arguments. Every subset of the partition indices receives a weight
slot, so the enumeration includes every admissible-family encoding.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

variable {X : Type uX} {u q : ℕ} {Label : Fin u → Type uLabel}

/-- Decode the common index, pivot labels, and rounded grouped weights into
an actual real-valued function on the original domain. -/
def compressionDecode (L : (i : Fin u) → X → Label i) (E : FixedLabels L q)
    (h s : ℕ) (θ : ℝ)
    (code : CompressionCode u q h s (weightCodeSize (roundingStep θ s u))) : X → ℝ :=
  fun x => ∑ j : Fin h, LogProfile.gamma h j.val *
    ∑ k : Fin s, ∑ T : Finset (Fin u),
      decodeWeight (roundingStep θ s u) (code.2.2 j k T) *
        CompressionLevels.ballIndicator L T (2 * j.val + 1) x
          (E.representative code.1 (code.2.1 j k))

/-- The actual finite family, fixed before choosing a coefficient vector. -/
def compressionList (L : (i : Fin u) → X → Label i) (E : FixedLabels L q)
    (h s : ℕ) (θ : ℝ) : Finset (X → ℝ) :=
  compressionImage (compressionDecode L E h s θ)

end MetricEntropyDuality

end

end OAI


