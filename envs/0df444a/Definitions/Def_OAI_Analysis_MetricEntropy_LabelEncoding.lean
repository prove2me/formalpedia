-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_LabelEncoding
-- name    : OAI_Analysis_MetricEntropy_LabelEncoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:00:27.513001+00:00
-- url     : https://prove2.me/theorems/9c68b2bd-610e-4e5a-9df8-6004c1e72d79
-- title:
--   Finite encodings of realized partition labels
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. Let $L_i:X\to\Lambda_i$ ($i\le u$) be label maps on a finite nonempty set $X$, and $q\in\mathbb N$.
--
--   1. **Fixed labels.** A fixed-label system consists of codes $\mathrm{enc}_i:X\to\{1..q\}$ and representatives $\mathrm{rep}_i:\{1..q\}\to X$ with
--   $$
--   \mathrm{enc}_i(x)=\mathrm{enc}_i(y)\iff L_i(x)=L_i(y),\qquad L_i(\mathrm{rep}_i(\mathrm{enc}_i(x)))=L_i(x).
--   $$
--   2. **Range embedding.** The finite range of $L_i$ embeds into $\{1..q\}$ when it has at most $q$ elements.
--   3. **Construction.** If every $L_i$ takes at most $q$ values, such a system exists. It is fixed before any weights are chosen.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/LabelEncoding.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/LabelEncoding.lean by skeleton subtraction
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

namespace OAI

universe uX uLabel uY

/-!
# Fixed encodings of realized partition labels

Only the realized labels are counted. The ambient label types need not be
finite, and representatives are fixed from the label maps alone, before any
coefficient vector enters the compression construction.
-/

noncomputable section

namespace MetricEntropyDuality

/-- Shared finite label data for a family of partitions. A representative is
defined at every code, including unused codes, and preserves each realized
label when applied to its encoding. -/
structure FixedLabels {X : Type uX} {u : ℕ} {Label : Fin u → Type uLabel}
    (L : (i : Fin u) → X → Label i) (q : ℕ) where
  encode : Fin u → X → Fin q
  representative : Fin u → Fin q → X
  encode_eq_iff : ∀ i x y, encode i x = encode i y ↔ L i x = L i y
  label_representative_encode : ∀ i x,
    L i (representative i (encode i x)) = L i x

namespace FixedLabels

variable {X : Type uX} {u q : ℕ} {Label : Fin u → Type uLabel}
  {L : (i : Fin u) → X → Label i}

/-- Embed the finite range, rather than the entire ambient label type. -/
def rangeEmbedding {Y : Type uY} [Finite X] (f : X → Y) (q : ℕ)
    (hcard : Nat.card (Set.range f) ≤ q) : Set.range f ↪ Fin q :=
  (Finite.equivFin (Set.range f)).toEmbedding.trans (Fin.castLEEmb hcard)

/-- Construct all encodings and representative maps from the fixed label
family and its realized-cardinality bounds. The construction has no measure
or coefficient-vector parameter. Nonempty `X` supplies a representative even
at codes outside the encoding's image. -/
def ofCardBound [Finite X] [Nonempty X]
    (L : (i : Fin u) → X → Label i)
    (hcard : ∀ i, Nat.card (Set.range (L i)) ≤ q) : FixedLabels L q := by
  let enc : Fin u → X → Fin q := fun i x =>
    rangeEmbedding (L i) q (hcard i) ⟨L i x, ⟨x, rfl⟩⟩
  have heq : ∀ i x y, enc i x = enc i y ↔ L i x = L i y := by
    intro i x y
    constructor
    · intro h
      exact congrArg Subtype.val ((rangeEmbedding (L i) q (hcard i)).injective h)
    · intro h
      exact congrArg (rangeEmbedding (L i) q (hcard i)) (Subtype.ext h)
  let rep : Fin u → Fin q → X := fun i => Function.invFun (enc i)
  have hrep : ∀ i x, L i (rep i (enc i x)) = L i x := by
    intro i x
    apply (heq i _ _).mp
    exact Function.invFun_eq ⟨x, rfl⟩
  exact ⟨enc, rep, heq, hrep⟩

end FixedLabels

end MetricEntropyDuality

end

end OAI


