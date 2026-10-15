-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_SignParity
-- name    : OAI_Combinatorics_GotsmanLinial_SignParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:46:48.634287+00:00
-- url     : https://prove2.me/theorems/25257efc-07e2-4834-8e12-9d6d4cc714a1
-- title:
--   Full parity, adjacency, and ordered constant-sign edges of the Boolean cube
-- statement:
--   Let $Q_n=\{-1,1\}^n$ be the Boolean cube, and for $x\in Q_n$ and a coordinate $i$ let $x^{(i)}$ be the vertex obtained from $x$ by reversing the sign of coordinate $i$. Write $d_H$ for the Hamming distance.
--
--   1. **Full parity.** $\pi(x)=\prod_{i=1}^{n}x_i\in\{-1,1\}$, a real function with $\pi(x)^2=1$ and $\pi(x^{(i)})=-\pi(x)$; as a complex function it is the Walsh character $\chi_{[n]}$ of the full coordinate set.
--
--   2. **Adjacency.** Vertices $x,y$ are adjacent if $y=x^{(i)}$ for some coordinate $i$.
--
--   3. **Ordered neighbor pairs.** $\mathcal E_n=\{(x,y)\in Q_n\times Q_n: d_H(x,y)=1\}$, the ordered edges of the cube. One has $d_H(x,x^{(i)})=1$, and the map $(i,x)\mapsto(x,x^{(i)})$ from directions and vertices to ordered pairs is injective.
--
--   4. **Ordered constant edges.** For $h:Q_n\to\mathbb{R}$,
--   $$
--   \mathcal C(h)=\{(x,y)\in\mathcal E_n : h(x)=h(y)\},
--   $$
--   the ordered edges along which $h$ does not change.
--
--   5. **Constant shifts.** For a real polynomial $p$ in $n$ variables and $\varepsilon\in\mathbb{R}$, evaluation at cube vertices satisfies $(p+\varepsilon)(x)=p(x)+\varepsilon$.
--
--   These notions convert sensitivity into constant-sign edges: if $f$ takes values $\pm1$, then $f(x)\neq f(x^{(i)})$ exactly when $\pi f$ takes equal values at $x$ and $x^{(i)}$, because $\pi$ changes sign along every edge. Hence the ordered sensitive edges of a threshold function $f$ are the ordered constant edges of $\pi f$. The constant shift is used to perturb a polynomial so that it has no zeros on the cube without changing its threshold signs.
--
--   **Formalization Note** Vertices are Boolean functions on `Fin n` read as signs via `cubeCoord`, and $x^{(i)}$ is `flip i x`. The objects are `fullParity`, `CubeAdjacent`, `orderedNeighborPairs`, `orderedConstantEdges` and `directedEdgeEmbedding`; `polynomialValue p x` evaluates an `MvPolynomial` at the sign vector of `x`, and `polynomialValue_add_C` is the constant-shift rule.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/SignParity.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/SignParity.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GotsmanLinial mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_PolynomialDegree

namespace OAI

/-!
# Removing threshold zeros and turning sensitive edges into constant-sign edges

All graph pairs are ordered. The cube coordinates are the real
signs encoded by `Bool` in the public statement.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

/-- Full parity, with values in the reals. -/
noncomputable def fullParity {n : ℕ} (x : Cube n) : ℝ :=
  ∏ i : Fin n, cubeCoord x i

/-- Two cube vertices differ by a single coordinate flip. -/
def CubeAdjacent {n : ℕ} (x y : Cube n) : Prop :=
  ∃ i : Fin n, flip i x = y

/-- All ordered pairs of neighboring vertices. -/
noncomputable def orderedNeighborPairs (n : ℕ) : Finset (Cube n × Cube n) := by
  classical
  exact Finset.univ.filter fun e => hammingDist e.1 e.2 = 1

/-- Ordered neighboring pairs at which a real function has equal values. -/
noncomputable def orderedConstantEdges {n : ℕ} (h : Cube n → ℝ) :
    Finset (Cube n × Cube n) := by
  classical
  exact (orderedNeighborPairs n).filter fun e => h e.1 = h e.2

@[simp] theorem fullParity_sq {n : ℕ} (x : Cube n) : fullParity x ^ 2 = 1 := by
  rw [fullParity, ← Finset.prod_pow]
  simp

/-- Reversing one coordinate reverses full parity. -/
@[simp] theorem fullParity_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    fullParity (flip i x) = -fullParity x := by
  classical
  have hc : cubeCoord (flip i x) = Function.update (cubeCoord x) i (-cubeCoord x i) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [cubeCoord_flip_ne x i j hj, Function.update_of_ne hj]
  unfold fullParity
  rw [hc, Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase, neg_mul,
    Finset.mul_prod_erase Finset.univ (cubeCoord x) (Finset.mem_univ i)]

@[simp] theorem hammingDist_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    hammingDist x (flip i x) = 1 := by
  classical
  have hset : (Finset.univ.filter fun j => x j ≠ flip i x j) = {i} := by
    ext j
    by_cases hj : j = i
    · subst j
      cases hx : x i <;> simp [flip, hx]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      simp [flip, hj]
  simp only [hammingDist, hset, Finset.card_singleton]

/-- A vertex and a direction identify a unique ordered cube edge. -/
def directedEdgeEmbedding (n : ℕ) : (Fin n × Cube n) ↪ (Cube n × Cube n) where
  toFun e := (e.2, flip e.1 e.2)
  inj' := by
    rintro ⟨i, x⟩ ⟨j, y⟩ heq
    have hxy : x = y := congrArg Prod.fst heq
    subst y
    have hij : i = j := flip_injective_direction x (congrArg Prod.snd heq)
    subst j
    rfl

/-- The real parity used for threshold signs is exactly the full complex
Walsh character under the standard real embedding. -/
@[simp] theorem ofReal_fullParity {n : ℕ} (x : Cube n) :
    (fullParity x : ℂ) = walshChar Finset.univ x := by
  simp only [fullParity, Complex.ofReal_prod, walshChar]

@[simp] theorem polynomialValue_add_C {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (ε : ℝ) (x : Cube n) :
    polynomialValue (p + MvPolynomial.C ε) x = polynomialValue p x + ε := by
  simp [polynomialValue]

end LeanBlast.GotsmanLinial

end OAI


