-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
-- name    : OAI_Combinatorics_GotsmanLinial_Statement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:05:22.886907+00:00
-- url     : https://prove2.me/theorems/1399bfdc-0587-4b91-b759-fe48eea2a078
-- title:
--   Elementary identities for coordinate flips, cube signs and the threshold sign
-- statement:
--   This file introduces no new objects; it records the basic algebraic facts about the primitives of the Gotsman–Linial statement. A vertex of the cube is a map $x : \{1,\dots,n\} \to \{\mathrm{false}, \mathrm{true}\}$; its $i$-th sign is $\sigma_i(x) = 1$ if $x_i = \mathrm{true}$ and $\sigma_i(x) = -1$ otherwise; $x^{\oplus i}$ is the vertex obtained by negating the $i$-th coordinate; and the threshold sign is $\operatorname{sgn}(t) = 1$ for $t \ge 0$, $\operatorname{sgn}(t) = -1$ for $t < 0$. For all $n$, vertices $x$, coordinates $i, j$ and real $t$:
--
--   1. Flipping negates the chosen coordinate and is an involution: $(x^{\oplus i})_i = \lnot x_i$ and $(x^{\oplus i})^{\oplus i} = x$.
--   2. For fixed $x$, the map $i \mapsto x^{\oplus i}$ is injective: different directions lead to different neighbours.
--   3. Signs under flips: $\sigma_i(x^{\oplus i}) = -\sigma_i(x)$, and $\sigma_j(x^{\oplus i}) = \sigma_j(x)$ whenever $j \neq i$.
--   4. Every sign is $\pm 1$: $\sigma_i(x) \in \{1, -1\}$ and $\sigma_i(x)^2 = 1$.
--   5. The threshold sign: $\operatorname{sgn}(0) = 1$, $\operatorname{sgn}(t) \in \{1, -1\}$ and $\operatorname{sgn}(t)^2 = 1$.
--   6. The cube has exactly $2^n$ vertices.
--
--   These facts are used throughout the proof: to identify ordered cube edges with pairs (vertex, direction), to see that flipping a coordinate reverses the full parity $\prod_i \sigma_i(x)$, to treat threshold functions as $\pm 1$-valued, and to normalise counts by $2^n$.
--
--   **Formalization Note** The lemmas are `flip_apply_same`, `flip_flip`, `flip_injective_direction`, `cubeCoord_flip_same`, `cubeCoord_flip_ne`, `cubeCoord_cases`, `cubeCoord_sq`, `thresholdSign_zero`, `thresholdSign_cases`, `thresholdSign_sq` and `card_cube`; $\sigma_i(x)$ is `cubeCoord x i` and the cube is `Cube n = Fin n → Bool`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/Statement.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/Statement.lean by skeleton subtraction
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

namespace OAI

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

@[simp] theorem flip_apply_same {n : ℕ} (i : Fin n) (x : Cube n) :
    flip i x i = !(x i) := by
  simp [flip]

@[simp] theorem flip_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    flip i (flip i x) = x := by
  funext j
  by_cases h : j = i
  · subst j
    simp [flip]
  · simp [flip, h]

theorem flip_injective_direction {n : ℕ} (x : Cube n) :
    Function.Injective (fun i : Fin n => flip i x) := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  cases hxi : x i <;> simp [flip, hij, hxi] at hi

@[simp] theorem cubeCoord_flip_same {n : ℕ} (x : Cube n) (i : Fin n) :
    cubeCoord (flip i x) i = -cubeCoord x i := by
  cases hxi : x i <;> simp [cubeCoord, flip, hxi]

theorem cubeCoord_flip_ne {n : ℕ} (x : Cube n) (i j : Fin n) (h : j ≠ i) :
    cubeCoord (flip i x) j = cubeCoord x j := by
  simp [cubeCoord, flip, h]

theorem cubeCoord_cases {n : ℕ} (x : Cube n) (i : Fin n) :
    cubeCoord x i = 1 ∨ cubeCoord x i = -1 := by
  cases hxi : x i <;> simp [cubeCoord, hxi]

@[simp] theorem cubeCoord_sq {n : ℕ} (x : Cube n) (i : Fin n) :
    (cubeCoord x i) ^ 2 = 1 := by
  cases hxi : x i <;> simp [cubeCoord, hxi]

@[simp] theorem thresholdSign_zero : thresholdSign 0 = 1 := by
  simp [thresholdSign]

theorem thresholdSign_cases (t : ℝ) : thresholdSign t = 1 ∨ thresholdSign t = -1 := by
  unfold thresholdSign
  split <;> simp

@[simp] theorem thresholdSign_sq (t : ℝ) : thresholdSign t ^ 2 = 1 := by
  rcases thresholdSign_cases t with h | h <;> simp [h]

@[simp] theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  simp [Cube]

end LeanBlast.GotsmanLinial

end OAI


