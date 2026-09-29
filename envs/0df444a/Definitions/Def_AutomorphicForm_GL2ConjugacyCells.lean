-- Prove2me | Definitions.Def_AutomorphicForm_GL2ConjugacyCells
-- name    : AutomorphicForm_GL2ConjugacyCells
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/d37e69f8-dbda-5e24-9a86-069c429b90a2
-- title:
--   Conjugacy-type predicates and cells in GL2​
-- statement:
--   Over a field $K$, four predicates on a $2\times 2$ matrix $M$ with entries in $K$ are defined, each phrased in terms of the matrix itself or its characteristic polynomial `M.charpoly`. `IsCentralType M` asserts that $M = c\cdot 1$ for some scalar $c \in K$, i.e. $M$ is a scalar multiple of the identity. `IsUnipotentType M` is the conjunction of two conditions: $M$ is not of central type, and there exists $a \in K$ with $M.\mathrm{charpoly} = (X - a)^2$; thus the characteristic polynomial has a single repeated rational eigenvalue while $M$ itself is non-scalar, which covers the unipotent matrices and their scalar twists. `IsHyperbolicType M` asserts the existence of $a, b \in K$ with $a \neq b$ and $M.\mathrm{charpoly} = (X-a)(X-b)$, i.e. two distinct eigenvalues in $K$. `IsEllipticType M` asserts that no $a \in K$ is a root of $M.\mathrm{charpoly}$, i.e. the characteristic polynomial is irreducible over $K$ (for a degree-two polynomial, having no rational root).
--
--   Correspondingly four subsets of the general linear group $\mathrm{GL}_2(K)$ are defined — `centralCell`, `unipotentCell`, `hyperbolicCell` and `ellipticCell` — each consisting of those $\gamma$ whose underlying matrix satisfies the corresponding predicate; the coercion from the unit group to matrices is applied before testing the predicate. The four accompanying lemmas `mem_centralCell_iff`, `mem_unipotentCell_iff`, `mem_hyperbolicCell_iff` and `mem_ellipticCell_iff` record that membership in each cell is exactly the corresponding predicate on the underlying matrix, so that the set-builder definitions can be used interchangeably with the predicates. Note that the predicates are stated for arbitrary matrices and that no disjointness, exhaustiveness or conjugation-invariance statement is part of this module: it fixes the vocabulary only.
--
--   **Relation to Mathlib.** Mathlib supplies the characteristic polynomial `Matrix.charpoly` and the group `GL (Fin 2) K` used here, but has no classification of $2\times 2$ matrices into central, unipotent, hyperbolic and elliptic types; these predicates and the four cells are the project's own.
--
--   **Where it is used.** The four cells give a partition of $\mathrm{GL}_2$ by the existence and multiplicity of rational eigenvalues, which is the division of conjugacy classes used on the geometric side of the $\mathrm{GL}_2$ trace formula and in the local analysis of automorphic forms on $\mathrm{GL}_2$. The vocabulary fixed here is used throughout the automorphic part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_GL2ConjugacyCells.lean

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix Polynomial

noncomputable section

namespace AutomorphicForm

variable {K : Type*} [Field K]

def IsCentralType (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∃ c : K, M = c • (1 : Matrix (Fin 2) (Fin 2) K)

def IsUnipotentType (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ¬IsCentralType M ∧ ∃ a : K, M.charpoly = (X - C a) ^ 2

def IsHyperbolicType (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∃ a b : K, a ≠ b ∧ M.charpoly = (X - C a) * (X - C b)

def IsEllipticType (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∀ a : K, ¬M.charpoly.IsRoot a

def centralCell (K : Type*) [Field K] : Set (GL (Fin 2) K) :=
  {γ | IsCentralType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)}

def unipotentCell (K : Type*) [Field K] : Set (GL (Fin 2) K) :=
  {γ | IsUnipotentType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)}

def hyperbolicCell (K : Type*) [Field K] : Set (GL (Fin 2) K) :=
  {γ | IsHyperbolicType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)}

def ellipticCell (K : Type*) [Field K] : Set (GL (Fin 2) K) :=
  {γ | IsEllipticType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)}

theorem mem_centralCell_iff {γ : GL (Fin 2) K} :
    γ ∈ centralCell K ↔ IsCentralType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  Iff.rfl

theorem mem_unipotentCell_iff {γ : GL (Fin 2) K} :
    γ ∈ unipotentCell K ↔ IsUnipotentType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  Iff.rfl

theorem mem_hyperbolicCell_iff {γ : GL (Fin 2) K} :
    γ ∈ hyperbolicCell K ↔ IsHyperbolicType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  Iff.rfl

theorem mem_ellipticCell_iff {γ : GL (Fin 2) K} :
    γ ∈ ellipticCell K ↔ IsEllipticType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  Iff.rfl

end AutomorphicForm


