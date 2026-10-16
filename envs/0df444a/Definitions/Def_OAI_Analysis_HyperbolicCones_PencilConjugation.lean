-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
-- name    : OAI_Analysis_HyperbolicCones_PencilConjugation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:28:38.337251+00:00
-- url     : https://prove2.me/theorems/34755492-ff2c-4a9a-8805-0669ed514c5b
-- title:
--   Congruence and index restriction of linear matrix pencils
-- statement:
--   Let $V$ be a real vector space and let $\mathrm{Sym}_n$ be the space of real symmetric $n\times n$ matrices, with rows and columns indexed by $[n]=\{0,1,\dots,n-1\}$. A linear map $L:V\to\mathrm{Sym}_n$ is called a (linear matrix) pencil. It describes the spectrahedral set $\{x\in V: L(x)\succeq0\}$, where $M\succeq0$ means that $M$ is positive semidefinite. The file defines two ways of producing new pencils from $L$.
--
--   1. **Congruence.** For a real $n\times n$ matrix $U$, the pencil $U^{\mathsf T}LU:V\to\mathrm{Sym}_n$ given by
--   $$
--   (U^{\mathsf T}LU)(x)=U^{\mathsf T}L(x)\,U .
--   $$
--   2. **Restriction along an index map.** For a map $f:[m]\to[n]$, the pencil $L_f:V\to\mathrm{Sym}_m$ given by $L_f(x)_{ij}=L(x)_{f(i)\,f(j)}$ for $i,j\in[m]$. When $f$ is injective, $L_f(x)$ is the principal submatrix of $L(x)$ on the rows and columns $f(0),\dots,f(m-1)$.
--
--   Both constructions are linear in $x$ and take symmetric values. If $U$ is invertible, then $U^{\mathsf T}L(x)U\succeq0$ exactly when $L(x)\succeq0$, so congruence changes a representation without changing the set it represents. Restriction extracts diagonal blocks of a pencil. Both operations are used to bring a hypothetical spectrahedral representation of the hyperbolicity cone studied in the surrounding development into block form.
--
--   **Formalization Note** The definitions are `conjugatePencil L U`, written with the conjugate transpose of `U` (the transpose, since the entries are real), and `restrictPencil L f`, built with `Matrix.submatrix`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/PencilConjugation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/PencilConjugation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HyperbolicCones mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

def conjugatePencil {n : ℕ} (L : V →ₗ[ℝ] Sym n) (U : Mat n ℝ) : V →ₗ[ℝ] Sym n where
  toFun x := ⟨Uᴴ * (L x : Mat n ℝ) * U,
    Matrix.isHermitian_conjTranspose_mul_mul U (L x).property⟩
  map_add' x y := by
    apply Subtype.ext
    simp [mul_add, add_mul]
  map_smul' c x := by
    apply Subtype.ext
    simp

def restrictPencil {m n : ℕ} (L : V →ₗ[ℝ] Sym n) (f : Fin m → Fin n) :
    V →ₗ[ℝ] Sym m where
  toFun x := ⟨(L x : Mat n ℝ).submatrix f f, (sym_isHermitian (L x)).submatrix f⟩
  map_add' x y := by apply Subtype.ext; ext i j; simp
  map_smul' c x := by apply Subtype.ext; ext i j; simp

end Paper256

end

end OAI


