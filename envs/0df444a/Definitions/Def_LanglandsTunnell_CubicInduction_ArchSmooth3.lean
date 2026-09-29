-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
-- name    : LanglandsTunnell_CubicInduction_ArchSmooth3
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/68923433-878d-5b31-9574-e1477246d795
-- title:
--   Archimedean smoothness of functions on adelic GL3​ over Q
-- statement:
--   Let $\mathbb{A}$ denote the adele ring of $\mathbb{Q}$, realised as the product of the infinite adele ring and the finite adele ring, and let $GL_3(\mathbb{A})$ be the adelic general linear group `AdelicGL 3 (𝓞 ℚ) ℚ`. Three declarations set up a real parametrisation of the archimedean directions in this group. First, for an array $e \colon \mathrm{Fin}\,3 \to \mathrm{Fin}\,3 \to \mathbb{R}$ of real numbers, `archRealMat3 e` is the $3 \times 3$ matrix over $\mathbb{A}$ whose archimedean part is the matrix with entries the infinite adeles `StandardKernel.ofReal (e i j)` (the infinite adele whose coordinate at each infinite place of $\mathbb{Q}$ is $e\,i\,j$) and whose finite part is the identity matrix; this is the image of that archimedean matrix under the multiplicative inclusion `archMatrixInclN`. Secondly, `archRealLift3 e` is the element of $GL_3(\mathbb{A})$ with underlying matrix `archRealMat3 e` whenever that matrix is a unit in the matrix ring, and the identity element of $GL_3(\mathbb{A})$ otherwise; the second branch is a default value, the case of interest being arrays of non-zero determinant, for which the adelic matrix is invertible because its archimedean component is invertible and its finite component is the identity. Thirdly, `IsArchSmooth3` is a predicate on functions $\varphi \colon GL_3(\mathbb{A}) \to \mathbb{C}$: it holds when for every $g \in GL_3(\mathbb{A})$ the function of nine real variables
--   $$e \longmapsto \varphi\bigl(g \cdot \mathrm{archRealLift3}(e)\bigr)$$
--   is of class $C^\infty$ over $\mathbb{R}$, in the sense of `ContDiffOn` with smoothness order $\top$, on the set $\{e \mid \det(e) \neq 0\}$ of real arrays with non-vanishing determinant. Thus archimedean smoothness is expressed as smoothness of all right translates along this explicit real chart, rather than through a manifold structure on the adelic group.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring, the general linear group of matrices and the predicate `ContDiffOn` used here; the archimedean-smoothness condition for functions on an adelic group, and the real parametrisation through which it is phrased, are the project's own.
--
--   **Where it is used.** These definitions belong to the $GL_3$ vocabulary used in the cubic-induction (Langlands–Tunnell) part of the argument, where automorphic forms on $GL_3$ over $\mathbb{Q}$ are required to be smooth in the archimedean variables; that input is what makes the odd irreducible two-dimensional mod $3$ representations modular, the starting point of the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_ArchSmooth3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

namespace WhittakerBlock

def archRealMat3 (e : Fin 3 → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) :=
  AutomorphicForm.archMatrixInclN (Fin 3) ℚ (Matrix.of fun i j => AutomorphicForm.StandardKernel.ofReal (e i j))

open scoped Classical in

def archRealLift3 (e : Fin 3 → Fin 3 → ℝ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  if h : IsUnit (archRealMat3 e) then h.unit else 1

def IsArchSmooth3 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 3 → Fin 3 → ℝ => φ (g * archRealLift3 e)) {e | (Matrix.of e).det ≠ 0}

end WhittakerBlock

end


