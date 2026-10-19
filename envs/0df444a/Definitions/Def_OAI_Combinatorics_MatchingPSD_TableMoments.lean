-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
-- name    : OAI_Combinatorics_MatchingPSD_TableMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:31:49.183353+00:00
-- url     : https://prove2.me/theorems/490f17db-f40e-4120-9fb8-5921e0c744e3
-- title:
--   Color-pair types, color tables of paired 3-colorings and their empirical pair matrices
-- statement:
--   Colors are taken from $\{0, 1, 2\}$. Let $H$ be a finite set and $f : H \times \{0,1\} \to \{0,1,2\}$ a coloring of the paired vertex set, whose $i$-th pair is $\{(i,0),(i,1)\}$. The module defines:
--
--   1. The **type** of an unordered pair of colors (repetition allowed), one of six values given by the symmetric table
--   $$
--   \tau(a, b) = \begin{pmatrix} 0 & 1 & 2 \\ 1 & 3 & 4 \\ 2 & 4 & 5 \end{pmatrix}_{a b}, \qquad a, b \in \{0,1,2\},
--   $$
--   so $\tau(a,b) = \tau(b,a)$, the types $0, 3, 5$ are the monochromatic pairs $\{0,0\}, \{1,1\}, \{2,2\}$, and the types $1, 2, 4$ are $\{0,1\}, \{0,2\}, \{1,2\}$.
--   2. The **type multiplicity** $\mu = (1, 2, 2, 1, 2, 1)$, the number of ordered pairs $(a,b)$ of each type.
--   3. The bijection between colorings of $H \times \{0,1\}$ and maps $H \to \{0,1,2\}^2$, $f \mapsto \bigl(i \mapsto (f(i,0), f(i,1))\bigr)$ (this part needs no finiteness).
--   4. The **three-color table** $T_f : \{0,\dots,5\} \to \mathbb{N}$, $T_f(t) = \bigl|\{ i \in H : \tau(f(i,0), f(i,1)) = t\}\bigr|$, the number of pairs whose two endpoints carry a color pair of type $t$.
--   5. The **empirical pair matrix** $\Gamma_f \in \mathbb{R}^{3 \times 3}$ and the **empirical color distribution** $\pi_f \in \mathbb{R}^3$,
--   $$
--   \Gamma_f(a, b) = \frac{T_f(\tau(a,b))}{|H| \, \mu(\tau(a,b))}, \qquad \pi_f(a) = \frac{\bigl|\{v \in H \times \{0,1\} : f(v) = a\}\bigr|}{2 |H|}.
--   $$
--
--   Thus $\Gamma_f(a,b)$ is the probability that a uniformly random pair, with its two endpoints listed in uniformly random order, has colors $(a,b)$, and $\pi_f(a)$ is the fraction of vertices of color $a$. The matrix $\Gamma_f$ is symmetric and nonnegative with row sums $\sum_b \Gamma_f(a,b) = \pi_f(a)$, so for nonempty $H$ the table of a coloring determines its color counts. These quantities parametrize the product measure used to estimate how many colorings share a given table and to bound the second moment of the incidence kernel between perfect matchings and colorings with a prescribed table.
--
--   **Formalization Note** The definitions are `threeEdgeType`, `typeMultiplicity`, `pairColorEquiv`, `threeTable f := histogram (threeEdgeType ∘ pairColorEquiv f)`, `tableGamma f` and `tablePi f`, with colors in `Fin 3`, types in `Fin 6` and `H × Bool` as the paired vertex set. Divisions follow Lean's convention $x / 0 = 0$, so for empty $H$ both $\Gamma_f$ and $\pi_f$ vanish.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/TableMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TableMoments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace MatchingSmoothing
open Matrix
section TableKernel
variable {H : Type u_1} {C : Type u_2} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

end TableKernel
end MatchingSmoothing

namespace MatchingSmoothing
open Matrix

def threeEdgeType (p : Fin 3 × Fin 3) : Fin 6 :=
  (![![0, 1, 2], ![1, 3, 4], ![2, 4, 5]] : Fin 3 → Fin 3 → Fin 6) p.1 p.2

def typeMultiplicity : Fin 6 → ℕ := ![1, 2, 2, 1, 2, 1]

section ThreeTables
variable {H : Type u_3} [Fintype H] [DecidableEq H]

noncomputable def pairColorEquiv : (H × Bool → Fin 3) ≃ (H → Fin 3 × Fin 3) where
  toFun f i := (f (i,false), f (i,true))
  invFun k v := if v.2 then (k v.1).2 else (k v.1).1
  left_inv f := by funext ⟨i,b⟩; cases b <;> rfl
  right_inv k := by funext i; rfl

noncomputable def threeTable (f : H × Bool → Fin 3) : Fin 6 → ℕ :=
  histogram (threeEdgeType ∘ pairColorEquiv f)

noncomputable def tableGamma (f : H × Bool → Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ((threeTable f (threeEdgeType (i,j)) : ℝ) / Fintype.card H) /
    typeMultiplicity (threeEdgeType (i,j))

noncomputable def tablePi (f : H × Bool → Fin 3) : Fin 3 → ℝ :=
  fun i => (histogram f i : ℝ) / (2 * Fintype.card H)

end ThreeTables

section Probability
variable {V : Type u_6} {C : Type u_7} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

end Probability

section TableNormalization
variable {H : Type u_8} {C : Type u_9} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

end TableNormalization

section ThreeTableMoment
variable {H : Type u_10} [Fintype H] [DecidableEq H]

end ThreeTableMoment
end MatchingSmoothing

end OAI


