-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
-- name    : OAI_Analysis_HyperbolicCones_ScalingAlgebra
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:46:23.393986+00:00
-- url     : https://prove2.me/theorems/a9344c53-cb48-4ebd-9e8f-cd8fc00773f9
-- title:
--   The block scalar matrix $\operatorname{diag}(I_a, sI_c)$
-- statement:
--   For natural numbers $a,c$ and a real number $s$, the block scalar matrix is the $(a+c)\times(a+c)$ block-diagonal matrix
--
--   $$
--   J_{a,c}(s)=\begin{pmatrix}I_a&0\\0&s\,I_c\end{pmatrix},
--   $$
--
--   whose rows and columns are indexed by the disjoint union of an index set of size $a$ and one of size $c$.
--
--   The matrix $J_{a,c}(s)$ is symmetric. For $s\neq0$ it is invertible with inverse $J_{a,c}(s^{-1})$. Conjugating a two-block matrix by it rescales the blocks:
--   $J_{a,c}(s^{-1})\begin{pmatrix}P&R\\R^{\mathsf T}&N\end{pmatrix}J_{a,c}(s^{-1})=\begin{pmatrix}P&s^{-1}R\\s^{-1}R^{\mathsf T}&s^{-2}N\end{pmatrix}$ for $P\in\mathbb{R}^{a\times a}$, $R\in\mathbb{R}^{a\times c}$, $N\in\mathbb{R}^{c\times c}$. In particular, for matrices $D,F,A\in\mathbb{R}^{a\times a}$, $B,C\in\mathbb{R}^{a\times c}$ and $E\in\mathbb{R}^{c\times c}$, this congruence turns $\begin{pmatrix}D+s^2F+sA&s^2C+sB\\ (s^2C+sB)^{\mathsf T}&s^2E\end{pmatrix}$ into $\begin{pmatrix}D+sA+s^2F&B+sC\\ (B+sC)^{\mathsf T}&E\end{pmatrix}$. This is how a two-block matrix pencil evaluated at the rescaled point $(X,s^2Z,sy)$ is brought into the scaled form whose limit as $s\to0$ is studied. Because the congruence is invertible, it does not change positive semidefiniteness.
--
--   **Formalization Note** The definition is `blockScalar a c s`, built with `Matrix.fromBlocks` on the index type `Fin a ⊕ Fin c`. Here $a$ and $c$ are arbitrary natural numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/ScalingAlgebra.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/ScalingAlgebra.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HyperbolicCones mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

def blockScalar (a c : ℕ) (s : ℝ) :
    Matrix (Fin a ⊕ Fin c) (Fin a ⊕ Fin c) ℝ :=
  Matrix.fromBlocks 1 0 0 (s • (1 : Mat c ℝ))

end Paper256

end

end OAI


