-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
-- name    : OAI_Combinatorics_MatchingPSD_IncidenceKernels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:33:27.687265+00:00
-- url     : https://prove2.me/theorems/b89ecd61-ed9b-479f-83dc-4a53d5b1755f
-- title:
--   Incidence matrix of a relation, its normalized Gram kernel, and conditional averages
-- statement:
--   Let $X$ and $Z$ be finite sets and let $P$ be a relation between them, written $P(x, z)$ for $x \in X$, $z \in Z$. The module defines:
--
--   1. The **incidence matrix** $I_P \in \mathbb{R}^{Z \times X}$, with $I_P(z, x) = 1$ if $P(x, z)$ holds and $I_P(z, x) = 0$ otherwise.
--   2. The **common incidence** of $x, y \in X$, $c_P(x, y) = \bigl|\{ z \in Z : P(x, z) \text{ and } P(y, z)\}\bigr|$, which is the $(x,y)$ entry of $I_P^{\mathsf T} I_P$.
--   3. For a real normalization $D$, the **incidence kernel** and the **incidence operator**, both indexed by $X \times X$:
--   $$
--   K_{P,D}(x, y) = \frac{|Z|}{D^2}\, c_P(x, y), \qquad O_{P,D}(x, y) = \frac{K_{P,D}(x, y)}{|X|} .
--   $$
--   4. For a real normalization $E$ and a function $f : X \to \mathbb{R}$, the **conditional average** at $z \in Z$,
--   $$
--   \mathrm{avg}_{P,E}(f)(z) = \frac{1}{E} \sum_{x \in X :\, P(x, z)} f(x) .
--   $$
--
--   Since $O_{P,D} = \frac{|Z|}{D^2 |X|}\, I_P^{\mathsf T} I_P$, the incidence operator is symmetric positive semidefinite. If $X$ and $Z$ are nonempty, $D \neq 0$ and $E = |X| D / |Z|$, then the mean square of the conditional averages equals the normalized quadratic form of the operator,
--   $$
--   \frac{1}{|Z|} \sum_{z \in Z} \mathrm{avg}_{P,E}(f)(z)^2 = \frac{1}{|X|} \sum_{x \in X} f(x)\, (O_{P,D} f)(x),
--   $$
--   and when every $z$ is related to exactly $E$ elements of $X$ the conditional average is the plain average of $f$ over the fiber of $z$. This converts the question of how strongly a function on $X$ can correlate with the fibers of the relation into a spectral question about $O_{P,D}$; in the application $X$ is the set of perfect matchings, $Z$ a set of colorings, and $P$ says that the matching has a prescribed color table under the coloring.
--
--   **Formalization Note** The definitions are `incidence P` (a `Matrix Z X ℝ`), `commonIncidence P x y`, `incidenceKernel P D`, `incidenceOperator P D` and `conditionalAverage P E f z`; decidability of `P` is classical. `D` and `E` are arbitrary reals, and Lean's convention $x / 0 = 0$ makes the kernel and the operator vanish when $D = 0$, and the conditional averages vanish when $E = 0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/IncidenceKernels.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/IncidenceKernels.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
open Matrix

section FiniteSums
variable {G : Type u_1} {X : Type u_2} [Fintype G] [Group G] [Fintype X] [MulAction G X]

end FiniteSums

section KernelTrace
variable {G : Type u_3} {X : Type u_4} [Fintype G] [Group G] [Fintype X] [DecidableEq X]
  [MulAction G X]

end KernelTrace

section Incidence
variable {X : Type u_5} {Z : Type u_6} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z]

noncomputable def incidence (P : X → Z → Prop) : Matrix Z X ℝ :=
  by classical exact fun z x => if P x z then 1 else 0

noncomputable def commonIncidence (P : X → Z → Prop) (x y : X) : ℝ :=
  by classical exact (Fintype.card {z // P x z ∧ P y z} : ℝ)

noncomputable def incidenceKernel (P : X → Z → Prop) (D : ℝ) : Matrix X X ℝ :=
  fun x y => (Fintype.card Z : ℝ) / D ^ 2 * commonIncidence P x y

noncomputable def incidenceOperator (P : X → Z → Prop) (D : ℝ) : Matrix X X ℝ :=
  fun x y => incidenceKernel P D x y / Fintype.card X

noncomputable def conditionalAverage (P : X → Z → Prop) (E : ℝ) (f : X → ℝ) (z : Z) : ℝ :=
  (∑ x, incidence P z x * f x) / E

end Incidence
end MatchingSmoothing

end OAI


