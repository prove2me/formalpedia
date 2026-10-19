-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_PermutationSmoothing__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:33:13.84915+00:00
-- url     : https://prove2.me/theorems/e9622718-3d23-435e-ba8f-83ede1419be9
-- title:
--   Low-degree projection of functions on perfect matchings and the table energy
-- statement:
--   Fix $h \in \mathbb{N}$, let $V_h = \{0,\dots,h-1\} \times \{0,1\}$ ($2h$ vertices), and let $\mathcal{M}_h$ be the set of perfect matchings of $V_h$, encoded as permutations $M$ with $M(M(v)) = v$ and $M(v) \neq v$ for all $v$. For $d \in \mathbb{N}$ let $\mathcal{P}_{h,d}$ be the space of functions on $\mathcal{M}_h$ that are polynomials of degree at most $d$ in the edge indicators $x_{(a,b)}(M)$, where $x_{(a,b)}(M) = 1$ if $M(a) = b$ and $0$ otherwise. The module defines:
--
--   1. The **low-degree projection** $L_{h,d}$, the linear operator on the function space $\mathbb{R}^{\mathcal{M}_h}$ given by orthogonal projection onto $\mathcal{P}_{h,d}$ for the inner product $\langle f, g\rangle = \sum_{M} f(M) g(M)$.
--   2. For a finite vertex set $V$, color counts $s : \{0,1,2\} \to \mathbb{N}$, a target table $t : \{0,\dots,5\} \to \mathbb{N}$ and a function $f$ on the perfect matchings of $V$, the **table energy**
--   $$
--   \mathcal{E}_{s,t}(f) = \mathbb{E}_{z} \Bigl[ \bigl( \mathbb{E}_{M :\, \mathrm{tab}_M(z) = t}\, f(M) \bigr)^2 \Bigr],
--   $$
--   where $z$ is uniform over the colorings $V \to \{0,1,2\}$ with color counts $s$, the inner average is over the matchings $M$ whose color table under $z$ equals $t$, and $\mathrm{tab}_M(z)(\theta)$ is the number of edges of $M$ whose endpoint colors form the unordered pair of type $\theta$, the six types $0,\dots,5$ being $\{0,0\},\{0,1\},\{0,2\},\{1,1\},\{1,2\},\{2,2\}$.
--
--   The table energy measures how much of a function of the matching can be seen through color-table information. The projection $L_{h,d}$ is the operator in the permutation smoothing estimate: for every $K \in \mathbb{N}$ there are $d \ge 1$ and $h_0$ such that for all $h \ge h_0$, every coloring $z : V_h \to \{0,1,2\}$ using all three colors, every matching $M_0$ and every $f : \mathcal{M}_h \to \mathbb{R}$, the expectation over a uniformly random permutation $p$ of $V_h$ of the squared average of $M \mapsto (f - L_{h,d} f)(p M p^{-1})$ over the matchings $M$ with $\mathrm{tab}_M(z) = \mathrm{tab}_{M_0}(z)$ is at most $(2h)^{-2K}$ times the mean of $f^2$ over $\mathcal{M}_h$.
--
--   **Formalization Note** The definitions are `lowProjection h d`, the composite of `(matchingEquiv h).symm`, `(polynomialSpace h d).starProjection` and `matchingEquiv h`, and `tableEnergy s t f := 𝔼 z : Colorings V (Fin 3) s, (predicateAverage (fun M => M.table z.1 = t) f) ^ 2`. By Lean's conventions the inner average is $0$ when no matching has table $t$ under $z$, and the expectation over an empty set of colorings is $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/PermutationSmoothing.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/PermutationSmoothing.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingAffineLift mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials__MatchingAffineLift

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section Averages
variable {X : Type u_1} {Y : Type u_2} [Fintype X] [Fintype Y]
end Averages

noncomputable def lowProjection (h d : ℕ) : Module.End ℝ (Pairing (Vertices h) → ℝ) :=
  (matchingEquiv h).toLinearMap ∘ₗ (polynomialSpace h d).starProjection.toLinearMap ∘ₗ
    (matchingEquiv h).symm.toLinearMap

noncomputable def tableEnergy {V : Type u_6} [Fintype V] (s : Fin 3 → ℕ)
    (t : Fin 6 → ℕ) (f : Pairing V → ℝ) : ℝ :=
  𝔼 z : Colorings V (Fin 3) s, (predicateAverage (fun M => M.table z.1 = t) f)^2

end MatchingSmoothing

end OAI


