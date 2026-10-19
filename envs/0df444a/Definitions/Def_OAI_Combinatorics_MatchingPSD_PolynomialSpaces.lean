-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
-- name    : OAI_Combinatorics_MatchingPSD_PolynomialSpaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:40:52.399282+00:00
-- url     : https://prove2.me/theorems/c8c286d4-e7bd-4e48-8199-a0f0fa5e3b31
-- title:
--   Euclidean space of functions on perfect matchings of $2h$ points and its low-degree subspaces
-- statement:
--   Fix $h \in \mathbb{N}$ and let $V_h = \{0,\dots,h-1\} \times \{0,1\}$, a set of $2h$ vertices. A perfect matching of $V_h$ is encoded as a pairing, a permutation $M$ of $V_h$ with $M(M(v)) = v$ and $M(v) \neq v$ for all $v$; let $\mathcal{M}_h$ be the finite set of pairings. For an ordered pair $(a,b)$ of vertices, the edge coordinate is $x_{(a,b)}(M) = 1$ if $M(a) = b$ and $0$ otherwise. The module defines:
--
--   1. The **matching space** $\mathcal{H}_h = \ell^2(\mathcal{M}_h)$, the real functions on $\mathcal{M}_h$ with inner product $\langle f, g\rangle = \sum_{M \in \mathcal{M}_h} f(M) g(M)$, together with its linear identification with the plain function space $\mathbb{R}^{\mathcal{M}_h}$.
--   2. For $d \in \mathbb{N}$, the **polynomial space**
--   $$
--   \mathcal{P}_{h,d} = \operatorname{span}_{\mathbb{R}} \bigl\{ x_{e_1} x_{e_2} \cdots x_{e_m} : 0 \le m \le d,\ e_1, \dots, e_m \in V_h \times V_h \bigr\} \subseteq \mathcal{H}_h ,
--   $$
--   the functions on perfect matchings that are polynomials of degree at most $d$ in the edge coordinates (the empty product being the constant $1$).
--   3. For a permutation $p$ of $V_h$, the **relabelling isometry** $R_p$ of $\mathcal{H}_h$, $(R_p f)(M) = f(p^{-1} M p)$, induced by the relabelling $M \mapsto p M p^{-1}$ of matchings.
--
--   The polynomial spaces are invariant under all relabelling isometries, hence so are their orthogonal complements, the spaces of high-degree functions. This is the setting of the smoothing estimates: if $4k < h$ and a symmetric operator $A$ on $\mathcal{H}_h$ commutes with all $R_p$ and has $\operatorname{tr}(A^2) \le \binom{h}{k} a^2$ with $a \ge 0$, then $\langle f, A f\rangle \le a \|f\|^2$ for every $f$ orthogonal to $\mathcal{P}_{h,(4k)^2}$.
--
--   **Formalization Note** The definitions are `MatchingSpace h := EuclideanSpace ℝ (Pairing (Vertices h))`, `matchingEquiv h` (the linear equivalence `WithLp.linearEquiv`), `polynomialSpace h d` (the preimage of `lowDegree Pairing.edgeCoord d` under `matchingEquiv h`) and `relabelIso p := permIso (Pairing.relabelEquiv p)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/PolynomialSpaces.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/PolynomialSpaces.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression

namespace OAI

namespace MatchingSmoothing
open scoped RealInnerProductSpace

abbrev MatchingSpace (h : ℕ) := EuclideanSpace ℝ (Pairing (Vertices h))

noncomputable def matchingEquiv (h : ℕ) :
    MatchingSpace h ≃ₗ[ℝ] (Pairing (Vertices h) → ℝ) :=
  WithLp.linearEquiv 2 ℝ _

noncomputable def polynomialSpace (h d : ℕ) : Submodule ℝ (MatchingSpace h) :=
  (lowDegree Pairing.edgeCoord d).comap (matchingEquiv h).toLinearMap

noncomputable def relabelIso {h : ℕ} (p : Equiv.Perm (Vertices h)) :
    MatchingSpace h ≃ₗᵢ[ℝ] MatchingSpace h := permIso (Pairing.relabelEquiv p)

end MatchingSmoothing

end OAI


