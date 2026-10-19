-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
-- name    : OAI_Combinatorics_MatchingPSD_EdgeMonomials
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:45:24.525967+00:00
-- url     : https://prove2.me/theorems/8cc8b2f5-1bb0-4153-a987-ca901c087712
-- title:
--   Edge monomials on perfect matchings and averaging over color-preserving permutations
-- statement:
--   Let $V$ be a set of vertices and $\mathcal{M}(V)$ the set of pairings of $V$, i.e. permutations $M$ with $M(M(v)) = v$ and $M(v) \neq v$ for all $v$ (perfect matchings with edges $\{v, M(v)\}$). For an ordered pair $e = (a,b)$ let $x_e(M) = 1$ if $M(a) = b$ and $x_e(M) = 0$ otherwise. The module defines:
--
--   1. For a finite list $\ell = \bigl((a_1,b_1), \dots, (a_m,b_m)\bigr)$ of ordered vertex pairs, the **edge monomial**
--   $$
--   x^{\ell}(M) = \prod_{j=1}^{m} x_{(a_j,b_j)}(M),
--   $$
--   which equals $1$ if $M$ contains all listed edges and $0$ otherwise (the empty list gives the constant $1$).
--   2. The predicate that $M$ **contains** $\ell$: $M(a_j) = b_j$ for every $j$.
--   3. The **support** of $\ell$, the finite set $\{a_1, \dots, a_m\} \cup \{b_1, \dots, b_m\}$ of vertices occurring in $\ell$.
--   4. For a coloring $z : V \to C$ with an arbitrary color set $C$, the **color stabilizer** $\mathrm{Stab}(z) = \{p \in \mathrm{Sym}(V) : z(p(v)) = z(v) \text{ for all } v \in V\}$, the subgroup of permutations preserving every color class.
--   5. For finite $V$ and a coloring $z$, the **color average** (Reynolds operator of the stabilizer), acting linearly on functions $f : \mathcal{M}(V) \to \mathbb{R}$ by
--   $$
--   (\mathcal{R}_z f)(M) = \frac{1}{|\mathrm{Stab}(z)|} \sum_{p \in \mathrm{Stab}(z)} f\bigl(p^{-1} M p\bigr).
--   $$
--
--   The space of polynomials of degree at most $d$ in the edge indicators is the span of the edge monomials of lists of length at most $d$. The operator $\mathcal{R}_z$ is unchanged by precomposing $f$ with a stabilizer relabelling, fixes the constant function $1$, and satisfies $\mathcal{R}_z(fg) = f\, \mathcal{R}_z(g)$ whenever $f$ is invariant under the stabilizer. For three colors, the color average of a polynomial of degree at most $d$ in the edge indicators turns out to be a polynomial of degree at most $d$ in the numbers of edges of $M$ joining the three pairs of distinct color classes; this is how averages of low-degree functions over color-table classes of matchings are shown to depend polynomially on the table.
--
--   **Formalization Note** The definitions are `Pairing.edgeMonomial l := (l.map edgeCoord).prod`, `Pairing.ContainsList`, `Pairing.edgeSupport` (a `Finset V`), `colorStabilizer z` (a `Subgroup (Equiv.Perm V)`) and `colorAverage z`, the endomorphism `|Stab(z)|⁻¹ • ∑ p, Pairing.act p` of `Pairing V → ℝ`, where `Pairing.act p f M = f (relabel p⁻¹ M)`. Decidability is classical.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/EdgeMonomials.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/EdgeMonomials.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
namespace Pairing
variable {V : Type u_1}

noncomputable def edgeMonomial (l : List (V × V)) : Pairing V → ℝ :=
  (l.map edgeCoord).prod

def ContainsList (M : Pairing V) (l : List (V × V)) : Prop :=
  ∀ e ∈ l, M.1 e.1 = e.2

noncomputable def edgeSupport (l : List (V × V)) : Finset V :=
  l.toFinset.image Prod.fst ∪ l.toFinset.image Prod.snd

end Pairing

section ColorAverage
variable {V : Type u_2} {C : Type u_3} [Fintype V]

def colorStabilizer (z : V → C) : Subgroup (Equiv.Perm V) where
  carrier := {p | ∀ v, z (p v) = z v}
  one_mem' := fun _ => rfl
  mul_mem' := by intro p q hp hq v; exact (hp (q v)).trans (hq v)
  inv_mem' := by intro p hp v; simpa using (hp (p⁻¹ v)).symm

noncomputable def colorAverage (z : V → C) : Module.End ℝ (Pairing V → ℝ) :=
  (Fintype.card (colorStabilizer z) : ℝ)⁻¹ •
    ∑ p : colorStabilizer z, (Pairing.act p.1).toLinearMap

end ColorAverage
end MatchingSmoothing

end OAI


