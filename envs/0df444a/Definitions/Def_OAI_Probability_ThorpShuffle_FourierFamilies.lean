-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_FourierFamilies
-- name    : OAI_Probability_ThorpShuffle_FourierFamilies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T04:12:59.297575+00:00
-- url     : https://prove2.me/theorems/32ea15d4-9d8e-4716-ac9b-c76a9c693144
-- title:
--   Fourier families of irreducible unitary representations, character kernels and isotypic projectors
-- statement:
--   Let $G$ be a finite group. For a representation $\pi$ of $G$ on a finite-dimensional complex vector space, $\chi_\pi(g)=\operatorname{tr}\pi(g)$ denotes its character. For a representation $\rho$ of $G$ on any complex vector space $V$ and a function $f:G\to\mathbb{C}$, write
--   $$\rho(f)=\sum_{g\in G}f(g)\,\rho(g)\in\operatorname{End}_{\mathbb{C}}(V)$$
--   for the integrated operator (the action of $f$ regarded as an element of the group algebra).
--
--   1. **Fourier family.** A Fourier family for $G$ consists of a finite index set $\widehat{G}$ and, for every $i\in\widehat{G}$, a finite-dimensional complex inner product space $V_i$ carrying a representation $\rho_i$ of $G$, such that: (a) every $\rho_i$ is irreducible and $\dim_{\mathbb{C}}V_i>0$; (b) every $\rho_i$ is unitary, $\langle\rho_i(g)x,\rho_i(g)y\rangle=\langle x,y\rangle$ for all $g\in G$ and $x,y\in V_i$; (c) the $\rho_i$ are pairwise inequivalent, i.e. if $\rho_i$ and $\rho_j$ are isomorphic representations then $i=j$; (d) for every $g\in G$ the regular character identity holds:
--   $$\sum_{i\in\widehat{G}}\dim(V_i)\,\chi_{\rho_i}(g)=\begin{cases}|G|, & g=1,\\ 0, & g\ne 1.\end{cases}$$
--   2. **Degree.** $d_i=\dim_{\mathbb{C}}V_i$ for $i\in\widehat{G}$.
--   3. **Character kernel.** The function $k_i:G\to\mathbb{C}$,
--   $$k_i(g)=\frac{d_i}{|G|}\,\chi_{\rho_i}(g^{-1}).$$
--   4. **Isotypic projector.** For a representation $\rho$ of $G$ on a complex vector space $V$ and $i\in\widehat{G}$, the operator
--   $$P_i^{\rho}=\rho(k_i)=\frac{d_i}{|G|}\sum_{g\in G}\chi_{\rho_i}(g^{-1})\,\rho(g)\in\operatorname{End}_{\mathbb{C}}(V).$$
--
--   The right-hand side of (d) is the character of the regular representation of $G$. Since the characters of pairwise inequivalent irreducible representations are linearly independent, conditions (a), (c) and (d) together force $\widehat{G}$ to contain exactly one representative of every isomorphism class of irreducible representations, so a Fourier family is a concrete, unitary model of the dual of $G$. The kernel $k_i$ is a class function, and $P_i^{\rho}$ is the classical formula for the projection of $V$ onto its $\rho_i$-isotypic component; these projectors are the basic tool for decomposing averaging operators $\sum_g\nu(g)\rho(g)$ into irreducible pieces.
--
--   **Formalization Note** `Family G` is a structure (for `G : Type`) with fields `Index`, `Space`, `rep`, `positive`, `unitary`, `distinct` and `regular`, plus instance fields for finiteness of the index type, the inner product space structure, finite dimensionality and irreducibility (`Representation.IsIrreducible`). Item 2 is `degree`, item 3 is `kernel` and item 4 is `projector ρ i := integrated ρ (F.kernel i)`, where `integrated ρ f` is the integrated operator $\rho(f)$. The inner product is conjugate-linear in the first argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/FourierFamilies.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/FourierFamilies.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_PartitionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_DegreeBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_FirstMoment
import Definitions.Def_OAI_Probability_ThorpShuffle_Reynolds

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uG uE uV

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical

structure Family (G : Type) [Group G] [Fintype G] where
  Index : Type
  [finiteIndex : Fintype Index]
  Space : Index → Type
  [normed : ∀ i, NormedAddCommGroup (Space i)]
  [innerSpace : ∀ i, InnerProductSpace ℂ (Space i)]
  [finiteDim : ∀ i, FiniteDimensional ℂ (Space i)]
  rep : ∀ i, Representation ℂ G (Space i)
  [irreducible : ∀ i, Representation.IsIrreducible (rep i)]
  positive : ∀ i, 0 < Module.finrank ℂ (Space i)
  unitary : ∀ i g x y, ⟪rep i g x, rep i g y⟫_ℂ = ⟪x, y⟫_ℂ
  distinct : ∀ i j, Nonempty (Representation.Equiv (rep i) (rep j)) → i = j
  regular : ∀ g, ∑ i, (Module.finrank ℂ (Space i) : ℂ) * (rep i).character g =
    if g = 1 then (Fintype.card G : ℂ) else 0

attribute [instance] Family.finiteIndex Family.normed Family.innerSpace Family.finiteDim Family.irreducible

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

def degree (i : F.Index) : ℕ := Module.finrank ℂ (F.Space i)

def kernel (i : F.Index) (g : G) : ℂ :=
  (F.degree i : ℂ) * (Fintype.card G : ℂ)⁻¹ * (F.rep i).character g⁻¹

end Family
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

def projector (ρ : Representation ℂ G V) (i : F.Index) : Module.End ℂ V := integrated ρ (F.kernel i)

end Family
end Thorp.Fourier

end

end OAI


