-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_ProductProjectors
-- name    : OAI_Probability_ThorpShuffle_ProductProjectors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T04:17:09.561923+00:00
-- url     : https://prove2.me/theorems/1aaeb085-3ea9-4567-ab16-f591538edd11
-- title:
--   Splitting a vector by the coordinate of least irreducible degree in a representation of $H^I$
-- statement:
--   Let $H$ be a finite group with a Fourier family $(\rho_b)_{b\in\widehat{H}}$ (pairwise inequivalent irreducible unitary representations on finite-dimensional complex inner product spaces $V_b$, of dimensions $d_b>0$, whose degree-weighted characters add up to the regular character). Let $I$ be a finite nonempty set, $H^I$ the group of functions $I\to H$ under pointwise multiplication, and $\rho$ a representation of $H^I$ on a finite-dimensional complex inner product space $E$. For a multi-index $a:I\to\widehat{H}$, let $P_a^{\rho}=\sum_{g\in H^I}\prod_{i\in I}k_{a(i)}(g_i)\,\rho(g)$ be the joint projector, where $k_b(h)=\frac{d_b}{|H|}\operatorname{tr}\rho_b(h^{-1})$.
--
--   1. **Least factor.** For a multi-index $a$, $\operatorname{lf}(a)\in I$ is a coordinate at which the degree $d_{a(i)}$ is smallest:
--   $$d_{a(\operatorname{lf}(a))}\le d_{a(i)}\qquad\text{for all } i\in I$$
--   (one such coordinate is fixed once and for all when there are several).
--   2. **Split vector.** For $v\in E$ and $i\in I$,
--   $$v_i=\sum_{a:\,\operatorname{lf}(a)=i}P_a^{\rho}v,$$
--   the sum over all multi-indices $a:I\to\widehat{H}$ whose least factor is $i$.
--
--   Because the joint projectors sum to the identity, $v=\sum_{i\in I}v_i$, and when $\rho$ is unitary the pieces $v_i$ are mutually orthogonal, so $\sum_i\|v_i\|^2=\|v\|^2$. Moreover a nonzero joint projector $P_a^{\rho}$ forces $\prod_i d_{a(i)}\le\dim E$, so for every multi-index with $P_a^{\rho}\ne0$ the least degree $d=d_{a(\operatorname{lf}(a))}$ satisfies $d^{|I|}\le\dim E$. Consequently $v_i$ lies in the part of $E$ on which the $i$-th coordinate copy of $H$ acts only through irreducible representations of degree at most $(\dim E)^{1/|I|}$. This decomposition reduces norm bounds for averages over $H^I$ to bounds on low-degree irreducible representations of a single factor.
--
--   **Formalization Note** The Lean names are `leastFactor` (defined with `Classical.choose` applied to `Finset.exists_min_image`, which needs `[Nonempty I]`) and `splitVector ρ v i`, in the namespace `OAI.Thorp.Fourier.Family`. The finite-dimensional inner product structure on $E$ is part of the context but is not used by the formula itself.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/ProductProjectors.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/ProductProjectors.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_ThorpShuffle_FourierFamilies
import Definitions.Def_OAI_Probability_ThorpShuffle_JointProjectors

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uH uI uE uJ

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical
variable {H : Type uH} {I : Type uI} {E : Type uE} [Group H] [Fintype H] [Fintype I] [AddCommGroup E] [Module ℂ E]

end Thorp.Fourier

namespace Thorp.Fourier.Family
open scoped Classical
variable {H : Type} [Group H] [Fintype H] (F : Family H)
variable {I : Type} [Fintype I]

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

end Thorp.Fourier.Family

namespace Thorp.Fourier
open scoped Classical

namespace Family
variable {H I : Type} [Group H] [Fintype H] [Fintype I] [Nonempty I] (F : Family H)

noncomputable def leastFactor (a : I → F.Index) : I :=
  Classical.choose (Finset.exists_min_image Finset.univ (fun i => F.degree (a i)) Finset.univ_nonempty)

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

noncomputable def splitVector (ρ : Representation ℂ (I → H) E) (v : E) (i : I) : E :=
  ∑ a : I → F.Index, if F.leastFactor a = i then F.jointProjector ρ a v else 0

end Family
end Thorp.Fourier

end

end OAI


