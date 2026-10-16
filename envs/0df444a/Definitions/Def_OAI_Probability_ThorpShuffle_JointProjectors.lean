-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_JointProjectors
-- name    : OAI_Probability_ThorpShuffle_JointProjectors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T04:14:02.400163+00:00
-- url     : https://prove2.me/theorems/9c8cd6fc-4e1e-43a8-9f00-10f21c94fd61
-- title:
--   Joint character kernels, joint projectors and outer tensor products for the power group $H^I$
-- statement:
--   Let $H$ be a finite group with a Fourier family $(\rho_b)_{b\in\widehat{H}}$: a finite family of pairwise inequivalent irreducible unitary representations $\rho_b$ of $H$ on finite-dimensional complex inner product spaces $V_b$ of dimensions $d_b>0$, satisfying $\sum_b d_b\chi_{\rho_b}(h)=|H|$ for $h=1$ and $=0$ otherwise, where $\chi_\pi=\operatorname{tr}\pi$ is the character. Let $k_b(h)=\frac{d_b}{|H|}\chi_{\rho_b}(h^{-1})$ be its character kernels. Let $I$ be a finite set and let $H^I$ be the group of functions $g:I\to H$ under pointwise multiplication; write $g_i=g(i)$. A *multi-index* is a function $a:I\to\widehat{H}$.
--
--   1. **Joint kernel.** For a multi-index $a$, the function $K_a:H^I\to\mathbb{C}$,
--   $$K_a(g)=\prod_{i\in I}k_{a(i)}(g_i).$$
--   2. **Joint projector.** For a representation $\rho$ of $H^I$ on a complex vector space $E$,
--   $$P_a^{\rho}=\sum_{g\in H^I}K_a(g)\,\rho(g)\in\operatorname{End}_{\mathbb{C}}(E).$$
--   3. **Tensor representation along a list.** For a finite list $\ell$ of elements of $I$, a finite-dimensional representation $T_a(\ell)$ of $H^I$ defined recursively: $T_a(\text{empty list})$ is the trivial representation on $\mathbb{C}$, and for $\ell=(i,\ell')$ it is the tensor product $(\rho_{a(i)}\circ\mathrm{ev}_i)\otimes T_a(\ell')$, where $\mathrm{ev}_i(g)=g_i$. Thus for $\ell=(i_1,\dots,i_m)$ the group element $g$ acts on $V_{a(i_1)}\otimes\cdots\otimes V_{a(i_m)}\otimes\mathbb{C}$ by $\rho_{a(i_1)}(g_{i_1})\otimes\cdots\otimes\rho_{a(i_m)}(g_{i_m})\otimes\mathrm{id}$.
--   4. **Outer tensor product.** $\boxtimes_{i\in I}\rho_{a(i)}=T_a(\ell_I)$, where $\ell_I$ is a fixed enumeration of $I$ listing every element exactly once.
--
--   The character of the outer tensor product is $g\mapsto\prod_{i}\chi_{\rho_{a(i)}}(g_i)$, so $K_a$ is precisely the character kernel $\frac{\dim}{|H^I|}\chi(g^{-1})$ of the irreducible representation $\boxtimes_i\rho_{a(i)}$ of $H^I$, and $P_a^{\rho}$ is the projection of $E$ onto the corresponding isotypic component. These joint projectors refine the isotypic decomposition simultaneously in every coordinate copy of $H$; they are the tool for analysing representations of a product of groups, such as a product of symmetric groups acting blockwise.
--
--   **Formalization Note** The Lean names are `jointKernel`, `jointProjector`, `tensorList` and `tensorFamily`, in the namespace `OAI.Thorp.Fourier.Family`; representations of $H^I$ are `Representation ℂ (I → H) E`, and items 3 and 4 are objects of `FDRep ℂ (I → H)` built with `Representation.tprod`. The enumeration in item 4 is `Finset.univ.toList`, a noncanonical order that does not affect the representation up to isomorphism; the trailing factor $\mathbb{C}$ comes from the base case of the recursion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/JointProjectors.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/JointProjectors.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uE

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end Family
end Thorp.Fourier

namespace Thorp.Fourier.Family
open scoped Classical
variable {H : Type} [Group H] [Fintype H] (F : Family H)
variable {I : Type} [Fintype I]

def jointKernel (a : I → F.Index) (g : I → H) : ℂ := ∏ i, F.kernel (a i) (g i)

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

def jointProjector (ρ : Representation ℂ (I → H) E) (a : I → F.Index) : Module.End ℂ E :=
  integrated ρ (F.jointKernel a)

def tensorList (a : I → F.Index) : List I → FDRep ℂ (I → H)
  | [] => FDRep.of (Representation.trivial ℂ (I → H) ℂ)
  | i :: l => FDRep.of (Representation.tprod ((F.rep (a i)).comp (Pi.evalMonoidHom (fun _ : I => H) i)) (tensorList a l).ρ)

def tensorFamily (a : I → F.Index) : FDRep ℂ (I → H) := F.tensorList a Finset.univ.toList

end Thorp.Fourier.Family

end

end OAI


