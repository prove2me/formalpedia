-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:14:37.793886+00:00
-- url     : https://prove2.me/theorems/7aea0026-a692-4dc7-96e4-b9b9485d8568
-- title:
--   The real part map as a contractive real-linear operator on a unital $C^*$-algebra
-- statement:
--   Let $A$ be a unital $C^*$-algebra, regarded as a real Banach space by restricting scalars to $\mathbb{R}$. The real part of $a\in A$ is the self-adjoint element
--
--   $$
--   \operatorname{Re}(a)=\frac{a+a^*}{2}\in A_{\mathrm{sa}}=\{\,b\in A : b^*=b\,\}.
--   $$
--
--   The file packages the real part as a bounded real-linear operator $\operatorname{Re}:A\to A$ with
--
--   $$
--   \|\operatorname{Re}(a)\|\le\|a\|\qquad(a\in A),
--   $$
--
--   so that its operator norm is at most $1$, together with the evaluation rule $\operatorname{Re}(a)=\tfrac12(a+a^*)$. The map is $\mathbb{R}$-linear but not $\mathbb{C}$-linear.
--
--   Composing a bounded real functional $F:A\to\mathbb{R}$ with $\operatorname{Re}$ gives a real functional $F\circ\operatorname{Re}$ of norm at most $\|F\|$ that agrees with $F$ on $A_{\mathrm{sa}}$; its complexification is a complex linear functional with the same values on self-adjoint elements. In the surrounding development this turns a Hahn–Banach norming functional into a positive one: for every positive element $d$ of a nontrivial unital $C^*$-algebra there is a positive linear functional $f$ with $|f(a)|\le\|a\|$ for all $a$ and $f(d)=\|d\|$.
--
--   **Formalization Note** The Lean name is `realPartCLM`, a continuous real-linear map from `A` to `A` obtained from Mathlib's `realPart` (which takes values in the self-adjoint part) followed by the inclusion, made continuous with bound constant $1$ via `mkContinuous`. The simp lemma `realPartCLM_apply` identifies its value with `realPart a`. The order on `A` present in the surrounding section plays no role in this definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/PositiveFunctional.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/PositiveFunctional.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndividualStrongInfiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

def realPartCLM : A →L[ℝ] A :=
  ((selfAdjoint.submodule ℝ A).subtype.comp (realPart : A →ₗ[ℝ] selfAdjoint A)).mkContinuous 1
    (fun a => by
      change ‖(realPart a : A)‖ ≤ 1 * ‖a‖
      simpa using realPart.norm_le a)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma realPartCLM_apply (a : A) : realPartCLM a = (realPart a : A) := rfl

end MainGap

end

end OAI


