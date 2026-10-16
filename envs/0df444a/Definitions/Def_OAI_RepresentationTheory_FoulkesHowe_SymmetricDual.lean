-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
-- name    : OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:19:51.522075+00:00
-- url     : https://prove2.me/theorems/20be6069-b2a1-4c60-97a3-bde0cd671a5c
-- title:
--   A map $\mathrm{Sym}^n(V^*)\to(\mathrm{Sym}^n V)^*$ that evaluates pure powers correctly is injective
-- statement:
--   Let $V$ be a finite-dimensional complex vector space with dual space $V^*=\mathrm{Hom}_{\mathbb{C}}(V,\mathbb{C})$. For a complex vector space $U$ let $S(U)$ be its symmetric algebra over $\mathbb{C}$ and, for $n\in\mathbb{N}$, let $\mathrm{Sym}^n U\subseteq S(U)$ be the linear span of the products $u_0u_1\cdots u_{n-1}$ of $n$ elements of $U$. For $x\in V$ write $x^n=x\,x\cdots x\in\mathrm{Sym}^n V$ ($n$ factors). For $p\in S(V^*)$ and $x\in V$ let $p(x)\in\mathbb{C}$ be the image of $p$ under the $\mathbb{C}$-algebra homomorphism $S(V^*)\to\mathbb{C}$ that extends $\varphi\mapsto\varphi(x)$; this is the value at $x$ of $p$ regarded as a polynomial function on $V$.
--
--   **Theorem.** Let $n\in\mathbb{N}$ and let $B:\mathrm{Sym}^n(V^*)\to(\mathrm{Sym}^n V)^*$ be a $\mathbb{C}$-linear map such that
--   $$B(p)\bigl(x^n\bigr)=p(x)\qquad\text{for all }p\in\mathrm{Sym}^n(V^*)\text{ and all }x\in V.$$
--   Then $B$ is injective.
--
--   The hypothesis only constrains $B$ on pure powers $x^n$, which is where a pairing between symmetric powers is easiest to compute. Together with the equality $\dim\mathrm{Sym}^n(V^*)=\dim(\mathrm{Sym}^n V)^*$, the theorem upgrades such a map to a linear isomorphism, which yields the perfect duality between $\mathrm{Sym}^n(V^*)$ and $\mathrm{Sym}^n V$.
--
--   **Formalization Note** The pure power $x^n$ is `symMonomial n V (fun _ => x)` and $p(x)$ is `SymmetricAlgebra.lift (Module.Dual.eval ℂ V x)` applied to the underlying element of `p` in the symmetric algebra of the dual.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/SymmetricDual.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/SymmetricDual.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation

namespace OAI

noncomputable section
universe u
namespace Problem346

variable (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A symmetric-power duality map is injective as soon as evaluation on pure powers agrees
with evaluation in the symmetric algebra. -/
theorem symPowDual_injective_of_pure_evaluation (n : ℕ)
    (B : SymPow n (Module.Dual ℂ V) →ₗ[ℂ] Module.Dual ℂ (SymPow n V))
    (hB : ∀ (p : SymPow n (Module.Dual ℂ V)) (x : V),
      B p (symMonomial n V (fun _ => x)) =
        SymmetricAlgebra.lift (Module.Dual.eval ℂ V x) p.val) :
    Function.Injective B := by
  intro p q hpq
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply symAlg_dual_eq_zero_of_eval_eq_zero V
  intro x
  rw [map_sub, ← hB p x, ← hB q x, hpq, sub_self]

end Problem346

end

end OAI


