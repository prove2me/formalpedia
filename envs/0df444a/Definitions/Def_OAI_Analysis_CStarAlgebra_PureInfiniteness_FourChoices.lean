-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:30:41.658658+00:00
-- url     : https://prove2.me/theorems/69cbf00c-8141-44d6-b2a8-32f5c88d630a
-- title:
--   Four-choice data: four contractions in a hereditary subalgebra with prescribed moduli
-- statement:
--   Let $A$ be a unital $C^*$-algebra with its usual order. Notation: for self-adjoint $d$ and $\varepsilon\ge0$, $(d-\varepsilon)_+$ is $d$ under the functional calculus with $t\mapsto\max(t-\varepsilon,0)$; for $0\le l<u$, $\theta_{l,u}(d)$ is $d$ under the ramp $t\mapsto\min\bigl(1,\max(t-l,0)/(u-l)\bigr)$; $\delta(d)=\max(\tfrac12-d,0)$; and $\operatorname{Her}(h)$ is the norm closure of $\{hah^*: a\in A\}$. For $X\in A$, $B_0,\dots,B_3\in A$, a finite set $E\subseteq A$ and $\eta\in\mathbb{R}$ put
--
--   $$
--   \begin{aligned}
--   X_1&=(X-\tfrac1{16})_+, & V_1&=(X-\tfrac18)_+, & U_1&=X_1\,\delta(B_0B_0^*)^2X_1,\\
--   H_1&=\theta_{3/32,1/8}(X), & K_1&=\theta_{3/64,1/16}(X), & W&=\sqrt2\,B_0^*H_1+\sqrt{1-H_1^2},\\
--   Q&=\theta_{0,1}\bigl(K_1(1-WW^*)K_1\bigr), & X_2&=(Q-\tfrac12)_+, & R_2&=X_2\,\delta(B_2B_2^*)^2X_2,
--   \end{aligned}
--   $$
--
--   and
--
--   $$
--   \Sigma=(U_1-\eta)_+\Bigl(\sum_{w\in E}wV_1w^*\Bigr)(U_1-\eta)_+ .
--   $$
--
--   A four-choice for $(X,B,E,\eta)$ is a quadruple $T_0,\dots,T_3\in A$ such that
--
--   1. **Contractions in the working subalgebra.** $\|T_i\|\le1$ and $T_i\in\operatorname{Her}\bigl((X-\tfrac1{32})_+\bigr)$ for every $i$;
--   2. **First pair.** $T_0T_0^*=\theta_{\eta,2\eta}(\Sigma)$, $T_1T_1^*=T_0T_0^*$, $T_0T_1^*=0$, and $T_0^*T_0,\ T_1^*T_1\in\operatorname{Her}(V_1)$;
--   3. **Last pair.** $T_2^*T_3=0$, $T_2^*T_2=T_3^*T_3$, and $T_2T_2^*,\ T_3T_3^*\in\operatorname{Her}\bigl((R_2-\eta)_+\bigr)$;
--   4. **Norm condition.** For every $C^*$-algebra $D$, not necessarily unital, and every $*$-homomorphism $\pi:A\to D$,
--
--      $$
--      \|\pi(R_2)\|\ge4\eta\ \Longrightarrow\ \|\pi(T_2)\|=1 .
--      $$
--
--   Only $B_0$ and $B_2$ enter these conditions; the whole quadruple $B$ is the target that the $T_i$ are later compared with.
--
--   In the surrounding development a four-choice exists for every $\eta>0$ and every finite $E$ whenever $X\ge0$ and every positive element of $\operatorname{Her}\bigl((X-\tfrac1{32})_+\bigr)$ is properly infinite (meaning that $\operatorname{diag}(h,h)$ is a norm limit of $r_j^*hr_j$ with row vectors $r_j\in A^{1\times2}$). Four-choices for all pairs $(n,E)$, with $\eta=1/(n+1)$, are then combined along an ultrafilter to produce contractions $T_j$ in that hereditary subalgebra such that no unital Hilbert-space representation $\pi$ with $\|\pi(X)\|>\tfrac14$ satisfies $\pi(T_j)=\pi(B_j)$ for all $j$.
--
--   **Formalization Note** The structure is `FourChoice X B E η` with `B` indexed by `Fin 4`, `E` a `Finset A`, and fields `T`, `contractive`, `mem` (membership in `fourHer X`), `first_mod`, `first_equal`, `first_cross`, `outer₀`, `outer₁`, `last_cross`, `last_equal`, `outer₂`, `outer₃` and `last_norm`, expressed through `firstSandwich`, `firstU`, `firstV`, `lastR`, `cut` and `ramp`. In `last_norm` the algebra `D` ranges over a fixed universe `v`, a parameter of the structure, and `π` is a non-unital star-algebra homomorphism. All orders, on `A` and on target algebras, are Mathlib's spectral orders, fixed by local instances; the remaining sections of the file contain no declarations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/FourChoices.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/FourChoices.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndividualStrongInfiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
local instance fourChoicesPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance fourChoicesStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

end MainGap

namespace MainGap
variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
local instance fourChoicesMapDomainOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance fourChoicesMapDomainStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance fourChoicesMapCodomainOrder : PartialOrder D := CStarAlgebra.spectralOrder D
local instance fourChoicesMapCodomainStarOrder : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
variable (π : A →⋆ₐ[ℂ] D)

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
local instance fourChoiceStructureOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance fourChoiceStructureStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

universe v

structure FourChoice (X : A) (B : Fin 4 → A) (E : Finset A) (η : ℝ) where
  T : Fin 4 → A
  contractive : ∀ i, ‖T i‖ ≤ 1
  mem : ∀ i, T i ∈ fourHer X
  first_mod : T 0 * star (T 0) = ramp (firstSandwich (firstU X (B 0)) (firstV X) η E) η (2*η)
  first_equal : T 1 * star (T 1) = T 0 * star (T 0)
  first_cross : T 0 * star (T 1) = 0
  outer₀ : star (T 0) * T 0 ∈ Her (firstV X)
  outer₁ : star (T 1) * T 1 ∈ Her (firstV X)
  last_cross : star (T 2) * T 3 = 0
  last_equal : star (T 2) * T 2 = star (T 3) * T 3
  outer₂ : T 2 * star (T 2) ∈ Her (cut (lastR X (B 0) (B 2)) η)
  outer₃ : T 3 * star (T 3) ∈ Her (cut (lastR X (B 0) (B 2)) η)
  last_norm : ∀ {D : Type v} [NonUnitalCStarAlgebra D] (π : A →⋆ₙₐ[ℂ] D),
    4*η ≤ ‖π (lastR X (B 0) (B 2))‖ → ‖π (T 2)‖ = 1

namespace FourChoice
variable {X : A} {B : Fin 4 → A} {E : Finset A} {η : ℝ} (F : FourChoice.{v, _} X B E η)

variable {D : Type v} [CStarAlgebra D]
local instance fourChoiceRepresentationOrder : PartialOrder D := CStarAlgebra.spectralOrder D
local instance fourChoiceRepresentationStarOrder : StarOrderedRing D :=
  CStarAlgebra.spectralOrderedRing D
variable (π : A →⋆ₐ[ℂ] D) (hX : 0 ≤ X) (hη : 0 < η)
  (hmatch : ∀ i, π (F.T i) = π (B i))

end FourChoice
end MainGap

end

end OAI


