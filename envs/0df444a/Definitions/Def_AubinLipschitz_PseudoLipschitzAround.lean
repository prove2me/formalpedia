-- Prove2me | Definitions.Def_AubinLipschitz_PseudoLipschitzAround
-- name    : AubinLipschitz_PseudoLipschitzAround
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:19.933573+00:00
-- url     : https://prove2.me/theorems/b440bee5-6f31-4273-a0eb-fce3f22e62e0
-- title:
--   §3, Definition 1 — pseudo-Lipschitz set-valued map
-- statement:
--   Let $S=F^{-1}$ be a set-valued map from a normed space $P$ to a normed space $Z$ and let $x_0\in S(y_0)$. Write $\underline d(A,B)=\sup_{x\in A}\inf_{y\in B}\|x-y\|$. The map $S$ is **pseudo-Lipschitz around $(y_0,x_0)$** if there exist a neighbourhood $\mathcal W$ of $y_0$, two neighbourhoods $\mathcal U\subset\mathcal V$ of $x_0$ and a constant $\ell>0$ such that
--
--   1. $S(y)\cap\mathcal U\neq\emptyset$ for every $y\in\mathcal W$;
--   2. $\underline d\big(S(y_1)\cap\mathcal U,\ S(y_2)\cap\mathcal V\big)\le\ell\|y_1-y_2\|$ for all $y_1,y_2\in\mathcal W$.
--
--   This is the property now usually called the Aubin property. It is weaker than Lipschitz continuity of the whole map: only the part of the value near $x_0$ is controlled, and an excess, not a Hausdorff distance, is bounded.
--
--   **Formalization Note** The excess is written pointwise with the extended distance to a set, which equals $+\infty$ when the set is empty. So clause 2 does not hold vacuously when $S(y_2)\cap\mathcal V$ is empty.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, Definition 1, (1), p.22

import Mathlib

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, Definition 1, (1), p.22, for a set-valued map `S = F⁻¹ : P ⇉ Z`: `S` is
*pseudo-Lipschitz around `(y₀, x₀)`* when `x₀ ∈ S(y₀)` and there are a neighbourhood `W` of `y₀`,
neighbourhoods `U ⊆ V` of `x₀` and `ℓ > 0` with
(i) `S(y) ∩ U ≠ ∅` for every `y ∈ W`, and
(ii) `d(S(y₁) ∩ U, S(y₂) ∩ V) ≤ ℓ ‖y₁ − y₂‖` for all `y₁, y₂ ∈ W`,
where `d(A, B) = sup_{x ∈ A} inf_{y ∈ B} ‖x − y‖`.

**Formalization Note** `d` is written pointwise with `Metric.infEDist`, whose value on an empty
target set is `⊤`, so (ii) is not vacuous when `S(y₂) ∩ V` is empty; the supremum over the empty
set is `0`, as in the paper. `x₀ ∈ S(y₀)` is the paper's precondition "`(x₀, y₀)` belongs to the
graph of `F`". -/
def PseudoLipschitzAround {P Z : Type*} [NormedAddCommGroup P] [NormedAddCommGroup Z]
    (S : P → Set Z) (y₀ : P) (x₀ : Z) : Prop :=
  x₀ ∈ S y₀ ∧ ∃ W ∈ nhds y₀, ∃ U ∈ nhds x₀, ∃ V ∈ nhds x₀, U ⊆ V ∧ ∃ ℓ : ℝ, 0 < ℓ ∧
    (∀ y ∈ W, (S y ∩ U).Nonempty) ∧
    ∀ y₁ ∈ W, ∀ y₂ ∈ W, ∀ x ∈ S y₁ ∩ U,
      Metric.infEDist x (S y₂ ∩ V) ≤ ENNReal.ofReal (ℓ * ‖y₁ - y₂‖)

end AubinLipschitz


