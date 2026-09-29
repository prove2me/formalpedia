-- Prove2me | Definitions.Def_ThreeOpSplitting_ConvexRates_Algorithm
-- name    : ThreeOpSplitting_ConvexRates_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:53:32.269634+00:00
-- url     : https://prove2.me/theorems/eb3ef1e0-b977-4b51-9c0a-9b449567e042
-- title:
--   Algorithm 2 with $\lambda_k \equiv 1$, the operator $T$ of Eq. (1.2), and the weighted ergodic iterate
-- statement:
--   Let $H$ be a real Hilbert space, $\gamma > 0$, and let $\operatorname{prox}_{\gamma f}, \operatorname{prox}_{\gamma g} : H \to H$ and $\nabla h : H \to H$ be given maps.
--
--   1. The **three-operator map** of Eq. (1.2), specialised to problem (3.1), is
--   $$T z = \operatorname{prox}_{\gamma f}\big(2\operatorname{prox}_{\gamma g}(z) - z - \gamma \nabla h(\operatorname{prox}_{\gamma g}(z))\big) + z - \operatorname{prox}_{\gamma g}(z).$$
--   2. **Algorithm 2** with relaxation parameters $\lambda_k \equiv 1$ starts from $z^0 \in H$ and, for $k = 0, 1, \dots$, sets
--   $$x^k_g = \operatorname{prox}_{\gamma g}(z^k),\qquad x^k_f = \operatorname{prox}_{\gamma f}\big(2x^k_g - z^k - \gamma\nabla h(x^k_g)\big),\qquad z^{k+1} = z^k + (x^k_f - x^k_g).$$
--   3. For a sequence $(x^i)_{i \ge 0}$ in $H$ the **weighted ergodic iterate** is
--   $$\bar x^k = \frac{2}{(k+1)(k+2)} \sum_{i=0}^{k} (i+1)\, x^i .$$
--
--   With $\lambda_k \equiv 1$ one has $z^{k+1} = T z^k$. Theorems 3.1 and 3.2 of Davis and Yin measure the objective error at $x^k_g$ and at the weighted ergodic iterate $\bar x^k_g$ of $(x^i_g)$.
--
--   **Formalization Note** The relaxation parameter is fixed to $\lambda_k \equiv 1$, the only case in which Theorems 3.1 and 3.2 are stated. The maps are free parameters here; the theorems require them to be the proximal maps of $f, g$ and the gradient of $h$. Iterates are indexed from $0$.
-- source:
--   Davis and Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017), https://doi.org/10.1007/s11228-017-0421-z, p. 830 Eq. (1.2); p. 838 Algorithm 2; pp. 839-840 Section 3.2 (weighted ergodic iterates)

import Mathlib

namespace ThreeOpSplitting.ConvexRates

/-- The three-operator map of Eq. (1.2) specialised to problem (3.1):
`T z = prox_{γf}(2 prox_{γg} z - z - γ ∇h(prox_{γg} z)) + z - prox_{γg} z`.
Here `proxf`, `proxg`, `gradh` stand for `prox_{γf}`, `prox_{γg}`, `∇h`. -/
noncomputable def splittingOp {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (proxf proxg gradh : H → H) (γ : ℝ) (z : H) : H :=
  proxf ((2 : ℝ) • proxg z - z - γ • gradh (proxg z)) + z - proxg z

/-- The sequence `(z^k)` of Algorithm 2 with relaxation `λ_k ≡ 1`, started at `z⁰`:
`z^{k+1} = z^k + (x^k_f - x^k_g)` with `x^k_g = prox_{γg}(z^k)` and
`x^k_f = prox_{γf}(2x^k_g - z^k - γ∇h(x^k_g))`. -/
noncomputable def algZ {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (proxf proxg gradh : H → H) (γ : ℝ) (z0 : H) : ℕ → H
  | 0 => z0
  | k + 1 =>
      algZ proxf proxg gradh γ z0 k +
        (proxf ((2 : ℝ) • proxg (algZ proxf proxg gradh γ z0 k) - algZ proxf proxg gradh γ z0 k
            - γ • gradh (proxg (algZ proxf proxg gradh γ z0 k)))
          - proxg (algZ proxf proxg gradh γ z0 k))

/-- Step 1 of Algorithm 2: `x^k_g = prox_{γg}(z^k)`. -/
noncomputable def algXg {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (proxf proxg gradh : H → H) (γ : ℝ) (z0 : H) (k : ℕ) : H :=
  proxg (algZ proxf proxg gradh γ z0 k)

/-- Step 2 of Algorithm 2: `x^k_f = prox_{γf}(2x^k_g - z^k - γ∇h(x^k_g))`. -/
noncomputable def algXf {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (proxf proxg gradh : H → H) (γ : ℝ) (z0 : H) (k : ℕ) : H :=
  proxf ((2 : ℝ) • algXg proxf proxg gradh γ z0 k - algZ proxf proxg gradh γ z0 k
    - γ • gradh (algXg proxf proxg gradh γ z0 k))

/-- The weighted ergodic iterate `x̄^k = 2/((k+1)(k+2)) ∑_{i=0}^k (i+1) x^i` (§3.2). -/
noncomputable def weightedErgodic {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (x : ℕ → H) (k : ℕ) : H :=
  (2 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) •
    ∑ i ∈ Finset.range (k + 1), ((i : ℝ) + 1) • x i

end ThreeOpSplitting.ConvexRates


