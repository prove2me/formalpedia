-- Prove2me | Definitions.Def_StrongWeakEq_Existence_BestResponse
-- name    : StrongWeakEq_Existence_BestResponse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:21.210771+00:00
-- url     : https://prove2.me/theorems/228e967a-8845-4399-9299-eaadda223225
-- title:
--   Proof of Theorem 3.3, p. 26 — the best-response correspondence Φ(Q)
-- statement:
--   Let $D_i$, $\mathcal Q$ and $F(Q)=(F(1,Q),\dots,F(N,Q))$ be as in the model of §2. For $Q\in\mathcal Q$ the best-response set is
--   $$\Phi(Q)=\Big\{R\in\mathcal Q:\ R_i\in\arg\max_{q\in D_i}\big[f(0,i,q)+F(Q)\cdot q\big]\ \ \forall i\in S\Big\}.$$
--
--   A fixed point $Q^*\in\Phi(Q^*)$ is exactly a generator satisfying $\Gamma^{Q^*}(Q^*_i)\ge\Gamma^{Q^*}(Q_i)$ for all $(i,Q)\in S\times\mathcal Q$, which is the characterization (3.10) of weak equilibria. The proof of Theorem 3.3 obtains such a fixed point from Kakutani–Fan's theorem.
--
--   **Formalization Note** The argmax is written out: $R\in\mathcal Q$ and $f(0,i,q)+F(Q)\cdot q\le f(0,i,R_i)+F(Q)\cdot R_i$ for every $i$ and every $q\in D_i$. The map is defined on all matrices; only its values at $Q\in\mathcal Q$ are used.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 26, proof of Theorem 3.3 (definition of Φ)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model

namespace StrongWeakEq.Existence

/-- Proof of Theorem 3.3, p. 26: the best-response map
`Φ(Q) = {R ∈ 𝒬 : Rᵢ ∈ argmax_{q ∈ Dᵢ} [f(0,i,q) + F(Q) · q] ∀ i}`. -/
def bestResponse {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (Q : Matrix (Fin N) (Fin N) ℝ) :
    Set (Matrix (Fin N) (Fin N) ℝ) :=
  {R ∈ Controls D | ∀ i, ∀ q ∈ D i,
    f 0 i q + q ⬝ᵥ (fun j => payoff f Q j) ≤ f 0 i (R i) + R i ⬝ᵥ (fun j => payoff f Q j)}

end StrongWeakEq.Existence


