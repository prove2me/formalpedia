-- Prove2me | Definitions.Def_AssortSearch_SearchQC_ProofTerms
-- name    : AssortSearch_SearchQC_ProofTerms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:26.379986+00:00
-- url     : https://prove2.me/theorems/0b3bb7b6-5f4a-4df9-ad44-0efa4541deee
-- title:
--   The functions $\bar H, J, f, N, g, D, K$ of the proof of Theorem 5
-- statement:
--   These are the auxiliary functions in the proof of Theorem 5 (pp. 14–15). Throughout, $\lambda>0$, $V_S>0$ is the preference mass $v_0+\sum_{i\in S}v_i$ of the current assortment, $x=v_j\ge 0$ is the preference of the added variant $j$, $m$ is the common margin and $c'$ is the derivative of the cost function $c$.
--
--   1. $\bar H(v_j)=1-H(\bar U,S_j)=1-e^{-\lambda(v_j+V_S)}$, and its derivative $\bar H'(v_j)=\lambda e^{-\lambda(v_j+V_S)}$.
--   2. The coefficients
--   $$J(v_j)=\frac{\bar H(v_j)V_S+\bar H'(v_j)v_j(v_j+V_S)}{(v_j+V_S)^2},\qquad N(v_j)=\frac{\bar H'(v_j)(v_j+V_S)-\bar H(v_j)}{(v_j+V_S)^2}.$$
--   3. The marginal-profit terms
--   $$f(v_j)=m-c'\Bigl(\frac{\bar H(v_j)v_j}{v_j+V_S}\Bigr),\qquad g(v_j)=m\sum_{i\in S}v_i-\sum_{i\in S}c'\Bigl(\frac{\bar H(v_j)v_i}{v_j+V_S}\Bigr)v_i.$$
--   4. The functions of (8)–(9)
--   $$D(v_j)=e^{\lambda(v_j+V_S)}-1+\frac{\lambda v_j}{V_S}(v_j+V_S),\qquad K(v_j)=e^{\lambda(v_j+V_S)}-1-\lambda(v_j+V_S).$$
--
--   The arguments of $c'$ are exactly the demands $q_j^{si}(v_j)$ and $q_i^{si}(v_j)$ of the variants in $S_j$, so $h^{si\prime}=Jf+Ng$ is the derivative of the profit change, written as in display (7).
--
--   **Formalization Note** $V_S$ enters as a real parameter `VS`; the milestones instantiate it with $v_0+\sum_{i\in S}v_i$. The derivative $c'$ is Mathlib's `deriv c`, which is the true derivative wherever $c$ is differentiable; the milestones assume differentiability on $(0,1)$, where every argument of $c'$ lies when $v_j>0$. $\bar H'$ is written out explicitly rather than as `deriv`.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), pp. 14-15 (PDF 16-17), proof of Theorem 5, displays (7)-(9)

import Mathlib

namespace AssortSearch.SearchQC

/-- `H̄(v_j) = 1 - H(Ū, S_j) = 1 - exp(-λ (v_j + V_S))` (p. 14), with `x = v_j`, `VS = V_S`. -/
noncomputable def Hbar (lam VS x : ℝ) : ℝ :=
  1 - Real.exp (-(lam * (x + VS)))

/-- `H̄'(v_j) = λ exp(-λ (v_j + V_S))`, the derivative of `H̄` in `v_j`. -/
noncomputable def HbarDeriv (lam VS x : ℝ) : ℝ :=
  lam * Real.exp (-(lam * (x + VS)))

/-- `J(v_j) = (H̄(v_j) V_S + H̄'(v_j) v_j (v_j + V_S)) / (v_j + V_S)^2` (p. 14). -/
noncomputable def Jfn (lam VS x : ℝ) : ℝ :=
  (Hbar lam VS x * VS + HbarDeriv lam VS x * x * (x + VS)) / (x + VS) ^ 2

/-- The paper's `f(v_j) = m - c'(H̄(v_j) v_j / (v_j + V_S))` (p. 15), `c' = deriv c`. -/
noncomputable def fFn (m : ℝ) (c : ℝ → ℝ) (lam VS x : ℝ) : ℝ :=
  m - deriv c (Hbar lam VS x * x / (x + VS))

/-- `N(v_j) = (H̄'(v_j) (v_j + V_S) - H̄(v_j)) / (v_j + V_S)^2` (p. 15). -/
noncomputable def Nfn (lam VS x : ℝ) : ℝ :=
  (HbarDeriv lam VS x * (x + VS) - Hbar lam VS x) / (x + VS) ^ 2

/-- `g(v_j) = m ∑_{i∈S} v_i - ∑_{i∈S} c'(H̄(v_j) v_i / (v_j + V_S)) v_i` (p. 15). -/
noncomputable def gFn {n : ℕ} (m : ℝ) (c : ℝ → ℝ) (lam : ℝ) (v : Fin n → ℝ)
    (S : Finset (Fin n)) (VS x : ℝ) : ℝ :=
  m * ∑ i ∈ S, v i - ∑ i ∈ S, deriv c (Hbar lam VS x * v i / (x + VS)) * v i

/-- `D(v_j) = e^{λ(v_j+V_S)} - 1 + (λ v_j / V_S)(v_j + V_S)` (p. 15). -/
noncomputable def Dfn (lam VS x : ℝ) : ℝ :=
  Real.exp (lam * (x + VS)) - 1 + lam * x / VS * (x + VS)

/-- `K(v_j) = e^{λ(v_j+V_S)} - 1 - λ (v_j + V_S)` (p. 15). -/
noncomputable def Kfn (lam VS x : ℝ) : ℝ :=
  Real.exp (lam * (x + VS)) - 1 - lam * (x + VS)

end AssortSearch.SearchQC


