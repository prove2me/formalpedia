-- Prove2me | Definitions.Def_ChoicePAC_MidPoint_OPAC
-- name    : ChoicePAC_MidPoint_OPAC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:20.322083+00:00
-- url     : https://prove2.me/theorems/541d5c9a-c4a7-4e8d-ab7f-af4590b51209
-- title:
--   OPAC on one window: admissible probabilities, expectation of a function of the consumption, conditional mean
-- statement:
--   **OPAC** (Sec. 5.3, pp. 328–329) is PAC without the capacity check. On a window $[s,t)$ of length $\ell = t-s$ in the $k$-th system, with constant allocation probabilities $p$, the window holds $N \sim \mathrm{Poisson}(k\Lambda\ell)$ arrivals, $\Lambda = \sum_q\lambda_q$, whose types are i.i.d. with law $\lambda_q/\Lambda$; an arrival of type $q$ is presented offer $j \in S_q$ with probability $p_j$ and then consumes an independent copy of $A^j$. Let $\zeta = \sum_j \zeta^j(s,t)$ be the total consumption vector.
--
--   1. *Admissible probabilities:* $p_j \ge 0$ and $\sum_{j\in S_q} p_j \le 1$ for every type $q$.
--   2. $\mathbb E[f(\zeta)]$ for a function $f$ of the consumption vector, computed arrival by arrival from $\zeta = 0$.
--   3. The conditional mean of the consumption of resource $i$ (App. B.3, p. 334):
--   $$\big(\bar A\,\mathbb E[N(s,t)\mid\mathfrak F_s]\big)_i = \sum_j k\lambda_{q(j)}(t-s)p_j\bar A_{ij}.$$
--
--   The deviation $\tilde\Delta_i(s,t) = \zeta_i - \sum_j k\lambda_{q(j)}(t-s)p_j\bar A_{ij}$ is the object of Lemmas B.1 and C.4.
--
--   **Formalization Note** Conditioning on $\mathfrak F_s$ disappears: given the history up to $s$, OPAC's window is a fresh Poisson window with the probabilities $p$ fixed at the last re-solve, so the conditional expectation is this expectation with those $p$. The window uses the same Poisson representation as the PAC window value.
-- source:
--   Jasin, Kumar, A Re-Solving Heuristic with Bounded Revenue Loss for Network Revenue Management with Customer Choice, Math. Oper. Res. 37(2), 2012, Sec. 5.3, pp. 328–329; App. B.3, p. 334; Lemma C.4, p. 338

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model

namespace ChoicePAC.MidPoint

open MeasureTheory Matrix

namespace Instance

variable {NT n m : ℕ} (I : Instance NT n m)

/-- Admissible offer probabilities: `p_j ≥ 0` and `Σ_{j∈S_q} p_j ≤ 1` for every type `q` (the
probabilities `Y_j / ((1 − t) k λ_{q(j)})` used by PAC and OPAC always satisfy this). -/
def AdmissibleProbs (p : Fin n → ℝ) : Prop :=
  0 ≤ p ∧ ∀ q, ∑ j ∈ I.S q, p j ≤ 1

/-- One arrival under OPAC (Sec. 5.3, pp. 328–329): PAC without the capacity check. The state is
the consumption `acc` accumulated so far; the arrival has type `q` with probability `λ_q / Λ`,
offer `j ∈ S_q` is presented with probability `p_j` and then consumes `A^j ~ D_j`. -/
noncomputable def opacStep (p : Fin n → ℝ) (W : (Fin m → ℝ) → ℝ) (acc : Fin m → ℝ) : ℝ :=
  ∑ q, (I.lam q / I.Λ) *
    ((1 - ∑ j ∈ I.S q, p j) * W acc + ∑ j ∈ I.S q, p j * ∫ a, W (acc + a) ∂(I.D j))

/-- `E[f(ζ)]`, where `ζ = Σ_j ζ^j(s, t)` is the total consumption vector of OPAC during a window
`[s, t)` of length `ℓ = t − s` in the `k`-th system with constant allocation probabilities `p`
(App. B.3, p. 334; Lemma C.4, p. 338). The window holds `N ~ Poisson(k Λ ℓ)` arrivals with i.i.d.
types of law `λ_q / Λ`. -/
noncomputable def opacExpect (k : ℕ) (ℓ : ℝ) (p : Fin n → ℝ) (f : (Fin m → ℝ) → ℝ) : ℝ :=
  ∑' N : ℕ, poissonWeight ((k : ℝ) * I.Λ * ℓ) N * (I.opacStep p)^[N] f 0

/-- The conditional mean of the OPAC consumption of resource `i` on the window:
`(Ā E[N(s,t) | 𝔉_s])_i = Σ_j k λ_{q(j)} (t − s) p_j Ā_ij` (App. B.3, p. 334). -/
noncomputable def opacMean (k : ℕ) (ℓ : ℝ) (p : Fin n → ℝ) (i : Fin m) : ℝ :=
  ∑ j, (k : ℝ) * I.lam (I.typ j) * ℓ * p j * I.Abar i j

end Instance

end ChoicePAC.MidPoint


