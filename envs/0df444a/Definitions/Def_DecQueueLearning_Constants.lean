-- Prove2me | Definitions.Def_DecQueueLearning_Constants
-- name    : DecQueueLearning_Constants
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:39:33.792787+00:00
-- url     : https://prove2.me/theorems/96d78167-d9cb-4ce8-865d-ef9d5f976307
-- title:
--   Tuning constants $L_{\mathrm{check}}, L_{\mathrm{conv}}, L_{\mathrm{epoch}}$ (eq. (2)) and $C_1, C_2, \ell_0, T_0$ (eq. (5))
-- statement:
--   With $\xi=\varepsilon^2/(3200K^2(\log N+K))$, the algorithms use
--   $$
--   L_{\mathrm{check}}=\Big\lceil\max\Big(3,\Big(\frac{2}{\ln(1-\delta)}\Big)^2,\frac{2\ln\xi}{\ln(1-\delta)}\Big)\Big\rceil,\quad
--   L_{\mathrm{conv}}=\Big\lceil\frac{99KL_{\mathrm{check}}}{\varepsilon}(\log N+K)\Big\rceil,\quad
--   L_{\mathrm{epoch}}=\Big\lceil\Big(\frac{32}{\varepsilon}+1\Big)L_{\mathrm{conv}}\Big\rceil .
--   $$
--   Epoch $\ell\ge1$ consists of the slots $t_0,\dots,t_0+L_{\mathrm{epoch}}-1$ with $t_0=(\ell-1)L_{\mathrm{epoch}}+1$, and slot $t$ lies in epoch $\lfloor (t-1)/L_{\mathrm{epoch}}\rfloor+1$.
--
--   For the forced-exploration algorithm with parameter $\gamma\in(0,1)$, eq. (5) sets
--   $$
--   C_1=\max\Big(80,\frac{1}{K^2L_{\mathrm{check}}\delta^2}\Big),\quad C_2=\max\Big(80\ln(2NKL_{\mathrm{epoch}}),\frac{\ln(2L_{\mathrm{epoch}})}{K^2L_{\mathrm{check}}\delta^2}\Big),
--   $$
--   $$
--   \ell_0=\Big\lceil\max\Big((NKL_{\mathrm{epoch}})^{1/\gamma}+1,\ (2C_2)^{1/(1-\gamma)},\ \Big(\frac{4C_1}{1-\gamma}\Big)^{2/(1-\gamma)}\Big)\Big\rceil,\qquad T_0=\ell_0L_{\mathrm{epoch}}+1 .
--   $$
--
--   **Formalization Note** $\log$ is $\log_2$ and $\ln$ the natural logarithm. The proof of Lemma 3.6 (Appendix D.5) needs base 2 in $\log N$.
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, eq. (2) p. 9; eq. (5) p. 18; Algorithm 1 p. 10

import Mathlib

namespace DecQueueLearning

/-- The constant `ξ = ε² / (3200 K² (log N + K))`, arXiv:2206.03324v3, §3, p. 9.

**Formalization Note** `log` is the base-2 logarithm `Real.logb 2` (the proof of Lemma 3.6 in
Appendix D.5, p. 42, uses `p < log N` for the number `p` of halvings of `N`). -/
noncomputable def xi (N K : ℕ) (ε : ℝ) : ℝ :=
  ε ^ 2 / (3200 * (K : ℝ) ^ 2 * (Real.logb 2 N + K))

/-- The check period, eq. (2), arXiv:2206.03324v3, p. 9:
`L_check = ⌈max(3, (2 / ln(1 − δ))², 2 ln ξ / ln(1 − δ))⌉` (`ln` the natural logarithm). -/
noncomputable def Lcheck (N K : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈max 3 (max ((2 / Real.log (1 - δ)) ^ 2) (2 * Real.log (xi N K ε) / Real.log (1 - δ)))⌉₊

/-- The converging length, eq. (2), arXiv:2206.03324v3, p. 9:
`L_conv = ⌈(99 K L_check / ε)(log N + K)⌉`, with `log = log₂`. -/
noncomputable def Lconv (N K : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈(99 * (K : ℝ) * (Lcheck N K ε δ : ℝ) / ε) * (Real.logb 2 N + K)⌉₊

/-- The epoch length, eq. (2), arXiv:2206.03324v3, p. 9: `L_epoch = ⌈(32/ε + 1) L_conv⌉`. -/
noncomputable def Lepoch (N K : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈(32 / ε + 1) * (Lconv N K ε δ : ℝ)⌉₊

/-- The first time slot `t₀ = (ℓ − 1) L + 1` of epoch `ℓ ≥ 1` for epochs of length `L`
(Algorithm 1 and Algorithm 4, line 5, arXiv:2206.03324v3, pp. 10, 17). Time slots are `1, 2, …`. -/
def epochStart (L ℓ : ℕ) : ℕ := (ℓ - 1) * L + 1

/-- The epoch `ℓ = ⌊(t − 1)/L⌋ + 1` containing slot `t ≥ 1`, for epochs of length `L`. -/
def epochOf (L t : ℕ) : ℕ := (t - 1) / L + 1

/-- The constant `C₁ = max(80, 1/(K² L_check δ²))`, eq. (5), arXiv:2206.03324v3, p. 18. -/
noncomputable def C1 (N K : ℕ) (ε δ : ℝ) : ℝ :=
  max 80 (1 / ((K : ℝ) ^ 2 * (Lcheck N K ε δ : ℝ) * δ ^ 2))

/-- The constant `C₂ = max(80 ln(2 N K L_epoch), ln(2 L_epoch)/(K² L_check δ²))`, eq. (5),
arXiv:2206.03324v3, p. 18. -/
noncomputable def C2 (N K : ℕ) (ε δ : ℝ) : ℝ :=
  max (80 * Real.log (2 * N * K * (Lepoch N K ε δ : ℝ)))
    (Real.log (2 * (Lepoch N K ε δ : ℝ)) / ((K : ℝ) ^ 2 * (Lcheck N K ε δ : ℝ) * δ ^ 2))

/-- The epoch threshold, eq. (5), arXiv:2206.03324v3, p. 18:
`ℓ₀ = ⌈max((N K L_epoch)^{1/γ} + 1, (2 C₂)^{1/(1−γ)}, (4 C₁/(1 − γ))^{2/(1−γ)})⌉`. -/
noncomputable def ell0 (N K : ℕ) (ε δ γ : ℝ) : ℕ :=
  ⌈max (((N : ℝ) * K * (Lepoch N K ε δ : ℝ)) ^ (1 / γ) + 1)
    (max ((2 * C2 N K ε δ) ^ (1 / (1 - γ))) ((4 * C1 N K ε δ / (1 - γ)) ^ (2 / (1 - γ))))⌉₊

/-- The time slot `T₀ = ℓ₀ L_epoch + 1`, arXiv:2206.03324v3, p. 18. -/
noncomputable def T0 (N K : ℕ) (ε δ γ : ℝ) : ℕ :=
  ell0 N K ε δ γ * Lepoch N K ε δ + 1

end DecQueueLearning


