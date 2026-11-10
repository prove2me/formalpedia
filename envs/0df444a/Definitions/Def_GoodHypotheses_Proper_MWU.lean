-- Prove2me | Definitions.Def_GoodHypotheses_Proper_MWU
-- name    : GoodHypotheses_Proper_MWU
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:14:15.769717+00:00
-- url     : https://prove2.me/theorems/badb5b12-ebee-45c8-abd8-32ea7f1555fb
-- title:
--   The multiplicative weights update: weights, normalized weights and the weighted loss
-- statement:
--   With learning rate $\eta$ and losses $\ell^t_i$, the **MWU weights** are $W^1_i=1$ and $W^{t+1}_i=W^t_i\exp(-\eta\,\ell^t_i)$; the **normalized weights** are $\tilde W^t_i=W^t_i/\sum_jW^t_j$, and the **weighted loss** of round $t$ is $\langle\tilde W^t,\ell^t\rangle=\sum_i\tilde W^t_i\ell^t_i$ (§3.2). Stochastic MWU applies the same update to sampled losses $\hat\ell^t_i$ pathwise.
--
--   **Formalization Note.** Rounds are 0-based: `weight η ℓ t` is the weight vector in force during 0-based round `t` (the paper's $W^{t+1}$ with 0-based $t$), `weight η ℓ 0 = 1`. Losses are an arbitrary sequence; an adaptive choice depending on earlier weights is one such sequence.
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), §3.2, pp. 15–16

import Mathlib

namespace GoodHypotheses.Proper

/-!
# Multiplicative weights update (§3.2, p. 15)

Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, *A Good Way to Find Good Hypotheses*,
STOC 2027 submission (manuscript sha256 a428fbe0…), §3.2, pp. 15–16.

Rounds are `0`-based: round `t` of the paper (`t ∈ [T]`) is `t - 1` here. `weight η ℓ t` is the
paper's `W^{t+1}` with `0`-based `t`, i.e. the weights in force during (`0`-based) round `t`:
`weight η ℓ 0 = 1` (the paper's `W^1 := 1`) and
`weight η ℓ (t + 1) i = weight η ℓ t i · exp(−η ℓ_t,i)` (the paper's `W^{t+1}_i := W^t_i exp(−η ℓ^t_i)`).
The losses `ℓ t i` of round `t` may be any reals; an adaptive choice (depending on earlier
weights) is one particular sequence, so statements quantify over all sequences.
The same update applied to sampled losses `ℓ̂` (pathwise) is stochastic MWU (p. 16).
-/

/-- The (unnormalized) MWU weights in force during `0`-based round `t`. -/
noncomputable def weight {n : ℕ} (η : ℝ) (ℓ : ℕ → Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => fun _ => 1
  | t + 1 => fun i => weight η ℓ t i * Real.exp (-η * ℓ t i)

/-- The normalized weights `W̃^t_i = W^t_i / ∑_j W^t_j`. -/
noncomputable def normWeight {n : ℕ} (η : ℝ) (ℓ : ℕ → Fin n → ℝ) (t : ℕ) (i : Fin n) : ℝ :=
  weight η ℓ t i / ∑ j, weight η ℓ t j

/-- The weighted loss `⟨W̃^t, ℓ^t⟩` of round `t`, for the weights produced by the losses `ℓ`. -/
noncomputable def mixLoss {n : ℕ} (η : ℝ) (ℓ : ℕ → Fin n → ℝ) (t : ℕ) : ℝ :=
  ∑ i, normWeight η ℓ t i * ℓ t i

end GoodHypotheses.Proper


