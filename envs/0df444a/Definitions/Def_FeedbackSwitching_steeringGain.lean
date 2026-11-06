-- Prove2me | Definitions.Def_FeedbackSwitching_steeringGain
-- name    : FeedbackSwitching_steeringGain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:29.284957+00:00
-- url     : https://prove2.me/theorems/a31e0a70-9938-429c-a6d9-84b1b69747d8
-- title:
--   Steering gain $\Gamma(\ell_{1:h})$ (Eq. (38))
-- statement:
--   For a holding family of $(p,x)$, base rate $\kappa=2^{-m}$ and a loss block $\ell_1,\dots,\ell_h$, the **steering gain** is
--   $$
--   \Gamma(\ell_{1:h})=\mathbb E_\tau\sum_{1\le t<t'\le h}(1-\tau)^{t'-t}\,\big\langle\ell_t,(I-P_\tau)P_\tau^{\,t'-t-1}\ell_{t'}\big\rangle_p ,
--   $$
--   with $\tau$ drawn from the dyadic law (25). It is a deterministic function of the losses and the holding family; it measures how much steering lowers the expected loss of a block.
--
--   **Formalization Note** Rounds are 0-based; $\mathbb E_\tau$ is the finite sum over the atoms of the rate law.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Eq. (38), p.30 (PDF p.32)

import Mathlib
import Definitions.Def_FeedbackSwitching_holdingP
import Definitions.Def_FeedbackSwitching_rateLaw
open Matrix

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

**Steering gain** of a loss block `ℓ_1, …, ℓ_h` (Eq. (38), p.30 = PDF p.32):
`Γ(ℓ_{1:h}) = E_τ ∑_{1≤t<t'≤h} (1 − τ)^{t'−t} ⟨ℓ_t, (I − P_τ) P_τ^{t'−t−1} ℓ_{t'}⟩_p`,
with `τ` drawn from the dyadic law (25) for `κ = 2^{−m}` and `P_τ` the holding chain of `(p, x)`.

**Formalization Note.** Rounds are 0-based (`t < t' < h`); the expectation over `τ` is the finite
sum over the atoms of `rateProb m`. -/
noncomputable def steeringGain {K : ℕ} (p x : Fin K → ℝ) (m : ℕ) (ℓ : ℕ → Fin K → ℝ) (h : ℕ) :
    ℝ :=
  ∑ k : Fin (m + 1), rateProb m k *
    ∑ t ∈ Finset.range h, ∑ t' ∈ (Finset.range h).filter (fun t' => t < t'),
      (1 - rateVal m k) ^ (t' - t) *
        wInner p (ℓ t) ((1 - holdingP p x (rateVal m k)) *ᵥ
          ((holdingP p x (rateVal m k) ^ (t' - t - 1)) *ᵥ ℓ t'))

end FeedbackSwitching


