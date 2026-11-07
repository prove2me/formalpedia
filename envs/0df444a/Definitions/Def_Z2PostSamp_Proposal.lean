-- Prove2me | Definitions.Def_Z2PostSamp_Proposal
-- name    : Z2PostSamp_Proposal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:24.872203+00:00
-- url     : https://prove2.me/theorems/5e750079-d104-4914-9ead-89251847ab42
-- title:
--   The sequential proposal $Q$ of (2.6)
-- statement:
--   Given logit vectors $\widehat\ell^{(k)}(x_{S_k})$ for $k_0\le k<n$, the proposal draws the first $k_0$ revealed signs uniformly and then the sign at $I_{k+1}$ with probability $q_k(b\mid x_{S_k})=e^{b\widehat\ell}/(2\cosh\widehat\ell)$, $\widehat\ell=\widehat\ell^{(k)}_{I_{k+1}}(x_{S_k})$. Its density is
--
--   $$Q(x)=2^{-k_0}\prod_{k=k_0}^{n-1}\frac{\exp\big(x_{I_{k+1}}\widehat\ell^{(k)}_{I_{k+1}}(x_{S_k})\big)}{2\cosh\big(\widehat\ell^{(k)}_{I_{k+1}}(x_{S_k})\big)} .$$
--
--   This is the warm proposal that the independence Metropolis correction turns into an approximate posterior sample.
--
--   **Formalization Note** The logit maps are an argument; $Q$ is a probability exactly when each map depends on $x$ only through the prefix $x_{S_k}$, which the statements assume.
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), §2.2, p.8, (2.5)–(2.6)

import Mathlib
import Definitions.Def_CriticalSK

set_option autoImplicit false

open OAI.CriticalSK

namespace Z2PostSamp

noncomputable section

/-!
# The sequential proposal `Q` of (2.6)

Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), §2.2, p.8: the first `k₀` revealed signs are independent uniform, and the sign at
`I_{k+1}` is drawn from (2.5) `q_k(b | x_{S_k}) = exp(b ℓ̂_{I_{k+1}}^{(k)}(x_{S_k})) /
(2 cosh ℓ̂_{I_{k+1}}^{(k)}(x_{S_k}))`, so (2.6)
`Q(x) = 2^{−k₀} Π_{k=k₀}^{n−1} exp(x_{I_{k+1}} ℓ̂^{(k)}_{I_{k+1}}(x_{S_k})) / (2 cosh ℓ̂^{(k)}_{I_{k+1}}(x_{S_k}))`.

**Formalization Note.** `lh k x` is the logit vector `ℓ̂^{(k)}(x_{S_k})` for the fixed data, order and
record (suppressed, as on p.8). The product runs over the 0-based positions `a` with `k₀ ≤ a < n`,
whose site `I a` is the paper's `I_{a+1}`. `Q` is a probability on `{±1}ⁿ` when each `lh k` depends on
`x` only through the prefix `x_{S_k}` (`IsPrefixFn`); that is a hypothesis of the statements, not of
the definition.
-/

/-- The proposal density `Q(x)` of (2.6). -/
def propQ {n : ℕ} (k0 : ℕ) (I : Equiv.Perm (Fin n)) (lh : ℕ → Spin n → Fin n → ℝ) (x : Spin n) :
    ℝ :=
  (1 / 2 : ℝ) ^ k0 * ∏ a : Fin n, if k0 ≤ a.val then
      Real.exp (spinValue (x (I a)) * lh a.val x (I a)) / (2 * Real.cosh (lh a.val x (I a)))
    else 1

end

end Z2PostSamp


