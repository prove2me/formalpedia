-- Prove2me | Definitions.Def_QPVEntanglement_securityBound
-- name    : QPVEntanglement_securityBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:26:43.521174+00:00
-- url     : https://prove2.me/theorems/0b29c1b3-54b4-41af-9090-019dedd2165e
-- title:
--   The qubit bound $B(\lambda)$, the threshold $\nu(\lambda)$ and $m=\omega(\log_2^2\lambda)$
-- statement:
--   For parameter functions $m,R_H,s:\mathbb N\to\mathbb N$ and a constant $\kappa$,
--
--   $$B(\lambda)=\Big\lfloor\frac{m(\lambda)}{\lceil\log_2^2\lambda\rceil}\Big\rfloor\,R_H(\lambda)\,\big(2\kappa(s(\lambda)-2.5)-1\big),$$
--
--   and $\nu(\lambda)=(1-10^{-7})^{\lceil\log_2^2\lambda\rceil}$. The condition $m=\omega(\log_2^2\lambda)$ means $m(\lambda)/\log_2^2\lambda\to\infty$.
--
--   These are the bound (23)–(24) and the success threshold of Theorem 7.
--
--   **Formalization Note** $\lfloor\cdot\rfloor$ is natural-number division ($m/0=0$ at $\lambda\le1$), $\lceil\cdot\rceil$ is `Nat.ceil`, $\log_2$ is `Real.logb 2`; $B$ is real.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Theorem 7, eqs. (23)–(24), p.38; proof of Theorem 7, p.38

import Mathlib

set_option autoImplicit false

namespace QPVEntanglement

/-- `⌈log₂² λ⌉`, the number of blocks in Theorem 7 (p.38, p.45). -/
noncomputable def logSqCeil (lam : ℕ) : ℕ := ⌈(Real.logb 2 (lam : ℝ)) ^ 2⌉₊

/-- The success threshold `ν(λ) = (1 − 10⁻⁷)^{⌈log₂² λ⌉}` of Theorem 7 (p.38: "Let
`ν(λ) := (1 − 10⁻⁷)^{⌈log₂²(λ)⌉}`, which is negligible"). -/
noncomputable def nu (lam : ℕ) : ℝ := (1 - 1 / 10 ^ 7 : ℝ) ^ logSqCeil lam

/-- `m = ω(log₂² λ)`: `m(λ) / log₂²(λ) → ∞` (Theorem 7, p.38; pinned model P13). -/
def OmegaLogSq (m : ℕ → ℕ) : Prop :=
  Filter.Tendsto (fun lam : ℕ => (m lam : ℝ) / (Real.logb 2 (lam : ℝ)) ^ 2) Filter.atTop Filter.atTop

/-- **The qubit bound of Theorem 7**, eqs. (23)–(24), p.38. Behera–Goyal, *Breaking the Bounded
Entanglement Barrier for Quantum Position Verification*, arXiv:2609.39234 (sha256 bdf2928d…),
Theorem 7, p.38:

`B(λ) = ⌊ m / ⌈log₂²(λ)⌉ ⌋ · R_H · (2κ(s − 2.5) − 1)`.

**Formalization Note.** `⌊·⌋` is natural-number division (`m / 0 = 0` at `λ ≤ 1`, where
`⌈log₂² λ⌉ = 0`; the theorems only use the bound for large `λ` or as an upper bound on sizes),
`⌈·⌉` is `Nat.ceil`, `log₂` is `Real.logb 2`; the bound is a real number. -/
noncomputable def securityBound (κ : ℝ) (m RH s : ℕ → ℕ) (lam : ℕ) : ℝ :=
  ((m lam / logSqCeil lam : ℕ) : ℝ) * (RH lam : ℝ) * (2 * κ * ((s lam : ℝ) - 2.5) - 1)

end QPVEntanglement


