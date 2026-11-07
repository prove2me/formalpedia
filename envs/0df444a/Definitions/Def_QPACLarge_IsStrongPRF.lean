-- Prove2me | Definitions.Def_QPACLarge_IsStrongPRF
-- name    : QPACLarge_IsStrongPRF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:08:01.036198+00:00
-- url     : https://prove2.me/theorems/2a9413a6-34fa-4678-b827-69b818249283
-- title:
--   Strong pseudorandom function family, Eq. (7)
-- statement:
--   Let $\ell$ be polynomially bounded and computable in polynomial time, and let $G_\lambda = \{g_{\lambda,s}\}_{s \in \{0,1\}^{\ell(\lambda)}}$ have a deterministic evaluation algorithm running in time $\mathrm{poly}(\lambda)$ on $(1^\lambda, s, x)$. The family is a **strong pseudorandom function family** with exponent $\varepsilon \in (0,1)$ (rational) if every oracle algorithm $D$ running in time at most $2^{\lambda^\varepsilon}$ satisfies
--
--   $$
--   \mathrm{Adv}_G(D, \lambda) \le 2^{-\lambda^\varepsilon} \tag{7}
--   $$
--
--   for every sufficiently large $\lambda$. The paper's "strong PRF" is the existence of such an $\varepsilon$.
--
--   **Formalization Note** Polynomial time in the input length of $(1^\lambda, s, x)$ is polynomial time in $\lambda$ because $\ell$ is polynomially bounded; $\ell$ is computed as $1^\lambda \mapsto 1^{\ell(\lambda)}$. Distinguishers are clocked at $\lfloor 2^{\lambda^\varepsilon}\rfloor$ steps (see `prfAdv`).
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 4.2.1, p.31, Definition (Strong PRFs), Eq. (7)

import Mathlib
import Definitions.Def_QPACLarge_prfAdv
import Definitions.Def_QAlgorithms_ClassicalUnaryInput

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity Filter

/-- **Strong pseudorandom function family with exponent `ε`.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 4.2.1, p.31, Definition (Strong PRFs): "Let `ℓ : ℕ → ℕ` be polynomially bounded and
computable in polynomial time. Consider a family `G_λ = {g_{λ,s} : {0,1}^λ → {0,1}}_{s∈{0,1}^{ℓ(λ)}}`
with a deterministic evaluation algorithm running in `poly(λ)` time on input `(1^λ, s, x)`. … We
call `G` a strong pseudorandom function family (strong PRF) if there is a rational constant
`ε ∈ (0, 1)` such that every `D` running in time at most `2^{λ^ε}` satisfies
`Adv_G(D, λ) ≤ 2^{−λ^ε}` (7) for every sufficiently large `λ`."

`IsStrongPRF ℓ G ε`: `ℓ` is polynomially bounded and `1^λ ↦ 1^{ℓ(λ)}` is polynomial-time
computable, the evaluation algorithm `G` is polynomial-time computable, `ε ∈ (0, 1)`, and Eq. (7)
holds for every oracle machine clocked at `⌊2^{λ^ε}⌋` steps. "`G` is a strong PRF" is
`∃ ε : ℚ, IsStrongPRF ℓ G ε`.

**Formalization Note.** Polynomial time in the input length `2λ + ℓ(λ) + 1` of `(1^λ, s, x)` is
polynomial time in `λ`, since `ℓ` is polynomially bounded. Clocking (see `prfAdv`,
`SubexpOWFExists`) changes the class of distinguishers only up to a polynomial in `2^{λ^ε}`. -/
def IsStrongPRF (ℓ : ℕ → ℕ) (G : Str → Str) (ε : ℚ) : Prop :=
  (∃ p : Polynomial ℕ, ∀ lam, ℓ lam ≤ p.eval lam) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam, g (unary lam) = unary (ℓ lam)) ∧
  PolyTimeComputable G ∧ 0 < ε ∧ ε < 1 ∧
  ∀ D : HMBinPacking.OracleMachine, ∀ᶠ lam : ℕ in atTop,
    prfAdv D ℓ G lam ⌊(2 : ℝ) ^ ((lam : ℝ) ^ (ε : ℝ))⌋₊ ≤ (2 : ℝ) ^ (-((lam : ℝ) ^ (ε : ℝ)))

end QPACLarge


