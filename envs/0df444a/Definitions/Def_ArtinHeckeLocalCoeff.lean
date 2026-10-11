-- Prove2me | Definitions.Def_ArtinHeckeLocalCoeff
-- name    : ArtinHeckeLocalCoeff
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T15:06:22.353399+00:00
-- url     : https://prove2.me/theorems/2264d7e5-17e3-4cbf-aee4-d255731632f2
-- title:
--   The local coefficient table of the principal row in Proposition 7.3 (u = 1) of the proof of Theorem 1.2
-- statement:
--   One object of §7.3 of OpenAI, *Primitive roots for every admissible integer base* (2026), pp. 46–48. It depends on nothing beyond Mathlib.
--
--   - `principalLocalCoeff Q η θ e₀ l k m`: for a natural number $Q$ (the norm of a prime), complex numbers $\eta$ and $\theta$, and natural numbers $e_0, l, k, m$, the following value. When $e_0 = 0$:
--     - $1$ if $l = 0$ and ($k = 0$ or $m = 0$), and $0$ if $l = 0$ otherwise;
--     - for even $l > 0$: $\theta^{l/2}Q^{3l}(1 - Q^{-1})$ if $k = 0$ and $l/2 \le m$, and $\theta^{l/2}Q^{3l}$ if $k = 1$ and $m = l/2$;
--     - $0$ in all other cases.
--
--     When $e_0 = 1$ and $l$ is even:
--     - $-\eta\sqrt Q\,\theta^{l/2}Q^{3l}$ if $k = 0$ and $m = l/2$;
--     - $-\eta\sqrt Q\,\theta^{l/2}Q^{3l}(Q - 1)$ if $k = 1$ and $m > l/2$;
--     - $0$ otherwise.
--
--     In every other case it is $0$.
--
--   In the paper's notation this is the local coefficient of the principal frequency series $\mathcal F_1$ at a prime $\mathfrak p$ with $v_{\mathfrak p}(\mathfrak c) = e_0$, $v_{\mathfrak p}(\mathfrak n) = l$, $v_{\mathfrak p}(\mathfrak s) = k$ and $v_{\mathfrak p}(\mathfrak r) = m$, so that $t = e_0 + 3l$ and $J = 6m$, from the table (7.17). Here $\eta = \eta(\mathfrak p)$ and $\theta = \vartheta(\mathfrak p)^6$. The table is written after substituting the paper's relations $\gamma_1\gamma_2\vartheta = -\eta$, $\tau_1 = \sqrt Q\,\gamma_1$ and $\tau_1\tau_5 = Q$.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 46–48, Proposition 7.3, (7.16)–(7.17) at u = 1 (the local coefficient table of the principal row)

import Mathlib

namespace ArtinPrimitiveRoots

/-- The coefficient table of the principal row at a prime of norm `Q`, for valuations
`e₀, l, k, m` of `𝔠, 𝔫, 𝔰, 𝔯` there: Proposition 7.3, (7.16)–(7.17), at `u = 1`, of OpenAI's
*Primitive roots for every admissible integer base*, pp. 46–48. -/
noncomputable def principalLocalCoeff (Q : ℕ) (η θ : ℂ) (e₀ l k m : ℕ) : ℂ :=
  if e₀ = 0 then
    if l = 0 then (if k = 0 ∨ m = 0 then 1 else 0)
    else if Even l then
      (if k = 0 ∧ l / 2 ≤ m then θ ^ (l / 2) * (Q : ℂ) ^ (3 * l) * (1 - (Q : ℂ)⁻¹)
       else if k = 1 ∧ m = l / 2 then θ ^ (l / 2) * (Q : ℂ) ^ (3 * l) else 0)
    else 0
  else if e₀ = 1 ∧ Even l then
    (if k = 0 ∧ m = l / 2 then -(η * (Real.sqrt Q : ℂ)) * θ ^ (l / 2) * (Q : ℂ) ^ (3 * l)
     else if k = 1 ∧ l / 2 < m then
       -(η * (Real.sqrt Q : ℂ)) * θ ^ (l / 2) * (Q : ℂ) ^ (3 * l) * ((Q : ℂ) - 1)
     else 0)
  else 0

end ArtinPrimitiveRoots


