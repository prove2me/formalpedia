-- Prove2me | Definitions.Def_ArtinHeckePoissonLocal
-- name    : ArtinHeckePoissonLocal
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T16:04:36.518978+00:00
-- url     : https://prove2.me/theorems/36b322fe-c25b-4789-8dba-525898c4b66d
-- title:
--   (7.17) of OpenAI's Primitive roots paper — the local values of the Poisson factor of the principal row at a prime power (u = 1)
-- statement:
--   One object of §7.3 of OpenAI, *Primitive roots for every admissible integer base* (2026), p. 48. It depends on nothing beyond Mathlib.
--
--   - `poissonLocal Q γ e₀ l k m`: for a natural number $Q$ (the norm of a prime), a complex number $\gamma$, and natural numbers $e_0, l, k, m$, the following value. When $e_0 = 0$:
--     - $1$ if $l = 0$ and ($k = 0$ or $m = 0$), and $0$ if $l = 0$ otherwise;
--     - for even $l > 0$: $Q^{3l}(1 - Q^{-1})$ if $k = 0$ and $l/2 \le m$, and $Q^{3l}$ if $k = 1$ and $m = l/2$;
--     - $0$ in all other cases.
--
--     When $e_0 = 1$ and $l$ is even:
--     - $\sqrt Q\,\gamma\,Q^{3l}$ if $k = 0$ and $m = l/2$;
--     - $\sqrt Q\,\gamma\,Q^{3l}(Q - 1)$ if $k = 1$ and $m > l/2$;
--     - $0$ otherwise.
--
--     In every other case it is $0$.
--
--   In the paper's notation this is the stripped local sum $C_{t,k}(J)$ of (7.15), evaluated in (7.17), at $t = e_0 + 3l$ and $J = 6m$, with $\gamma$ in the place of $\gamma_1(\mathfrak p)$, so that $\tau_1 = \sqrt Q\,\gamma$ (p. 49: “Indeed $\tau_1 = \sqrt Q\,\gamma_1(\mathfrak p)$ in the chosen additive sign”).
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 48: “For $t = 0$ the value is $C_{0,0}(J) = 1$, and $C_{0,k}(J) = \mathbf 1_{J=0}$ for $k > 0$. For $t > 0$ it is $C_{t,0}(J) = \mathbf 1_{J \ge t-1} Q^{t-1} T_t(p^{J-t+1})$, $C_{t,1}(J) = \mathbf 1_{J\ge t}\,\tau_1 Q^{t-1} T_{t-1}(p^{J-t})$, $C_{t,k}(J) = 0$ $(k \ge 2)$. (7.17)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 48, (7.17) at u = 1 (the local values C_{t,k}(6m) of the Poisson factor at a prime power)

import Mathlib

namespace ArtinPrimitiveRoots

/-- The local values `C_{t,k}(J)` of (7.17) of OpenAI's *Primitive roots for every admissible
integer base*, p. 48, at `t = e₀ + 3l`, `J = 6m`, written with `Q` the norm of the prime and `γ` in
the place of `γ₁(𝔭)` (so that `τ₁ = √Q γ`): for `e₀ = 0`, the value is `1` if `l = 0` and
(`k = 0` or `m = 0`); for even `l > 0` it is `Q^{3l}(1 − Q⁻¹)` if `k = 0` and `l/2 ≤ m`, and
`Q^{3l}` if `k = 1` and `m = l/2`; for `e₀ = 1` and even `l` it is `√Q γ Q^{3l}` if `k = 0` and
`m = l/2`, and `√Q γ Q^{3l}(Q − 1)` if `k = 1` and `l/2 < m`; it is `0` otherwise. -/
noncomputable def poissonLocal (Q : ℕ) (γ : ℂ) (e₀ l k m : ℕ) : ℂ :=
  if e₀ = 0 then
    if l = 0 then (if k = 0 ∨ m = 0 then 1 else 0)
    else if Even l then
      (if k = 0 ∧ l / 2 ≤ m then (Q : ℂ) ^ (3 * l) * (1 - (Q : ℂ)⁻¹)
       else if k = 1 ∧ m = l / 2 then (Q : ℂ) ^ (3 * l) else 0)
    else 0
  else if e₀ = 1 ∧ Even l then
    (if k = 0 ∧ m = l / 2 then (Real.sqrt Q : ℂ) * γ * (Q : ℂ) ^ (3 * l)
     else if k = 1 ∧ l / 2 < m then (Real.sqrt Q : ℂ) * γ * (Q : ℂ) ^ (3 * l) * ((Q : ℂ) - 1)
     else 0)
  else 0

end ArtinPrimitiveRoots


