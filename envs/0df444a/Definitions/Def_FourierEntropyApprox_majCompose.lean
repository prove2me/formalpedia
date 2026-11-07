-- Prove2me | Definitions.Def_FourierEntropyApprox_majCompose
-- name    : FourierEntropyApprox_majCompose
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:22.253908+00:00
-- url     : https://prove2.me/theorems/d7a318ee-aca3-4cd3-bc74-0226e13dbc61
-- title:
--   Majority $\mathrm{Maj}_t$ and the composition $P_t=\mathrm{Maj}_t(P,\dots,P)$
-- statement:
--   **Majority** on $t$ variables is the Boolean function $\mathrm{Maj}_t:\{-1,1\}^t\to\{-1,1\}$ with
--
--   $$\mathrm{Maj}_t(y)=\begin{cases}1 & \text{if } y_1+\dots+y_t\ge 0,\\ -1 & \text{otherwise.}\end{cases}$$
--
--   For a real function $P$ on $\{-1,1\}^n$, the composition $P_t=\mathrm{Maj}_t(P,\dots,P)$ substitutes $P(x)$ for every variable of the multilinear (Fourier) expansion of $\mathrm{Maj}_t$:
--
--   $$P_t(x)=\sum_{S\subseteq[t]}\widehat{\mathrm{Maj}_t}(S)\,P(x)^{|S|}.$$
--
--   This is the majority amplification of the proof of Theorem 3.2: when $P$ has the sign of a Boolean $f$ with a margin, $P_t$ approximates $f$ with an error exponentially small in $t$, at the price of a spectral norm exponential in $t$.
--
--   **Formalization Note** For even $t$ the paper does not say how a tie is broken; here a tie gives $+1$. For $t=0$ this makes $\mathrm{Maj}_0\equiv1$ and $P_0\equiv1$. $P_t$ is the multilinear composition, not $\mathrm{Maj}_t$ applied to the signs of $P$.
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), proof of Theorem 3.2, p.15 (PDF p.15)

import Mathlib
import Definitions.Def_FourierEntropyApprox_fourierCoeff

namespace FourierEntropyApprox

/-!
# Majority and its composition with a polynomial

M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), proof of Theorem 3.2, p.15: "Let Maj_t be the Majority function on t variables. Then, define
P_t := Maj_t(P, . . . , P)".

**Formalization Note.**
* `maj t` is Majority on `t` variables with values `±1`. For even `t` the paper does not say how a tie is
  broken; here a tie gives `+1` (`maj t y = 1` iff `∑ᵢ yᵢ ≥ 0`). For `t = 0` this gives the constant `1`.
* `Maj_t(P, …, P)` is the composition of the multilinear (Fourier) expansion of `Maj_t` with `t` copies of `P`:
  `P_t(x) = ∑_{S ⊆ [t]} M̂aj_t(S) · P(x)^{|S|}`. It is a real function on the cube, and it is not the sign
  of `P` fed to `Maj_t`.
-/

/-- Majority on `t` variables: `1` if `∑ᵢ yᵢ ≥ 0`, else `−1` (ties to `+1`). -/
noncomputable def maj (t : ℕ) (y : Cube t) : ℝ := if 0 ≤ ∑ i, spin (y i) then 1 else -1

/-- `P_t = Maj_t(P, …, P)`, the multilinear expansion of `Maj_t` evaluated at `(P(x), …, P(x))` (p.15). -/
noncomputable def majCompose {n : ℕ} (t : ℕ) (P : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ S : Finset (Fin t), fourierCoeff (maj t) S * P x ^ S.card

end FourierEntropyApprox


