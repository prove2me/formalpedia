-- Prove2me | Definitions.Def_TightQLB_Fourier
-- name    : TightQLB_Fourier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T01:59:45.78022+00:00
-- url     : https://prove2.me/theorems/cf21c008-2ae9-4af6-900a-fcd4b9388399
-- title:
--   The Fourier ensemble: sign oracle $f$, characters $\chi_z$, coefficients $\hat f(z)$ and the ideal distribution $p_f(z)=\hat f(z)^2$
-- statement:
--   Fix $n$ and put $N=2^n$. The oracle is a uniformly random function $f:\{0,1\}^n\to\{-1,1\}$, so that the $N$ values $f(x)$ are independent uniformly random signs. For $z\in\{0,1\}^n$ the character is $\chi_z(x)=(-1)^{z\cdot x}$, with $z\cdot x$ the inner product modulo 2. The Fourier coefficients and the ideal distribution are
--
--   $$
--   \hat f(z)=\frac1N\sum_x\chi_z(x)f(x),\qquad p_f(z)=\hat f(z)^2 .
--   $$
--
--   By Parseval's identity $\sum_z p_f(z)=1$ for every $f$. The module also fixes the expectation $\mathbb E_f$ over the oracle.
--
--   These objects define what the score of a device rewards: outcome $z$ is worth $Np_f(z)$.
--
--   **Formalization Note** A sign function is encoded by a bit function `fb : Qubits n → Bool` through $f(x)=(-1)^{\mathtt{fb}\,x}$ (`fval`); this is a bijection, so the uniform average over the $2^N$ bit functions (`avgF`) is $\mathbb E_f$. $z\cdot x$ is the published `QAlgorithms.dotBits`, and $N$ is `(2 : ℝ) ^ n`.
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §3.1, Eqs. (6)–(7), p. 13 (PDF p. 16)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
open QAlgorithms

namespace TightQLB

/-!
# The Fourier ensemble

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…), §3.1, Eqs. (6)–(7) and (12),
pp.13–14 (PDF pp.16–17).

"Throughout, n ≥ 1 and N = 2^n." The oracle is a uniformly random sign function
`f : {0,1}^n → {−1, 1}`; the characters are `χ_z(x) = (−1)^{z·x}`; the Fourier coefficients and the
ideal distribution are `f̂(z) = N⁻¹ Σ_x χ_z(x) f(x)` and `p_f(z) = f̂(z)²`.

**Formalization Note.**
* A sign function is encoded by a bit function `fb : Qubits n → Bool` through
  `f(x) = (−1)^{fb x}` (`fval`), so the uniform average over `f` is the uniform average over the
  `2^N` bit functions (`avgF`). This is a bijection and changes no instance.
* `z · x mod 2` is the published `QAlgorithms.dotBits`.
* `N = 2^n` is written `(2 : ℝ) ^ n`.
-/

/-- §3.1, p.13 (PDF p.16): the sign `f(x) = (−1)^{fb x} ∈ {−1, 1}` of the oracle encoded by the bit
function `fb`. -/
noncomputable def fval {n : ℕ} (fb : Qubits n → Bool) (x : Qubits n) : ℝ :=
  if fb x then -1 else 1

/-- §3.1, before (6), p.13 (PDF p.16): the character `χ_z(x) = (−1)^{z·x}`. -/
noncomputable def chi {n : ℕ} (z x : Qubits n) : ℝ :=
  if dotBits z x then -1 else 1

/-- §3.1, Eq. (7), p.13 (PDF p.16): the Fourier coefficient `f̂(z) = N⁻¹ Σ_x χ_z(x) f(x)`,
`N = 2^n`. -/
noncomputable def fhat {n : ℕ} (fb : Qubits n → Bool) (z : Qubits n) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x, chi z x * fval fb x

/-- §3.1, Eq. (7), p.13 (PDF p.16): the ideal distribution `p_f(z) = f̂(z)²`. -/
noncomputable def idealDist {n : ℕ} (fb : Qubits n → Bool) (z : Qubits n) : ℝ :=
  fhat fb z ^ 2

/-- §3.1, p.13 (PDF p.16) and Eq. (12), p.14 (PDF p.17): the expectation `E_f g(f)` over a uniformly
random sign function, i.e. the uniform average over all `2^N` bit functions `fb`. -/
noncomputable def avgF {n : ℕ} (g : (Qubits n → Bool) → ℝ) : ℝ :=
  (Fintype.card (Qubits n → Bool) : ℝ)⁻¹ * ∑ fb, g fb

end TightQLB


