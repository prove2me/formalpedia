-- Prove2me | Definitions.Def_LinMaxLoad_Supplement_fourierCoeff
-- name    : LinMaxLoad_Supplement_fourierCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:22:19.671234+00:00
-- url     : https://prove2.me/theorems/4c2fce03-e939-4fb4-b230-5d8514db915a
-- title:
--   Fourier coefficient $\hat S(\gamma)$ of a set $S \subseteq \mathbb F_p^u$
-- statement:
--   Let $p$ be a prime. For $\gamma \in \mathbb F_p^u$ the character $\chi_\gamma : \mathbb F_p^u \to \mathbb C^\times$ is
--
--   $$
--   \chi_\gamma(x) = e^{\frac{2\pi i}{p}\sum_{i=1}^u \gamma_i x_i}.
--   $$
--
--   The **Fourier coefficient** at $\gamma$ of (the indicator of) a set $S \subseteq \mathbb F_p^u$ is
--
--   $$
--   \hat S(\gamma) = \mathbb E_{x \sim \mathbb F_p^u}\bigl[1_S(x)\,\chi_\gamma(x)\bigr] = p^{-u} \sum_{x \in S} \chi_\gamma(x).
--   $$
--
--   The Fourier 1-norm $\|\hat S\|_1 = \sum_{\gamma} |\hat S(\gamma)|$ bounds the expected linear max load (Theorem 5 / Lemma 9 of the paper).
--
--   **Formalization Note** The exponent $\sum_i \gamma_i x_i$ is computed in $\mathbb F_p = \mathbb Z/p\mathbb Z$ and read as its representative in $\{0, \dots, p-1\}$; since $e^{2\pi i k/p}$ depends only on $k \bmod p$ this is the character above. No complex conjugate is taken, as in the paper; $|\hat S(\gamma)|$ is the same either way.
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Section 2.2, p.8

import Mathlib

namespace LinMaxLoad.Supplement

/-- **Fourier coefficient of a set** `Ŝ(γ) = E_{x ∼ F_p^u}[1_S(x) χ_γ(x)]` (Section 2.2, p.8, of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)),
with the character `χ_γ(x) = exp((2πi/p) Σ_{i=1}^u γ_i x_i)`. Since `1_S` vanishes off `S`,
`Ŝ(γ) = p^{-u} Σ_{x ∈ S} χ_γ(x)`.

**Formalization Note** `F_p^u` is `Fin u → ZMod p`. The exponent `Σ_i γ_i x_i` is computed in
`ZMod p` and read as its representative in `{0, …, p − 1}` (`ZMod.val`); `exp(2πi k/p)` depends
only on `k mod p`, so this is the paper's character. No complex conjugate is taken, as printed. -/
noncomputable def fourierCoeff (p u : ℕ) [Fact p.Prime] (S : Finset (Fin u → ZMod p))
    (γ : Fin u → ZMod p) : ℂ :=
  ((p : ℂ) ^ u)⁻¹ * ∑ x ∈ S,
    Complex.exp (2 * Real.pi * Complex.I * (((∑ i, γ i * x i).val : ℕ) : ℂ) / (p : ℂ))

end LinMaxLoad.Supplement


