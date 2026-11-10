-- Prove2me | Definitions.Def_DQILocal_Recon_Spectra
-- name    : DQILocal_Recon_Spectra
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:04:58.214068+00:00
-- url     : https://prove2.me/theorems/19b2dd94-316d-4c04-9d42-0c0abe736f52
-- title:
--   Gibbs weights $p_\beta$, spectra, convolution, reflection, $P_{\lambda,\mu}$, $\nu_\delta$ and $S(\nu)$
-- statement:
--   Fix an integer $q\ge 2$, write $\mathbb Z_q$ for the integers modulo $q$ and $\omega=e^{2\pi i/q}$. For a cost $f:\mathbb Z_q\to\mathbb R$ and an inverse temperature $\beta$, the **Gibbs weights** are
--
--   $$p_\beta(z)=\frac{e^{-\beta f(z)}}{\sum_{w\in\mathbb Z_q}e^{-\beta f(w)}},\qquad z\in\mathbb Z_q .$$
--
--   A **spectrum** is a probability vector $\nu$ on $\mathbb Z_q$ (nonnegative entries summing to one). For vectors $\lambda,\mu$ on $\mathbb Z_q$:
--
--   1. the convolution $(\lambda*\mu)(z)=\sum_w\lambda(w)\mu(z-w)$, the reflection $R\lambda(z)=\lambda(-z)$ and the uniform vector $\mathrm u(z)=1/q$;
--   2. the label probabilities $P_{\lambda,\mu}(\delta)=\sum_l\lambda(l+\delta)\mu(l)$ and the outgoing spectra $\nu_\delta(l)=\lambda(l+\delta)\mu(l)/P_{\lambda,\mu}(\delta)$;
--   3. the success function $S(\nu)=\frac1q\bigl(\sum_z\sqrt{\nu(z)}\bigr)^2$;
--   4. the phase $\omega^{y}=e^{2\pi i y/q}$ of $y\in\mathbb Z_q$, so that $\omega^{yz}$ uses the product $yz$ computed in $\mathbb Z_q$.
--
--   These are the scalar ingredients of the node operations of belief propagation with quantum messages and of the spectral recursion.
--
--   **Formalization Note** Spectra are functions $\mathbb Z_q\to\mathbb R$ with the probability-vector property as a separate predicate `IsProbVec`. The paper uses $\nu_\delta$ only when $P_{\lambda,\mu}(\delta)>0$; when it is $0$, Lean's division returns the zero vector, and that value is always weighted by $P_{\lambda,\mu}(\delta)=0$. The phase reads $y$ through its representative in $\{0,\dots,q-1\}$.
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), §3.1, p. 15; eq. (5), p. 16; §4.1 and Lemma 4.1, p. 23; Definition 4.2, p. 24

import Mathlib

namespace DQILocal.Recon

open scoped BigOperators

/-- **Gibbs weights, spectra and the operations on them.**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), §3.1, unnumbered
display, p. 15 (the weights `p`); eq. (5), p. 16 (spectrum, phase `ω`); §4.1, p. 23 (`λ ∗ μ`,
`Rλ`, `u`); Lemma 4.1, p. 23 (`P_{λ,μ}`, `ν_δ`); Definition 4.2, p. 24 (`S`).

* `gibbsWeight q f β z = e^{-β f(z)} / Σ_w e^{-β f(w)}` (the weights `p = p_β`, p. 15).
* `IsProbVec ν`: `ν` is a probability vector on `ℤ_q` (nonnegative entries summing to one); the
  paper calls such a vector a *spectrum* (p. 16).
* `conv λ μ z = Σ_w λ(w) μ(z - w)` (`λ ∗ μ`), `refl λ z = λ(-z)` (`Rλ`), `unif z = 1/q` (`u`).
* `omega q y = e^{2πi y/q}` for `y ∈ ℤ_q`, read through the representative `y.val ∈ {0,…,q-1}`;
  so `ω^{yz}` is `omega q (y * z)` with the product taken in `ℤ_q`.
* `labelProb λ μ δ = Σ_l λ(l + δ) μ(l)` (`P_{λ,μ}(δ)`) and
  `nuDelta λ μ δ l = λ(l + δ) μ(l) / P_{λ,μ}(δ)` (`ν_δ`).
* `succFn ν = (1/q) (Σ_z √ν(z))²` (`S(ν)`, Definition 4.2).

**Formalization Note.** Spectra are plain functions `ZMod q → ℝ`; the probability-vector property is
the separate predicate `IsProbVec`, assumed where the paper says "spectrum". `nuDelta` is used by the
paper only when `P_{λ,μ}(δ) > 0`; at `P_{λ,μ}(δ) = 0` Lean's division gives the zero vector, and every
place this value enters (the spectral recursion, BPQM) weights it by `P_{λ,μ}(δ) = 0`. -/
noncomputable def gibbsWeight (q : ℕ) [NeZero q] (f : ZMod q → ℝ) (β : ℝ) (z : ZMod q) : ℝ :=
  Real.exp (-β * f z) / ∑ w : ZMod q, Real.exp (-β * f w)

/-- A probability vector on `ℤ_q` (a *spectrum*, eq. (5), p. 16). -/
def IsProbVec {q : ℕ} [NeZero q] (ν : ZMod q → ℝ) : Prop :=
  (∀ z, 0 ≤ ν z) ∧ ∑ z, ν z = 1

/-- Convolution `(λ ∗ μ)(z) = Σ_w λ(w) μ(z - w)` (§4.1, p. 23). -/
noncomputable def conv {q : ℕ} [NeZero q] (lam mu : ZMod q → ℝ) (z : ZMod q) : ℝ :=
  ∑ w : ZMod q, lam w * mu (z - w)

/-- Reflection `Rλ(z) = λ(-z)` (§4.1, p. 23). -/
def refl {q : ℕ} (lam : ZMod q → ℝ) (z : ZMod q) : ℝ := lam (-z)

/-- The uniform vector `u` (§4.1, p. 23). -/
noncomputable def unif (q : ℕ) (_z : ZMod q) : ℝ := 1 / (q : ℝ)

/-- The phase `ω^y = e^{2πi y / q}` for `y ∈ ℤ_q` (`ω = e^{2πi/q}`, p. 15). -/
noncomputable def omega (q : ℕ) (y : ZMod q) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℕ) : ℂ) / (q : ℂ))

/-- Label probability `P_{λ,μ}(δ) = Σ_l λ(l + δ) μ(l)` (Lemma 4.1, p. 23). -/
noncomputable def labelProb {q : ℕ} [NeZero q] (lam mu : ZMod q → ℝ) (δ : ZMod q) : ℝ :=
  ∑ l : ZMod q, lam (l + δ) * mu l

/-- Outgoing spectrum `ν_δ(l) = λ(l + δ) μ(l) / P_{λ,μ}(δ)` (Lemma 4.1, p. 23). -/
noncomputable def nuDelta {q : ℕ} [NeZero q] (lam mu : ZMod q → ℝ) (δ : ZMod q) (l : ZMod q) :
    ℝ :=
  lam (l + δ) * mu l / labelProb lam mu δ

/-- Success function `S(ν) = (1/q) (Σ_z √ν(z))²` (Definition 4.2, p. 24). -/
noncomputable def succFn {q : ℕ} [NeZero q] (ν : ZMod q → ℝ) : ℝ :=
  (1 / (q : ℝ)) * (∑ z : ZMod q, Real.sqrt (ν z)) ^ 2

end DQILocal.Recon


