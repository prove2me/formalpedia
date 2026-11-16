-- Prove2me | Definitions.Def_DQILocal_Recon_Supplement_Thresholds
-- name    : DQILocal_Recon_Supplement_Thresholds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:25:58.354459+00:00
-- url     : https://prove2.me/theorems/ad949e43-0d5a-4af5-88f0-6eff29027241
-- title:
--   $p_\infty$, $p_{\beta_d}$, $\langle f\rangle_p$, $s_d$, Hamming weight, $H_A$, $s_\eta$ and $\kappa_\eta$
-- statement:
--   Let $f:\mathbb Z_q\to\mathbb R$ be a cost and $\beta_d\in[0,\infty]$ the reconstruction threshold of the primal model on the $(k,D)$ tree (base `betaD`).
--
--   1. $p_\infty$ is the uniform law on the minimizers of $f$, and $p_{\beta_d}$ is the Gibbs weight vector at $\beta_d$, read as $p_\infty$ when $\beta_d=\infty$.
--   2. $\langle f\rangle_p=\sum_zp(z)f(z)$.
--   3. For Max-XORSAT ($q=2$, $f(z)=z$), $s_d=p_{\beta_d}(0)=\tfrac12+\tfrac12\tanh(\beta_d/2)$, read as $1$ when $\beta_d=\infty$.
--   4. $|x|=\#\{j:x_j\ne0\}$, and for $A\subseteq\mathbb Z_q$, $H_A(x)=\#\{j:x_j\notin A\}$.
--   5. For $\eta>0$, $s_\eta=p_{\beta_d+\eta}(A)$ and $\kappa_\eta=1-P_\infty(p_{\beta_d+\eta})$, where $P_\infty=\lim_tP_t$ for the spectral recursion at the spectrum $p_{\beta_d+\eta}$.
--
--   These are the limiting quantities of the approximate-optimization bounds of Section 6.2.
--
--   **Formalization Note** $s_\eta$ and $\kappa_\eta$ use $\beta_d$ through its real value; they are used only when $\beta_d$ is finite. $P_\infty$ is the base `Pinf`, the supremum of the nondecreasing sequence $P_t$.
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), §3.1, p. 15 (p_∞); Theorem 6.5, p. 40 (p_{β_d}, s_d); §6.2.2, p. 41 (H_A); Theorem 6.9, p. 42 (s_η, κ_η); §6.3.3, p. 50 (Hamming weight)

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_SpectralRecursion
import Definitions.Def_DQILocal_Recon_Reconstruction

namespace DQILocal.Recon.Supplement

open scoped BigOperators
open DQILocal.Recon

/-- **The zero-temperature weights `p_∞`.**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), §3.1, p. 15:
`p_∞ = lim_{β→∞} p_β` is the uniform law on the minimizers of `f`. -/
noncomputable def pInf (q : ℕ) [NeZero q] (f : ZMod q → ℝ) (z : ZMod q) : ℝ := by
  classical
  exact if ∀ w, f z ≤ f w then
      1 / ((Finset.univ.filter fun y : ZMod q => ∀ w, f y ≤ f w).card : ℝ)
    else 0

/-- **`p_{β_d}` (Theorem 6.5, p. 40)**: the Gibbs weights at the reconstruction threshold
`β_d = betaD k D q f ∈ [0, ∞]`, read as `p_∞` when `β_d = ∞` ("If `β_d = ∞`, then `p_{β_d}`
means `p_∞`"). -/
noncomputable def pBetaD (k D q : ℕ) [NeZero q] (f : ZMod q → ℝ) : ZMod q → ℝ :=
  if betaD k D q f = ⊤ then pInf q f else gibbsWeight q f (betaD k D q f).toReal

/-- **The mean cost** `⟨f⟩_p = Σ_z p(z) f(z)` (p. 6). -/
noncomputable def avgCost {q : ℕ} [NeZero q] (p : ZMod q → ℝ) (f : ZMod q → ℝ) : ℝ :=
  ∑ z, p z * f z

/-- **`s_d` for Max-XORSAT (Theorem 6.5, p. 40)**: for `q = 2`, `f(z) = z` and the threshold
`b = β_d ∈ [0, ∞]`, `s_d = p_{β_d}(0) = ½ + ½ tanh(β_d / 2)`, read as `1` when `β_d = ∞`
(`p_∞(0) = 1` for `f(z) = z`). The theorems apply it to `b = betaD k D q f` with `q = 2` and
`f z = z.val`. -/
noncomputable def sdOf (b : ENNReal) : ℝ :=
  if b = ⊤ then 1 else 1 / 2 + (1 / 2) * Real.tanh (b.toReal / 2)

/-- **Hamming weight** `|x| = #{j : x_j ≠ 0}` (p. 50). -/
noncomputable def hamWt {q m : ℕ} (x : Fin m → ZMod q) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => x j ≠ 0).card

/-- **`H_A(x)`, the number of violated constraints for a two-level cost (§6.2.2, p. 41)**:
`H_A(x) = #{j : x_j ∉ A}`. -/
noncomputable def violA {q m : ℕ} (A : Finset (ZMod q)) (x : Fin m → ZMod q) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => x j ∉ A).card

/-- **`s_η` (Theorem 6.9, p. 42)**: `s_η = p_{β_d+η}(A) = Σ_{z ∈ A} p_{β_d+η}(z)`, a function of
`(k, D, q, f, A, η)` only. `β_d` is finite in Theorem 6.9 and enters as `β_d.toReal`. -/
noncomputable def sEta (k D q : ℕ) [NeZero q] (f : ZMod q → ℝ) (A : Finset (ZMod q)) (η : ℝ) : ℝ :=
  ∑ z ∈ A, gibbsWeight q f ((betaD k D q f).toReal + η) z

/-- **`κ_η` (Theorem 6.9, p. 42)**: `κ_η = 1 - P_∞(p_{β_d+η})` with `P_∞ = lim_t P_t` (base `Pinf`,
the supremum of the nondecreasing sequence `P_t`), a function of `(k, D, q, f, η)` only. -/
noncomputable def kappaEta (k D q : ℕ) [NeZero q] (f : ZMod q → ℝ) (η : ℝ) : ℝ :=
  1 - Pinf k D q f ((betaD k D q f).toReal + η)

end DQILocal.Recon.Supplement


