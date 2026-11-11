-- Prove2me | Definitions.Def_DoubleCorrRME_Perm
-- name    : DoubleCorrRME_Perm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:08.235322+00:00
-- url     : https://prove2.me/theorems/b2a72dcc-b97c-442d-923d-175d484bedf5
-- title:
--   Uniform random permutations: $\mathbb E_\pi$, $\|\cdot\|_{L_p}$, the random batch means $b_i$ and $G_h$
-- statement:
--   Let $\pi$ be uniform on the permutations of $[m]$. For $f$ a function of $\pi$, $\mathbb E_\pi f=\frac1{m!}\sum_\pi f(\pi)$ and $\|f\|_{L_p}=(\mathbb E_\pi|f|^p)^{1/p}$.
--
--   For $m=Nn$ and vectors $v_1,\dots,v_m\in\mathbb R^d$, the random batch means are $b_i(\pi)=\frac1n\sum_{r=(i-1)n+1}^{in}v_{\pi(r)}$, and for $h\in\mathbb R^d$, $G_h(\pi)=\frac1N\sum_{i=1}^N|\langle h,b_i(\pi)\rangle|$.
--
--   These are the objects of the permutation concentration argument (Lemmas 4.4, 4.5).
--
--   **Formalization Note** Positions are 0-based: user $i$'s block is $i\cdot n+j$, $j<n$.
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Lemma 4.4, p.21 (PDF p.22); Lemma 4.5 and its proof, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_DoubleCorrRME_Model

namespace DoubleCorrRME

/-!
# Uniform random permutations: expectation, `L_p` norms, random batch means

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…): Lemma 4.4, p.21
(PDF p.22); Lemma 4.5 and its proof, p.22 (PDF p.23); `∥·∥_{L_p}`, p.4 (PDF p.5).

**Formalization Note.**
* `π` is uniform on the finite group `Equiv.Perm (Fin m)`, so the expectation of `f(π)` is the finite
  average `(1/m!) ∑_π f(π)`, and `∥X∥_{L_p} := (E|X|^p)^{1/p}` (`Real.rpow`, real `p ≥ 1` in every use).
  No measurability question arises.
* Positions are 0-based: the paper's block `(i − 1)n + 1, …, in` of user `i ∈ [N]` is the block
  `i·n + j`, `j ∈ Fin n`, of `i ∈ Fin N` (`finProdFinEquiv`).
-/

/-- `E_π[f(π)]` for `π` uniform on the permutations of `[m]`. -/
noncomputable def permAvg (m : ℕ) (f : Equiv.Perm (Fin m) → ℝ) : ℝ :=
  ((Fintype.card (Equiv.Perm (Fin m)) : ℝ))⁻¹ * ∑ π, f π

/-- `∥f∥_{L_p} := (E_π |f(π)|^p)^{1/p}` for `π` uniform on the permutations of `[m]`. -/
noncomputable def permLp (m : ℕ) (p : ℝ) (f : Equiv.Perm (Fin m) → ℝ) : ℝ :=
  (permAvg m fun π => |f π| ^ p) ^ (1 / p)

/-- Lemma 4.5: `b_i(π) := (1/n) ∑_{r=(i−1)n+1}^{in} v_{π(r)}`, the mean of the `i`-th block of `n`
consecutive positions after permuting by `π`. -/
noncomputable def batchMean {N n d : ℕ} (v : Fin (N * n) → Vec d) (π : Equiv.Perm (Fin (N * n)))
    (i : Fin N) : Vec d :=
  ((n : ℝ))⁻¹ • ∑ j : Fin n, v (π (finProdFinEquiv (i, j)))

/-- Proof of Lemma 4.5: `G_h(π) := (1/N) ∑_{i=1}^N |⟨h, b_i(π)⟩|`. -/
noncomputable def gH {N n d : ℕ} (v : Fin (N * n) → Vec d) (h : Vec d)
    (π : Equiv.Perm (Fin (N * n))) : ℝ :=
  ((N : ℝ))⁻¹ * ∑ i, |inner ℝ h (batchMean v π i)|

end DoubleCorrRME


