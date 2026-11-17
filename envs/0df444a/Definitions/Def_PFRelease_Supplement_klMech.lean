-- Prove2me | Definitions.Def_PFRelease_Supplement_klMech
-- name    : PFRelease_Supplement_klMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:43:48.578332+00:00
-- url     : https://prove2.me/theorems/8f0d5ae1-3c0b-4abf-a93f-08dfade6702c
-- title:
--   User histograms, average counts $\bar H_j(s)$, the target $g_{\mathrm{KL}}$, the score $\varphi_{\mathrm{KL}}$ and the release $M_{\mathrm{KL}}$
-- statement:
--   Fix public integers $T\ge1$ and $d\ge2$. A record is either $\perp$ or a **histogram** $H\in\mathbb Z_{\ge0}^d$ with $\sum_{j\in[d]}H_j=T$. For a dataset $s$, $\bar H_j(s)$ is the average count of category $j$ over the $|s|$ records of $s$, null records counting as zero histograms. For a public pseudocount $\lambda>0$ and a nonempty dataset $s$,
--   $$
--   g_{\mathrm{KL}}(s):=\ln\Big(\frac{T+d\lambda}{d}\Big)-\frac1d\sum_{j\in[d]}\ln\big(\lambda+\bar H_j(s)\big),
--   $$
--   with the denominators $|s|$ and $T+d\lambda$ fixed also on datasets with null records. The score of a non-null histogram $H$ against a nonempty dataset $s$ is
--   $$
--   \varphi_{\mathrm{KL}}(s,H):=\Big(\frac1d\sum_{j\in[d]}\frac{H_j}{\lambda+\bar H_j(s)}\Big)^{-1},\qquad \varphi_{\mathrm{KL}}(\emptyset,H):=0,
--   $$
--   and the release mechanism on datasets of $n$ records is $M_{\mathrm{KL}}(s):=g_{\mathrm{KL}}(s)+\mathrm{Lap}\big(2/(\tau n\varepsilon)\big)$.
--
--   On a dataset without null records, $g_{\mathrm{KL}}(s)$ is the KL divergence from the uniform distribution on the categories to the smoothed pooled frequencies $(\lambda+\bar H_j(s))/(T+d\lambda)$.
--
--   **Formalization Note** Histograms are functions `Fin d → ℕ` summing to $T$; the hypotheses $T\ge1$, $d\ge2$ belong to the theorem. The outer inverse of the score is taken in $[0,\infty]$. The score's value at the null record is not fixed by the paper and is set to $0$. $\mathrm{Lap}(\sigma)$ is the published `PrivLearn.Generic.laplace`, and the law of $M_{\mathrm{KL}}(s)$ is its image under $z\mapsto g_{\mathrm{KL}}(s)+z$.
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), eq. (3), p.19 (PDF p.21); App. D.3, Setting and target, Score and release mechanism, p.47 (PDF p.49)

import Mathlib
import Definitions.Def_PFRelease_Dataset

open MeasureTheory

namespace PFRelease.Supplement

/-- A user histogram (Shenfeld, Tsfadia, Ligett, arXiv:2610.40654, held version sha256 e1d516b3…,
App. D.3, p.47 = PDF p.49): `H ∈ ℤ^d_{≥0}` with `Σ_{j∈[d]} H_j = T`.

**Formalization Note** Nonnegative integer counts are natural numbers; categories are `Fin d`. The
standing assumptions `T ≥ 1` and `d ≥ 2` are hypotheses of the theorem. -/
def Histogram (d T : ℕ) : Type := {H : Fin d → ℕ // ∑ j, H j = T}

/-- The count of category `j` in a record, with a null record counted as the zero histogram. -/
def histCount {d T : ℕ} : Option (Histogram d T) → Fin d → ℝ
  | none, _ => 0
  | some H, j => (H.1 j : ℝ)

/-- The average count `H̄_j(s)` of category `j` over the `|s|` records of `s`, null records counted as
zero histograms and included in `|s|` (App. D.3, p.47 = PDF p.49). -/
noncomputable def avgCount {d T : ℕ} (l : List (Option (Histogram d T))) (j : Fin d) : ℝ :=
  (l.length : ℝ)⁻¹ * (l.map fun x => histCount x j).sum

/-- The target `g_KL(s) := ln((T + dλ)/d) − (1/d) Σ_{j∈[d]} ln(λ + H̄_j(s))` for a nonempty dataset
(App. D.3, p.47 = PDF p.49), with the fixed denominators `|s|` and `T + dλ` also on datasets with null
records. -/
noncomputable def gKL {d T : ℕ} (lam : ℝ) (l : List (Option (Histogram d T))) : ℝ :=
  Real.log ((T + d * lam) / d) - (1 / (d : ℝ)) * ∑ j, Real.log (lam + avgCount l j)

/-- The score `φ_KL(s, H) := (d⁻¹ Σ_{j∈[d]} H_j/(λ + H̄_j(s)))⁻¹` for a nonempty dataset `s` and a
non-null histogram `H`, with `φ_KL(∅, H) := 0` (eq. (3), p.19 = PDF p.21; App. D.3, p.47).

**Formalization Note** The outer inverse is taken in `[0, ∞]` (`1/0 = ∞`). The value at the null
record is unrestricted by the paper (footnote 5, p.12); it is `0` here and never matters for the
theorem, whose input has no null records. -/
noncomputable def phiKL {d T : ℕ} (lam : ℝ) :
    List (Option (Histogram d T)) → Option (Histogram d T) → ENNReal
  | [], _ => 0
  | _ :: _, none => 0
  | y :: l, some H =>
      (ENNReal.ofReal ((1 / (d : ℝ)) * ∑ j, (H.1 j : ℝ) / (lam + avgCount (y :: l) j)))⁻¹

/-- The release mechanism `M_KL(s) := g_KL(s) + Lap(2/(τnε))` on datasets of `n` records (eq. (3),
p.19 = PDF p.21): the law of `g_KL(s)` plus Laplace noise of scale `2/(τnε)`.

**Formalization Note** `Lap(σ)` is the published `PrivLearn.Generic.laplace`; the law of the sum is
the image of the noise law under the translation `z ↦ g_KL(s) + z`. -/
noncomputable def mKL {d T : ℕ} (lam τ ε : ℝ) {n : ℕ} (s : Fin n → Option (Histogram d T)) :
    Measure ℝ :=
  (PrivLearn.Generic.laplace (2 / (τ * n * ε))).map fun z => gKL lam (toList s) + z

end PFRelease.Supplement


