-- Prove2me | Definitions.Def_MFHeisGibbs_Filter
-- name    : MFHeisGibbs_Filter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:33.040036+00:00
-- url     : https://prove2.me/theorems/c248eee2-a94c-4ef1-98de-09b46051cf34
-- title:
--   KMS filters (4), $c_\star$, the Metropolis filter, $\tilde f$, $m_f$, $N_f$, $\gamma_f$, $f_\infty$ and the exponent of the phase diagram
-- statement:
--   A **KMS filter** is a continuous $f:\mathbb R\to\mathbb C$ with
--
--   $$f(\nu)=e^{-\nu/2}\overline{f(-\nu)},\qquad |f|\le1,\qquad c_\star:=\inf_{\nu\le0}|f(\nu)|^2>0 .$$
--
--   The Metropolis filter is $f_M(\nu)=1$ for $\nu\le0$ and $e^{-\nu/2}$ for $\nu\ge0$. The symmetrized filter is $\tilde f(\nu)=e^{\nu/4}f(\nu)$, with $m_f=\inf_{|\nu|\le\beta}|\tilde f(\nu)|$, $N_f=\sup_{|\nu|\le\beta}|f(\nu)|$ and $\gamma_f=\frac{n}{n-1}\frac{m_f^4}{54N_f^2}$. The limit $f_\infty$ is $c_-$ on $\nu<0$, $c_0$ at $\nu=0$ and $0$ on $\nu>0$. The exponent of the phase diagram is $0$ for $\beta<2$, $\tfrac12$ at $\beta=2$ and $1$ for $\beta>2$, and $\Phi$ is the standard normal distribution function.
--
--   These parametrize the three families of Lindbladians and the bounds on their gaps.
--
--   **Formalization Note** `KMSRel` is continuity plus the KMS relation alone, the hypothesis of Theorem 2 and Lemma 13. `cStar` is the infimum of a nonempty set of nonnegative numbers, and $m_f,N_f$ are taken over a compact interval, so no junk value occurs.
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), (4), p.3 (PDF 4); (8), p.4 (PDF 5); (35), p.12 (PDF 13); (46), (47), p.15 (PDF 16); p.36 (PDF 37)

import Mathlib

open Set

namespace MFHeisGibbs

/-!
# KMS filters

Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…),
(4), p.3; (8), p.4; (35), p.12; (46), p.15; pp.36, 40.

**Formalization Note.** `cStar f` is a real infimum over `ν ≤ 0` of a nonnegative quantity, so it is
never a junk value of an empty or unbounded set. `f` need not be real-valued; (4) forces `f(0)` to
be real, and the page's `f(0)²` is written `‖f 0‖²`.
-/

/-- The normalization constant `c⋆ = inf_{ν≤0} |f(ν)|²`, (4). -/
noncomputable def cStar (f : ℝ → ℂ) : ℝ := sInf ((fun ν => ‖f ν‖ ^ 2) '' Iic 0)

/-- Continuity and the KMS relation `f(ν) = e^{−ν/2} f*(−ν)` of (4), with no normalization. -/
def KMSRel (f : ℝ → ℂ) : Prop :=
  Continuous f ∧ ∀ ν : ℝ, f ν = (Real.exp (-ν / 2) : ℂ) * (starRingEnd ℂ) (f (-ν))

/-- A KMS filter: `f` is continuous and satisfies all of (4), that is, the KMS relation, `|f| ≤ 1`
and `c⋆ > 0`. -/
def IsKMSFilter (f : ℝ → ℂ) : Prop :=
  KMSRel f ∧ (∀ ν, ‖f ν‖ ≤ 1) ∧ 0 < cStar f

/-- The Metropolis filter `f_M`, (8): `1` for `ν ≤ 0`, `e^{−ν/2}` for `ν ≥ 0`. -/
noncomputable def fM (ν : ℝ) : ℂ := if ν ≤ 0 then 1 else (Real.exp (-ν / 2) : ℂ)

/-- The symmetrized filter `f̃(ν) = e^{ν/4} f(ν)`, (35). -/
noncomputable def fTilde (f : ℝ → ℂ) (ν : ℝ) : ℂ := (Real.exp (ν / 4) : ℂ) * f ν

/-- `m_f = inf_{|ν|≤β} |f̃(ν)|`, (46). -/
noncomputable def mf (β : ℝ) (f : ℝ → ℂ) : ℝ := sInf ((fun ν => ‖fTilde f ν‖) '' Icc (-β) β)

/-- `N_f = sup_{|ν|≤β} |f(ν)|`, (46). -/
noncomputable def Nf (β : ℝ) (f : ℝ → ℂ) : ℝ := sSup ((fun ν => ‖f ν‖) '' Icc (-β) β)

/-- `γ_f = (n/(n−1)) · m_f⁴/(54 N_f²)`, (47). -/
noncomputable def gammaF (β : ℝ) (f : ℝ → ℂ) (n : ℕ) : ℝ :=
  ((n : ℝ) / ((n : ℝ) - 1)) * (mf β f ^ 4 / (54 * Nf β f ^ 2))

/-- The standard normal distribution function `Φ`, p.53. -/
noncomputable def normalCdf (x : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x

/-- The zero-temperature limit `f_∞` of `f(βν)`, p.36: `c₋` for `ν < 0`, `c₀` for `ν = 0`, `0` for
`ν > 0`. -/
noncomputable def fInf (c₀ cm : ℝ) (ν : ℝ) : ℝ := if ν < 0 then cm else if ν = 0 then c₀ else 0

/-- The exponent of the gap in the phase diagram of Theorem 1: `0` for `β < 2`, `1/2` for `β = 2`,
`1` for `β > 2`. -/
noncomputable def phase (β : ℝ) : ℝ := if β < 2 then 0 else if β = 2 then 1 / 2 else 1

end MFHeisGibbs


