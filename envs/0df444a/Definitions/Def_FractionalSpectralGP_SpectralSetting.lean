-- Prove2me | Definitions.Def_FractionalSpectralGP_SpectralSetting
-- name    : FractionalSpectralGP_SpectralSetting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:48.580917+00:00
-- url     : https://prove2.me/theorems/145c95e8-7ce2-4832-9013-1f21af6118fc
-- title:
--   The standing class: $\sigma$ on $[-\tfrac12,\tfrac12]$ with orthonormal basis $(e_{\lambda_n})_{n\ge0}$, $\lambda_0=0$
-- statement:
--   A **spectral setting** consists of
--
--   1. a finite Borel measure $\sigma$ on $\mathbb R$ supported in $[-\tfrac12,\tfrac12]$, i.e. $\sigma(\mathbb R\setminus[-\tfrac12,\tfrac12])=0$;
--   2. a sequence $\lambda_0,\lambda_1,\dots$ of reals with $\lambda_0=0$,
--
--   such that the exponentials $e_{\lambda_n}(u)=e^{i\lambda_nu}$, $n=0,1,\dots$, form an orthonormal basis of $L^2(d\sigma)$.
--
--   This is the class of measures the paper works with ("the measures $\sigma$ we consider are such that an orthonormal basis of $L^2(d\sigma)$ is of the form $e^{i\lambda_nu}$, $n=0,1,\dots$"). Every object of the mission ($T$, $Q_\sigma$, $X_\sigma$, $W_\sigma$) is built from such a setting. Examples are the measures $\sigma_m$ of the paper and Lebesgue measure on $[-\tfrac12,\tfrac12]$ with the frequencies $2\pi\mathbb Z$ enumerated starting from $0$.
--
--   **Formalization Note** The conditions $\lambda_0=0$ and $\operatorname{supp}\sigma\subset[-\tfrac12,\tfrac12]$ are not displayed in the paper but are used: the proof of Lemma 5.1 uses $W^*h_0=1$, i.e. $e_{\lambda_0}=1$, and the support condition is that of $\sigma_m$ (p.8), of the constant in Lemma 3.2 and of the boundedness of $T$. The paper's further condition $\lambda_n\in\pi\mathbb N_0$ is not imposed (no proof uses it). $\sigma(\mathbb R)=1$ follows from $\|e_{\lambda_0}\|=1$.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, end of §3, p.9; §2, p.8; §5, p.12

import Mathlib
import Definitions.Def_FractionalSpectralGP_expL2

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The standing class of measures of the paper (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, end of §3, p.9; §2, p.8;
§5, p.12): a finite Borel measure `σ` on `ℝ` together with an enumeration `λ₀, λ₁, …` of a
spectrum such that `e_{λ_n}`, `n = 0, 1, …`, is an orthonormal basis of `L²(dσ)`, with `λ₀ = 0`
and `σ` supported in `[-1/2, 1/2]`.

**Formalization Note.** The last two clauses are not displayed by the paper but are used: the
proof of Lemma 5.1 (p.12) uses `W* h₀ = 1`, i.e. `e_{λ₀} = 1`, and the support condition is that
of `σ_m` (p.8), of `K` in Lemma 3.2 and of the boundedness of `T` in (5.1). The page's
`λ_n ∈ πℕ₀` and the symmetry of `σ` are not imposed: no proof uses them (generalization; the
paper's measures `σ_m` are instances). `σ(ℝ) = 1` and discreteness of the spectrum follow and are
not fields. -/
structure SpectralSetting where
  /-- The spectral measure `σ`. -/
  σ : Measure ℝ
  /-- `σ` is a finite measure. -/
  [isFinite : IsFiniteMeasure σ]
  /-- The enumeration `n ↦ λ_n` of the spectrum. -/
  lam : ℕ → ℝ
  /-- The exponentials `e_{λ_n}` are orthonormal in `L²(dσ)`. -/
  orthonormal : Orthonormal ℂ (fun n => expL2 σ (lam n))
  /-- The exponentials `e_{λ_n}` span a dense subspace of `L²(dσ)`. -/
  dense : ⊤ ≤ (Submodule.span ℂ (Set.range fun n => expL2 σ (lam n))).topologicalClosure
  /-- `λ₀ = 0`, so `e_{λ₀} = 1`. -/
  lam_zero : lam 0 = 0
  /-- `σ` is supported in `[-1/2, 1/2]`. -/
  support : σ (Set.Icc (-1/2 : ℝ) (1/2))ᶜ = 0

attribute [instance] SpectralSetting.isFinite

end FractionalSpectralGP


