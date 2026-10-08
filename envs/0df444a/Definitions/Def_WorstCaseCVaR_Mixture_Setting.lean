-- Prove2me | Definitions.Def_WorstCaseCVaR_Mixture_Setting
-- name    : WorstCaseCVaR_Mixture_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:26.504593+00:00
-- url     : https://prove2.me/theorems/ec8e19af-0736-47bc-8c22-daf4d81609fc
-- title:
--   Setting of §2–§2.1: $F_\beta$ (1), CVaR (2), mixtures (4), $F^i_\beta$, $F^{\mathcal L}_\beta$, $H_\beta$, WCVaR (3)
-- statement:
--   This file fixes the objects of §2 and §2.1 of Zhu and Fukushima (2009) on which every statement of the mission rests.
--
--   A decision $x\in\mathbb R^n$ and a random vector $y\in\mathbb R^m$ determine a loss $f(x,y)\in\mathbb R$. Fix a confidence level $\beta$ and write $[t]^+=\max\{t,0\}$.
--
--   1. **Rockafellar–Uryasev function (1).** For a probability distribution $P$ of $y$,
--   $$F_\beta(x,\alpha)=\alpha+\frac{1}{1-\beta}\int_{\mathbb R^m}[f(x,y)-\alpha]^+\,dP(y),\qquad \alpha\in\mathbb R.$$
--   2. **Conditional value-at-risk (2).** $\mathrm{CVaR}_\beta(x)=\min_{\alpha\in\mathbb R}F_\beta(x,\alpha)$, written as the infimum of the values $F_\beta(x,\alpha)$, $\alpha\in\mathbb R$.
--   3. **Mixtures (4)–(5).** Given $l$ likelihood distributions $P^1,\dots,P^l$ and a weight vector $\lambda$ in the probability simplex $\Lambda=\{\lambda\in\mathbb R^l:\ \lambda_i\ge0,\ \sum_i\lambda_i=1\}$, the mixture is $\sum_{i=1}^l\lambda_iP^i$.
--   4. **Component functions.** $F^i_\beta(x,\alpha)$ is the function (1) for $P^i$, and $F^{\mathcal L}_\beta(x,\alpha)=\max_{i\in\mathcal L}F^i_\beta(x,\alpha)$ with $\mathcal L=\{1,\dots,l\}$, $l\ge1$.
--   5. **The function of the proof of Theorem 1.** $H_\beta(x,\alpha,\lambda)$ is the function (1) for the mixture $\sum_i\lambda_iP^i$.
--   6. **Worst-case CVaR (3).** Over the mixture family $\mathcal P_M$,
--   $$\mathrm{WCVaR}_\beta(x)=\sup_{\lambda\in\Lambda}\mathrm{CVaR}_\beta(x)\ \text{under}\ \textstyle\sum_i\lambda_iP^i .$$
--
--   Every theorem of the mission is stated in terms of these objects.
--
--   **Formalization Note** Distributions are probability measures on `Fin m → ℝ` rather than densities; Remark 1 of the paper states every result for general distributions, and a density $p$ is the measure $p\cdot\mathrm{Leb}$. Indices run over `Fin l` (zero-based). CVaR is the real `sInf` of the range of $\alpha\mapsto F_\beta(x,\alpha)$; under $0<\beta<1$ and integrable loss this range is bounded below and its infimum is attained, which is what the theorems assume. The mixture is the finite sum of measures $\sum_i \mathrm{ofReal}(\lambda_i)\cdot P^i$ and WCVaR is the real `sSup` of the image of the simplex, which is nonempty for $l\ge1$. The bodies of $F_\beta$ and CVaR coincide with those of the platform definition `Local_Definitions_KallCVar`, which is not reused because it declares itself provisional.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1156, Eq. (1)–(2); p. 1157, Definition 1, Eq. (3)–(5), F^i_β, F^𝓛_β; p. 1158, Remark 1; p. 1166, proof of Theorem 1, H_β

import Mathlib

open MeasureTheory

namespace WorstCaseCVaR.Mixture

/-- The Rockafellar–Uryasev function (1) of Zhu–Fukushima (p. 1156):
`F_β(x, α) = α + (1 - β)⁻¹ ∫ [f(x, y) - α]⁺ dP(y)`, for a probability measure `P` on `ℝᵐ`
(the paper's density `p(·)`; Remark 1 extends every result to general distributions). -/
noncomputable def ruFun {m n : ℕ} (P : Measure (Fin m → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (x : Fin n → ℝ) (α : ℝ) : ℝ :=
  α + (1 - β)⁻¹ * ∫ y, max (f x y - α) 0 ∂P

/-- CVaR via formula (2) (p. 1156): `CVaR_β(x) = min_{α ∈ ℝ} F_β(x, α)`, written as the
infimum of the range of `α ↦ F_β(x, α)`. For `0 < β < 1` and integrable loss the range is
bounded below and the infimum is attained, so this real `sInf` is the paper's minimum. -/
noncomputable def cvar {m n : ℕ} (P : Measure (Fin m → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (x : Fin n → ℝ) : ℝ :=
  sInf (Set.range (ruFun P f β x))

/-- The mixture `∑ᵢ λᵢ Pⁱ` of the likelihood distributions `P 0, …, P (l-1)` (Eq. (4), p. 1157),
for a weight vector `lam` (meant to lie in the simplex `Λ = stdSimplex ℝ (Fin l)` of Eq. (5)). -/
noncomputable def mixture {l m : ℕ} (P : Fin l → Measure (Fin m → ℝ)) (lam : Fin l → ℝ) :
    Measure (Fin m → ℝ) :=
  ∑ i, ENNReal.ofReal (lam i) • P i

/-- `F^i_β(x, α)` (p. 1157): the Rockafellar–Uryasev function of the `i`-th likelihood
distribution. -/
noncomputable def Fi {l m n : ℕ} (P : Fin l → Measure (Fin m → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (x : Fin n → ℝ) (i : Fin l) (α : ℝ) : ℝ :=
  ruFun (P i) f β x α

/-- `F^𝓛_β(x, α) = max_{i ∈ 𝓛} F^i_β(x, α)` (p. 1157), `𝓛 = Fin l` with `l ≠ 0`. -/
noncomputable def FL {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (x : Fin n → ℝ) (α : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => Fi P f β x i α)

/-- `H_β(x, α, λ)` of the proof of Theorem 1 (p. 1166): the Rockafellar–Uryasev function of the
mixture `∑ᵢ λᵢ Pⁱ`. -/
noncomputable def Hfun {l m n : ℕ} (P : Fin l → Measure (Fin m → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (x : Fin n → ℝ) (α : ℝ) (lam : Fin l → ℝ) : ℝ :=
  ruFun (mixture P lam) f β x α

/-- Worst-case CVaR (Definition 1, Eq. (3), p. 1157) over the mixture set `𝒫_M` of Eq. (4):
`WCVaR_β(x) = sup_{λ ∈ Λ} CVaR_β(x)` under `∑ᵢ λᵢ Pⁱ`, the supremum of the image of the
simplex `Λ`. -/
noncomputable def wcvar {l m n : ℕ} (P : Fin l → Measure (Fin m → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup ((fun lam => cvar (mixture P lam) f β x) '' stdSimplex ℝ (Fin l))

end WorstCaseCVaR.Mixture


