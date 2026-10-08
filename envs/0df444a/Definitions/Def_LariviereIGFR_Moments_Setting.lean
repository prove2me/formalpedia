-- Prove2me | Definitions.Def_LariviereIGFR_Moments_Setting
-- name    : LariviereIGFR_Moments_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:11.379385+00:00
-- url     : https://prove2.me/theorems/72f1d6b7-2128-4a51-8bd6-23f59dca580b
-- title:
--   §1 and §3, pp. 602–603 — survival Φ̄, failure rate h, g(ξ) = ξh(ξ), regular density, IGFR, support (α, ∞), E[Xⁿ]
-- statement:
--   This file fixes the objects of Lariviere's note on increasing generalized failure rates that the moment result (Theorem 2) is about.
--
--   A random variable is represented by its law $\nu$, a measure on $\mathbb R$, with distribution function $\Phi(\xi)=\nu((-\infty,\xi])$. Let $\psi:\mathbb R\to\mathbb R$ be a candidate density.
--
--   1. The **survival function** is $\bar\Phi(\xi)=1-\Phi(\xi)$.
--   2. The **failure rate** is $h(\xi)=\psi(\xi)/\bar\Phi(\xi)$.
--   3. The **generalized failure rate** (Lariviere and Porteus 2001) is
--   $$
--   g(\xi)=\xi\,h(\xi).
--   $$
--   4. $\psi$ is a **regular density** of $\nu$ if $\psi\ge 0$, $\nu(A)=\int_A\psi(x)\,dx$ for every Borel set $A$, $\psi(\xi)=\Phi'(\xi)$ at every $\xi$ with $0<\Phi(\xi)<1$, and $\psi(\xi)=0$ at every $\xi$ with $\Phi(\xi)=0$.
--   5. The law is **IGFR** (increasing generalized failure rate) if $g$ is weakly increasing on $\{\xi:\Phi(\xi)<1\}$.
--   6. The law has **support $(\alpha,\infty)$**, for a number $\alpha\ge 0$, if $\Phi(\xi)=0$ exactly when $\xi\le\alpha$ and $\Phi(\xi)<1$ for every $\xi$.
--   7. For a real $n$, the **$n$-th moment** is $\mathbb E[X^n]=\int x^n\,d\nu(x)\in[0,\infty]$; "finite" means $<\infty$.
--
--   These are the paper's standing definitions of §1 (failure rate, generalized failure rate, IGFR on $\{\Phi<1\}$) together with the support and moment notions used in Theorem 2.
--
--   **Formalization Note** The distribution function is Mathlib's `ProbabilityTheory.cdf`. The paper's "Φ has density φ" determines φ only up to a null set, while $h$ and $g$ read φ pointwise; `IsRegDensity` pins the version that is the derivative of Φ on the open support $\{0<\Phi<1\}$ and $0$ where $\Phi=0$ (so that $g$ does not jump at the left end of the support). Measurability of ψ is not a separate clause. Lean's division returns $0$ where $\bar\Phi=0$; IGFR is quantified over $\{\Phi<1\}$, where $\bar\Phi>0$. The moment is a lower Lebesgue integral of $\max(x^n,0)$ (`ENNReal.ofReal (x ^ n)`, real power) valued in $[0,\infty]$, so an infinite moment is $\infty$ and not a junk $0$; for laws with $\nu((-\infty,0))=0$ this is $\int x^n\,d\nu$ exactly. These definitions duplicate those of the companion mission `LariviereIGFR.Char.Setting` (same bodies), because drafts cannot import drafts; `HasSupportIoi` and `nthMoment` are new here.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 602, §1 (Φ̄, h, g, IGFR); p. 603, §3 preamble and Theorem 2 (support (α, ∞), E[Xⁿ])

import Mathlib
import Definitions.Def_LariviereIGFR_Char_Setting

namespace LariviereIGFR.Moments

open MeasureTheory ProbabilityTheory

/-- "`X` has support `(α, ∞)`" (Theorem 2, p. 603), with `0 ≤ α` from §1: the cdf vanishes
exactly on `(-∞, α]` and never reaches `1`. -/
def HasSupportIoi (ν : Measure ℝ) (α : ℝ) : Prop :=
  0 ≤ α ∧ (∀ ξ, cdf ν ξ = 0 ↔ ξ ≤ α) ∧ ∀ ξ, cdf ν ξ < 1

/-- The `n`-th moment `𝔼[Xⁿ] = ∫ xⁿ dν(x)` for real `n`, as an extended nonnegative real
(a lower Lebesgue integral, so an infinite moment is `⊤` rather than a junk `0`). -/
noncomputable def nthMoment (ν : Measure ℝ) (n : ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (x ^ n) ∂ν

end LariviereIGFR.Moments


