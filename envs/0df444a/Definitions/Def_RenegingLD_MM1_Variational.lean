-- Prove2me | Definitions.Def_RenegingLD_MM1_Variational
-- name    : RenegingLD_MM1_Variational
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:14.626206+00:00
-- url     : https://prove2.me/theorems/5bebd27b-55f0-4969-b0bb-57c73d7a6a8c
-- title:
--   §4–§6, pp. 18–30 — the class C_T, the local rate L, Λ(A, T), equation (5.9), the candidate (ξ̄, ζ̄) of (5.3)–(5.4) and γ*_T
-- statement:
--   This file adds the objects of §§4–6 of the paper used to analyse the variational problem $I^*_{\gamma,T}$. The parameters $\lambda,\mu,\theta>0$, $x_0\ge0$, $T>0$ and the function $\ell$ are as in the model file.
--
--   1. **The class $\mathcal C_T$ (p. 18).** The pairs $(\xi,\zeta)$ of continuous functions $[0,T]\to\mathbb R_+$ such that (i) $\xi(0)=x_0$, $\zeta(0)=0$; (ii) $\xi,\zeta$ are absolutely continuous and $\zeta'(t)=0$ for a.e. $t\in[0,T]$ with $\xi(t)=0$; (iii) $\zeta$ is nondecreasing.
--   2. **The local rate (p. 19).** For $(x,p,q)\in\mathbb R_+\times\mathbb R\times\mathbb R_+$,
--   $$L(x,p,q)=\lambda\ell\Big(\tfrac{\sqrt{(p+q)^2+4\lambda\mu}+(p+q)}{2\lambda}\Big)+\mu\ell\Big(\tfrac{\sqrt{(p+q)^2+4\lambda\mu}-(p+q)}{2\mu}\Big)+\theta x\,\ell\Big(\tfrac{q}{\theta x}\Big)\mathbf 1_{\{x>0\}}+\infty\cdot\mathbf 1_{\{x=0,\,q>0\}} .$$
--   3. **$\Lambda$ and equation (5.9) (p. 23).** $\Lambda(A,T)=\dfrac{e^{-\theta T}-A}{1-A}$, and (5.9) is the equation in $A$
--   $$\frac{1}{1-Ae^{\theta T}}=\frac{1}{2\lambda[\theta T-1+e^{-\theta T}]}\Big\{\theta[\gamma T-x_0+x_0\Lambda(A,T)]+\Big(\theta^2[\gamma T-x_0+x_0\Lambda(A,T)]^2-4\lambda[\theta T-1+e^{-\theta T}]\,\mu\,[\log\Lambda(A,T)-\Lambda(A,T)+1]\Big)^{1/2}\Big\}.$$
--   4. **The candidate minimizer (5.3)–(5.4) (p. 23).** For constants $A,B$,
--   $$\bar\xi(t)=\frac{e^{-\theta t}-A}{1-A}x_0+\frac{\lambda B}{\theta}(e^{\theta t}-1)(e^{-\theta t}-A)+\frac{\mu}{\theta B}\,\frac{e^{-\theta t}-1}{1-A},$$
--   $$\bar\zeta(t)=\frac{\lambda B}{\theta}\big[\theta t-1+e^{-\theta t}\big]+\frac{\mu}{\theta B}\Big[\log\frac{e^{-\theta t}-A}{1-A}-\frac{e^{-\theta t}-A}{1-A}+1\Big]+\frac{1-e^{-\theta t}}{1-A}x_0 .$$
--   Construction 5.3 takes $A\in(-\infty,e^{-\theta T})$ the root of (5.9) and $B=1/(1-Ae^{\theta T})$.
--   5. **The LLN reneging rate (Lemma 6.1, p. 30).** $\gamma^*_T=(\lambda-\mu)+\frac{1-e^{-\theta T}}{T}\Big(x_0-\frac{\lambda-\mu}{\theta}\Big)$.
--
--   These are the ingredients of the proof that $I^*_{\gamma,T}/T\to C(\gamma)$: $L$ gives an integral form of $I_T$ on $\mathcal C_T$, $(\bar\xi,\bar\zeta)$ is the explicit minimizer for $x_0>0$, and $\gamma^*_T T$ is the reneging of the zero-cost (law of large numbers) path.
--
--   **Formalization Note.** $\xi',\zeta'$ are Lean's `deriv`, which is the a.e. derivative for absolutely continuous functions (and $0$ at the null set where it does not exist). The local rate is valued in $[0,\infty]$; its three real terms are nonnegative on the stated domain, so the `ENNReal.ofReal` coercions lose nothing there; the indicator terms are an if-then-else. Equation (5.9) is a proposition about $A$; the root is never chosen by `Classical.choose` — statements quantify over every $A<e^{-\theta T}$ satisfying (5.9) (Lemma 5.2(a) states that there is exactly one). For $A<e^{-\theta T}$ and $T>0$ every logarithm, square root and denominator in (5.9) is honest: $\Lambda\in(0,1)$, the radicand is $\ge0$, $1-Ae^{\theta T}>0$ and $\theta T-1+e^{-\theta T}>0$. The definitions are duplicates of nothing on the platform.
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 18 (C_T), p. 19 (L), p. 23 ((5.3), (5.4), Λ(A, T), (5.9)), p. 25 (Construction 5.3), p. 30 (Lemma 6.1, γ*_T)

import Mathlib
import Definitions.Def_RenegingLD_MM1_Model

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

/-- The class `C_T` of §4 (p. 18): continuous nonnegative paths on `[0, T]` with
(i) `ξ(0) = x₀`, `ζ(0) = 0`; (ii) `ξ`, `ζ` absolutely continuous and `ζ′(t) = 0` for a.e.
`t ∈ [0, T]` with `ξ(t) = 0`; (iii) `ζ` nondecreasing. -/
def InCT (x0 T : ℝ) (ξ ζ : ℝ → ℝ) : Prop :=
  IsPath T ξ ζ ∧ ξ 0 = x0 ∧ ζ 0 = 0 ∧
    AbsolutelyContinuousOnInterval ξ 0 T ∧ AbsolutelyContinuousOnInterval ζ 0 T ∧
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ξ t = 0 → deriv ζ t = 0) ∧
    MonotoneOn ζ (Set.Icc 0 T)

/-- The local rate `L(x, p, q)` of §4 (p. 19), for `(x, p, q) ∈ ℝ₊ × ℝ × ℝ₊`:
`λℓ((√((p+q)² + 4λµ) + (p+q))/(2λ)) + µℓ((√((p+q)² + 4λµ) − (p+q))/(2µ))
 + θxℓ(q/(θx))·1{x>0} + ∞·1{x=0, q>0}`. -/
noncomputable def Lloc (lam mu θ x p q : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (lam * ell ((Real.sqrt ((p + q) ^ 2 + 4 * lam * mu) + (p + q)) / (2 * lam)))
    + ENNReal.ofReal (mu * ell ((Real.sqrt ((p + q) ^ 2 + 4 * lam * mu) - (p + q)) / (2 * mu)))
    + (if 0 < x then ENNReal.ofReal (θ * x * ell (q / (θ * x))) else if 0 < q then ⊤ else 0)

/-- `Λ(A, T) = (e^{−θT} − A)/(1 − A)` (§5, p. 23). -/
noncomputable def Lam (θ A T : ℝ) : ℝ := (Real.exp (-θ * T) - A) / (1 - A)

/-- Equation (5.9) for `A`:
`1/(1 − Ae^{θT}) = (1/(2λ[θT − 1 + e^{−θT}])) {θ[γT − x₀ + x₀Λ(A,T)]
  + (θ²[γT − x₀ + x₀Λ(A,T)]² − 4λ[θT − 1 + e^{−θT}] µ [log Λ(A,T) − Λ(A,T) + 1])^{1/2}}`. -/
def eq59 (lam mu θ γ x0 T A : ℝ) : Prop :=
  1 / (1 - A * Real.exp (θ * T)) =
    1 / (2 * lam * (θ * T - 1 + Real.exp (-θ * T))) *
      (θ * (γ * T - x0 + x0 * Lam θ A T)
        + Real.sqrt (θ ^ 2 * (γ * T - x0 + x0 * Lam θ A T) ^ 2
            - 4 * lam * (θ * T - 1 + Real.exp (-θ * T)) * mu
              * (Real.log (Lam θ A T) - Lam θ A T + 1)))

/-- The candidate state trajectory (5.3):
`ξ(t) = ((e^{−θt} − A)/(1 − A)) x₀ + (λB/θ)(e^{θt} − 1)(e^{−θt} − A) + (µ/(θB))(e^{−θt} − 1)/(1 − A)`. -/
noncomputable def xiBar (lam mu θ x0 A B t : ℝ) : ℝ :=
  (Real.exp (-θ * t) - A) / (1 - A) * x0
    + lam * B / θ * (Real.exp (θ * t) - 1) * (Real.exp (-θ * t) - A)
    + mu / (θ * B) * ((Real.exp (-θ * t) - 1) / (1 - A))

/-- The candidate reneging trajectory, second line of (5.4):
`ζ(t) = (λB/θ)[θt − 1 + e^{−θt}] + (µ/(θB))[log((e^{−θt} − A)/(1 − A)) − (e^{−θt} − A)/(1 − A) + 1]
  + ((1 − e^{−θt})/(1 − A)) x₀`. -/
noncomputable def zetaBar (lam mu θ x0 A B t : ℝ) : ℝ :=
  lam * B / θ * (θ * t - 1 + Real.exp (-θ * t))
    + mu / (θ * B) * (Real.log ((Real.exp (-θ * t) - A) / (1 - A))
        - (Real.exp (-θ * t) - A) / (1 - A) + 1)
    + (1 - Real.exp (-θ * t)) / (1 - A) * x0

/-- `γ*_T = (λ − µ) + ((1 − e^{−θT})/T)(x₀ − (λ − µ)/θ)` (Lemma 6.1, p. 30). -/
noncomputable def gammaStar (lam mu θ x0 T : ℝ) : ℝ :=
  (lam - mu) + (1 - Real.exp (-θ * T)) / T * (x0 - (lam - mu) / θ)

end RenegingLD.MM1


