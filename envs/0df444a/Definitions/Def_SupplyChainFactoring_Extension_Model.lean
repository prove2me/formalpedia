-- Prove2me | Definitions.Def_SupplyChainFactoring_Extension_Model
-- name    : SupplyChainFactoring_Extension_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:27:12.542227+00:00
-- url     : https://prove2.me/theorems/229be7f3-01f4-41e5-9622-778c846e7793
-- title:
--   Kouvelis–Xu model: strict-IFR demand, credit functions, factoring and reverse factoring profits, and the retailer's problem (13)
-- statement:
--   This file fixes the model of Kouvelis and Xu (2021) used for the retailer's payment extension problem of §5.3.
--
--   **Primitives (§3.1–3.3).** Demand $D\ge 0$ has law $\mu$ with density $f$, cumulative distribution function $F$ and $\bar F = 1-F$. There is a support end $\mathbb Z\in(0,+\infty]$ with $f(\xi)>0$ on $[0,\mathbb Z]$ and $f=0$ outside $[0,\mathbb Z]$; $f$ is continuous on $[0,\mathbb Z]$; $D$ has a finite mean; and the failure rate $z(\xi)=f(\xi)/\bar F(\xi)$ is strictly increasing on $[0,\mathbb Z)$ (strict IFR). Credit ratings lie in $(C_{\min},C_{\max})$ with $0\le C_{\min}$; the default probability $\rho$ takes values in $[0,1]$ and is strictly decreasing there, and the interest premium $\eta$ is positive and (weakly) decreasing there. We write $\rho_j=\rho(C_j)$, $\eta_j=\eta(C_j)$ for $j=s$ (supplier), $r$ (retailer). The lead time $t_1>0$, payment term $t_2>0$, liquidity risks $\lambda_s,\lambda_r\ge0$, unit cost $c>0$ and retail price $p>c$ are fixed.
--
--   **Derived quantities.** Expected sales and the two auxiliary functions are
--   $$S(q)=\int_0^q \bar F(\xi)\,d\xi,\qquad k(q)=\frac{S(q)}{\bar F(q)},\qquad z(q)=\frac{f(q)}{\bar F(q)}.$$
--   The scheme coefficients are $\Lambda_{\mathcal F}(C_s,C_r)=(1-\rho_r)+(1-\rho_s)-e^{\eta_s t_2}$ (recourse), $\Lambda_{\mathcal N}(C_r)=e^{-\eta_r t_2}(1-\rho_r)$ (non-recourse) and $\Lambda_{\mathcal R}=e^{-\eta_r(t_2+\tau)}$ (reverse factoring with payment extension $\tau$), and $c_{\mathcal R}(\tau)=c\,e^{(\eta_s+\lambda_s)t_1+\eta_r(t_2+\tau)}$ is the effective unit cost of reverse factoring (Eq. (12)).
--
--   **Profits.** Under a scheme with coefficient $\Lambda$, the supplier's profit at wholesale price $w$ and quantity $q$ is (Eq. (10))
--   $$\pi(q;w)=(1-\rho_s)\bigl(\Lambda e^{-\lambda_s t_1} w S(q)-c\,q\,e^{\eta_s t_1}\bigr).$$
--   The retailer earns $\Pi(w)=e^{-\lambda_s t_1}(1-\rho_r)(p-w)S(q)$ under factoring and $\Pi_{\mathcal R}(w,\tau)=e^{-\lambda_s t_1}(1-\rho_r)(2-e^{-\lambda_r\tau})(p-w)S(q)$ under reverse factoring.
--
--   **Game-theoretic notions.**
--   1. A *best response* to $w$ is a $q\ge0$ maximizing $\pi(\cdot;w)$ over $q\ge0$.
--   2. An *equilibrium* $(w,q)$ of a factoring scheme has $w\ge0$, $q$ a best response to $w$, and no $w'\ge0$ with a best response $q'$ giving the retailer (the Stackelberg leader) more.
--   3. A scheme is *feasible* if some $w\ge0$ with a best response gives the retailer strictly positive profit.
--   4. With both factoring schemes available, *non-recourse is adopted* if it is feasible and some non-recourse equilibrium gives the supplier at least the profit of every recourse equilibrium (when recourse is feasible); *recourse is adopted* if it is feasible and some recourse equilibrium gives the supplier strictly more than every non-recourse equilibrium (when non-recourse is feasible). Ties go to non-recourse.
--   5. The thresholds $\mathbb C_{\mathcal N}$, $\mathbb C_{\mathcal F}$, $\mathbb C_1$, $\mathbb C^{\max}_{\mathcal R}$ are "the unique value of $C_s$ in $(C_{\min},C_{\max})$" satisfying, respectively, $c_{\mathcal N}=p$, $c_{\mathcal F}=p$, $\Lambda_{\mathcal F}=\Lambda_{\mathcal N}$ and $\Lambda_{\mathcal F}=e^{-\eta_r t_2}$.
--   6. Problem (13) at the existing wholesale price $w_s$: $\tau$ with supplier response $q$ is *feasible* if $\tau\ge0$, $q$ is the supplier's best response under reverse factoring at $(w_s,\tau)$, and the supplier's profit is at least his existing equilibrium profit $\pi_s$; it is *optimal* if no feasible $(\tau',q')$ gives the retailer a larger $\Pi_{\mathcal R}(w_s,\cdot)$.
--   7. $\Xi_{[0,z]}(x)=\max\{0,\min\{z,x\}\}$ is the projection of $x$ onto $[0,z]$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** $\mathbb Z$ is an extended real (`EReal`), $+\infty$ allowed. The paper's "continuous p.d.f. with $f>0$ in $[0,\mathbb Z]$" is read as continuity on $[0,\mathbb Z]$ with $\mathbb Z$ the upper end of the support ($f=0$ beyond it). $\mathbb C_{\mathcal N}$ and $\mathbb C_{\mathcal F}$ are stated cross-multiplied ($c\,e^{(\eta_s+\lambda_s)t_1+\eta_r t_2}=p(1-\rho_r)$ and $c\,e^{(\eta_s+\lambda_s)t_1}=p\,\Lambda_{\mathcal F}$) because $\Lambda_{\mathcal F}$ can be $\le0$. Wholesale prices in equilibria and in feasibility are nonnegative. The paper writes $\Xi_{[0,z]}(x)=0$ "if $x<z$"; this is a misprint for $x<0$, as the words "projection of $x$ onto the line segment $[0,z]$" in the same sentence show.
-- source:
--   Kouvelis and Xu, A Supply Chain Theory of Factoring and Reverse Factoring, Management Science 67(10), 2021, pp. 6075–6076 (§3.1–3.3), p. 6078 (Eq. (8), Proposition 2), p. 6079 (Eq. (9), Proposition 3), p. 6080 (Eq. (10), Proposition 4), p. 6082 (Eq. (12), Π_R), p. 6084 (problem (13), Ξ, ℂ^max_R)

import Mathlib

namespace SupplyChainFactoring.Extension

open MeasureTheory ProbabilityTheory

/-- The primitives of Kouvelis and Xu (2021), §3.1–3.3 (pp. 6074–6075), together with the
standing assumptions stated there.

* Demand `D ≥ 0` has law `μ` with density `f`; `f > 0` on `[0, Z]` (`Z ≤ +∞`, here `Z : EReal`)
  and `f = 0` outside `[0, Z]` (`Z` is the upper end of the support); `f` is continuous on
  `[0, Z]`; `D` has a finite mean; the failure rate `z(ξ) = f(ξ)/F̄(ξ)` is strictly increasing
  on `[0, Z)` (strict IFR).
* Credit ratings lie in `(Cmin, Cmax)`, `0 ≤ Cmin`; the default probability `ρ` takes values
  in `[0, 1]` and is strictly decreasing there; the interest premium `η` is positive and
  (weakly) decreasing there.
* `t1 > 0` lead time, `t2 > 0` payment term, `lamS ≥ 0`, `lamR ≥ 0` liquidity risks of the
  supplier and the retailer, `0 < c < p` unit cost and retail price. -/
structure Model where
  μ : Measure ℝ
  [isProb : IsProbabilityMeasure μ]
  f : ℝ → ℝ
  Z : EReal
  Z_pos : 0 < Z
  f_nonneg : ∀ x, 0 ≤ f x
  density : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))
  f_zero_of_neg : ∀ x : ℝ, x < 0 → f x = 0
  f_zero_of_gt : ∀ x : ℝ, Z < (x : EReal) → f x = 0
  f_pos : ∀ x : ℝ, 0 ≤ x → (x : EReal) ≤ Z → 0 < f x
  f_continuousOn : ContinuousOn f {x : ℝ | 0 ≤ x ∧ (x : EReal) ≤ Z}
  finite_mean : Integrable (fun x : ℝ => x) μ
  strict_ifr : StrictMonoOn (fun x : ℝ => f x / (1 - cdf μ x)) {x : ℝ | 0 ≤ x ∧ (x : EReal) < Z}
  Cmin : ℝ
  Cmax : ℝ
  Cmin_nonneg : 0 ≤ Cmin
  Cmin_lt_Cmax : Cmin < Cmax
  ρ : ℝ → ℝ
  η : ℝ → ℝ
  ρ_mem : ∀ C ∈ Set.Ioo Cmin Cmax, ρ C ∈ Set.Icc (0 : ℝ) 1
  ρ_strictAnti : StrictAntiOn ρ (Set.Ioo Cmin Cmax)
  η_pos : ∀ C ∈ Set.Ioo Cmin Cmax, 0 < η C
  η_antitone : AntitoneOn η (Set.Ioo Cmin Cmax)
  t1 : ℝ
  t2 : ℝ
  lamS : ℝ
  lamR : ℝ
  c : ℝ
  p : ℝ
  t1_pos : 0 < t1
  t2_pos : 0 < t2
  lamS_nonneg : 0 ≤ lamS
  lamR_nonneg : 0 ≤ lamR
  c_pos : 0 < c
  c_lt_p : c < p

namespace Model

variable (M : Model)

/-- Complementary CDF `F̄(x) = 1 − F(x)` of demand. -/
noncomputable def Fbar (x : ℝ) : ℝ := 1 - cdf M.μ x

/-- Expected sales `S(q) = E[min(D, q)] = ∫₀^q F̄(ξ) dξ` (p. 6076). -/
noncomputable def S (q : ℝ) : ℝ := ∫ ξ in (0 : ℝ)..q, M.Fbar ξ

/-- `k(q) = S(q)/F̄(q)` (p. 6076); meaningful for `q ∈ [0, Z)`. -/
noncomputable def k (q : ℝ) : ℝ := M.S q / M.Fbar q

/-- Failure rate `z(q) = f(q)/F̄(q)` (p. 6075); meaningful for `q ∈ [0, Z)`. -/
noncomputable def z (q : ℝ) : ℝ := M.f q / M.Fbar q

/-- `q ∈ (0, Z)`: a positive quantity below the upper end of the demand support. -/
def InSupport (q : ℝ) : Prop := 0 < q ∧ (q : EReal) < M.Z

/-- Recourse coefficient `Λ_𝓕(Cs, Cr) = (1 − ρr) + (1 − ρs) − e^{ηs t2}` (p. 6080). -/
noncomputable def ΛF (Cs Cr : ℝ) : ℝ := (1 - M.ρ Cr) + (1 - M.ρ Cs) - Real.exp (M.η Cs * M.t2)

/-- Non-recourse coefficient `Λ_𝓝(Cr) = e^{−ηr t2}(1 − ρr)` (p. 6080). -/
noncomputable def ΛN (Cr : ℝ) : ℝ := Real.exp (-(M.η Cr * M.t2)) * (1 - M.ρ Cr)

/-- Reverse factoring coefficient `Λ_𝓡 = e^{−ηr(t2+τ)}` (p. 6082). -/
noncomputable def ΛR (Cr τ : ℝ) : ℝ := Real.exp (-(M.η Cr * (M.t2 + τ)))

/-- Effective unit production cost in reverse factoring,
`c_𝓡(τ) = c e^{(ηs+λs)t1 + ηr(t2+τ)}` (Eq. (12), p. 6082). -/
noncomputable def cR (Cs Cr τ : ℝ) : ℝ :=
  M.c * Real.exp ((M.η Cs + M.lamS) * M.t1 + M.η Cr * (M.t2 + τ))

/-- The supplier's expected profit under a post-shipment scheme with coefficient `Λ`,
`π(q; w) = (1 − ρs)(Λ e^{−λs t1} w S(q) − c q e^{ηs t1})` (Eq. (10), p. 6080; for reverse
factoring with `Λ = Λ_𝓡`, p. 6082). -/
noncomputable def supplierProfit (Λ Cs w q : ℝ) : ℝ :=
  (1 - M.ρ Cs) * (Λ * Real.exp (-(M.lamS * M.t1)) * w * M.S q - M.c * q * Real.exp (M.η Cs * M.t1))

/-- `q` is a best response of the supplier to the wholesale price `w` under the scheme with
coefficient `Λ`: it maximizes `π(·; w)` over `q ≥ 0`. -/
def IsBestResponse (Λ Cs w q : ℝ) : Prop :=
  0 ≤ q ∧ ∀ q' : ℝ, 0 ≤ q' → M.supplierProfit Λ Cs w q' ≤ M.supplierProfit Λ Cs w q

/-- The retailer's expected profit under recourse or non-recourse factoring,
`Π(w) = e^{−λs t1}(1 − ρr)(p − w)S(q)` (pp. 6078–6079). -/
noncomputable def retailerProfit (Cr w q : ℝ) : ℝ :=
  Real.exp (-(M.lamS * M.t1)) * (1 - M.ρ Cr) * (M.p - w) * M.S q

/-- The retailer's expected profit under reverse factoring with payment extension `τ`,
`Π_𝓡(w, τ) = e^{−λs t1}(1 − ρr)(2 − e^{−λr τ})(p − w)S(q)` (p. 6082, last line of the display). -/
noncomputable def retailerProfitR (Cr τ w q : ℝ) : ℝ :=
  Real.exp (-(M.lamS * M.t1)) * (1 - M.ρ Cr) * (2 - Real.exp (-(M.lamR * τ))) * (M.p - w) * M.S q

/-- `(w, q)` is a Stackelberg equilibrium of the pull game under the factoring scheme with
coefficient `Λ` (`Λ_𝓕(Cs, Cr)` or `Λ_𝓝(Cr)`): `w ≥ 0`, `q` is a best response to `w`, and no
wholesale price `w' ≥ 0` with a best response `q'` gives the retailer (the leader) more. -/
def IsEquilibrium (Λ Cs Cr w q : ℝ) : Prop :=
  0 ≤ w ∧ M.IsBestResponse Λ Cs w q ∧
    ∀ w' q' : ℝ, 0 ≤ w' → M.IsBestResponse Λ Cs w' q' →
      M.retailerProfit Cr w' q' ≤ M.retailerProfit Cr w q

/-- The factoring scheme with coefficient `Λ` is feasible: some wholesale price `w ≥ 0`, with a
supplier best response to it, gives the retailer a strictly positive expected profit. -/
def Feasible (Λ Cs Cr : ℝ) : Prop :=
  ∃ w q : ℝ, 0 ≤ w ∧ M.IsBestResponse Λ Cs w q ∧ 0 < M.retailerProfit Cr w q

/-- Non-recourse factoring is adopted when both factoring schemes are available: it is feasible,
and its equilibrium supplier profit is at least that of every recourse equilibrium when recourse
factoring is feasible (ties go to non-recourse). -/
def AdoptedNonRecourse (Cs Cr : ℝ) : Prop :=
  M.Feasible (M.ΛN Cr) Cs Cr ∧
    ∃ w q : ℝ, M.IsEquilibrium (M.ΛN Cr) Cs Cr w q ∧
      (M.Feasible (M.ΛF Cs Cr) Cs Cr → ∀ w' q' : ℝ, M.IsEquilibrium (M.ΛF Cs Cr) Cs Cr w' q' →
        M.supplierProfit (M.ΛF Cs Cr) Cs w' q' ≤ M.supplierProfit (M.ΛN Cr) Cs w q)

/-- Recourse factoring is adopted when both factoring schemes are available: it is feasible, and
its equilibrium supplier profit strictly exceeds that of every non-recourse equilibrium when
non-recourse factoring is feasible. -/
def AdoptedRecourse (Cs Cr : ℝ) : Prop :=
  M.Feasible (M.ΛF Cs Cr) Cs Cr ∧
    ∃ w q : ℝ, M.IsEquilibrium (M.ΛF Cs Cr) Cs Cr w q ∧
      (M.Feasible (M.ΛN Cr) Cs Cr → ∀ w' q' : ℝ, M.IsEquilibrium (M.ΛN Cr) Cs Cr w' q' →
        M.supplierProfit (M.ΛN Cr) Cs w' q' < M.supplierProfit (M.ΛF Cs Cr) Cs w q)

/-- `C` is the unique supplier rating in `(Cmin, Cmax)` satisfying `P`. -/
def IsUniqueRating (P : ℝ → Prop) (C : ℝ) : Prop :=
  C ∈ Set.Ioo M.Cmin M.Cmax ∧ P C ∧ ∀ C' ∈ Set.Ioo M.Cmin M.Cmax, P C' → C' = C

/-- `ℂ_𝓝`: the unique `Cs` with `c_𝓝 = p` (Proposition 3, p. 6079), i.e.
`c e^{(ηs+λs)t1 + ηr t2} = p (1 − ρr)`. -/
def IsThresholdN (Cr C : ℝ) : Prop :=
  M.IsUniqueRating
    (fun Cs => M.c * Real.exp ((M.η Cs + M.lamS) * M.t1 + M.η Cr * M.t2) = M.p * (1 - M.ρ Cr)) C

/-- `ℂ_𝓕`: the unique `Cs` with `c_𝓕 = p` (Proposition 2, p. 6078), cross-multiplied:
`c e^{(ηs+λs)t1} = p Λ_𝓕(Cs, Cr)`. -/
def IsThresholdF (Cr C : ℝ) : Prop :=
  M.IsUniqueRating (fun Cs => M.c * Real.exp ((M.η Cs + M.lamS) * M.t1) = M.p * M.ΛF Cs Cr) C

/-- `ℂ_1`: the unique `Cs` with `(1 − ρr) + (1 − ρs) − e^{ηs t2} = e^{−ηr t2}(1 − ρr)`
(Proposition 4, p. 6080). -/
def IsThreshold1 (Cr C : ℝ) : Prop :=
  M.IsUniqueRating (fun Cs => M.ΛF Cs Cr = M.ΛN Cr) C

/-- `ℂ^max_𝓡`: the unique `Cs` with `(1 − ρr) + (1 − ρs) − e^{ηs t2} = e^{−ηr t2}` (p. 6084). -/
def IsThresholdRmax (Cr C : ℝ) : Prop :=
  M.IsUniqueRating (fun Cs => M.ΛF Cs Cr = Real.exp (-(M.η Cr * M.t2))) C

/-- Constraints of the retailer's problem (13) (p. 6084) at the existing wholesale price `ws`:
`τ ≥ 0`, `q` is the supplier's best response under reverse factoring at `(ws, τ)`, and the supplier
accepts, i.e. his profit is at least his profit `πs` in the existing equilibrium. -/
def FeasibleExtension (Cs Cr ws πs τ q : ℝ) : Prop :=
  0 ≤ τ ∧ M.IsBestResponse (M.ΛR Cr τ) Cs ws q ∧ πs ≤ M.supplierProfit (M.ΛR Cr τ) Cs ws q

/-- `(τ, q)` solves problem (13): it is feasible and no feasible `(τ', q')` gives the retailer
a larger `Π_𝓡` at the fixed wholesale price `ws`. -/
def IsOptimalExtension (Cs Cr ws πs τ q : ℝ) : Prop :=
  M.FeasibleExtension Cs Cr ws πs τ q ∧
    ∀ τ' q' : ℝ, M.FeasibleExtension Cs Cr ws πs τ' q' →
      M.retailerProfitR Cr τ' ws q' ≤ M.retailerProfitR Cr τ ws q

end Model

/-- The projection `Ξ_{[0,z]}(x)` of `x` onto `[0, z]` (p. 6084, misprint corrected):
`z` if `x > z`, `0` if `x < 0`, `x` otherwise. -/
noncomputable def Xi (z x : ℝ) : ℝ := max 0 (min z x)

end SupplyChainFactoring.Extension


