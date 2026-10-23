-- Prove2me | Definitions.Def_PricingSamples_OneSampleMHR_Setting
-- name    : PricingSamples_OneSampleMHR_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:53:29.46498+00:00
-- url     : https://prove2.me/theorems/a12cc764-2e59-498b-81a1-abcbcfbac66c
-- title:
--   §2, pp. 10–17 — value laws in G, the ccdf F̄, opt(F), Γ_α, Γ_α^{−1}, G_α (7), α-strong regularity (Definition 2), 𝓕_α, r_F, the one-sample revenue of δ_γ
-- statement:
--   The model of Allouah, Bahamou and Besbes, *Pricing with Samples* (§2, pp. 10–12; §3.1, pp. 12–14; §4.1, pp. 16–17).
--
--   A seller sells one good to one buyer whose value $v \ge 0$ is drawn from a distribution $F$ on $[0,\infty)$. The **complementary cdf** is $\bar F(p) = 1 - F(p) = \mathbb P(v > p)$; posting the price $p$ earns $p\,\bar F(p)$ in expectation. The class $\mathcal G$ consists of all such $F$ with $0 < \mathbb E_F[v] < \infty$, and the **oracle revenue** is
--
--   $$\mathrm{opt}(F) = \sup_{p \ge 0}\, p\,\bar F(p),$$
--
--   which lies in $(0,\infty)$ for every $F \in \mathcal G$. An **oracle optimal price** $r_F$ is a maximizer of $p \mapsto p\bar F(p)$ on $[0,\infty)$, and $q_w := \bar F(w)$ denotes the quantile at $w$.
--
--   **Generalized Pareto tails.** For $v \ge 0$,
--
--   $$\Gamma_\alpha(v) = \begin{cases} (1 + (1-\alpha) v)^{-1/(1-\alpha)} & \alpha \in [0,1),\\ e^{-v} & \alpha = 1,\end{cases}\qquad \Gamma_\alpha^{-1}(q) = \begin{cases} \dfrac{q^{-(1-\alpha)} - 1}{1-\alpha} & \alpha \in [0,1),\\ -\ln q & \alpha = 1,\end{cases}$$
--
--   for $q \in (0,1]$, with the conventions $\Gamma_\alpha^{-1}(0) = +\infty$ and $\Gamma_\alpha(+\infty) = 0$. For $w < w'$ and $q' \le q$, the two-point interpolant of eq. (7) is
--
--   $$G_\alpha\big(v \,\big|\, (w,q),(w',q')\big) = q\,\Gamma_\alpha\!\Big(\Gamma_\alpha^{-1}\big(\tfrac{q'}{q}\big)\,\frac{v-w}{w'-w}\Big),$$
--
--   the generalized Pareto tail through $(w,q)$ and $(w',q')$.
--
--   **α-strong regularity.** For $\alpha \in [0,1]$, $F$ is **$\alpha$-strongly regular** if it has a density and its virtual value $\varphi_F(v) = v - (1-F(v))/f(v)$ satisfies $\varphi_F(v') - \varphi_F(v) \ge \alpha (v' - v)$ for $v' \ge v$ in the support (Definition 2). Equivalently (p. App-10), $v \mapsto \Gamma_\alpha^{-1}(\bar F(v))$ is convex where $\bar F > 0$. The class $\mathcal F_\alpha = \{F \in \mathcal G : F \text{ is } \alpha\text{-SR}\}$ decreases in $\alpha$; $\mathcal F_0$ is the class of regular distributions and $\mathcal F_1$ the class of **monotone hazard rate** (mhr) distributions.
--
--   **One-sample pricing.** The mechanism $\delta_\gamma$ observes one sample $s \sim F$, independent of $v$, and posts the price $\gamma s$. Its expected revenue is
--
--   $$\mathbb E_{s\sim F}\big[\gamma s\,\bar F(\gamma s)\big] = \int_0^\infty \gamma s\,\bar F(\gamma s)\,dF(s),$$
--
--   and its performance against $F$ is this revenue divided by $\mathrm{opt}(F)$ (eqs. (3)–(4)).
--
--   These objects carry every statement of the mission: the goal bounds the revenue of $\delta_{0.76}$ against $\mathrm{opt}(F)$ on $\mathcal F_1$, Lemma 2 and Lemma G-1 compare $\bar F$ with $G_\alpha$, and Lemma 1 bounds local revenue integrals through generalized inverses.
--
--   **Formalization Note** A law is a measure $\mu$ on $\mathbb R$; $\mathcal G$ asks for a probability measure with $\mu((-\infty,0)) = 0$, $v \mapsto v$ integrable and $\int v\,d\mu > 0$. The ccdf is the strict tail $\bar F(p) = \mu((p,\infty))$. On $\mathcal G$ the set $\{p\bar F(p) : p \ge 0\}$ is nonempty and bounded above by $\mathbb E[v]$, so `sSup` is the true supremum. α-strong regularity is encoded in its convexity form: $\mu$ is absolutely continuous (admits a density) and $v \mapsto \Gamma_\alpha^{-1}(\bar F(v))$ is convex on $\{v \ge 0 : \bar F(v) > 0\}$; this takes the support to be an interval, as the paper's proofs do. $\Gamma_\alpha$ and $\Gamma_\alpha^{-1}$ treat $\alpha = 1$ as a separate branch (Lean's $1/0 = 0$ would otherwise turn $\Gamma_1$ into a constant). $G_\alpha$ encodes the conventions for $q' = 0$ explicitly: the value is $q$ for $v \le w$ and $0$ for $v > w$. `IsOptPrice μ r` says $r \ge 0$ maximizes $p \mapsto p\bar F(p)$ on $[0,\infty)$. `genInv H q` is the generalized inverse $\inf\{x \ge 0 : H(x) \le q\}$ of a non-increasing $H$, the analogue of $F^{-1}(1-q) = \inf\{v \in \mathbb R_+ : F(v) \ge 1-q\}$ (p. 12), and `minGenInv c H q` $= \inf(\{c\} \cup \{x \ge 0 : H(x) \le q\}) = \min(c, H^{-1}(q))$ with $\inf\emptyset = +\infty$.
-- source:
--   Allouah, Bahamou, Besbes, Pricing with Samples, SSRN 3334650 (rev. 06/02/2021), pp. 10–14 (eq. (1), class G, Definition 2, 𝓕_α, r_F, generalized inverse, eqs. (3)–(4)), p. 16 (Γ_α), p. 17 (eq. (7)), p. App-9 (Γ_α^{−1}), p. App-10 (convexity form of α-SR)

import Mathlib

namespace PricingSamples.OneSampleMHR

open MeasureTheory

/-- The complementary cdf `F̄(p) = 1 − F(p) = P(v > p)` of a value law `μ` on `ℝ` (§2, p. 10),
with the strict tail `(p, ∞)`. -/
noncomputable def ccdf (μ : Measure ℝ) (p : ℝ) : ℝ :=
  (μ (Set.Ioi p)).toReal

/-- The class `G` (§2, p. 11): laws `F` of a buyer value with support in `[0, ∞)` and
`0 < E_F[v] < ∞`. -/
def InG (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Iio 0) = 0 ∧ Integrable (fun v : ℝ => v) μ ∧
    0 < ∫ v, v ∂μ

/-- The oracle revenue `opt(F) = sup_{p ≥ 0} p F̄(p)` (eq. (1), p. 10). On `G` the set is
nonempty and bounded above by `E_F[v]`, so `sSup` is the true supremum. -/
noncomputable def opt (μ : Measure ℝ) : ℝ :=
  sSup ((fun p : ℝ => p * ccdf μ p) '' Set.Ici 0)

/-- The generalized Pareto tail `Γ_α` (p. 16): `Γ_α(v) = (1 + (1 − α) v)^{−1/(1−α)}` for
`α ∈ [0, 1)` and `Γ_1(v) = e^{−v}`. Used for `v ≥ 0`. -/
noncomputable def GammaA (α v : ℝ) : ℝ :=
  if α = 1 then Real.exp (-v) else (1 + (1 - α) * v) ^ (-(1 / (1 - α)))

/-- The inverse `Γ_α^{−1}` of `Γ_α` on `(0, 1]` (p. App-9): `(q^{−(1−α)} − 1)/(1 − α)` for
`α ∈ [0, 1)` and `−ln q` for `α = 1`. Used for `q ∈ (0, 1]`; the paper's convention
`Γ_α^{−1}(0) = +∞` is handled inside `Galpha`. -/
noncomputable def GammaAInv (α q : ℝ) : ℝ :=
  if α = 1 then -Real.log q else (q ^ (-(1 - α)) - 1) / (1 - α)

/-- `G_α(v | (w, q), (w′, q′)) = q Γ_α(Γ_α^{−1}(q′/q) (v − w)/(w′ − w))` (eq. (7), p. 17), for
`w′ ≥ v ≥ w ≥ 0`, `q′ ≤ q` (and, as in Lemma 2, also for `v ≥ w′`). When `q′ = 0` the paper's
conventions `Γ_α^{−1}(0) = +∞`, `Γ_α(+∞) = 0` give the value `q` at `v = w` and `0` for `v > w`;
the `if` encodes exactly this. -/
noncomputable def Galpha (α w q w' q' v : ℝ) : ℝ :=
  if q' = 0 then (if v ≤ w then q else 0)
  else q * GammaA α (GammaAInv α (q' / q) * ((v - w) / (w' - w)))

/-- α-strong regularity (Definition 2, pp. 11–12), in the equivalent form the paper uses in the
proof of Lemma 2 (p. App-10, after Schweizer–Szech): `F` admits a density (`μ ≪ Lebesgue`) and
`v ↦ Γ_α^{−1}(F̄(v))` is convex on `{v ≥ 0 : F̄(v) > 0}`. For `α = 1` this says `−log F̄` is
convex there (monotone hazard rate); for `α = 0` that `1/F̄` is convex (regularity). -/
def IsAlphaSR (α : ℝ) (μ : Measure ℝ) : Prop :=
  μ ≪ volume ∧
    ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < ccdf μ v} (fun v => GammaAInv α (ccdf μ v))

/-- The class `𝓕_α = {F ∈ G : F is α-SR}` (p. 12). `𝓕_1` is the monotone hazard rate class. -/
def InFAlpha (α : ℝ) (μ : Measure ℝ) : Prop :=
  InG μ ∧ IsAlphaSR α μ

/-- `r` is an oracle optimal price: a maximizer of `p ↦ p F̄(p)` over `p ≥ 0` (p. 12, `r_F`). -/
def IsOptPrice (μ : Measure ℝ) (r : ℝ) : Prop :=
  0 ≤ r ∧ IsMaxOn (fun p : ℝ => p * ccdf μ p) (Set.Ici 0) r

/-- Expected revenue of the deterministic multiplicative mechanism `δ_γ`, which posts the price
`γ s` after observing one sample `s ∼ F` (eqs. (3)–(4), pp. 13–14):
`E_s[γ s F̄(γ s)] = ∫ γ s F̄(γ s) dF(s)`. -/
noncomputable def postRev (γ : ℝ) (μ : Measure ℝ) : ℝ :=
  ∫ s, γ * s * ccdf μ (γ * s) ∂μ

/-- The generalized inverse of a non-increasing `H : ℝ_+ → [0, 1]`, `H^{−1}(q) = inf{x ≥ 0 :
H(x) ≤ q}`, the analogue for a ccdf of `F^{−1}(1 − q) = inf{v ∈ ℝ_+ : F(v) ≥ 1 − q}` (p. 12). -/
noncomputable def genInv (H : ℝ → ℝ) (q : ℝ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ H x ≤ q}

/-- `min(c, H^{−1}(q))` with the paper's convention `inf ∅ = +∞` (so the value is `c` when no
`x ≥ 0` has `H(x) ≤ q`): the infimum of `{c} ∪ {x ≥ 0 : H(x) ≤ q}`. -/
noncomputable def minGenInv (c : ℝ) (H : ℝ → ℝ) (q : ℝ) : ℝ :=
  sInf (insert c {x : ℝ | 0 ≤ x ∧ H x ≤ q})

end PricingSamples.OneSampleMHR


