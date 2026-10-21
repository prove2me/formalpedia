-- Prove2me | Definitions.Def_SmoothBandit_Regret_Model
-- name    : SmoothBandit_Regret_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:04.067415+00:00
-- url     : https://prove2.me/theorems/14844b50-83d7-427e-bad6-974930fa7329
-- title:
--   §2, pp. 7–12 — two-armed smooth contextual bandit: Hölder class, (c₀, r₀)-regularity, Assumptions 1–4, the class 𝒫, and the constants p, λ₀, C₀
-- statement:
--   This file fixes the model of the smooth contextual bandit problem of Hu, Kallus and Mao.
--
--   **Instances.** Contexts live in $\mathbb R^d$ with the Euclidean norm. There are two arms, $+1$ and $-1$. At rounds $t = 1, 2, \dots$ nature draws $(X_t, Y_t(1), Y_t(-1))$ i.i.d. from a common law, where $X_t$ is the context and $Y_t(\pm1) \in [0,1]$ are the rewards of the two arms. Alongside, the probability space carries i.i.d. fair coins, independent of the data, which the algorithm uses whenever it must "pull $\pm1$ randomly, equiprobably". An instance records the support $\mathcal X$ of the context, the contexts, the potential rewards, the coins, and the conditional mean rewards $\eta_{\pm1}(x) = E[Y(\pm1) \mid X = x]$, the last stated as $\int_{\{X_t \in A\}} Y_t(a)\,dP = \int_{\{X_t \in A\}} \eta_a(X_t)\,dP$ for every measurable $A$, with $\eta_a(X_t)$ integrable. The **conditional average treatment effect** is $\tau = \eta_1 - \eta_{-1}$, the **optimal decision regions** are $\mathcal Q_a = \{x \in \mathcal X : a\tau(x) \ge 0\}$, and the oracle policy is $\pi^*(x) = +1$ if $\tau(x) \ge 0$ and $-1$ otherwise.
--
--   **Hölder class (Definition 1).** For $\beta > 0$ let $\mathfrak b(\beta)$ be the largest integer strictly below $\beta$ and $M_\beta$ the number of multi-indices $r \in \mathbb Z_+^d$ with $|r| \le \mathfrak b(\beta)$. A function $\eta$ with values in $[0,1]$ on $\mathcal X$ is $(\beta, L, \mathcal X)$-Hölder if it is $\mathfrak b(\beta)$-times continuously differentiable and, for all $x, x' \in \mathcal X$,
--
--   $$\Big|\eta(x') - \sum_{|r| \le \mathfrak b(\beta)} \frac{(x'-x)^r}{r!} D^r\eta(x)\Big| \le L\|x'-x\|^\beta .$$
--
--   **Regularity (Definition 2).** A set $S$ is weakly $(c, r)$-regular at $x$ if $\mathrm{Leb}[S \cap \mathcal B(x, r)] \ge c\,\mathrm{Leb}[\mathcal B(x,r)]$, with $\mathcal B(x, r)$ the closed ball; strongly $(c_0, r_0)$-regular at $x$ if this holds for all $0 \le r \le r_0$; and a $(c_0, r_0)$-regular set if it is Lebesgue measurable and strongly regular at each of its points.
--
--   **Assumptions.**
--   1. (Smoothness) For $a = \pm1$, $\eta_a$ is $(\beta, L, \mathcal X)$-Hölder and $(1, L_1, \mathcal X)$-Hölder.
--   2. (Regular decision regions) For $a = \pm1$, $\mathcal Q_a$ is a non-empty $(c_0, r_0)$-regular set.
--   3. (Strong density) $\mathcal X$ is compact, $\mathcal X \subseteq [0,1]^d$, $X \in \mathcal X$ almost surely, and $\mu_{\min}\mathrm{Leb}(A) \le P(X \in A) \le \mu_{\max}\mathrm{Leb}(A)$ for measurable $A \subseteq \mathcal X$.
--   4. (Margin) $P(0 < |\tau(X)| \le t) \le \gamma t^\alpha$ for all $t > 0$.
--
--   The class $\mathcal P(\beta, L_1, L, c_0, r_0, \mu_{\min}, \mu_{\max}, \gamma, \alpha)$ consists of the instances satisfying all four. The standing parameter range is $\beta \ge 1$, $L, L_1 > 0$, $0 < c_0 \le 1$, $r_0 > 0$, $0 < \mu_{\min} \le \mu_{\max}$, $\gamma > 0$, $\alpha \ge 0$.
--
--   **Constants.** $v_d$ is the volume of the unit ball, $p = \mu_{\min} c_0 r_0^d v_d$ (Lemma 1), and
--
--   $$\lambda_0 = \tfrac14 \mu_{\min} \inf_{\substack{W \in \mathbb R^{M_\beta},\ \|W\| = 1\\ S \subseteq \mathcal B(0,1) \text{ compact},\ \mathrm{Leb}(S) = c_0 v_d/2^d}} \int_S \Big(\sum_{|s| \le \mathfrak b(\beta)} W_s u^s\Big)^2 du,$$
--
--   $$C_0 = \frac{3p\lambda_0^2}{4(1+L_1\sqrt d)^2}\min\Big\{\frac{1}{12M_\beta^4\mu_{\max}v_d + 2p\lambda_0M_\beta^2},\ \frac{1}{108M_\beta v_d\mu_{\max} + 6\sqrt{M_\beta}\,p\lambda_0},\ \frac{1}{108M_\beta L^2v_d\mu_{\max} + 6\sqrt{M_\beta}\,L(2v_d\mu_{\max}+p)\lambda_0}\Big\}$$
--
--   (Lemma 7). These two constants drive the epoch schedule of the algorithm.
--
--   **Formalization Note.** Arms are `Bool` (`true` is $+1$); Lean time $t$ is paper time $t+1$. "$\mathfrak b(\beta)$-times continuously differentiable" is $C^{\mathfrak b(\beta)}$ on an open neighbourhood of $\mathcal X$, and the multi-index Taylor sum is written as $\sum_{k \le \mathfrak b(\beta)} \frac1{k!} D^k\eta(x)[x'-x, \dots, x'-x]$, which is the same sum by the multinomial theorem. The density condition is stated on measurable subsets of $\mathcal X$, which is equivalent to a Lebesgue density between $\mu_{\min}$ and $\mu_{\max}$ on $\mathcal X$ vanishing off $\mathcal X$. The page's $\lambda_0$ prints $W \in \mathbb R^d$; $W$ is indexed by the multi-indices, so $W \in \mathbb R^{M_\beta}$. $L > 0$ and $c_0 \le 1$ are made explicit: $C_0$ divides by $L$, and a class with $c_0 > 1$ is empty. Rewards lie in $[0,1]$ as in §2.1 (§2.6 writes $\mathbb R$).
-- source:
--   Hu, Kallus & Mao, Smooth Contextual Bandits, arXiv:1909.02553v4, pp. 7–12 and 25: §1.2 (b(β), M_β, notation), §2.1 (1)–(2), Definitions 1–2, Assumptions 1–4, §2.6 (the class 𝒫), Lemma 1 (p), Lemma 7 (λ₀, C₀)

import Mathlib

noncomputable section

namespace SmoothBandit.Regret

open MeasureTheory ProbabilityTheory

/-- The context space `ℝ^d`, with the Euclidean norm. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The two arms: `true` is arm `+1`, `false` is arm `-1`. -/
abbrev Arm := Bool

/-- The sign `a ∈ {+1, -1}` of an arm. -/
def armSign : Arm → ℝ
  | true => 1
  | false => -1

/-- The unit cube `[0,1]^d`. -/
def cube (d : ℕ) : Set (E d) := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The parameters `(β, L, L1, c0, r0, µmin, µmax, γ, α)` of the class `𝒫` (§2.6). -/
structure Params where
  β : ℝ
  L : ℝ
  L1 : ℝ
  c0 : ℝ
  r0 : ℝ
  muMin : ℝ
  muMax : ℝ
  γ : ℝ
  α : ℝ

/-- The standing parameter range: `β ≥ 1` (Assumption 1), `L, L1 > 0`, `0 < c0 ≤ 1`, `r0 > 0`,
`0 < µmin ≤ µmax` (Assumption 3), `γ > 0`, `α ≥ 0` (Assumption 4). -/
def Params.Standing (P : Params) : Prop :=
  1 ≤ P.β ∧ 0 < P.L ∧ 0 < P.L1 ∧ 0 < P.c0 ∧ P.c0 ≤ 1 ∧ 0 < P.r0 ∧
  0 < P.muMin ∧ P.muMin ≤ P.muMax ∧ 0 < P.γ ∧ 0 ≤ P.α

/-- `b(β)`, the largest integer strictly smaller than `β` (for `β > 0`). -/
def bOf (β : ℝ) : ℕ := ⌈β⌉₊ - 1

/-- The multi-indices `r ∈ ℤ^d_+` with `|r| = r_1 + ⋯ + r_d ≤ l`. -/
def multiIdx (d l : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (l + 1)).filter (fun r => ∑ i, r i ≤ l)

/-- `M_β`, the number of multi-indices `r` with `|r| ≤ b(β)`. -/
def Mbeta (d : ℕ) (β : ℝ) : ℕ := (multiIdx d (bOf β)).card

/-- The monomial `u^r = u_1^{r_1} ⋯ u_d^{r_d}`. -/
def mono {d : ℕ} (r : Fin d → ℕ) (u : E d) : ℝ := ∏ i, u i ^ r i

/-- Definition 1: `η` is `(β, L, 𝒳)`-Hölder. It maps `𝒳` into `[0,1]`, is `b(β)`-times continuously
differentiable (on an open neighbourhood of `𝒳`), and its Taylor polynomial of order `b(β)` at any
`x ∈ 𝒳` approximates it at any `x' ∈ 𝒳` within `L‖x' - x‖^β`. The multi-index sum
`∑_{|r| ≤ b(β)} (x'-x)^r / r! · D^r η(x)` is written as `∑_{k ≤ b(β)} D^k η(x)[x'-x, …, x'-x] / k!`. -/
def IsHolder {d : ℕ} (β L : ℝ) (𝒳 : Set (E d)) (η : E d → ℝ) : Prop :=
  (∀ x ∈ 𝒳, η x ∈ Set.Icc (0 : ℝ) 1) ∧
  (∃ U : Set (E d), IsOpen U ∧ 𝒳 ⊆ U ∧ ContDiffOn ℝ (bOf β) η U) ∧
  ∀ x ∈ 𝒳, ∀ x' ∈ 𝒳,
    |η x' - ∑ k ∈ Finset.range (bOf β + 1),
        ((k.factorial : ℝ))⁻¹ * iteratedFDeriv ℝ k η x (fun _ => x' - x)| ≤ L * ‖x' - x‖ ^ β

/-- The volume inequality used by Definition 2, also evaluated at grid centres outside `S` in (6). -/
def RegularVolumeAt {d : ℕ} (c r : ℝ) (S : Set (E d)) (x : E d) : Prop :=
  ENNReal.ofReal c * volume (Metric.closedBall x r) ≤ volume (S ∩ Metric.closedBall x r)

/-- Definition 2: `S` is weakly `(c, r)`-regular at a point `x ∈ S`. -/
def WeaklyRegularAt {d : ℕ} (c r : ℝ) (S : Set (E d)) (x : E d) : Prop :=
  NullMeasurableSet S volume ∧ x ∈ S ∧ RegularVolumeAt c r S x

/-- Definition 2: `S` is strongly `(c0, r0)`-regular at `x`: weakly `(c0, r)`-regular for all
`0 ≤ r ≤ r0`. -/
def StronglyRegularAt {d : ℕ} (c0 r0 : ℝ) (S : Set (E d)) (x : E d) : Prop :=
  NullMeasurableSet S volume ∧ x ∈ S ∧
    ∀ r : ℝ, 0 ≤ r → r ≤ r0 → RegularVolumeAt c0 r S x

/-- Definition 2: a Lebesgue-measurable `S` is a `(c0, r0)`-regular set if it is strongly
`(c0, r0)`-regular at every one of its points. -/
def IsRegularSet {d : ℕ} (c0 r0 : ℝ) (S : Set (E d)) : Prop :=
  NullMeasurableSet S volume ∧ ∀ x ∈ S, StronglyRegularAt c0 r0 S x

/-- One instance of the smooth contextual bandit, on one probability space `Ω`: the covariate
support `𝒳`, the contexts `X t`, the potential rewards `Y t ω a` of both arms, the fair coins used
for "pull ±1 randomly, equiprobably", and the conditional mean rewards `η a`.
Lean time `t` is paper time `t + 1`. -/
structure Machine (d : ℕ) (Ω : Type) [MeasurableSpace Ω] where
  P : Measure Ω
  𝒳 : Set (E d)
  X : ℕ → Ω → E d
  Y : ℕ → Ω → Arm → ℝ
  coin : ℕ → Ω → Bool
  η : Arm → E d → ℝ

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- §2.1: `(X_t, Y_t(1), Y_t(-1), coin_t)` are i.i.d. over `t`; the coin is fair and independent of
`(X_t, Y_t(±1))`; rewards lie in `[0, 1]`; and `η_a(x) = E[Y(a) | X = x]`, written as the integral
identity on every measurable event `{X_t ∈ A}` with `η_a(X_t)` integrable. -/
def IsMachine (M : Machine d Ω) : Prop :=
  IsProbabilityMeasure M.P ∧
  (∀ t, Measurable (M.X t)) ∧
  (∀ t a, Measurable (fun ω => M.Y t ω a)) ∧
  (∀ t, Measurable (M.coin t)) ∧
  (∀ a, Measurable (M.η a)) ∧
  iIndepFun (fun t ω => (M.X t ω, M.Y t ω true, M.Y t ω false, M.coin t ω)) M.P ∧
  (∀ t, M.P.map (fun ω => (M.X t ω, M.Y t ω true, M.Y t ω false, M.coin t ω)) =
      M.P.map (fun ω => (M.X 0 ω, M.Y 0 ω true, M.Y 0 ω false, M.coin 0 ω))) ∧
  (∀ t, IndepFun (fun ω => (M.X t ω, M.Y t ω true, M.Y t ω false)) (M.coin t) M.P) ∧
  (∀ t, M.P {ω | M.coin t ω = true} = 1 / 2) ∧
  (∀ t ω a, M.Y t ω a ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ t a, Integrable (fun ω => M.η a (M.X t ω)) M.P) ∧
  (∀ t a (A : Set (E d)), MeasurableSet A →
    ∫ ω in M.X t ⁻¹' A, M.Y t ω a ∂M.P = ∫ ω in M.X t ⁻¹' A, M.η a (M.X t ω) ∂M.P)

/-- The conditional average treatment effect `τ(x) = η_1(x) - η_{-1}(x)`. -/
def tau (M : Machine d Ω) (x : E d) : ℝ := M.η true x - M.η false x

/-- The optimal decision region `Q_a = {x ∈ 𝒳 : a τ(x) ≥ 0}`. -/
def Q (M : Machine d Ω) (a : Arm) : Set (E d) := {x | x ∈ M.𝒳 ∧ 0 ≤ armSign a * tau M x}

/-- The oracle policy (1): `π*(x) = +1` if `τ(x) ≥ 0`, and `-1` otherwise. -/
def piStar (M : Machine d Ω) (x : E d) : Arm := decide (0 ≤ tau M x)

/-- Assumption 1: for `a = ±1`, `η_a` is `(β, L, 𝒳)`-Hölder and `(1, L1, 𝒳)`-Hölder. -/
def Assumption1 (P : Params) (M : Machine d Ω) : Prop :=
  ∀ a, IsHolder P.β P.L M.𝒳 (M.η a) ∧ IsHolder 1 P.L1 M.𝒳 (M.η a)

/-- Assumption 2: for `a = ±1`, `Q_a` is a non-empty `(c0, r0)`-regular set. -/
def Assumption2 (P : Params) (M : Machine d Ω) : Prop :=
  ∀ a, (Q M a).Nonempty ∧ IsRegularSet P.c0 P.r0 (Q M a)

/-- The support part of Assumption 3: `𝒳` is compact, `𝒳 ⊆ [0,1]^d`, and `X` lies in `𝒳` almost
surely. -/
def SupportCond (M : Machine d Ω) : Prop :=
  IsCompact M.𝒳 ∧ M.𝒳 ⊆ cube d ∧ M.P (M.X 0 ⁻¹' M.𝒳) = 1

/-- The density part of Assumption 3: the law of `X` has a Lebesgue density between `µmin` and
`µmax` on `𝒳`, stated on measurable subsets of `𝒳`. -/
def DensityCond (M : Machine d Ω) (muMin muMax : ℝ) : Prop :=
  ∀ A : Set (E d), MeasurableSet A → A ⊆ M.𝒳 →
    ENNReal.ofReal muMin * volume A ≤ M.P (M.X 0 ⁻¹' A) ∧
    M.P (M.X 0 ⁻¹' A) ≤ ENNReal.ofReal muMax * volume A

/-- Assumption 3 (strong density, compact support in `[0,1]^d`). -/
def Assumption3 (P : Params) (M : Machine d Ω) : Prop :=
  SupportCond M ∧ DensityCond M P.muMin P.muMax

/-- Assumption 4 (margin condition): `P(0 < |τ(X)| ≤ t) ≤ γ t^α` for all `t > 0`. -/
def Assumption4 (P : Params) (M : Machine d Ω) : Prop :=
  ∀ t : ℝ, 0 < t →
    (M.P {ω | 0 < |tau M (M.X 0 ω)| ∧ |tau M (M.X 0 ω)| ≤ t}).toReal ≤ P.γ * t ^ P.α

/-- The class `𝒫(β, L1, L, c0, r0, µmin, µmax, γ, α)` of §2.6: Assumptions 1 to 4. -/
def InClass (P : Params) (M : Machine d Ω) : Prop :=
  IsMachine M ∧ Assumption1 P M ∧ Assumption2 P M ∧ Assumption3 P M ∧ Assumption4 P M

/-- `v_d`, the Lebesgue volume of the closed unit ball of `ℝ^d`. -/
def vd (d : ℕ) : ℝ := (volume (Metric.closedBall (0 : E d) 1)).toReal

/-- Lemma 1's constant `p = µmin c0 r0^d v_d`. -/
def pConst (P : Params) (d : ℕ) : ℝ := P.muMin * P.c0 * P.r0 ^ d * vd d

/-- The polynomial `u ↦ ∑_{|s| ≤ l} W_s u^s` with coefficient vector `W ∈ ℝ^{M}`. -/
def polyVal {d l : ℕ} (W : EuclideanSpace ℝ (multiIdx d l)) (u : E d) : ℝ :=
  ∑ s : multiIdx d l, W s * mono s.1 u

/-- Lemma 7's `λ0 = (1/4) µmin inf ∫_S (∑_{|s| ≤ b(β)} W_s u^s)^2 du`, the infimum over unit vectors
`W ∈ ℝ^{M_β}` and compact `S ⊆ B(0,1)` with `Leb(S) = c0 v_d / 2^d`. -/
def lam0 (P : Params) (d : ℕ) : ℝ :=
  (1 / 4) * P.muMin *
    sInf {v : ℝ | ∃ (W : EuclideanSpace ℝ (multiIdx d (bOf P.β))) (S : Set (E d)),
      ‖W‖ = 1 ∧ IsCompact S ∧ S ⊆ Metric.closedBall 0 1 ∧
      volume S = ENNReal.ofReal (P.c0 * vd d / 2 ^ d) ∧
      v = ∫ u in S, (polyVal W u) ^ 2}

/-- Lemma 7's constant `C0`. -/
def C0 (P : Params) (d : ℕ) : ℝ :=
  let p := pConst P d
  let l := lam0 P d
  let M : ℝ := Mbeta d P.β
  let v := vd d
  3 * p * l ^ 2 / (4 * (1 + P.L1 * Real.sqrt d) ^ 2) *
    min (1 / (12 * M ^ 4 * P.muMax * v + 2 * p * l * M ^ 2))
      (min (1 / (108 * M * v * P.muMax + 6 * Real.sqrt M * p * l))
        (1 / (108 * M * P.L ^ 2 * v * P.muMax + 6 * Real.sqrt M * P.L * (2 * v * P.muMax + p) * l)))

end SmoothBandit.Regret


