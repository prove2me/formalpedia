-- Prove2me | Definitions.Def_SingCtrlLevy_Barrier_Model
-- name    : SingCtrlLevy_Barrier_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:36.917618+00:00
-- url     : https://prove2.me/theorems/7813a102-f620-433c-9832-fe272b7e26c3
-- title:
--   §§2–5, (2.2)–(2.5), (3.6)–(3.9), (4.35), pp. 3–21 — admissible singular controls, cost v_π, value v, barrier strategy, v_b, ρ, b*, τ⁻_b, f^(ε), X^[ε]
-- statement:
--   This file defines the singular control problem of Noba and Yamazaki and the objects its solution is built from. Throughout, $X=(X_t)_{t\ge0}$ is a real process on $(\Omega,\mathcal F,\mathbb P)$ with $X_0=0$, $x\in\mathbb R$ is the starting point (under $\mathbb P_x$ the process is $x+X$), $q>0$ is the discount rate, $C\in\mathbb R$ the unit cost of controlling, and $f:\mathbb R\to\mathbb R$ the running cost.
--
--   1. **Strategies.** A strategy is a process $R=(R_t)_{t\ge0}$ that is nondecreasing, right-continuous, adapted to the natural filtration $\mathcal F_t=\sigma(X_s:s\le t)$ of $X$, and starts at $R_{0-}=0$; so $R_0\ge0$ and an initial jump is allowed. The controlled process is
--   $$U_t=x+X_t+R_t\qquad(2.2).$$
--   2. **Cost measure.** $dR_t$ is the Lebesgue–Stieltjes measure of the path extended by $R_t=0$ for $t<0$; it charges $\{0\}$ with the initial jump $R_0$.
--   3. **Admissibility from $x$** (2.4): $R$ is a strategy and $\mathbb E_x\big[\int_0^\infty e^{-qt}|f(U_t)|\,dt+\int_{[0,\infty)}e^{-qt}\,dR_t\big]<\infty$.
--   4. **Cost and value.**
--   $$v_\pi(x)=\mathbb E_x\Big[\int_0^\infty e^{-qt}f(U_t)\,dt+C\int_{[0,\infty)}e^{-qt}\,dR_t\Big]\quad(2.3),\qquad v(x)=\inf_{\pi\in\mathcal A}v_\pi(x).$$
--   5. **Barrier strategy at $b$** from $x$: $R^b_t=-\inf_{s\in[0,t]}\{(x+X_s-b)\wedge0\}$, so $U^b=x+X+R^b$ is $X$ reflected at the lower barrier $b$ and $R^b_0=(b-x)^+$. Its costs are $v^{(1)}_b(x)=\mathbb E_x[\int_0^\infty e^{-qt}f(U^b_t)dt]$, $v^{(2)}_b(x)=\mathbb E_x[\int_{[0,\infty)}e^{-qt}dR^b_t]$ and $v_b=v^{(1)}_b+Cv^{(2)}_b$ (3.6).
--   6. **The barrier level.** With $f'_+$, $f'_-$ the right and left derivatives,
--   $$\rho(b)=\mathbb E\Big[\int_0^\infty e^{-qt}f'_+(U^0_t+b)\,dt\Big]\ (3.9),\qquad b^*=\inf\{b\in\mathbb R:\rho(b)+C\ge0\}\ (3.8),$$
--   where $U^0$ is $X$ reflected at $0$ started at $0$. The same construction with any function $g$ in place of $f'_+$ gives $\rho_g$ and $b^*_g$.
--   7. **First down-crossing time** (2.5): $\tau^-_b=\inf\{t>0:x+X_t<b\}\in[0,\infty]$, and $e^{-q\tau}$ is read as $0$ when $\tau=\infty$.
--   8. **Assumption 1.** (i) $f$ is convex; (ii) $|f(x)|\le k_1+k_2|x|^N$ for some $k_1,k_2$, $N\in\mathbb N$; (iii) $f'_+(-\infty)<-Cq<f'_+(\infty)$.
--   9. **Smoothing** (4.35): for $\varepsilon>0$, $f^{(\varepsilon)\prime}(x)=\varepsilon^{-2}\int_{-\varepsilon}^0dz\int_{-\varepsilon}^0f'_+(x+y+z)\,dy$ and $f^{(\varepsilon)}(x)=f(b)+\int_b^xf^{(\varepsilon)\prime}(y)\,dy$ (the paper anchors at $b=b^*$).
--   10. **Shifted process** (§5): $X^{[\varepsilon]}_t=X_t+\varepsilon t$.
--
--   The main result of the paper is that the barrier strategy at $b^*$ is optimal over all admissible strategies.
--
--   **Formalization Note** Admissibility is defined per starting point: the barrier strategy depends on $x$ through $R^b_0=(b-x)^+$, so the admissible set is read as the set of strategies chosen for the start $x$ satisfying (2.4) at that $x$. Time integrals are over $[0,\infty)\subset\mathbb R$. The integrability (2.4) is a lower Lebesgue integral in $[0,\infty]$; costs are Bochner integrals, which are genuine integrals exactly under (2.4). $v$ takes values in $\overline{\mathbb R}$ (`EReal`). $f'_\pm$ are one-sided derivatives within $(y,\infty)$ and $(-\infty,y)$. Assumption 1(iii) is written as "$f'_+(y)<-Cq$ for some $y$ and $f'_+(y)>-Cq$ for some $y$", which is equivalent to the limit form because $f'_+$ is nondecreasing. $\tau^-_b$ is valued in $[0,\infty]$. The oriented interval integral $\int_b^x$ covers both branches of the paper's definition of $f^{(\varepsilon)}$.
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, pp. 3–4 §2.1 (2.2)–(2.4) and v; p. 4 Assumption 1 and (2.5); pp. 5–6 §3 R^b, U^b, (3.6), (3.8), (3.9); p. 17 (4.35); p. 19 b*_(ε); p. 21 §5 X^[ε]

import Mathlib

namespace SingCtrlLevy.Barrier

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The natural σ-algebra `F_t = σ(X_s : s ≤ t)` of the process `X`. -/
abbrev naturalSigma (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ (s : ℝ≥0) (_ : s ≤ t), MeasurableSpace.comap (X s) inferInstance

/-- A strategy (p. 3): nondecreasing, right-continuous, adapted to the natural filtration of
`X`, with `R_{0-} = 0` (so `R_0 ≥ 0`; a jump at time `0` is allowed). -/
def IsStrategy (X : ℝ≥0 → Ω → ℝ) (R : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ ω, 0 ≤ R 0 ω) ∧ (∀ ω, Monotone fun t => R t ω) ∧
    (∀ ω (t : ℝ≥0), ContinuousWithinAt (fun s => R s ω) (Set.Ici t) t) ∧
    (∀ t, Measurable[naturalSigma X t] (R t))

/-- The path `t ↦ R_t` extended by `R_t = 0` for `t < 0` (`R_{0-} = 0`). -/
noncomputable def pathExt (R : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  if t < 0 then 0 else R t.toNNReal ω

open Classical in
/-- The Lebesgue–Stieltjes measure `dR_t(ω)` on `ℝ` of the extended path; it carries the atom
`R_0 - R_{0-} = R_0` at `t = 0`. (Zero measure if the extended path is not monotone.) -/
noncomputable def dR (R : ℝ≥0 → Ω → ℝ) (ω : Ω) : Measure ℝ :=
  if h : Monotone (pathExt R ω) then h.stieltjesFunction.measure else 0

/-- The controlled process (2.2) under `P_x`: `U_t = x + X_t + R_t`. -/
def U (X : ℝ≥0 → Ω → ℝ) (x : ℝ) (R : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x + X t ω + R t ω

/-- Admissibility from the start `x` (p. 4): `R` is a strategy and (2.4) holds,
`E_x[∫_0^∞ e^{-qt}|f(U_t)| dt + ∫_{[0,∞)} e^{-qt} dR_t] < ∞`. -/
def IsAdmissible (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (f : ℝ → ℝ) (q x : ℝ)
    (R : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStrategy X R ∧
    ∫⁻ ω, ((∫⁻ t in Set.Ici (0 : ℝ),
        ENNReal.ofReal (Real.exp (-q * t) * |f (U X x R t.toNNReal ω)|))
      + ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-q * t)) ∂(dR R ω)) ∂P < ⊤

/-- The expected cost (2.3):
`v_π(x) = E_x[∫_0^∞ e^{-qt} f(U_t) dt + C ∫_{[0,∞)} e^{-qt} dR_t]`. -/
noncomputable def cost (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (f : ℝ → ℝ) (q C x : ℝ)
    (R : ℝ≥0 → Ω → ℝ) : ℝ :=
  ∫ ω, ((∫ t in Set.Ici (0 : ℝ), Real.exp (-q * t) * f (U X x R t.toNNReal ω))
    + C * ∫ t in Set.Ici (0 : ℝ), Real.exp (-q * t) ∂(dR R ω)) ∂P

/-- The value function `v(x) = inf_{π ∈ A} v_π(x)` (p. 4), in `EReal`. -/
noncomputable def value (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (f : ℝ → ℝ) (q C x : ℝ) : EReal :=
  ⨅ (R : ℝ≥0 → Ω → ℝ) (_ : IsAdmissible P X f q x R), (cost P X f q C x R : EReal)

/-- The barrier strategy at `b` from the start `x` (p. 5):
`R^b_t = -inf_{s ∈ [0,t]} ((x + X_s - b) ∧ 0)`. -/
noncomputable def barrierR (X : ℝ≥0 → Ω → ℝ) (x b : ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => -⨅ s : Set.Icc (0 : ℝ≥0) t, min (x + X s ω - b) 0

/-- `v^{(1)}_b(x) = E_x[∫_0^∞ e^{-qt} f(U^b_t) dt]` (p. 6). -/
noncomputable def vb1 (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (f : ℝ → ℝ) (q x b : ℝ) : ℝ :=
  ∫ ω, (∫ t in Set.Ici (0 : ℝ), Real.exp (-q * t) * f (U X x (barrierR X x b) t.toNNReal ω)) ∂P

/-- `v^{(2)}_b(x) = E_x[∫_{[0,∞)} e^{-qt} dR^b_t]` (p. 6). -/
noncomputable def vb2 (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (q x b : ℝ) : ℝ :=
  ∫ ω, (∫ t in Set.Ici (0 : ℝ), Real.exp (-q * t) ∂(dR (barrierR X x b) ω)) ∂P

/-- `v_b(x) = v^{(1)}_b(x) + C v^{(2)}_b(x)` (3.6). -/
noncomputable def vb (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (f : ℝ → ℝ) (q C x b : ℝ) : ℝ :=
  vb1 P X f q x b + C * vb2 P X q x b

/-- Right-hand derivative `f'_+(y)`. -/
noncomputable def rd (f : ℝ → ℝ) (y : ℝ) : ℝ := derivWithin f (Set.Ioi y) y

/-- Left-hand derivative `f'_-(y)`. -/
noncomputable def ld (f : ℝ → ℝ) (y : ℝ) : ℝ := derivWithin f (Set.Iio y) y

/-- `E[∫_0^∞ e^{-qt} g(U^0_t + b) dt]`, with `U^0` the process reflected at `0` started at `0`;
for `g = f'_+` this is `ρ(b)` of (3.9). -/
noncomputable def rhoOf (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (q : ℝ) (g : ℝ → ℝ) (b : ℝ) : ℝ :=
  ∫ ω, (∫ t in Set.Ici (0 : ℝ),
    Real.exp (-q * t) * g (U X 0 (barrierR X 0 0) t.toNNReal ω + b)) ∂P

/-- `ρ(b) = E_b[∫_0^∞ e^{-qt} f'_+(U^b_t) dt] = E[∫_0^∞ e^{-qt} f'_+(U^0_t + b) dt]` (3.9). -/
noncomputable def rho (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (f : ℝ → ℝ) (q : ℝ) (b : ℝ) : ℝ :=
  rhoOf P X q (rd f) b

/-- `inf {b ∈ ℝ : ρ_g(b) + C ≥ 0}` for the derivative `g`. -/
noncomputable def bstarOf (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (q C : ℝ) (g : ℝ → ℝ) : ℝ :=
  sInf {b : ℝ | 0 ≤ rhoOf P X q g b + C}

/-- `b* = inf {b ∈ ℝ : ρ(b) + C ≥ 0}` (3.8). -/
noncomputable def bstar (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (f : ℝ → ℝ) (q C : ℝ) : ℝ :=
  bstarOf P X q C (rd f)

/-- The first down-crossing time under `P_x` (2.5): `τ⁻_b = inf {t > 0 : x + X_t < b}`,
`= ∞` if the set is empty. -/
noncomputable def tauMinus (X : ℝ≥0 → Ω → ℝ) (x b : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : 0 < t ∧ x + X t ω < b), (t : ℝ≥0∞)

/-- `e^{-qτ}` for `τ ∈ [0, ∞]`, with `e^{-q∞} = 0`. -/
noncomputable def expDisc (q : ℝ) (τ : ℝ≥0∞) : ℝ :=
  if τ = ⊤ then 0 else Real.exp (-q * τ.toReal)

/-- Assumption 1 (p. 4): (i) `f` convex; (ii) `|f(x)| ≤ k₁ + k₂|x|^N`;
(iii) `f'_+(-∞) < -Cq < f'_+(∞)`, written as `∃ y, f'_+(y) < -Cq` and `∃ y, -Cq < f'_+(y)`
(equivalent, `f'_+` being nondecreasing). -/
def Assumption1 (f : ℝ → ℝ) (C q : ℝ) : Prop :=
  ConvexOn ℝ Set.univ f ∧ (∃ k₁ k₂ : ℝ, ∃ N : ℕ, ∀ x, |f x| ≤ k₁ + k₂ * |x| ^ N) ∧
    (∃ y, rd f y < -C * q) ∧ (∃ y, -C * q < rd f y)

/-- `f^{(ε)'}(x) = ε⁻² ∫_{-ε}^0 dz ∫_{-ε}^0 f'_+(x + y + z) dy` (4.35). -/
noncomputable def fEpsDeriv (f : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  1 / ε ^ 2 * ∫ z in (-ε)..0, ∫ y in (-ε)..0, rd f (x + y + z)

/-- `f^{(ε)}(x) = f(b) + ∫_b^x f^{(ε)'}(y) dy` (p. 17, with anchor `b`; the paper takes
`b = b*`; for `x < b` the oriented integral gives `f(b) - ∫_x^b`). -/
noncomputable def fEps (f : ℝ → ℝ) (b ε x : ℝ) : ℝ :=
  f b + ∫ y in b..x, fEpsDeriv f ε y

/-- `X^{[ε]}_t = X_t + εt` (§5, p. 21). -/
def XShift (X : ℝ≥0 → Ω → ℝ) (ε : ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => X t ω + ε * (t : ℝ)

end SingCtrlLevy.Barrier


