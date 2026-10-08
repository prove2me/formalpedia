-- Prove2me | Definitions.Def_AntonelliBFSDE_Backward_Equation
-- name    : AntonelliBFSDE_Backward_Equation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:04:51.002331+00:00
-- url     : https://prove2.me/theorems/4817bf97-4872-4748-b783-deac906b20f5
-- title:
--   Hypotheses 1–4, the operator $G$ of (2.1), $L^1(\mu)$ solutions, and the iterated integrals $A^{(n)}$, $A^{(n-)}$
-- statement:
--   Let $A$, $\mu$ and $L^1(\mu)$ be as in the setting, with $|A|_T\le\beta$. The data of the backward equation are a **driver** $g:[0,T]\times\Omega\times\mathbb R\to\mathbb R$, $(s,\omega,u)\mapsto g_s(\omega,u)$, a **terminal value** $Y$ and a constant $k$. The driver is $\mathcal B\otimes\mathcal F\otimes\mathcal B(\mathbb R)/\mathcal B(\mathbb R)$-measurable, and **hypotheses 1–4** of §2 are:
--
--   1. $k>0$ and $|g_s(\omega,u)-g_s(\omega,v)|\le k|u-v|$ for all $u,v\in\mathbb R$, $s\in[0,T]$ and $\omega$ (2.2);
--   2. $g_s(\cdot,u)$ is $\mathcal F_s$-measurable for each $s\in[0,T]$ and $u$;
--   3. $E\big(\int_0^T|g_s(0)|\,|dA_s|\big)<+\infty$;
--   4. $Y\in L^1(P)$ and $Y$ is $\mathcal F_T$-measurable.
--
--   For a process $V$ put $\xi_t=\int_t^T g_s(V_s)\,dA_s+Y$ (integral over $(t,T]$). The operator of (2.1) is
--   $$G(V)_t=E\Big(\int_t^T g_s(V_s)\,dA_s+Y\ \Big|\ \mathcal F_t\Big).$$
--   A process $W$ is a **version of $G(V)$** if every $\xi_t$, $t\le T$, is integrable, $W$ is a jointly measurable version of $t\mapsto E(\xi_t\mid\mathcal F_t)$, and every path of $W$ is càdlàg on $[0,T]$. $V$ **solves (2.1) in the $L^1(\mu)$ sense** if $V\in L^1(\mu)$ and, for a version $G(V)$,
--   $$E\Big(\int_0^T|G(V)_t-V_t|\,|dA_t|\Big)=0.$$
--
--   For the proof of Theorem 2.4 the paper assumes $A$ nondecreasing and introduces, for a nondecreasing right-continuous path $a$ with $a_0=0$, the iterated Lebesgue–Stieltjes integrals
--   $$a^{(0)}=a^{(0-)}=1,\qquad a^{(n+1)}_t=\int_{(0,t]}a^{(n)}_s\,da_s,\qquad a^{((n+1)-)}_t=\int_{(0,t]}a^{(n-)}_{s-}\,da_s,$$
--   so that $a^{(1)}=a^{(1-)}=a$, and the brackets
--   $$(a_u-a_t)^{[n]}=\sum_{i=0}^n(-1)^i a_u^{((n-i)-)}a_t^{(i)},\qquad (a_{u-}-a_t)^{[n]}=\sum_{i=0}^n(-1)^i a_{u-}^{((n-i)-)}a_t^{(i)}.$$
--   Finally $dC$ on $[0,\infty)$ denotes, for a nondecreasing path $C$ with $C_0\ge0$, the Stieltjes measure with the convention $C_{0-}=0$ (an atom of mass $C_0$ at $0$), as in (2.6).
--
--   These are the objects of Theorem 2.4 and of every milestone.
--
--   **Formalization Note** The paper writes "for each $s$ and $u$" and "$\forall s\in[0,T]$"; only $[0,T]$ matters, and the Lipschitz bound is uniform in $\omega$ (the paper's $g_s(u)$ is shorthand for $g(s,\omega,u)$). $G(V)$ is defined only up to versions, so it is not a Lean function: statements quantify over versions. Every version must have an integrable argument $\xi_t$, because Mathlib's conditional expectation of a non-integrable function is $0$. Versions are required to be càdlàg: the paper works with càdlàg processes throughout (it refers to Protter 1990), and two merely jointly measurable versions may differ on the graph of a random time charged by $|dA|$, which has positive $\mu$-measure; two càdlàg versions are indistinguishable. The iterated integrals are Bochner integrals of bounded functions over $(0,t]$ against finite measures; left limits are Mathlib's `Function.leftLim`.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), pp. 778–780, (2.1), hypotheses 1–4, (2.2); p. 780, (2.6) and the notation in the proof of Theorem 2.4

import Mathlib
import Definitions.Def_AntonelliBFSDE_Backward_Setting

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace AntonelliBFSDE.Backward

/-- Hypotheses 1–4 of §2 (Antonelli 1993, pp. 778–779) on the driver `g` and the terminal
value `Y` of the backward equation (2.1), for the integrator `I` on `[0, T]`. -/
structure Hypotheses {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) {T β : ℝ≥0} (I : BVIntegrator 𝓕 T β) (g : ℝ≥0 → Ω → ℝ → ℝ) (Y : Ω → ℝ)
    (k : ℝ) : Prop where
  /-- `g` is `𝓑 × 𝓕 × 𝓑(ℝ) / 𝓑(ℝ)`-measurable. -/
  measurable : Measurable fun p : ℝ≥0 × Ω × ℝ => g p.1 p.2.1 p.2.2
  /-- 1. the Lipschitz constant is positive. -/
  k_pos : 0 < k
  /-- 1., (2.2): `g` is uniformly Lipschitz in `u`, uniformly in `s ∈ [0, T]` and `ω`. -/
  lipschitz : ∀ s ≤ T, ∀ ω u v, |g s ω u - g s ω v| ≤ k * |u - v|
  /-- 2. `g_s(·, u)` is `𝓕_s`-measurable for each `s ∈ [0, T]` and `u`. -/
  adapted : ∀ s ≤ T, ∀ u, Measurable[𝓕 s] fun ω => g s ω u
  /-- 3. `E(∫_0^T |g_s(0)| |dA_s|) < +∞`. -/
  integrable_zero : L1Norm P I (fun s ω => g s ω 0) < ⊤
  /-- 4. `Y ∈ L¹(P)`. -/
  integrable_Y : Integrable Y P
  /-- 4. `Y` is `𝓕_T`-measurable. -/
  measurable_Y : Measurable[𝓕 T] Y

/-- The argument of the conditional expectation in (2.1):
`ξ_t = ∫_t^T g_s(V_s) dA_s + Y`, the integral being over `(t, T]`. -/
noncomputable def xi {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {T β : ℝ≥0} (I : BVIntegrator 𝓕 T β) (g : ℝ≥0 → Ω → ℝ → ℝ) (Y : Ω → ℝ)
    (V : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  I.integral (fun s ω => g s ω (V s ω)) t T ω + Y ω

/-- `W` is a version of `G(V)` of (2.1): every `ξ_t` (`t ≤ T`) is integrable, `W` is a
jointly measurable version of `t ↦ E(ξ_t | 𝓕_t)`, and every path of `W` is càdlàg on `[0, T]`
(the paper works with càdlàg processes throughout, after Protter 1990). Two càdlàg versions are
indistinguishable on `[0, T]`; mere jointly measurable versions could differ on the graph of a
random time charged by `|dA|`, a set of positive `μ`-measure. -/
def IsGVersion {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) {T β : ℝ≥0} (I : BVIntegrator 𝓕 T β) (g : ℝ≥0 → Ω → ℝ → ℝ) (Y : Ω → ℝ)
    (V W : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t ≤ T, Integrable (xi I g Y V t) P) ∧ IsCondExpVersion 𝓕 P T (xi I g Y V) W ∧
    ∀ ω, IsCadlagOn (fun t => W t ω) T

/-- `V` solves (2.1) in the `L¹(μ)` sense: `V ∈ L¹(μ)` and `E(∫_0^T |G(V)_t - V_t| |dA_t|) = 0`
for a càdlàg version `G(V)` (any two càdlàg versions are indistinguishable on `[0, T]`). -/
def IsL1Solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) {T β : ℝ≥0} (I : BVIntegrator 𝓕 T β) (g : ℝ≥0 → Ω → ℝ → ℝ) (Y : Ω → ℝ)
    (V : ℝ≥0 → Ω → ℝ) : Prop :=
  MemL1 P I V ∧ ∃ W : ℝ≥0 → Ω → ℝ, IsGVersion 𝓕 P I g Y V W ∧
    ∫⁻ ω, I.absLIntegral (fun s ω => W s ω - V s ω) 0 T ω ∂P = 0

/-- The Lebesgue–Stieltjes measure `dc` on `[0, ∞)` of a nondecreasing path `c` with the
convention `c_{0-} = 0` (Dellacherie–Meyer; Antonelli 1993, (2.6), p. 780): the Stieltjes measure
of `c` on `(0, ∞)` plus an atom of mass `c_0` at `0`. Every use assumes `c` nondecreasing,
right-continuous and `c_0 ≥ 0`. -/
noncomputable def measureFromZero (c : ℝ≥0 → ℝ) : Measure ℝ :=
  stieltjesMeasureOf c + ENNReal.ofReal (c 0) • Measure.dirac 0

/-- The iterated Stieltjes integrals `a^{(n)}` of a path `a` (proof of Theorem 2.4, p. 780):
`a^{(0)} = 1` and `a^{(n+1)}_t = ∫_{(0,t]} a^{(n)}_s da_s`. -/
noncomputable def iterInt (a : ℝ≥0 → ℝ) : ℕ → ℝ≥0 → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun t => ∫ s in Set.Ioc (0 : ℝ) t, iterInt a n s.toNNReal ∂stieltjesMeasureOf a

/-- The iterated Stieltjes integrals `a^{(n-)}` with left limits (p. 780):
`a^{(0-)} = 1` and `a^{((n+1)-)}_t = ∫_{(0,t]} a^{(n-)}_{s-} da_s`. -/
noncomputable def iterIntMinus (a : ℝ≥0 → ℝ) : ℕ → ℝ≥0 → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun t =>
      ∫ s in Set.Ioc (0 : ℝ) t, Function.leftLim (iterIntMinus a n) s.toNNReal
        ∂stieltjesMeasureOf a

/-- `(a_u - a_t)^{[n]} = ∑_{i=0}^n (-1)^i a_u^{((n-i)-)} a_t^{(i)}` (p. 780). -/
noncomputable def bracket (a : ℝ≥0 → ℝ) (n : ℕ) (u t : ℝ≥0) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * iterIntMinus a (n - i) u * iterInt a i t

/-- `(a_{u-} - a_t)^{[n]} = ∑_{i=0}^n (-1)^i a_{u-}^{((n-i)-)} a_t^{(i)}`, the same formula with
left limits in `u` (p. 780, "the same formula holding also for `u_-`"). -/
noncomputable def bracketLeft (a : ℝ≥0 → ℝ) (n : ℕ) (u t : ℝ≥0) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ i * Function.leftLim (iterIntMinus a (n - i)) u * iterInt a i t

end AntonelliBFSDE.Backward


