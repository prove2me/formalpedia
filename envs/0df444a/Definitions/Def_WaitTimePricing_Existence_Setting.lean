-- Prove2me | Definitions.Def_WaitTimePricing_Existence_Setting
-- name    : WaitTimePricing_Existence_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:10.566549+00:00
-- url     : https://prove2.me/theorems/5ddbf3ad-b241-494c-be85-9ddaa1230934
-- title:
--   §3 — wait-time pricing model: Assumption 1, service time $\mathtt t(p)$, thresholds $\hat w, L(w), \bar w, \Gamma(w)$, objectives and the DDEs (12)–(15)
-- statement:
--   This file fixes the model of a single-server queue in which the firm announces to each arriving customer the current wait time $w$ and a price rate $p$, and the customer chooses whether to join and how long to be served.
--
--   **Primitives.** A model consists of a usage utility $U:\mathbb R\to\mathbb R$, a waiting cost $c:\mathbb R\to\mathbb R$, a Poisson arrival rate $\lambda$ and a maximum service time $C$. The **standing assumptions** are $\lambda>0$, $C>0$, $U$ three times and $c$ twice continuously differentiable, and Assumption 1:
--
--   1. $U(t)\ge 0$, $U(0)=0$, $0\le U'(t)\le U'(0)<\infty$ and $U''(t)<0$ for all $t\in[0,C]$;
--   2. $\frac{d^2}{dt^2}\,[U'(t)\,t]<0$ for all $t\in[0,C]$;
--   3. $c(0)=0$, $c'(w)>0$ and $c''(w)\ge 0$ for all $w\ge 0$.
--
--   **Customer's choice.** For a price $p\in[0,U'(0)]$ the chosen service time (5) is
--   $$\mathtt t(p)=\min\{(U')^{-1}(p),\,C\},$$
--   encoded as $\mathtt t(p)=\sup\{t\in[0,C] : p\le U'(t)\}$, and the realized service time (6) is $\mathtt t(p,w)=\mathtt t(p)\cdot\mathbb 1\{U(\mathtt t(p))-p\,\mathtt t(p)-c(w)\ge 0\}$.
--
--   **Thresholds.** $\hat w=\sup\{w>0 : U(C)-U'(C)C-c(w)=0\}$ (Proposition 1(i)); $L(w)=\inf\{t\in[0,C] : U(t)-U'(t)t-c(w)\ge 0\}$ (Proposition 1(ii)); $\bar w=\sup\{w>0 : U(C)=c(w)\}$ (Proposition 2(i)); and the joining price bound
--   $$\Gamma(w)=\sup\{p\in[0,U'(0)] : U(\mathtt t(p))-p\,\mathtt t(p)-c(w)\ge 0\}$$
--   (Proposition 2(ii)). Each is defined by its characterizing set; Propositions 1 and 2 state that these sets have the claimed structure.
--
--   **Objectives (Lemma 1).** For revenue, $\mathbf v(p)=p\,\mathtt t(p)$ and $\alpha=0$; for social welfare, $\mathbf v(p)=U(\mathtt t(p))$ and $\alpha=1$.
--
--   **Optimality equations.** For a function $V$ and a wait time $w$ write
--   $$I_V(w)=\max_{p\in[0,\Gamma(w)]}\big[\mathbf v(p)-\alpha c(w)+V(w+\mathtt t(p))-V(w)\big].$$
--   A constant $g$ and a function $V$ solve the delay differential equations (12)–(15) if
--   $$g=-V'(w)+\lambda\max\{I_V(w),0\}\ \ (0<w\le\bar w),\qquad g=\lambda\max\{I_V(0),0\},\qquad g=-V'(w)\ \ (w>\bar w),\qquad V(\bar w)=0.$$
--   Since $c(0)=0$, $I_V(0)=\max_{p\in[0,\Gamma(0)]}[\mathbf v(p)+V(\mathtt t(p))-V(0)]$ is exactly the inner maximum of (13).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $U$ and $c$ are defined on all of $\mathbb R$ and assumed $C^3$ resp. $C^2$ there (any $C^3$ function on $[0,C]$ extends), so $U'$ is the two-sided derivative also at $0$ and $C$; Assumption 1's inequalities are imposed exactly on $[0,C]$ and $[0,\infty)$. $\lambda>0$ and $C>0$ are used but not stated in the paper. $\mathtt t(p)$ is meaningful only for $p\in[0,U'(0)]$ and $\Gamma(w)$ only for $w\in[0,\bar w]$. The "max" $I_V(w)$ is the real supremum of the image of $[0,\Gamma(w)]$. In (12) and (14), $V'(w)$ is encoded by the assertion that $V$ has the prescribed derivative at $w$ (so differentiability is part of the claim), never by a default-valued derivative operator.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 7 Assumption 1; p. 8 (5), (6), Proposition 1; p. 9 Proposition 2; p. 10 Lemma 1; pp. 12–13 (12)–(15)

import Mathlib

/-!
# Wait-time based pricing: the model and the optimality equations

Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times,
SSRN 3709573 (version of October 12, 2020), pp. 6–13: Assumption 1 (p. 7), (1), (5), (6)
(pp. 7–8), Propositions 1–2 (pp. 8–9, thresholds ŵ, L(w), w̄, Γ(w)), Lemma 1 (p. 10, v and α),
and the optimality equations (12)–(15) (pp. 12–13).
-/

namespace WaitTimePricing.Existence

noncomputable section

open Set

/-- The primitives of the model (pp. 6–7): the usage utility `U(t)` of a service time `t`,
the waiting cost `c(w)` of a wait time `w`, the Poisson arrival rate `λ` (`lam`) and the maximum
service time `C`. -/
structure Model where
  /-- usage utility `U(t)` -/
  U : ℝ → ℝ
  /-- waiting cost `c(w)` -/
  c : ℝ → ℝ
  /-- Poisson arrival rate `λ` -/
  lam : ℝ
  /-- maximum service time `C` -/
  C : ℝ

/-- Standing assumptions (Lin–Shang–Sun, SSRN 3709573, p. 7, Assumption 1, and the sentence before
it: "U(t) is three times differentiable, and the wait time cost function c(w) twice
differentiable"):

* (i) `U(t) ≥ 0`, `U(0) = 0`, `0 ≤ U′(t) ≤ U′(0) < ∞` and `U″(t) < 0` for all `t ∈ [0, C]`;
* (ii) `d²/dt² [U′(t) t] < 0` for all `t ∈ [0, C]`;
* (iii) `c(0) = 0`, `c′(w) > 0` and `c″(w) ≥ 0` for all `w ≥ 0`.

**Formalization Note.** `U` and `c` are functions on all of `ℝ`, assumed `C³` resp. `C²` on `ℝ`
(a disclosed strengthening of "three / two times differentiable": a `C³` function on `[0, C]`
extends to `ℝ`, and this makes `U′ = deriv U` an honest two-sided derivative at `0` and `C`).
The inequalities of Assumption 1 are imposed exactly on `[0, C]` resp. `[0, ∞)`. The paper
uses `λ > 0` and `C > 0` without stating them; they are added here. -/
structure Model.Standing (M : Model) : Prop where
  lam_pos : 0 < M.lam
  C_pos : 0 < M.C
  U_contDiff : ContDiff ℝ 3 M.U
  c_contDiff : ContDiff ℝ 2 M.c
  /-- Assumption 1(i): `U(t) ≥ 0` on `[0, C]` -/
  U_nonneg : ∀ t ∈ Icc 0 M.C, 0 ≤ M.U t
  /-- Assumption 1(i): `U(0) = 0` -/
  U_zero : M.U 0 = 0
  /-- Assumption 1(i): `0 ≤ U′(t)` on `[0, C]` -/
  deriv_U_nonneg : ∀ t ∈ Icc 0 M.C, 0 ≤ deriv M.U t
  /-- Assumption 1(i): `U′(t) ≤ U′(0)` on `[0, C]` -/
  deriv_U_le : ∀ t ∈ Icc 0 M.C, deriv M.U t ≤ deriv M.U 0
  /-- Assumption 1(i): `U″(t) < 0` on `[0, C]` -/
  deriv2_U_neg : ∀ t ∈ Icc 0 M.C, deriv (deriv M.U) t < 0
  /-- Assumption 1(ii): `d²/dt² [U′(t) t] < 0` on `[0, C]` -/
  deriv2_revenue_neg : ∀ t ∈ Icc 0 M.C, deriv (deriv (fun s => deriv M.U s * s)) t < 0
  /-- Assumption 1(iii): `c(0) = 0` -/
  c_zero : M.c 0 = 0
  /-- Assumption 1(iii): `c′(w) > 0` for `w ≥ 0` -/
  deriv_c_pos : ∀ w, 0 ≤ w → 0 < deriv M.c w
  /-- Assumption 1(iii): `c″(w) ≥ 0` for `w ≥ 0` -/
  deriv2_c_nonneg : ∀ w, 0 ≤ w → 0 ≤ deriv (deriv M.c) w

/-- The service-time function (5), p. 8: `t(p) := min{(U′)⁻¹(p), C}` for `p ∈ [0, U′(0)]`.

**Formalization Note.** Encoded by its characterizing set as
`t(p) = sup {t ∈ [0, C] | p ≤ U′(t)}`. Under Assumption 1, `U′` is strictly decreasing on
`[0, C]`, so this set is `[0, min((U′)⁻¹(p), C)]` for `p ∈ [U′(C), U′(0)]` and all of `[0, C]`
for `p < U′(C)`. The value is meaningful only for `p ∈ [0, U′(0)]`; every statement of the
mission quantifies `p` there. -/
def tOf (M : Model) (p : ℝ) : ℝ :=
  sSup {t ∈ Icc 0 M.C | p ≤ deriv M.U t}

/-- The chosen service time (6), p. 8: `t(p, w) := t(p) · 1{U(t(p)) − p·t(p) − c(w) ≥ 0}`. -/
def tJoin (M : Model) (p w : ℝ) : ℝ :=
  if 0 ≤ M.U (tOf M p) - p * tOf M p - M.c w then tOf M p else 0

/-- The threshold `ŵ` of Proposition 1(i), p. 8: the positive solution of
`U(C) − U′(C)C − c(ŵ) = 0` (3).

**Formalization Note.** Defined by its characterizing set, `ŵ := sup {w > 0 | U(C) − U′(C)C −
c(w) = 0}`; Proposition 1(i) asserts that this set is the singleton `{ŵ}`. -/
def what (M : Model) : ℝ :=
  sSup {w ∈ Ioi (0 : ℝ) | M.U M.C - deriv M.U M.C * M.C - M.c w = 0}

/-- The lower bound `L(w)` of Proposition 1(ii), p. 8: the least `t ∈ [0, C]` with
`U(t) − U′(t)t − c(w) ≥ 0`.

**Formalization Note.** Defined as `inf {t ∈ [0, C] | U(t) − U′(t)t − c(w) ≥ 0}`; it is meaningful
for `w ∈ [0, ŵ]`, where Proposition 1(ii) asserts the "if and only if" characterization (4). -/
def Lw (M : Model) (w : ℝ) : ℝ :=
  sInf {t ∈ Icc 0 M.C | 0 ≤ M.U t - deriv M.U t * t - M.c w}

/-- The threshold `w̄` of Proposition 2(i), p. 9: the positive solution of `U(C) = c(w̄)` (7).

**Formalization Note.** Defined by its characterizing set, `w̄ := sup {w > 0 | U(C) = c(w)}`;
Proposition 2(i) asserts that this set is the singleton `{w̄}`. -/
def wbar (M : Model) : ℝ :=
  sSup {w ∈ Ioi (0 : ℝ) | M.U M.C = M.c w}

/-- The joining price bound `Γ(w)` of Proposition 2(ii), p. 9: the largest price
`p ∈ [0, U′(0)]` at which a customer facing wait time `w` still joins,
`U(t(p)) − p·t(p) − c(w) ≥ 0` (8).

**Formalization Note.** Defined as `sup {p ∈ [0, U′(0)] | U(t(p)) − p·t(p) − c(w) ≥ 0}`, not by a
closed form; it is meaningful for `w ∈ [0, w̄]`, where Proposition 2(ii) asserts (8). -/
def Gamma (M : Model) (w : ℝ) : ℝ :=
  sSup {p ∈ Icc 0 (deriv M.U 0) | 0 ≤ M.U (tOf M p) - p * tOf M p - M.c w}

/-- The two objectives of Lemma 1, p. 10: long-run average revenue or social welfare. -/
inductive Objective
  | revenue
  | welfare

/-- The per-customer value `v(p)` of Lemma 1, p. 10: `v(p) = p·t(p)` (revenue, Lemma 1(i)) or
`v(p) = U(t(p))` (social welfare, Lemma 1(ii)). -/
def v (M : Model) : Objective → ℝ → ℝ
  | .revenue, p => p * tOf M p
  | .welfare, p => M.U (tOf M p)

/-- The waiting-cost weight `α` of Lemma 1, p. 10: `α = 0` (revenue) or `α = 1` (welfare). -/
def alpha : Objective → ℝ
  | .revenue => 0
  | .welfare => 1

/-- The inner maximum of the optimality equations (12)–(13), p. 12, and of Algorithm 1
(19), (22), p. 14, for a candidate relative value function `V` at wait time `w`:
`max_{p ∈ [0, Γ(w)]} [v(p) − α c(w) + V(w + t(p)) − V(w)]`.

**Formalization Note.** The "max" is the real `sSup` of the image of `[0, Γ(w)]`. This set is
nonempty (`Γ(w) ≥ 0` for `w ∈ [0, w̄]`, Proposition 2) and, for the functions `V` to which it is
applied (Algorithm 1's piecewise-linear `V^g_N` and the Lipschitz limit `V^ḡ`), bounded and
attained. At `w = 0` the term `α c(0)` vanishes because `c(0) = 0` (Assumption 1(iii)), so
`innerMax M obj V 0` is the inner maximum of (13) and (22). -/
def innerMax (M : Model) (obj : Objective) (V : ℝ → ℝ) (w : ℝ) : ℝ :=
  sSup ((fun p => v M obj p - alpha obj * M.c w + V (w + tOf M p) - V w) '' Icc 0 (Gamma M w))

/-- The optimality equations (12)–(15), pp. 12–13, for a constant `g` and a relative value
function `V`:

* (12) `g = −V′(w) + λ max{max_{p∈[0,Γ(w)]} [v(p) − αc(w) + V(w + t(p)) − V(w)], 0}`,
  for all `w ∈ (0, w̄]`;
* (13) `g = λ max{max_{p∈[0,Γ(0)]} [v(p) + V(t(p)) − V(0)], 0}`;
* (14) `g = −V′(w)` for all `w > w̄`;
* (15) `V(w̄) = 0`.

**Formalization Note.** `V′(w)` is encoded by `HasDerivAt V d w` with `d` the value the equation
prescribes (so (12) and (14) assert differentiability of `V` at `w`), never by `deriv`. The inner
maxima are `innerMax` (a real `sSup`, see there); in (13) the term `α c(0)` of `innerMax` is zero
since `c(0) = 0`. -/
def SolvesDDE (M : Model) (obj : Objective) (g : ℝ) (V : ℝ → ℝ) : Prop :=
  (∀ w ∈ Ioc 0 (wbar M), HasDerivAt V (M.lam * max (innerMax M obj V w) 0 - g) w) ∧
  g = M.lam * max (innerMax M obj V 0) 0 ∧
  (∀ w, wbar M < w → HasDerivAt V (-g) w) ∧
  V (wbar M) = 0

end

end WaitTimePricing.Existence


