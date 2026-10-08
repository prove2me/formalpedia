-- Prove2me | Definitions.Def_TsengCGD_Linear_Basic
-- name    : TsengCGD_Linear_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:48.573522+00:00
-- url     : https://prove2.me/theorems/a8039fde-aae0-4eef-96ec-4983825db78c
-- title:
--   Problem (1), the direction $d_H(x;\mathcal J)$ (6), stationarity, CGD with the Armijo rule, rule (12), block-separability (20), (22), Assumptions 1–2, Q-/R-linear rates
-- statement:
--   These are the objects of Tseng and Yun's coordinate gradient descent (CGD) method, as used in the linear convergence analysis of §5.
--
--   **Problem (1).** Throughout, $\Re^n$ is the space of real vectors with the Euclidean inner product $x^Ty$ and norm $\|\cdot\|$, $\mathcal N=\{1,\dots,n\}$, and for $\mathcal J\subseteq\mathcal N$ the subvector $x_{\mathcal J}$ collects the coordinates in $\mathcal J$. The data are a scalar $c>0$, a proper, convex, lower semicontinuous function $P:\Re^n\to(-\infty,\infty]$ with effective domain $\operatorname{dom}P=\{x\mid P(x)<\infty\}$, and a function $f$ that is continuously differentiable on an open set containing $\operatorname{dom}P$. The objective is
--   $$F_c(x)=f(x)+cP(x).$$
--
--   **The direction (6).** For $x\in\operatorname{dom}P$, a nonempty $\mathcal J\subseteq\mathcal N$ and a symmetric positive definite matrix $H$,
--   $$d_H(x;\mathcal J)=\arg\min_d\Big\{\nabla f(x)^Td+\tfrac12 d^THd+cP(x+d)\ \Big|\ d_j=0\ \forall j\notin\mathcal J\Big\},$$
--   and $d_I(x)=d_I(x;\mathcal N)$ (13) is the full direction with $H=I$. With a parameter $\gamma\in[0,1)$ and a direction $d$ at $x$,
--   $$\Delta=\nabla f(x)^Td+\gamma\, d^THd+cP(x+d)-cP(x)\qquad(10).$$
--
--   **Stationarity (p. 394).** A point $x$ is stationary for $F_c$ if $x\in\operatorname{dom}F_c$ and the one-sided directional derivative $F_c'(x;d)=\lim_{\alpha\downarrow0}(F_c(x+\alpha d)-F_c(x))/\alpha$ is $\ge0$ for every $d$. $\bar X$ denotes the set of stationary points.
--
--   **The CGD method (p. 391).** Start at $x^0\in\operatorname{dom}P$; at iteration $k$ choose a nonempty $\mathcal J^k\subseteq\mathcal N$ and $H^k\succ0_n$, take $d^k=d_{H^k}(x^k;\mathcal J^k)$, choose a stepsize $\alpha^k>0$ and set $x^{k+1}=x^k+\alpha^kd^k$.
--
--   **Armijo rule (9).** With $0<\beta<1$, $0<\sigma<1$, $0\le\gamma<1$ and $\alpha^k_{\rm init}>0$, $\alpha^k$ is the largest element of $\{\alpha^k_{\rm init}\beta^j\}_{j\ge0}$ satisfying
--   $$F_c(x^k+\alpha^kd^k)\le F_c(x^k)+\alpha^k\sigma\Delta^k.$$
--
--   **Restricted Gauss–Seidel rule (12).** There is a subsequence $\mathcal T=\{t_0<t_1<\cdots\}\subseteq\{0,1,\dots\}$ with $t_0=0$ such that for every $k=t_i\in\mathcal T$, with $\tau(k)=t_{i+1}$ the next element of $\mathcal T$, the sets $\mathcal J^k,\dots,\mathcal J^{\tau(k)-1}$ are pairwise disjoint with union $\mathcal N$.
--
--   **Block-separability (20).** $P$ is block-separable with respect to $\mathcal J$ if $P(x)=P_{\mathcal J}(x_{\mathcal J})+P_{\mathcal J^C}(x_{\mathcal J^C})$ for all $x$, with $P_{\mathcal J},P_{\mathcal J^C}$ proper, convex and lower semicontinuous.
--
--   **Lipschitz gradient (22).** $\|\nabla f(y)-\nabla f(z)\|\le L\|y-z\|$ for all $y,z\in\operatorname{dom}P$, with $L\ge0$.
--
--   **Assumption 1 (p. 399).** $\bar\lambda I\succeq H^k\succeq\underline\lambda I$ for all $k$, with $0<\underline\lambda\le\bar\lambda$.
--
--   **Assumption 2 (p. 404).** (a) $\bar X\ne\emptyset$ and for every $\zeta\ge\min_xF_c(x)$ there are $\tau,\epsilon>0$ with
--   $$\operatorname{dist}(x,\bar X)\le\tau\|d_I(x)\|\quad\text{whenever }F_c(x)\le\zeta,\ \|d_I(x)\|\le\epsilon.$$
--   (b) There is $\delta>0$ with $\|x-y\|\ge\delta$ whenever $x,y\in\bar X$ and $F_c(x)\ne F_c(y)$.
--
--   **Rates.** A real sequence $s_i$ converges at least Q-linearly if it converges to some $v$ and eventually $|s_{i+1}-v|\le q|s_i-v|$ for a fixed $q\in[0,1)$; a vector sequence converges at least R-linearly if $\|s_i-\bar x\|\le Cq^i$ for some $\bar x$, $C$ and $q\in[0,1)$. Finally $\|d\|_p=(\sum_j|d_j|^p)^{1/p}$, $\|g_{\mathcal J}\|_q$ is the $q$-norm of the subvector $g_{\mathcal J}$, and $r^k=\sum_{\ell=k}^{\tau(k)-1}\|d^\ell\|$ for $k\in\mathcal T$.
--
--   These definitions are shared by every statement of the mission: Lemmas 4 and 5, Theorem 1(f) and Theorem 2.
--
--   **Formalization Note** $\Re^n$ is `EuclideanSpace ℝ (Fin n)` with 0-based coordinates. The extended-valued $P$ is the pair $(D,P)$: its effective domain $D=\operatorname{dom}P$ and its finite values on $D$; "proper, convex, lsc" is the published `ProxNewton.Inexact.IsProperClosedConvex`. $F_c$ is never evaluated off $D$: every statement carries membership in $D$ explicitly. $d_H(x;\mathcal J)$ is defined by `Classical.epsilon` on the minimizer predicate `IsDir`, which is the paper's unique minimizer when $x\in D$ and $H\succ0$; runs use the predicate. Stationarity is stated in liminf form, which agrees with the paper's limit for convex $P$ and differentiable $f$. The Armijo rule takes the first admissible $j$. Assumption 1 is stated through the quadratic form $z^THz$. $\operatorname{dist}(x,\bar X)$ is `Metric.infDist` (the paper's min presumes attainment), and "for any $\zeta\ge\min F_c$" is "for every real $\zeta$", which is equivalent since the condition is empty below $\inf F_c$. Block-separability is stated with explicit witnesses $P_{\mathcal J}$, $P_{\mathcal J^C}$ on $\Re^n$ that depend only on $x_{\mathcal J}$, resp. $x_{\mathcal J^C}$, each with its own effective domain. $\mathcal T$ is a strictly increasing map $t:\mathbb N\to\mathbb N$ with $t(0)=0$.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), pp. 388–404: (1) p. 388, (6) p. 390, CGD method p. 391, (9)–(10), (12) p. 392, (13) p. 392, stationarity p. 394, (20), (22) p. 397, Assumption 1 p. 399, Assumption 2 p. 404, Q-/R-linear p. 405 and footnote 2 p. 409

import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Linear

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- X̄, the set of stationary points of F_c (p. 404). -/
def statSet (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ) : Set (TsengCGD.Global.Vec n) :=
  {x | TsengCGD.Global.IsStationary f D P c x}

/-- The restricted Gauss–Seidel rule (12): 𝒯 = {t 0 < t 1 < ⋯} with t 0 = 0, τ(t i) = t (i+1),
and 𝒥^{t i}, …, 𝒥^{t(i+1)−1} pairwise disjoint with union 𝒩. -/
def RestrictedGaussSeidel (J : ℕ → Finset (Fin n)) (t : ℕ → ℕ) : Prop :=
  StrictMono t ∧ t 0 = 0 ∧ ∀ i,
    ((Finset.Ico (t i) (t (i + 1)) : Set ℕ).PairwiseDisjoint J) ∧
      (Finset.Ico (t i) (t (i + 1))).biUnion J = Finset.univ

/-- (22): ∇f is L-Lipschitz on dom P, L ≥ 0. -/
def GradLipOn (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (L : ℝ) : Prop :=
  0 ≤ L ∧ ∀ y ∈ D, ∀ z ∈ D, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖

/-- Assumption 2(a) (p. 404). -/
def Assumption2a (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ) : Prop :=
  (statSet f D P c).Nonempty ∧ ∀ ζ : ℝ, ∃ τ > 0, ∃ ε > 0, ∀ x ∈ D,
    TsengCGD.Global.Fc f P c x ≤ ζ → ‖TsengCGD.Global.dI f D P c x‖ ≤ ε →
      Metric.infDist x (statSet f D P c) ≤ τ * ‖TsengCGD.Global.dI f D P c x‖

/-- Assumption 2(b) (p. 404). -/
def Assumption2b (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ) : Prop :=
  ∃ δ > 0, ∀ x ∈ statSet f D P c, ∀ y ∈ statSet f D P c, TsengCGD.Global.Fc f P c x ≠ TsengCGD.Global.Fc f P c y → δ ≤ ‖x - y‖

/-- At least Q-linear convergence of a real sequence ([42, Chap. 9]): it converges to some v and
eventually |s_{i+1} − v| ≤ q|s_i − v| for a q < 1. -/
def QLinear (s : ℕ → ℝ) : Prop :=
  ∃ v, Tendsto s atTop (𝓝 v) ∧ ∃ q, 0 ≤ q ∧ q < 1 ∧ ∀ᶠ i in atTop, |s (i + 1) - v| ≤ q * |s i - v|

/-- At least R-linear convergence of a vector sequence: ‖s_i − x̄‖ ≤ C qⁱ for a limit x̄ and q < 1
(equivalently lim sup ‖s_i − x̄‖^{1/i} < 1, footnote 2 p. 409). -/
def RLinear (s : ℕ → TsengCGD.Global.Vec n) : Prop :=
  ∃ xbar : TsengCGD.Global.Vec n, ∃ C q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ i, ‖s i - xbar‖ ≤ C * q ^ i

/-- ‖d‖_p = (Σ_j |d_j|^p)^{1/p} (p. 390), real p ≥ 1. -/
noncomputable def pNorm (p : ℝ) (d : TsengCGD.Global.Vec n) : ℝ := (∑ j, |d j| ^ p) ^ (1 / p)

/-- ‖g_𝒥‖_q, the q-norm of the subvector indexed by 𝒥. -/
noncomputable def pNormOn (p : ℝ) (J : Finset (Fin n)) (g : TsengCGD.Global.Vec n) : ℝ :=
  (∑ j ∈ J, |g j| ^ p) ^ (1 / p)

/-- r^k = Σ_{ℓ=k}^{τ(k)−1} ‖d^ℓ‖ of Theorem 2(a), for k = t i ∈ 𝒯 and τ(k) = t (i+1). -/
noncomputable def r (t : ℕ → ℕ) (d : ℕ → TsengCGD.Global.Vec n) (i : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.Ico (t i) (t (i + 1)), ‖d ℓ‖

end TsengCGD.Linear


