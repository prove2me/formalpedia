-- Prove2me | Definitions.Def_SethiChengSS_Finite_Supplement_Capacity
-- name    : SethiChengSS_Finite_Supplement_Capacity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:25:41.17462+00:00
-- url     : https://prove2.me/theorems/90740252-bc9e-4f37-98ed-9e88275d5164
-- title:
--   §5.2 — demand quantile, service bounds, capacity-constrained policies and DP (5.2)
-- statement:
--   Let $D$ be the published finite inventory model. The additional data are a finite real capacity $B$, a real penetration level $C_{\min}$ and a service parameter $\beta$. Write
--   $$\Phi_{i,n}(t)=\int_{[0,t]}\varphi_{i,n}(z)\,dz,\quad Q_{i,n}(q)=\inf\{t\in\mathbb R:q\le\Phi_{i,n}(t)\},\quad A_n^i=C_{\min}+Q_{i,n}(1-\beta).$$
--   Feasibility means $0<\beta<1$ and $A_n^i\le B$ for all $n<N$ and states $i$. At beginning surplus $x\le B$, an order $u$ is feasible exactly when $u\ge0$ and $A_n^i\le x+u\le B$. These are post-order surplus bounds. The service failure probability is the density integral of the event $x+u-\xi_n\le C_{\min}$.
--
--   The constrained DP has terminal value $f_N$ and, at earlier dates,
--   $$z_n(i,y)=c_n^iy+F_{n+1}(v_{n+1})(i,y),\quad h_n(i,x)=\inf_{y\ge x,\ A_n^i\le y\le B}[K_n^i\delta(y-x)+z_n(i,y)],\quad v_n(i,x)=f_n(i,x)-c_n^ix+h_n(i,x).$$
--   The operational value is separately defined by the infimum of the published $J_n$ over every measurable history-dependent policy satisfying the action inequalities almost surely under the published path law. Thus impossible negative-demand histories impose no capacity restriction. The threshold rule uses real thresholds and is extended by zero for $x>B$.
--
--   These definitions provide the common interface for Theorems 5.2 and 5.3. The general model, density data, history type and dynamics are imported; only their capacity/service restriction and derived CDF are added.
--
--   **Formalization Note** The auxiliary real DP is meaningful on the feasible half-line. Its real infima are justified by the nonemptiness and boundedness conclusions of Theorem 5.2. An additional extended-real $h_n$ represents empty action sets by $+\infty$, including $A_n^i>B$; the real auxiliary default is never asserted to be an infeasible problem's value. The quantile is used only for $0<q<1$; its level set is proved nonempty and bounded below in Theorem 5.2, so its real infimum is genuine. The scan's cross-reference to (4.11) for the DP is read as (4.9), as the following theorem explicitly states. No cost, demand, or transition assumption is bundled into the additional data.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 936, Section 5.2, equations (4.9), (4.11), (5.2)

import Mathlib
import Definitions.Def_SethiChengSS_Finite_Model

namespace SethiChengSS.Finite.Supplement

open MeasureTheory Filter Topology
open scoped ENNReal

variable {L : ℕ}

/-- The additional data of §5.2. Capacity and penetration level are arbitrary finite reals. -/
structure ServiceData where
  B : ℝ
  Cmin : ℝ
  β : ℝ

/-- The CDF corresponding to the published density. A singleton endpoint has zero mass. -/
noncomputable def demandCDF (D : Data L) (n : ℕ) (i : Fin L) (t : ℝ) : ℝ :=
  ∫ z in Set.Icc 0 t, D.φ n i z

/-- The paper's generalized inverse, used only at q∈(0,1). -/
noncomputable def demandQuantile (D : Data L) (n : ℕ) (i : Fin L) (q : ℝ) : ℝ :=
  sInf {t : ℝ | q ≤ demandCDF D n i t}

/-- The service bound A^i_n in §5.2. -/
noncomputable def serviceA (D : Data L) (T : ServiceData) (n : ℕ) (i : Fin L) : ℝ :=
  T.Cmin + demandQuantile D n i (1 - T.β)

/-- The explicitly printed feasibility assumption; equality A=B is permitted. -/
def ServiceFeasible (D : Data L) (T : ServiceData) (N : ℕ) : Prop :=
  0 < T.β ∧ T.β < 1 ∧ ∀ n < N, ∀ i, serviceA D T n i ≤ T.B

/-- Feasible order quantities, equivalently max(x,A)≤x+u≤B. -/
def capAction (D : Data L) (T : ServiceData) (n : ℕ) (i : Fin L) (x u : ℝ) : Prop :=
  0 ≤ u ∧ serviceA D T n i ≤ x + u ∧ x + u ≤ T.B

/-- Feasible post-order surplus levels in (5.2). -/
def capLevels (D : Data L) (T : ServiceData) (n : ℕ) (i : Fin L) (x : ℝ) : Set ℝ :=
  {y | x ≤ y ∧ serviceA D T n i ≤ y ∧ y ≤ T.B}

/-- The density-weighted path measure; zero-probability state paths impose no constraint. -/
noncomputable def demandPathLaw (D : Data L) (n : ℕ) {m : ℕ}
    (σ : Fin (m + 1) → Fin L) : Measure (Fin m → ℝ) :=
  volume.withDensity (fun ξ => ENNReal.ofReal (pathWeight D n σ ξ))

/-- Capacity/service feasibility is required almost surely under the actual model law.
In particular no capacity requirement is imposed on impossible negative-demand paths. -/
def CapAdmissible (D : Data L) (T : ServiceData) (N n : ℕ) (i : Fin L)
    (x : ℝ) (U : Policy L) : Prop :=
  Admissible (N - n) U ∧
    ∀ σ : Fin (N - n + 1) → Fin L, σ 0 = i →
      ∀ᵐ ξ ∂demandPathLaw D n σ, ∀ t : Fin (N - n),
        capAction D T (n + t) (σ t.castSucc)
          (surplus U x t (initStates σ t t.2.le) (initDemands ξ t t.2.le))
          (U t (initStates σ t t.2.le) (initDemands ξ t t.2.le))

/-- Infimum of J over all constrained measurable history-dependent policies. -/
noncomputable def capValue (D : Data L) (T : ServiceData) (N n : ℕ)
    (i : Fin L) (x : ℝ) : ℝ≥0∞ :=
  ⨅ U : Policy L, ⨅ (_ : CapAdmissible D T N n i x U), J D N n i x U

/-- The expression minimized over post-order levels in (5.2). -/
noncomputable def capObjective (D : Data L) (n : ℕ) (b : Fin L → ℝ → ℝ)
    (i : Fin L) (x y : ℝ) : ℝ :=
  D.K n i * delta (y - x) + D.c n i * y + F D n b i y

/-- Real recursion on the feasible half-line. Outside that domain the real infimum is
only an auxiliary default: capH below, rather than this default, represents an empty action set. -/
noncomputable def capAux (D : Data L) (T : ServiceData) (N : ℕ) : ℕ → Fin L → ℝ → ℝ
  | 0 => D.f N
  | m + 1 => fun i x => D.f (N - (m + 1)) i x - D.c (N - (m + 1)) i * x +
      sInf (capObjective D (N - (m + 1)) (capAux D T N m) i x ''
        capLevels D T (N - (m + 1)) i x)

/-- The real-valued DP functions on x≤B, assuming ServiceFeasible. -/
noncomputable def capV (D : Data L) (T : ServiceData) (N n : ℕ) : Fin L → ℝ → ℝ :=
  capAux D T N (N - n)

/-- The constrained z of (4.11). -/
noncomputable def capZ (D : Data L) (T : ServiceData) (N n : ℕ) (i : Fin L) (y : ℝ) : ℝ :=
  D.c n i * y + F D n (capV D T N (n + 1)) i y

/-- The extended infimum (5.2); when A>B or x>B its empty range gives +∞. -/
noncomputable def capH (D : Data L) (T : ServiceData) (N n : ℕ) (i : Fin L) (x : ℝ) : EReal :=
  ⨅ y : {y : ℝ // y ∈ capLevels D T n i x},
    ((capObjective D n (capV D T N (n + 1)) i x y : ℝ) : EReal)

/-- The probability of the source event x_{k+1}≤C_min at a post-order level y. -/
noncomputable def serviceFailure (D : Data L) (T : ServiceData) (n : ℕ)
    (i : Fin L) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : ℝ, Set.indicator {z : ℝ | y - z ≤ T.Cmin}
    (fun z => ENNReal.ofReal (D.φ n i z)) z

/-- Real capacity/service thresholds, extended nonnegatively by zero off the half-line. -/
noncomputable def capRule (T : ServiceData) (s S : ℕ → Fin L → ℝ)
    (n : ℕ) (i : Fin L) (x : ℝ) : ℝ :=
  if x ≤ T.B then orderSS (s n i) (S n i) x else 0

end SethiChengSS.Finite.Supplement


