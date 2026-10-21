-- Prove2me | Definitions.Def_NonprofitFunds_Capacity_Model
-- name    : NonprofitFunds_Capacity_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:21.465077+00:00
-- url     : https://prove2.me/theorems/65d71683-6cc5-4513-be8a-fccd6bd6aea5
-- title:
--   §3, pp. 7–12 — two-period nonprofit budget allocation: program, discretionary administration, fundraising, capacity, problems (1) and (2)
-- statement:
--   This file sets up the two-period model of Kotsi, Aflaki, Aydin and Pedraza-Martinez, *Allocation of nonprofit funds among program, fundraising, and administration* (§3), together with the auxiliary objects of §4.2 and Appendix B.
--
--   **Data.** A nonprofit meets $r+1$ dollars of needs per program dollar ($r>0$). It starts period 1 with budget $B_1$, needs $\psi_1$ and capacity $k_1$. Maintaining capacity $k$ costs the required administration $m(k)$; discretionary administration $a$ adds capacity $\delta(a)$ in the next period. Spending $p$ on program, $a$ on discretionary administration and $f$ on fundraising raises the donations
--   $$D(p,a,f)=\phi\Big(\frac{p}{p+a+f}\Big)\,f .$$
--   The second-period needs are a random variable $\Psi\ge 0$ with law $\mu$. The data $(r,B_1,\psi_1,m,\delta,\phi,\mu)$ are fixed; the capacity $k_1$ is a separate argument of every object.
--
--   **Standing assumptions.**
--   1. $r>0$, $B_1>0$, $\psi_1\ge 0$.
--   2. Assumption 1(a): $m$ is convex and nondecreasing on $[0,\infty)$, with $m(0)\ge 0$.
--   3. Assumption 1(b): $\delta(0)=0$, $\delta$ is strictly concave and strictly increasing on $[0,\infty)$, and $\delta'(a)\to\infty$ as $a\downarrow 0$.
--   4. Assumption 2: on $[0,1]$, $\phi$ is strictly concave and nondecreasing, $\phi(0)=1$ and $\phi(x)>1$ for $x\in(0,1]$.
--   5. Regularity: $m,\delta$ are continuous on $[0,\infty)$ and twice continuously differentiable on $(0,\infty)$; $\phi$ is continuous on $[0,1]$ and twice continuously differentiable on $(0,1)$.
--   6. $\mu$ is a probability measure with $\mu((-\infty,0))=0$, absolutely continuous with respect to Lebesgue measure, and $\mu((x,\infty))>0$ for every $x\ge 0$.
--
--   The capacity $k_1$ is **admissible** when $k_1\ge 0$ and $B_1\ge 2m(k_1)$ (p. 10).
--
--   **Objects.** With $\hat B_1=B_1-m(k_1)$ and $\theta=\min(\psi_1,k_1,(r+1)\hat B_1)$:
--   1. the second-period net budget $\hat B_2(p,a,f)=D(p,a,f)-m(k_1+\delta(a))$;
--   2. the second-period value $V_2(B_2,\psi_2,k_2)$, the supremum of $(r+1)p_2$ over $p_2,a_2,f_2\ge 0$ with $p_2+a_2+m(k_2)+f_2\le B_2$ and $(r+1)p_2\le\min(k_2,\psi_2)$;
--   3. problem (1) at $t=1$: maximize $(r+1)p+\mathbb E[V_2(B_2,\Psi,k_1+\delta(a))]$ over $p,a,f\ge 0$ with $p+a+m(k_1)+f\le B_1$, $(r+1)p\le\min(k_1,\psi_1)$, $B_2=B_1-p-a-m(k_1)-f+D(p,a,f)$ and $B_2\ge m(k_1+\delta(a))$;
--   4. problem (2): maximize $(r+1)p+\mathbb E_\Psi[\min(\Psi,(r+1)\hat B_2)]$ over $p,a,f\ge 0$ with $p+a+f=\hat B_1$, $(r+1)p\le\theta$, $\hat B_2\ge 0$ and $(r+1)\hat B_2\le k_1+\delta(a)$, and its optimal allocations;
--   5. $J_{nb}(p)=(r+1)p+\mathbb E_\Psi[\min(\Psi,(r+1)\hat B_2(p,0,\hat B_1-p))]$ (3), problem (S.1) (problem (2) with $a=0$) and its optimal solutions;
--   6. the condition $k_1\le\bar k$, read as: some $p\in[0,\hat B_1]$ has $(r+1)\hat B_2(p,0,\hat B_1-p)\ge k_1$; the sets $\{p\in[0,\hat B_1]:(r+1)\hat B_2(p,0,\hat B_1-p)\ge k_1\}$ (the interval $[p^+_l,p^+_u]$) and $\{p\in[0,\hat B_1]:\hat B_2(p,0,\hat B_1-p)\ge 0\}$ (the interval $[0,p^0_u]$);
--   7. equation (4), $(r+1)\hat B_2(p,a,\hat B_1-p-a)=k_1+\delta(a)$; the property that a function $\hat a$ solves (4) with $0\le\hat a(p)\le\hat B_1-p$ on $[p^+_l,p^+_u]$; $J_b(p)=(r+1)p+\mathbb E_\Psi[\min(\Psi,(r+1)\hat B_2(p,\hat a(p),\hat B_1-p-\hat a(p)))]$ (5); and the allocations that are optimal among the feasible allocations of (2) satisfying (4).
--
--   These are the objects every statement of the mission is phrased in.
--
--   **Formalization Note.** All quantities are real numbers. Strict concavity of $\phi$, the regularity of $m,\delta,\phi$, $m(0)\ge 0$, $B_1>0$, $\psi_1\ge0$ and the full support of $\Psi$ are added to the page's assumptions (see the mission description). Lean's convention $x/0=0$ gives $D(0,0,0)=\phi(0)\cdot 0=0$. $\mathbb E_\Psi[\min(\Psi,y)]$ is the integral of $x\mapsto\min(x,y)$ against $\mu$; it is integrable because $\mu$ lives on $[0,\infty)$. $V_2$ is a supremum; Lemma S.1 shows the supremum is attained and equal to $\min(\psi_2,k_2,(r+1)(B_2-m(k_2)))$, so the expectation in problem (1) is of an almost-everywhere measurable function. Constraint (1e) at $t=2$ is dropped from $V_2$: the terminal value is $0$, and Lemma S.1's allocation $p_2=\hat B_2$ violates (1e) whenever $m>0$. The thresholds $p^+_l,p^+_u,p^0_u$, the function $\hat a$ and the maximizers $\tilde p_{nb},\tilde p_b$ are not defined here; statements take them as variables characterized by hypotheses.
-- source:
--   Kotsi, Aflaki, Aydin & Pedraza-Martinez, Allocation of nonprofit funds among program, fundraising, and administration, SSRN 3460795 (blinded MSOM submission), pp. 7–12 (PDF 7–12), §3, Assumptions 1–2, problems (1)–(2); pp. 16–17 (PDF 16–17), (3)–(5); pp. S5–S8 (PDF 34–37), (S.1)–(S.2)

import Mathlib

namespace NonprofitFunds.Capacity

open MeasureTheory Filter Topology

/-- The fixed data of the two-period nonprofit budget-allocation model (Kotsi, Aflaki, Aydin &
Pedraza-Martinez, §3): return on program `r`, first-period budget `B1`, first-period needs `psi1`,
required administration `m`, capacity expansion `delta`, donation multiplier `phi`, and the law `μ`
of the random second-period needs `Ψ`. The first-period capacity `k1` is not part of the data. -/
structure Params where
  r : ℝ
  B1 : ℝ
  psi1 : ℝ
  m : ℝ → ℝ
  delta : ℝ → ℝ
  phi : ℝ → ℝ
  μ : Measure ℝ

namespace Params

variable (P : Params)

/-- The standing assumptions of §3.1–3.2: `r > 0` (p. 8), Assumption 1(a)–(b) (p. 9),
Assumption 2 (p. 9, with strict concavity of `phi`), regularity of `m`, `delta`, `phi`,
and the law of `Ψ`: a probability measure on `[0, ∞)` with a density and full support. -/
def Standing : Prop :=
  0 < P.r ∧ 0 < P.B1 ∧ 0 ≤ P.psi1 ∧
  -- Assumption 1(a): m convex-increasing (plus m(0) ≥ 0)
  ConvexOn ℝ (Set.Ici 0) P.m ∧ MonotoneOn P.m (Set.Ici 0) ∧ 0 ≤ P.m 0 ∧
  -- Assumption 1(b): δ strictly concave-increasing, δ(0) = 0, δ'(0+) = ∞
  P.delta 0 = 0 ∧ StrictConcaveOn ℝ (Set.Ici 0) P.delta ∧ StrictMonoOn P.delta (Set.Ici 0) ∧
  Tendsto (deriv P.delta) (𝓝[>] 0) atTop ∧
  -- Assumption 2: φ concave (here strictly) and increasing on [0, 1], φ(0) = 1, φ > 1 on (0, 1]
  P.phi 0 = 1 ∧ (∀ x ∈ Set.Ioc (0 : ℝ) 1, 1 < P.phi x) ∧ MonotoneOn P.phi (Set.Icc 0 1) ∧
  StrictConcaveOn ℝ (Set.Icc 0 1) P.phi ∧
  -- regularity
  ContinuousOn P.m (Set.Ici 0) ∧ ContDiffOn ℝ 2 P.m (Set.Ioi 0) ∧
  ContinuousOn P.delta (Set.Ici 0) ∧ ContDiffOn ℝ 2 P.delta (Set.Ioi 0) ∧
  ContinuousOn P.phi (Set.Icc 0 1) ∧ ContDiffOn ℝ 2 P.phi (Set.Ioo 0 1) ∧
  -- the law of Ψ: a probability measure on [0, ∞) with a pdf and full support
  IsProbabilityMeasure P.μ ∧ P.μ (Set.Iio 0) = 0 ∧ P.μ ≪ volume ∧
  (∀ x : ℝ, 0 ≤ x → 0 < P.μ (Set.Ioi x))

/-- The standing range of the first-period capacity: `k1 ≥ 0` and `B1 ≥ 2 m(k1)` (p. 10). -/
def Admissible (k1 : ℝ) : Prop := 0 ≤ k1 ∧ 2 * P.m k1 ≤ P.B1

/-- Donations, Assumption 2: `D(p, a, f) = φ(p / (p + a + f)) · f`. -/
noncomputable def D (p a f : ℝ) : ℝ := P.phi (p / (p + a + f)) * f

/-- First-period net budget `B̂1 = B1 − m(k1)`. -/
def Bhat1 (k1 : ℝ) : ℝ := P.B1 - P.m k1

/-- Second-period net budget `B̂2 = D(p1, a1, f1) − m(k1 + δ(a1))`. -/
noncomputable def Bhat2 (k1 p a f : ℝ) : ℝ := P.D p a f - P.m (k1 + P.delta a)

/-- Remark 2: `θ = min(ψ1, k1, (r + 1) B̂1)`. -/
noncomputable def theta (k1 : ℝ) : ℝ := min P.psi1 (min k1 ((P.r + 1) * P.Bhat1 k1))

/-- `E_Ψ[min(Ψ, y)]`, the expectation against the law `μ` of `Ψ`. -/
noncomputable def Emin (y : ℝ) : ℝ := ∫ x, min x y ∂P.μ

/-! ### Problem (1) at `t = 2` (second period, terminal value `V3 ≡ 0`) -/

/-- Feasible second-period allocations: `p, a, f ≥ 0`, (1a), (1b). -/
def Feasible2nd (B2 psi2 k2 p a f : ℝ) : Prop :=
  0 ≤ p ∧ 0 ≤ a ∧ 0 ≤ f ∧ p + a + P.m k2 + f ≤ B2 ∧ (P.r + 1) * p ≤ min k2 psi2

/-- The attainable second-period rewards `(r + 1) p2`. -/
def V2Set (B2 psi2 k2 : ℝ) : Set ℝ :=
  {v | ∃ p a f, P.Feasible2nd B2 psi2 k2 p a f ∧ v = (P.r + 1) * p}

/-- `V2(B2, ψ2, k2)`, the optimal second-period reward. -/
noncomputable def V2 (B2 psi2 k2 : ℝ) : ℝ := sSup (P.V2Set B2 psi2 k2)

/-! ### Problem (1) at `t = 1` -/

/-- Second-period budget (1c): `B2 = B1 − p − a − m(k1) − f + D(p, a, f)`. -/
noncomputable def B2next (k1 p a f : ℝ) : ℝ := P.B1 - p - a - P.m k1 - f + P.D p a f

/-- Feasible first-period allocations of problem (1): `p, a, f ≥ 0`, (1a), (1b), (1e),
with (1c), (1d) substituted. -/
def Feasible1 (k1 p a f : ℝ) : Prop :=
  0 ≤ p ∧ 0 ≤ a ∧ 0 ≤ f ∧ p + a + P.m k1 + f ≤ P.B1 ∧ (P.r + 1) * p ≤ min k1 P.psi1 ∧
  P.m (k1 + P.delta a) ≤ P.B2next k1 p a f

/-- Objective of problem (1) at `t = 1`: `(r + 1) p + E[V2(B2, Ψ, k1 + δ(a))]`. -/
noncomputable def obj1 (k1 p a f : ℝ) : ℝ :=
  (P.r + 1) * p + ∫ x, P.V2 (P.B2next k1 p a f) x (k1 + P.delta a) ∂P.μ

/-- Attainable objective values of problem (1). -/
def Val1 (k1 : ℝ) : Set ℝ := {v | ∃ p a f, P.Feasible1 k1 p a f ∧ v = P.obj1 k1 p a f}

/-! ### Problem (2) (Lemma 1) -/

/-- Feasible allocations of problem (2): `p, a, f ≥ 0`, (2a), (2b), (2e), (2f),
with (2c), (2d) substituted. -/
def Feasible2 (k1 p a f : ℝ) : Prop :=
  0 ≤ p ∧ 0 ≤ a ∧ 0 ≤ f ∧ p + a + f = P.Bhat1 k1 ∧ (P.r + 1) * p ≤ P.theta k1 ∧
  0 ≤ P.Bhat2 k1 p a f ∧ (P.r + 1) * P.Bhat2 k1 p a f ≤ k1 + P.delta a

/-- Objective of problem (2): `(r + 1) p + E_Ψ[min(Ψ, (r + 1) B̂2)]`. -/
noncomputable def obj2 (k1 p a f : ℝ) : ℝ :=
  (P.r + 1) * p + P.Emin ((P.r + 1) * P.Bhat2 k1 p a f)

/-- Attainable objective values of problem (2). -/
def Val2 (k1 : ℝ) : Set ℝ := {v | ∃ p a f, P.Feasible2 k1 p a f ∧ v = P.obj2 k1 p a f}

/-- An optimal allocation of problem (2). -/
def IsOptimal2 (k1 p a f : ℝ) : Prop :=
  P.Feasible2 k1 p a f ∧ ∀ p' a' f', P.Feasible2 k1 p' a' f' → P.obj2 k1 p' a' f' ≤ P.obj2 k1 p a f

/-! ### The objects of §4.2 and Appendix B -/

/-- `J_nb` (3): the objective of (2) with `a1 = 0`, `f1 = B̂1 − p1`. -/
noncomputable def Jnb (k1 p : ℝ) : ℝ :=
  (P.r + 1) * p + P.Emin ((P.r + 1) * P.Bhat2 k1 p 0 (P.Bhat1 k1 - p))

/-- Feasible points of problem (S.1): (2) with `a1 = 0`, `f1 = B̂1 − p1`. -/
def FeasibleS1 (k1 p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ P.Bhat1 k1 ∧ (P.r + 1) * p ≤ P.theta k1 ∧
  0 ≤ P.Bhat2 k1 p 0 (P.Bhat1 k1 - p) ∧ (P.r + 1) * P.Bhat2 k1 p 0 (P.Bhat1 k1 - p) ≤ k1

/-- An optimal solution `p*_nb` of problem (S.1). -/
def IsOptimalS1 (k1 p : ℝ) : Prop :=
  P.FeasibleS1 k1 p ∧ ∀ q, P.FeasibleS1 k1 q → P.Jnb k1 q ≤ P.Jnb k1 p

/-- `k1 ≤ k̄`, where `k̄/(r + 1) = max_{p1} B̂2(p1, 0)`: some program level raises a
second-period net budget with `(r + 1) B̂2(p1, 0) ≥ k1`. -/
def BelowKbar (k1 : ℝ) : Prop :=
  ∃ p ∈ Set.Icc 0 (P.Bhat1 k1), k1 ≤ (P.r + 1) * P.Bhat2 k1 p 0 (P.Bhat1 k1 - p)

/-- The program levels with `(r + 1) B̂2(p1, 0) ≥ k1`; when nonempty this is `[p⁺_l, p⁺_u]`. -/
def PlusSet (k1 : ℝ) : Set ℝ :=
  {p | p ∈ Set.Icc 0 (P.Bhat1 k1) ∧ k1 ≤ (P.r + 1) * P.Bhat2 k1 p 0 (P.Bhat1 k1 - p)}

/-- The program levels with `B̂2(p1, 0) ≥ 0`; this is `[0, p⁰_u]`. -/
def ZeroSet (k1 : ℝ) : Set ℝ :=
  {p | p ∈ Set.Icc 0 (P.Bhat1 k1) ∧ 0 ≤ P.Bhat2 k1 p 0 (P.Bhat1 k1 - p)}

/-- Equation (4) at `(p1, a1)` with `f1 = B̂1 − p1 − a1`: `(r + 1) B̂2(p1, a1) = k1 + δ(a1)`. -/
def Eq4 (k1 p a : ℝ) : Prop :=
  (P.r + 1) * P.Bhat2 k1 p a (P.Bhat1 k1 - p - a) = k1 + P.delta a

/-- `aHat` is `â` on `[pl, pu]`: for each such `p1`, `â(p1) ∈ [0, B̂1 − p1]` solves (4). -/
def IsAHat (k1 pl pu : ℝ) (aHat : ℝ → ℝ) : Prop :=
  ∀ p ∈ Set.Icc pl pu, 0 ≤ aHat p ∧ aHat p ≤ P.Bhat1 k1 - p ∧ P.Eq4 k1 p (aHat p)

/-- `J_b` (5): the objective of (2) at `a1 = â(p1)`, `f1 = B̂1 − p1 − â(p1)`. -/
noncomputable def Jb (k1 : ℝ) (aHat : ℝ → ℝ) (p : ℝ) : ℝ :=
  (P.r + 1) * p + P.Emin ((P.r + 1) * P.Bhat2 k1 p (aHat p) (P.Bhat1 k1 - p - aHat p))

/-- An allocation optimal among the feasible allocations of (2) that exhaust second-period
capacity, i.e. that satisfy (4). -/
def IsOptimalExh (k1 p a f : ℝ) : Prop :=
  (P.Feasible2 k1 p a f ∧ P.Eq4 k1 p a) ∧
  ∀ p' a' f', P.Feasible2 k1 p' a' f' → P.Eq4 k1 p' a' → P.obj2 k1 p' a' f' ≤ P.obj2 k1 p a f

end Params

end NonprofitFunds.Capacity


