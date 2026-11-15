-- Prove2me | Definitions.Def_StableMSR_Recovery_Supplement_Hub
-- name    : StableMSR_Recovery_Supplement_Hub
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:11:26.292322+00:00
-- url     : https://prove2.me/theorems/20c396d1-f6a5-47a1-9e21-8109a3a2514e
-- title:
--   Metric perturbations and the hub/dummy construction
-- statement:
--   Let $(Y,d_Y)$ be a nonempty finite metric space, $1\le k\le |Y|$, $\tau>0$, and $\gamma>1$. Write $a=\mathrm{OPT}_k(Y)$ for the attained minimum over all exact-$k$ partitions. Define
--
--   $$
--   D=\operatorname{diam}(Y),\quad R_0=1+D+\tau+\frac\tau{\gamma-1},\quad
--   \delta=\gamma R_0-\tau,\quad L_0=\delta+R_0+1.
--   $$
--
--   Adjoin a hub $u_0$ and $k+1$ dummies. Preserve source distances, set $d(u_0,y)=R_0$, set distinct dummy distances to $\delta$, and set every source-or-hub to dummy distance to $L_0$. Diagonal distances are zero. The target has $K=k+2$ clusters and supplied partition $\mathcal O_0=\{Y\cup\{u_0\}\}\cup\{\{z\}:z\text{ dummy}\}$. Its threshold is $\lambda_*=(\delta+a)/R_0$.
--
--   Metric perturbations are the published symmetric bounded perturbations with the triangle inequality added. Metric stability requires unique optimality under every such real perturbation. These definitions support the exact reduction and its threshold.
--
--   **Formalization Note** Source points occupy indices below $n$, the hub has index $n$, and dummies occupy the remaining $k+1$ indices. The optimum is a minimum of a finite nonempty family on every valid input. Invalid counts have a zero convention, never used in a theorem.
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), pp. 23–25, Appendix C equations (3)–(5); PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Geometry

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Supplement

/-- A finite, attained minimum when feasible partitions exist; the empty-family fallback is zero. -/
noncomputable def optimumValue {n : ℕ} (d : Point n → Point n → ℝ) (k : ℕ) : ℝ :=
  let Q := (Finset.univ : Finset (Partition n)).filter (Feasible Finset.univ k)
  if h : Q.Nonempty then Q.inf' h (cost d) else 0

noncomputable def hubRadius {n : ℕ} (d : Point n → Point n → ℝ) (γ τ : ℝ) : ℝ :=
  1 + diameter d Finset.univ + τ + τ / (γ - 1)

noncomputable def dummyDistance {n : ℕ} (d : Point n → Point n → ℝ) (γ τ : ℝ) : ℝ :=
  γ * hubRadius d γ τ - τ

noncomputable def crossDistance {n : ℕ} (d : Point n → Point n → ℝ) (γ τ : ℝ) : ℝ :=
  dummyDistance d γ τ + hubRadius d γ τ + 1

/-- Y = [0,n), hub = n, and k+1 dummies = [n+1,n+k+2). -/
noncomputable def hubDistance {n : ℕ} (d : Point n → Point n → ℝ)
    (k : ℕ) (γ τ : ℝ) (x y : Point (n + k + 2)) : ℝ :=
  if x = y then 0 else
  if hx : x.val < n then
    if hy : y.val < n then d ⟨x.val,hx⟩ ⟨y.val,hy⟩
    else if y.val = n then hubRadius d γ τ else crossDistance d γ τ
  else if _hy : y.val < n then
    if x.val = n then hubRadius d γ τ else crossDistance d γ τ
  else if x.val = n ∨ y.val = n then crossDistance d γ τ
  else dummyDistance d γ τ

noncomputable def hubSource (n k : ℕ) : Cluster (n + k + 2) :=
  Finset.univ.filter (fun x => x.val ≤ n)

noncomputable def suppliedPartition (n k : ℕ) : Partition (n + k + 2) :=
  insert (hubSource n k)
    (((Finset.univ : Cluster (n + k + 2)).filter (fun x => n < x.val)).image (fun x => {x}))

noncomputable def stabilityThreshold {n : ℕ} (d : Point n → Point n → ℝ)
    (k : ℕ) (γ τ : ℝ) : ℝ :=
  (dummyDistance d γ τ + optimumValue d k) / hubRadius d γ τ

def MetricPerturbation {n : ℕ} (d : Point n → Point n → ℝ) (γ : ℝ)
    (p : Point n → Point n → ℝ) : Prop :=
  Perturbation d γ p ∧ ∀ x y z, p x z ≤ p x y + p y z

noncomputable def StableMetric {n : ℕ} (d : Point n → Point n → ℝ)
    (k : ℕ) (γ : ℝ) (O : Partition n) : Prop :=
  Feasible Finset.univ k O ∧ ∀ p, MetricPerturbation d γ p → UniqueOptimal p Finset.univ k O

end StableMSR.Recovery.Supplement


