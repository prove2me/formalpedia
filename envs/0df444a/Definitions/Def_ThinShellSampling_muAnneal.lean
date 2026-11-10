-- Prove2me | Definitions.Def_ThinShellSampling_muAnneal
-- name    : ThinShellSampling_muAnneal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:47:13.539202+00:00
-- url     : https://prove2.me/theorems/40dd6cb8-eefc-40ca-9bba-c05bf8e3bf1b
-- title:
--   Exponential lift, truncation $\bar K$, $\bar\pi$, and annealing laws $\mu_{\sigma^2,\rho}$
-- statement:
--   For a convex $V$ under the standing assumptions, the **exponential lift** is the law $\pi^{X,T}(dx,dt)\propto e^{-nt}1_K(x,t)\,dx\,dt$ on $\mathbb R^n\times\mathbb R$ with $K=\{(x,t):V(x)\le nt\}$; its $X$-marginal is $\pi$. With $a=V(0)/n$, $\ell=\log(4e)$, $D=1\vee R\ell$ and $b=13\ell+5$, the **truncated epigraph** is
--
--   $$
--   \bar K=K\cap\big(B(0,D)\times[a-10,a+b]\big).
--   $$
--
--   The **truncated lift** is $\bar\pi^{X,T}\propto\pi^{X,T}1_{\bar K}$, and $\bar\pi$ is its $X$-marginal. The **annealing laws** (6.1) are, for $\rho\ge0$, $\sigma^2>0$,
--
--   $$
--   \mu_{\sigma^2,\rho}(dx,dt)\propto\exp\Big(-\frac{\|x\|^2}{2\sigma^2}-\rho t\Big)1_{\bar K}(x,t)\,dx\,dt .
--   $$
--
--   At $\rho=n$ the $X$-marginal of $\mu_{\sigma^2,n}$ is the Gaussian tilt $\bar\pi_{\sigma^2}$. Algorithm 6.6 anneals along $(n^{-1},1)\to(n^{-1},n)\to(\sigma^2_{\mathrm{last}},n)$.
--
--   **Formalization Note** The radius parameter $R$ is explicit; every statement uses $R=(\mathbb E_\pi\|X\|^2)^{1/2}$. $B(0,D)$ is taken closed (a null-set difference).
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), §6.1, (exp-lifting), p.34 (PDF p.36); §6.2, pp.35–36 (PDF pp.37–38); (6.1), p.36 (PDF p.38)

import Mathlib
import Definitions.Def_ThinShellSampling_expTilt
import Definitions.Def_ThinShellSampling_piOf

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory
open scoped ENNReal

/-- **The epigraph `K = {(x, t) ∈ ℝⁿ × ℝ : V(x) ≤ nt}`** of the exponential lift.

Kook, Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity*, STOC 2027 submission
(manuscript sha256 25a041a9…), §6.1, display (exp-lifting), p.34 (PDF p.36). Points with `V(x) = ∞`
lie in no fibre. -/
def liftK {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) :
    Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  {z | V z.1 ≤ (((n : ℝ) * z.2 : ℝ) : WithTop ℝ)}

/-- `a = V(0)/n`, "known from one oracle query" (§6.2, p.35 = PDF p.37). -/
noncomputable def aConst {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : ℝ :=
  vr V 0 / n

/-- `ℓ = log(4e)` (§6.2, p.35 = PDF p.37). -/
noncomputable def ellC : ℝ := Real.log (4 * Real.exp 1)

/-- `D = 1 ∨ Rℓ` (§6.2, p.35 = PDF p.37). -/
noncomputable def Drad (R : ℝ) : ℝ := max 1 (R * ellC)

/-- `b = 13ℓ + 5` (§6.2, p.35 = PDF p.37). -/
noncomputable def bConst : ℝ := 13 * ellC + 5

/-- **The truncated epigraph** `K̄ = K ∩ (B(0, D) × [a − 10, a + b])`, with `D = 1 ∨ Rℓ`,
`ℓ = log(4e)`, `b = 13ℓ + 5`, `a = V(0)/n`.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §6.2, "Constant-mass
truncation", p.35 (PDF p.37): "let `ℓ := log(4e)`, `D := 1 ∨ Rℓ`, and `b := 13ℓ + 5`. We then truncate
the epigraph `K` as follows: `K̄ := K ∩ (B(0, D) × [a − 10, a + b])`."

**Formalization Note.** `R` is a parameter (in every use, `R = Rrad V = (E_π‖X‖²)^{1/2}`).
`B(0, D)` is taken closed; the open ball differs by a Lebesgue-null set, so no law below changes. -/
def Kbar {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (R : ℝ) :
    Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  liftK V ∩ (Metric.closedBall 0 (Drad R) ×ˢ Set.Icc (aConst V - 10) (aConst V + bConst))

/-- **The truncated lift** `π̄^{X,T} ∝ π^{X,T} 1_{K̄}`, i.e. `π̄^{X,T}(dx, dt) ∝ e^{−nt} 1_{K̄}(x, t) dx dt`.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §6.2, p.36 (PDF p.38): "Let
`π̄^{X,T} ∝ π^{X,T} 1_{K̄}` be the truncated distribution", with `dπ^{X,T}(x, t) ∝ e^{−nt} 1_K(x, t) dx dt`
(exp-lifting), p.34; `K̄ ⊆ K`. -/
noncomputable def piBarLift {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (R : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n) × ℝ) :=
  expTilt ((volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict (Kbar V R))
    (fun z => (n : ℝ) * z.2)

/-- **`π̄`, the `X`-marginal of the truncated lift** (§6.2, p.36 = PDF p.38: "write `π̄` for its
`X`-marginal"). -/
noncomputable def piBar {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (R : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (piBarLift V R).map Prod.fst

/-- **The annealing laws (6.1)** `μ_{σ²,ρ}(dx, dt) ∝ exp(−‖x‖²/(2σ²) − ρt) 1_{K̄}(x, t) dx dt`.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §6.3, eq. (6.1), p.36 (PDF
p.38): "we use the following annealing distribution with parameters `ρ ≥ 0` and `σ² > 0`".

**Formalization Note.** Built from the same `Kbar V R` as `piBar`; at `ρ = n` its `X`-marginal is the
Gaussian tilt `π̄_{σ²}` (p.38). Only `σ² > 0`, `ρ ≥ 0` are used. -/
noncomputable def muAnneal {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (R σ2 ρ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n) × ℝ) :=
  expTilt ((volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict (Kbar V R))
    (fun z => ‖z.1‖ ^ 2 / (2 * σ2) + ρ * z.2)

end ThinShellSampling


