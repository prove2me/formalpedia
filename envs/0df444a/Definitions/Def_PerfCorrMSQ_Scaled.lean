-- Prove2me | Definitions.Def_PerfCorrMSQ_Scaled
-- name    : PerfCorrMSQ_Scaled
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:50.257921+00:00
-- url     : https://prove2.me/theorems/b40589c1-b3df-4b7d-9bfd-cb5a9b8f59b0
-- title:
--   Diffusion and LOF scalings of the processes, and the initial conditions (Ia), (Ib)
-- statement:
--   Diffusion scaling (pp.6, 13): $\hat X^n=n^{-1/2}(X^n-n)$, and $\hat Y^n=n^{-1/2}Y^n$ for $Y=Q_0,Z_0,U_1,U_2,V,M_A,M_S,M_R$; $\hat L^n(0)=n^{-1/2}L^n(0)$.
--
--   LOF scaling (pp.8, 13–14): $\tilde X^n(t)=n^{-3/4}(X^n(n^{1/4}t)-n)$, likewise $\tilde Z^n,\tilde Z^n_2$ centered at $n$; $\tilde Y^n(t)=n^{-3/4}Y^n(n^{1/4}t)$ for $Y=Q,Q_0,Z_0,Z_1,U_1,U_2,V,M_A,M_S,M_R$; $\tilde w^n(t)=n^{1/4}w^n(n^{1/4}t)$; $\tilde L^n(0)=n^{-3/4}L^n(0)$.
--
--   The initial conditions (p.9), for a probability measure $\nu$ on $\mathbb R$ (the law of $X_0$):
--
--   $$
--   \text{(Ia)}\quad(\hat X^n(0),\hat L^n(0))\Rightarrow(X_0,0),\qquad \text{(Ib)}\quad(\tilde X^n(0),\tilde L^n(0))\Rightarrow(X_0,0),\ X_0\ge0\text{ a.s.}
--   $$
--
--   **Formalization Note** Each condition is stated as weak convergence of the laws of the first coordinate to $\nu$ (against bounded continuous functions) together with convergence in probability of the second to $0$; since the second limit is constant this is equivalent to joint convergence in $\mathbb R^2$. $X_0\ge0$ is $\nu((-\infty,0))=0$. The page prints $\tilde Q^n_0(t):=n^{-3/4}Q^n(n^{1/4}t)$, a typo for $Q^n_0$. At $n=0$ every scaled quantity is $0$ (division by $0$), a value no statement uses.
-- source:
--   Yu and Perry, Many-Server Heavy-Traffic Limits for Queueing Systems with Perfectly Correlated Service and Patience Times, arXiv:2008.12890v1, §3.1 p.6, §3.2 p.8, §3.3 p.9 ((Ia), (Ib)), §5.1 p.13, §5.2 pp.13–14

import Mathlib
import Definitions.Def_PerfCorrMSQ_Model

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction
open scoped NNReal

namespace PerfCorrMSQ

/-!
Diffusion scaling (§3.1 p.6 and §5.1 p.13) and LOF scaling (§3.2 p.8 and §5.2 pp.13–14) of the
processes of system `n`, and the initial conditions (Ia), (Ib) (p.9) of Yu–Perry,
arXiv:2008.12890v1.

**Formalization Note.** Every scaled process is a function `n ↦ ω ↦ t ↦ value` with real time
`t`, used at `t ≥ 0`. Scalings divide by `√n` or `n^{3/4}`; at `n = 0` Lean's `x / 0 = 0` makes
every scaled process the constant `0`, a value no statement uses (every hypothesis is for
`n ≥ 1`, and every limit is as `n → ∞`).
-/

variable {Ω : Type*}

/-- Diffusion scaling `n^{−1/2} y(t)`. -/
noncomputable def dif (n : ℕ) (y : ℝ → ℝ) (t : ℝ) : ℝ := y t / Real.sqrt n

/-- Centered diffusion scaling `n^{−1/2}(y(t) − n)`. -/
noncomputable def difC (n : ℕ) (y : ℝ → ℝ) (t : ℝ) : ℝ := (y t - n) / Real.sqrt n

/-- LOF scaling `n^{−3/4} y(n^{1/4} t)`. -/
noncomputable def lof (n : ℕ) (y : ℝ → ℝ) (t : ℝ) : ℝ :=
  y ((n : ℝ) ^ ((1 : ℝ) / 4) * t) / (n : ℝ) ^ ((3 : ℝ) / 4)

/-- Centered LOF scaling `n^{−3/4}(y(n^{1/4} t) − n)`. -/
noncomputable def lofC (n : ℕ) (y : ℝ → ℝ) (t : ℝ) : ℝ :=
  (y ((n : ℝ) ^ ((1 : ℝ) / 4) * t) - n) / (n : ℝ) ^ ((3 : ℝ) / 4)

/-! ### Diffusion-scaled processes (p.6, p.13) -/

/-- `X̂ⁿ(t) = n^{−1/2}(Xⁿ(t) − n)`. -/
noncomputable def Xhat (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  difC n (fun t => ((sys.prim n ω).X θ n t : ℝ)) t

/-- `Q̂ⁿ₀ = n^{−1/2} Qⁿ₀`. -/
noncomputable def Q0hat (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  dif n (fun t => ((sys.prim n ω).Q0 θ n t : ℝ)) t

/-- `Ẑⁿ₀ = n^{−1/2} Zⁿ₀`. -/
noncomputable def Z0hat (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  dif n (fun t => ((sys.prim n ω).Z0 θ n t : ℝ)) t

/-- `Ûⁿ₁ = n^{−1/2} Uⁿ₁`. -/
noncomputable def U1hat (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  dif n ((sys.prim n ω).U1 θ n) t

/-- `Ûⁿ₂ = n^{−1/2} Uⁿ₂`. -/
noncomputable def U2hat (θ : ℝ) (lam : ℕ → ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω)
    (t : ℝ) : ℝ :=
  dif n ((sys.prim n ω).U2 θ n (lam n)) t

/-- `V̂ⁿ = n^{−1/2} Vⁿ`. -/
noncomputable def Vhat (θ : ℝ) (lam : ℕ → ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω)
    (t : ℝ) : ℝ :=
  dif n ((sys.prim n ω).V θ n (lam n)) t

/-- `M̂ⁿ_A = n^{−1/2} Mⁿ_A`. -/
noncomputable def MAhat (lam : ℕ → ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  dif n ((sys.prim n ω).MA (lam n)) t

/-- `M̂ⁿ_S = n^{−1/2} Mⁿ_S`. -/
noncomputable def MShat (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  dif n ((sys.prim n ω).MS θ n) t

/-- `M̂ⁿ_R = n^{−1/2} Mⁿ_R`. -/
noncomputable def MRhat (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  dif n ((sys.prim n ω).MR θ n) t

/-- `L̂ⁿ(0) = n^{−1/2} Lⁿ(0)` (p.9). -/
noncomputable def L0hat (sys : SystemData Ω) (n : ℕ) (ω : Ω) : ℝ :=
  (sys.prim n ω).L0 / Real.sqrt n

/-! ### LOF-scaled processes (p.8, pp.13–14) -/

/-- `X̃ⁿ(t) = n^{−3/4}(Xⁿ(n^{1/4} t) − n)`. -/
noncomputable def Xtil (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  lofC n (fun t => ((sys.prim n ω).X θ n t : ℝ)) t

/-- `Z̃ⁿ(t) = n^{−3/4}(Zⁿ(n^{1/4} t) − n)`. -/
noncomputable def Ztil (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  lofC n (fun t => ((sys.prim n ω).Z θ n t : ℝ)) t

/-- `Z̃ⁿ₁(t) = n^{−3/4} Zⁿ₁(n^{1/4} t)`. -/
noncomputable def Z1til (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  lof n (fun t => ((sys.prim n ω).Z1 θ n t : ℝ)) t

/-- `Z̃ⁿ₂(t) = n^{−3/4}(Zⁿ₂(n^{1/4} t) − n)`. -/
noncomputable def Z2til (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  lofC n ((sys.prim n ω).Z2 θ n) t

/-- `Z̃ⁿ₀(t) = n^{−3/4} Zⁿ₀(n^{1/4} t)`. -/
noncomputable def Z0til (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  lof n (fun t => ((sys.prim n ω).Z0 θ n t : ℝ)) t

/-- `Q̃ⁿ(t) = n^{−3/4} Qⁿ(n^{1/4} t)`. -/
noncomputable def Qtil (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  lof n (fun t => ((sys.prim n ω).Q θ n t : ℝ)) t

/-- `Q̃ⁿ₀(t) = n^{−3/4} Qⁿ₀(n^{1/4} t)` (p.13 prints `Qⁿ` for `Qⁿ₀`, a typo). -/
noncomputable def Q0til (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  lof n (fun t => ((sys.prim n ω).Q0 θ n t : ℝ)) t

/-- `Ũⁿ₁(t) = n^{−3/4} Uⁿ₁(n^{1/4} t)`. -/
noncomputable def U1til (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  lof n ((sys.prim n ω).U1 θ n) t

/-- `Ũⁿ₂(t) = n^{−3/4} Uⁿ₂(n^{1/4} t)`. -/
noncomputable def U2til (θ : ℝ) (lam : ℕ → ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω)
    (t : ℝ) : ℝ :=
  lof n ((sys.prim n ω).U2 θ n (lam n)) t

/-- `Ṽⁿ(t) = n^{−3/4} Vⁿ(n^{1/4} t)`. -/
noncomputable def Vtil (θ : ℝ) (lam : ℕ → ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω)
    (t : ℝ) : ℝ :=
  lof n ((sys.prim n ω).V θ n (lam n)) t

/-- `M̃ⁿ_A(t) = n^{−3/4} Mⁿ_A(n^{1/4} t)`. -/
noncomputable def MAtil (lam : ℕ → ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  lof n ((sys.prim n ω).MA (lam n)) t

/-- `M̃ⁿ_S(t) = n^{−3/4} Mⁿ_S(n^{1/4} t)`. -/
noncomputable def MStil (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  lof n ((sys.prim n ω).MS θ n) t

/-- `M̃ⁿ_R(t) = n^{−3/4} Mⁿ_R(n^{1/4} t)`. -/
noncomputable def MRtil (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  lof n ((sys.prim n ω).MR θ n) t

/-- `w̃ⁿ(t) = n^{1/4} wⁿ(n^{1/4} t)`. -/
noncomputable def wtil (θ : ℝ) (sys : SystemData Ω) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  (n : ℝ) ^ ((1 : ℝ) / 4) * (sys.prim n ω).w θ n ((n : ℝ) ^ ((1 : ℝ) / 4) * t)

/-- `L̃ⁿ(0) = n^{−3/4} Lⁿ(0)` (p.9). -/
noncomputable def L0til (sys : SystemData Ω) (n : ℕ) (ω : Ω) : ℝ :=
  (sys.prim n ω).L0 / (n : ℝ) ^ ((3 : ℝ) / 4)

/-! ### Initial conditions (p.9) -/

/-- **Condition (Ia)** (p.9): `(X̂ⁿ(0), L̂ⁿ(0)) ⇒ (X₀, 0)` in `ℝ²`, with `X₀ ∼ ν`. Stated as weak
convergence of the laws of `X̂ⁿ(0)` to `ν` (against bounded continuous test functions) together
with `L̂ⁿ(0) → 0` in probability; since the second limit is a constant, this is equivalent to the
joint convergence. -/
def InitialIa [MeasurableSpace Ω] (P : Measure Ω) (θ : ℝ) (sys : SystemData Ω)
    (ν : ProbabilityMeasure ℝ) : Prop :=
  (∀ g : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ => ∫ ω, g (Xhat θ sys n ω 0) ∂P) atTop
    (𝓝 (∫ x, g x ∂(ν : Measure ℝ)))) ∧
  TendstoInMeasure P (fun n ω => L0hat sys n ω) atTop (fun _ => 0)

/-- **Condition (Ib)** (p.9): `(X̃ⁿ(0), L̃ⁿ(0)) ⇒ (X₀, 0)` in `ℝ²`, where `X₀ ∼ ν` and `X₀ ≥ 0`
w.p.1 (`ν` gives no mass to `(−∞, 0)`). Encoded as for `PerfCorrMSQ.InitialIa`. -/
def InitialIb [MeasurableSpace Ω] (P : Measure Ω) (θ : ℝ) (sys : SystemData Ω)
    (ν : ProbabilityMeasure ℝ) : Prop :=
  (∀ g : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ => ∫ ω, g (Xtil θ sys n ω 0) ∂P) atTop
    (𝓝 (∫ x, g x ∂(ν : Measure ℝ)))) ∧
  TendstoInMeasure P (fun n ω => L0til sys n ω) atTop (fun _ => 0) ∧
  (ν : Measure ℝ) (Set.Iio 0) = 0

end PerfCorrMSQ


