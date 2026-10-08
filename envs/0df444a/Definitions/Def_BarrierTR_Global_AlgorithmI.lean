-- Prove2me | Definitions.Def_BarrierTR_Global_AlgorithmI
-- name    : BarrierTR_Global_AlgorithmI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:40.794996+00:00
-- url     : https://prove2.me/theorems/4632e3fd-9323-4807-b623-d0ebc6841df7
-- title:
--   §2.3, pp. 16–17 — Algorithm I: trials at decreasing radii, penalty update (2.39), acceptance test, slack reset; Assumptions 4.1
-- statement:
--   **Algorithm I** (p. 16) applies a trust-region SQP step to the barrier problem (2.2) with fixed $\mu>0$. Its data are $\xi,\eta,\rho,\tau\in(0,1)$, $\beta>0$, an initial penalty $\nu_{-1}>0$, an initial radius $\Delta_0>0$, the Cauchy constants $\gamma_1,\gamma_2>0$, the bound $\gamma_Z>0$ of (2.30), a contraction factor $c\in(0,1)$ and a norm $\|\cdot\|_T$ on $\mathbb R^{n+m}$. At iteration $k$, with iterate $(x_k,s_k)$, $s_0>0$, symmetric $B_k$ and null-space basis $Z_k$, it tries radii $\Delta$ and at each one
--
--   1. computes a vertical step $v$ feasible for (2.37), satisfying the range space condition (2.14) and the vertical Cauchy condition (2.18) with $\tilde\Delta=\xi\Delta$;
--   2. picks $\hat\Delta$ with $\Delta-\|(v_x,\tilde Dv_s)\|_T\le\hat\Delta\le\Delta$, a horizontal step $h$ feasible for (2.26) satisfying (2.33), and the total step $d=v+h$ with $\|(d_x,Dd_s)\|_T\le\Delta$ (2.38);
--   3. chooses the smallest $\nu$ with
--   $$\mathrm{pred}_k(d)\ge\rho\,\nu\,\mathrm{vpred}_k(v)\qquad(2.39),$$
--   replaced by $\nu_{k-1}$ if $\nu\le\nu_{k-1}$, and otherwise increased if necessary so that $\nu\ge1.5\,\nu_{k-1}$;
--   4. rejects $d$ if $\phi(x_k+d_x,s_k+d_s;\nu)>\phi(x_k,s_k;\nu)-\eta\,\mathrm{pred}_k(d)$ or $d_s^{(i)}<-\tau s_k^{(i)}$ for some $i$, and then retries with $\Delta$ replaced by $c\Delta$;
--   5. on acceptance sets $x_{k+1}=x_k+d_x$, $s_{k+1}=\max(s_k+d_s,-g(x_{k+1}))$ componentwise, and a first radius $\Delta_{k+1}\ge\Delta_k$ for the next iteration.
--
--   A **run** records the iterates, $B_k$, $Z_k$, and all trials of every iteration, the last one accepted; `IsRunUpTo N` imposes the rules on iterations $k<N$, and `IsRun` is the infinite run. **Assumptions 4.1**: (a) $f,g$ are differentiable on an open convex set $X$ containing all iterates and $\nabla f$, $g$, $A$ are Lipschitz on $X$; (b) $\{f_k\}$ is bounded below and $\{\nabla f_k\},\{g_k\},\{A_k\},\{B_k\}$ are bounded.
--
--   This is the object of the global analysis of §3–§4 and the inner loop of Algorithm II.
--
--   **Formalization Note** "Solving approximately" is read as returning a feasible point satisfying the printed conditions. By (2.40)–(2.41), when (2.39) fails at $\nu_{k-1}$ and $\mathrm{vpred}_k(v)>0$, the smallest admissible $\nu$ is $-(\mathrm{hpred}_k(h)+\chi_k)/((1-\rho)\,\mathrm{vpred}_k(v))$; the update is written with this value, and the constant $1.5$ is kept. The step-4 factor is a fixed $c\in(0,1)$ (the paper's example is $1/2$). The multipliers $\lambda_k$ are not recorded: the paper leaves them free and they enter only through $B_k$. Iterations are indexed from $k=0$.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, pp. 16–21, Algorithm I, (2.37)–(2.41), Assumptions 4.1

import Mathlib
import Definitions.Def_BarrierTR_Global_Setting

namespace BarrierTR.Global

open scoped RealInnerProductSpace
open Filter Topology

variable {n m : ℕ}

/-- The data chosen at the start of Algorithm I (p. 16), plus the constants of the conditions it
imposes on the steps: the barrier parameter `μ > 0`; `ξ, η, ρ, τ ∈ (0, 1)`; `β > 0`; the initial
penalty `ν₋₁ > 0` (`νInit`); the initial radius `Δ₀ > 0`; the Cauchy constants `γ₁, γ₂ > 0` of
(2.18), (2.33); the bound `γ_Z > 0` of (2.30); the factor `c ∈ (0, 1)` by which Step 4 decreases
`Δ_k`; and the trust-region norm `‖·‖_T` on `ℝⁿ⁺ᵐ`. -/
structure Params (n m : ℕ) where
  μ : ℝ
  ξ : ℝ
  η : ℝ
  ρ : ℝ
  τ : ℝ
  β : ℝ
  νInit : ℝ
  Δ₀ : ℝ
  γ₁ : ℝ
  γ₂ : ℝ
  γZ : ℝ
  c : ℝ
  T : Seminorm ℝ (Z n m)
  μ_pos : 0 < μ
  ξ_mem : 0 < ξ ∧ ξ < 1
  η_mem : 0 < η ∧ η < 1
  ρ_mem : 0 < ρ ∧ ρ < 1
  τ_mem : 0 < τ ∧ τ < 1
  β_pos : 0 < β
  νInit_pos : 0 < νInit
  Δ₀_pos : 0 < Δ₀
  γ₁_pos : 0 < γ₁
  γ₂_pos : 0 < γ₂
  γZ_pos : 0 < γZ
  c_mem : 0 < c ∧ c < 1
  T_definite : ∀ z, T z = 0 → z = 0

/-- One pass through Steps 1–3 of Algorithm I at a trust-region radius `Δ`: the vertical step `v`,
the horizontal radius `Δ̂`, the horizontal step `h`, and the penalty parameter `ν`. The total step
is `d = v + h`. -/
structure Trial (n m : ℕ) where
  Δ : ℝ
  v : Z n m
  Δhat : ℝ
  h : Z n m
  ν : ℝ

/-- The total step `d = v + h` of a trial. -/
def Trial.d (t : Trial n m) : Z n m := t.v + t.h

/-- Steps 1–3 of Algorithm I at the iterate `(x, s)` with matrices `B`, `Z = (Z_xᵀ Z_sᵀ)ᵀ` and
previous penalty `ν_prev = ν_{k−1}`, at the radius `t.Δ > 0`:
1. `v` is feasible for (2.37) and satisfies (2.14) and (2.18), with `Δ̃ = ξΔ`, `δ̃ = max(β, Δ̃)`;
2. `Δ − ‖(v_x, D̃v_s)‖_T ≤ Δ̂ ≤ Δ` (p. 14), `h` is feasible for (2.26) and satisfies (2.33), and
   `d = v + h` is feasible for (2.38): `‖(d_x, D d_s)‖_T ≤ Δ`, `D = max(β, Δ) S⁻¹`;
3. `ν` is the smallest value with `pred(d) ≥ ρ ν vpred(v)` (2.39), replaced by `ν_prev` if it is
   `≤ ν_prev` and otherwise increased if necessary to at least `1.5 ν_prev`. When (2.39) fails at
   `ν_prev` and `vpred(v) > 0`, the smallest such `ν` is `−(hpred(h) + χ)/((1 − ρ) vpred(v))`
   by (2.40)–(2.41). -/
structure IsTrial (P : Params n m) (f : E n → ℝ) (g : E n → F m) (x : E n) (s : F m)
    (B : E n →L[ℝ] E n) (Zx : E n →L[ℝ] E n) (Zs : E n →L[ℝ] F m) (νprev : ℝ)
    (t : Trial n m) : Prop where
  radius_pos : 0 < t.Δ
  vert_feasible : VertFeasible P.T P.β (P.ξ * t.Δ) s t.v
  range_space : RangeSpaceCond P.T P.β (P.ξ * t.Δ) g x s t.v
  vert_cauchy : VertCauchy P.T P.β (P.ξ * t.Δ) P.γ₁ g x s t.v
  Δhat_lower : t.Δ - P.T (scaleD (max P.β (P.ξ * t.Δ)) s t.v) ≤ t.Δhat
  Δhat_upper : t.Δhat ≤ t.Δ
  horiz_feasible : HorizFeasible P.T P.β t.Δ t.Δhat g x s t.h
  horiz_cauchy : HorizCauchy P.T P.β t.Δ t.Δhat P.γ₂ f P.μ x s B Zx Zs t.v t.h
  total_feasible : P.T (scaleD (max P.β t.Δ) s t.d) ≤ t.Δ
  penalty : t.ν =
    if P.ρ * νprev * vpred g x s t.v ≤ pred f g P.μ νprev x s B t.d then νprev
    else max (-(hpred f P.μ x s B t.v t.h + chi f P.μ x s B t.v) /
      ((1 - P.ρ) * vpred g x s t.v)) (1.5 * νprev)

/-- Step 4 of Algorithm I rejects the trial step `d` with penalty `ν`:
`d_s⁽ⁱ⁾ < −τ s⁽ⁱ⁾` for some `i`, or `φ(x + d_x, s + d_s; ν) > φ(x, s; ν) − η pred(d)`.
(When the first disjunct fails, `s + d_s ≥ (1 − τ)s > 0`, so the merit function is evaluated
only at positive slacks.) -/
def Rejected (P : Params n m) (f : E n → ℝ) (g : E n → F m) (x : E n) (s : F m)
    (B : E n →L[ℝ] E n) (ν : ℝ) (d : Z n m) : Prop :=
  (∃ i, d.snd i < -P.τ * s i) ∨
    merit f g P.μ ν x s - P.η * pred f g P.μ ν x s B d < merit f g P.μ ν (x + d.fst) (s + d.snd)

/-- The record of a run of Algorithm I: iterates `x_k`, `s_k`, matrices `B_k` and
`Z_k = (Z_xᵀ Z_sᵀ)ᵀ`, and at iteration `k` the trials `trial k 0, …, trial k (rejections k)`
at successively smaller radii; the last one is accepted. -/
structure RunData (n m : ℕ) where
  x : ℕ → E n
  s : ℕ → F m
  B : ℕ → E n →L[ℝ] E n
  Zx : ℕ → E n →L[ℝ] E n
  Zs : ℕ → E n →L[ℝ] F m
  rejections : ℕ → ℕ
  trial : ℕ → ℕ → Trial n m

namespace RunData

variable (R : RunData n m)

/-- The accepted trial of iteration `k`. -/
def acc (k : ℕ) : Trial n m := R.trial k (R.rejections k)
/-- The accepted radius `Δ_k`. -/
def Δ (k : ℕ) : ℝ := (R.acc k).Δ
/-- The penalty parameter `ν_k`. -/
def ν (k : ℕ) : ℝ := (R.acc k).ν
/-- The accepted vertical step `v_k`. -/
def v (k : ℕ) : Z n m := (R.acc k).v
/-- The accepted horizontal step `h_k`. -/
def h (k : ℕ) : Z n m := (R.acc k).h
/-- The accepted horizontal radius `Δ̂_k`. -/
def Δhat (k : ℕ) : ℝ := (R.acc k).Δhat
/-- The accepted total step `d_k = v_k + h_k`. -/
def d (k : ℕ) : Z n m := (R.acc k).d
/-- `ν_{k−1}`: the initial penalty `ν₋₁` at `k = 0`, else the previous accepted penalty. -/
def νPrev (P : Params n m) : ℕ → ℝ
  | 0 => P.νInit
  | k + 1 => R.ν k

end RunData

/-- Iteration `k` of Algorithm I (Steps 1–5): `B_k` is symmetric, `Z_k` satisfies (2.29)–(2.30),
every trial is a valid pass through Steps 1–3 with `ν_prev = ν_{k−1}`, each rejected trial fails
Step 4 and is followed by one at radius `c` times smaller, the last trial passes Step 4, and
Step 5 sets `x_{k+1} = x_k + d_x`, `s_{k+1} = max(s_k + d_s, −g(x_{k+1}))` (componentwise) and a
first radius `Δ_{k+1} ≥ Δ_k` for the next iteration. -/
structure IsStep (P : Params n m) (f : E n → ℝ) (g : E n → F m) (R : RunData n m) (k : ℕ) :
    Prop where
  B_symm : IsSelfAdjoint (R.B k)
  null_basis : IsNullBasis g (R.x k) P.γZ (R.Zx k) (R.Zs k)
  trials : ∀ j ≤ R.rejections k,
    IsTrial P f g (R.x k) (R.s k) (R.B k) (R.Zx k) (R.Zs k) (R.νPrev P k) (R.trial k j)
  rejected : ∀ j < R.rejections k,
    Rejected P f g (R.x k) (R.s k) (R.B k) (R.trial k j).ν (R.trial k j).d ∧
      (R.trial k (j + 1)).Δ = P.c * (R.trial k j).Δ
  accepted : ¬ Rejected P f g (R.x k) (R.s k) (R.B k) (R.ν k) (R.d k)
  x_next : R.x (k + 1) = R.x k + (R.d k).fst
  s_next : ∀ i, R.s (k + 1) i = max (R.s k i + (R.d k).snd i) (-(g (R.x (k + 1)) i))
  radius_next : R.Δ k ≤ (R.trial (k + 1) 0).Δ

/-- `R` records Algorithm I with data `P`, started at `(x_0, s_0)` with `s_0 > 0` and radius `Δ₀`,
for its iterations `k < N` (`N = ⊤`: the infinite run). -/
structure IsRunUpTo (P : Params n m) (f : E n → ℝ) (g : E n → F m) (R : RunData n m)
    (N : ℕ∞) : Prop where
  s_pos₀ : ∀ i, 0 < R.s 0 i
  radius₀ : (R.trial 0 0).Δ = P.Δ₀
  step : ∀ k : ℕ, (k : ℕ∞) < N → IsStep P f g R k

/-- `R` is an (infinite) run of Algorithm I applied to the barrier problem (2.2) with data `P`. -/
def IsRun (P : Params n m) (f : E n → ℝ) (g : E n → F m) (R : RunData n m) : Prop :=
  IsRunUpTo P f g R ⊤

/-- Assumptions 4.1 for a run of Algorithm I.
(a) `f` and `g` are differentiable on an open convex set `X` containing all the iterates, and
`∇f`, `g`, `A` are Lipschitz continuous on `X`.
(b) `{f_k}` is bounded below and `{∇f_k}`, `{g_k}`, `{A_k}`, `{B_k}` are bounded. -/
structure Assumptions41 (f : E n → ℝ) (g : E n → F m) (R : RunData n m) : Prop where
  domain : ∃ X : Set (E n), IsOpen X ∧ Convex ℝ X ∧ (∀ k, R.x k ∈ X) ∧
    DifferentiableOn ℝ f X ∧ DifferentiableOn ℝ g X ∧
    LipOn X (gradient f) ∧ LipOn X g ∧ LipOn X (A g)
  f_bddBelow : BddBelow (Set.range fun k => f (R.x k))
  grad_bdd : ∃ C, ∀ k, ‖gradient f (R.x k)‖ ≤ C
  g_bdd : ∃ C, ∀ k, ‖g (R.x k)‖ ≤ C
  A_bdd : ∃ C, ∀ k, ‖A g (R.x k)‖ ≤ C
  B_bdd : ∃ C, ∀ k, ‖R.B k‖ ≤ C

end BarrierTR.Global


