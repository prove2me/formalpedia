-- Prove2me | Definitions.Def_MFGLimit_LDP_Equations
-- name    : MFGLimit_LDP_Equations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:36.350996+00:00
-- url     : https://prove2.me/theorems/b772bbea-42dc-4ea2-a941-d3366731b91c
-- title:
--   §2.3–§2.5, §4, §6.1 — Nash system (2.6), master equation (2.8), Assumptions A, B, B′, SDEs (2.7), (4.1), (6.1), b̃ (3.10), Condition 6.3
-- statement:
--   The equations and assumptions of the paper.
--
--   **Nash system (2.6).** Functions $v^{n,i}:[0,T]\times(\mathbb R^d)^n\to\mathbb R$, $i=1,\dots,n$, continuously differentiable in $t$ and twice continuously differentiable in $\boldsymbol x$, with
--
--   $$\partial_tv^{n,i}+H(x_i,m^n_{\boldsymbol x},D_{x_i}v^{n,i})+\sum_{j\ne i}D_{x_j}v^{n,i}\cdot\hat b(x_j,m^n_{\boldsymbol x},D_{x_j}v^{n,j})+\frac12\sum_{j}\mathrm{Tr}[D^2_{x_j,x_j}v^{n,i}\sigma\sigma^\top]+\frac12\sum_{j,k}\mathrm{Tr}[D^2_{x_j,x_k}v^{n,i}\sigma_0\sigma_0^\top]=0$$
--
--   on $(0,T)\times(\mathbb R^d)^n$ and $v^{n,i}(T,\boldsymbol x)=g(x_i,m^n_{\boldsymbol x})$.
--
--   **Master equation (2.8).** $U(t,x,m)$ with
--   $$0=\partial_tU+H(x,m,D_xU)+\tfrac12\mathrm{Tr}[(\sigma\sigma^\top+\sigma_0\sigma_0^\top)D^2_xU]+\int\hat b(v,m,D_xU(t,v,m))\cdot D_mU(t,x,m,v)\,dm(v)+\tfrac12\int\mathrm{Tr}[(\sigma\sigma^\top+\sigma_0\sigma_0^\top)D_vD_mU]\,dm(v)+\tfrac12\iint\mathrm{Tr}[\sigma_0\sigma_0^\top D^2_mU]\,dm(v)dm(v')+\int\mathrm{Tr}[\sigma_0\sigma_0^\top D_xD_mU]\,dm(v)$$
--   and $U(T,x,m)=g(x,m)$.
--
--   **Assumption A.** (1) $p^*\in[1,2]$, $\hat\alpha(x,m,y)$ minimizes $a\mapsto b(x,m,a)\cdot y+f(x,m,a)$, and $|\hat b(x,m,y)-\hat b(x',m',y')|\le C(|x-x'|+\mathcal W_{p^*}(m,m')+|y-y'|)$; (2) $\sigma$ is non-degenerate; (3) $\mu_0\in\mathcal P^{p'}(\mathbb R^d)$ for some $p'>4$; (4) for each $n$ the Nash system has a classical solution with $|D_{x_j}v^{n,i}|\le L_{n,i,j}(1+|\boldsymbol x|)$, $|v^{n,i}|\le L_{n,i}(1+|\boldsymbol x|^2)$; (5) the master equation has a classical solution $U$ on $[0,T]\times\mathbb R^d\times\mathcal P^2(\mathbb R^d)$ with continuous $\partial_tU,D_xU,D_mU,D^2_xU,D_vD_mU,D_xD_mU,D^2_mU$, bounded $D_xU,D_mU,D_xD_mU,D^2_mU$, and $D_xU$ Lipschitz in $(x,m)$ uniformly in $t$ for $\mathcal W_{p^*}$ on $\mathcal P^{p^*}(\mathbb R^d)$.
--
--   **Assumption B:** $|\hat f(x,m,y)-\hat f(x,m,y')|\le C|y-y'|$. **Assumption B′:** $U$ bounded, $v^{n,i}$ bounded uniformly in $n,i$, and $|\hat f(x,m,y)-\hat f(x,m,y')|\le C(1+|y|+|y'|)|y-y'|$.
--
--   **Particle systems.** The Nash state process (2.7) $dX^i_t=\hat b(X^i_t,m^n_{\boldsymbol X_t},D_{x_i}v^{n,i}(t,\boldsymbol X_t))dt+\sigma dB^i_t+\sigma_0dW_t$; with $\tilde b(t,x,m)=\hat b(x,m,D_xU(t,x,m))$ (3.10), the McKean–Vlasov particle system (4.1) $d\bar X^i_t=\tilde b(t,\bar X^i_t,m^n_{\bar{\boldsymbol X}_t})dt+\sigma dB^i_t+\sigma_0dW_t$; and the general system (6.1) with a drift $\tilde b$. All start from $X^i_0$.
--
--   **Condition 6.3.** (1) $\int e^{\lambda|y|}\mu_0(dy)<\infty$ for every $\lambda>0$ (6.2); (2) $\tilde b:[0,T]\times\mathbb R^d\times\mathcal P^1(\mathbb R^d)\to\mathbb R^d$ is bounded, continuous, and Lipschitz in $(x,m)$ uniformly in time.
--
--   **Formalization Note** Derivatives in $t$, $x$, $v$ are genuine (Fréchet) derivatives; derivatives in $m$ are flat-derivative witnesses. The classical-solution properties of $U$ are required on $\mathcal P^2$ (as A(5) states) and the existence and Lipschitz property of $D_xU$ on $\mathcal P^{p^*}$ (A(5)'s parenthesis), which is where $\tilde b$ is evaluated. Assumption A also records the Borel measurability of $b,f,g$ (§2.3). Solutions of the SDEs are path-valued and adapted, and satisfy the integral equation a.s. for each $t$; the stochastic integrals of the constant matrices are $\sigma(B^i_t-B^i_0)$ and $\sigma_0(W_t-W_0)$.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, pp. 6–9, 13, 15, 25, (2.6)–(2.8), Assumptions A, B, B′, (3.10), (4.1), (6.1), Condition 6.3

import Mathlib
import Definitions.Def_MFGLimit_LDP_Model
import Definitions.Def_MFGLimit_LDP_MeasureDeriv

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLimit.LDP

variable {d d₀ : ℕ} {A : Type*}

/-! ### Derivatives used by the Nash system (2.6) -/

/-- The block gradient `D_{x_j} F(x) ∈ ℝ^d` of `F : (ℝ^d)^n → ℝ`. -/
noncomputable def Dxj {n : ℕ} (F : (Fin n → MFGLimit.Conc.E d) → ℝ) (x : Fin n → MFGLimit.Conc.E d) (j : Fin n) : MFGLimit.Conc.E d :=
  gradient (fun y => F (Function.update x j y)) (x j)

/-- The block Hessian `D²_{x_j, x_k} F(x)`: the array `(∂_{x_j^a} ∂_{x_k^b} F(x))_{a,b}`. -/
noncomputable def blockHess {n : ℕ} (F : (Fin n → MFGLimit.Conc.E d) → ℝ) (x : Fin n → MFGLimit.Conc.E d) (j k : Fin n) :
    Fin d → Fin d → ℝ :=
  fun a b => iteratedFDeriv ℝ 2 F x ![Pi.single j (ebasis a), Pi.single k (ebasis b)]

/-- The Euclidean norm `|x| = ‖x‖_{n,2} = (Σ_i |x_i|²)^{1/2}` of `x ∈ (ℝ^d)^n`. -/
noncomputable def normN2 {n : ℕ} (x : Fin n → MFGLimit.Conc.E d) : ℝ := Real.sqrt (∑ i, ‖x i‖ ^ 2)

/-- The time derivative `∂_t F(t, z)` on `[0, T]` (one-sided at the end points). -/
noncomputable def dtime {X : Type*} (T : ℝ≥0) (F : ℝ≥0 → X → ℝ) (t : ℝ) (z : X) : ℝ :=
  derivWithin (fun s : ℝ => F s.toNNReal z) (Set.Icc 0 (T : ℝ)) t

/-- (2.6), p. 7 and A(4): `(v^{n,i})_{i}` is a classical solution of the `n`-player Nash system:
each `v^{n,i}(t, x)` is continuously differentiable in `t ∈ [0, T]` and twice continuously
differentiable in `x ∈ (ℝ^d)^n`; for `(t, x) ∈ (0, T) × (ℝ^d)^n`,
`∂_t v^{n,i} + H(x_i, m^n_x, D_{x_i} v^{n,i}) + Σ_{j ≠ i} D_{x_j} v^{n,i} · b̂(x_j, m^n_x, D_{x_j} v^{n,j})
 + ½ Σ_j Tr[D²_{x_j,x_j} v^{n,i} σσᵀ] + ½ Σ_{j,k} Tr[D²_{x_j,x_k} v^{n,i} σ₀σ₀ᵀ] = 0`,
and `v^{n,i}(T, x) = g(x_i, m^n_x)`. -/
structure IsNashSystemSolution (M : Model d d₀ A) (T : ℝ≥0) (n : ℕ)
    (v : Fin n → ℝ≥0 → (Fin n → MFGLimit.Conc.E d) → ℝ) : Prop where
  time_diff : ∀ i x, ∀ t ∈ Set.Icc (0 : ℝ) T,
    DifferentiableWithinAt ℝ (fun s : ℝ => v i s.toNNReal x) (Set.Icc 0 (T : ℝ)) t
  time_cont : ∀ i x, ContinuousOn (fun t => dtime T (v i) t x) (Set.Icc 0 (T : ℝ))
  space_C2 : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ContDiff ℝ 2 (v i t)
  pde : ∀ i, ∀ t : ℝ, 0 < t → t < T → ∀ x : Fin n → MFGLimit.Conc.E d,
    dtime T (v i) t x
      + M.H (x i) (empMeas x) (Dxj (v i t.toNNReal) x i)
      + (∑ j ∈ Finset.univ.erase i,
          inner ℝ (Dxj (v i t.toNNReal) x j) (M.bhat (x j) (empMeas x) (Dxj (v j t.toNNReal) x j)))
      + (1 / 2) * ∑ j, trMul (M.σ * M.σ.transpose) (blockHess (v i t.toNNReal) x j j)
      + (1 / 2) * ∑ j, ∑ k, trMul (M.σ₀ * M.σ₀.transpose) (blockHess (v i t.toNNReal) x j k) = 0
  terminal : ∀ i x, v i T x = M.g (x i) (empMeas x)

/-! ### Derivatives used by the master equation (2.8) -/

/-- `D_x U(t, x, m)`, the gradient in `x`. -/
noncomputable def DxU (U : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → ℝ) (t : ℝ≥0) (x : MFGLimit.Conc.E d)
    (m : Measure (MFGLimit.Conc.E d)) : MFGLimit.Conc.E d :=
  gradient (fun y => U t y m) x

/-- `D_m U(t, x, m, v) = D_v (δU/δm)(t, x, m, v)` for a flat derivative `dU = δU/δm`. -/
noncomputable def DmU (dU : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d → ℝ) (t : ℝ≥0) (x : MFGLimit.Conc.E d)
    (m : Measure (MFGLimit.Conc.E d)) (v : MFGLimit.Conc.E d) : MFGLimit.Conc.E d :=
  gradient (dU t x m) v

/-- `D_x D_m U(t, x, m, v)`: the array `(∂_{x_j} (D_m U)_i)_{i,j}`. -/
noncomputable def DxDmU (dU : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d → ℝ) (t : ℝ≥0) (x : MFGLimit.Conc.E d)
    (m : Measure (MFGLimit.Conc.E d)) (v : MFGLimit.Conc.E d) : Fin d → Fin d → ℝ :=
  fun i j => fderiv ℝ (fun y => inner ℝ (gradient (dU t y m) v) (ebasis i)) x (ebasis j)

/-- `D²_m U(t, x, m, v, v') = D²_{v,v'} (δ²U/δm²)(t, x, m, v, v')`: the array
`(∂_{v_i} ∂_{v'_j} d2U)_{i,j}` for a second flat derivative `d2U = δ²U/δm²`. -/
noncomputable def D2mU (d2U : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d → MFGLimit.Conc.E d → ℝ) (t : ℝ≥0) (x : MFGLimit.Conc.E d)
    (m : Measure (MFGLimit.Conc.E d)) (v v' : MFGLimit.Conc.E d) : Fin d → Fin d → ℝ :=
  fun i j => fderiv ℝ (fun w => fderiv ℝ (fun w' => d2U t x m w w') v' (ebasis j)) v (ebasis i)

/-- (2.8), p. 7 and A(5), p. 9, for given flat derivatives `dU = δU/δm` and `d2U = δ²U/δm²`
(§2.2 with `q = 2`): the classical-solution properties on `[0, T] × ℝ^d × P_2(ℝ^d)`
(continuous `∂_tU, D_xU, D_mU, D²_xU, D_vD_mU, D_xD_mU, D²_mU`, jointly in all variables with
`W_2` in the measure; `D_xU, D_mU, D_xD_mU, D²_mU` bounded), the equation (2.8) on
`(0, T) × ℝ^d × P_2(ℝ^d)`, the terminal condition, and: `D_xU(t, x, m)` exists for
`m ∈ P_{p*}(ℝ^d)` and is Lipschitz in `(x, m)` for `W_{p*}`, uniformly in `t`. -/
structure MasterProps (M : Model d d₀ A) (T : ℝ≥0) (U : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → ℝ)
    (dU : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d → ℝ)
    (d2U : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d → MFGLimit.Conc.E d → ℝ) : Prop where
  flat1 : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x, IsFlatDeriv 2 (U t x) (dU t x)
  flat2 : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x v,
    IsFlatDeriv 2 (fun m => dU t x m v) (fun m v' => d2U t x m v v')
  time_diff : ∀ x m, MFGLimit.Conc.IsPp 2 m → ∀ t ∈ Set.Icc (0 : ℝ) T,
    DifferentiableWithinAt ℝ (fun s : ℝ => U s.toNNReal x m) (Set.Icc 0 (T : ℝ)) t
  x_C2 : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ m, MFGLimit.Conc.IsPp 2 m → ContDiff ℝ 2 (fun y => U t y m)
  v_C2 : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x m, MFGLimit.Conc.IsPp 2 m → ContDiff ℝ 2 (dU t x m)
  xv_diff : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ m v, MFGLimit.Conc.IsPp 2 m →
    Differentiable ℝ (fun y => gradient (dU t y m) v)
  vv_C2 : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x m, MFGLimit.Conc.IsPp 2 m →
    ContDiff ℝ 2 (fun p : MFGLimit.Conc.E d × MFGLimit.Conc.E d => d2U t x m p.1 p.2)
  cont_dt : ContOnPq 2 T (fun t x m (_ : Unit) => dtime T (fun s z => U s z.1 z.2) t (x, m))
  cont_Dx : ContOnPq 2 T (fun t x m (_ : Unit) => DxU U t x m)
  cont_D2x : ContOnPq 2 T (fun t x m (_ : Unit) => hessE (fun y => U t y m) x)
  cont_Dm : ContOnPq 2 T (fun t x m v => DmU dU t x m v)
  cont_DvDm : ContOnPq 2 T (fun t x m v => hessE (dU t x m) v)
  cont_DxDm : ContOnPq 2 T (fun t x m v => DxDmU dU t x m v)
  cont_D2m : ContOnPq 2 T (fun t x m (w : MFGLimit.Conc.E d × MFGLimit.Conc.E d) => D2mU d2U t x m w.1 w.2)
  bdd_Dx : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x m, MFGLimit.Conc.IsPp 2 m → ‖DxU U t x m‖ ≤ C
  bdd_Dm : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x m v, MFGLimit.Conc.IsPp 2 m → ‖DmU dU t x m v‖ ≤ C
  bdd_DxDm : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x m v, MFGLimit.Conc.IsPp 2 m →
    ∀ i j, |DxDmU dU t x m v i j| ≤ C
  bdd_D2m : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x m v v', MFGLimit.Conc.IsPp 2 m →
    ∀ i j, |D2mU d2U t x m v v' i j| ≤ C
  Dx_exists : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x m, MFGLimit.Conc.IsPp M.pStar m →
    DifferentiableAt ℝ (fun y => U t y m) x
  Dx_lip : ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x x' m m', MFGLimit.Conc.IsPp M.pStar m → MFGLimit.Conc.IsPp M.pStar m' →
    ‖DxU U t x m - DxU U t x' m'‖ ≤ L * (‖x - x'‖ + (Wp M.pStar m m').toReal)
  pde : ∀ t : ℝ, 0 < t → t < T → ∀ x m, MFGLimit.Conc.IsPp 2 m →
    dtime T (fun s z => U s z.1 z.2) t (x, m)
      + M.H x m (DxU U t.toNNReal x m)
      + (1 / 2) * trMul (M.σ * M.σ.transpose + M.σ₀ * M.σ₀.transpose) (hessE (fun y => U t.toNNReal y m) x)
      + (∫ v, inner ℝ (M.bhat v m (DxU U t.toNNReal v m)) (DmU dU t.toNNReal x m v) ∂m)
      + (1 / 2) * (∫ v, trMul (M.σ * M.σ.transpose + M.σ₀ * M.σ₀.transpose) (hessE (dU t.toNNReal x m) v) ∂m)
      + (1 / 2) * (∫ v, ∫ v', trMul (M.σ₀ * M.σ₀.transpose) (D2mU d2U t.toNNReal x m v v') ∂m ∂m)
      + (∫ v, trMul (M.σ₀ * M.σ₀.transpose) (DxDmU dU t.toNNReal x m v) ∂m) = 0
  terminal : ∀ x m, MFGLimit.Conc.IsPp 2 m → U T x m = M.g x m

/-- A(5): `U` is a classical solution of the master equation (2.8): there are flat derivatives
`δU/δm`, `δ²U/δm²` with which `MasterProps` holds. -/
def IsMasterSolution (M : Model d d₀ A) (T : ℝ≥0) (U : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → ℝ) : Prop :=
  ∃ dU d2U, MasterProps M T U dU d2U

/-! ### Assumptions A, B, B′ (§2.5, pp. 8–9) -/

/-- Assumption A, for the Nash-system solutions `v n` and the master-equation solution `U` used
to build the equilibrium, together with the Borel measurability of `b, f, g` (§2.3):
1. `p* ∈ [1, 2]`, `α̂(x, m, y)` minimizes `a ↦ b(x, m, a)·y + f(x, m, a)` for `m ∈ P_{p*}`, and `b̂`
   is Lipschitz in `(x, m, y)` (metric `W_{p*}` in `m`);
2. `σ` is non-degenerate;
3. `μ₀ ∈ P_{p'}(ℝ^d)` for some `p' > 4` (the i.i.d. property is part of `IsSetup`);
4. each `(v^{n,i})_i` is a classical solution of (2.6) with `|D_{x_j} v^{n,i}| ≤ L_{n,i,j}(1 + |x|)`
   and `|v^{n,i}| ≤ L_{n,i}(1 + |x|²)` on `[0, T] × (ℝ^d)^n`;
5. `U` is a classical solution of the master equation (2.8). -/
structure AssumptionA [TopologicalSpace A] [MeasurableSpace A] (M : Model d d₀ A) (T : ℝ≥0)
    (μ₀ : Measure (MFGLimit.Conc.E d)) (v : ∀ n, Fin n → ℝ≥0 → (Fin n → MFGLimit.Conc.E d) → ℝ)
    (U : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → ℝ) : Prop where
  borel_b : Measurable (fun z : MFGLimit.Conc.E d × {m : Measure (MFGLimit.Conc.E d) // MFGLimit.Conc.IsPp M.pStar m} × A =>
    M.b z.1 z.2.1 z.2.2)
  borel_f : Measurable (fun z : MFGLimit.Conc.E d × {m : Measure (MFGLimit.Conc.E d) // MFGLimit.Conc.IsPp M.pStar m} × A =>
    M.f z.1 z.2.1 z.2.2)
  borel_g : Measurable (fun z : MFGLimit.Conc.E d × {m : Measure (MFGLimit.Conc.E d) // MFGLimit.Conc.IsPp M.pStar m} => M.g z.1 z.2)
  pStar_ge : 1 ≤ M.pStar
  pStar_le : M.pStar ≤ 2
  minimizer : ∀ x m y, MFGLimit.Conc.IsPp M.pStar m → ∀ a,
    inner ℝ (M.b x m (M.αhat x m y)) y + M.f x m (M.αhat x m y) ≤ inner ℝ (M.b x m a) y + M.f x m a
  bhat_lip : ∃ C : ℝ, ∀ x x' y y' m m', MFGLimit.Conc.IsPp M.pStar m → MFGLimit.Conc.IsPp M.pStar m' →
    ‖M.bhat x m y - M.bhat x' m' y'‖ ≤ C * (‖x - x'‖ + (Wp M.pStar m m').toReal + ‖y - y'‖)
  σ_nondeg : M.σ.det ≠ 0
  μ₀_moment : ∃ p' > (4 : ℝ), MFGLimit.Conc.IsPp p' μ₀
  nash : ∀ n, IsNashSystemSolution M T n (v n)
  nash_grad_growth : ∀ n (i j : Fin n), ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x,
    ‖Dxj (v n i t) x j‖ ≤ L * (1 + normN2 x)
  nash_growth : ∀ n (i : Fin n), ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x,
    |v n i t x| ≤ L * (1 + normN2 x ^ 2)
  master : IsMasterSolution M T U

/-- Assumption B: `f̂(x, m, y)` is Lipschitz in `y`, uniformly in `(x, m)`. -/
def AssumptionB (M : Model d d₀ A) : Prop :=
  ∃ C : ℝ, ∀ x y y' m, MFGLimit.Conc.IsPp M.pStar m → |M.fhat x m y - M.fhat x m y'| ≤ C * ‖y - y'‖

/-- Assumption B′: (1) `U` is uniformly bounded; (2) the Nash-system solutions are bounded
uniformly in `n` and `i`; (3) `f̂` is locally Lipschitz in `y` with quadratic growth,
`|f̂(x, m, y) − f̂(x, m, y')| ≤ C(1 + |y| + |y'|)|y − y'|`. -/
def AssumptionB' (M : Model d d₀ A) (T : ℝ≥0) (v : ∀ n, Fin n → ℝ≥0 → (Fin n → MFGLimit.Conc.E d) → ℝ)
    (U : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → ℝ) : Prop :=
  (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x m, MFGLimit.Conc.IsPp 2 m → |U t x m| ≤ C) ∧
    (∃ C : ℝ, ∀ n (i : Fin n), ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x, |v n i t x| ≤ C) ∧
    (∃ C : ℝ, ∀ x y y' m, MFGLimit.Conc.IsPp M.pStar m →
      |M.fhat x m y - M.fhat x m y'| ≤ C * (1 + ‖y‖ + ‖y'‖) * ‖y - y'‖)

/-! ### The particle systems -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A path-valued solution `X = (X^1, …, X^n)` of the system
`dX^i_t = drift_i(t, X_t) dt + σ dB^i_t + σ₀ dW_t`, `X^i_0 = X₀^i`, on `[0, T]` (players indexed
from `0`): each `X^i` is `𝔽`-adapted, and for every `t ∈ [0, T]`, almost surely the drift is
integrable on `[0, t]` and `X^i_t = X^i_0 + ∫₀ᵗ drift_i(s, X_s) ds + σ(B^i_t − B^i_0) + σ₀(W_t − W_0)`
(the stochastic integrals of the constant matrices `σ`, `σ₀`). -/
def IsSystem (T : ℝ≥0) (𝔽 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (W : ℝ≥0 → Ω → Fin d₀ → ℝ) (B : ℕ → ℝ≥0 → Ω → Fin d → ℝ) (X₀ : ℕ → Ω → MFGLimit.Conc.E d) {n : ℕ}
    (drift : Fin n → ℝ → (Fin n → MFGLimit.Conc.E d) → MFGLimit.Conc.E d) (X : Fin n → Ω → CPath d T) : Prop :=
  (∀ i, ∀ t : Set.Icc (0 : ℝ≥0) T, Measurable[𝔽 t] (fun ω => X i ω t)) ∧
    ∀ i, ∀ t : Set.Icc (0 : ℝ≥0) T, ∀ᵐ ω ∂P,
      IntegrableOn (fun s : ℝ => drift i s (fun j => (X j ω).atR s)) (Set.Icc 0 (t : ℝ)) ∧
      X i ω t = X₀ i.val ω + (∫ s in Set.Icc (0 : ℝ) t, drift i s (fun j => (X j ω).atR s))
        + matVec σ (toE (B i.val t ω) - toE (B i.val 0 ω)) + matVec σ₀ (toE (W t ω) - toE (W 0 ω))

/-- (2.7): the in-equilibrium state process of the `n`-player game,
`dX^i_t = b̂(X^i_t, m^n_{X_t}, D_{x_i} v^{n,i}(t, X_t)) dt + σ dB^i_t + σ₀ dW_t`, `X^i_0 = X₀^i`. -/
def IsNashState (M : Model d d₀ A) (T : ℝ≥0) (𝔽 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (W : ℝ≥0 → Ω → Fin d₀ → ℝ) (B : ℕ → ℝ≥0 → Ω → Fin d → ℝ) (X₀ : ℕ → Ω → MFGLimit.Conc.E d) {n : ℕ}
    (v : Fin n → ℝ≥0 → (Fin n → MFGLimit.Conc.E d) → ℝ) (X : Fin n → Ω → CPath d T) : Prop :=
  IsSystem T 𝔽 P M.σ M.σ₀ W B X₀
    (fun i s x => M.bhat (x i) (empMeas x) (Dxj (v i s.toNNReal) x i)) X

/-- The general weakly interacting system (6.1),
`dX̃^i_t = b̃(t, X̃^i_t, m^n_{X̃_t}) dt + σ dB^i_t + σ₀ dW_t`, `X̃^i_0 = X₀^i`. -/
def IsInteractingSystem (T : ℝ≥0) (𝔽 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (W : ℝ≥0 → Ω → Fin d₀ → ℝ) (B : ℕ → ℝ≥0 → Ω → Fin d → ℝ) (X₀ : ℕ → Ω → MFGLimit.Conc.E d)
    (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d) {n : ℕ} (X : Fin n → Ω → CPath d T) : Prop :=
  IsSystem T 𝔽 P σ σ₀ W B X₀ (fun i s x => btil s.toNNReal (x i) (empMeas x)) X

/-- The drift `b̃(t, x, m) := b̂(x, m, D_xU(t, x, m))` (3.10). -/
noncomputable def btilOf (M : Model d d₀ A) (U : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → ℝ) (t : ℝ≥0)
    (x : MFGLimit.Conc.E d) (m : Measure (MFGLimit.Conc.E d)) : MFGLimit.Conc.E d :=
  M.bhat x m (DxU U t x m)

/-- The McKean–Vlasov particle system (4.1),
`dX̄^i_t = b̂(X̄^i_t, m^n_{X̄_t}, D_xU(t, X̄^i_t, m^n_{X̄_t})) dt + σ dB^i_t + σ₀ dW_t`, `X̄^i_0 = X₀^i`. -/
def IsMVParticle (M : Model d d₀ A) (T : ℝ≥0) (𝔽 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (W : ℝ≥0 → Ω → Fin d₀ → ℝ) (B : ℕ → ℝ≥0 → Ω → Fin d → ℝ) (X₀ : ℕ → Ω → MFGLimit.Conc.E d)
    (U : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → ℝ) {n : ℕ} (X : Fin n → Ω → CPath d T) : Prop :=
  IsInteractingSystem T 𝔽 P M.σ M.σ₀ W B X₀ (btilOf M U) X

/-! ### Condition 6.3 (p. 25) -/

/-- (6.2): `∫ exp(λ|y|) μ₀(dy) < ∞` for every `λ > 0`. -/
def ExpMoments (μ₀ : Measure (MFGLimit.Conc.E d)) : Prop :=
  ∀ lam : ℝ, 0 < lam → ∫⁻ y, ENNReal.ofReal (Real.exp (lam * ‖y‖)) ∂μ₀ < ⊤

/-- Condition 6.3(2): the drift `b̃ : [0, T] × ℝ^d × P_1(ℝ^d) → ℝ^d` is bounded, continuous (metric
`W_1` in the measure), and Lipschitz in `(x, m)` uniformly in time. -/
def DriftCond (T : ℝ≥0) (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d) : Prop :=
  (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x m, MFGLimit.Conc.IsPp 1 m → ‖btil t x m‖ ≤ C) ∧
    ContOnPq 1 T (fun t x m (_ : Unit) => btil t x m) ∧
    ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x x' m m', MFGLimit.Conc.IsPp 1 m → MFGLimit.Conc.IsPp 1 m' →
      ‖btil t x m - btil t x' m'‖ ≤ L * (‖x - x'‖ + (Wp 1 m m').toReal)

end MFGLimit.LDP


