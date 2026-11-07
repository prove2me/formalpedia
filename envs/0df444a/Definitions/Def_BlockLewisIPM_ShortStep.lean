-- Prove2me | Definitions.Def_BlockLewisIPM_ShortStep
-- name    : BlockLewisIPM_ShortStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:51:12.961212+00:00
-- url     : https://prove2.me/theorems/4d63b57d-372a-4bf5-9d11-744706c67d27
-- title:
--   Valid sampling, the short step of Algorithm 1, the sampling law of Lemma 38, the extended program and repeated calls
-- statement:
--   A random block scalar $R=(R_i)_i$ is a **valid sampling** associated with a vector $\delta\in\mathbb R^n$ (Definition 19) if $\mathbb E[R_i]=1$, $\operatorname{Var}[R_i\|\delta_i\|_2]\le\beta^2\sqrt{d/m}\,\|\delta_i\|_2\|\delta\|_2/C_{\mathrm{Var}}^2$, $\operatorname{Var}[R_i]\le2\bar\tau_i^{-1}$, $\mathbb E[R_iR_j]\le2$ for $i\ne j$, and with high probability
--
--   $$\|R\delta-\delta\|_{2,\infty}\le\beta\sqrt{d/m}\,\frac{\|\delta\|_2}{C_{\mathrm{Var}}^2},\qquad A^\top\nabla^2\Phi(\bar x)^{-1/2}\bar T^{-1/2}R\bar T^{-1/2}\nabla^2\Phi(\bar x)^{-1/2}A\approx_\alpha A^\top\bar T^{-1}\nabla^2\Phi(\bar x)^{-1}A .$$
--
--   **One call of Algorithm 1** takes $(x,s,\rho,\rho^{(\mathrm{new})})$ with $|\rho^{(\mathrm{new})}-\rho|\le r\rho$ for $r=\alpha\beta/(4C_{\mathrm{norm}}\sqrt d)$, approximations $(\bar x,\bar\tau)$, $\bar\mu$, a dual vector $g=-\beta\nabla^{\mathrm{loc}}_\mu\Psi(\bar\mu,\bar x)^{\flat(\bar\tau)}$, $\bar H\approx_\alpha H=A^\top\bar T^{-1}\nabla^2\Phi(\bar x)^{-1}A$, and sets
--
--   $$\delta_1=\bar T^{-1}\nabla^2\Phi(\bar x)^{-1/2}A\bar H^{-1}A^\top\nabla^2\Phi(\bar x)^{-1/2}g,\quad \delta_2=\bar T^{-1}\nabla^2\Phi(\bar x)^{-1/2}A\bar H^{-1}(A^\top x-b),$$
--
--   $$x^{(\mathrm{new})}=x+\nabla^2\Phi(\bar x)^{-1/2}\bigl(g-R(\delta_1+\delta_2)\bigr),\qquad s^{(\mathrm{new})}=s+\rho\bar T\nabla^2\Phi(\bar x)^{1/2}\delta_1 .$$
--
--   The file also defines the sampling probabilities of Lemma 38, the extended program (28) of Lemma 49 on $K\times[0,2]$, and a **run**: repeated calls in which each input may depend on the earlier samples.
--
--   **Formalization Note** The bars of Definition 19's item 5 do not print on p.15; they are read at $\bar x,\bar\tau$, as Algorithm 1 uses them. `GoodStep` is the event of the two high-probability items, and expectations in the milestones are conditional on it, since $x^{(\mathrm{new})}\in\operatorname{int}K$ is only known there. At $\delta=0$ the ratio $\|\delta_i\|^2/\|\delta\|^2$ of Lemma 38 is read as $1/m$.
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Definition 19, p.15; Algorithm 1, p.16; Lemma 38, p.37; Lemma 49, p.44; Lemmas 51–52, p.45

import Mathlib
import Definitions.Def_BlockLewisIPM_Potential

namespace BlockLewisIPM

/-!
# Valid sampling, the short step and its repeated calls

Zhang, Wright, *A Fast Lewis-weight Interior Point Method for Linear Optimization over
Product-Domain* (manuscript, sha256 66072000…), Definition 19, p.15, Algorithm 1, p.16, Lemma 38,
p.37, and the setting of Lemma 51, p.45.

**Formalization Note.**
* `δ` of Definition 19 is a free vector, unrelated to the accuracy of Theorem 54.
* The bars of Definition 19 item 5 and of `T` do not print on p.15. In use the matrices are at `x̄`
  and `τ̄` (Algorithm 1, line 13), so they are read so here (reading of the mission).
* Definition 19 holds for a law `μ` on any sample space. `R` is the scalar per block `R_i`. `MemLp 2`
  is explicit, since Mathlib's variance of a non-`L²` function is `0`. Items 4, 5 are "w.h.p.".
* `StepData` is the input of Algorithm 1, which leaves `x̄, τ̄, µ̄, H̄` and the maximizer free, and
  `xNew`, `sNew` are its output as functions of the sample of `R`.
* `IsStepCall` is one call as analysed in §4: `(x, s, ρ)` is `ϵ`-centered ("We will suppose (x, s, ρ)
  is ϵ-central for the rest of the section", p.22), the assertion of line 4 holds with the `r` of
  Lemma 20, and lines 5, 7, 8, 9 and 13 hold.
* `GoodStep` is the event of items 4 and 5. Out of `int K` the barrier terms have junk values, and
  `x^(new) ∈ int K` only on that event, so the expectations of the milestones are read conditionally
  on it (mission reading): the law of `R` under `ProbabilityTheory.cond`.
* The sampling law of Lemma 38 is on the finite space `Fin N → ι`. `sampleRatio` is `1/m` at `δ = 0`,
  where the printed ratio is `0/0`.
* `Run` is the sequence of Lemma 51 ("repeatedly calling Algorithm 1") as a tree over the histories
  of samples: each history gives the next input, chosen adaptively, and the law of the next `R`.
  `Realizes` says a process has these conditional laws.
-/

open Matrix MeasureTheory ProbabilityTheory

/-- The entrywise expectation of a random vector. -/
noncomputable def expectVec {Ω a : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (f : Ω → a → ℝ) :
    a → ℝ :=
  fun j => ∫ ω, f ω j ∂ν

/-- The entrywise expectation of a random matrix. -/
noncomputable def expectMat {Ω a : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (f : Ω → Matrix a a ℝ) : Matrix a a ℝ :=
  Matrix.of fun i j => ∫ ω, f ω i j ∂ν

namespace Instance

variable {ι : Type} [Fintype ι] [DecidableEq ι] (I : Instance ι)

/-- The event of Definition 19 item 4 for the sample `r` and the vector `δ`. -/
def MaximumEvent (P : Params) (Cvar : ℝ) (δ : I.Vec) (r : ι → ℝ) : Prop :=
  blockSupNorm (diagG (dim := I.dim) r *ᵥ δ - δ) ≤
    P.β * Real.sqrt ((I.d : ℝ) / P.m) * eNorm δ / Cvar ^ 2

/-- The event of Definition 19 item 5 for `r`, at accuracy `γ`, at `x̄` and `τ̄`. -/
def SpectralEvent (γ : ℝ) (xb : I.Vec) (τb r : ι → ℝ) : Prop :=
  ApproxEq γ
    (I.Aᵀ * (I.hessInvSqrt xb * diagG (dim := I.dim) (fun i => (Real.sqrt (τb i))⁻¹) *
      diagG (dim := I.dim) r * diagG (dim := I.dim) (fun i => (Real.sqrt (τb i))⁻¹) *
        I.hessInvSqrt xb * I.A))
    (I.schur τb xb)

/-- `R` is a valid sampling block-diagonal matrix associated with `δ` (Definition 19, p.15), at `x̄`
and `τ̄`, for the law `μ`. -/
structure IsValidSampling (P : Params) (Cvar : ℝ) (xb : I.Vec) (τb : ι → ℝ) (δ : I.Vec)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (R : Ω → ι → ℝ) : Prop where
  cvar_ge : P.Cnorm ≤ Cvar
  measurable : ∀ i, Measurable fun ω => R ω i
  memLp : ∀ i, MemLp (fun ω => R ω i) 2 μ
  expectation : ∀ i, ∫ ω, R ω i ∂μ = 1
  variance_block : ∀ i, Var[fun ω => R ω i * eNorm (block δ i); μ] ≤
    P.β ^ 2 * Real.sqrt ((I.d : ℝ) / P.m) * (eNorm (block δ i) * eNorm δ) / Cvar ^ 2
  variance : ∀ i, Var[fun ω => R ω i; μ] ≤ 2 * (τb i)⁻¹
  covariance : ∀ i j, i ≠ j → ∫ ω, R ω i * R ω j ∂μ ≤ 2
  maximum : Whp μ P.m fun ω => I.MaximumEvent P Cvar δ (R ω)
  spectral : Whp μ P.m fun ω => I.SpectralEvent P.α xb τb (R ω)

/-- The input of Algorithm 1 (p.16): `x, s, ρ, ρ^(new)` and the choices `x̄, τ̄, µ̄, g, H̄`. -/
structure StepData where
  /-- `x`. -/
  x : I.Vec
  /-- `s`. -/
  s : I.Vec
  /-- `ρ`. -/
  ρ : ℝ
  /-- `ρ^(new)`. -/
  ρnew : ℝ
  /-- `x̄`. -/
  xb : I.Vec
  /-- `τ̄`. -/
  τb : ι → ℝ
  /-- `µ̄`. -/
  μb : I.Vec
  /-- `g`. -/
  g : I.Vec
  /-- `H̄`. -/
  Hb : Matrix (Fin I.d) (Fin I.d) ℝ

variable {I}

namespace StepData

variable (D : I.StepData)

/-- `H = A⊤T̄⁻¹∇²Φ(x̄)⁻¹A` (Algorithm 1, line 9). -/
noncomputable def H : Matrix (Fin I.d) (Fin I.d) ℝ := I.schur D.τb D.xb

/-- `δ₁ = T̄⁻¹∇²Φ(x̄)^{-1/2} A H̄⁻¹ A⊤ ∇²Φ(x̄)^{-1/2} g` (Algorithm 1, line 10). -/
noncomputable def δ₁ : I.Vec :=
  (diagG (dim := I.dim) (fun i => (D.τb i)⁻¹) * I.hessInvSqrt D.xb * I.A * D.Hb⁻¹ * I.Aᵀ *
    I.hessInvSqrt D.xb) *ᵥ D.g

/-- `δ₂ = T̄⁻¹∇²Φ(x̄)^{-1/2} A H̄⁻¹ (A⊤x - b)` (Algorithm 1, line 11). -/
noncomputable def δ₂ : I.Vec :=
  (diagG (dim := I.dim) (fun i => (D.τb i)⁻¹) * I.hessInvSqrt D.xb * I.A * D.Hb⁻¹) *ᵥ
    (I.Aᵀ *ᵥ D.x - I.b)

/-- `δ_r = δ₁ + δ₂` (Algorithm 1, line 12). -/
noncomputable def δr : I.Vec := D.δ₁ + D.δ₂

/-- `x^(new) = x + ∇²Φ(x̄)^{-1/2}(g - R δ_r)` for the sample `r` of `R` (lines 14, 16). -/
noncomputable def xNew (r : ι → ℝ) : I.Vec :=
  D.x + I.hessInvSqrt D.xb *ᵥ (D.g - diagG (dim := I.dim) r *ᵥ D.δr)

/-- `s^(new) = s + ρ T̄ ∇²Φ(x̄)^{1/2} δ₁` (lines 15, 16). -/
noncomputable def sNew : I.Vec :=
  D.s + D.ρ • ((diagG (dim := I.dim) D.τb * I.hessSqrt D.xb) *ᵥ D.δ₁)

/-- `µ^(new) = µ(x^(new), s^(new), ρ^(new))` for the sample `r`. -/
noncomputable def muNew (P : Params) (r : ι → ℝ) : I.Vec :=
  I.mu P (D.xNew r) D.sNew D.ρnew

/-- `τ^(new) = τ(x^(new))` for the sample `r`. -/
noncomputable def tauNew (P : Params) (r : ι → ℝ) : ι → ℝ := I.tau P (D.xNew r)

/-- The event of Definition 19 items 4 and 5 for the sample `r`. -/
def GoodStep (P : Params) (Cvar : ℝ) (r : ι → ℝ) : Prop :=
  I.MaximumEvent P Cvar D.δr r ∧ I.SpectralEvent P.α D.xb D.τb r

end StepData

/-- One call of Algorithm 1 at an `ϵ`-centered triplet with `ϵ` of Algorithm 1 (§4.2, p.22), with
sampling law `μ` and `R`: lines 4, 5, 7, 8, 9 and 13. -/
structure IsStepCall (P : Params) (Cvar : ℝ) (D : I.StepData) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : Ω → ι → ℝ) : Prop where
  centered : I.IsCentered P P.ϵ D.x D.s D.ρ
  assertion : |D.ρnew - D.ρ| ≤ P.r I.d * D.ρ
  approx : I.IsApprox P P.α D.x D.xb D.τb
  mu_approx : I.IsMuApprox (10 * P.α) D.x (I.mu P D.x D.s D.ρ) D.μb
  flat : ∃ h : I.Vec, IsFlat P.Cnorm D.τb (I.gradLoc P.lam D.μb D.xb) h ∧ D.g = -P.β • h
  H_approx : ApproxEq P.α D.Hb D.H
  valid : I.IsValidSampling P Cvar D.xb D.τb D.δr μ R

/-- The law of `R` conditional on the good event of the step. -/
noncomputable def stepLaw (P : Params) (Cvar : ℝ) (D : I.StepData) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : Ω → ι → ℝ) : Measure Ω :=
  ProbabilityTheory.cond μ {ω | D.GoodStep P Cvar (R ω)}

/-! ### Lemma 38 -/

/-- The ratio `‖δ_i‖²/‖δ‖²` of Lemma 38; `1/m` at `δ = 0`. -/
noncomputable def sampleRatio (δ : I.Vec) (i : ι) : ℝ := by
  classical exact
    if δ = 0 then (Fintype.card ι : ℝ)⁻¹ else eNorm (block δ i) ^ 2 / eNorm δ ^ 2

/-- `K = 2m/√d + ∑ τ_i` of Lemma 38, p.37. -/
noncomputable def sampleK (I : Instance ι) (τ : ι → ℝ) : ℝ :=
  2 * Fintype.card ι / Real.sqrt I.d + ∑ i, τ i

/-- `p_i = (m/(K√d)) (‖δ_i‖²/‖δ‖² + 1/m) + τ_i/K` of Lemma 38, p.37. -/
noncomputable def sampleP (δ : I.Vec) (τ : ι → ℝ) (i : ι) : ℝ :=
  (Fintype.card ι : ℝ) / (sampleK I τ * Real.sqrt I.d) *
      (sampleRatio δ i + (Fintype.card ι : ℝ)⁻¹) + τ i / sampleK I τ

/-- The sample `R_i = (1/N) ∑_j (X^(j))_i` of Lemma 38, where `X^(j) = e_{idx j} / p_{idx j}`. -/
noncomputable def sampleR {N : ℕ} (p : ι → ℝ) (idx : Fin N → ι) (i : ι) : ℝ :=
  (1 / (N : ℝ)) * ∑ j, if idx j = i then (p i)⁻¹ else 0

/-- The law of `N` i.i.d. draws from `p`, on `Fin N → ι` with the full σ-algebra. -/
noncomputable def sampleLaw {N : ℕ} (p : ι → ℝ) : @Measure (Fin N → ι) ⊤ :=
  letI : MeasurableSpace (Fin N → ι) := ⊤
  Measure.sum fun idx => ENNReal.ofReal (∏ j, p (idx j)) • Measure.dirac idx

/-- The block leverage `σ_i(T^{-1/2}∇²Φ(x̄)^{-1/2}A)` (p.10). -/
noncomputable def blockLeverage (I : Instance ι) (τ : ι → ℝ) (xb : I.Vec) (i : ι) : ℝ :=
  blockTrace (projMat
    (diagG (dim := I.dim) (fun i => (Real.sqrt (τ i))⁻¹) * I.hessInvSqrt xb * I.A)) i

/-! ### The extended program of Lemma 49 -/

/-- The block sizes of `K × [0, 2]`. -/
def extDim (dim : ι → ℕ) : Option ι → ℕ
  | none => 1
  | some i => dim i

/-- The vector `[v; t]` of the extended program. -/
def extVec {dim : ι → ℕ} (v : BIdx dim → ℝ) (t : ℝ) : BIdx (extDim dim) → ℝ
  | ⟨none, _⟩ => t
  | ⟨some i, l⟩ => v ⟨i, l⟩

/-- The barrier `-h(z) = -log(z) - log(2 - z)` of Lemma 49, on `ℝ¹`. -/
noncomputable def intervalBarrier (z : Eu 1) : ℝ :=
  -(Real.log (z 0) + Real.log (2 - z 0))

/-- The extended program (28) of Lemma 49, p.44, for `x^(init)`, `L`, `R` and the accuracy `δ`:
`Ã = [A; b - A⊤x^(init)]`, `b̃ = b`, `c̃ = [c; LR/δ]`, the set `K × [0, 2]` and the barrier
`Φ̃([x, z]) = ∑ ϕ_i(x_i) - h(z)`. -/
noncomputable def extended (I : Instance ι) (xinit : I.Vec) (L Rad δ : ℝ) : Instance (Option ι) where
  dim := extDim I.dim
  d := I.d
  A := fun j k => match j with
    | ⟨none, _⟩ => (I.b - I.Aᵀ *ᵥ xinit) k
    | ⟨some i, l⟩ => I.A ⟨i, l⟩ k
  b := I.b
  c := extVec I.c (L * Rad / δ)
  K := fun o => match o with
    | none => {z : Eu 1 | 0 ≤ z 0 ∧ z 0 ≤ 2}
    | some i => I.K i
  φ := fun o => match o with
    | none => intervalBarrier
    | some i => I.φ i

/-! ### Repeated calls -/

/-- The samples drawn before step `k`. -/
abbrev History (ι : Type) (k : ℕ) := Fin k → ι → ℝ

/-- The sequence of Lemma 51 on the tree of histories: `step k h` is the input of call `k` after the
history `h`, and `law k h` is the law of its `R`. -/
structure Run (I : Instance ι) where
  /-- The input of call `k`. -/
  step : ∀ k, History ι k → I.StepData
  /-- The law of the sample of call `k`. -/
  law : ∀ k, History ι k → Measure (ι → ℝ)

/-- `U` is a run of repeated calls of Algorithm 1: each call's output is the next call's input, and
at every `ϵ`-centered point the call is as in `IsStepCall`. -/
structure IsRun (P : Params) (Cvar : ℝ) (U : Run I) : Prop where
  next_x : ∀ k h r, (U.step (k + 1) (Fin.snoc (α := fun _ => ι → ℝ) h r)).x = (U.step k h).xNew r
  next_s : ∀ k h r, (U.step (k + 1) (Fin.snoc (α := fun _ => ι → ℝ) h r)).s = (U.step k h).sNew
  next_ρ : ∀ k h r, (U.step (k + 1) (Fin.snoc (α := fun _ => ι → ℝ) h r)).ρ = (U.step k h).ρnew
  call : ∀ k h, I.IsCentered P P.ϵ (U.step k h).x (U.step k h).s (U.step k h).ρ →
    IsProbabilityMeasure (U.law k h) ∧ IsStepCall P Cvar (U.step k h) (U.law k h) id

/-- The samples before step `k` of a process `R`. -/
def histOf {Ω : Type*} (R : ℕ → Ω → ι → ℝ) (k : ℕ) (ω : Ω) : History ι k := fun l => R l ω

/-- The process `R` on `(Ω, μ)` has the conditional laws of `U`. -/
def Realizes (U : Run I) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (R : ℕ → Ω → ι → ℝ) : Prop :=
  (∀ k, Measurable (R k)) ∧
    ∀ k, (fun h => condDistrib (R k) (histOf R k) μ h) =ᵐ[μ.map (histOf R k)] U.law k

/-- The event that the first `T` calls start at `ϵ`-centered points, the last point is `ϵ`-centered,
and every sample is in the good event of its step. -/
def RunGood (P : Params) (Cvar : ℝ) (U : Run I) {Ω : Type*} (R : ℕ → Ω → ι → ℝ) (T : ℕ) (ω : Ω) :
    Prop :=
  (∀ k ≤ T, let D := U.step k (histOf R k ω); I.IsCentered P P.ϵ D.x D.s D.ρ) ∧
    ∀ k < T, (U.step k (histOf R k ω)).GoodStep P Cvar (R k ω)

/-- The three bullets of Lemma 51, p.45, at `ω`, for `T` calls and the nearby sequence `xh`. -/
def NearbyBullets (P : Params) (αnb : ℝ) (U : Run I) (xh : ∀ k, History ι k → I.Vec) {Ω : Type*}
    (R : ℕ → Ω → ι → ℝ) (T : ℕ) (ω : Ω) : Prop :=
  (∀ k ≤ T,
    let x := (U.step k (histOf R k ω)).x
    let xk := xh k (histOf R k ω)
    blockSupNorm (I.hessSqrt x *ᵥ (xk - x)) ≤ αnb ∧
      blockSupNorm (I.hessSqrt xk *ᵥ (xk - x)) ≤ 2 * αnb) ∧
    ∀ k < T,
      let x := (U.step k (histOf R k ω)).x
      let xk := xh k (histOf R k ω)
      let xk' := xh (k + 1) (histOf R (k + 1) ω)
      mixedBlockNorm P.Cnorm (I.tau P x) (I.hessSqrt xk *ᵥ (xk' - xk)) ≤ 2 * P.β

/-- `W_i = T(x)_i^{1/2-1/p} C̃_i(x)`, the block of `W^(k)` of Lemma 52, p.45. -/
noncomputable def wBlock (P : Params) (I : Instance ι) (x : I.Vec) (i : ι) :
    Matrix (Fin (I.dim i)) (Fin (I.dim i)) ℝ :=
  (I.tau P x i ^ ((1 : ℝ) / 2 - 1 / P.p)) • I.cBlock P.σ x i

/-- The three bullets of Lemma 52, p.45, at `ω`, with hidden constant `K₀`. -/
def StabilityBullets (P : Params) (K₀ αnb : ℝ) (U : Run I) (xh : ∀ k, History ι k → I.Vec)
    {Ω : Type*} (R : ℕ → Ω → ι → ℝ) (T : ℕ) (ω : Ω) : Prop :=
  (∀ k ≤ T,
    let x := (U.step k (histOf R k ω)).x
    let xk := xh k (histOf R k ω)
    supNorm (fun i => opNorm ((wBlock P I xk i)⁻¹ * (wBlock P I x i - wBlock P I xk i))) ≤
      K₀ * αnb) ∧
    ∀ k < T,
      let xk := xh k (histOf R k ω)
      let xk' := xh (k + 1) (histOf R (k + 1) ω)
      wtNorm (I.tau P xk) (fun i => (I.tau P xk i)⁻¹ * (I.tau P xk' i - I.tau P xk i)) ≤
          K₀ * P.β / P.Cnorm ∧
        wtNorm (I.tau P xk)
            (fun i => opNorm ((wBlock P I xk i)⁻¹ * (wBlock P I xk' i - wBlock P I xk i))) ≤
          K₀ * P.β / P.Cnorm

end Instance

end BlockLewisIPM


