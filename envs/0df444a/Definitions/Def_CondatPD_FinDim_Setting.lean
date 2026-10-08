-- Prove2me | Definitions.Def_CondatPD_FinDim_Setting
-- name    : CondatPD_FinDim_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:19:18.021619+00:00
-- url     : https://prove2.me/theorems/f6d21cac-d3af-493f-8b74-0ab2be5456c2
-- title:
--   §2–§5 — conjugate, smooth term (2), solutions of (6) and (48), Algorithms 3.1, 3.2, 5.1, 5.2, the operators P, P′ and T
-- statement:
--   Throughout, $\mathcal X$ and $\mathcal Y$ are real Hilbert spaces, $L:\mathcal X\to\mathcal Y$ is a bounded linear operator with adjoint $L^*$, and functions with values in $\mathbb R\cup\{+\infty\}$ are encoded as extended reals. This file fixes the objects of Condat's primal–dual splitting method used by Theorems 3.3 and 5.3.
--
--   1. **Fenchel–Rockafellar conjugate.** For $J:\mathcal H\to\mathbb R\cup\{+\infty\}$,
--   $$J^*(s)=\sup_{s'\in\mathcal H}\big[\langle s,s'\rangle-J(s')\big],$$
--   an extended-real supremum.
--   2. **Smooth term (2).** $F:\mathcal X\to\mathbb R$ is convex, differentiable on $\mathcal X$, and $\|\nabla F(x)-\nabla F(x')\|\le\beta\|x-x'\|$ for all $x,x'$, for a given $\beta\in[0,+\infty[$.
--   3. **Solutions of (6).** $(\hat x,\hat y)\in\mathcal X\times\mathcal Y$ solves
--   $$0\in\partial G(\hat x)+L^*\hat y+\nabla F(\hat x),\qquad 0\in-L\hat x+\partial H^*(\hat y),$$
--   written equivalently as $-L^*\hat y-\nabla F(\hat x)\in\partial G(\hat x)$ and $L\hat x\in\partial H^*(\hat y)$, where $\partial J(u)=\{v:\ J(u)+\langle v,u'-u\rangle\le J(u')\ \forall u'\}$.
--   4. **Algorithm 3.1, (9).** Given maps $P_G=\mathrm{prox}_{\tau G}$, $P_H=\mathrm{prox}_{\sigma H^*}$, relaxation parameters $(\rho_n)$ and error terms $e_{F,n},e_{G,n}\in\mathcal X$, $e_{H,n}\in\mathcal Y$, a pair of sequences $(x_n,y_n)$ is a run if for every $n$
--   $$\tilde x_{n+1}=P_G\big(x_n-\tau(\nabla F(x_n)+e_{F,n})-\tau L^*y_n\big)+e_{G,n},\quad \tilde y_{n+1}=P_H\big(y_n+\sigma L(2\tilde x_{n+1}-x_n)\big)+e_{H,n},$$
--   $$(x_{n+1},y_{n+1})=\rho_n(\tilde x_{n+1},\tilde y_{n+1})+(1-\rho_n)(x_n,y_n).$$
--   The initial estimate $(x_0,y_0)$ is arbitrary.
--   5. **Algorithm 3.2, (10).** The same with the dual step first: $\tilde y_{n+1}=P_H(y_n+\sigma Lx_n)+e_{H,n}$ and $\tilde x_{n+1}=P_G\big(x_n-\tau(\nabla F(x_n)+e_{F,n})-\tau L^*(2\tilde y_{n+1}-y_n)\big)+e_{G,n}$, then the same relaxation.
--   6. **The operators $P$ of (20) and $P'$ of (44)** on $\mathcal Z=\mathcal X\times\mathcal Y$:
--   $$P(x,y)=\Big(\tfrac1\tau x-L^*y,\ -Lx+\tfrac1\sigma y\Big),\qquad P'(x,y)=\Big(\tfrac1\tau x+L^*y,\ Lx+\tfrac1\sigma y\Big),$$
--   and their quadratic forms $\langle z,Pz\rangle_I=\langle x,\tfrac1\tau x-L^*y\rangle+\langle y,-Lx+\tfrac1\sigma y\rangle$ and $\langle z,P'z\rangle_I=\langle x,\tfrac1\tau x+L^*y\rangle+\langle y,Lx+\tfrac1\sigma y\rangle$, where $\langle\cdot,\cdot\rangle_I$ is the product inner product (19).
--   7. **The operator $T$** of the proof of Theorem 3.3 (steps 1. and 2. of Algorithm 3.1 with $F=0$ and no error terms): $T(x,y)=(\tilde x,\tilde y)$ with $\tilde x=\mathrm{prox}_{\tau G}(x-\tau L^*y)$ and $\tilde y=\mathrm{prox}_{\sigma H^*}\big(y+\sigma L(2\tilde x-x)\big)$.
--   8. **Section 5.** For $m$ Hilbert spaces $\mathcal Y_1,\dots,\mathcal Y_m$, functions $H_i$ and bounded linear $L_i:\mathcal X\to\mathcal Y_i$: $(\hat x,\hat y_1,\dots,\hat y_m)$ solves (48) if $-\sum_i L_i^*\hat y_i-\nabla F(\hat x)\in\partial G(\hat x)$ and $L_i\hat x\in\partial H_i^*(\hat y_i)$ for every $i$. Algorithm 5.1, (55), computes $\tilde x_{n+1}=\mathrm{prox}_{\tau G}\big(x_n-\tau(\nabla F(x_n)+e_{F,n})-\tau\sum_i L_i^*y_{i,n}\big)+e_{G,n}$, $x_{n+1}=\rho_n\tilde x_{n+1}+(1-\rho_n)x_n$, and for every $i$, $\tilde y_{i,n+1}=\mathrm{prox}_{\sigma H_i^*}\big(y_{i,n}+\sigma L_i(2\tilde x_{n+1}-x_n)\big)+e_{H_i,n}$, $y_{i,n+1}=\rho_n\tilde y_{i,n+1}+(1-\rho_n)y_{i,n}$. Algorithm 5.2, (56), computes first, for every $i$, $\tilde y_{i,n+1}=\mathrm{prox}_{\sigma H_i^*}(y_{i,n}+\sigma L_ix_n)+e_{H_i,n}$ and $y_{i,n+1}=\rho_n\tilde y_{i,n+1}+(1-\rho_n)y_{i,n}$, then $\tilde x_{n+1}=\mathrm{prox}_{\tau G}\big(x_n-\tau(\nabla F(x_n)+e_{F,n})-\tau\sum_iL_i^*(2\tilde y_{i,n+1}-y_{i,n})\big)+e_{G,n}$ and $x_{n+1}=\rho_n\tilde x_{n+1}+(1-\rho_n)x_n$.
--
--   These are the objects of problem (1) and its primal–dual inclusion (6), shared by every statement of the mission.
--
--   **Formalization Note** Proximity operators are not constructed: they enter as maps satisfying the published minimisation predicate `IsProx`, and the subdifferential is the published `IsSubgradient`, which also asks $J(u)<+\infty$ (automatic for a proper $J$). The step-3 formula of Algorithm 5.2 is printed as $\tau\sum_i L_i^*(2\tilde y_{n+1}-y_n)$ without the index $i$; the indexed form is used. $P$, $P'$ and $T$ are plain maps on $\mathcal X\times\mathcal Y$.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), pp. 2–5, (1), (2), (6), Algorithms 3.1–3.2; p. 10, (19)–(20); pp. 12–13, proof of Theorem 3.3, operator T, (44); pp. 14–15, (48), Algorithms 5.1–5.2

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_InertialFB_IFB_ConvexAnalysis

open InnerProductSpace

namespace CondatPD.FinDim

/-! Objects of Condat (2013), §2–§3 and §5, and the operators `P`, `P′`, `T` of the proof of
Theorem 3.3 (§4). Γ₀ is `ThreeOpSplitting.ConvexRates.IsProperClosedConvex`, proximity operators
are maps satisfying `ThreeOpSplitting.ConvexRates.IsProx`, and `∂J` is
`InertialFB.IFB.IsSubgradient`. -/

/-- The Fenchel–Rockafellar conjugate `J*(s) = sup_{s'} [⟨s, s'⟩ − J(s')]` (p. 2), an extended
real supremum. -/
noncomputable def conj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (J : E → EReal) (s : E) : EReal :=
  ⨆ s' : E, ((⟪s, s'⟫_ℝ : ℝ) : EReal) - J s'

/-- The smooth term of (2): `F` is convex, differentiable on `X`, and `∇F` is `β`-Lipschitz for
some `β ∈ [0, +∞[`. -/
def IsSmoothTerm {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (β : ℝ) (F : X → ℝ) : Prop :=
  ConvexOn ℝ Set.univ F ∧ Differentiable ℝ F ∧ 0 ≤ β ∧
    ∀ x x' : X, ‖gradient F x - gradient F x'‖ ≤ β * ‖x - x'‖

/-- `(xh, yh)` solves the inclusion (6):
`0 ∈ ∂G(xh) + L* yh + ∇F(xh)` and `0 ∈ −L xh + ∂H*(yh)`, written as
`−L* yh − ∇F(xh) ∈ ∂G(xh)` and `L xh ∈ ∂H*(yh)`. -/
def IsPDSolution {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → ℝ) (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y) (xh : X) (yh : Y) : Prop :=
  InertialFB.IFB.IsSubgradient G xh (-(ContinuousLinearMap.adjoint L yh) - gradient F xh) ∧
    InertialFB.IFB.IsSubgradient (conj H) yh (L xh)

/-- `(x, y)` is a run of Algorithm 3.1, (9), with proximity maps `PG = prox_{τG}`,
`PH = prox_{σH*}`, relaxation parameters `ρ` and error terms `eF, eG, eH`; the initial estimate
`(x 0, y 0)` is arbitrary. -/
def IsAlg31Run {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → ℝ) (PG : X → X) (PH : Y → Y) (τ σ : ℝ) (L : X →L[ℝ] Y) (ρ : ℕ → ℝ)
    (eF eG : ℕ → X) (eH : ℕ → Y) (x : ℕ → X) (y : ℕ → Y) : Prop :=
  ∀ n : ℕ,
    let xt := PG (x n - τ • (gradient F (x n) + eF n) - τ • ContinuousLinearMap.adjoint L (y n))
      + eG n
    let yt := PH (y n + σ • L ((2 : ℝ) • xt - x n)) + eH n
    x (n + 1) = ρ n • xt + (1 - ρ n) • x n ∧ y (n + 1) = ρ n • yt + (1 - ρ n) • y n

/-- `(x, y)` is a run of Algorithm 3.2, (10): the dual step comes first, and the primal step uses
the over-relaxed dual point `2 ỹₙ₊₁ − yₙ`. -/
def IsAlg32Run {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → ℝ) (PG : X → X) (PH : Y → Y) (τ σ : ℝ) (L : X →L[ℝ] Y) (ρ : ℕ → ℝ)
    (eF eG : ℕ → X) (eH : ℕ → Y) (x : ℕ → X) (y : ℕ → Y) : Prop :=
  ∀ n : ℕ,
    let yt := PH (y n + σ • L (x n)) + eH n
    let xt := PG (x n - τ • (gradient F (x n) + eF n)
      - τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • yt - y n)) + eG n
    x (n + 1) = ρ n • xt + (1 - ρ n) • x n ∧ y (n + 1) = ρ n • yt + (1 - ρ n) • y n

/-- The quadratic form `⟨z, P z⟩_I` of the operator `P` of (20), at `z = (x, y)`:
`⟨x, x/τ − L* y⟩ + ⟨y, −L x + y/σ⟩`. -/
noncomputable def qP {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (τ σ : ℝ) (L : X →L[ℝ] Y) (x : X) (y : Y) : ℝ :=
  ⟪x, τ⁻¹ • x - ContinuousLinearMap.adjoint L y⟫_ℝ + ⟪y, -(L x) + σ⁻¹ • y⟫_ℝ

/-- The quadratic form `⟨z, P′ z⟩_I` of the operator `P′` of (44), at `z = (x, y)`:
`⟨x, x/τ + L* y⟩ + ⟨y, L x + y/σ⟩`. -/
noncomputable def qP' {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (τ σ : ℝ) (L : X →L[ℝ] Y) (x : X) (y : Y) : ℝ :=
  ⟪x, τ⁻¹ • x + ContinuousLinearMap.adjoint L y⟫_ℝ + ⟪y, L x + σ⁻¹ • y⟫_ℝ

/-- The operator `P : (x, y) ↦ (x/τ − L* y, −L x + y/σ)` of (20), as a map on `X × Y`. -/
noncomputable def opP {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (τ σ : ℝ) (L : X →L[ℝ] Y) (z : X × Y) : X × Y :=
  (τ⁻¹ • z.1 - ContinuousLinearMap.adjoint L z.2, -(L z.1) + σ⁻¹ • z.2)

/-- The operator `T` of the proof of Theorem 3.3 (p. 12): steps 1. and 2. of Algorithm 3.1 with
`F = 0` and no error terms, `T(x, y) = (x̃, ỹ)` with `x̃ = prox_{τG}(x − τ L* y)` and
`ỹ = prox_{σH*}(y + σ L(2x̃ − x))`. -/
noncomputable def stepT {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (PG : X → X) (PH : Y → Y) (τ σ : ℝ) (L : X →L[ℝ] Y) (z : X × Y) : X × Y :=
  let xt := PG (z.1 - τ • ContinuousLinearMap.adjoint L z.2)
  (xt, PH (z.2 + σ • L ((2 : ℝ) • xt - z.1)))

/-! §5: `m` composite terms `Hᵢ ∘ Lᵢ`, `Lᵢ : X → Yᵢ`. -/

/-- `(xh, yh₁, …, yhₘ)` solves (48): `0 ∈ ∂G(xh) + Σᵢ Lᵢ* yhᵢ + ∇F(xh)` and, for every `i`,
`0 ∈ −Lᵢ xh + ∂Hᵢ*(yhᵢ)`. -/
def IsPDSolutionM {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {m : ℕ} {Y : Fin m → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, InnerProductSpace ℝ (Y i)]
    [∀ i, CompleteSpace (Y i)]
    (F : X → ℝ) (G : X → EReal) (H : ∀ i, Y i → EReal) (L : ∀ i, X →L[ℝ] Y i)
    (xh : X) (yh : ∀ i, Y i) : Prop :=
  InertialFB.IFB.IsSubgradient G xh
      (-(∑ i, ContinuousLinearMap.adjoint (L i) (yh i)) - gradient F xh) ∧
    ∀ i, InertialFB.IFB.IsSubgradient (conj (H i)) (yh i) (L i xh)

/-- `(x, y)` is a run of Algorithm 5.1, (55), with `PG = prox_{τG}` and `PH i = prox_{σHᵢ*}`. -/
def IsAlg51Run {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {m : ℕ} {Y : Fin m → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, InnerProductSpace ℝ (Y i)]
    [∀ i, CompleteSpace (Y i)]
    (F : X → ℝ) (PG : X → X) (PH : ∀ i, Y i → Y i) (τ σ : ℝ) (L : ∀ i, X →L[ℝ] Y i)
    (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → ∀ i, Y i) (x : ℕ → X) (y : ℕ → ∀ i, Y i) : Prop :=
  ∀ n : ℕ,
    let xt := PG (x n - τ • (gradient F (x n) + eF n)
      - τ • ∑ i, ContinuousLinearMap.adjoint (L i) (y n i)) + eG n
    x (n + 1) = ρ n • xt + (1 - ρ n) • x n ∧
      ∀ i, y (n + 1) i =
        ρ n • (PH i (y n i + σ • L i ((2 : ℝ) • xt - x n)) + eH n i) + (1 - ρ n) • y n i

/-- `(x, y)` is a run of Algorithm 5.2, (56), with step 3 in its indexed form
`τ Σᵢ Lᵢ*(2ỹ_{i,n+1} − y_{i,n})`. -/
def IsAlg52Run {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {m : ℕ} {Y : Fin m → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, InnerProductSpace ℝ (Y i)]
    [∀ i, CompleteSpace (Y i)]
    (F : X → ℝ) (PG : X → X) (PH : ∀ i, Y i → Y i) (τ σ : ℝ) (L : ∀ i, X →L[ℝ] Y i)
    (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → ∀ i, Y i) (x : ℕ → X) (y : ℕ → ∀ i, Y i) : Prop :=
  ∀ n : ℕ,
    let yt : ∀ i, Y i := fun i => PH i (y n i + σ • L i (x n)) + eH n i
    let xt := PG (x n - τ • (gradient F (x n) + eF n)
      - τ • ∑ i, ContinuousLinearMap.adjoint (L i) ((2 : ℝ) • yt i - y n i)) + eG n
    (∀ i, y (n + 1) i = ρ n • yt i + (1 - ρ n) • y n i) ∧
      x (n + 1) = ρ n • xt + (1 - ρ n) • x n

end CondatPD.FinDim


