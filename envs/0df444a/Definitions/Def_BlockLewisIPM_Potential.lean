-- Prove2me | Definitions.Def_BlockLewisIPM_Potential
-- name    : BlockLewisIPM_Potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:49:45.206503+00:00
-- url     : https://prove2.me/theorems/b26cc0d6-0d03-431b-a56b-6dd9d32dca76
-- title:
--   Parameters, mixed norms, the central path residual, the potential and $\epsilon$-centering
-- statement:
--   The parameters of Algorithm 1 are, for a universal constant $C$ and $m\ge2$ blocks,
--
--   $$\theta=\frac1{10\log m},\ \ p=1-\theta,\ \ \epsilon=\frac\theta C,\ \ C_{\mathrm{norm}}=\frac C\theta,\ \ C_\lambda=30\log(10m),\ \ \lambda=\frac{C_\lambda}{\epsilon^2},\ \ \beta=\frac{\theta}{CC_\lambda\sqrt\lambda},\ \ \alpha=\frac\beta C,\ \ \sigma=\frac\theta C.$$
--
--   The **mixed norms** are $\|u\|_{\tau+\infty}=\|u\|_\infty+C_{\mathrm{norm}}\|u\|_\tau$ and $\|v\|_{2,\tau+\infty}=\|v\|_{2,\infty}+C_{\mathrm{norm}}\|v\|_{2,\tau}$, with dual norms and maximizers $v^{\flat(\tau)}$.
--
--   For a triplet $(x,s,\rho)$, the **residual**, **metric** and **potential** are
--
--   $$\mu_i=\frac{s_i}{\rho\tau(x)_i}+\nabla\phi_i(x_i),\qquad \Gamma_i(\mu_i,x_i)=2D_{\phi_i^*}\bigl(\nabla\phi_i(x_i)-\mu_i,\nabla\phi_i(x_i)\bigr),\qquad \Psi(\mu,x)=\sum_i e^{\lambda\Gamma_i(\mu_i,x_i)},$$
--
--   with $\nabla^{\mathrm{loc}}_\mu\Psi=\nabla^2\Phi(x)^{1/2}\nabla_\mu\Psi$.
--
--   The triplet is **$\epsilon$-centered** if $x\in\operatorname{int}K$, $\rho>0$, and
--
--   1. $\Gamma_i(\mu_i,x_i)\le\epsilon^2$ for all $i$;
--   2. $\|A^\top x-b\|_{(A^\top T^{-1}\nabla^2\Phi(x)^{-1}A)^{-1}}\le\alpha\beta/(2C_{\mathrm{norm}})$;
--   3. $Ay+s=c$ for some $y$.
--
--   A pair $(\bar x,\bar\tau)$ is an **$\alpha$-approximation** of $(x,\tau(x))$ if $\|\nabla^2\phi_i(x_i)^{1/2}(x_i-\bar x_i)\|_2\le\alpha$ for all $i$ and $\|T(x)^{-1}(\tau(x)-\bar\tau)\|_\infty\le\alpha$; and $\bar\mu$ is a $10\alpha$-approximation of $\mu$ if $\|\nabla^2\phi_i(x_i)^{-1/2}(\mu_i-\bar\mu_i)\|_2\le10\alpha$ for all $i$.
--
--   **Formalization Note** "With high probability" (§3.1) means failure at most $m^{-10}$, written on the outer measure. The parameters need $m\ge2$ since $\theta$ is undefined at $m=1$.
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Algorithm 1, p.16; Definitions 14–18, pp.13–14

import Mathlib
import Definitions.Def_BlockLewisIPM_LewisWeight

namespace BlockLewisIPM

/-!
# Parameters, mixed norms, the central path residual and the potential

Zhang, Wright, *A Fast Lewis-weight Interior Point Method for Linear Optimization over
Product-Domain* (manuscript, sha256 66072000…), the parameters of Algorithm 1, p.16, and Definitions
14–18, pp.13–14.

**Formalization Note.**
* `Params` holds the universal `C` and `m`. The other parameters are the functions of Algorithm 1,
  with natural `log`. `θ` needs `m ≥ 2`, which statements using it assume.
* The dual norms of Definition 14 are suprema over the unit ball, which is nonempty and bounded. A
  maximizer `u^♭(τ)` need not be unique: `IsFlat` says `h` is one.
* `∇_µΨ` is the derivative in `µ` at fixed `x`, in the standard basis, and `∇_ΓΨ = (ψ′(Γ_i))_i`.
* `IsCentered` includes `x ∈ int K` and `ρ > 0`, without which Definition 17's terms have no meaning.
* `ϕ_i*` is finite everywhere for compact `K_i`, so `Γ` is defined for every `µ`.
-/

open Matrix

/-- The universal constant `C` and the number of blocks `m`. -/
structure Params where
  /-- The universal constant `C` of §3.1, p.10. -/
  C : ℝ
  /-- The number of blocks. -/
  m : ℕ

namespace Params

variable (P : Params)

/-- `θ = 1/(10 log m)`. -/
noncomputable def θ : ℝ := 1 / (10 * Real.log P.m)
/-- `p = 1 - θ`. -/
noncomputable def p : ℝ := 1 - P.θ
/-- `ϵ = θ/C`. -/
noncomputable def ϵ : ℝ := P.θ / P.C
/-- `C_norm = C/θ`. -/
noncomputable def Cnorm : ℝ := P.C / P.θ
/-- `C_λ = 30 log(10 m)`. -/
noncomputable def Clam : ℝ := 30 * Real.log (10 * P.m)
/-- `λ = C_λ/ϵ²`. -/
noncomputable def lam : ℝ := P.Clam / P.ϵ ^ 2
/-- `β = θ/(C C_λ √λ)`. -/
noncomputable def β : ℝ := P.θ / (P.C * P.Clam * Real.sqrt P.lam)
/-- `α = β/C`. -/
noncomputable def α : ℝ := P.β / P.C
/-- `σ = θ/C`. -/
noncomputable def σ : ℝ := P.θ / P.C
/-- `r = αβ/(4 C_norm √d)` of Lemma 20, p.15, and of the assertion in Algorithm 1, p.16. -/
noncomputable def r (d : ℕ) : ℝ := P.α * P.β / (4 * P.Cnorm * Real.sqrt d)

end Params

/-- "With high probability" (§3.1, p.11): the event fails with probability at most `m⁻¹⁰`. Written
on the outer measure, so measurability of the event never enters. -/
def Whp {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (m : ℕ) (E : Ω → Prop) :
    Prop :=
  μ {ω | ¬ E ω} ≤ ENNReal.ofReal ((m : ℝ) ^ (-10 : ℝ))

section Norms

variable {ι : Type} [Fintype ι] {dim : ι → ℕ}

/-- `‖u‖_{τ+∞} = ‖u‖_∞ + C_norm ‖u‖_τ` (Definition 14, p.13). -/
noncomputable def mixedNorm (Cnorm : ℝ) (τ u : ι → ℝ) : ℝ :=
  supNorm u + Cnorm * wtNorm τ u

/-- `‖v‖_{2,τ+∞} = ‖v‖_{2,∞} + C_norm ‖v‖_{2,τ}` (Definition 14, p.13). -/
noncomputable def mixedBlockNorm (Cnorm : ℝ) (τ : ι → ℝ) (v : BIdx dim → ℝ) : ℝ :=
  mixedNorm Cnorm τ (blockNorms v)

/-- `‖u‖*_{τ+∞} = max_{‖h‖_{τ+∞} ≤ 1} h⊤u` (Definition 14, p.13). -/
noncomputable def dualMixedNorm (Cnorm : ℝ) (τ u : ι → ℝ) : ℝ :=
  sSup {a | ∃ h : ι → ℝ, mixedNorm Cnorm τ h ≤ 1 ∧ a = h ⬝ᵥ u}

/-- `‖v‖*_{2,τ+∞} = max_{‖h‖_{2,τ+∞} ≤ 1} h⊤v` (Definition 14, p.13). -/
noncomputable def dualMixedBlockNorm (Cnorm : ℝ) (τ : ι → ℝ) (v : BIdx dim → ℝ) : ℝ :=
  sSup {a | ∃ h : BIdx dim → ℝ, mixedBlockNorm Cnorm τ h ≤ 1 ∧ a = h ⬝ᵥ v}

/-- `h` is a dual vector `v^{♭(τ)}`: a maximizer of `h⊤v` on the unit ball of `‖·‖_{2,τ+∞}`
(Definition 14, p.13). -/
def IsFlat (Cnorm : ℝ) (τ : ι → ℝ) (v h : BIdx dim → ℝ) : Prop :=
  mixedBlockNorm Cnorm τ h ≤ 1 ∧ ∀ h', mixedBlockNorm Cnorm τ h' ≤ 1 → h' ⬝ᵥ v ≤ h ⬝ᵥ v

end Norms

namespace Instance

variable {ι : Type} [Fintype ι] [DecidableEq ι] (I : Instance ι)

/-- `τ(x)` for the parameters of `P`. -/
noncomputable def tau (P : Params) (x : I.Vec) : ι → ℝ := I.tauAt P.p P.σ x

/-- The parameters of Algorithm 1 at this instance, for the universal constant `C`. -/
def par (_I : Instance ι) (C : ℝ) : Params := ⟨C, Fintype.card ι⟩

/-- The residual `µ_i(x, s, ρ) = s_i/(ρτ(x)_i) + ∇ϕ_i(x_i)` of Definition 15, p.14. -/
noncomputable def mu (P : Params) (x s : I.Vec) (ρ : ℝ) : I.Vec :=
  glue fun i => (ρ * I.tau P x i)⁻¹ • block s i + I.grad x i

/-- `Γ_i(µ_i, x_i) = 2 D_{ϕ_i*}(∇ϕ_i(x_i) - µ_i, ∇ϕ_i(x_i))` of Definition 15, p.14. -/
noncomputable def Gam (μ x : I.Vec) (i : ι) : ℝ :=
  2 * bregman (conj (I.K i) (I.φ i)) (I.grad x i - block μ i) (I.grad x i)

/-- The potential `Ψ(µ, x) = ∑ e^{λ Γ_i(µ_i, x_i)}` of Definition 16, p.14. -/
noncomputable def Psi (lam : ℝ) (μ x : I.Vec) : ℝ :=
  ∑ i, Real.exp (lam * I.Gam μ x i)

/-- `∇_µΨ(µ, x)`, at fixed `x`. -/
noncomputable def gradMuPsi (lam : ℝ) (μ x : I.Vec) : I.Vec :=
  fun j => fderiv ℝ (fun μ' : I.Vec => I.Psi lam μ' x) μ (Pi.single j 1)

/-- `∇^loc_µΨ(µ, x) = ∇²Φ(x)^{1/2} ∇_µΨ(µ, x)` of Definition 16, p.14. -/
noncomputable def gradLoc (lam : ℝ) (μ x : I.Vec) : I.Vec :=
  I.hessSqrt x *ᵥ I.gradMuPsi lam μ x

/-- `∇_ΓΨ(µ, x) = (ψ′(Γ_i))_i = (λ e^{λ Γ_i})_i`, with `ψ(a) = e^{λ a}`. -/
noncomputable def gradGamPsi (lam : ℝ) (μ x : I.Vec) : ι → ℝ :=
  fun i => lam * Real.exp (lam * I.Gam μ x i)

/-- `A⊤T⁻¹∇²Φ(x)⁻¹A` for the weights `τ`. -/
noncomputable def schur (τ : ι → ℝ) (x : I.Vec) : Matrix (Fin I.d) (Fin I.d) ℝ :=
  I.Aᵀ * (diagG (dim := I.dim) (fun i => (τ i)⁻¹) * I.hessInv x * I.A)

/-- `(x, s, ρ)` is `ϵ`-centered (Definition 17, p.14), for the parameters `α, β, C_norm` of `P`. -/
structure IsCentered (P : Params) (ϵ : ℝ) (x s : I.Vec) (ρ : ℝ) : Prop where
  eps_pos : 0 < ϵ
  eps_le : ϵ ≤ 1 / 100
  rho_pos : 0 < ρ
  domain : I.InDomain x
  centrality : ∀ i, I.Gam (I.mu P x s ρ) x i ≤ ϵ ^ 2
  primal : wNorm (I.schur (I.tau P x) x)⁻¹ (I.Aᵀ *ᵥ x - I.b) ≤ P.α * P.β / (2 * P.Cnorm)
  dual : ∃ y : Fin I.d → ℝ, I.A *ᵥ y + s = I.c

/-- `(x̄, τ̄)` is an `α`-approximation of `(x, τ(x))` (Definition 18, p.14). -/
def IsApprox (P : Params) (γ : ℝ) (x xb : I.Vec) (τb : ι → ℝ) : Prop :=
  (∀ i, eNorm (matSqrt (I.hess x i) *ᵥ (block x i - block xb i)) ≤ γ) ∧
    supNorm (fun i => (I.tau P x i)⁻¹ * (I.tau P x i - τb i)) ≤ γ

/-- `µ̄` is a `10α`-approximation of `µ` at `x` (Definition 18, p.14). -/
def IsMuApprox (γ : ℝ) (x μ μb : I.Vec) : Prop :=
  ∀ i, eNorm (matInvSqrt (I.hess x i) *ᵥ (block μ i - block μb i)) ≤ γ

end Instance

end BlockLewisIPM


