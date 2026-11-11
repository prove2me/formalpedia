-- Prove2me | Definitions.Def_DiscIsoCurvature_Cube_Curvature
-- name    : DiscIsoCurvature_Cube_Curvature
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:08:24.486949+00:00
-- url     : https://prove2.me/theorems/57e23368-5181-4d43-b15f-65205ad86d64
-- title:
--   Bakry–Émery conditions BE and rBE, gradient estimates WGE, SGE and CSGE, and the matrix fields M, D, M⋆, D⋆
-- statement:
--   In the setting of §3 (rates $q$, weights $w$, generator $L$, $P_t=e^{tL}$), for $\rho\in\mathbb R$ and every $f:\Omega\to\mathbb R$, pointwise at every $x$:
--
--   - **BE** with constant $\rho$: $\Gamma_{2;w}(f)\ge\rho\,\Gamma_w(f)$;
--   - **rBE**: $\Gamma_{2;w}(f)-\Gamma(\sqrt{\Gamma_w(f)})\ge\rho\,\Gamma_w(f)$;
--   - **WGE**: $\Gamma_w(P_tf)\le e^{-2\rho t}P_t(\Gamma_w(f))$ for $t\ge0$;
--   - **SGE**: $\sqrt{\Gamma_w(P_tf)}\le e^{-\rho t}P_t\sqrt{\Gamma_w(f)}$ for $t\ge0$;
--   - **CSGE** (coordinate-wise strong gradient estimate): for every $\tau\in[0,\infty]$ and $t\ge0$,
--   $$\big\|P_\tau|\nabla_w|P_tf\big\|_2\le e^{-\rho t}\big\|P_{\tau+t}|\nabla_w|f\big\|_2,$$
--   where $|\nabla_w|g=(|\delta_{w,1}|g,\dots,|\delta_{w,n}|g)$, $P$ acts entrywise and $\|\cdot\|_2$ is the Euclidean norm over coordinates. 0-CSGE is $\tau=0$ and ∞-CSGE is $\tau=\infty$ ($P_\infty=\mathbb E_\mu$).
--
--   **Matrix fields** (Eqs. (49), (51)): $M_{ij}(x)=\tfrac12\big(\sqrt{\mu(x^{ij})/\mu(x^i)}-\sqrt{\mu(x^j)/\mu(x)}\big)$ for $i\ne j$, $M_{ii}=0$; $D(x)=\mathrm{diag}\{\sqrt{\mu(x)/\mu(x^i)}\}_i$; $M^\star=(\sup_x|M_{ij}(x)|)_{ij}$ and $D^\star=(\inf_xD_{ij}(x))_{ij}$.
--
--   These are the curvature notions of §4 and the matrices of §6 whose eigenvalues bound the CSGE constant.
--
--   **Formalization Note.** `CSGEAt μ q w ρ τ` is the condition at one $\tau$ (`τ : WithTop ℝ≥0`, `t : ℝ≥0`, $\tau+t$ in `WithTop ℝ≥0`); `CSGE` quantifies over every $\tau$. The suprema and infima in $M^\star$, $D^\star$ are over the finite nonempty cube.
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 18 Definitions 4.1, 4.3, p. 21 Definition 4.8, p. 33 Eq. (49), p. 34 Eq. (51), p. 35 Theorem 6.4

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Semigroup

namespace DiscIsoCurvature.Cube

open scoped NNReal

/-!
# Bakry–Émery conditions, gradient estimates, CSGE, and the matrix fields `M`, `D`, `M⋆`, `D⋆`

Chen, Chen, Zhang, *Discrete Isoperimetric Inequalities via Curvature*, arXiv:2609.24687
(version of November 3, 2026, sha256 ec30d304…): Definitions 4.1, 4.3 (p. 18), Definition 4.8
(p. 21), Eqs. (49) (p. 33) and (51) (p. 34), Theorem 6.4 (p. 35).

All conditions are pointwise inequalities, for every `f : Ω → ℝ` and every `x ∈ Ω` (the paper's
`f ≤ g` means `f(x) ≤ g(x)` for all `x`, §4.1), with a real constant `ρ` (possibly negative).
`L`, `P_t`, `Γ_w`, `Γ_{2;w}`, `|δ_{w,i}|` are those of the rates `q`, weights `w`
(`Def_DiscIsoCurvature_Cube_Semigroup`). The standing assumptions of Definitions 4.1, 4.3, 4.8
(a distribution `μ`, positive rates reversible for `μ`, positive weights) are hypotheses of the
theorems that use these conditions.
-/

/-- Bakry–Émery condition with constant `ρ` (Definition 4.1): `Γ_{2;w}(f) ≥ ρ Γ_w(f)`. -/
def BE {n : ℕ} (q w : Fin n → BoolCube n → ℝ) (ρ : ℝ) : Prop :=
  ∀ (f : BoolCube n → ℝ) (x : BoolCube n), ρ * gamma w q f f x ≤ gamma2 w q f x

/-- Reinforced Bakry–Émery condition with constant `ρ` (Definition 4.1):
`Γ_{2;w}(f) − Γ(√(Γ_w(f))) ≥ ρ Γ_w(f)`, with `Γ` unweighted. -/
def RBE {n : ℕ} (q w : Fin n → BoolCube n → ℝ) (ρ : ℝ) : Prop :=
  ∀ (f : BoolCube n → ℝ) (x : BoolCube n),
    ρ * gamma w q f f x ≤
      gamma2 w q f x
        - gamma (unitWeight n) q (fun y => Real.sqrt (gamma w q f f y))
            (fun y => Real.sqrt (gamma w q f f y)) x

/-- Weak gradient estimate with constant `ρ` (Definition 4.3):
`Γ_w(P_t f) ≤ e^{−2ρt} P_t(Γ_w(f))` for all `f` and `t ≥ 0`. -/
def WGE {n : ℕ} (q w : Fin n → BoolCube n → ℝ) (ρ : ℝ) : Prop :=
  ∀ (f : BoolCube n → ℝ) (t : ℝ), 0 ≤ t → ∀ x : BoolCube n,
    gamma w q (semigroup q t f) (semigroup q t f) x ≤
      Real.exp (-2 * ρ * t) * semigroup q t (fun y => gamma w q f f y) x

/-- Strong gradient estimate with constant `ρ` (Definition 4.3):
`√(Γ_w(P_t f)) ≤ e^{−ρt} P_t √(Γ_w(f))` for all `f` and `t ≥ 0`. -/
def SGE {n : ℕ} (q w : Fin n → BoolCube n → ℝ) (ρ : ℝ) : Prop :=
  ∀ (f : BoolCube n → ℝ) (t : ℝ), 0 ≤ t → ∀ x : BoolCube n,
    Real.sqrt (gamma w q (semigroup q t f) (semigroup q t f) x) ≤
      Real.exp (-ρ * t) * semigroup q t (fun y => Real.sqrt (gamma w q f f y)) x

/-- The coordinate-wise strong gradient estimate at a fixed `τ ∈ [0, ∞]` (Definition 4.8):
for every `f` and `t ≥ 0`, pointwise in `x`,
`‖P_τ |∇_w| P_t f‖₂ ≤ e^{−ρt} ‖P_{τ+t} |∇_w| f‖₂`, where `P` acts on the vector field
`|∇_w| g = (|δ_{w,i}| g)ᵢ` entrywise and `‖·‖₂` is the Euclidean norm over `i`. `τ = 0` is
0-CSGE, `τ = ⊤` is ∞-CSGE (`P_∞ = E_μ`). Here `t : ℝ≥0` and `τ + t` is computed in
`WithTop ℝ≥0` (`∞ + t = ∞`). -/
def CSGEAt {n : ℕ} (μ : BoolCube n → ℝ) (q w : Fin n → BoolCube n → ℝ) (ρ : ℝ) (τ : WithTop ℝ≥0) :
    Prop :=
  ∀ (f : BoolCube n → ℝ) (t : ℝ≥0) (x : BoolCube n),
    l2norm (fun i => semigroupExt μ q τ (absDelta w q i (semigroup q t f)) x) ≤
      Real.exp (-ρ * t) *
        l2norm (fun i => semigroupExt μ q (τ + (t : WithTop ℝ≥0)) (absDelta w q i f) x)

/-- CSGE with constant `ρ` (Definition 4.8): `CSGEAt` for every `τ ∈ [0, ∞]`. -/
def CSGE {n : ℕ} (μ : BoolCube n → ℝ) (q w : Fin n → BoolCube n → ℝ) (ρ : ℝ) : Prop :=
  ∀ τ : WithTop ℝ≥0, CSGEAt μ q w ρ τ

/-- The matrix field `M` of (49) (p. 33): for `i ≠ j`,
`M_ij(x) = ½ (√(μ(x^{ij})/μ(x^i)) − √(μ(x^j)/μ(x)))`, and `M_ii(x) = 0`;
`x^{ij} = (x^i)^j`. -/
noncomputable def matM {n : ℕ} (μ : BoolCube n → ℝ) (x : BoolCube n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 0 else
    (1 / 2) * (Real.sqrt (μ (flip (flip x i) j) / μ (flip x i)) - Real.sqrt (μ (flip x j) / μ x))

/-- The diagonal matrix field `D(x) = diag{√(μ(x)/μ(x^i))}ᵢ` of (51) (p. 34). -/
noncomputable def matD {n : ℕ} (μ : BoolCube n → ℝ) (x : BoolCube n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => Real.sqrt (μ x / μ (flip x i)))

/-- `M⋆ = (sup_x |M_ij(x)|)_{ij}` (Theorem 6.4, p. 35). -/
noncomputable def matMStar {n : ℕ} (μ : BoolCube n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ⨆ x : BoolCube n, |matM μ x i j|

/-- `D⋆ = (inf_x D_ij(x))_{ij}` (Theorem 6.4, p. 35). -/
noncomputable def matDStar {n : ℕ} (μ : BoolCube n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ⨅ x : BoolCube n, matD μ x i j

end DiscIsoCurvature.Cube


