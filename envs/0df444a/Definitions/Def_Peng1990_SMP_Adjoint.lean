-- Prove2me | Definitions.Def_Peng1990_SMP_Adjoint
-- name    : Peng1990_SMP_Adjoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:31:23.493359+00:00
-- url     : https://prove2.me/theorems/bee8f561-31e5-4fa5-b070-4f90c82bf956
-- title:
--   Variational equations (5), (6), (12), the representation relations (13), (17), and the adjoint equations (19), (20)
-- statement:
--   Fix a problem as in `ControlProblem`, a Wiener process $B$ with its filtration, and a reference pair $(y,u)$. Write $f_x(t)=f_x(y(t),u(t))$ for $f=g,\sigma,l,h$.
--
--   1. **First-order variational equation (5)** for a perturbed control $u^\varepsilon$: $y_1(0)=0$,
--   $$dy_1=\big[g_x(t)y_1+g(y,u^\varepsilon)-g(y,u)\big]dt+\sum_j\big[\sigma^j_x(t)y_1+\sigma^j(y,u^\varepsilon)-\sigma^j(y,u)\big]dB^j .$$
--   2. **Second-order variational equation (6)**: $y_2(0)=0$,
--   $$dy_2=\big[g_x(t)y_2+\tfrac12g_{xx}(t)y_1y_1+(g_x(y,u^\varepsilon)-g_x(y,u))y_1\big]dt+\sum_j\big[\sigma^j_x(t)y_2+\tfrac12\sigma^j_{xx}(t)y_1y_1+(\sigma^j_x(y,u^\varepsilon)-\sigma^j_x(y,u))y_1\big]dB^j .$$
--   3. **Linear system (12)**: $dz=(g_x(t)z+\varphi)\,dt+\sum_j(\sigma^j_x(t)z+\psi_j)\,dB^j$, $z(0)=0$.
--   4. **First-order adjoint process (13).** $(p,K)\in L^2_{\mathcal F}(0,T;\mathbb R^n)\times(L^2_{\mathcal F}(0,T;\mathbb R^n))^d$ such that for all $(\varphi,\psi)$ in the same space and every solution $z$ of (12),
--   $$E\int_0^T\Big[(p,\varphi)+\sum_{j=1}^d(K_j,\psi_j)\Big]dt=E\int_0^T l_x(t)z(t)\,dt+E\big(h_x(y(T))z(T)\big).$$
--   5. **Symmetric matrix system** (p. 973): $dZ=\big[Zg_x^*+g_xZ+\sum_j\sigma^j_xZ\sigma^{j*}_x+\Phi\big]dt+\sum_j\big[Z\sigma^{j*}_x+\sigma^j_xZ+\psi_j\big]dB^j$, $Z(0)=0$.
--   6. **Second-order adjoint process (16)–(17).** $(P,Q)\in L^2_{\mathcal F}(0,T;\mathbb R^{n,n})\times(L^2_{\mathcal F}(0,T;\mathbb R^{n,n}))^d$, symmetric-valued on $[0,T]$, such that for all symmetric-valued $(\Phi,\Psi)$ in the same space and every solution $Z$ of item 5,
--   $$E\int_0^T(Z(t),H_{xx}(t))_*\,dt+E\big(Z(T),h_{xx}(y(T))\big)_*=E\int_0^T\Big[(P(t),\Phi(t))_*+\sum_{j=1}^d(Q_j(t),\psi_j(t))_*\Big]dt,$$
--   where $(A_1,A_2)_*=\operatorname{tr}(A_1A_2)$ and $H_{xx}(t)=H_{xx}(y(t),u(t),p(t),K(t))$.
--   7. **First-order adjoint equation (19)**: $-dp=\big[g_x^*p+\sum_j\sigma^{j*}_xK_j+l_x\big](t)\,dt-\sum_jK_j\,dB^j$, $p(T)=h_x(y(T))$.
--   8. **Second-order adjoint equation (20)**: $-dP=\big[g_x^*P+Pg_x+\sum_j\sigma^{j*}_xP\sigma^j_x+\sum_j\sigma^{j*}_xQ_j+\sum_jQ_j\sigma^j_x+H_{xx}(y,u,p,K)\big]dt-\sum_jQ_j\,dB^j$, $P(T)=h_{xx}(y(T))$.
--
--   All solutions are in the sense of the `Stochastic` definitions: progressive for the natural filtration of $B$, which is what gives the backward equations their content.
--
--   **Formalization Note** In (5), (6) and the $Z$-equation the page writes $\sigma_x(\cdot)y\,dB$ and $[Z\sigma_x^*+\sigma_xZ+\Psi]\,dB$; these are read column by column, $\sum_j(\dots)^j\,dB^j$. In (6) the four integrals of the page are merged into one $ds$- and one $dB$-integral. On p. 972 $I$ uses $h_x(T)$ for $h_x(y(T))$. $R^{n,n}$ is the space of symmetric matrices (p. 973), so the test processes of (17) are symmetric-valued.
-- source:
--   Peng, A General Stochastic Maximum Principle for Optimal Control Problems, SIAM J. Control Optim. 28(4), 1990, https://doi.org/10.1137/0328054, p. 968, Lemma 1, (5), (6); pp. 971–972, (12), (13); p. 973, the symmetric matrix system, (16), (17); p. 974, (19); p. 975, (20)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_Peng1990_SMP_ControlProblem

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace Peng1990.SMP

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n k d : ℕ}

/-- `g_x(x, v)`, the Jacobian of `g` in `x`. -/
noncomputable def gX (cp : ControlProblem n k d) (x : Fin n → ℝ) (v : Fin k → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  jac (fun x' => cp.g x' v) x

/-- `σʲ_x(x, v)`, the Jacobian of the column `σʲ` in `x`. -/
noncomputable def σX (cp : ControlProblem n k d) (j : Fin d) (x : Fin n → ℝ) (v : Fin k → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  jac (fun x' => cp.σ j x' v) x

/-- `l_x(x, v)`, the gradient of `l` in `x`. -/
noncomputable def lX (cp : ControlProblem n k d) (x : Fin n → ℝ) (v : Fin k → ℝ) : Fin n → ℝ :=
  grad (fun x' => cp.l x' v) x

/-- The first-order variational equation (5) for the reference pair `(y, u)` and the perturbed
control `uε`: `y₁(0) = 0`,
`dy₁ = [g_x(y, u) y₁ + (g(y, uε) − g(y, u))] ds + Σⱼ [σʲ_x(y, u) y₁ + (σʲ(y, uε) − σʲ(y, u))] dBʲ`. -/
def SolvesFirstVariation (cp : ControlProblem n k d) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (y : ℝ≥0 → Ω → Fin n → ℝ) (u uε : ℝ≥0 → Ω → Fin k → ℝ)
    (y₁ : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesSDE 𝓕 P cp.T B 0
    (fun s ω z => gX cp (y s ω) (u s ω) *ᵥ z + (cp.g (y s ω) (uε s ω) - cp.g (y s ω) (u s ω)))
    (fun j s ω z => σX cp j (y s ω) (u s ω) *ᵥ z
      + (cp.σ j (y s ω) (uε s ω) - cp.σ j (y s ω) (u s ω)))
    y₁

/-- The second-order variational equation (6): `y₂(0) = 0`,
`dy₂ = [g_x(y, u) y₂ + ½ g_xx(y, u) y₁ y₁ + (g_x(y, uε) − g_x(y, u)) y₁] ds
      + Σⱼ [σʲ_x(y, u) y₂ + ½ σʲ_xx(y, u) y₁ y₁ + (σʲ_x(y, uε) − σʲ_x(y, u)) y₁] dBʲ`. -/
def SolvesSecondVariation (cp : ControlProblem n k d) (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (B : ℝ≥0 → Ω → Fin d → ℝ) (y : ℝ≥0 → Ω → Fin n → ℝ)
    (u uε : ℝ≥0 → Ω → Fin k → ℝ) (y₁ y₂ : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesSDE 𝓕 P cp.T B 0
    (fun s ω z => gX cp (y s ω) (u s ω) *ᵥ z
      + (1 / 2 : ℝ) • d2 (fun x => cp.g x (u s ω)) (y s ω) (y₁ s ω)
      + (gX cp (y s ω) (uε s ω) - gX cp (y s ω) (u s ω)) *ᵥ y₁ s ω)
    (fun j s ω z => σX cp j (y s ω) (u s ω) *ᵥ z
      + (1 / 2 : ℝ) • d2 (fun x => cp.σ j x (u s ω)) (y s ω) (y₁ s ω)
      + (σX cp j (y s ω) (uε s ω) - σX cp j (y s ω) (u s ω)) *ᵥ y₁ s ω)
    y₂

/-- The linear system (12): `z(0) = 0`,
`dz = (g_x(t) z + φ(t)) dt + Σⱼ (σʲ_x(t) z + ψⱼ(t)) dBʲ`, with `f_x(t) = f_x(y(t), u(t))`. -/
def SolvesLinearFirst (cp : ControlProblem n k d) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ)
    (φ : ℝ≥0 → Ω → Fin n → ℝ) (ψ : Fin d → ℝ≥0 → Ω → Fin n → ℝ)
    (z : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesSDE 𝓕 P cp.T B 0
    (fun s ω z' => gX cp (y s ω) (u s ω) *ᵥ z' + φ s ω)
    (fun j s ω z' => σX cp j (y s ω) (u s ω) *ᵥ z' + ψ j s ω)
    z

/-- `(p, K)` is the first-order adjoint process of (13): `p, K₁, …, K_d ∈ L²_𝓕(0, T; ℝⁿ)` and
for every `(φ, ψ) ∈ L²_𝓕(0, T; ℝⁿ) × (L²_𝓕(0, T; ℝⁿ))ᵈ` and every solution `z` of (12),
`E ∫₀ᵀ [(p, φ) + Σⱼ (Kⱼ, ψⱼ)] dt = E ∫₀ᵀ l_x(t) z(t) dt + E (h_x(y(T)) z(T))`. -/
def RepresentsI (cp : ControlProblem n k d) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ)
    (p : ℝ≥0 → Ω → Fin n → ℝ) (K : Fin d → ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  L2F 𝓕 P cp.T p ∧ (∀ j, L2F 𝓕 P cp.T (K j)) ∧
    ∀ (φ : ℝ≥0 → Ω → Fin n → ℝ) (ψ : Fin d → ℝ≥0 → Ω → Fin n → ℝ)
      (z : ℝ≥0 → Ω → Fin n → ℝ),
      L2F 𝓕 P cp.T φ → (∀ j, L2F 𝓕 P cp.T (ψ j)) → SolvesLinearFirst cp 𝓕 P B y u φ ψ z →
        ∫ ω, ∫ t in Set.Icc (0 : ℝ) cp.T,
            (p t.toNNReal ω ⬝ᵥ φ t.toNNReal ω
              + ∑ j, K j t.toNNReal ω ⬝ᵥ ψ j t.toNNReal ω) ∂volume ∂P
          = (∫ ω, ∫ t in Set.Icc (0 : ℝ) cp.T,
              lX cp (y t.toNNReal ω) (u t.toNNReal ω) ⬝ᵥ z t.toNNReal ω ∂volume ∂P)
            + ∫ ω, grad cp.h (y cp.T ω) ⬝ᵥ z cp.T ω ∂P

/-- The symmetric-matrix linear system before (16): `Z(0) = 0`,
`dZ = [Z g_x* + g_x Z + Σⱼ σʲ_x Z σʲ_x* + Φ] dt + Σⱼ [Z σʲ_x* + σʲ_x Z + ψⱼ] dBʲ`
(coefficients at `(y(t), u(t))`), read entrywise. -/
def SolvesLinearSecond (cp : ControlProblem n k d) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ)
    (Φ : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ) (Ψ : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (Z : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  SolvesSDE 𝓕 P cp.T B 0
    (fun s ω z => matEntries
      (entriesMat z * (gX cp (y s ω) (u s ω))ᵀ + gX cp (y s ω) (u s ω) * entriesMat z
        + ∑ j, σX cp j (y s ω) (u s ω) * entriesMat z * (σX cp j (y s ω) (u s ω))ᵀ
        + Φ s ω))
    (fun j s ω z => matEntries
      (entriesMat z * (σX cp j (y s ω) (u s ω))ᵀ + σX cp j (y s ω) (u s ω) * entriesMat z
        + Ψ j s ω))
    (fun s ω => matEntries (Z s ω))

/-- `(P, Q)` is the second-order adjoint process of (16)–(17) for the first-order adjoint
`(p, K)`: `P, Q₁, …, Q_d ∈ L²_𝓕(0, T; ℝ^{n,n})` with symmetric values on `[0, T]`, and for every
symmetric-matrix-valued `(Φ, Ψ) ∈ L²_𝓕 × (L²_𝓕)ᵈ` and every solution `Z` of the system before
(16), `M(Φ, Ψ) = E ∫₀ᵀ (Z, H_xx(t))_* dt + E (Z(T), h_xx(y(T)))_*` equals
`E ∫₀ᵀ [(P, Φ)_* + Σⱼ (Qⱼ, ψⱼ)_*] dt`, where `(A₁, A₂)_* = tr(A₁ A₂)` and
`H_xx(t) = H_xx(y(t), u(t), p(t), K(t))`. -/
def RepresentsM (cp : ControlProblem n k d) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ)
    (p : ℝ≥0 → Ω → Fin n → ℝ) (K : Fin d → ℝ≥0 → Ω → Fin n → ℝ)
    (Pm : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  L2F 𝓕 P cp.T (fun s ω => matEntries (Pm s ω)) ∧
    (∀ j, L2F 𝓕 P cp.T (fun s ω => matEntries (Q j s ω))) ∧
    (∀ t ≤ cp.T, ∀ ω, (Pm t ω).IsSymm) ∧ (∀ j, ∀ t ≤ cp.T, ∀ ω, (Q j t ω).IsSymm) ∧
    ∀ (Φ : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
      (Ψ : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
      (Z : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ),
      L2F 𝓕 P cp.T (fun s ω => matEntries (Φ s ω)) →
      (∀ j, L2F 𝓕 P cp.T (fun s ω => matEntries (Ψ j s ω))) →
      (∀ t ≤ cp.T, ∀ ω, (Φ t ω).IsSymm) → (∀ j, ∀ t ≤ cp.T, ∀ ω, (Ψ j t ω).IsSymm) →
      SolvesLinearSecond cp 𝓕 P B y u Φ Ψ Z →
        (∫ ω, ∫ t in Set.Icc (0 : ℝ) cp.T,
            Matrix.trace (Z t.toNNReal ω * hamXX cp (y t.toNNReal ω) (u t.toNNReal ω)
              (p t.toNNReal ω) (fun j => K j t.toNNReal ω)) ∂volume ∂P)
          + ∫ ω, Matrix.trace (Z cp.T ω * hess cp.h (y cp.T ω)) ∂P
          = ∫ ω, ∫ t in Set.Icc (0 : ℝ) cp.T,
              (Matrix.trace (Pm t.toNNReal ω * Φ t.toNNReal ω)
                + ∑ j, Matrix.trace (Q j t.toNNReal ω * Ψ j t.toNNReal ω)) ∂volume ∂P

/-- `(p, K)` solves the first-order adjoint equation (19):
`−dp = [g_x*(y, u) p + Σⱼ σʲ_x*(y, u) Kⱼ + l_x(y, u)] dt − Σⱼ Kⱼ dBʲ`, `p(T) = h_x(y(T))`. -/
def SolvesFirstAdjoint (cp : ControlProblem n k d) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ)
    (p : ℝ≥0 → Ω → Fin n → ℝ) (K : Fin d → ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesBSDE 𝓕 P cp.T B (fun ω => grad cp.h (y cp.T ω))
    (fun s ω p' K' => (gX cp (y s ω) (u s ω))ᵀ *ᵥ p'
      + ∑ j, (σX cp j (y s ω) (u s ω))ᵀ *ᵥ K' j + lX cp (y s ω) (u s ω))
    p K

/-- `(P, Q)` solves the second-order adjoint equation (20) (read entrywise):
`−dP = [g_x* P + P g_x + Σⱼ σʲ_x* P σʲ_x + Σⱼ σʲ_x* Qⱼ + Σⱼ Qⱼ σʲ_x + H_xx(y, u, p, K)] dt
       − Σⱼ Qⱼ dBʲ`, `P(T) = h_xx(y(T))`, all coefficients at `(y(t), u(t))`. -/
def SolvesSecondAdjoint (cp : ControlProblem n k d) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ)
    (p : ℝ≥0 → Ω → Fin n → ℝ) (K : Fin d → ℝ≥0 → Ω → Fin n → ℝ)
    (Pm : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  SolvesBSDE 𝓕 P cp.T B (fun ω => matEntries (hess cp.h (y cp.T ω)))
    (fun s ω P' Q' => matEntries
      ((gX cp (y s ω) (u s ω))ᵀ * entriesMat P' + entriesMat P' * gX cp (y s ω) (u s ω)
        + ∑ j, (σX cp j (y s ω) (u s ω))ᵀ * entriesMat P' * σX cp j (y s ω) (u s ω)
        + ∑ j, (σX cp j (y s ω) (u s ω))ᵀ * entriesMat (Q' j)
        + ∑ j, entriesMat (Q' j) * σX cp j (y s ω) (u s ω)
        + hamXX cp (y s ω) (u s ω) (p s ω) (fun j => K j s ω)))
    (fun s ω => matEntries (Pm s ω)) (fun j s ω => matEntries (Q j s ω))

end Peng1990.SMP


