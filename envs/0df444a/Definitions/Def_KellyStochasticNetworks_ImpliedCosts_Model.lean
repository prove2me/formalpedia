-- Prove2me | Definitions.Def_KellyStochasticNetworks_ImpliedCosts_Model
-- name    : KellyStochasticNetworks_ImpliedCosts_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:47:35.187005+00:00
-- url     : https://prove2.me/theorems/74ffb312-65bd-4778-b5ee-0015f84a199b
-- title:
--   Fixed-point revenue, interpolated capacity, and implied costs
-- statement:
--   Let $J$ and $R$ be finite numbers of links and routes, $A_{jr}$ a nonnegative integer circuit requirement, $\nu_r$ an offered traffic rate, and $w_r$ the worth of a carried call. Write $E(\rho,n)$ for the published scalar Erlang formula. For a real capacity $x\ge0$, put $n=\lfloor x\rfloor$ and interpolate linearly:
--   $$\widetilde E(\rho,x)=(1-x+n)E(\rho,n)+(x-n)E(\rho,n+1).$$
--   For a blocking vector $B$, define acceptance $a_r=\prod_j(1-B_j)^{A_{jr}}$, carried traffic $\lambda_r=\nu_ra_r$, carried circuit load $q_j=\sum_rA_{jr}\lambda_r$, and reduced load $\rho_j=q_j/(1-B_j)$. A physical interpolated fixed point satisfies $0\le B_j<1$ and $B_j=\widetilde E(\rho_j,C_j)$. Select such a fixed point when one exists, and define revenue by
--   $$W(\nu;C)=\sum_r w_r\nu_r\prod_j(1-B_j(\nu,C))^{A_{jr}}.$$
--   At integer capacity define $\delta_j=\rho_j[E(\rho_j,C_j-1)-E(\rho_j,C_j)]$. The surplus is $s_r=w_r-\sum_jc_jA_{jr}$, and the cost system consists of this equation together with
--   $$c_j=\delta_j\frac{\sum_r A_{jr}\lambda_r(s_r+c_j)}{q_j}.$$
--   For Exercise 4.9 also define $\Lambda=\operatorname{diag}(\lambda_r)$, $\Gamma=\operatorname{diag}(\delta_j/[(1-\delta_j)q_j])$, $H=\Gamma^{1/2}$, $Q=I+HA\Lambda A^TH$, and the row vector $c_*=w\Lambda A^THQ^{-1}H$.
--
--   These definitions specify the fixed-point approximation and its local cost system independently of any derivative claim.
--
--   **Formalization Note** Indices are zero-based finite types and all traffic, value, and probability coordinates are real. The selector returns zero when no physical fixed point exists; the goal establishes the physical integer-capacity fixed point rather than assuming this fallback is valid. Definitions are total outside their intended domain: negative capacities use the truncated natural floor, natural subtraction is truncated, and real division by zero and a singular matrix inverse are totalized. The theorem domains require positive integer capacities, positive traffic, and every link used, and Exercise 4.9 establishes positive link loads, $0\le\delta_j<1$, and invertibility. No smoothness or sensitivity property is assumed in the definition.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed pp. 102–103, 106–107 (PDF pp. 110–111, 114–115), Eqs. (4.1)–(4.8) and Exercise 4.9; https://doi.org/10.1017/CBO9781139565363

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyStochasticNetworks_LossNetwork

namespace KellyStochasticNetworks.ImpliedCosts

/-- Linear interpolation in capacity, including the left-hand interval at a positive
integer. Values at negative capacities are an unused total extension. -/
noncomputable def interpolatedErlang (ρ x : ℝ) : ℝ :=
  let n := Nat.floor x
  (1 - (x - (n : ℝ))) * erlang ρ n + (x - (n : ℝ)) * erlang ρ (n + 1)

/-- Route acceptance in the independent-link approximation (4.4). -/
noncomputable def acceptance {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (B : Fin J → ℝ) (r : Fin R) : ℝ :=
  ∏ j, (1 - B j) ^ A j r

/-- Carried traffic, not the exact stationary traffic of the loss process. -/
noncomputable def carried {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (B : Fin J → ℝ) (r : Fin R) : ℝ :=
  ν r * acceptance A B r

noncomputable def linkLoad {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (lam : Fin R → ℝ) (j : Fin J) : ℝ :=
  ∑ r, (A j r : ℝ) * lam r

/-- Reduced offered load (4.2). -/
noncomputable def reducedLoad {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (B : Fin J → ℝ) (j : Fin J) : ℝ :=
  (1 - B j)⁻¹ * linkLoad A (carried A ν B) j

/-- The real-capacity extension of the published `ErlangFixedPoint` relation.
The range condition specifies physical blocking probabilities. -/
def InterpolatedFixedPoint {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C B : Fin J → ℝ) : Prop :=
  (∀ j, B j ∈ Set.Ico (0 : ℝ) 1) ∧
    ∀ j, B j = interpolatedErlang (reducedLoad A ν B j) (C j)

/-- Choose a physical fixed point of the actual equations, or zero if none exists.
No continuity, derivative, cost identity, or existence theorem is built into this definition. -/
noncomputable def blocking {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℝ) : Fin J → ℝ := by
  classical
  exact if h : ∃ B, InterpolatedFixedPoint A ν C B then Classical.choose h else 0

/-- Fixed-point revenue, with the scalar interpolation used before solving the network. -/
noncomputable def revenue {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (w ν : Fin R → ℝ) (C : Fin J → ℝ) : ℝ :=
  ∑ r, w r * carried A ν (blocking A ν C) r

/-- Erlang's improvement quantity at a positive integer capacity (printed p. 103). -/
noncomputable def improvement {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (B : Fin J → ℝ) (j : Fin J) : ℝ :=
  let ρ := reducedLoad A ν B j
  ρ * (erlang ρ (C j - 1) - erlang ρ (C j))

noncomputable def surplus {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (w : Fin R → ℝ) (c : Fin J → ℝ) (r : Fin R) : ℝ :=
  w r - ∑ j, c j * (A j r : ℝ)

/-- Equations (4.7) and (4.8). The theorem statements ensure every link has positive
carried load; the displayed quotient is not interpreted as a zero-load convention. -/
def CostSystem {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (w lam : Fin R → ℝ) (δ : Fin J → ℝ) (s : Fin R → ℝ) (c : Fin J → ℝ) : Prop :=
  s = surplus A w c ∧
    ∀ j, c j = δ j * (∑ r, (A j r : ℝ) * lam r * (s r + c j)) / linkLoad A lam j

noncomputable def incidence {J R : ℕ} (A : Fin J → Fin R → ℕ) :
    Matrix (Fin J) (Fin R) ℝ := fun j r => (A j r : ℝ)

noncomputable def gamma {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (lam : Fin R → ℝ) (δ : Fin J → ℝ) (j : Fin J) : ℝ :=
  δ j / ((1 - δ j) * linkLoad A lam j)

/-- The symmetric matrix in Exercise 4.9. -/
noncomputable def symmetricCostMatrix {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (lam : Fin R → ℝ) (δ : Fin J → ℝ) : Matrix (Fin J) (Fin J) ℝ :=
  let H := Matrix.diagonal (fun j => Real.sqrt (gamma A lam δ j))
  1 + H * incidence A * Matrix.diagonal lam * (incidence A).transpose * H

/-- The row-vector formula for c in Exercise 4.9, using the nonsingular matrix inverse. -/
noncomputable def explicitCosts {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (w lam : Fin R → ℝ) (δ : Fin J → ℝ) : Fin J → ℝ :=
  let H := Matrix.diagonal (fun j => Real.sqrt (gamma A lam δ j))
  Matrix.vecMul w (Matrix.diagonal lam * (incidence A).transpose * H *
    (symmetricCostMatrix A lam δ)⁻¹ * H)

end KellyStochasticNetworks.ImpliedCosts


