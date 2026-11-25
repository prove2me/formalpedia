-- Prove2me | Definitions.Def_Arxiv1912_10252_Basic
-- name    : Arxiv1912_10252_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T07:01:30.878803+00:00
-- url     : https://prove2.me/theorems/88298383-9c4e-467b-888d-4593ae42e75b
-- title:
--   Steady-state two-port channel model of heat transfer (Li et al., Section IV)
-- statement:
--   The steady-state two-port model of Section IV of Li, Li, Qi, Qiu and Chen (arXiv:1912.10252), at leading order in the channel length $L$.
--
--   1. **Geometry and parameters.** A region $V$ is connected to two uniform channels of thermal conductivity $\kappa_c>0$ and cross-section $\sigma>0$. Channel 1 runs over $-L\le x\le x_1$ and channel 2 over $x_2\le x\le L$. The source points satisfy $x_a\le x_1$ and $x_b\ge x_2$. A point source has strength $Q_0$, and $H=\int_V h\,dV$ is the total heat generation in $V$, which does not depend on the conditions outside $V$.
--   2. **Green's functions in the channels (Eq. 15).** The steady-state Green's functions vanish at $x=\pm L$ and are piecewise linear in the channels. $G(x\mid x_a,0)$ has slopes $C_1(x_a)$ on $[-L,x_a]$, $D_1(x_a)$ on $[x_a,x_1]$ and $C_2(x_a)$ on $[x_2,L]$. $G(x\mid x_b,0)$ has slopes $C_1(x_b)$ on $[-L,x_1]$, $D_2(x_b)$ on $[x_2,x_b]$ and $C_2(x_b)$ on $[x_b,L]$. The six slopes are taken at their limiting values as $L\to\infty$.
--   3. **Energy conservation (Eq. 16).**
--   $$-\kappa_cD_1(x_a)\sigma=-\kappa_cC_2(x_a)\sigma+H,\qquad -\kappa_cC_1(x_b)\sigma=-\kappa_cD_2(x_b)\sigma+H,$$
--   $$-\kappa_c[C_1(x_a)-C_2(x_a)]\sigma=-\kappa_c[C_1(x_b)-C_2(x_b)]\sigma=Q_0+H.$$
--   4. **The matrix $\mathbf G$ (Eq. 17).** $\mathbf G=\begin{pmatrix}G(x_a\mid x_a,0)&G(x_a\mid x_b,0)\\G(x_b\mid x_a,0)&G(x_b\mid x_b,0)\end{pmatrix}$. By Eq. (15) its entries are $C_1(x_a)(x_a+L)$, $C_1(x_b)(x_a+L)$, $C_2(x_a)(x_b-L)$ and $C_2(x_b)(x_b-L)$. At leading order in $L$,
--   $$\mathbf G=L\begin{pmatrix}C_1(x_a)&C_1(x_b)\\-C_2(x_a)&-C_2(x_b)\end{pmatrix}.$$
--   5. **The flux matrix $\mathbf Q$ (Eq. 19).** $\mathbf Q=\kappa_c\begin{pmatrix}D_1(x_a)&C_1(x_b)\\C_2(x_a)&D_2(x_b)\end{pmatrix}$. It sends the coefficients $(f_a,f_b)$ of the superposition $F=f_aG(\cdot\mid x_a,0)+f_bG(\cdot\mid x_b,0)$ to the heat fluxes $(q_1,q_2)$ in the channels near the interfaces.
--   6. **Global reciprocity (Eq. 14, Section IV).** The system is steady-state globally reciprocal if $\mathbf G_{12}=\mathbf G_{21}$.
--   7. **Not a thermal diode (Eqs. 17, 22, 25).** Take any temperatures $T_1,T_2$. Let $\mathbf Gf=(T_1,T_2)^\top$ and $\mathbf G\tilde f=(T_2,T_1)^\top$. The system is not a thermal diode if, for every such choice, $\mathbf Q\tilde f=(-q_2,-q_1)^\top$, where $(q_1,q_2)^\top=\mathbf Qf$.
--
--   **Formalization Note** The paper takes the limit $L\to\infty$ when it passes from Eq. (17) to Eqs. (18) and (20). The definitions therefore record the slopes as numbers (their limits) and $\mathbf G$ by its leading-order term. Condition (25) is homogeneous in the fluxes, so it does not change when $\mathbf G$ is rescaled. The no-diode condition quantifies over coefficient vectors solving Eqs. (17) and (22) and does not use $\mathbf G^{-1}$ or $\mathbf Q^{-1}$. It is therefore meaningful when $H=0$ and $\mathbf Q$ is singular. Matrix indices $1,2$ of the paper are $0,1$ in Lean.
-- source:
--   Li, Li, Qi, Qiu and Chen, Diffusive non-reciprocity and thermal diode, arXiv:1912.10252v3 (2019), Section III, Eq. (14); Section IV, Eqs. (15)-(25), PDF pp. 5-7

import Mathlib

/-!
Ying Li, Jiaxin Li, Minghong Qi, Cheng-Wei Qiu and Hongsheng Chen, *Diffusive non-reciprocity and
thermal diode*, arXiv:1912.10252v3: the steady-state two-port channel model of Section IV
(Eqs. (15)-(25), PDF pp. 6-7), taken at leading order in the channel length `L` as `L → ∞`.

Channel 1 occupies `-L ≤ x ≤ x₁`, channel 2 occupies `x₂ ≤ x ≤ L`, and the source points satisfy
`x_a ≤ x₁`, `x_b ≥ x₂`. The steady-state Green's functions `G(x | x_a, 0)` and `G(x | x_b, 0)` are
piecewise linear in the channels, with slopes `C₁(x_a), D₁(x_a), C₂(x_a)` and
`C₁(x_b), D₂(x_b), C₂(x_b)` (Eq. (15)). The region `V` between the channels is a black box: it enters
only through these slopes, the energy balance (16), and the linearity used to superpose the two
Green's functions.
-/

noncomputable section

namespace Arxiv1912_10252

/-- Section IV, Eqs. (15)-(16), PDF p. 6: the parameters of the steady-state two-port model, with
`C₁(x_a)`, ... read as their limits as `L → ∞`. -/
structure TwoPortData where
  /-- `κ_c`, the thermal conductivity of the two channels. -/
  kc : ℝ
  /-- `σ`, the cross-section area of the channels. -/
  sigma : ℝ
  /-- `L`, the channel ends sit at `x = ±L`. -/
  L : ℝ
  /-- `Q₀`, the strength of the point source in Eq. (3). -/
  Q0 : ℝ
  /-- `H = ∫_V h(r) dV`, the total heat generation in `V`, independent of outside conditions. -/
  H : ℝ
  /-- `C₁(x_a)`, slope of `G(x | x_a, 0)` on `-L ≤ x ≤ x_a`. -/
  C1a : ℝ
  /-- `D₁(x_a)`, slope of `G(x | x_a, 0)` on `x_a ≤ x ≤ x₁`. -/
  D1a : ℝ
  /-- `C₂(x_a)`, slope of `G(x | x_a, 0)` on `x₂ ≤ x ≤ L`. -/
  C2a : ℝ
  /-- `C₁(x_b)`, slope of `G(x | x_b, 0)` on `-L ≤ x ≤ x₁`. -/
  C1b : ℝ
  /-- `D₂(x_b)`, slope of `G(x | x_b, 0)` on `x₂ ≤ x ≤ x_b`. -/
  D2b : ℝ
  /-- `C₂(x_b)`, slope of `G(x | x_b, 0)` on `x_b ≤ x ≤ L`. -/
  C2b : ℝ

/-- Section IV, Eq. (16), PDF p. 6: energy conservation for the two steady-state Green's functions
when the total heat generation `H` in `V` does not depend on the outside conditions. -/
def EnergyConservation (s : TwoPortData) : Prop :=
  -s.kc * s.D1a * s.sigma = -s.kc * s.C2a * s.sigma + s.H ∧
  -s.kc * s.C1b * s.sigma = -s.kc * s.D2b * s.sigma + s.H ∧
  -s.kc * (s.C1a - s.C2a) * s.sigma = s.Q0 + s.H ∧
  -s.kc * (s.C1b - s.C2b) * s.sigma = s.Q0 + s.H

/-- Section IV, Eq. (17) with Eq. (15), PDF p. 6: the matrix
`G = [[G(x_a|x_a,0), G(x_a|x_b,0)], [G(x_b|x_a,0), G(x_b|x_b,0)]]` at leading order in `L`.
Eq. (15) gives `G(x_a|x_a,0) = C₁(x_a)(x_a+L)`, `G(x_a|x_b,0) = C₁(x_b)(x_a+L)`,
`G(x_b|x_a,0) = C₂(x_a)(x_b-L)`, `G(x_b|x_b,0) = C₂(x_b)(x_b-L)`; as `L → ∞` these are
`C₁(x_a)L`, `C₁(x_b)L`, `-C₂(x_a)L`, `-C₂(x_b)L`. -/
def greenMat (s : TwoPortData) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![s.C1a * s.L, s.C1b * s.L; -(s.C2a * s.L), -(s.C2b * s.L)]

/-- Section IV, Eq. (19), PDF p. 6: the matrix `Q = κ_c [[D₁(x_a), C₁(x_b)], [C₂(x_a), D₂(x_b)]]`
sending the superposition coefficients `(f_a, f_b)` to the heat fluxes `(q₁, q₂)` in the channels
near the interfaces `S₁`, `S₂`. -/
def fluxMat (s : TwoPortData) : Matrix (Fin 2) (Fin 2) ℝ :=
  s.kc • !![s.D1a, s.C1b; s.C2a, s.D2b]

/-- Section III, Eq. (14), and Section IV, PDF p. 7: steady-state global reciprocity of the two-port
system, `G₁₂ = G₂₁`. -/
def IsGloballyReciprocal (s : TwoPortData) : Prop :=
  greenMat s 0 1 = greenMat s 1 0

/-- Section IV, Eqs. (17), (22), (25), PDF pp. 6-7: the system is not a thermal diode. For all
temperatures `T₁, T₂`, if the coefficients `f = (f_a, f_b)` give `F(x_a) = T₁`, `F(x_b) = T₂`
(Eq. (17)) and `f̃` gives the swapped temperatures (Eq. (22)), then the new fluxes
`(q̃₁, q̃₂) = Q f̃` equal `(-q₂, -q₁)`, where `(q₁, q₂) = Q f` (Eq. (25)). -/
def IsNotDiode (s : TwoPortData) : Prop :=
  ∀ (T1 T2 : ℝ) (f f' : Fin 2 → ℝ),
    (greenMat s).mulVec f = ![T1, T2] → (greenMat s).mulVec f' = ![T2, T1] →
      (fluxMat s).mulVec f' = ![-((fluxMat s).mulVec f 1), -((fluxMat s).mulVec f 0)]

end Arxiv1912_10252


