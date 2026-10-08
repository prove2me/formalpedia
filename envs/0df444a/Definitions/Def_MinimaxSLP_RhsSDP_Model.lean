-- Prove2me | Definitions.Def_MinimaxSLP_RhsSDP_Model
-- name    : MinimaxSLP_RhsSDP_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:26.177827+00:00
-- url     : https://prove2.me/theorems/5b3b21e8-1ba6-41ab-972b-5bfdf3310f12
-- title:
--   The model of §1 and §3: X, 𝒬(h, x), 𝕌, the moment class 𝒫 (10), Ẑ(x), the duals (12) and (15), the joint SDP (14) and Z
-- statement:
--   This file fixes the objects of the two-stage minimax stochastic linear program with a random right-hand side, a constant objective and a piecewise-linear disutility, together with the dual programs (12) and (15) and the joint semidefinite program (14).
--
--   **First and second stage.** For $A\in\mathbb R^{m_1\times n}$ and $b\in\mathbb R^{m_1}$ the first-stage feasible region is $X=\{x\in\mathbb R^n : Ax=b,\ x\ge 0\}$. For a recourse matrix $W\in\mathbb R^{r\times d}$, a technology matrix $T\in\mathbb R^{r\times n}$, a constant objective $q\in\mathbb R^d$ and a right-hand side $h\in\mathbb R^r$, the second-stage cost is the optimal value of the dual linear program
--   $$
--   \mathcal Q(h,x)=\max_{p}\ (h-Tx)'p\quad\text{s.t.}\quad W'p\le q .
--   $$
--
--   **Disutility.** For coefficients $\alpha_1,\dots,\alpha_K$ and $\beta_1,\dots,\beta_K$ ($K\ge 1$), $\mathbb U(t)=\max_{k=1,\dots,K}(\alpha_k t+\beta_k)$.
--
--   **Moment class and worst-case value.** For $\mu\in\mathbb R^r$ and $Q\in\mathbb R^{r\times r}$, the class $\mathcal P$ of (10) consists of the probability distributions $P$ of $\tilde h$ on $\mathbb R^r$ with finite second moments, $\mathbb E_P[\tilde h]=\mu$ and $\mathbb E_P[\tilde h\tilde h']=Q$. The worst-case expected disutility, the value of the moment problem (11), is
--   $$
--   \hat Z(x)=\sup_{P\in\mathcal P}\mathbb E_P\big[\mathbb U(\mathcal Q(\tilde h,x))\big].
--   $$
--
--   **The dual (12).** With the Frobenius product $Q\cdot Y=\sum_{i,j}Q_{ij}Y_{ij}$,
--   $$
--   \hat Z_D(x)=\min_{Y,y,y_0}\ Q\cdot Y+\mu'y+y_0\quad\text{s.t.}\quad h'Yh+y'h+y_0\ge\mathbb U(\mathcal Q(h,x))\ \ \forall h\in\mathbb R^r ,
--   $$
--   over symmetric $Y\in\mathbb R^{r\times r}$, $y\in\mathbb R^r$, $y_0\in\mathbb R$.
--
--   **The programs (15) and (14).** Let $p_1,\dots,p_N\in\mathbb R^r$ be the extreme points of $\{p : W'p\le q\}$ (Assumption 5). For a piece $k$ and an extreme point $p_i$ write
--   $$
--   M_{k,i}(x,Y,y,y_0)=\begin{pmatrix}Y & \tfrac12(y-\alpha_k p_i)\\ \tfrac12(y-\alpha_k p_i)' & y_0+\alpha_k p_i'Tx-\beta_k\end{pmatrix}.
--   $$
--   The program (15) minimizes $Q\cdot Y+\mu'y+y_0$ subject to $M_{k,i}(x,Y,y,y_0)\succeq 0$ for all $k=1,\dots,K$ and $i=1,\dots,N$. The joint program (14) is
--   $$
--   \hat Z_{\rm SDP}=\min_{x,Y,y,y_0}\ c'x+Q\cdot Y+\mu'y+y_0\quad\text{s.t.}\quad M_{k,i}(x,Y,y,y_0)\succeq 0\ \ \forall k,i,\qquad Ax=b,\ x\ge 0 .
--   $$
--   Finally $Z=\min_{x\in X}\big(c'x+\hat Z(x)\big)$ is the optimal value of the risk-averse minimax problem (2) with random right-hand side.
--
--   These are the objects of Theorem 3.2, which asserts $Z=\hat Z_{\rm SDP}$.
--
--   **Formalization Note** The paper writes $p$ both for the dimension of $q$ and $w$ and for the dual vector; here the dimension is $d$ and the dual vector is `π` (or `ps i` for the extreme points). Indices $k,i$ run over `Fin K`, `Fin N` (zero-based). The moment class is built from the published `MomentDRO.Conf.HasSecondMoments`, `meanVec` and `secondMomentAbout P 0` (the uncentred second moment), on measures rather than the densities of (11). $\mathcal Q(h,x)$ is the real supremum of $(h-Tx)'p$ over the dual polyhedron; it is attained and finite under Assumptions 2 and 3, and statements never rely on its junk value. Every printed min/max is a real `sInf`/`sSup` of the set of objective values; the theorems state as `IsLUB`/`IsGLB` that these are genuine finite bounds, and attainment is not claimed. $Y$ is required symmetric in (12), (14) and (15), which changes no optimal value since $Q$ is symmetric. The bordered matrix is the published `WorstCaseVaR.KnownMoments.bordered`, indexed by `Fin r ⊕ Fin 1`, and $\succeq 0$ is `Matrix.PosSemidef`. The first-stage region $X$, the disutility $\mathbb U$, the moment class $\mathcal P$ and the Frobenius product are not redefined here: they are the objects `X`, `disutility`, `momentClass` and `frob` of the companion definition `MinimaxSLP.ObjSDP.Model` (§1–2), which this file imports; the class (10) is that construction taken on $\mathbb R^r$.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, pp. 580–590: (2) and (3) (p. 581), X (p. 582, Assumption 1), (10) and 𝒬(h̃, x) (p. 587), (11) and (12) (p. 588), Assumption 5, (14) and (15) (p. 589)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic
import Definitions.Def_MinimaxSLP_ObjSDP_Model

namespace MinimaxSLP.RhsSDP

open MeasureTheory Matrix

/-- Second-stage value in the §3 form (p. 587): `𝒬(h, x) = max_π (h − T x)′π s.t. W′π ≤ q`,
as a real supremum. Here `W ∈ ℝ^{r×d}` (`d` is the paper's dimension `p` of `q` and `w`),
`T ∈ ℝ^{r×n}`, the constant objective is `q ∈ ℝ^d` and the dual variable is `π ∈ ℝ^r` (the
paper's `p`). Under complete recourse (Assumption 2) and `{π : W′π ≤ q} ≠ ∅` (Assumption 3 at
`q`) the supremum is attained and finite; otherwise it is the junk value of `sSup`, which no
statement uses. -/
noncomputable def Qval {r d n : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (q : Fin d → ℝ) (h : Fin r → ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup ((fun π => (h - T *ᵥ x) ⬝ᵥ π) '' {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})

/-- The values `E_P[𝕌(𝒬(h̃, x))]`, `P ∈ 𝒫`, of the primal moment problem (11), p. 588. -/
noncomputable def primalValues {r d n K : ℕ} [NeZero K] (W : Matrix (Fin r) (Fin d) ℝ)
    (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ) (α β : Fin K → ℝ) (μ : Fin r → ℝ)
    (Q : Matrix (Fin r) (Fin r) ℝ) (x : Fin n → ℝ) : Set ℝ :=
  (fun P => ∫ h, MinimaxSLP.ObjSDP.disutility α β (Qval W T q h x) ∂P) '' MinimaxSLP.ObjSDP.momentClass μ Q

/-- Worst-case expected disutility `Ẑ(x) = sup_{P ∈ 𝒫} E_P[𝕌(𝒬(h̃, x))]`, the value of (11),
p. 588, as the real supremum of `primalValues`. -/
noncomputable def Zhat {r d n K : ℕ} [NeZero K] (W : Matrix (Fin r) (Fin d) ℝ)
    (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ) (α β : Fin K → ℝ) (μ : Fin r → ℝ)
    (Q : Matrix (Fin r) (Fin r) ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup (primalValues W T q α β μ Q x)

/-- Objective `Q · Y + μ′y + y₀` of the duals (12) and (15), at a point `s = (Y, y, y₀)`. -/
def dualObj {r : ℕ} (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (s : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) : ℝ :=
  MinimaxSLP.ObjSDP.frob Q s.1 + μ ⬝ᵥ s.2.1 + s.2.2

/-- Feasible set of the dual (12), p. 588: `(Y, y, y₀)` with `Y` symmetric and
`h′Yh + y′h + y₀ ≥ 𝕌(𝒬(h, x))` for every `h ∈ ℝʳ`. -/
def dualFeasible12 {r d n K : ℕ} [NeZero K] (W : Matrix (Fin r) (Fin d) ℝ)
    (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ) (α β : Fin K → ℝ) (x : Fin n → ℝ) :
    Set (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) :=
  {s | s.1.IsSymm ∧
    ∀ h : Fin r → ℝ, MinimaxSLP.ObjSDP.disutility α β (Qval W T q h x) ≤ h ⬝ᵥ (s.1 *ᵥ h) + s.2.1 ⬝ᵥ h + s.2.2}

/-- `Ẑ_D(x)`, the optimal value of (12), p. 588, as the real infimum of the objective over
`dualFeasible12` (the printed `min` read as an infimum). -/
noncomputable def ZhatD {r d n K : ℕ} [NeZero K] (W : Matrix (Fin r) (Fin d) ℝ)
    (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ) (α β : Fin K → ℝ) (μ : Fin r → ℝ)
    (Q : Matrix (Fin r) (Fin r) ℝ) (x : Fin n → ℝ) : ℝ :=
  sInf (dualObj μ Q '' dualFeasible12 W T q α β x)

/-- The bordered matrix of (14)/(15), pp. 589–590, for one piece `(a, b) = (α_k, β_k)` and one
dual extreme point `p = p_i`:
`( Y  ½(y − a p) ; ½(y − a p)′  y₀ + a p′T x − b )`, indexed by `Fin r ⊕ Fin 1`
(built with the published `WorstCaseVaR.KnownMoments.bordered`). -/
noncomputable def bordered15 {r n : ℕ} (T : Matrix (Fin r) (Fin n) ℝ) (Y : Matrix (Fin r) (Fin r) ℝ)
    (y : Fin r → ℝ) (y₀ a b : ℝ) (p : Fin r → ℝ) (x : Fin n → ℝ) :
    Matrix (Fin r ⊕ Fin 1) (Fin r ⊕ Fin 1) ℝ :=
  WorstCaseVaR.KnownMoments.bordered Y ((1 / 2 : ℝ) • (y - a • p))
    (y₀ + a * (p ⬝ᵥ (T *ᵥ x)) - b)

/-- Feasible set of (15), p. 589: `(Y, y, y₀)` with `Y` symmetric and, for every piece
`k ∈ Fin K` and every extreme point `i ∈ Fin N` (`ps : Fin N → ℝʳ`, Assumption 5), the bordered
matrix `bordered15` positive semidefinite. -/
def feasible15 {r n K N : ℕ} (T : Matrix (Fin r) (Fin n) ℝ) (α β : Fin K → ℝ)
    (ps : Fin N → Fin r → ℝ) (x : Fin n → ℝ) :
    Set (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) :=
  {s | s.1.IsSymm ∧
    ∀ k i, (bordered15 T s.1 s.2.1 s.2.2 (α k) (β k) (ps i) x).PosSemidef}

/-- The optimal value of (15), p. 589, as the real infimum of `Q · Y + μ′y + y₀` over
`feasible15`. -/
noncomputable def ZhatD15 {r n K N : ℕ} (T : Matrix (Fin r) (Fin n) ℝ) (α β : Fin K → ℝ)
    (ps : Fin N → Fin r → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ) (x : Fin n → ℝ) : ℝ :=
  sInf (dualObj μ Q '' feasible15 T α β ps x)

/-- Feasible set of the joint semidefinite program (14), p. 589: points `(x, Y, y, y₀)` with
`A x = b`, `x ≥ 0`, `Y` symmetric and every bordered matrix `bordered15` (which contains `x`
in its corner entry `y₀ + α_k p_i′T x − β_k`) positive semidefinite. -/
def feasible14 {m₁ n r K N : ℕ} (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (T : Matrix (Fin r) (Fin n) ℝ) (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ) :
    Set ((Fin n → ℝ) × Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) :=
  {z | A *ᵥ z.1 = b ∧ 0 ≤ z.1 ∧ z.2.1.IsSymm ∧
    ∀ k i, (bordered15 T z.2.1 z.2.2.1 z.2.2.2 (α k) (β k) (ps i) z.1).PosSemidef}

/-- Objective of (14): `c′x + Q · Y + μ′y + y₀`. -/
def obj14 {n r : ℕ} (c : Fin n → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (z : (Fin n → ℝ) × Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) : ℝ :=
  c ⬝ᵥ z.1 + dualObj μ Q z.2

/-- `Ẑ_SDP`, the optimal value of (14), p. 589, as the real infimum of `obj14` over
`feasible14` (the printed `min` read as an infimum). -/
noncomputable def ZhatSDP {m₁ n r K N : ℕ} (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (c : Fin n → ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ)
    (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  sInf (obj14 c μ Q '' feasible14 A b T α β ps)

/-- Objective `c′x + Ẑ(x)` of the risk-averse minimax problem (2) with random right-hand
side, `min_{x ∈ X} (c′x + sup_{P ∈ 𝒫} E_P[𝕌(𝒬(h̃, x))])` (pp. 581, 588). -/
noncomputable def minimaxObj {n r d K : ℕ} [NeZero K] (c : Fin n → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ) (x : Fin n → ℝ) : ℝ :=
  c ⬝ᵥ x + Zhat W T q α β μ Q x

/-- `Z`, the optimal value of the minimax problem (2), as the real infimum of `c′x + Ẑ(x)`
over `X` (the printed `min` read as an infimum). -/
noncomputable def Zval {m₁ n r d K : ℕ} [NeZero K] (A : Matrix (Fin m₁) (Fin n) ℝ)
    (b : Fin m₁ → ℝ) (c : Fin n → ℝ) (W : Matrix (Fin r) (Fin d) ℝ)
    (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ) (α β : Fin K → ℝ) (μ : Fin r → ℝ)
    (Q : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  sInf (minimaxObj c W T q α β μ Q '' MinimaxSLP.ObjSDP.X A b)

end MinimaxSLP.RhsSDP


