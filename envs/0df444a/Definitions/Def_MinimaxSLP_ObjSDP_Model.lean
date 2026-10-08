-- Prove2me | Definitions.Def_MinimaxSLP_ObjSDP_Model
-- name    : MinimaxSLP_ObjSDP_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:14.590301+00:00
-- url     : https://prove2.me/theorems/747032c3-da40-4287-80fc-67b109a8f5e2
-- title:
--   The model of §1–2.1: X, X(x), 𝒬(q, x), 𝕌, the moment class 𝒫 (4), Z(x) and Z of (2), the dual (6), and the semidefinite programs (8) and (7)
-- statement:
--   This file fixes the objects of the two-stage minimax stochastic linear program with random objective and a piecewise-linear disutility, together with the three optimization problems that Theorem 2.1 relates.
--
--   **First and second stage.** For $A\in\mathbb R^{m_1\times n}$, $b\in\mathbb R^{m_1}$ and $c\in\mathbb R^n$ the first-stage feasible region is $X=\{x\in\mathbb R^n : Ax=b,\ x\ge 0\}$. For a recourse matrix $W\in\mathbb R^{r\times d}$, a technology matrix $T\in\mathbb R^{r\times n}$ and $h\in\mathbb R^r$, the recourse set of $x$ is
--   $$
--   X(x)=\{w\in\mathbb R^{d} : Ww=h-Tx,\ w\ge 0\},
--   $$
--   and the second-stage cost of an objective vector $q\in\mathbb R^d$ is the optimal value of a linear program,
--   $$
--   \mathcal Q(q,x)=\min_{w}\ q'w\quad\text{s.t.}\quad Ww=h-Tx,\ w\ge 0 .
--   $$
--
--   **Disutility.** For coefficients $\alpha_1,\dots,\alpha_K$ and $\beta_1,\dots,\beta_K$ ($K\ge 1$), the disutility is $\mathbb U(t)=\max_{k=1,\dots,K}(\alpha_k t+\beta_k)$.
--
--   **Moment class and the problem (2).** For $\mu\in\mathbb R^d$ and $Q\in\mathbb R^{d\times d}$, the class $\mathcal P$ of (4) consists of the probability distributions $P$ of the random objective $\tilde q$ on $\mathbb R^d$ with finite second moments, $\mathbb E_P[\tilde q]=\mu$ and $\mathbb E_P[\tilde q\tilde q']=Q$. The worst-case expected disutility of $x$ and the optimal value of problem (2) are
--   $$
--   Z(x)=\sup_{P\in\mathcal P}\mathbb E_P\big[\mathbb U(\mathcal Q(\tilde q,x))\big],\qquad Z=\min_{x\in X}\big(c'x+Z(x)\big).
--   $$
--
--   **The dual (6).** With the Frobenius product $Q\cdot Y=\sum_{i,j}Q_{ij}Y_{ij}$,
--   $$
--   Z_D(x)=\min_{Y,y,y_0}\ Q\cdot Y+\mu'y+y_0\quad\text{s.t.}\quad q'Yq+q'y+y_0\ge \mathbb U(\mathcal Q(q,x))\ \ \forall q\in\mathbb R^d,
--   $$
--   over symmetric $Y\in\mathbb S^{d\times d}$, $y\in\mathbb R^d$, $y_0\in\mathbb R$.
--
--   **The semidefinite programs (8) and (7).** Write
--   $$
--   M_k(Y,y,y_0,w_k)=\begin{pmatrix}Y & \tfrac12(y-\alpha_k w_k)\\ \tfrac12(y-\alpha_k w_k)' & y_0-\beta_k\end{pmatrix}.
--   $$
--   Problem (8) minimizes $Q\cdot Y+\mu'y+y_0$ over $(Y,y,y_0,w_1,\dots,w_K)$ subject to $M_k\succeq 0$, $Ww_k+Tx=h$ and $w_k\ge 0$ for every $k$, with $x$ fixed. Problem (7) is one program over $(x,Y,y,y_0,w_1,\dots,w_K)$ jointly:
--   $$
--   Z_{\mathrm{SDP}}=\min\ c'x+Q\cdot Y+\mu'y+y_0\quad\text{s.t.}\quad M_k\succeq 0,\ Ww_k+Tx=h,\ w_k\ge 0\ (k=1,\dots,K),\quad Ax=b,\ x\ge 0 .
--   $$
--
--   These are the objects about which Theorem 2.1 and the steps of its proof are stated.
--
--   **Formalization Note** The paper writes $p$ both for the dimension of $q$ and $w$ and for the dual vector of the second-stage LP; here the dimension is $d$ and dual vectors are `π`. The paper's "$X(x):=\{x\in\mathbb R^n:\dots\}$" (p. 580) is a typo for $w\in\mathbb R^d$. Indices $k$ run over `Fin K` (zero-based). The moment class is built from the published `MomentDRO.Conf.HasSecondMoments`, `meanVec` and `secondMomentAbout P 0` (the uncentred second moment), on measures rather than the densities $f$ of the paper's (5). Every printed min/max is a real `sInf`/`sSup` of the set of objective values (`primalValues`, `firstStageValues`, `dualValues6`, `dualValues8`, `values7`); $\mathcal Q(q,x)$ is the real infimum of $q'w$ over $X(x)$, attained and finite whenever $X(x)\neq\emptyset$ and Assumption 3 holds, and the junk value $0$ otherwise. The theorems never rely on junk values: they carry those hypotheses and assert `IsLUB`/`IsGLB` where an optimal value is used. Bordered matrices are `Matrix.fromBlocks` indexed by `Fin d ⊕ Fin 1` and $\succeq 0$ is `Matrix.PosSemidef` (which includes symmetry). (7) is defined as one joint program, not through $Z_D(x)$. This file is shared by the whole series: the definitions of the missions on Theorem 2.2 (`MinimaxSLP.ObjExtremal`), Theorem 3.2 (`MinimaxSLP.RhsSDP`) and Theorem 3.3 (`MinimaxSLP.RhsExtremal`) import it rather than restating $X$, $X(x)$, $\mathcal Q$, $\mathbb U$, $\mathcal P$ and the Frobenius product.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, pp. 580–584: X and X(x) (p. 580), (2)–(3) (p. 581), (4) and 𝒬(q̃, x) (p. 582), (5)–(7) (pp. 582–583), (8) (p. 584)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting

namespace MinimaxSLP.ObjSDP

open MeasureTheory Matrix

/-- First-stage feasible region `X = {x ∈ ℝⁿ : A x = b, x ≥ 0}` (p. 580). -/
def X {m₁ n : ℕ} (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ) : Set (Fin n → ℝ) :=
  {x | A *ᵥ x = b ∧ 0 ≤ x}

/-- Recourse set `X(x) = {w ∈ ℝ^d : W w = h − T x, w ≥ 0}` (p. 580; the paper's `x ∈ ℝⁿ`
there is a typo for `w ∈ ℝ^d`, `d` being the paper's dimension `p` of `q` and `w`). -/
def recourseSet {r d n : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (h : Fin r → ℝ) (x : Fin n → ℝ) : Set (Fin d → ℝ) :=
  {w | W *ᵥ w = h - T *ᵥ x ∧ 0 ≤ w}

/-- Second-stage value `𝒬(q, x) = min_w q′w s.t. W w = h − T x, w ≥ 0` (p. 582), as a real
infimum. Under the §2 hypotheses (`X(x) ≠ ∅`, Assumption 3 for all `q`) it is attained and finite;
it is the junk value `0` only when `X(x) = ∅` or the LP is unbounded, which no statement uses. -/
noncomputable def Qval {r d n : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (h : Fin r → ℝ) (q : Fin d → ℝ) (x : Fin n → ℝ) : ℝ :=
  sInf ((fun w => q ⬝ᵥ w) '' recourseSet W T h x)

/-- Piecewise-linear disutility (3), p. 581: `𝕌(t) = max_k (α_k t + β_k)`, pieces indexed by
`Fin K` (zero-based). -/
noncomputable def disutility {K : ℕ} [NeZero K] (α β : Fin K → ℝ) (t : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun k => α k * t + β k)

/-- The moment class (4), p. 582: probability measures on `ℝ^d` with finite second moments,
mean `μ` and uncentred second-moment matrix `E[q q′] = Q`. -/
def momentClass {d : ℕ} (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) :
    Set (Measure (Fin d → ℝ)) :=
  {P | MomentDRO.Conf.HasSecondMoments P ∧ MomentDRO.Conf.meanVec P = μ ∧
    MomentDRO.Conf.secondMomentAbout P 0 = Q}

/-- The values `E_P[𝕌(𝒬(q̃, x))]`, `P ∈ 𝒫`, of the primal moment problem (5), p. 582. -/
noncomputable def primalValues {r d n K : ℕ} [NeZero K] (W : Matrix (Fin r) (Fin d) ℝ)
    (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ) (α β : Fin K → ℝ) (μ : Fin d → ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ) (x : Fin n → ℝ) : Set ℝ :=
  (fun P => ∫ q, disutility α β (Qval W T h q x) ∂P) '' momentClass μ Q

/-- Worst-case expected disutility `Z(x) = sup_{P ∈ 𝒫} E_P[𝕌(𝒬(q̃, x))]` (p. 582, (5)). -/
noncomputable def Zx {r d n K : ℕ} [NeZero K] (W : Matrix (Fin r) (Fin d) ℝ)
    (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ) (α β : Fin K → ℝ) (μ : Fin d → ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup (primalValues W T h α β μ Q x)

/-- The objective values `c′x + Z(x)`, `x ∈ X`, of problem (2), p. 581. -/
noncomputable def firstStageValues {m₁ n r d K : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ) (c : Fin n → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) : Set ℝ :=
  (fun x => c ⬝ᵥ x + Zx W T h α β μ Q x) '' X A b

/-- `Z = min_{x ∈ X} (c′x + sup_{P ∈ 𝒫} E_P[𝕌(𝒬(q̃, x))])`, problem (2), p. 581 (the printed
`min` read as an infimum). -/
noncomputable def Z {m₁ n r d K : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ) (c : Fin n → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sInf (firstStageValues A b c W T h α β μ Q)

/-- Frobenius product `Q · Y = Σ_{i,j} Q_ij Y_ij`. -/
def frob {d : ℕ} (Q Y : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, ∑ j, Q i j * Y i j

/-- Feasible set of the dual (6), p. 583: `Y` symmetric, `y ∈ ℝ^d`, `y₀ ∈ ℝ` with
`q′Yq + q′y + y₀ ≥ 𝕌(𝒬(q, x))` for every `q ∈ ℝ^d`. -/
def dualFeasible6 {r d n K : ℕ} [NeZero K] (W : Matrix (Fin r) (Fin d) ℝ)
    (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ) (α β : Fin K → ℝ) (x : Fin n → ℝ) :
    Set (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × ℝ) :=
  {s | s.1.IsSymm ∧ ∀ q : Fin d → ℝ,
    disutility α β (Qval W T h q x) ≤ q ⬝ᵥ (s.1 *ᵥ q) + q ⬝ᵥ s.2.1 + s.2.2}

/-- Objective values `Q · Y + μ′y + y₀` of the feasible points of (6). -/
def dualValues6 {r d n K : ℕ} [NeZero K] (W : Matrix (Fin r) (Fin d) ℝ)
    (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ) (α β : Fin K → ℝ) (μ : Fin d → ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ) (x : Fin n → ℝ) : Set ℝ :=
  (fun s : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × ℝ => frob Q s.1 + μ ⬝ᵥ s.2.1 + s.2.2) ''
    dualFeasible6 W T h α β x

/-- `Z_D(x)`, the optimal value of (6), p. 583 (the printed `min` read as an infimum). -/
noncomputable def ZD {r d n K : ℕ} [NeZero K] (W : Matrix (Fin r) (Fin d) ℝ)
    (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ) (α β : Fin K → ℝ) (μ : Fin d → ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ) (x : Fin n → ℝ) : ℝ :=
  sInf (dualValues6 W T h α β μ Q x)

/-- The bordered matrix `( V  v ; v′  v₀ )`, indexed by `Fin d ⊕ Fin 1`. -/
def bordered {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (v0 : ℝ) :
    Matrix (Fin d ⊕ Fin 1) (Fin d ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks V (Matrix.of fun i _ => v i) (Matrix.of fun _ j => v j)
    (Matrix.of fun _ _ => v0)

/-- The LMI block of (7) and (8), pp. 583–584:
`( Y  ½(y − α_k w_k) ; ½(y − α_k w_k)′  y₀ − β_k )`. -/
noncomputable def lmiBlock {d : ℕ} (Y : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) (y0 : ℝ)
    (a b : ℝ) (w : Fin d → ℝ) : Matrix (Fin d ⊕ Fin 1) (Fin d ⊕ Fin 1) ℝ :=
  bordered Y ((1 / 2 : ℝ) • (y - a • w)) (y0 - b)

/-- Feasible set of (8), p. 584. A point is `(Y, y, y₀, w)` with `Y ∈ ℝ^{d×d}`, `y ∈ ℝ^d`,
`y₀ ∈ ℝ` and one recourse vector `w_k ∈ ℝ^d` per piece `k ∈ Fin K`, such that for every `k`
the LMI block is positive semidefinite, `W w_k + T x = h` and `w_k ≥ 0`. -/
def feasible8 {r d n K : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (h : Fin r → ℝ) (α β : Fin K → ℝ) (x : Fin n → ℝ) :
    Set (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × ℝ × (Fin K → Fin d → ℝ)) :=
  {s | ∀ k, (lmiBlock s.1 s.2.1 s.2.2.1 (α k) (β k) (s.2.2.2 k)).PosSemidef ∧
    W *ᵥ s.2.2.2 k + T *ᵥ x = h ∧ 0 ≤ s.2.2.2 k}

/-- Objective values `Q · Y + μ′y + y₀` of the feasible points of (8). -/
def dualValues8 {r d n K : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (h : Fin r → ℝ) (α β : Fin K → ℝ) (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin n → ℝ) : Set ℝ :=
  (fun s : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × ℝ × (Fin K → Fin d → ℝ) =>
    frob Q s.1 + μ ⬝ᵥ s.2.1 + s.2.2.1) '' feasible8 W T h α β x

/-- The optimal value of (8), p. 584 (the printed `min` read as an infimum). -/
noncomputable def ZD8 {r d n K : ℕ} (W : Matrix (Fin r) (Fin d) ℝ)
    (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ) (α β : Fin K → ℝ) (μ : Fin d → ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ) (x : Fin n → ℝ) : ℝ :=
  sInf (dualValues8 W T h α β μ Q x)

/-- Feasible set of the semidefinite program (7), p. 583: one program over
`(x, Y, y, y₀, w_1, …, w_K)` jointly, with `A x = b`, `x ≥ 0` and, for every `k`, the LMI block
positive semidefinite, `W w_k + T x = h` and `w_k ≥ 0`. -/
def feasible7 {m₁ n r d K : ℕ} (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) :
    Set ((Fin n → ℝ) × Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × ℝ × (Fin K → Fin d → ℝ)) :=
  {s | (∀ k, (lmiBlock s.2.1 s.2.2.1 s.2.2.2.1 (α k) (β k) (s.2.2.2.2 k)).PosSemidef ∧
      W *ᵥ s.2.2.2.2 k + T *ᵥ s.1 = h ∧ 0 ≤ s.2.2.2.2 k) ∧
    A *ᵥ s.1 = b ∧ 0 ≤ s.1}

/-- Objective values `c′x + Q · Y + μ′y + y₀` of the feasible points of (7). -/
def values7 {m₁ n r d K : ℕ} (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ) (c : Fin n → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) : Set ℝ :=
  (fun s : (Fin n → ℝ) × Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × ℝ × (Fin K → Fin d → ℝ) =>
    c ⬝ᵥ s.1 + frob Q s.2.1 + μ ⬝ᵥ s.2.2.1 + s.2.2.2.1) '' feasible7 A b W T h α β

/-- `Z_SDP`, the optimal value of (7), p. 583 (the printed `min` read as an infimum). -/
noncomputable def ZSDP {m₁ n r d K : ℕ} (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (c : Fin n → ℝ) (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (h : Fin r → ℝ) (α β : Fin K → ℝ) (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sInf (values7 A b c W T h α β μ Q)

end MinimaxSLP.ObjSDP


