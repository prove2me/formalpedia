-- Prove2me | Definitions.Def_MinimaxSLP_ObjExtremal_Model
-- name    : MinimaxSLP_ObjExtremal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:13.986618+00:00
-- url     : https://prove2.me/theorems/00960d65-1296-464d-b429-3f098d407532
-- title:
--   The dual (9) of §2.2 and its optimal value Z_DD(x), on top of the shared model of §1–2.1 (X, X(x), 𝒬(q, x), 𝕌, 𝒫 (4), Z(x), (6))
-- statement:
--   This file defines the feasible set, the objective and the optimal value $Z_{DD}(x)$ of the dual problem (9). The other objects recalled below (first and second stage, disutility, moment class, $Z(x)$ and the dual (6)) are imported from the shared model `MinimaxSLP.ObjSDP.Model` of the companion mission on Theorem 2.1.
--
--   **First and second stage.** For $A\in\mathbb R^{m_1\times n}$ and $b\in\mathbb R^{m_1}$ the first-stage feasible region is $X=\{x\in\mathbb R^n : Ax=b,\ x\ge 0\}$. For a recourse matrix $W\in\mathbb R^{r\times d}$, a technology matrix $T\in\mathbb R^{r\times n}$ and $h\in\mathbb R^r$, the recourse set of $x$ is
--   $$
--   X(x)=\{w\in\mathbb R^{d} : Ww=h-Tx,\ w\ge 0\},
--   $$
--   and the second-stage cost of an objective vector $q\in\mathbb R^d$ is the optimal value of a linear program,
--   $$
--   \mathcal Q(q,x)=\min_{w}\ q'w\quad\text{s.t.}\quad Ww=h-Tx,\ w\ge 0 .
--   $$
--
--   **Disutility.** For coefficients $\alpha_1,\dots,\alpha_K$ and $\beta_1,\dots,\beta_K$ ($K\ge 1$), the disutility is the piecewise-linear function $\mathbb U(t)=\max_{k=1,\dots,K}(\alpha_k t+\beta_k)$.
--
--   **Moment class and worst-case value.** For $\mu\in\mathbb R^d$ and $Q\in\mathbb R^{d\times d}$, the class $\mathcal P$ of (4) consists of the probability distributions $P$ of the random objective $\tilde q$ on $\mathbb R^d$ with finite second moments, $\mathbb E_P[\tilde q]=\mu$ and $\mathbb E_P[\tilde q\tilde q']=Q$. The worst-case expected disutility is
--   $$
--   Z(x)=\sup_{P\in\mathcal P}\mathbb E_P\big[\mathbb U(\mathcal Q(\tilde q,x))\big].
--   $$
--
--   **The dual (6).** With the Frobenius product $Q\cdot Y=\sum_{i,j}Q_{ij}Y_{ij}$,
--   $$
--   Z_D(x)=\min_{Y,y,y_0}\ Q\cdot Y+\mu'y+y_0\quad\text{s.t.}\quad q'Yq+q'y+y_0\ge \mathbb U(\mathcal Q(q,x))\ \ \forall q\in\mathbb R^d,
--   $$
--   over symmetric $Y\in\mathbb S^{d\times d}$, $y\in\mathbb R^d$, $y_0\in\mathbb R$.
--
--   **The dual (9).** Over $V_k\in\mathbb R^{d\times d}$, $v_k\in\mathbb R^d$, $v_{k0}\in\mathbb R$ and $p_k\in\mathbb R^r$, $k=1,\dots,K$,
--   $$
--   Z_{DD}(x)=\max\ \sum_{k=1}^K (h-Tx)'p_k+\beta_k v_{k0}\quad\text{s.t.}\quad \sum_{k=1}^K\begin{pmatrix}V_k & v_k\\ v_k' & v_{k0}\end{pmatrix}=\begin{pmatrix}Q&\mu\\ \mu'&1\end{pmatrix},\ \ \begin{pmatrix}V_k & v_k\\ v_k' & v_{k0}\end{pmatrix}\succeq 0,\ \ W'p_k\le\alpha_k v_k .
--   $$
--
--   These are the objects about which Lemma 2.1 and Theorem 2.2 are stated: $Z_{DD}(x)$ bounds $Z(x)$ from above, and the three values coincide.
--
--   **Formalization Note** The paper writes $p$ for the dimension of $q$ and $w$ and also $p_k$ for dual vectors; here the dimension is $d$ and the dual vectors are `π`. The paper's "$X(x):=\{x\in\mathbb R^n:\dots\}$" (p. 580) is a typo for $w\in\mathbb R^d$. Indices $k$ run over `Fin K` (zero-based). The moment class is built from the published `MomentDRO.Conf.HasSecondMoments`, `meanVec` and `secondMomentAbout P 0` (the uncentred second moment), on measures rather than the densities $f$ of the paper's (5). Every printed min/max is a real `sInf`/`sSup` of the set of objective values (`primalValues`, `dualValues6`, `dualValues9`); $\mathcal Q(q,x)$ is the real infimum of $q'w$ over $X(x)$, which is attained and finite whenever $X(x)\neq\emptyset$ and Assumption 3 holds, and is the junk value $0$ otherwise. The theorems never rely on junk values: they carry those hypotheses and assert `IsLUB`/`IsGLB` where an optimal value is used. Bordered matrices are `Matrix.fromBlocks` indexed by `Fin d ⊕ Fin 1`, and $\succeq 0$ is `Matrix.PosSemidef` (which includes symmetry). The objects other than (9) are the ones of the shared module `MinimaxSLP.ObjSDP.Model`, imported here.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, pp. 580–584: X and X(x) (p. 580), (3) (p. 581), (4) and 𝒬(q̃, x) (p. 582), (5)–(6) (pp. 582–583), (9) (p. 584)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model

namespace MinimaxSLP.ObjExtremal

open MeasureTheory Matrix

/-- Feasible set of (9), p. 584. A point is `(V, v, v₀, p)` with `V_k ∈ ℝ^{d×d}`, `v_k ∈ ℝ^d`,
`v_k0 ∈ ℝ`, `p_k ∈ ℝ^r` (`k ∈ Fin K`) such that
`Σ_k ( V_k v_k ; v_k′ v_k0 ) = ( Q μ ; μ′ 1 )`, every block `( V_k v_k ; v_k′ v_k0 ) ⪰ 0`,
and `W′p_k ≤ α_k v_k`. -/
def feasible9 {r d K : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (α : Fin K → ℝ) (μ : Fin d → ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ) :
    Set ((Fin K → Matrix (Fin d) (Fin d) ℝ) × (Fin K → Fin d → ℝ) × (Fin K → ℝ) ×
      (Fin K → Fin r → ℝ)) :=
  {s | ∑ k, MinimaxSLP.ObjSDP.bordered (s.1 k) (s.2.1 k) (s.2.2.1 k) = MinimaxSLP.ObjSDP.bordered Q μ 1 ∧
    (∀ k, (MinimaxSLP.ObjSDP.bordered (s.1 k) (s.2.1 k) (s.2.2.1 k)).PosSemidef) ∧
    ∀ k, W.transpose *ᵥ s.2.2.2 k ≤ α k • s.2.1 k}

/-- Objective of (9): `Σ_k ((h − T x)′p_k + β_k v_k0)`. -/
def obj9 {r d n K : ℕ} (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ) (β : Fin K → ℝ)
    (x : Fin n → ℝ)
    (s : (Fin K → Matrix (Fin d) (Fin d) ℝ) × (Fin K → Fin d → ℝ) × (Fin K → ℝ) ×
      (Fin K → Fin r → ℝ)) : ℝ :=
  ∑ k, ((h - T *ᵥ x) ⬝ᵥ s.2.2.2 k + β k * s.2.2.1 k)

/-- Objective values of the feasible points of (9). -/
def dualValues9 {r d n K : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (h : Fin r → ℝ) (α β : Fin K → ℝ) (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin n → ℝ) : Set ℝ :=
  obj9 T h β x '' feasible9 W α μ Q

/-- `Z_DD(x)`, the optimal value of (9), p. 584 (the printed `max` read as a supremum here;
attainment is a separate milestone). -/
noncomputable def ZDD {r d n K : ℕ} (W : Matrix (Fin r) (Fin d) ℝ)
    (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ) (α β : Fin K → ℝ) (μ : Fin d → ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup (dualValues9 W T h α β μ Q x)

end MinimaxSLP.ObjExtremal


