-- Prove2me | Definitions.Def_MinimaxSLP_RhsExtremal_Model
-- name    : MinimaxSLP_RhsExtremal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:12.451458+00:00
-- url     : https://prove2.me/theorems/c4b8f8a1-6701-472c-b97a-af4a2c31a64a
-- title:
--   The model of §1 and §3: X, 𝒬(h, x), 𝕌, the moment class 𝒫 (10), Ẑ(x), the dual (16) with Ẑ_DD(x), and the Gaussian mixture P_m(x)
-- statement:
--   This file fixes the objects of the two-stage minimax stochastic linear program with a random right-hand side, a constant objective and a piecewise-linear disutility, together with the semidefinite program (16) and the mixed normal distribution used to attain its value.
--
--   **First and second stage.** For $A\in\mathbb R^{m_1\times n}$ and $b\in\mathbb R^{m_1}$ the first-stage feasible region is $X=\{x\in\mathbb R^n : Ax=b,\ x\ge 0\}$. For a recourse matrix $W\in\mathbb R^{r\times d}$, a technology matrix $T\in\mathbb R^{r\times n}$, a constant objective $q\in\mathbb R^d$ and a right-hand side $h\in\mathbb R^r$, the second-stage cost is the optimal value of the dual linear program
--   $$
--   \mathcal Q(h,x)=\max_{p}\ (h-Tx)'p\quad\text{s.t.}\quad W'p\le q .
--   $$
--
--   **Disutility.** For coefficients $\alpha_1,\dots,\alpha_K$ and $\beta_1,\dots,\beta_K$ ($K\ge 1$), $\mathbb U(t)=\max_{k=1,\dots,K}(\alpha_k t+\beta_k)$.
--
--   **Moment class and worst-case value.** For $\mu\in\mathbb R^r$ and $Q\in\mathbb R^{r\times r}$, the class $\mathcal P$ of (10) consists of the probability distributions $P$ of $\tilde h$ on $\mathbb R^r$ with finite second moments, $\mathbb E_P[\tilde h]=\mu$ and $\mathbb E_P[\tilde h\tilde h']=Q$. The worst-case expected disutility is
--   $$
--   \hat Z(x)=\sup_{P\in\mathcal P}\mathbb E_P\big[\mathbb U(\mathcal Q(\tilde h,x))\big].
--   $$
--
--   **The program (16).** Let $p_1,\dots,p_N\in\mathbb R^r$ be the extreme points of $\{p : W'p\le q\}$ (Assumption 5). Over blocks $V_k^i\in\mathbb R^{r\times r}$, $v_k^i\in\mathbb R^r$, $v_{k0}^i\in\mathbb R$, $k=1,\dots,K$, $i=1,\dots,N$,
--   $$
--   \hat Z_{DD}(x)=\max\ \sum_{k=1}^K\sum_{i=1}^N\big(\alpha_k p_i'v_k^i+v_{k0}^i(\beta_k-\alpha_k p_i'Tx)\big)\quad\text{s.t.}\quad \sum_{k=1}^K\sum_{i=1}^N\begin{pmatrix}V_k^i & v_k^i\\ (v_k^i)' & v_{k0}^i\end{pmatrix}=\begin{pmatrix}Q&\mu\\ \mu'&1\end{pmatrix},\ \ \begin{pmatrix}V_k^i & v_k^i\\ (v_k^i)' & v_{k0}^i\end{pmatrix}\succeq 0 .
--   $$
--
--   **The mixture $P_m(x)$.** For a point of (16), the mixed distribution draws, with probability $v_{k0}^i$, a normal vector
--   $$
--   \tilde h_k^i\sim\mathbb N\!\left(\frac{v_k^i}{v_{k0}^i},\ \frac{V_k^i v_{k0}^i-v_k^i(v_k^i)'}{(v_{k0}^i)^2}\right).
--   $$
--
--   These are the objects of Theorem 3.3: some distribution in $\mathcal P$ attains $\hat Z(x)$, and its value equals $\hat Z_{DD}(x)$.
--
--   **Formalization Note** The paper writes $p$ both for the dimension of $q$ and $w$ and for the dual vector; here the dimension is $d$ and the dual vector is `π` (or `ps i` for the extreme points). Indices $k,i$ run over `Fin K`, `Fin N` (zero-based). The moment class is built from the published `MomentDRO.Conf.HasSecondMoments`, `meanVec` and `secondMomentAbout P 0` (the uncentred second moment), on measures rather than the densities of (11). $\mathcal Q(h,x)$ is the real supremum of $(h-Tx)'p$ over the dual polyhedron; it is attained and finite under Assumptions 2 and 3, and statements never rely on its junk value. $\hat Z(x)$ and $\hat Z_{DD}(x)$ are real `sSup`s of value sets; the theorems state attainment explicitly. Bordered matrices are `Matrix.fromBlocks` indexed by `Fin r ⊕ Fin 1`, and $\succeq 0$ is `Matrix.PosSemidef`. The normal law is Mathlib's `multivariateGaussian` on `EuclideanSpace ℝ (Fin r)`, transported to `Fin r → ℝ`; the mixture weight is `ENNReal.ofReal` $v_{k0}^i$, so a block with $v_{k0}^i\le 0$ contributes nothing. The paper's "$V_k^i v_{k0}$", "$v_{k0}^2$" and "with probability $v_{k0}$" (pp. 590–591) are read with the superscript $i$. The companion mission on Theorem 3.2 (`MinimaxSLP.RhsSDP`) defines the shared objects with the same names.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, pp. 580–591: X (p. 582, Assumption 1), (3) (p. 581), (10) and 𝒬(h̃, x) (p. 587), (11) (p. 588), Assumption 5 (p. 589), (16) (p. 590), the mixture P_m(x) (pp. 590–591)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model
import Definitions.Def_MinimaxSLP_RhsSDP_Model

namespace MinimaxSLP.RhsExtremal

open MeasureTheory Matrix ProbabilityTheory

/-- Feasible set of (16), p. 590. A point assigns to every pair `(k, i)` (`k ∈ Fin K`,
`i ∈ Fin N`) a block `(V_k^i, v_k^i, v_k0^i)` with `V_k^i ∈ ℝ^{r×r}`, `v_k^i ∈ ℝʳ`,
`v_k0^i ∈ ℝ`, such that `Σ_{k,i} ( V_k^i v_k^i ; (v_k^i)′ v_k0^i ) = ( Q μ ; μ′ 1 )` and every
block is positive semidefinite. -/
def feasible16 {r : ℕ} (K N : ℕ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ) :
    Set (Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ)) :=
  {s | ∑ k, ∑ i, MinimaxSLP.ObjSDP.bordered (s k i).1 (s k i).2.1 (s k i).2.2 = MinimaxSLP.ObjSDP.bordered Q μ 1 ∧
    ∀ k i, (MinimaxSLP.ObjSDP.bordered (s k i).1 (s k i).2.1 (s k i).2.2).PosSemidef}

/-- Objective of (16): `Σ_{k,i} (α_k p_i′v_k^i + v_k0^i (β_k − α_k p_i′T x))`, where
`p_1, …, p_N` (here `ps : Fin N → ℝʳ`) are the dual extreme points of Assumption 5. -/
def obj16 {r n K N : ℕ} (T : Matrix (Fin r) (Fin n) ℝ) (α β : Fin K → ℝ)
    (ps : Fin N → Fin r → ℝ) (x : Fin n → ℝ)
    (s : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ)) : ℝ :=
  ∑ k, ∑ i, (α k * (ps i ⬝ᵥ (s k i).2.1) + (s k i).2.2 * (β k - α k * (ps i ⬝ᵥ (T *ᵥ x))))

/-- `Ẑ_DD(x)`, the optimal value of (16), p. 590, as the real supremum of the objective over the
feasible set (attainment is a separate statement). -/
noncomputable def ZhatDD {r n K N : ℕ} (T : Matrix (Fin r) (Fin n) ℝ) (α β : Fin K → ℝ)
    (ps : Fin N → Fin r → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup (obj16 T α β ps x '' feasible16 K N μ Q)

/-- The multivariate normal law `ℕ(m, S)` on `ℝʳ` (as `Fin r → ℝ`): Mathlib's
`multivariateGaussian` on `EuclideanSpace ℝ (Fin r)`, transported along the identification
`EuclideanSpace ℝ (Fin r) ≃ (Fin r → ℝ)`. -/
noncomputable def gaussian {r : ℕ} (m : Fin r → ℝ) (S : Matrix (Fin r) (Fin r) ℝ) :
    Measure (Fin r → ℝ) :=
  (multivariateGaussian (WithLp.toLp 2 m) S).map (fun z : EuclideanSpace ℝ (Fin r) => WithLp.ofLp z)

/-- The mixed distribution `P_m(x)` of p. 591 built from a point `s` of (16): the component
`h̃_k^i ∼ ℕ(v_k^i / v_k0^i, (V_k^i v_k0^i − v_k^i (v_k^i)′) / (v_k0^i)²)` is drawn with
probability `v_k0^i`. Blocks with `v_k0^i ≤ 0` receive weight `ENNReal.ofReal v_k0^i = 0`. -/
noncomputable def mixture {r K N : ℕ}
    (s : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ)) : Measure (Fin r → ℝ) :=
  ∑ k, ∑ i, ENNReal.ofReal (s k i).2.2 •
    gaussian ((s k i).2.2⁻¹ • (s k i).2.1)
      (((s k i).2.2 ^ 2)⁻¹ • ((s k i).2.2 • (s k i).1 - Matrix.vecMulVec (s k i).2.1 (s k i).2.1))

end MinimaxSLP.RhsExtremal


