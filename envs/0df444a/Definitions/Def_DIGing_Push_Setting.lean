-- Prove2me | Definitions.Def_DIGing_Push_Setting
-- name    : DIGing_Push_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:56:37.574343+00:00
-- url     : https://prove2.me/theorems/3c125b68-5165-48d4-a056-0a6fa669cf73
-- title:
--   Algorithm 2, Assumptions 6–7, (48)–(50), Theorem 18, pp. 21–25 — directed graphs, push-sum weights, Push-DIGing runs, R̃(k), Q₁, τ̃, δ, J₂
-- statement:
--   This file defines the directed-graph model, the Push-DIGing algorithm and the constants of its rate.
--
--   **Graphs.** A time-varying directed graph on agents $\{1,\dots,n\}$ is a sequence of arc sets $\mathcal A(k)$; an arc $(j\to i)\in\mathcal A(k)$ means that agent $j$ can send to agent $i$ at time $k$. The out-degree $d^{\rm out}_j(k)$ is the number of agents $i\ne j$ with $(j\to i)\in\mathcal A(k)$.
--
--   **Assumption 6 ($\tilde B_\ominus$-strong connectivity).** There is an integer $\tilde B_\ominus>0$ such that for every $t=0,1,\dots$ the directed graph with arc set $\bigcup_{\ell=t\tilde B_\ominus}^{(t+1)\tilde B_\ominus-1}\mathcal A(\ell)$ is strongly connected. One writes $B_\ominus=2\tilde B_\ominus-1$.
--
--   **Assumption 7 (mixing matrices).** For every $k$,
--   $$C_{ij}(k)=\begin{cases}\dfrac{1}{d^{\rm out}_j(k)+1}, & i=j\ \text{or}\ (j\to i)\in\mathcal A(k),\\[4pt] 0,&\text{otherwise.}\end{cases}$$
--
--   **Push-DIGing (Algorithm 2).** Fix a step size $\alpha$ and $\mathbf x(0)=\mathbf u(0)\in\mathbb R^{n\times p}$. Set $\mathbf y(0)=\nabla\mathbf f(\mathbf x(0))$, $\mathbf v(0)=\mathbf 1$, and for $k=0,1,\dots$
--   $$\begin{aligned}\mathbf u(k+1)&=C(k)\big(\mathbf u(k)-\alpha\mathbf y(k)\big),\qquad \mathbf v(k+1)=C(k)\mathbf v(k),\\ \mathbf x(k+1)&=V(k+1)^{-1}\mathbf u(k+1),\qquad \mathbf y(k+1)=C(k)\mathbf y(k)+\nabla\mathbf f(\mathbf x(k+1))-\nabla\mathbf f(\mathbf x(k)),\end{aligned}$$
--   where $V(k)=\operatorname{diag}\{\mathbf v(k)\}$. The weights $\mathbf v(k)$ depend on the matrices only.
--
--   **Derived objects.** $\tilde R(k)=V(k+1)^{-1}C(k)V(k)$, its products $\tilde R_b(k)=\tilde R(k)\tilde R(k-1)\cdots\tilde R(k-b+1)$ with $\tilde R_0(k)=I$, the scaled tracking variable $\mathbf h(k)=V(k)^{-1}\mathbf y(k)$, and the gradient increments $\mathbf z(k)=\nabla\mathbf f(\mathbf x(k))-\nabla\mathbf f(\mathbf x(k-1))$, $\mathbf z(0)=0$.
--
--   **Constants.** With $B_\ominus$ as above and an integer $B$,
--   $$\tilde\tau=\frac{1}{n^{2+nB_\ominus}},\qquad Q_1=2n\,\frac{1+\tilde\tau^{-nB_\ominus}}{1-\tilde\tau^{nB_\ominus}},\qquad \delta=Q_1\big(1-\tilde\tau^{nB_\ominus}\big)^{\frac{B-1}{nB_\ominus}},$$
--   $$J_2=3Q_1\|V^{-1}\|^1_{\max}\,\bar\kappa\,B\,\big(\delta+Q_1(B-1)\big)(1+\sqrt n)\big(1+4\sqrt n\sqrt{\bar\kappa}\big),$$
--   where $\|V^{-1}\|^1_{\max}=\sup_{k\ge0}\max_i 1/v_i(k)$. For constants $J,\delta,\mu$ the step-size thresholds are
--   $$\alpha_{\rm split}=\frac{1.5\big(\sqrt{J^2+(1-\delta^2)J}-\delta J\big)^2}{\mu J(J+1)^2},\qquad \alpha_{\max}=\frac{1.5(1-\delta)^2}{\mu J},$$
--   and the rate is $\lambda=\sqrt[2B]{1-\alpha\mu/1.5}$ if $\alpha\le\alpha_{\rm split}$ and $\lambda=\sqrt[B]{\sqrt{\alpha\mu J/1.5}+\delta}$ otherwise.
--
--   These are the objects about which Theorem 18 and its lemmas are stated.
--
--   **Formalization Note** An arc $j\to i$ is the pair `(j, i)`. The printed Assumption 7 gives $C_{ij}(k)=1/(d^{\rm out}_j(k)+1)$ on arcs only; read literally, the columns of $C(k)$ sum to $d/(d+1)\ne1$, so $C(k)$ is not column stochastic and $\mathbf v(k)$ may vanish. The paper's own uses (the agent updates on p. 21 with the term $C_{ii}(k)$, "column stochastic", $C_{ij}(k)\ge1/n$, $v_j(k)\ge1/n^{nB_\ominus}$) require the push-sum convention, in which agent $j$ keeps the share $1/(d^{\rm out}_j(k)+1)$; that self-weight is added here and disclosed. $\tilde R_b(k)$ uses natural-number subtraction in its indices and is only used for $k\ge b-1$. Real powers are `Real.rpow`; $\tilde\tau^{-nB_\ominus}$ is the inverse of a natural power. $\|V^{-1}\|^1_{\max}$ is not defined here: statements take a number `Vmax` together with the hypothesis that it is the least upper bound of $\{1/v_i(k)\}$.
-- source:
--   arXiv:1607.03218v3, §4.2 Algorithm 2 (p. 21); §5 Assumptions 6 and 7 (pp. 21–22), (48)–(50) (p. 22); Theorem 18 (p. 25); z(k) from §3.2 (p. 10)

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Undir_Setting

namespace DIGing.Push

/-- The out-degree `d^out_j(k) = |N^out_j(k)|` of agent `j` at time `k` (§5, p. 21; Assumption 7,
p. 22): the number of agents `i ≠ j` with an arc `j → i` in `A(k)`. An arc `j → i` is the pair
`(j, i) ∈ A k`. -/
def outDeg {n : ℕ} (A : ℕ → Finset (Fin n × Fin n)) (k : ℕ) (j : Fin n) : ℕ :=
  (Finset.univ.filter fun i => i ≠ j ∧ (j, i) ∈ A k).card

/-- Assumption 6 (`B̃⊖`-strongly connected graph sequence, pp. 21–22): `B̃⊖ > 0`, and for every
`t = 0, 1, …` the directed graph on `V` with arc set `⋃_{ℓ = tB̃⊖}^{(t+1)B̃⊖ − 1} A(ℓ)` is strongly
connected: every agent `j` is reachable from every agent `i` along arcs of that union. -/
def Assumption6 {n : ℕ} (A : ℕ → Finset (Fin n × Fin n)) (Bt : ℕ) : Prop :=
  0 < Bt ∧ ∀ t : ℕ, ∀ i j : Fin n,
    Relation.ReflTransGen (fun a b => ∃ l ∈ Finset.Ico (t * Bt) ((t + 1) * Bt), (a, b) ∈ A l) i j

/-- Assumption 7 (Mixing matrix sequence `{C(k)}`, p. 22), in the push-sum convention:
`C_ij(k) = 1/(d^out_j(k) + 1)` if `i = j` or `j → i` is an arc of `A(k)`, and `C_ij(k) = 0`
otherwise. The self-weight `C_jj(k) = 1/(d^out_j(k) + 1)` is a disclosed addition to the printed
rule: it makes every `C(k)` column stochastic, as the paper's analysis requires. -/
def Assumption7 {n : ℕ} (A : ℕ → Finset (Fin n × Fin n)) (C : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    Prop :=
  ∀ k i j, C k i j = if i = j ∨ (j, i) ∈ A k then 1 / ((outDeg A k j : ℝ) + 1) else 0

/-- The push-sum weights `v(k)` of Algorithm 2 (p. 21): `v(0) = 1 ∈ ℝⁿ`, `v(k+1) = C(k) v(k)`. -/
def vSeq {n : ℕ} (C : ℕ → Matrix (Fin n) (Fin n) ℝ) : ℕ → Fin n → ℝ
  | 0 => fun _ => 1
  | k + 1 => (C k).mulVec (vSeq C k)

/-- `R̃(k) = (V(k+1))⁻¹ C(k) V(k)` with `V(k) = diag{v(k)}` (p. 22). -/
noncomputable def Rt {n : ℕ} (C : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => (vSeq C (k + 1) i)⁻¹) * C k * Matrix.diagonal (vSeq C k)

/-- `R̃_b(k) = R̃(k) R̃(k−1) ⋯ R̃(k−b+1)` (p. 22), with `R̃_0(k) = I`. Natural subtraction makes the
factors junk for `k < b − 1`; the product is only used at `k ≥ b − 1`. -/
noncomputable def prodR {n : ℕ} (C : ℕ → Matrix (Fin n) (Fin n) ℝ) (b k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (List.ofFn (fun t : Fin b => Rt C (k - t))).prod

/-- A run of Push-DIGing (Algorithm 2, p. 21) with step size `α`: `x(0) = u(0)`,
`y(0) = ∇f(x(0))`, and for every `k`
`u(k+1) = C(k)(u(k) − αy(k))`, `x(k+1) = (V(k+1))⁻¹u(k+1)`,
`y(k+1) = C(k)y(k) + ∇f(x(k+1)) − ∇f(x(k))`, where `v(k) = vSeq C k`. -/
def IsPushDIGingRun {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (C : ℕ → Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (u x y : ℕ → DIGing.Undir.Stack n p) : Prop :=
  u 0 = x 0 ∧ y 0 = DIGing.Undir.gradStack f (x 0) ∧
  ∀ k, u (k + 1) = DIGing.Undir.mix (C k) (u k - α • y k) ∧
    x (k + 1) = (fun i => (vSeq C (k + 1) i)⁻¹ • u (k + 1) i) ∧
    y (k + 1) = DIGing.Undir.mix (C k) (y k) + DIGing.Undir.gradStack f (x (k + 1)) - DIGing.Undir.gradStack f (x k)

/-- `h(k) = (V(k))⁻¹ y(k)` (p. 22). -/
noncomputable def hSeq {n p : ℕ} (C : ℕ → Matrix (Fin n) (Fin n) ℝ) (y : ℕ → DIGing.Undir.Stack n p) (k : ℕ) :
    DIGing.Undir.Stack n p :=
  fun i => (vSeq C k i)⁻¹ • y k i

/-- `τ̃ = 1/n^{2 + nB⊖}` of (50) (p. 22), with `Bm = B⊖`. -/
noncomputable def tauT (n Bm : ℕ) : ℝ := 1 / (n : ℝ) ^ (2 + n * Bm)

/-- `Q₁ = 2n (1 + τ̃^{−nB⊖})/(1 − τ̃^{nB⊖})` of (50) (p. 22). -/
noncomputable def Q1 (n Bm : ℕ) : ℝ :=
  2 * n * (1 + (tauT n Bm ^ (n * Bm))⁻¹) / (1 - tauT n Bm ^ (n * Bm))

/-- `δ = Q₁ (1 − τ̃^{nB⊖})^{(B−1)/(nB⊖)}` of Lemma 13 and Theorem 18 (pp. 22, 25). -/
noncomputable def deltaPush (n Bm B : ℕ) : ℝ :=
  Q1 n Bm * (1 - tauT n Bm ^ (n * Bm)) ^ (((B : ℝ) - 1) / ((n : ℝ) * Bm))

/-- `J₂ = 3Q₁‖V⁻¹‖¹_max κ̄ B (δ + Q₁(B − 1))(1 + √n)(1 + 4√n√κ̄)` of Theorem 18 (p. 25), with
`Vmax = ‖V⁻¹‖¹_max`. -/
noncomputable def J2 {n : ℕ} (Lc mu : Fin n → ℝ) (Bm B : ℕ) (Vmax : ℝ) : ℝ :=
  3 * Q1 n Bm * Vmax * DIGing.Undir.kappa Lc mu * B * (deltaPush n Bm B + Q1 n Bm * ((B : ℝ) - 1)) *
    (1 + Real.sqrt n) * (1 + 4 * Real.sqrt n * Real.sqrt (DIGing.Undir.kappa Lc mu))

/-- The split point `1.5(√(J² + (1−δ²)J) − δJ)² / (μ J (J+1)²)` of the two step-size regimes. -/
noncomputable def alphaSplit (J δ μ : ℝ) : ℝ :=
  3 / 2 * (Real.sqrt (J ^ 2 + (1 - δ ^ 2) * J) - δ * J) ^ 2 / (μ * J * (J + 1) ^ 2)

/-- The step-size bound `1.5(1 − δ)²/(μ J)`. -/
noncomputable def alphaMax (J δ μ : ℝ) : ℝ := 3 / 2 * (1 - δ) ^ 2 / (μ * J)

/-- The rate `λ`: `(1 − αμ/1.5)^{1/(2B)}` if `α ≤ alphaSplit`, else `(√(αμJ/1.5) + δ)^{1/B}`. -/
noncomputable def rateLam (J δ μ α : ℝ) (B : ℕ) : ℝ :=
  if α ≤ alphaSplit J δ μ then (1 - α * μ / (3 / 2)) ^ ((1 : ℝ) / (2 * (B : ℝ)))
  else (Real.sqrt (α * μ * J / (3 / 2)) + δ) ^ ((1 : ℝ) / (B : ℝ))

end DIGing.Push


