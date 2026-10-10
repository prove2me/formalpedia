-- Prove2me | Definitions.Def_StrongWeakEq_Limit_Discretization
-- name    : StrongWeakEq_Limit_Discretization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:42.252667+00:00
-- url     : https://prove2.me/theorems/cd360db6-9fe5-48fe-a2ae-df82db266bdb
-- title:
--   §5.1, p. 17, (5.8)–(5.11) — eventual monotonicity of |f|, discretized payoff κⁿ, generator Q^{u,n} of a transition matrix, admissible transition rows 𝒜ⁿ
-- statement:
--   This definition sets up the time discretization of the continuous-time problem of §2 with a mesh $\delta>0$ (on the page $\delta=\delta_n$ with $\delta_n\downarrow0$).
--
--   1. **Eventual monotonicity** (5.8): there is $T>0$, independent of $i$ and $q$, such that $t\mapsto|f(t,i,q)|$ is nonincreasing for $t\ge T$.
--   2. **Discretized payoff** (5.9): for $k\in\{0,1,2,\dots\}$, $i\in S$ and $\alpha\in\mathfrak P$,
--   $$
--   \kappa^n(k,i,\alpha)=f\big(k\delta_n,\,i,\,\tilde\alpha^{i,n}\big)\cdot\delta_n,\qquad \tilde\alpha^{i,n}=\frac1{\delta_n}(\alpha_1,\dots,\alpha_{i-1},\alpha_i-1,\alpha_{i+1},\dots,\alpha_N).
--   $$
--   3. **Generator of a transition matrix** (5.10): for a transition matrix $u$, $Q^{u,n}=(q^{u,n}_{ij})$ with
--   $$
--   q^{u,n}_{ij}=\begin{cases}\frac1{\delta_n}u_{ij}, & j\ne i,\\[2pt] \frac1{\delta_n}(u_{ii}-1), & j=i,\end{cases}\qquad\text{i.e. } Q^{u,n}=\frac{1}{\delta_n}(u-I).
--   $$
--   4. **Admissible transition matrices** (5.11): $\mathcal A^n=\{u \text{ transition matrix}: Q^{u,n}\in\mathcal Q\}$, described row by row: the admissible rows at state $i$ are $\{\alpha\in\mathfrak P:\ \tfrac1{\delta_n}(\alpha-e_i)\in D_i\}$, with $e_i$ the $i$-th unit vector.
--
--   With these, the discretized problem $V^n$ is (5.3) with $\kappa$ and $\mathcal A$ replaced by $\kappa^n$ and $\mathcal A^n$; its equilibria $u^n$ and their generators $Q^n=Q^{u^n,n}\in\mathcal Q$ are the objects of Lemma 5.1 and Theorem 5.2.
--
--   **Formalization Note** $\kappa^n$ is a total function: it is defined for every $\alpha$, also when $\tilde\alpha^{i,n}\notin D_i$, but it is only ever evaluated in statements on rows of matrices in $\mathcal A^n$, where $\tilde\alpha^{i,n}=Q^{u,n}_i\in D_i$. A transition matrix is a matrix whose rows lie in $\mathfrak P$, so $\mathcal A^n$ is `DControls (admRows D δ)`, and $\tilde\alpha^{i,n}$ of the row $u_i$ is exactly the $i$-th row of $Q^{u,n}$. Condition (5.8) is required for $q\in D_i$ only, which is where $f$ is ever evaluated. States are `Fin N`.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 17, (5.8)–(5.11)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Discrete_DiscreteModel

namespace StrongWeakEq.Limit

/-- (5.9), p. 17: the discretized payoff `κⁿ(k, i, α) = f(k δₙ, i, α̃^{i,n}) · δₙ`, where
`α̃^{i,n} = (1/δₙ)(α₁, …, αᵢ − 1, …, α_N)` is the generator row of the transition row `α`. -/
noncomputable def kappaN {N : ℕ} (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (δ : ℝ) :
    ℕ → Fin N → (Fin N → ℝ) → ℝ :=
  fun k i α => f ((k : ℝ) * δ) i (δ⁻¹ • (α - Pi.single i (1 : ℝ))) * δ

/-- (5.10), p. 17: the generator `Q^{u,n} = (u − I)/δₙ` of a transition matrix `u`: entries
`u_{ij}/δₙ` for `j ≠ i` and `(u_{ii} − 1)/δₙ` on the diagonal. -/
noncomputable def genOf {N : ℕ} (δ : ℝ) (u : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  δ⁻¹ • (u - 1)

/-- (5.11), p. 17, row by row: the admissible transition rows at state `i` for the mesh `δ`,
`{α ∈ 𝔓 : (1/δ)(α − eᵢ) ∈ Dᵢ}`. Then `DControls (admRows D δ)` is
`𝒜ⁿ = {u transition matrix : Q^{u,n} ∈ 𝒬}`. -/
def admRows {N : ℕ} (D : Fin N → Set (Fin N → ℝ)) (δ : ℝ) (i : Fin N) : Set (Fin N → ℝ) :=
  {α | α ∈ StrongWeakEq.Discrete.Simplex N ∧ δ⁻¹ • (α - Pi.single i (1 : ℝ)) ∈ D i}

/-- (5.8), p. 17: there is `T > 0`, independent of `i` and `q`, such that `t ↦ |f(t, i, q)|` is
nonincreasing for `t ≥ T` (for every `i` and every `q ∈ Dᵢ`). -/
def EventuallyNonincreasing {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∀ i, ∀ q ∈ D i, AntitoneOn (fun t => |f t i q|) (Set.Ici T)

end StrongWeakEq.Limit


