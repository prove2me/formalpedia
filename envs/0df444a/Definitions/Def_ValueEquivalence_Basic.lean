-- Prove2me | Definitions.Def_ValueEquivalence_Basic
-- name    : ValueEquivalence_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T17:48:16.153125+00:00
-- url     : https://prove2.me/theorems/ea6a6206-7679-4c52-b27d-be3f9514b8ad
-- title:
--   Finite MDP models, Bellman operators and value equivalence
-- statement:
--   Objects of Sections 2–4 and Appendix A.1.1 of Grimm, Barreto, Singh and Silver (2020), for finite state and action spaces.
--
--   1. **Policies and kernels.** $S$ and $A$ are finite sets. A policy is a map $\pi:S\to\mathcal P(A)$, written $\pi(a\mid s)\ge0$ with $\sum_a\pi(a\mid s)=1$, and $\boldsymbol\Pi$ is the set of all policies. A transition kernel is $p(s'\mid s,a)\ge0$ with $\sum_{s'}p(s'\mid s,a)=1$.
--   2. **Models and Bellman operators (eq. 2).** A model is a pair $m=(r,p)$ of an expected reward $r(s,a)\in\mathbb R$ and a transition kernel $p$. With a discount $\gamma$, the Bellman operator of a policy $\pi$ induced by $m$ acts on $v:S\to\mathbb R$ by
--   $$T^m_\pi[v](s)=\sum_a\pi(a\mid s)\Big(r(s,a)+\gamma\sum_{s'}p(s'\mid s,a)\,v(s')\Big).$$
--   The greedy Bellman operator of Appendix A.1.1 is $T^m v(s)=\max_a\big(r(s,a)+\gamma\sum_{s'}p(s'\mid s,a)v(s')\big)$.
--   3. **Value equivalence (Definitions 1, 2).** For a set of policies $\Pi$ and a set of functions $\mathcal V\subseteq\mathbb V=\{v:S\to\mathbb R\}$, models $m,\tilde m$ are value equivalent with respect to $\Pi,\mathcal V$ if $T^m_\pi v=T^{\tilde m}_\pi v$ for all $\pi\in\Pi$, $v\in\mathcal V$. For a set of models $\mathcal M$ and the true model $m^*$, $\mathcal M(\Pi,\mathcal V)$ is the set of models in $\mathcal M$ value equivalent to $m^*$.
--   4. **Pointwise span (eq. 3).** For a set $\mathcal H$ of functions on $X$ with values in a vector space, $g\in p\text{-span}(\mathcal H)$ iff $g(x)\in\operatorname{span}\{h(x):h\in\mathcal H\}$ for every $x$. For policies, $x=s$ and $h(x)=\pi(\cdot\mid s)\in\mathbb R^A$.
--   5. **Value-equivalent kernels.** With the reward $r^*$ of $m^*$ known, $\mathcal P(\Pi,\mathcal V)$ is the set of kernels $\tilde p$ in a class $\mathcal P$ such that $(r^*,\tilde p)$ is value equivalent to $m^*$; $\mathbb P(\Pi,\mathcal V)$ is the case where $\mathcal P$ is the set of all kernels.
--   6. **Dimension of a set (Section 3.2).** For a subset $\mathcal X$ of a finite-dimensional real vector space, $\dim[\mathcal X]=\min\{\dim\mathcal W:\mathcal W\text{ a subspace},\ \mathcal X+c\subseteq\mathcal W\text{ for some }c\}$. For matrices $\boldsymbol A\in\mathbb R^{k\times n}$, $\boldsymbol C\in\mathbb R^{m\times\ell}$, $\mathcal B=\{\boldsymbol B\in\mathbb R^{n\times m}:\boldsymbol A\boldsymbol B\boldsymbol C=0\}$ is the space of Lemma 1.
--   7. **Maximum-likelihood loss (eq. 5).** For a distribution $D$ on $S\times A$, $\ell_{p,D}(p,\tilde p)=\sum_{s,a}D(s,a)\,D_{\mathrm{KL}}\big(p(\cdot\mid s,a)\,\|\,\tilde p(\cdot\mid s,a)\big)$, with $D_{\mathrm{KL}}(q\|q')=\sum_{s'}q(s')\log\frac{q(s')}{q'(s')}$, terms with $q(s')=0$ equal to $0$, and value $+\infty$ if $q'(s')=0<q(s')$ for some $s'$.
--
--   **Formalization Note** The paper states Sections 2–3.1 for general state and action spaces; here $S$ and $A$ are finite types, as in the paper's Section 3.2 from Proposition 2 on. A model carries the proof that $p$ is a transition kernel. The Bellman operator is defined for any $\pi:S\times A\to\mathbb R$, so that it can be evaluated on pointwise combinations of policies. The dimension uses $\operatorname{finrank}$ of subspaces, which is the Hamel dimension in finite dimensions. The loss takes values in the extended reals.
-- source:
--   Grimm, Barreto, Singh and Silver, The Value Equivalence Principle for Model-Based Reinforcement Learning, arXiv:2011.03506v1 (2020), Sections 2, 3 (Definitions 1-2, eq. (3), Section 3.2), 4 (eq. (5)) and Appendix A.1.1

import Mathlib

/-!
Grimm, Barreto, Singh and Silver, *The Value Equivalence Principle for Model-Based Reinforcement
Learning*, arXiv:2011.03506v1 (NeurIPS 2020): finite Markov decision processes, models and their
Bellman operators (Section 2), value equivalence and spaces of value-equivalent models
(Section 3, Definitions 1 and 2), pointwise span (eq. (3)), the dimension `dim[·]` of a set of
transition matrices (Section 3.1), the maximum-likelihood loss (eq. (5)) and the greedy Bellman
operator of Appendix A.1.1. State and action spaces are finite, as in Section 3.1 from
Proposition 2 on.
-/

noncomputable section

namespace ValueEquivalence

variable {S A : Type*} [Fintype S] [Fintype A]

/-- Section 2, p. 2: `p` is a transition kernel, i.e. `p(·|s,a)` (written `p s a`) is a
probability distribution on the finite state space `S` for every state `s` and action `a`. -/
def IsTransitionKernel (p : S → A → S → ℝ) : Prop :=
  (∀ s a s', 0 ≤ p s a s') ∧ ∀ s a, ∑ s', p s a s' = 1

/-- Section 2, p. 2: a policy `π : S → 𝒫(A)`, written `π s a = π(a|s)`. -/
def IsPolicy (π : S → A → ℝ) : Prop :=
  (∀ s a, 0 ≤ π s a) ∧ ∀ s, ∑ a, π s a = 1

/-- Section 2, p. 2: the set `𝚷` of all policies. -/
def policies : Set (S → A → ℝ) := {π | IsPolicy π}

/-- Section 3, p. 3 (and Section 3.1, p. 5, for finite `S`, `A`): a model `m = (r, p)`, an
expected reward `r(s,a)` together with a transition kernel `p(s'|s,a)`. -/
structure Model (S A : Type*) [Fintype S] where
  /-- the expected reward `r(s,a)` -/
  r : S → A → ℝ
  /-- the transition kernel, `p s a s' = p(s'|s,a)` -/
  p : S → A → S → ℝ
  /-- `p` is a transition kernel -/
  isKernel : IsTransitionKernel p

/-- Eq. (2), p. 2: the Bellman operator of policy `π` induced by model `m` and discount `γ`,
`T_π[v](s) = E_{A∼π(·|s), S'∼p(·|s,A)}[r(s,A) + γ v(S')]`. -/
def bellman (m : Model S A) (γ : ℝ) (π : S → A → ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => ∑ a, π s a * (m.r s a + γ * ∑ s', m.p s a s' * v s')

/-- Definition 1, p. 3: models `m` and `m'` are value equivalent with respect to a set of policies
`Pol` and a set of functions `V` if `T_π v = T'_π v` for all `π ∈ Pol` and all `v ∈ V`. -/
def IsValueEquivalent (γ : ℝ) (Pol : Set (S → A → ℝ)) (V : Set (S → ℝ)) (m m' : Model S A) :
    Prop :=
  ∀ π ∈ Pol, ∀ v ∈ V, bellman m γ π v = bellman m' γ π v

/-- Definition 2, p. 3: the space `M_m(Pol, V) ⊆ M` of models in `M` that are value equivalent to
`m` with respect to `Pol` and `V`. With `m = m*` the true model this is `M(Pol, V)`. -/
def veSpace (γ : ℝ) (M : Set (Model S A)) (m : Model S A) (Pol : Set (S → A → ℝ))
    (V : Set (S → ℝ)) : Set (Model S A) :=
  {m' | m' ∈ M ∧ IsValueEquivalent γ Pol V m m'}

/-- Eq. (3), p. 4: the pointwise span of a set `H` of functions on `X`, in the equivalent form
stated right after eq. (3): `g ∈ p-span(H)` iff `g(x) ∈ span {h(x) : h ∈ H}` for every `x`.
For policies, `X = S` and `h(x) = π(·|s) ∈ ℝ^A`. -/
def pspan {X W : Type*} [AddCommGroup W] [Module ℝ W] (H : Set (X → W)) : Set (X → W) :=
  {g | ∀ x, g x ∈ Submodule.span ℝ ((fun h => h x) '' H)}

/-- Section 3.1, p. 5: the set `ℙ(Pol, V)` (for `PP` the set of all transition kernels) or
`𝒫(Pol, V)` (Section 4, p. 5, for a class `PP` of kernels) of transition kernels in `PP` that,
with the known reward `r*` of the true model `m*`, are value equivalent to `m*`. -/
def veKernels (γ : ℝ) (mstar : Model S A) (PP : Set (S → A → S → ℝ)) (Pol : Set (S → A → ℝ))
    (V : Set (S → ℝ)) : Set (S → A → S → ℝ) :=
  Model.p '' veSpace γ {m | m.r = mstar.r ∧ m.p ∈ PP} mstar Pol V

/-- Section 3.1, p. 5: the dimension of a set `X`, the least Hamel dimension of a vector space
`W` containing a translate `X + c`: `dim[X] = min_{(W, c) : X + c ⊆ W} H-dim[W]`. Used on
finite-dimensional real spaces, where the Hamel dimension is `Module.finrank`. -/
def setDim {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] (X : Set E) : ℕ :=
  sInf {d | ∃ (W : Submodule ℝ E) (c : E),
    (fun x => x + c) '' X ⊆ (W : Set E) ∧ Module.finrank ℝ W = d}

/-- Lemma 1, p. 14: for `A ∈ ℝ^{k×n}` and `C ∈ ℝ^{m×l}`, the vector space
`𝓑 = {B ∈ ℝ^{n×m} : A B C = 0}`. -/
def twoSidedKernel {k n m l : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (C : Matrix (Fin m) (Fin l) ℝ) :
    Submodule ℝ (Matrix (Fin n) (Fin m) ℝ) where
  carrier := {B | A * B * C = 0}
  add_mem' := by
    intro B B' hB hB'
    change A * B * C = 0 at hB
    change A * B' * C = 0 at hB'
    show A * (B + B') * C = 0
    rw [Matrix.mul_add, Matrix.add_mul, hB, hB', add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c B hB
    change A * B * C = 0 at hB
    show A * (c • B) * C = 0
    rw [Matrix.mul_smul, Matrix.smul_mul, hB, smul_zero]

/-- Eq. (5), p. 5: the Kullback–Leibler divergence `D_KL(q ‖ q')` of two distributions on the
finite set `S`, `∑_s q(s) log (q(s)/q'(s))`, with `0 log(0/·) = 0` and value `+∞` when
`q'(s) = 0 < q(s)` for some `s`. -/
def klDivFin (q q' : S → ℝ) : EReal :=
  ∑ s, if q s = 0 then 0 else if q' s = 0 then ⊤ else ((q s * Real.log (q s / q' s) : ℝ) : EReal)

/-- Eq. (5), p. 5: the maximum-likelihood loss
`ℓ_{p,D}(p, p') = E_{(S,A)∼D}[D_KL(p(·|S,A) ‖ p'(·|S,A))]` for a distribution `D` on `S × A`. -/
def mleLoss (D : S → A → ℝ) (p p' : S → A → S → ℝ) : EReal :=
  ∑ s, ∑ a, ((D s a : ℝ) : EReal) * klDivFin (p s a) (p' s a)

/-- Appendix A.1.1, proof of Proposition 4, p. 16: the greedy Bellman operator
`T v = max_a T_a v` of model `m`, where `T_a` is the Bellman operator of the policy that always
selects action `a` (meaningful for nonempty `A`). -/
def bellmanOpt (m : Model S A) (γ : ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => ⨆ a, (m.r s a + γ * ∑ s', m.p s a s' * v s')

end ValueEquivalence


