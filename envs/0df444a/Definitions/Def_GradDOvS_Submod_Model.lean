-- Prove2me | Definitions.Def_GradDOvS_Submod_Model
-- name    : GradDOvS_Submod_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:10.347037+00:00
-- url     : https://prove2.me/theorems/80d4e987-a147-46ad-9c1b-bc92726b9662
-- title:
--   §2–§3, pp. 9–20 — Lovász extension (2), subgradient (3), estimator (4), P_X, T_M, the simulation oracle, Algorithm 2 and the rounding of Algorithm 1
-- statement:
--   The objects of §3 of Zhang, Zheng and Lavaei for stochastic submodular minimization on $\{0,1\}^d$. A point of $\{0,1\}^d$ is identified with the set $A \subseteq \{1,\dots,d\}$ of its unit coordinates, with indicator vector $\mathbb 1_A \in \mathbb R^d$; the box is $[0,1]^d$.
--
--   1. **Standing assumptions** on $f : \{0,1\}^d \to \mathbb R$ and $L$: $d \ge 1$; $f$ is submodular, $f(A\cap B)+f(A\cup B) \le f(A)+f(B)$ (Assumption 2, which on $\{0,1\}^d$ is submodularity, p. 16); and $|f(A)-f(B)| \le L$ for all $A,B$ (Assumption 4, p. 16).
--   2. **Consistent permutation** (Definition 4): a permutation $\alpha$ of $\{1,\dots,d\}$ with $x_{\alpha(1)} \ge \dots \ge x_{\alpha(d)}$. A canonical one, $\alpha_x$, is fixed by sorting the coordinates of $x$ in decreasing order with ties broken by index.
--   3. **Neighbouring points**: $S^{x,0} = \emptyset$ and $S^{x,i} = \{\alpha(1),\dots,\alpha(i)\}$ for $i = 1,\dots,d$.
--   4. **Lovász extension** (2):
--   $$\tilde f(x) = f(S^{x,0}) + \sum_{i=1}^d \big[f(S^{x,i}) - f(S^{x,i-1})\big]\, x_{\alpha(i)},$$
--   evaluated with any given permutation, and $\tilde f$ itself with the canonical one.
--   5. **The vector (3)**: $g_{\alpha(i)} = f(S^{x,i}) - f(S^{x,i-1})$, $i = 1,\dots,d$; and **subgradients** relative to the box: $g \in \partial \tilde f(x)$ iff $\langle g, x-y\rangle \ge \tilde f(x) - \tilde f(y)$ for every $y \in [0,1]^d$ (p. 17).
--   6. $\min f = \min_{A} f(A)$; the projection $P_X(x) = (x\wedge \mathbf 1)\vee \mathbf 0$ and the truncation $T_M(g) = (g \wedge M\mathbf 1)\vee(-M\mathbf 1)$ (p. 19).
--   7. **Simulation oracle** (§2, p. 9; Assumption 1, p. 10). Replications are indexed by slots: gradient slots $(t,k,j)$ for iteration $t < T$, coordinate $k$ and $j\in\{1,2\}$, and rounding slots $(i,s)$ for neighbouring point $i = 0,\dots,d$ and replication $s < n$. Slot $s$ yields a random vector $Z_s = (Z_s(A))_{A}$ of simulation outputs; the slots are mutually independent and measurable, and every $Z_s(A) - f(A)$ is sub-Gaussian with variance proxy $\sigma^2$.
--   8. **Estimator (4)** at $x$ from iteration $t$'s slots: $\hat g_{\alpha(i)} = F(S^{x,i},\xi^1_i) - F(S^{x,i-1},\xi^2_{i-1})$ with $\alpha = \alpha_x$; the **truncation bias** at $x$, $b(x) = \mathbb E[T_M(\hat g(x))] - g(x)$.
--   9. **Algorithm 2**: $x^0 = \mathbb 1_{A_0}$, $x^{t+1} = P_X(x^t - \eta\, T_M(\hat g^t))$ for $t<T$, and $\bar x = \frac1T\sum_{t=0}^{T-1} x^t$; the terms $X_t = \langle g^t + b^t - \tilde g^t, x^t - x^*\rangle$ of Lemma EC.3.
--   10. **Rounding (Algorithm 1)** of a random point $\bar x$: the neighbouring points $S^0,\dots,S^d$ of $\bar x$, the sample means $\hat F_n(S^i) = \frac1n\sum_{s<n} F(S^i,\xi_s)$, and the failure event: some minimizer of $\hat F_n(S^0),\dots,\hat F_n(S^d)$ has $f(S^i) > \min f + \epsilon$.
--
--   These are the objects every statement of the mission is written in.
--
--   **Formalization Note** Points of $\{0,1\}^d$ are `Finset (Fin d)` and indices are 0-based: the paper's $i \in \{1,\dots,d\}$ is `k : Fin d` with $i = k+1$, and $S^{x,i}$ is `nbr α i` for $i : ℕ$. The canonical consistent permutation is `Tuple.sort` of $-x$ (the paper allows any consistent permutation; the value of (2) does not depend on the choice, which is the first milestone). Submodularity is the published definition `NonmonotoneSubmod.Shared.Submodular`. The sub-Gaussian assumption uses Mathlib's `HasSubgaussianMGF` with parameter $\sigma^2$ ($\mathbb E e^{\lambda(Z-f)} \le e^{\sigma^2\lambda^2/2}$), which also makes each output integrable with mean $f(A)$. Each slot is read at exactly one point, so only its marginals matter; the paper's identical distribution of replications is not assumed. The iterate is frozen for $t \ge T$, where no slot exists; only $x^0,\dots,x^{T-1}$ enter $\bar x$.
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. 9 (f, F̂n), p. 10 (Assumption 1), p. 14 (Assumption 2), p. 16 (Assumption 4), p. 17 (Definition 4, eq. (2), (3), ∂f̃), p. 18 (eq. (4), Algorithm 1), p. 19 (P_X, T_M), pp. 19–20 (Algorithm 2), p. ec3 (PDF 41) (b_t), p. ec4 (PDF 42) (X_t)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace GradDOvS.Submod

open MeasureTheory ProbabilityTheory

/-! Zhang, Zheng & Lavaei, arXiv:2010.16250v3, §2–§3 (pp. 9–20): the stochastic submodular
minimization model on `{0,1}^d`, the Lovász extension (Definition 4, eq. (2)), the subgradient (3),
the estimator (4), the projection `P_X` and truncation `T_M` (p. 19), Algorithm 2 (pp. 19–20) and
the rounding step of Algorithm 1 (p. 18).

Conventions: a point of `{0,1}^d` is a `Finset (Fin d)` (a set `A` ↔ its indicator vector); the
paper's index `i ∈ {1,…,d}` is `k : Fin d` with `i = k + 1`; the neighbouring point `S^{x,i}`,
`i = 0,…,d`, is `nbr α i` for `i : ℕ`. -/

/-- The indicator vector `ind A ∈ {0,1}^d ⊆ ℝ^d` of `A ⊆ {1,…,d}`. -/
def ind {d : ℕ} (A : Finset (Fin d)) : Fin d → ℝ := fun i => if i ∈ A then 1 else 0

/-- The box `[0,1]^d`. -/
def box (d : ℕ) : Set (Fin d → ℝ) := Set.Icc 0 1

/-- Standing assumptions of §3 on `X = {0,1}^d`: `d ≥ 1`, Assumption 2 (on `{0,1}^d`, L♮-convexity
is submodularity, p. 16; Definition 4, p. 17) and Assumption 4 (p. 16: `|f x - f y| ≤ L` whenever
`‖x - y‖∞ ≤ 1`, which on `{0,1}^d` is every pair of points). -/
structure Standing {d : ℕ} (L : ℝ) (f : Finset (Fin d) → ℝ) : Prop where
  one_le_d : 1 ≤ d
  submodular : NonmonotoneSubmod.Shared.Submodular f
  lipschitz : ∀ A B : Finset (Fin d), |f A - f B| ≤ L

/-- Definition 4, p. 17: `α` is a consistent permutation of `x` if
`x_{α(1)} ≥ x_{α(2)} ≥ ⋯ ≥ x_{α(d)}`. -/
def IsConsistentPerm {d : ℕ} (x : Fin d → ℝ) (α : Equiv.Perm (Fin d)) : Prop :=
  Antitone (x ∘ α)

/-- The canonical consistent permutation of `x`: sort `-x` increasingly (`Tuple.sort`, which breaks
ties by index). It is consistent by `Tuple.monotone_sort`. -/
noncomputable def canonPerm {d : ℕ} (x : Fin d → ℝ) : Equiv.Perm (Fin d) :=
  Tuple.sort (fun i => -x i)

/-- Definition 4, p. 17: the neighbouring point `S^{x,i} = {α(1), …, α(i)}` (`S^{x,0} = ∅`) for the
consistent permutation `α` of `x`, for `i = 0, …, d`. In 0-based indexing it is the set of `j` with
`α⁻¹ j < i`. -/
def nbr {d : ℕ} (α : Equiv.Perm (Fin d)) (i : ℕ) : Finset (Fin d) :=
  Finset.univ.filter (fun j => ((α.symm j : Fin d) : ℕ) < i)

/-- Formula (2), p. 17, evaluated with a given permutation `α`:
`f(S^{x,0}) + ∑_{i=1}^d [f(S^{x,i}) - f(S^{x,i-1})] x_{α(i)}`. -/
def lovaszWith {d : ℕ} (f : Finset (Fin d) → ℝ) (x : Fin d → ℝ) (α : Equiv.Perm (Fin d)) : ℝ :=
  f (nbr α 0) + ∑ k : Fin d, (f (nbr α ((k : ℕ) + 1)) - f (nbr α k)) * x (α k)

/-- The Lovász extension `f̃` of (2), p. 17, computed with the canonical consistent permutation. -/
noncomputable def lovasz {d : ℕ} (f : Finset (Fin d) → ℝ) (x : Fin d → ℝ) : ℝ :=
  lovaszWith f x (canonPerm x)

/-- The vector (3), p. 17: `g_{α(i)} = f(S^{x,i}) - f(S^{x,i-1})` for `i = 1, …, d`. -/
def chainGrad {d : ℕ} (f : Finset (Fin d) → ℝ) (α : Equiv.Perm (Fin d)) : Fin d → ℝ :=
  fun j => f (nbr α (((α.symm j : Fin d) : ℕ) + 1)) - f (nbr α (α.symm j : Fin d))

/-- The subdifferential of p. 17: `g ∈ ∂f̃(x)` iff `⟨g, x - y⟩ ≥ f̃(x) - f̃(y)` for all `y ∈ [0,1]^d`. -/
def IsSubgradOn {d : ℕ} (f : Finset (Fin d) → ℝ) (x g : Fin d → ℝ) : Prop :=
  ∀ y ∈ box d, lovasz f x - lovasz f y ≤ ∑ i, g i * (x i - y i)

/-- The optimal value `min_{x ∈ {0,1}^d} f(x)` of problem (1). -/
def minf {d : ℕ} (f : Finset (Fin d) → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty f

/-- The projection `P_X(x) = (x ∧ 1) ∨ 0` onto `[0,1]^d`, p. 19. -/
def proj {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ := fun i => max 0 (min 1 (x i))

/-- The truncation `T_M(g) = (g ∧ M1) ∨ (-M1)`, p. 19. -/
def trunc {d : ℕ} (M : ℝ) (g : Fin d → ℝ) : Fin d → ℝ := fun i => max (-M) (min M (g i))

/-- Index set of the simulation replications: gradient slots `(t, k, j)` (iteration `t < T`,
coordinate `k`, the two evaluations `j ∈ {0,1}` of (4)) and rounding slots `(i, s)` (neighbouring
point `i = 0, …, d`, replication `s < n`) of Algorithm 1. -/
abbrev Slot (d T n : ℕ) : Type := (Fin T × Fin d × Fin 2) ⊕ (Fin (d + 1) × Fin n)

/-- The simulation oracle (§2, p. 9; Assumption 1, p. 10). Slot `s` provides a replication
`Z s ω A` of `F(A, ξ_A)` at every point `A`; the slots are mutually independent, each is measurable,
and each output is centred at `f A` and sub-Gaussian with parameter `σ²`. -/
structure IsSimOracle {Ω ι : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (f : Finset (Fin d) → ℝ) (σ : NNReal) (Z : ι → Ω → Finset (Fin d) → ℝ) : Prop where
  measurable : ∀ s, Measurable (Z s)
  indep : iIndepFun Z P
  subgaussian : ∀ s A, HasSubgaussianMGF (fun ω => Z s ω A - f A) (σ ^ 2) P

/-- The subgradient estimator (4), p. 18, at the point `x` from the gradient slots of iteration `t`,
with `α` the canonical consistent permutation of `x`:
`ĝ_{α(i)} = F(S^{x,i}, ξ^1_i) - F(S^{x,i-1}, ξ^2_{i-1})`. -/
noncomputable def gradEst {Ω : Type*} {d T n : ℕ} (Z : Slot d T n → Ω → Finset (Fin d) → ℝ)
    (t : Fin T) (x : Fin d → ℝ) (ω : Ω) : Fin d → ℝ :=
  fun j =>
    Z (Sum.inl (t, (canonPerm x).symm j, 0)) ω (nbr (canonPerm x) ((((canonPerm x).symm j : Fin d) : ℕ) + 1)) -
      Z (Sum.inl (t, (canonPerm x).symm j, 1)) ω (nbr (canonPerm x) ((canonPerm x).symm j : Fin d))

/-- The bias of the truncated estimator at a point `x` (Lemma EC.2, p. ec3):
`b(x) = E[T_M(ĝ(x))] - g(x)` with `g(x)` the vector (3). -/
noncomputable def truncBias {Ω : Type*} [MeasurableSpace Ω] {d T n : ℕ} (P : Measure Ω)
    (Z : Slot d T n → Ω → Finset (Fin d) → ℝ) (f : Finset (Fin d) → ℝ) (M : ℝ) (t : Fin T)
    (x : Fin d → ℝ) : Fin d → ℝ :=
  fun j => (∫ ω, trunc M (gradEst Z t x ω) j ∂P) - chainGrad f (canonPerm x) j

/-- The iterates `x^t` of Algorithm 2, pp. 19–20: `x^0 = ind A₀` and, for `t < T`,
`x^{t+1} = P_X(x^t - η T_M(ĝ^t))` with `ĝ^t` the estimator (4) at `x^t` from slots of iteration `t`.
For `t ≥ T` (no slot) the iterate is frozen; only `t ≤ T` is ever used. -/
noncomputable def ssgdIter {Ω : Type*} {d T n : ℕ} (Z : Slot d T n → Ω → Finset (Fin d) → ℝ)
    (η M : ℝ) (A₀ : Finset (Fin d)) : ℕ → Ω → Fin d → ℝ
  | 0 => fun _ => ind A₀
  | t + 1 => fun ω =>
      if h : t < T then
        proj (ssgdIter Z η M A₀ t ω - η • trunc M (gradEst Z ⟨t, h⟩ (ssgdIter Z η M A₀ t ω) ω))
      else ssgdIter Z η M A₀ t ω

/-- The averaging point `x̄ = (∑_{t=0}^{T-1} x^t) / T` of Algorithm 2, step 7. -/
noncomputable def ssgdAvg {Ω : Type*} {d T n : ℕ} (Z : Slot d T n → Ω → Finset (Fin d) → ℝ)
    (η M : ℝ) (A₀ : Finset (Fin d)) (ω : Ω) : Fin d → ℝ :=
  (1 / (T : ℝ)) • ∑ t ∈ Finset.range T, ssgdIter Z η M A₀ t ω

/-- The term `X_t = ⟨g^t + b^t - g̃^t, x^t - x*⟩` of Lemma EC.3, p. ec4, with `g^t` the vector (3) at
`x^t`, `b^t = b(x^t)` the truncation bias, `g̃^t = T_M(ĝ^t)` and `x* = ind A*`. -/
noncomputable def mdsTerm {Ω : Type*} [MeasurableSpace Ω] {d T n : ℕ} (P : Measure Ω)
    (Z : Slot d T n → Ω → Finset (Fin d) → ℝ) (f : Finset (Fin d) → ℝ) (η M : ℝ)
    (A₀ Astar : Finset (Fin d)) (t : Fin T) (ω : Ω) : ℝ :=
  ∑ j, (chainGrad f (canonPerm (ssgdIter Z η M A₀ t ω)) j
        + truncBias P Z f M t (ssgdIter Z η M A₀ t ω) j
        - trunc M (gradEst Z t (ssgdIter Z η M A₀ t ω) ω) j)
      * (ssgdIter Z η M A₀ t ω j - ind Astar j)

/-- The `i`-th neighbouring point `S^i` of the random point `x̄(ω)` (Algorithm 1, steps 1–2). -/
noncomputable def roundPt {Ω : Type*} {d : ℕ} (xbar : Ω → Fin d → ℝ) (ω : Ω) (i : Fin (d + 1)) :
    Finset (Fin d) :=
  nbr (canonPerm (xbar ω)) i

/-- The sample mean `F̂_n(S^i) = (1/n) ∑_{s<n} F(S^i, ξ_s)` of Algorithm 1, step 3, from the `n`
rounding slots of neighbouring point `i`. -/
noncomputable def roundMean {Ω : Type*} {d T n : ℕ} (Z : Slot d T n → Ω → Finset (Fin d) → ℝ)
    (xbar : Ω → Fin d → ℝ) (ω : Ω) (i : Fin (d + 1)) : ℝ :=
  (1 / (n : ℝ)) * ∑ s : Fin n, Z (Sum.inr (i, s)) ω (roundPt xbar ω i)

/-- The failure event of Algorithm 1 (step 4) applied to `x̄`: some minimizer of the sample means
`F̂_n(S^0), …, F̂_n(S^d)` (any tie-break) has objective value more than `ε` above `min f`. -/
noncomputable def roundFail {Ω : Type*} {d T n : ℕ} (f : Finset (Fin d) → ℝ) (ε : ℝ)
    (Z : Slot d T n → Ω → Finset (Fin d) → ℝ) (xbar : Ω → Fin d → ℝ) : Set Ω :=
  {ω | ∃ i : Fin (d + 1), (∀ j, roundMean Z xbar ω i ≤ roundMean Z xbar ω j) ∧
      minf f + ε < f (roundPt xbar ω i)}

end GradDOvS.Submod


