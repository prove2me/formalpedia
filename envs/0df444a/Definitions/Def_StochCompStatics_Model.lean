-- Prove2me | Definitions.Def_StochCompStatics_Model
-- name    : StochCompStatics_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:00.052741+00:00
-- url     : https://prove2.me/theorems/2d1cf01e-f5af-4f7b-812d-9cdf923055b4
-- title:
--   The discounted MDP $(S,A,\Gamma,p,r,\beta)$: $h$, the Bellman operator $T$, the policy correspondence $G$, Assumption 1 and the standing assumptions
-- statement:
--   A discounted dynamic program is a tuple $(S,A,\Gamma,p,r,\beta)$: a state space $S$ (a measurable space with a partial order $\le$), an action space $A\subseteq\mathbb R$, a feasibility correspondence $\Gamma$ assigning to every state $s$ a non-empty set $\Gamma(s)\subseteq A$ of feasible actions, a transition probability $p$ ($p(s,a,\cdot)$ is the law of the next state), a single-period payoff $r:S\times A\to\mathbb R$, and a discount factor $0<\beta<1$.
--
--   1. For $f:S\to\mathbb R$, equation (1) defines
--   $$
--   h(s,a,f)=r(s,a)+\beta\int_S f(s')\,p(s,a,ds'),\qquad Tf(s)=\max_{a\in\Gamma(s)}h(s,a,f).
--   $$
--   2. The **optimal policy correspondence** is $G(s)=\{a\in\Gamma(s):V(s)=h(s,a,V)\}$, and the **policy function** is $g(s)=\max G(s)$.
--   3. $p$ is **monotone** if for every increasing $f$ the map $(s,a)\mapsto\int_S f(s')\,p(s,a,ds')$ is increasing on $S\times A$ (componentwise order); $p$ has **stochastically increasing differences** if $(s,a)\mapsto p(s,a,B)$ has increasing differences for every measurable upper set $B$.
--   4. A correspondence $G$ is **ascending** if $s_1\le s_2$, $b\in G(s_1)$, $b'\in G(s_2)$ imply $\max\{b,b'\}\in G(s_2)$ and $\min\{b,b'\}\in G(s_1)$.
--   5. **Assumption 1**: (i) $r(s,a)$ is increasing in $s$ and has increasing differences in $(s,a)$; (ii) $p$ is monotone and has stochastically increasing differences; (iii) $s_1\le s_2$ implies $\Gamma(s_1)\subseteq\Gamma(s_2)$.
--   6. The **standing assumptions** for $\beta$ and a function $V$: the iterates $T^n0$ converge uniformly to $V$; $V=TV$ with the maximum attained at every state; the maximum defining every iterate is attained; and the iterates and $V$ are measurable and integrable against every $p(s,a,\cdot)$, $a\in A$.
--
--   These objects are the vocabulary of every statement of the mission: Assumption 1 and the standing assumptions are the hypotheses of Propositions 5 and 6 and of Theorem 3.
--
--   **Formalization Note** $p$ is a Markov kernel from $S\times\mathbb R$ to $S$. The maximum is `sSup` of the image $h(s,\Gamma(s),f)$; since `sSup` of an unbounded set is $0$ in Lean, attainment is assumed explicitly wherever the paper writes max. Monotonicity of $p$ is required for the increasing $f$ that are measurable and integrable against every $p(s,a,\cdot)$ (footnote 9). Increasing differences and the induced set order are the published definitions `Supermodularity.Monotonicity.IncreasingDifferencesOn` and `Supermodularity.Lattices.InducedSetOrder`. The paper assumes $T^nf\to V$ uniformly for every $f$ and that $V$ is the unique continuous fixed point; only $f=0$ is assumed here, and the uniform limit determines $V$.
-- source:
--   Light, Stochastic Comparative Statics in Markov Decision Processes, arXiv:1904.05481v2, §2, pp.4–6 (model, eq. (1), G, g, standing assumptions); Definition 1(i), p.8; footnote 9, p.8; §3.2, p.11 (increasing differences, upper sets, stochastically increasing differences, ascending, Assumption 1)

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

namespace StochCompStatics

open MeasureTheory ProbabilityTheory Filter Supermodularity.Monotonicity Supermodularity.Lattices

variable {S : Type*} [MeasurableSpace S]

/-- The function `h(s, a, f) = r(s, a) + β ∫_S f(s') p(s, a, ds')` of equation (1)
(Light, Stochastic Comparative Statics in Markov Decision Processes, arXiv:1904.05481v2, §2,
eq. (1), p.5).

**Formalization Note** The transition probability `p` is a kernel from `S × ℝ` to `S`: actions are
real numbers (the paper's `A ⊆ ℝ`), and `p (s, a)` is the law of the next state. The integral is
the Bochner integral, which is `0` for a non-integrable `f`; every statement that uses `h` assumes
the integrability of the paper's footnote 9 explicitly. -/
noncomputable def h (p : Kernel (S × ℝ) S) (r : S → ℝ → ℝ) (β : ℝ) (f : S → ℝ) (s : S) (a : ℝ) :
    ℝ :=
  r s a + β * ∫ s', f s' ∂(p (s, a))

/-- The Bellman operator `Tf(s) = max_{a ∈ Γ(s)} h(s, a, f)` (arXiv:1904.05481v2, §2, p.5).

**Formalization Note** The maximum is written as `sSup` of the image `h(s, Γ(s), f)`. In `ℝ`,
`sSup` of an empty or unbounded set is `0`, so every statement that uses `bellman` assumes that the
maximum is attained (an `IsGreatest` hypothesis), which is what the paper's `max` presupposes. -/
noncomputable def bellman (Γ : S → Set ℝ) (p : Kernel (S × ℝ) S) (r : S → ℝ → ℝ) (β : ℝ)
    (f : S → ℝ) (s : S) : ℝ :=
  sSup (h p r β f s '' Γ s)

/-- The optimal policy correspondence `G(s) = {a ∈ Γ(s) : V(s) = h(s, a, V)}`
(arXiv:1904.05481v2, §2, p.6). -/
def optSet (Γ : S → Set ℝ) (p : Kernel (S × ℝ) S) (r : S → ℝ → ℝ) (β : ℝ) (V : S → ℝ) (s : S) :
    Set ℝ :=
  {a | a ∈ Γ s ∧ V s = h p r β V s a}

/-- The feasibility correspondence: for every state `s`, the set `Γ(s)` of feasible actions is a
non-empty subset of the action space `A ⊆ ℝ` (arXiv:1904.05481v2, §2, pp.4–5).

**Formalization Note** The paper also asks the graph `Γ ⊆ S × A` and its sections to be
measurable; no statement of this mission uses that, so it is dropped. -/
def IsActionCorr (A : Set ℝ) (Γ : S → Set ℝ) : Prop :=
  ∀ s, (Γ s).Nonempty ∧ Γ s ⊆ A

/-- Definition 1(i) (arXiv:1904.05481v2, p.8): `p` is **monotone** if for every increasing
function `f` the function `(s, a) ↦ ∫_S f(s') p(s, a, ds')` is increasing in `(s, a)`.

**Formalization Note** `S × ℝ` carries the componentwise order, and the monotonicity is required
on `S × A`, the paper's domain of `p`. Following footnote 9 (p.8, "all functions are assumed to be
integrable"), the condition is imposed for the increasing functions `f` that are measurable and
integrable against every `p(s, a)` with `a ∈ A`; for every other `f` the integral does not exist. -/
def IsMonotoneKernel [Preorder S] (A : Set ℝ) (p : Kernel (S × ℝ) S) : Prop :=
  ∀ f : S → ℝ, Monotone f → Measurable f → (∀ s, ∀ a ∈ A, Integrable f (p (s, a))) →
    MonotoneOn (fun x : S × ℝ => ∫ s', f s' ∂(p x)) (Set.univ ×ˢ A)

/-- Stochastically increasing differences (arXiv:1904.05481v2, §3.2, p.11): `p` has
stochastically increasing differences if `p(s, a, B)` has increasing differences in `(s, a)` on
`S × A` for every upper set `B ∈ B(S)`. -/
def HasStochIncDiff [PartialOrder S] (A : Set ℝ) (p : Kernel (S × ℝ) S) : Prop :=
  ∀ B : Set S, IsUpperSet B → MeasurableSet B →
    IncreasingDifferencesOn (fun s a => (p (s, a) B).toReal) (Set.univ ×ˢ A)

/-- A correspondence `G : S → 2^ℝ` is **ascending** (arXiv:1904.05481v2, §3.2, p.11) if
`s₂ ≥ s₁`, `b ∈ G(s₁)` and `b' ∈ G(s₂)` imply `max{b, b'} ∈ G(s₂)` and `min{b, b'} ∈ G(s₁)`,
i.e. `G(s₁) ⊑ G(s₂)` in the induced set order. -/
def IsAscending {X : Type*} [Preorder X] (G : X → Set ℝ) : Prop :=
  ∀ ⦃s₁ s₂ : X⦄, s₁ ≤ s₂ → InducedSetOrder (G s₁) (G s₂)

/-- Assumption 1 (arXiv:1904.05481v2, §3.2, p.11):
(i) `r(s, a)` is increasing in `s` and has increasing differences in `(s, a)`;
(ii) `p` is monotone and has stochastically increasing differences;
(iii) `s₁ ≤ s₂` implies `Γ(s₁) ⊆ Γ(s₂)`.

**Formalization Note** The monotonicity of `r` in `s` is required for every action `a ∈ A`, and
the increasing differences of `r` on `S × A`. -/
def Assumption1 [PartialOrder S] (A : Set ℝ) (Γ : S → Set ℝ) (p : Kernel (S × ℝ) S)
    (r : S → ℝ → ℝ) : Prop :=
  ((∀ a ∈ A, Monotone fun s => r s a) ∧ IncreasingDifferencesOn r (Set.univ ×ˢ A)) ∧
  (IsMonotoneKernel A p ∧ HasStochIncDiff A p) ∧
  (∀ ⦃s₁ s₂ : S⦄, s₁ ≤ s₂ → Γ s₁ ⊆ Γ s₂)

/-- The standing assumptions on the value function (arXiv:1904.05481v2, §2, p.6, and
footnote 9, p.8), for the discount factor `β`: `V` is the uniform limit of the value iterates
`Tⁿ0`, `V` satisfies the Bellman equation `TV = V` with its maximum attained, the maximum defining
every iterate is attained, and the iterates and `V` are measurable and integrable against every
`p(s, a)`, `a ∈ A`.

**Formalization Note** The paper assumes that the value function is the unique continuous
solution of `TV = V` and that `Tⁿf → V` uniformly for every `f`. Only `f = 0` is assumed here, and
continuity and uniqueness are not assumed; since a uniform limit is unique, `V` is determined by
the first clause. The attainment clauses encode the `max` in the definition of `T` (p.5), and the
measurability and integrability clauses are footnote 9 ("all functions are assumed to be
integrable"). -/
def StandingAssumptions (A : Set ℝ) (Γ : S → Set ℝ) (p : Kernel (S × ℝ) S) (r : S → ℝ → ℝ)
    (β : ℝ) (V : S → ℝ) : Prop :=
  TendstoUniformly (fun n => (bellman Γ p r β)^[n] 0) V atTop ∧
  (∀ s, IsGreatest (h p r β V s '' Γ s) (V s)) ∧
  (∀ n s, ∃ a ∈ Γ s,
    IsGreatest (h p r β ((bellman Γ p r β)^[n] 0) s '' Γ s) (h p r β ((bellman Γ p r β)^[n] 0) s a)) ∧
  (∀ n, Measurable ((bellman Γ p r β)^[n] 0) ∧
    ∀ s, ∀ a ∈ A, Integrable ((bellman Γ p r β)^[n] 0) (p (s, a))) ∧
  (Measurable V ∧ ∀ s, ∀ a ∈ A, Integrable V (p (s, a)))

/-- The policy function `g(s) = max G(s)` (arXiv:1904.05481v2, §2, p.6): `g(s)` is the greatest
element of the optimal policy correspondence `G(s)`, and `g` is measurable.

**Formalization Note** Policies are Borel measurable functions (p.5); the measurability of `g` is
what makes the state process under `g` a Markov chain with the laws `stateLaw` of
`Def_StochCompStatics_ChainLaw`. -/
def IsPolicyFunction (Γ : S → Set ℝ) (p : Kernel (S × ℝ) S) (r : S → ℝ → ℝ) (β : ℝ)
    (V g : S → ℝ) : Prop :=
  (∀ s, IsGreatest (optSet Γ p r β V s) (g s)) ∧ Measurable g

end StochCompStatics


