-- Prove2me | Definitions.Def_WhittleGittins_Retirement_BanditProcess
-- name    : WhittleGittins_Retirement_BanditProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:58.092003+00:00
-- url     : https://prove2.me/theorems/e55d4430-d96f-4ac2-9d45-2b095b9f1276
-- title:
--   Whittle's bandit process with a retirement option: φᵢ(xᵢ, sᵢ, M), F(x, s, M), the index Mᵢ, F̂ of (13), Pᵢ of (17), policies and the index rule
-- statement:
--   This file sets up the model of Whittle's *Multi-armed Bandits and the Gittins Index* (1980), Sections 1, 2 and 4.
--
--   **Projects.** There are $N$ projects, indexed by $i$. Project $i$ has a state $x_i$ in a measurable space $X_i$. If project $i$ is engaged in state $x_i$, one earns the expected immediate reward $R_i(x_i)$ and the state moves to $x_i(t+1)$ according to a Markov transition kernel $P_i$ (which may depend on $i$); the states of all other projects stay unchanged. Rewards are discounted by a factor $\beta$ with $0 \le \beta < 1$, and are uniformly bounded:
--   $$k(1-\beta) \le R_i(x_i) \le K(1-\beta) \qquad (1)$$
--   for constants $k, K$ (possibly negative). The combined state is $x = (x_1,\dots,x_N)$.
--
--   **Infinite-horizon values.** The operator (3) is
--   $$L_i\theta(x) = R_i(x_i) + \beta\, \mathbb E[\theta(x(t+1)) \mid x(t) = x,\ i(t) = i].$$
--   A function $\Phi$ is a *continuing value* if it is a bounded measurable solution of $\Phi = \max_i L_i\Phi$ (2). A function $F(x, M)$ is an *$M$-process value* if, for every retirement reward $M$, $F(\cdot, M)$ is a bounded measurable solution of $F = \max(M, \max_i L_i F)$ (4). A function $\varphi_i(x_i, M)$ is a *one-project value* for project $i$ if it is, for every $M$, a bounded measurable solution of $\varphi_i = \max(M, L_i\varphi_i)$ (9). The infinite-horizon index is $M_i(x_i) = \inf\{M : \varphi_i(x_i, M) = M\}$.
--
--   **Finite horizons.** A budget vector $s = (s_1,\dots,s_N)$ of natural numbers bounds the number of further times each project may be operated; a project with $s_i > 0$ is *active*, and $D_i s$ lowers $s_i$ by one. The single-project value with horizon $s_i$ is defined by the recursion (14):
--   $$\varphi_i(x_i, 0, M) = M,\qquad \varphi_i(x_i, n+1, M) = \max\big[M,\ R_i(x_i) + \beta\, \mathbb E\,\varphi_i(x_i(t+1), n, M)\big].$$
--   The maximal expected reward $F(x, s, M)$ of the $M$-process with process-time limits $s$ is the backward-induction value: $F(x, 0, M) = M$, and
--   $$F(x, s, M) = \max\Big(M,\ \max_{i:\, s_i > 0}\big[R_i(x_i) + \beta\,\mathbb E\,F(x(t+1), D_i s, M)\big]\Big),$$
--   which equals $M$ when no project is active. The index is $M_i(x_i, s_i) = \inf\{M : \varphi_i(x_i, s_i, M) = M\}$.
--
--   **The formula of Section 4.** With $\partial/\partial m$ the right derivative,
--   $$\hat F(x, s, M) = K - \int_M^K \prod_i \frac{\partial \varphi_i(x_i, s_i, m)}{\partial m}\, dm \quad (13),\qquad P_i(x, s, M) = \prod_{j\ne i}\frac{\partial \varphi_j(x_j, s_j, M)}{\partial M}\quad (17),$$
--   and $L_i\hat F(x, s, M) = R_i(x_i) + \beta\,\mathbb E\,\hat F(x(t+1), D_i s, M)$ is the extended operator (15) applied to $\hat F$.
--
--   **Policies.** A Markov allocation policy chooses, in each $(x, s)$ and for retirement reward $M$, either a project to engage or retirement. It is *feasible* if it only engages active projects, and *measurable* if each decision set $\{x : \sigma(x, s, M) = i\}$ is measurable. Its value is the expected discounted reward it earns (retiring pays $M$). The *index rule* engages an active project whose index $M_i(x_i, s_i)$ is maximal among the active projects if that maximal value exceeds $M$, and otherwise retires; ties are broken arbitrarily.
--
--   These objects are the language of Theorem 1 and of every relation in its proof.
--
--   **Formalization Note** Projects are indexed by `Fin N` (0-based; the paper uses $1,\dots,N$). The infinite-horizon maxima over $i$ use `Finset.sup'` and need `[NeZero N]`. The phrase "unique bounded solution" is encoded as "bounded measurable solution" (uniqueness is a consequence of the contraction). $F(x, s, M)$ is defined by backward induction on $\sum_i s_i$ through an explicit fuel argument (`Fuel`), not through $\hat F$, the index or a policy. The index of an exhausted project ($s_i = 0$) is the paper's $-\infty$; in Lean `index` returns the junk value `0` there, so every use (the index rule, the theorems) only ranges over active projects. $\partial/\partial m$ is the right derivative `derivWithin f (Set.Ici m) m`. Policies are Markov in $(x, s, M)$, valued in `Option (Fin N)` with `none` meaning retirement, and their value is defined by the same recursion as $F$ with the maximum replaced by the policy's choice.
-- source:
--   Whittle, Multi-armed Bandits and the Gittins Index, J. R. Statist. Soc. B 42 (1980), pp. 143–144 (PDF 1–2), Sections 1–2, (1)–(4); p. 146 (PDF 4), (9) and (13); p. 147 (PDF 5), (14), (15), the index Mᵢ, Theorem 1, (17)

import Mathlib

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Whittle's multi-project bandit process (Sections 1–2, pp. 143–144): `N` projects indexed by
`Fin N`; project `i` has a measurable state space `X i`, a Markov transition kernel `P i` (which
may depend on `i`), and a measurable expected one-step reward `R i`. Rewards are discounted by
`β` with `0 ≤ β < 1` and satisfy the uniform bound (1), `k(1 − β) ≤ Rᵢ(xᵢ) ≤ K(1 − β)`. -/
structure BanditProcess (N : ℕ) (X : Fin N → Type*) [∀ i, MeasurableSpace (X i)] where
  /-- Transition kernel of project `i` (applied only when project `i` is engaged). -/
  P : ∀ i, Kernel (X i) (X i)
  P_markov : ∀ i, IsMarkovKernel (P i)
  /-- Expected immediate reward `Rᵢ(xᵢ)` of engaging project `i` in state `xᵢ`. -/
  R : ∀ i, X i → ℝ
  R_meas : ∀ i, Measurable (R i)
  /-- Discount factor. -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- The constants `k`, `K` of bound (1) (possibly negative). -/
  k : ℝ
  K : ℝ
  /-- Bound (1). -/
  bound : ∀ i (x : X i), k * (1 - β) ≤ R i x ∧ R i x ≤ K * (1 - β)

variable {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]

/-! ### Infinite horizon: the operators (3) and the value equations (2), (4), (9) -/

/-- The operator `Lᵢ` of (3): `Lᵢ θ(x) = Rᵢ(xᵢ) + β E[θ(x(t+1)) | x(t) = x, i(t) = i]`, where only
the `i`th component of the state moves, according to `P i`. -/
noncomputable def Lop (B : BanditProcess N X) (i : Fin N) (θ : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    ℝ :=
  B.R i (x i) + B.β * ∫ y, θ (Function.update x i y) ∂(B.P i (x i))

/-- The one-project version of `Lᵢ`, acting on functions of `xᵢ` only. -/
noncomputable def Lop1 (B : BanditProcess N X) (i : Fin N) (ψ : X i → ℝ) (xi : X i) : ℝ :=
  B.R i xi + B.β * ∫ y, ψ y ∂(B.P i xi)

/-- `Φ` is the value of the continuing process: a bounded measurable solution of the dynamic
programming equation (2), `Φ = maxᵢ Lᵢ Φ`. (Bounded solutions of (2) are unique.) -/
def IsContinuingValue [NeZero N] (B : BanditProcess N X) (Φ : (∀ j, X j) → ℝ) : Prop :=
  Measurable Φ ∧ (∃ C : ℝ, ∀ x, |Φ x| ≤ C) ∧
    ∀ x, Φ x = Finset.univ.sup' Finset.univ_nonempty (fun i => Lop B i Φ x)

/-- `F` is the value of the `M`-process: for every retirement reward `M`, `F(·, M)` is a bounded
measurable solution of (4), `F = max(M, maxᵢ Lᵢ F)`. -/
def IsMProcessValue [NeZero N] (B : BanditProcess N X) (F : (∀ j, X j) → ℝ → ℝ) : Prop :=
  ∀ M : ℝ, Measurable (fun x => F x M) ∧ (∃ C : ℝ, ∀ x, |F x M| ≤ C) ∧
    ∀ x, F x M = max M (Finset.univ.sup' Finset.univ_nonempty (fun i => Lop B i (fun z => F z M) x))

/-- `φᵢ` is the value of the single-project `M`-process for project `i`: for every `M`,
`φᵢ(·, M)` is a bounded measurable solution of (9), `φᵢ = max(M, Lᵢ φᵢ)`. -/
def IsOneProjectValue (B : BanditProcess N X) (i : Fin N) (φ : X i → ℝ → ℝ) : Prop :=
  ∀ M : ℝ, Measurable (fun xi => φ xi M) ∧ (∃ C : ℝ, ∀ xi, |φ xi M| ≤ C) ∧
    ∀ xi, φ xi M = max M (Lop1 B i (fun z => φ z M) xi)

/-- The infinite-horizon index `Mᵢ(xᵢ)`: the infimal `M` with `φᵢ(xᵢ, M) = M`. -/
noncomputable def indexInf {i : Fin N} (φ : X i → ℝ → ℝ) (xi : X i) : ℝ :=
  sInf {M : ℝ | φ xi M = M}

/-! ### Finite horizons (Section 4): budgets `s`, the values `φᵢ(xᵢ, sᵢ, M)` and `F(x, s, M)` -/

/-- The projects that may still be engaged: those with remaining process time `sᵢ > 0`. -/
def active (s : Fin N → ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => 0 < s i)

/-- `Dᵢ s`: decrease `sᵢ` by one (applied only to active `i`). -/
def decr (s : Fin N → ℕ) (i : Fin N) : Fin N → ℕ :=
  Function.update s i (s i - 1)

/-- The right-hand side `max(M, maxᵢ gᵢ)` of a dynamic programming equation, the inner maximum
ranging over the active projects; equal to `M` when no project is active. -/
noncomputable def bellmanMax (s : Fin N → ℕ) (M : ℝ) (g : Fin N → ℝ) : ℝ :=
  if h : (active s).Nonempty then max M ((active s).sup' h g) else M

/-- `φᵢ(xᵢ, sᵢ, M)`: the single-project `M`-process value when project `i` may be operated at most
`sᵢ` more times, by the recursion (14): `φᵢ(xᵢ, 0, M) = M` and
`φᵢ(xᵢ, n + 1, M) = max(M, Rᵢ(xᵢ) + β E[φᵢ(xᵢ(t+1), n, M)])`. -/
noncomputable def phi (B : BanditProcess N X) (i : Fin N) : X i → ℕ → ℝ → ℝ
  | _, 0, M => M
  | xi, n + 1, M => max M (B.R i xi + B.β * ∫ y, phi B i y n M ∂(B.P i xi))

/-- Backward induction for the multi-project `M`-process, with an explicit fuel argument (the
intended fuel is `∑ i, sᵢ`, which every engagement decreases by one). -/
noncomputable def Fuel (B : BanditProcess N X) : ℕ → (∀ j, X j) → (Fin N → ℕ) → ℝ → ℝ
  | 0, _, _, M => M
  | n + 1, x, s, M =>
      bellmanMax s M (fun i =>
        B.R i (x i) + B.β * ∫ y, Fuel B n (Function.update x i y) (decr s i) M ∂(B.P i (x i)))

/-- `F(x, s, M)`: the maximal expected reward of the `M`-process when the process time of project
`i` may not exceed `sᵢ`, i.e. the backward-induction value of `F = max(M, maxᵢ Lᵢ F)` (with `Lᵢ` as
in (15), maximum over active projects) and `F(x, 0, M) = M`. -/
noncomputable def F (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ) : ℝ :=
  Fuel B (∑ i, s i) x s M

/-- The finite-horizon index `Mᵢ(xᵢ, sᵢ)`: the infimal `M` with `φᵢ(xᵢ, sᵢ, M) = M`. It is only
meaningful for `sᵢ > 0`; for `sᵢ = 0` the paper's value is `−∞` and every use is guarded by
`0 < sᵢ`. -/
noncomputable def index (B : BanditProcess N X) (i : Fin N) (xi : X i) (n : ℕ) : ℝ :=
  sInf {M : ℝ | phi B i xi n M = M}

/-- Right derivative `∂f/∂m` at `m` (derivative within `[m, ∞)`). -/
noncomputable def rderiv (f : ℝ → ℝ) (m : ℝ) : ℝ :=
  derivWithin f (Set.Ici m) m

/-- `F̂(x, s, M) = K − ∫_M^K ∏ᵢ ∂φᵢ(xᵢ, sᵢ, m)/∂m dm`, formula (13). -/
noncomputable def Fhat (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ) : ℝ :=
  B.K - ∫ m in M..B.K, ∏ i, rderiv (fun m' => phi B i (x i) (s i) m') m

/-- `Pᵢ(x, s, M) = ∏_{j ≠ i} ∂φⱼ(xⱼ, sⱼ, M)/∂M`, formula (17). -/
noncomputable def Pdist (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N)
    (M : ℝ) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, rderiv (fun m' => phi B j (x j) (s j) m') M

/-- `Lᵢ F̂(x, s, M)` with the extended operator (15):
`Rᵢ(xᵢ) + β E[F̂(x(t+1), Dᵢ s, M) | x(t) = x, i(t) = i]`. -/
noncomputable def LFhat (B : BanditProcess N X) (i : Fin N) (x : ∀ j, X j) (s : Fin N → ℕ)
    (M : ℝ) : ℝ :=
  B.R i (x i) + B.β * ∫ y, Fhat B (Function.update x i y) (decr s i) M ∂(B.P i (x i))

/-! ### Markov allocation policies with a retirement option -/

/-- A Markov allocation policy: in state `x` with budgets `s` and retirement reward `M` it engages
project `i` (`some i`) or retires (`none`). -/
abbrev Policy (N : ℕ) (X : Fin N → Type*) := (∀ j, X j) → (Fin N → ℕ) → ℝ → Option (Fin N)

/-- A policy is feasible if it only engages projects with remaining process time. -/
def IsFeasible (σ : Policy N X) : Prop :=
  ∀ x s M i, σ x s M = some i → 0 < s i

/-- A policy is measurable if each decision `{x | σ(x, s, M) = i}` is a measurable set of states. -/
def IsMeasurablePolicy (σ : Policy N X) : Prop :=
  ∀ s M i, MeasurableSet {x | σ x s M = some i}

/-- Expected discounted reward of a policy, with an explicit fuel argument (intended `∑ i, sᵢ`):
retiring yields `M`; engaging an active project `i` yields `Rᵢ(xᵢ)` plus `β` times the expected
value from the new state with budgets `Dᵢ s`. -/
noncomputable def polValueFuel (B : BanditProcess N X) (σ : Policy N X) :
    ℕ → (∀ j, X j) → (Fin N → ℕ) → ℝ → ℝ
  | 0, _, _, M => M
  | n + 1, x, s, M =>
      match σ x s M with
      | none => M
      | some i =>
          if 0 < s i then
            B.R i (x i) + B.β * ∫ y, polValueFuel B σ n (Function.update x i y) (decr s i) M
              ∂(B.P i (x i))
          else M

/-- The expected total discounted reward of the policy `σ` in the `M`-process from `(x, s)`. -/
noncomputable def polValue (B : BanditProcess N X) (σ : Policy N X) (x : ∀ j, X j)
    (s : Fin N → ℕ) (M : ℝ) : ℝ :=
  polValueFuel B σ (∑ i, s i) x s M

/-- The (finite-horizon) Gittins index rule of Theorem 1: at `(x, s)` it engages an active project
whose index `Mᵢ(xᵢ, sᵢ)` is maximal among the active projects, provided that maximal value exceeds
`M`, and otherwise retires. Ties among projects may be broken arbitrarily. -/
def IsIndexRule (B : BanditProcess N X) (σ : Policy N X) : Prop :=
  ∀ x s M,
    (∀ i, σ x s M = some i →
      0 < s i ∧ (∀ j, 0 < s j → index B j (x j) (s j) ≤ index B i (x i) (s i)) ∧
        M < index B i (x i) (s i)) ∧
    (σ x s M = none → ∀ j, 0 < s j → index B j (x j) (s j) ≤ M)

end WhittleGittins.Retirement


