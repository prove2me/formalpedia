-- Prove2me | Definitions.Def_WhittleGittins_Retirement_Supplement_SuperBanditProcess
-- name    : WhittleGittins_Retirement_Supplement_SuperBanditProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:48:04.144814+00:00
-- url     : https://prove2.me/theorems/fc79439f-46b5-4d3c-95cf-d40e0faaa107
-- title:
--   Whittle's superprocess: controlled projects, the u-optimized values φᵢ, F, the modified index Mᵢ, F̂ of (13), control rules and the index rule
-- statement:
--   This file sets up the superprocess model of Section 5 of Whittle's *Multi-armed Bandits and the Gittins Index* (1980), on top of the published model of the base mission (`WhittleGittins.Retirement.BanditProcess`), whose helpers (active projects, $D_i s$, the right derivative, the infinite-horizon index, project policies) it reuses.
--
--   **Superprocess.** There are $N$ projects. Project $i$ has a state $x_i$ in a measurable space $X_i$ and a nonempty measurable set $U_i$ of procedures (controls). If project $i$ is engaged in state $x_i$ with procedure $u$, one earns the expected reward $R_i(x_i, u)$ and $x_i$ moves according to a Markov kernel $P_i(\cdot \mid x_i, u)$; all other projects stay frozen. At each instant one first chooses the project, then the procedure. Rewards are discounted by $\beta$ with $0 \le \beta < 1$ and obey bound (1) uniformly in the control:
--   $$k(1-\beta) \le R_i(x_i, u) \le K(1-\beta).$$
--
--   **Infinite horizon.** The operator of Section 5 is
--   $$L_{iu}\theta(x) = R_i(x_i, u) + \beta\,\mathbb E[\theta(x(t+1)) \mid x(t) = x,\ i(t) = i,\ u(t) = u].$$
--   A function $\varphi_i(x_i, M)$ is a one-project value if, for every $M$, it is a bounded measurable solution of (22), $\varphi_i = \max(M, \sup_u L_{iu}\varphi_i)$; a function $F(x, M)$ is an $M$-process value if, for every $M$, it is a bounded measurable solution of $F = \max(M, \max_i \sup_u L_{iu} F)$. Control maps $h_i : X_i \to U_i$ are *$M$-independent optimal controls* if $h_i(x_i)$ attains $\sup_u L_{iu}\varphi_i(x_i, M)$ whenever $M < \varphi_i(x_i, M)$ (the continuation region), for every $M$.
--
--   **Finite horizons.** With budgets $s = (s_1, \dots, s_N)$, the $u$-optimized one-project value is
--   $$\varphi_i(x_i, 0, M) = M,\qquad \varphi_i(x_i, n+1, M) = \max\Big[M,\ \sup_u \big(R_i(x_i, u) + \beta\,\mathbb E[\varphi_i(x_i(t+1), n, M) \mid u]\big)\Big],$$
--   and $F(x, s, M)$ is the backward-induction value $F(x, 0, M) = M$,
--   $$F(x, s, M) = \max\Big(M,\ \max_{i:\, s_i > 0} \sup_u \big[R_i(x_i, u) + \beta\,\mathbb E\,F(x(t+1), D_i s, M)\big]\Big).$$
--   The modified index is $M_i(x_i, s_i) = \inf\{M : \varphi_i(x_i, s_i, M) = M\}$, and
--   $$\hat F(x, s, M) = K - \int_M^K \prod_i \frac{\partial \varphi_i(x_i, s_i, m)}{\partial m}\, dm \qquad (13)$$
--   with these $\varphi_i$. Control maps $h_i(x_i, n)$ are $M$-independent optimal controls if $h_i(x_i, n+1)$ attains the supremum over $u$ in the recursion for $\varphi_i(x_i, n+1, M)$ whenever $M < \varphi_i(x_i, n+1, M)$, for every $M$.
--
--   **Policies.** A Markov policy is a project choice $\sigma(x, s, M)$ (a project or retirement, as in the base mission) together with a control rule $c_i(x, s, M) \in U_i$. Its value is the expected discounted reward it earns, retirement paying $M$. The index rule engages an active project whose modified index $M_i(x_i, s_i)$ is maximal among the active projects if that maximum exceeds $M$, and otherwise retires; ties are broken arbitrarily. With control maps $h_i$, the induced control rule applies $h_i(x_i, s_i)$ to the engaged project.
--
--   These objects are the language of Theorem 2.
--
--   **Formalization Note** Projects are indexed by `Fin N`. Every supremum over $u$ is the real `⨆`; the brackets are bounded above and below because of bound (1) and the boundedness of the value functions, and $U_i$ is nonempty, so the junk value of an empty or unbounded supremum never arises. The infinite-horizon maxima over $i$ use `Finset.sup'` and need `[NeZero N]`. The index of an exhausted project is the paper's $-\infty$; it is never consulted, because the index rule ranges over active projects only. The right derivative is `derivWithin f (Set.Ici m) m`. "Unique bounded solution" is encoded as "bounded measurable solution" (uniqueness follows from the contraction). Rewards are jointly measurable in $(x_i, u)$; a control rule is measurable if each $x \mapsto c_i(x, s, M)$ is.
-- source:
--   Whittle, Multi-armed Bandits and the Gittins Index, J. R. Statist. Soc. B 42 (1980), p. 148 (PDF 6), Section 5, Superprocesses, (22) and the following display; p. 144 (PDF 2), bound (1); p. 147 (PDF 5), (13), (14), the index Mᵢ

import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

namespace WhittleGittins.Retirement.Supplement

open MeasureTheory ProbabilityTheory

/-- Whittle's superprocess (Section 5, p. 148): a multi-project bandit process in which project
`i`, when engaged in state `xᵢ`, is operated with a procedure (control) `u ∈ U i` that affects
both the expected reward `Rᵢ(xᵢ, u)` and the transition `xᵢ(t) → xᵢ(t+1)`, which follows the
Markov kernel `P i` at `(xᵢ, u)`. Unengaged projects stay frozen. Rewards are discounted by `β`
with `0 ≤ β < 1` and satisfy bound (1) uniformly in the control:
`k(1 − β) ≤ Rᵢ(xᵢ, u) ≤ K(1 − β)`. Every project has at least one control. -/
structure SuperBanditProcess (N : ℕ) (X : Fin N → Type*) [∀ i, MeasurableSpace (X i)]
    (U : Fin N → Type*) [∀ i, MeasurableSpace (U i)] where
  /-- Every project has at least one available procedure. -/
  U_nonempty : ∀ i, Nonempty (U i)
  /-- Transition kernel of project `i` under control `u` (applied only when `i` is engaged). -/
  P : ∀ i, Kernel (X i × U i) (X i)
  P_markov : ∀ i, IsMarkovKernel (P i)
  /-- Expected immediate reward `Rᵢ(xᵢ, u)` of engaging project `i` in state `xᵢ` with control `u`. -/
  R : ∀ i, X i → U i → ℝ
  R_meas : ∀ i, Measurable (Function.uncurry (R i))
  /-- Discount factor. -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- The constants `k`, `K` of bound (1) (possibly negative). -/
  k : ℝ
  K : ℝ
  /-- Bound (1), uniformly in the control. -/
  bound : ∀ i (x : X i) (u : U i), k * (1 - β) ≤ R i x u ∧ R i x u ≤ K * (1 - β)

variable {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]
  {U : Fin N → Type*} [∀ i, MeasurableSpace (U i)]

/-! ### Infinite horizon: the operators `Lᵢᵤ` and the value equations (22) -/

/-- The operator `Lᵢᵤ` of Section 5:
`Lᵢᵤ θ(x) = Rᵢ(xᵢ, u) + β E[θ(x(t+1)) | x(t) = x, i(t) = i, u(t) = u]`, where only the `i`th
component of the state moves, according to `P i` at `(xᵢ, u)`. -/
noncomputable def LopU (B : SuperBanditProcess N X U) (i : Fin N) (u : U i)
    (θ : (∀ j, X j) → ℝ) (x : ∀ j, X j) : ℝ :=
  B.R i (x i) u + B.β * ∫ y, θ (Function.update x i y) ∂(B.P i (x i, u))

/-- The one-project version of `Lᵢᵤ`, acting on functions of `xᵢ` only. -/
noncomputable def Lop1U (B : SuperBanditProcess N X U) (i : Fin N) (u : U i) (ψ : X i → ℝ)
    (xi : X i) : ℝ :=
  B.R i xi u + B.β * ∫ y, ψ y ∂(B.P i (xi, u))

/-- `F` is the value of the superprocess `M`-process: for every retirement reward `M`, `F(·, M)`
is a bounded measurable solution of `F = max(M, maxᵢ sup_u Lᵢᵤ F)` (Section 5, p. 148). -/
def IsMProcessValueU [NeZero N] (B : SuperBanditProcess N X U) (F : (∀ j, X j) → ℝ → ℝ) :
    Prop :=
  ∀ M : ℝ, Measurable (fun x => F x M) ∧ (∃ C : ℝ, ∀ x, |F x M| ≤ C) ∧
    ∀ x, F x M = max M (Finset.univ.sup' Finset.univ_nonempty
      (fun i => ⨆ u : U i, LopU B i u (fun z => F z M) x))

/-- `φᵢ` is the value of the single-project superprocess `M`-process for project `i`: for every
`M`, `φᵢ(·, M)` is a bounded measurable solution of (22), `φᵢ = max(M, sup_u Lᵢᵤ φᵢ)`. -/
def IsOneProjectValueU (B : SuperBanditProcess N X U) (i : Fin N) (φ : X i → ℝ → ℝ) : Prop :=
  ∀ M : ℝ, Measurable (fun xi => φ xi M) ∧ (∃ C : ℝ, ∀ xi, |φ xi M| ≤ C) ∧
    ∀ xi, φ xi M = max M (⨆ u : U i, Lop1U B i u (fun z => φ z M) xi)

/-- The hypothesis of Theorem 2, infinite horizon: the control maps `hᵢ : Xᵢ → Uᵢ` are optimal in
the continuation region of every one-project problem, whatever the retirement reward: whenever
`M < φᵢ(xᵢ, M)`, `hᵢ(xᵢ)` attains `sup_u Lᵢᵤ φᵢ(xᵢ, M)`. The control does not depend on `M`. -/
def IsMIndependentControl (B : SuperBanditProcess N X U) (φ : ∀ i, X i → ℝ → ℝ)
    (h : ∀ i, X i → U i) : Prop :=
  ∀ i (xi : X i) (M : ℝ), M < φ i xi M →
    Lop1U B i (h i xi) (fun z => φ i z M) xi = ⨆ u : U i, Lop1U B i u (fun z => φ i z M) xi

/-! ### Finite horizons: budgets `s`, `φᵢ(xᵢ, sᵢ, M)`, `F(x, s, M)`, the index, and `F̂` -/

/-- `φᵢ(xᵢ, sᵢ, M)` with `u`-optimization: the single-project superprocess `M`-process value when
project `i` may be operated at most `sᵢ` more times: `φᵢ(xᵢ, 0, M) = M` and
`φᵢ(xᵢ, n + 1, M) = max(M, sup_u [Rᵢ(xᵢ, u) + β E[φᵢ(xᵢ(t+1), n, M) | u]])`. -/
noncomputable def phiU (B : SuperBanditProcess N X U) (i : Fin N) : X i → ℕ → ℝ → ℝ
  | _, 0, M => M
  | xi, n + 1, M => max M (⨆ u : U i, (B.R i xi u + B.β * ∫ y, phiU B i y n M ∂(B.P i (xi, u))))

/-- Backward induction for the multi-project superprocess `M`-process, with an explicit fuel
argument (the intended fuel is `∑ i, sᵢ`). -/
noncomputable def FuelU (B : SuperBanditProcess N X U) :
    ℕ → (∀ j, X j) → (Fin N → ℕ) → ℝ → ℝ
  | 0, _, _, M => M
  | n + 1, x, s, M =>
      bellmanMax s M (fun i => ⨆ u : U i,
        (B.R i (x i) u + B.β * ∫ y, FuelU B n (Function.update x i y) (decr s i) M
          ∂(B.P i (x i, u))))

/-- `F(x, s, M)` with `u`-optimization: the backward-induction value of
`F = max(M, max_{i active} sup_u Lᵢᵤ F)`, `F(x, 0, M) = M`. -/
noncomputable def FU (B : SuperBanditProcess N X U) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ) : ℝ :=
  FuelU B (∑ i, s i) x s M

/-- The modified index `Mᵢ(xᵢ, sᵢ)`: the infimal `M` with `φᵢ(xᵢ, sᵢ, M) = M` for the
`u`-optimized `φᵢ`. Meaningful only for `sᵢ > 0` (the paper's value is `−∞` at `sᵢ = 0`). -/
noncomputable def indexU (B : SuperBanditProcess N X U) (i : Fin N) (xi : X i) (n : ℕ) : ℝ :=
  sInf {M : ℝ | phiU B i xi n M = M}

/-- `F̂(x, s, M) = K − ∫_M^K ∏ᵢ ∂φᵢ(xᵢ, sᵢ, m)/∂m dm`, formula (13) with the `u`-optimized `φᵢ`. -/
noncomputable def FhatU (B : SuperBanditProcess N X U) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ) :
    ℝ :=
  B.K - ∫ m in M..B.K, ∏ i, rderiv (fun m' => phiU B i (x i) (s i) m') m

/-- The hypothesis of Theorem 2, finite horizon: the control maps `hᵢ(xᵢ, n)` (a control for each
one-project state `(xᵢ, n)`) are optimal in the continuation region of every one-project problem,
whatever the retirement reward: whenever `M < φᵢ(xᵢ, n + 1, M)`, `hᵢ(xᵢ, n + 1)` attains the
supremum over `u` in the recursion for `φᵢ(xᵢ, n + 1, M)`. -/
def IsMIndependentControlFin (B : SuperBanditProcess N X U) (h : ∀ i, X i → ℕ → U i) : Prop :=
  ∀ i (xi : X i) (n : ℕ) (M : ℝ), M < phiU B i xi (n + 1) M →
    B.R i xi (h i xi (n + 1)) + B.β * ∫ y, phiU B i y n M ∂(B.P i (xi, h i xi (n + 1))) =
      ⨆ u : U i, (B.R i xi u + B.β * ∫ y, phiU B i y n M ∂(B.P i (xi, u)))

/-! ### Policies: a project choice (the base `Policy`) together with a control rule -/

/-- A Markov control rule: in state `x` with budgets `s` and retirement reward `M`, the procedure
`cᵢ(x, s, M)` applied if project `i` is engaged. -/
abbrev ControlRule (N : ℕ) (X : Fin N → Type*) (U : Fin N → Type*) :=
  ∀ i, (∀ j, X j) → (Fin N → ℕ) → ℝ → U i

/-- A control rule is measurable if each `x ↦ cᵢ(x, s, M)` is measurable. -/
def IsMeasurableControl (c : ControlRule N X U) : Prop :=
  ∀ i s M, Measurable (fun x => c i x s M)

/-- The control rule induced by one-project control maps `hᵢ(xᵢ, sᵢ)`. -/
def indexControl (h : ∀ i, X i → ℕ → U i) : ControlRule N X U :=
  fun i x s _ => h i (x i) (s i)

/-- Expected discounted reward of the project policy `σ` with control rule `c`, with an explicit
fuel argument (intended `∑ i, sᵢ`): retiring yields `M`; engaging an active project `i` with
control `u = cᵢ(x, s, M)` yields `Rᵢ(xᵢ, u)` plus `β` times the expected value from the new state
with budgets `Dᵢ s`. -/
noncomputable def polValueUFuel (B : SuperBanditProcess N X U) (σ : Policy N X)
    (c : ControlRule N X U) : ℕ → (∀ j, X j) → (Fin N → ℕ) → ℝ → ℝ
  | 0, _, _, M => M
  | n + 1, x, s, M =>
      match σ x s M with
      | none => M
      | some i =>
          if 0 < s i then
            B.R i (x i) (c i x s M) + B.β * ∫ y, polValueUFuel B σ c n (Function.update x i y)
              (decr s i) M ∂(B.P i (x i, c i x s M))
          else M

/-- The expected total discounted reward of `(σ, c)` in the superprocess `M`-process from `(x, s)`. -/
noncomputable def polValueU (B : SuperBanditProcess N X U) (σ : Policy N X) (c : ControlRule N X U)
    (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ) : ℝ :=
  polValueUFuel B σ c (∑ i, s i) x s M

/-- The index rule with the modified indices: at `(x, s)` engage an active project whose modified
index `Mᵢ(xᵢ, sᵢ)` is maximal among the active projects, provided that maximal value exceeds `M`,
and otherwise retire. Ties among projects may be broken arbitrarily. -/
def IsIndexRuleU (B : SuperBanditProcess N X U) (σ : Policy N X) : Prop :=
  ∀ x s M,
    (∀ i, σ x s M = some i →
      0 < s i ∧ (∀ j, 0 < s j → indexU B j (x j) (s j) ≤ indexU B i (x i) (s i)) ∧
        M < indexU B i (x i) (s i)) ∧
    (σ x s M = none → ∀ j, 0 < s j → indexU B j (x j) (s j) ≤ M)

end WhittleGittins.Retirement.Supplement


