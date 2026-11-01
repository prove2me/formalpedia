-- Prove2me | Definitions.Def_StructBandit_dusaPolicy
-- name    : StructBandit_dusaPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:16.708748+00:00
-- url     : https://prove2.me/theorems/a6b30617-bb90-4e10-8081-5fd20d85edf0
-- title:
--   The DUSA algorithm (Algorithm 1) with all its free choices
-- statement:
--   **DUSA** with accuracy $\epsilon>0$ pulls each arm once in the first $|X|$ rounds and sets $s_{|X|+1}=0$ and initial rates $\eta'>0$ and dual variables $\mu$. In each later round $t$ it runs the **sufficient information test** $\overline{\mathrm{Dual}}(N_t/\log t,x,P_t;\mu_t(x))\ge1+\epsilon$ for all $x\in\tilde X_d(P_t)$:
--
--   1. **Exploitation** (test passed): pull a least played empirically optimal arm; keep $s,\eta',\mu$.
--   2. **Exploration** (test failed): $s_{t+1}=s_t+1$; $\eta_t=\mathsf{SU}(P_t,\eta'_t;\mu_t,\epsilon)$; if $\min_xN_t(x)\le\epsilon s_t/(1+\log(1+s_t))$ pull a least pulled arm, otherwise pull $x^\star_t\in\arg\min\{N_t(x'):x'\in x^\star(P_t)\}$ if $N_t(x^\star_t)\le N_t(\bar x_t)$ and $\bar x_t\in\arg\min_xN_t(x)/\eta_t(x)$ otherwise; then $(\eta'_{t+1},\mu_{t+1})=\mathsf{DU}(P_t;\epsilon)$.
--
--   The module defines one round, the replayed state $(s_t,\eta'_t,\mu_t)$, the resulting policy, DUSA-reachable histories, the events $\mathcal E_t$ (exploitation) and $\mathcal X_t$ (exploration), the target $\eta_t$, and the measurability condition of the run.
--
--   **Formalization Note** Every choice the algorithm leaves open (order of the initial pulls, initial values, the element of each argmin set, and the deep update's output when (20) has no minimizer) is a field of `DusaRules`, a function of the seed and the history; the theorems hold for every such structure. $N_t/\eta_t$ is computed in $[0,\infty]$.
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Algorithm 1, p.24 (and pp.25–26)

import Mathlib
import Definitions.Def_StructBandit_regret
import Definitions.Def_StructBandit_shallowUpdate
import Definitions.Def_StructBandit_IsDUSol

open scoped BigOperators ENNReal

namespace StructBandit

/-- The internal state of DUSA at the start of round `t`: the exploration counter `s_t`, the reference
logarithmic rates `η′_t` and the dual variables `µ_t(x) = (α_t(x), β_t(x), λ_t(x))` of every arm. -/
structure DState (R : Finset ℝ) (X : Type*) where
  /-- The number `s_t` of exploration rounds so far. -/
  s : ℕ
  /-- The reference logarithmic rates `η′_t`. -/
  etaRef : X → ℝ
  /-- The dual variables `µ_t`. -/
  mu : X → DualVec R X

/-- **The free choices of DUSA** (arXiv:2007.07302v3, Algorithm 1, p.24). Algorithm 1 leaves open the
order of the initial pulls, the initial reference rates and dual variables, which element of each
argmin set is pulled, and what the deep update returns when (20) has no minimizer. Each choice may use
the randomization seed `v : V` and the history; each is constrained exactly as the algorithm states:
* `initPick v h A ∈ A`: in the first `|X|` rounds an arm not pulled yet;
* `eta0 v h x > 0`, `mu0 v h x ∈ ℝ₊ × ℝ × K⋆`: `η′_{|X|+1}(x) > 0`, `α_{|X|+1}(x) ∈ ℝ₊`, `β_{|X|+1}(x) ∈ ℝ`,
  `λ_{|X|+1}(x) ∈ K⋆`, chosen at the end of the initialization (p.23) from the history `h` of the first
  `|X|` rounds;
* `exploitPick`, `leastPick`, `barPick`, `starPick`: elements of the argmin sets
  `argmin{N_t(x′) : x′ ∈ x⋆(P_t)}`, `argmin_x N_t(x)`, `argmin_x N_t(x)/η_t(x)`,
  `argmin{N_t(x′) : x′ ∈ X⋆_t}`;
* `fallback`: a nonnegative rate and a dual-feasible vector, used when the deep update (20) has no
  minimizer (Algorithm 1 does not say what `(η′_{t+1}, µ_{t+1})` is then).

**Formalization Note.** The theorems of the mission hold for every such structure, so no tie-breaking
rule is fixed. -/
structure DusaRules {R : Finset ℝ} {X : Type*} [Fintype X] (S : Set (R → X → ℝ)) (V : Type*) where
  initPick : V → History R X → Finset X → X
  initPick_mem : ∀ v h A, A.Nonempty → initPick v h A ∈ A
  eta0 : V → History R X → X → ℝ
  eta0_pos : ∀ v h x, 0 < eta0 v h x
  mu0 : V → History R X → X → DualVec R X
  mu0_feas : ∀ v h x, IsDualFeasible S (mu0 v h x)
  exploitPick : V → History R X → Finset X → X
  exploitPick_mem : ∀ v h A, A.Nonempty → exploitPick v h A ∈ A
  leastPick : V → History R X → Finset X → X
  leastPick_mem : ∀ v h A, A.Nonempty → leastPick v h A ∈ A
  barPick : V → History R X → Finset X → X
  barPick_mem : ∀ v h A, A.Nonempty → barPick v h A ∈ A
  starPick : V → History R X → Finset X → X
  starPick_mem : ∀ v h A, A.Nonempty → starPick v h A ∈ A
  fallback : V → History R X → (X → ℝ) × (X → DualVec R X)
  fallback_nonneg : ∀ v h x, 0 ≤ (fallback v h).1 x
  fallback_feas : ∀ v h x, IsDualFeasible S ((fallback v h).2 x)

/-- The rate vector `N_t / log(t)` of round `t = |h| + 1`. -/
noncomputable def rateVec {R : Finset ℝ} {X : Type*} (h : History R X) : X → ℝ :=
  fun x => (pullCount h x : ℝ) / Real.log ((h.length : ℝ) + 1)

/-- **The sufficient information test** of round `t = |h| + 1` (Algorithm 1, p.24):
`Dual‾_t(x) = max_{ρ≥0} Dual(N_t/log(t), x, P_t; ρµ_t(x)) ≥ 1 + ε` for every `x ∈ X̃d(P_t)`. -/
def passesTest {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (S : Set (R → X → ℝ)) (ε : ℝ)
    (h : History R X) (st : DState R X) : Prop :=
  ∀ x ∈ deceitArms S (empDist h),
    (((1 + ε : ℝ)) : EReal) ≤ dualSup (rateVec h) x (empDist h) (st.mu x)

/-- The shallow-update target `η_t = SU(P_t, η′_t; µ_t, ε)` of round `t = |h| + 1`. -/
noncomputable def suTarget {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X]
    (S : Set (R → X → ℝ)) (ε : ℝ) (h : History R X) (st : DState R X) : Option (X → ℝ) :=
  shallowUpdate S (empDist h) st.etaRef st.mu ε

/-- The ratio `N_t(x)/η_t(x)` in `[0, ∞]`: `N/0 = ∞` for `N ≥ 1`, and `N/(+∞) = 0` when the shallow
update returned `+∞` (`none`). -/
noncomputable def ratio {R : Finset ℝ} {X : Type*} (h : History R X) (η : Option (X → ℝ)) (x : X) :
    ℝ≥0∞ :=
  match η with
  | none => 0
  | some e => (pullCount h x : ℝ≥0∞) / ENNReal.ofReal (e x)

open Classical in
/-- **One round of DUSA** (arXiv:2007.07302v3, Algorithm 1, p.24) at the history `h` of length `n`
(round `t = n + 1`) and state `st`; returns the arm pulled and the state of round `t + 1`.
* `n < |X|` (initialization): pull an arm not pulled yet; the state is kept.
* Exploitation (the test passes): pull a least played empirically optimal arm; `s, η′, µ` are kept.
* Exploration (otherwise): `s_{t+1} = s_t + 1`; `η_t = SU(P_t, η′_t; µ_t, ε)`; if
  `min_x N_t(x) ≤ ε s_t / (1 + log(1 + s_t))` pull a least pulled arm, else pull `x⋆_t` if
  `N_t(x⋆_t) ≤ N_t(x̄_t)` and `x̄_t` otherwise, with `x̄_t ∈ argmin_{x∈X} N_t(x)/η_t(x)` and
  `x⋆_t ∈ argmin{N_t(x′) : x′ ∈ X⋆_t}`; then `(η′_{t+1}, µ_{t+1}) = DU(P_t; ε)`, or the fallback when
  (20) has no minimizer.

**Formalization Note.** The box lists "pull the least pulled arm" and "pull `x⋆_t` / `x̄_t`" as
consecutive bullets; the prose ("Otherwise", p.25) makes the second the alternative of the first, and
the shallow and deep updates run in every exploration round ("the number of updates is equal to the
number of the exploration rounds", p.28). The argmin defining `x̄_t` ranges over `X`, as in the box. The
minimizer of (20) is unique when it exists, so `Classical.choose` selects it. -/
noncomputable def dusaStep {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X]
    (S : Set (R → X → ℝ)) (ε : ℝ) {V : Type*} (rules : DusaRules S V) (v : V)
    (h : History R X) (st : DState R X) : X × DState R X :=
  if h.length < Fintype.card X then
    (rules.initPick v h (Finset.univ.filter (fun x => pullCount h x = 0)), st)
  else if passesTest S ε h st then
    (rules.exploitPick v h (argminOn (optArms (empDist h)) (pullCount h)), st)
  else
    let N : X → ℝ := fun x => (pullCount h x : ℝ)
    let arm : X :=
      if Finset.univ.inf' Finset.univ_nonempty N ≤ ε * st.s / (1 + Real.log (1 + st.s)) then
        rules.leastPick v h (argminOn Finset.univ (pullCount h))
      else
        let xb := rules.barPick v h (argminOn Finset.univ (ratio h (suTarget S ε h st)))
        let xs := rules.starPick v h (argminOn (optArms (empDist h)) (pullCount h))
        if pullCount h xs ≤ pullCount h xb then xs else xb
    let du : (X → ℝ) × (X → DualVec R X) :=
      if hdu : ∃ p : (X → ℝ) × (X → DualVec R X), IsDUSol S (empDist h) ε p.1 p.2 then hdu.choose
      else rules.fallback v h
    (arm, ⟨st.s + 1, du.1, du.2⟩)

/-- The state of DUSA at the start of the round that follows the history `h`: the initial state
`s_{|X|+1} = 0`, `η′ = eta0`, `µ = mu0` is set when the `|X|` initial rounds end, and later states are
replayed from it. -/
noncomputable def dusaState {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X]
    (S : Set (R → X → ℝ)) (ε : ℝ) {V : Type*} (rules : DusaRules S V) (v : V) :
    History R X → DState R X
  | [] => ⟨0, rules.eta0 v [], rules.mu0 v []⟩
  | p :: h =>
      if h.length + 1 = Fintype.card X then ⟨0, rules.eta0 v (p :: h), rules.mu0 v (p :: h)⟩
      else (dusaStep S ε rules v h (dusaState S ε rules v h)).2

/-- **DUSA as a policy**: the arm DUSA pulls after the history `h`, with seed `v`. -/
noncomputable def dusaPolicy {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X]
    (S : Set (R → X → ℝ)) (ε : ℝ) {V : Type*} (rules : DusaRules S V) : Policy V R X :=
  fun v h => (dusaStep S ε rules v h (dusaState S ε rules v h)).1

/-- The history `h` is one DUSA can produce with seed `v`: every round's arm is DUSA's choice at the
preceding history (rewards are arbitrary elements of `R`). -/
def IsDusaHistory {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (S : Set (R → X → ℝ))
    (ε : ℝ) {V : Type*} (rules : DusaRules S V) (v : V) : History R X → Prop
  | [] => True
  | p :: h => IsDusaHistory S ε rules v h ∧ p.1 = dusaPolicy S ε rules v h

/-- The round `t = |h| + 1` is an **exploitation** round `E_t`: `t > |X|` and the test passes. -/
def IsExploitationAt {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (S : Set (R → X → ℝ))
    (ε : ℝ) {V : Type*} (rules : DusaRules S V) (v : V) (h : History R X) : Prop :=
  Fintype.card X ≤ h.length ∧ passesTest S ε h (dusaState S ε rules v h)

/-- The round `t = |h| + 1` is an **exploration** round `X_t`: `t > |X|` and the test fails. -/
def IsExplorationAt {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (S : Set (R → X → ℝ))
    (ε : ℝ) {V : Type*} (rules : DusaRules S V) (v : V) (h : History R X) : Prop :=
  Fintype.card X ≤ h.length ∧ ¬ passesTest S ε h (dusaState S ε rules v h)

/-- The target rate `η_t = SU(P_t, η′_t; µ_t, ε)` that DUSA computes in round `t = |h| + 1` (`none`
stands for `+∞`). -/
noncomputable def etaAt {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (S : Set (R → X → ℝ))
    (ε : ℝ) {V : Type*} (rules : DusaRules S V) (v : V) (h : History R X) : Option (X → ℝ) :=
  suTarget S ε h (dusaState S ε rules v h)

/-- DUSA's choices are `F_t`-measurable (the policy class `Π`, p.7): for every history the arm pulled and
the exploration counter are measurable functions of the seed. -/
def IsMeasurableRun {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (S : Set (R → X → ℝ))
    (ε : ℝ) {V : Type*} [MeasurableSpace V] (rules : DusaRules S V) : Prop :=
  IsAdmissible (dusaPolicy S ε rules) ∧
    ∀ (h : History R X) (n : ℕ), MeasurableSet {v | (dusaState S ε rules v h).s = n}

end StructBandit


