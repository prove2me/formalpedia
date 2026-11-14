-- Prove2me | Definitions.Def_KMedian195_ProfileConstruction
-- name    : KMedian195_ProfileConstruction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:37.249202+00:00
-- url     : https://prove2.me/theorems/79b879d7-2b2a-4490-8ad4-4d5eae5e5359
-- title:
--   KMedian195.ProfileConstruction
-- statement:
--   This is module `KMedian195.ProfileConstruction` of the library KMedian195: the proof that the factor-revealing program of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) (Part I, Definition 4.1, with the bid $[\alpha-\gamma d]^+$) has value at most $2-(\gamma-1)^2$ for $\gamma\in[1,1.224]$ (Part I, Theorem 4.4). The library was written by Codex in [epfl-thl2/project-k-median](https://github.com/epfl-thl2/project-k-median) (project `bound-195`, commit `d87e2a2`) and is taken from its copy in [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0).
--
--   **Contents.** The module is published as a whole: 101 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_KMedian195_ProfileConstruction`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Imported/KMedian195/ProfileConstruction.lean

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`,
file `bound-195/KMedian195/ProfileConstruction.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`), and:
* `if_pos`, `if_neg`, `dif_pos`, `dif_neg` (deprecated) are `if_pos`, `if_neg`,
  `dif_pos`, `dif_neg`.
* In `hatG_nonneg_of_phase1_of_later_nonneg`, `simpa ... using e` is `simpa ... using! e`: our
  Lean's `simpa` matches the simplified `e` against the goal only up to reducible unfolding;
  `using!` matches as before.
* The case of `Nat.strong_induction_on` is named `ind` (was `h`).
-/
module

public import Definitions.Def_KMedian195_DualSolution
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `KMedian195.ProfileConstruction` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
@[expose] public section

namespace KMedian195

variable {n : ℕ}

/-- The positive part `[x]^+ = max(x,0)`. -/
def posPart (x : ℝ) : ℝ :=
  max x 0

@[simp] theorem posPart_nonneg (x : ℝ) : 0 ≤ posPart x := by
  simp [posPart]

@[simp] theorem posPart_of_nonneg {x : ℝ} (hx : 0 ≤ x) : posPart x = x := by
  simp [posPart, max_eq_left hx]

@[simp] theorem posPart_of_nonpos {x : ℝ} (hx : x ≤ 0) : posPart x = 0 := by
  simp [posPart, max_eq_right hx]

/-- `R_i = \sum_{\ell=i+1}^n \hat g_\ell` for a profile `\hat g`. -/
def tailBudget (hatG : Idx n → ℝ) (i : Idx n) : ℝ :=
  Finset.sum (strictSuffixRange i) hatG

/-- `R_{i-1} = \sum_{\ell=i}^n \hat g_\ell` for a profile `\hat g`. -/
def beforeBudget (hatG : Idx n → ℝ) (i : Idx n) : ℝ :=
  Finset.sum (suffixRange i) hatG

/-- `R_0 = \sum_{\ell=1}^n \hat g_\ell` for a profile `\hat g`. -/
def totalBudget (hatG : Idx n → ℝ) : ℝ :=
  Finset.sum Finset.univ hatG

/--
The paper's factor `n-i`, interpreted on zero-based `Fin n` indices as the number of
strictly later time steps.
-/
def futureCountNat (i : Idx n) : ℕ :=
  n - i.1.succ

def futureCount (i : Idx n) : ℝ :=
  futureCountNat i

@[simp] theorem futureCount_nonneg (i : Idx n) : 0 ≤ futureCount i := by
  change (0 : ℝ) ≤ (futureCountNat i : ℝ)
  exact_mod_cast Nat.zero_le (futureCountNat i)

@[simp] theorem futureCount_last [NeZero n] : futureCount (lastIdx n) = 0 := by
  have hn : 0 < n := Nat.pos_of_neZero n
  change ((n - (Nat.pred n).succ : ℕ) : ℝ) = 0
  rw [Nat.succ_pred_eq_of_pos hn, Nat.sub_self, Nat.cast_zero]

theorem tailBudget_nonneg_of_nonneg {hatG : Idx n → ℝ}
    (hhatG : ∀ i, 0 ≤ hatG i) (i : Idx n) :
    0 ≤ tailBudget hatG i := by
  unfold tailBudget
  exact Finset.sum_nonneg (by intro j hj; exact hhatG j)

theorem beforeBudget_nonneg_of_nonneg {hatG : Idx n → ℝ}
    (hhatG : ∀ i, 0 ≤ hatG i) (i : Idx n) :
    0 ≤ beforeBudget hatG i := by
  unfold beforeBudget
  exact Finset.sum_nonneg (by intro j hj; exact hhatG j)

theorem totalBudget_nonneg_of_nonneg {hatG : Idx n → ℝ}
    (hhatG : ∀ i, 0 ≤ hatG i) :
    0 ≤ totalBudget hatG := by
  unfold totalBudget
  exact Finset.sum_nonneg (by intro j hj; exact hhatG j)

theorem beforeBudget_le_totalBudget_of_nonneg {hatG : Idx n → ℝ}
    (hhatG : ∀ i, 0 ≤ hatG i) (i : Idx n) :
    beforeBudget hatG i ≤ totalBudget hatG := by
  unfold beforeBudget totalBudget
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro j hj
    simp
  · intro j hjuniv hjnotsuffix
    exact hhatG j

theorem beforeBudget_le_one_of_nonneg_of_total_eq_one {hatG : Idx n → ℝ}
    (hhatG : ∀ i, 0 ≤ hatG i) (htotal : totalBudget hatG = 1) (i : Idx n) :
    beforeBudget hatG i ≤ 1 := by
  calc
    beforeBudget hatG i ≤ totalBudget hatG := beforeBudget_le_totalBudget_of_nonneg hhatG i
    _ = 1 := htotal

theorem beforeBudget_antitone_of_nonneg {hatG : Idx n → ℝ}
    (hhatG : ∀ i, 0 ≤ hatG i) {i j : Idx n} (hij : i ≤ j) :
    beforeBudget hatG j ≤ beforeBudget hatG i := by
  unfold beforeBudget
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro k hk
    simpa [suffixRange] using le_trans hij (mem_suffixRange.mp hk)
  · intro k hki hknj
    exact hhatG k

theorem posPart_sub_div_le_one {x θ : ℝ} (hx : 0 ≤ x) (hθ : 0 ≤ θ) :
    posPart (1 - x / θ) ≤ 1 := by
  unfold posPart
  apply max_le_iff.mpr
  constructor
  · have hdiv : 0 ≤ x / θ := div_nonneg hx hθ
    linarith
  · linarith

theorem posPart_sub_le_left {x θ : ℝ} (hx : 0 ≤ x) (hθ : 0 ≤ θ) :
    posPart (θ - x) ≤ θ := by
  unfold posPart
  apply max_le_iff.mpr
  constructor
  · linarith
  · exact hθ

theorem one_sub_posPart_sub_nonneg {x θ : ℝ}
    (hx : 0 ≤ x) (hθ : 0 ≤ θ) (hθle : θ ≤ 1) :
    0 ≤ 1 - posPart (θ - x) := by
  have hpos : posPart (θ - x) ≤ θ := posPart_sub_le_left hx hθ
  linarith

theorem beforeBudget_eq_self_add_tail (hatG : Idx n → ℝ) (i : Idx n) :
    beforeBudget hatG i = hatG i + tailBudget hatG i := by
  classical
  unfold beforeBudget tailBudget suffixRange strictSuffixRange
  rw [show Finset.univ.filter (fun j : Idx n => i ≤ j) =
      insert i (Finset.univ.filter (fun j : Idx n => i < j)) by
        ext j
        constructor
        · intro hj
          by_cases hji : j = i
          · simp [hji]
          · have hij : i < j := lt_of_le_of_ne (by simpa using hj) (Ne.symm hji)
            simp [hji, hij]
        · intro hj
          rcases Finset.mem_insert.mp hj with rfl | hj'
          · simp
          · have hij : i < j := by simpa using hj'
            simp [le_of_lt hij]]
  rw [Finset.sum_insert]
  · simp

noncomputable section

namespace DualProgram

variable {n : ℕ}

/-- The paper's `\varepsilon = \gamma - 1`. -/
def epsilon (P : DualProgram n) : ℝ :=
  P.Mcoeffmone

/-- The paper's `\theta = \varepsilon + \varepsilon^2`. -/
def theta (P : DualProgram n) : ℝ :=
  P.epsilon + P.epsilon ^ 2

/-- The paper's `\tau = 2\varepsilon + \varepsilon^2`. -/
def tau (P : DualProgram n) : ℝ :=
  2 * P.epsilon + P.epsilon ^ 2

/-- The paper's `\bar\tau = 1 - \tau`. -/
def barTau (P : DualProgram n) : ℝ :=
  1 - P.tau

/-- The paper's `1 - \theta`. -/
def oneMinusTheta (P : DualProgram n) : ℝ :=
  1 - P.theta

/-- The paper's auxiliary ratio `\varepsilon / \tau`. -/
def frac (P : DualProgram n) : ℝ :=
  P.epsilon / P.tau

/-- The target bound `\rho = 2 - \varepsilon^2`. -/
def rhoBound (P : DualProgram n) : ℝ :=
  2 - P.epsilon ^ 2

theorem gamma_mul_epsilon_eq_theta (P : DualProgram n) :
    P.Mcoeff * P.epsilon = P.theta := by
  dsimp [epsilon, theta, DualProgram.Mcoeffmone]
  ring

theorem gamma_add_one_sub_theta_eq_rho (P : DualProgram n) :
    P.Mcoeff + 1 - P.theta = P.rhoBound := by
  dsimp [epsilon, theta, rhoBound, DualProgram.Mcoeffmone]
  ring

theorem epsilon_add_theta_eq_tau (P : DualProgram n) :
    P.epsilon + P.theta = P.tau := by
  dsimp [epsilon, theta, tau]
  ring

theorem epsilon_nonneg_of_one_le_Mcoeff (P : DualProgram n) (hγ : 1 ≤ P.Mcoeff) :
    0 ≤ P.epsilon := by
  dsimp [epsilon, DualProgram.Mcoeffmone]
  linarith

theorem theta_nonneg_of_epsilon_nonneg (P : DualProgram n) (hε : 0 ≤ P.epsilon) :
    0 ≤ P.theta := by
  dsimp [theta]
  nlinarith

theorem theta_nonneg_of_one_le_Mcoeff (P : DualProgram n) (hγ : 1 ≤ P.Mcoeff) :
    0 ≤ P.theta :=
  P.theta_nonneg_of_epsilon_nonneg (P.epsilon_nonneg_of_one_le_Mcoeff hγ)

theorem tau_nonneg_of_epsilon_nonneg (P : DualProgram n) (hε : 0 ≤ P.epsilon) :
    0 ≤ P.tau := by
  dsimp [tau]
  nlinarith

theorem tau_nonneg_of_one_le_Mcoeff (P : DualProgram n) (hγ : 1 ≤ P.Mcoeff) :
    0 ≤ P.tau :=
  P.tau_nonneg_of_epsilon_nonneg (P.epsilon_nonneg_of_one_le_Mcoeff hγ)

theorem frac_nonneg_of_epsilon_nonneg (P : DualProgram n) (hε : 0 ≤ P.epsilon) :
    0 ≤ P.frac := by
  exact div_nonneg hε (P.tau_nonneg_of_epsilon_nonneg hε)

theorem frac_nonneg_of_one_le_Mcoeff (P : DualProgram n) (hγ : 1 ≤ P.Mcoeff) :
    0 ≤ P.frac :=
  P.frac_nonneg_of_epsilon_nonneg (P.epsilon_nonneg_of_one_le_Mcoeff hγ)

theorem frac_le_one_of_epsilon_nonneg (P : DualProgram n) (hε : 0 ≤ P.epsilon) :
    P.frac ≤ 1 := by
  by_cases hτ : P.tau = 0
  · simp [DualProgram.frac, hτ]
  · have hτnonneg : 0 ≤ P.tau := P.tau_nonneg_of_epsilon_nonneg hε
    have hτpos : 0 < P.tau := by
      exact lt_of_le_of_ne hτnonneg (by simpa [eq_comm] using hτ)
    have hεleτ : P.epsilon ≤ P.tau := by
      calc
        P.epsilon ≤ P.epsilon + P.theta := by
          have hθ : 0 ≤ P.theta := P.theta_nonneg_of_epsilon_nonneg hε
          linarith
        _ = P.tau := P.epsilon_add_theta_eq_tau
    exact (div_le_iff₀ hτpos).2 (by simpa using hεleτ)

theorem frac_le_one_of_one_le_Mcoeff (P : DualProgram n) (hγ : 1 ≤ P.Mcoeff) :
    P.frac ≤ 1 :=
  P.frac_le_one_of_epsilon_nonneg (P.epsilon_nonneg_of_one_le_Mcoeff hγ)

theorem theta_le_one_of_le_153_div_125
    (P : DualProgram n) (hγlo : 1 ≤ P.Mcoeff) (hγhi : P.Mcoeff ≤ (153 : ℝ) / 125) :
    P.theta ≤ 1 := by
  have hεnonneg : 0 ≤ P.epsilon := P.epsilon_nonneg_of_one_le_Mcoeff hγlo
  have hεupper : P.epsilon ≤ (28 : ℝ) / 125 := by
    dsimp [epsilon, DualProgram.Mcoeffmone]
    linarith
  dsimp [theta]
  nlinarith

theorem theta_le_barTau_of_le_153_div_125
    (P : DualProgram n) (hγlo : 1 ≤ P.Mcoeff) (hγhi : P.Mcoeff ≤ (153 : ℝ) / 125) :
    P.theta ≤ P.barTau := by
  have hεnonneg : 0 ≤ P.epsilon := P.epsilon_nonneg_of_one_le_Mcoeff hγlo
  have hεupper : P.epsilon ≤ (28 : ℝ) / 125 := by
    dsimp [epsilon, DualProgram.Mcoeffmone]
    linarith
  dsimp [theta, barTau, tau]
  nlinarith

theorem epsilon_le_theta_of_one_le_Mcoeff
    (P : DualProgram n) (hγ : 1 ≤ P.Mcoeff) :
    P.epsilon ≤ P.theta := by
  have hε : 0 ≤ P.epsilon := P.epsilon_nonneg_of_one_le_Mcoeff hγ
  dsimp [theta]
  nlinarith

theorem theta_le_tau_of_one_le_Mcoeff
    (P : DualProgram n) (hγ : 1 ≤ P.Mcoeff) :
    P.theta ≤ P.tau := by
  calc
    P.theta = P.epsilon + P.theta - P.epsilon := by ring
    _ ≤ P.epsilon + P.theta := by
      have hε : 0 ≤ P.epsilon := P.epsilon_nonneg_of_one_le_Mcoeff hγ
      linarith
    _ = P.tau := P.epsilon_add_theta_eq_tau

theorem barTau_nonneg_of_le_153_div_125
    (P : DualProgram n) (hγlo : 1 ≤ P.Mcoeff) (hγhi : P.Mcoeff ≤ (153 : ℝ) / 125) :
    0 ≤ P.barTau := by
  have hθbar : P.theta ≤ P.barTau := P.theta_le_barTau_of_le_153_div_125 hγlo hγhi
  have hθ : 0 ≤ P.theta := P.theta_nonneg_of_one_le_Mcoeff hγlo
  linarith

end DualProgram

section MaxOption

variable {α : Type*} [LinearOrder α]

/-- `Finset.max'` packaged as an `Option`-valued helper. -/
noncomputable def finsetMax? (s : Finset α) : Option α :=
  if h : s.Nonempty then some (s.max' h) else none

end MaxOption

namespace Advice

variable {n : ℕ} [NeZero n] {I : ProcedureInput n}

/--
The `D`-membership produced directly from the frontier advice:
`1` past the frontier, `μ*` on the frontier, and `0` before it.
-/
def muD (Γ : Advice I) (j : Idx n) : ℝ :=
  if Γ.t3Star < I.firstBidTime j then
    1
  else if I.firstBidTime j = Γ.t3Star then
    Γ.muStar j
  else
    0

theorem muD_eq_one (Γ : Advice I) {j : Idx n} (h : Γ.t3Star < I.firstBidTime j) :
    Γ.muD j = 1 := by
  simp [Advice.muD, h]

theorem muD_eq_muStar (Γ : Advice I) {j : Idx n} (h : I.firstBidTime j = Γ.t3Star) :
    Γ.muD j = Γ.muStar j := by
  simp [Advice.muD, h]

theorem muD_eq_zero (Γ : Advice I) {j : Idx n} (h : I.firstBidTime j < Γ.t3Star) :
    Γ.muD j = 0 := by
  have hnot₁ : ¬ Γ.t3Star < I.firstBidTime j := by
    exact not_lt.mpr (le_of_lt h)
  have hnot₂ : I.firstBidTime j ≠ Γ.t3Star := ne_of_lt h
  simp [Advice.muD, hnot₁, hnot₂]

theorem muD_nonneg_of_admissible (Γ : Advice I) (hΓ : Γ.Admissible) (j : Idx n) :
    0 ≤ Γ.muD j := by
  rcases hΓ with ⟨hmu, -, -, -⟩
  by_cases h₁ : Γ.t3Star < I.firstBidTime j
  · simp [Advice.muD, h₁]
  · by_cases h₂ : I.firstBidTime j = Γ.t3Star
    · simpa [Advice.muD, h₁, h₂] using (hmu j).1
    · simp [Advice.muD, h₁, h₂]

theorem muD_le_one_of_admissible (Γ : Advice I) (hΓ : Γ.Admissible) (j : Idx n) :
    Γ.muD j ≤ 1 := by
  rcases hΓ with ⟨hmu, -, -, -⟩
  by_cases h₁ : Γ.t3Star < I.firstBidTime j
  · simp [Advice.muD, h₁]
  · by_cases h₂ : I.firstBidTime j = Γ.t3Star
    · simpa [Advice.muD, h₁, h₂] using (hmu j).2
    · simp [Advice.muD, h₁, h₂]

end Advice

/--
Phase 2 of Algorithm 1: a profile `\hat g^{(2)}` satisfying the exact recursive equations
from the paper up to the frontier `t_3^\star`, and zero above it.
-/
structure PhaseTwoData {n : ℕ} [NeZero n] (I : ProcedureInput n) (Γ : Advice I) where
  hatG2 : Idx n → ℝ
  zero_above_t3 : ∀ ⦃i : Idx n⦄, Γ.t3Star < i → hatG2 i = 0
  hatG2_nonneg : ∀ i, 0 ≤ hatG2 i
  step_eq :
    ∀ i, i ≤ Γ.t3Star →
      hatG2 i =
        if i = lastIdx n ∧ Γ.t3Star = lastIdx n then
          Γ.hatGLast
        else
          (1 - Γ.muD i) * (tailBudget hatG2 i + I.program.tau) / futureCount i

namespace PhaseTwoData

variable {n : ℕ} [NeZero n] {I : ProcedureInput n} {Γ : Advice I}

def afterBudget (Ξ : PhaseTwoData I Γ) (i : Idx n) : ℝ :=
  tailBudget Ξ.hatG2 i

def beforeBudget (Ξ : PhaseTwoData I Γ) (i : Idx n) : ℝ :=
  KMedian195.beforeBudget Ξ.hatG2 i

theorem afterBudget_nonneg (Ξ : PhaseTwoData I Γ) (i : Idx n) : 0 ≤ Ξ.afterBudget i :=
  tailBudget_nonneg_of_nonneg Ξ.hatG2_nonneg i

theorem beforeBudget_nonneg (Ξ : PhaseTwoData I Γ) (i : Idx n) : 0 ≤ Ξ.beforeBudget i :=
  KMedian195.beforeBudget_nonneg_of_nonneg Ξ.hatG2_nonneg i

theorem beforeBudget_eq_self_add_afterBudget (Ξ : PhaseTwoData I Γ) (i : Idx n) :
    Ξ.beforeBudget i = Ξ.hatG2 i + Ξ.afterBudget i := by
  exact beforeBudget_eq_self_add_tail Ξ.hatG2 i

def t1Candidates (Ξ : PhaseTwoData I Γ) : Finset (Idx n) :=
  Finset.univ.filter fun i => Ξ.beforeBudget i ≥ I.program.barTau

def t2Candidates (Ξ : PhaseTwoData I Γ) : Finset (Idx n) :=
  Finset.univ.filter fun i => Ξ.beforeBudget i ≥ I.program.theta

noncomputable def t1? (Ξ : PhaseTwoData I Γ) : Option (Idx n) :=
  finsetMax? (Ξ.t1Candidates)

noncomputable def t2? (Ξ : PhaseTwoData I Γ) : Option (Idx n) :=
  finsetMax? (Ξ.t2Candidates)

/--
The paper's quantity `z = \sum_{\ell=t_2+1}^n [1 - R_{\ell-1}^{(2)}/\theta]^+ μ_\ell^D`.
It is only meaningful after `t₂` exists, so we package the undefined case as `0`.
-/
noncomputable def z (Ξ : PhaseTwoData I Γ) : ℝ :=
  match Ξ.t2? with
  | none => 0
  | some t2 =>
      Finset.sum (strictSuffixRange t2) fun ℓ =>
        posPart (1 - Ξ.beforeBudget ℓ / I.program.theta) * Γ.muD ℓ

end PhaseTwoData

/--
A successful output of the profile-construction algorithm: it includes the Phase 2 profile,
chosen thresholds `t₁,t₂`, the final profile `\hat g`, and the exact boundary/Phase 1 formulas.
-/
structure ProfileData {n : ℕ} [NeZero n] (I : ProcedureInput n) (Γ : Advice I) where
  phaseTwo : PhaseTwoData I Γ
  t1 : Idx n
  t1_spec : phaseTwo.t1? = some t1
  t1_beforeBudget_ge_barTau : I.program.barTau ≤ phaseTwo.beforeBudget t1
  phaseTwo_afterBudget_t1_lt_barTau :
    t1 ≠ lastIdx n → phaseTwo.afterBudget t1 < I.program.barTau
  phaseTwo_beforeBudget_lt_barTau_above_t1 :
    ∀ ⦃i : Idx n⦄, t1 < i → phaseTwo.beforeBudget i < I.program.barTau
  t2 : Idx n
  t2_spec : phaseTwo.t2? = some t2
  t2_beforeBudget_ge_theta : I.program.theta ≤ phaseTwo.beforeBudget t2
  phaseTwo_beforeBudget_lt_theta_above_t2 :
    ∀ ⦃i : Idx n⦄, t2 < i → phaseTwo.beforeBudget i < I.program.theta
  t1_le_t2 : t1 ≤ t2
  z : ℝ
  z_eq :
    z =
      Finset.sum (strictSuffixRange t2) fun ℓ =>
        posPart (1 - phaseTwo.beforeBudget ℓ / I.program.theta) * Γ.muD ℓ
  z_le_futureCount_t2 : z ≤ futureCount t2
  alpha : ℝ
  alpha_eq :
    alpha =
      if t1 = lastIdx n then
        1
      else
        (I.program.barTau - phaseTwo.afterBudget t1) / phaseTwo.hatG2 t1
  hatG : Idx n → ℝ
  hatGT1A : ℝ
  hatGT1A_eq :
    hatGT1A =
      if t1 = lastIdx n then
        0
      else
        (1 - alpha) * (1 - Γ.muD t1) *
          (1 - posPart (I.program.theta - tailBudget hatG (I.firstBidTime t1))) /
          (futureCount t1 + alpha * (1 - Γ.muD t1) - I.program.frac * z)
  hatGT1B : ℝ
  hatGT1B_eq :
    hatGT1B =
      if t1 = lastIdx n then
        phaseTwo.hatG2 t1
      else
        I.program.barTau - phaseTwo.afterBudget t1
  copied_above_t1 : ∀ ⦃i : Idx n⦄, t1 < i → hatG i = phaseTwo.hatG2 i
  boundary_eq : hatG t1 = hatGT1A + hatGT1B
  phase1_eq :
    ∀ ⦃i : Idx n⦄, i < t1 →
      hatG i =
        (1 - Γ.muD i) * (1 - posPart (I.program.theta - tailBudget hatG (I.firstBidTime i))) /
          (futureCount i - I.program.frac * z)
  total_eq_one : totalBudget hatG = 1

namespace ProfileData

variable {n : ℕ} [NeZero n] {I : ProcedureInput n} {Γ : Advice I}

def phaseTwoZ (C : ProfileData I Γ) : ℝ :=
  C.z

def boundaryAlpha (C : ProfileData I Γ) : ℝ :=
  C.alpha

def boundaryHatGB (C : ProfileData I Γ) : ℝ :=
  C.hatGT1B

def boundaryDenom (C : ProfileData I Γ) : ℝ :=
  futureCount C.t1 + C.alpha * (1 - Γ.muD C.t1) - I.program.frac * C.phaseTwoZ

def boundaryHatGA (C : ProfileData I Γ) : ℝ :=
  C.hatGT1A

def boundaryHatG (C : ProfileData I Γ) : ℝ :=
  C.boundaryHatGA + C.boundaryHatGB

def phase1Denom (C : ProfileData I Γ) (i : Idx n) : ℝ :=
  futureCount i - I.program.frac * C.phaseTwoZ

def phase1Numerator (C : ProfileData I Γ) (i : Idx n) : ℝ :=
  1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime i))

def phase1Value (C : ProfileData I Γ) (i : Idx n) : ℝ :=
  (1 - Γ.muD i) * C.phase1Numerator i / C.phase1Denom i

theorem beforeBudget_eq_phaseTwo_beforeBudget_of_lt_t1
    (C : ProfileData I Γ) {j : Idx n} (hj : C.t1 < j) :
    beforeBudget C.hatG j = C.phaseTwo.beforeBudget j := by
  unfold beforeBudget PhaseTwoData.beforeBudget
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact C.copied_above_t1 (lt_of_lt_of_le hj (mem_suffixRange.mp hi))

theorem tailBudget_nonneg_of_t1_le
    (C : ProfileData I Γ) {j : Idx n} (hj : C.t1 ≤ j) :
    0 ≤ tailBudget C.hatG j := by
  unfold tailBudget
  refine Finset.sum_nonneg ?_
  intro i hi
  have hji : j < i := mem_strictSuffixRange.mp hi
  have ht1i : C.t1 < i := lt_of_le_of_lt hj hji
  rw [C.copied_above_t1 ht1i]
  exact C.phaseTwo.hatG2_nonneg i

omit [NeZero n] in
theorem futureCount_antitone {i j : Idx n} (hij : i ≤ j) :
    futureCount j ≤ futureCount i := by
  change ((n - j.1.succ : ℕ) : ℝ) ≤ ((n - i.1.succ : ℕ) : ℝ)
  exact_mod_cast Nat.sub_le_sub_left (Nat.succ_le_succ hij) n

omit [NeZero n] in
theorem futureCountNat_lt_of_lt {i j : Idx n} (hij : i < j) :
    futureCountNat j < futureCountNat i := by
  have hijv : i.1 < j.1 := hij
  unfold futureCountNat
  omega

theorem z_le_futureCount_t1 (C : ProfileData I Γ) : C.z ≤ futureCount C.t1 := by
  calc
    C.z ≤ futureCount C.t2 := C.z_le_futureCount_t2
    _ ≤ futureCount C.t1 := futureCount_antitone C.t1_le_t2

theorem z_nonneg_of_admissible (C : ProfileData I Γ) (hΓ : Γ.Admissible) :
    0 ≤ C.z := by
  rw [C.z_eq]
  refine Finset.sum_nonneg ?_
  intro j hj
  exact mul_nonneg (posPart_nonneg _) (Advice.muD_nonneg_of_admissible Γ hΓ j)

theorem alpha_bounds
    (C : ProfileData I Γ) :
    0 ≤ C.alpha ∧ C.alpha ≤ 1 := by
  by_cases ht1 : C.t1 = lastIdx n
  · constructor <;> simp [C.alpha_eq, ht1]
  · have hafter_lt : C.phaseTwo.afterBudget C.t1 < I.program.barTau := by
      exact C.phaseTwo_afterBudget_t1_lt_barTau ht1
    have hnum_nonneg : 0 ≤ I.program.barTau - C.phaseTwo.afterBudget C.t1 := by
      linarith
    have hden_pos : 0 < C.phaseTwo.hatG2 C.t1 := by
      have hbefore :
          C.phaseTwo.beforeBudget C.t1 =
            C.phaseTwo.hatG2 C.t1 + C.phaseTwo.afterBudget C.t1 :=
        C.phaseTwo.beforeBudget_eq_self_add_afterBudget C.t1
      linarith [C.t1_beforeBudget_ge_barTau, hafter_lt, hbefore]
    have hnum_le_den :
        I.program.barTau - C.phaseTwo.afterBudget C.t1 ≤ C.phaseTwo.hatG2 C.t1 := by
      have hbefore :
          C.phaseTwo.beforeBudget C.t1 =
            C.phaseTwo.hatG2 C.t1 + C.phaseTwo.afterBudget C.t1 :=
        C.phaseTwo.beforeBudget_eq_self_add_afterBudget C.t1
      linarith [C.t1_beforeBudget_ge_barTau, hbefore]
    constructor
    · rw [C.alpha_eq, if_neg ht1]
      exact div_nonneg hnum_nonneg hden_pos.le
    · rw [C.alpha_eq, if_neg ht1]
      exact (div_le_iff₀ hden_pos).2 (by linarith)

theorem boundaryHatGB_nonneg
    (C : ProfileData I Γ) : 0 ≤ C.boundaryHatGB := by
  by_cases ht1 : C.t1 = lastIdx n
  · simp [ProfileData.boundaryHatGB, C.hatGT1B_eq, ht1, C.phaseTwo.hatG2_nonneg]
  · rw [ProfileData.boundaryHatGB, C.hatGT1B_eq, if_neg ht1]
    linarith [C.phaseTwo_afterBudget_t1_lt_barTau ht1]

theorem boundaryHatGA_nonneg_of_admissible
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    0 ≤ C.boundaryHatGA := by
  by_cases ht1 : C.t1 = lastIdx n
  · simp [ProfileData.boundaryHatGA, C.hatGT1A_eq, ht1]
  · have hα := C.alpha_bounds
    have h1α : 0 ≤ 1 - C.alpha := sub_nonneg.mpr hα.2
    have h1μ : 0 ≤ 1 - Γ.muD C.t1 := by
      exact sub_nonneg.mpr (Advice.muD_le_one_of_admissible Γ hΓ C.t1)
    have htail : 0 ≤ tailBudget C.hatG (I.firstBidTime C.t1) := by
      exact C.tailBudget_nonneg_of_t1_le (I.le_firstBidTime C.t1)
    have hθ : 0 ≤ I.program.theta := I.program.theta_nonneg_of_one_le_Mcoeff hγlo
    have hθle : I.program.theta ≤ 1 :=
      I.program.theta_le_one_of_le_153_div_125 hγlo hγhi
    have hnum3 :
        0 ≤ 1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime C.t1)) := by
      exact one_sub_posPart_sub_nonneg htail hθ hθle
    have hznonneg : 0 ≤ C.z := C.z_nonneg_of_admissible hΓ
    have hzle : C.z ≤ futureCount C.t1 := C.z_le_futureCount_t1
    have hfrac_nonneg : 0 ≤ I.program.frac := I.program.frac_nonneg_of_one_le_Mcoeff hγlo
    have hfrac_le : I.program.frac ≤ 1 := I.program.frac_le_one_of_one_le_Mcoeff hγlo
    have hfracz_le : I.program.frac * C.z ≤ futureCount C.t1 := by
      have hfracz_le_z : I.program.frac * C.z ≤ C.z := by
        nlinarith
      exact le_trans hfracz_le_z hzle
    have hden :
        0 ≤ futureCount C.t1 + C.alpha * (1 - Γ.muD C.t1) - I.program.frac * C.z := by
      have hαμ : 0 ≤ C.alpha * (1 - Γ.muD C.t1) := mul_nonneg hα.1 h1μ
      nlinarith [futureCount_nonneg C.t1, hαμ, hfracz_le]
    rw [ProfileData.boundaryHatGA, C.hatGT1A_eq, if_neg ht1]
    exact div_nonneg (mul_nonneg (mul_nonneg h1α h1μ) hnum3) hden

theorem boundaryHatGA_le_hatG_t1_of_admissible
    (C : ProfileData I Γ) :
    C.boundaryHatGA ≤ C.hatG C.t1 := by
  have hB : 0 ≤ C.boundaryHatGB := C.boundaryHatGB_nonneg
  have hEq : C.hatG C.t1 = C.boundaryHatGA + C.boundaryHatGB := C.boundary_eq
  linarith

theorem tailBudget_nonneg_at_firstBidTime_of_later_nonneg
    (C : ProfileData I Γ) {i : Idx n}
    (hlater : ∀ k, i < k → 0 ≤ C.hatG k) :
    0 ≤ tailBudget C.hatG (I.firstBidTime i) := by
  unfold tailBudget
  refine Finset.sum_nonneg ?_
  intro k hk
  exact hlater k (lt_of_le_of_lt (I.le_firstBidTime i) (mem_strictSuffixRange.mp hk))

theorem phase1Numerator_nonneg_of_later_nonneg
    (C : ProfileData I Γ)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {i : Idx n} (hlater : ∀ k, i < k → 0 ≤ C.hatG k) :
    0 ≤ C.phase1Numerator i := by
  unfold ProfileData.phase1Numerator
  have htail : 0 ≤ tailBudget C.hatG (I.firstBidTime i) :=
    C.tailBudget_nonneg_at_firstBidTime_of_later_nonneg hlater
  exact one_sub_posPart_sub_nonneg htail
    (I.program.theta_nonneg_of_one_le_Mcoeff hγlo)
    (I.program.theta_le_one_of_le_153_div_125 hγlo hγhi)

theorem phase1Denom_nonneg_of_lt_t1
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff)
    {i : Idx n} (hi : i < C.t1) :
    0 ≤ C.phase1Denom i := by
  unfold ProfileData.phase1Denom ProfileData.phaseTwoZ
  have hznonneg : 0 ≤ C.z := C.z_nonneg_of_admissible hΓ
  have hzle : C.z ≤ futureCount C.t1 := C.z_le_futureCount_t1
  have hfrac_nonneg : 0 ≤ I.program.frac := I.program.frac_nonneg_of_one_le_Mcoeff hγlo
  have hfrac_le : I.program.frac ≤ 1 := I.program.frac_le_one_of_one_le_Mcoeff hγlo
  have hfracz_le_z : I.program.frac * C.z ≤ C.z := by
    nlinarith
  have hfracz_le_t1 : I.program.frac * C.z ≤ futureCount C.t1 :=
    le_trans hfracz_le_z hzle
  have ht1le : futureCount C.t1 ≤ futureCount i :=
    futureCount_antitone (le_of_lt hi)
  linarith

theorem hatG_nonneg_of_phase1_of_later_nonneg
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {i : Idx n} (hi : i < C.t1)
    (hlater : ∀ k, i < k → 0 ≤ C.hatG k) :
    0 ≤ C.hatG i := by
  rw [C.phase1_eq hi]
  have hmu : 0 ≤ 1 - Γ.muD i := by
    exact sub_nonneg.mpr (Advice.muD_le_one_of_admissible Γ hΓ i)
  have hnum : 0 ≤ C.phase1Numerator i :=
    C.phase1Numerator_nonneg_of_later_nonneg hγlo hγhi hlater
  have hden : 0 ≤ C.phase1Denom i :=
    C.phase1Denom_nonneg_of_lt_t1 hΓ hγlo hi
  simpa [ProfileData.phase1Numerator, ProfileData.phase1Denom] using!
    (div_nonneg (mul_nonneg hmu hnum) hden)

theorem hatG_nonneg_of_admissible_and_coeff_bounds
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    ∀ i, 0 ≤ C.hatG i := by
  have hmain : ∀ m, ∀ i : Idx n, futureCountNat i = m → 0 ≤ C.hatG i := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro i hi
        by_cases hgt : C.t1 < i
        · rw [C.copied_above_t1 hgt]
          exact C.phaseTwo.hatG2_nonneg i
        · by_cases heq : i = C.t1
          · subst heq
            have hA : 0 ≤ C.boundaryHatGA := C.boundaryHatGA_nonneg_of_admissible hΓ hγlo hγhi
            have hB : 0 ≤ C.boundaryHatGB := C.boundaryHatGB_nonneg
            have hEq : C.hatG C.t1 = C.boundaryHatGA + C.boundaryHatGB := C.boundary_eq
            linarith
          · have hlt : i < C.t1 := lt_of_le_of_ne (not_lt.mp hgt) heq
            have hlater : ∀ k, i < k → 0 ≤ C.hatG k := by
              intro k hik
              have hklt : futureCountNat k < m := by
                rw [← hi]
                exact futureCountNat_lt_of_lt hik
              exact ih (futureCountNat k) hklt k rfl
            exact C.hatG_nonneg_of_phase1_of_later_nonneg hΓ hγlo hγhi hlt hlater
  intro i
  exact hmain (futureCountNat i) i rfl

/-- The paper's abbreviation `χ_j = [1 - R_{j-1}/θ]^+`. -/
def chi (C : ProfileData I Γ) (j : Idx n) : ℝ :=
  posPart (1 - beforeBudget C.hatG j / I.program.theta)

@[simp] theorem chi_nonneg (C : ProfileData I Γ) (j : Idx n) : 0 ≤ C.chi j := by
  simp [ProfileData.chi]

theorem chi_le_one_of_hatG_nonneg
    (C : ProfileData I Γ) (hhatG : ∀ i, 0 ≤ C.hatG i)
    (hθ : 0 ≤ I.program.theta) (j : Idx n) :
    C.chi j ≤ 1 := by
  simpa [ProfileData.chi] using
    posPart_sub_div_le_one (beforeBudget_nonneg_of_nonneg hhatG j) hθ

/-- Membership weights from Equation `(membership-assignment)` in `new_procedure.tex`. -/
def memberships (C : ProfileData I Γ) : MembershipWeights n where
  muA j :=
    if j < C.t1 then
      1 - Γ.muD j
    else if j = C.t1 then
      (1 - C.alpha) * (1 - Γ.muD j)
    else
      0
  muB j :=
    if j = C.t1 then
      C.alpha * (1 - Γ.muD j)
    else if C.t1 < j ∧ j ≤ C.t2 then
      1 - Γ.muD j
    else
      0
  muC j :=
    if C.t2 < j ∧ j ≤ Γ.t3Star then
      1 - Γ.muD j
    else
      0
  muD := Γ.muD

@[simp] theorem memberships_muD (C : ProfileData I Γ) (j : Idx n) :
    (C.memberships).muD j = Γ.muD j := rfl

theorem memberships_total (C : ProfileData I Γ) (j : Idx n) :
    (C.memberships).total j = 1 := by
  unfold MembershipWeights.total
  by_cases hj₁ : j < C.t1
  · have hneq : j ≠ C.t1 := ne_of_lt hj₁
    have hnotB : ¬ (C.t1 < j ∧ j ≤ C.t2) := by
      intro h
      exact (not_lt.mpr (le_of_lt hj₁)) h.1
    have hnotC : ¬ (C.t2 < j ∧ j ≤ Γ.t3Star) := by
      intro h
      exact (not_lt.mpr (le_trans (le_of_lt hj₁) C.t1_le_t2)) h.1
    simp [ProfileData.memberships, hj₁, hneq, hnotB, hnotC]
  · by_cases hj₂ : j = C.t1
    · have hnotC : ¬ (C.t2 < C.t1 ∧ C.t1 ≤ Γ.t3Star) := by
        intro h
        exact (not_lt.mpr C.t1_le_t2) h.1
      simp [ProfileData.memberships, hj₂, hnotC]
      ring_nf
    · by_cases hj₃ : C.t1 < j ∧ j ≤ C.t2
      · have hnotC : ¬ (C.t2 < j ∧ j ≤ Γ.t3Star) := by
          intro h
          exact (not_lt.mpr hj₃.2) h.1
        simp [ProfileData.memberships, hj₁, hj₂, hj₃, hnotC]
      · by_cases hj₄ : C.t2 < j ∧ j ≤ Γ.t3Star
        · simp [ProfileData.memberships, hj₁, hj₂, hj₃, hj₄]
        · have ht1j : C.t1 < j := by
            exact lt_of_le_of_ne (not_lt.mp hj₁) (Ne.symm hj₂)
          have ht2j : C.t2 < j := by
            apply lt_of_not_ge
            intro hjle
            exact hj₃ ⟨ht1j, hjle⟩
          have ht3j : Γ.t3Star < j := by
            apply lt_of_not_ge
            intro hjle
            exact hj₄ ⟨ht2j, hjle⟩
          have hμ : Γ.muD j = 1 := Advice.muD_eq_one Γ
            (lt_of_lt_of_le ht3j (I.le_firstBidTime j))
          simp [ProfileData.memberships, hj₁, hj₂, hj₃, hj₄, hμ]

theorem memberships_muA_eq_of_lt_t1
    (C : ProfileData I Γ) {j : Idx n} (hj : j < C.t1) :
    (C.memberships).muA j = 1 - Γ.muD j := by
  simp [ProfileData.memberships, hj]

theorem memberships_muB_eq_zero_of_lt_t1
    (C : ProfileData I Γ) {j : Idx n} (hj : j < C.t1) :
    (C.memberships).muB j = 0 := by
  have hneq : j ≠ C.t1 := ne_of_lt hj
  have hnot : ¬ C.t1 < j := not_lt.mpr (le_of_lt hj)
  simp [ProfileData.memberships, hneq, hnot]

theorem memberships_muC_eq_zero_of_lt_t1
    (C : ProfileData I Γ) {j : Idx n} (hj : j < C.t1) :
    (C.memberships).muC j = 0 := by
  have hnot : ¬ C.t2 < j := not_lt.mpr (le_trans (le_of_lt hj) C.t1_le_t2)
  simp [ProfileData.memberships, hnot]

theorem memberships_muA_eq_one_of_lt_t1_of_muD_eq_zero
    (C : ProfileData I Γ) {j : Idx n} (hj : j < C.t1) (hμ : Γ.muD j = 0) :
    (C.memberships).muA j = 1 := by
  rw [C.memberships_muA_eq_of_lt_t1 hj, hμ]
  simp

theorem memberships_nonnegative_of_admissible
    (C : ProfileData I Γ) (hΓ : Γ.Admissible) (hα : 0 ≤ C.alpha ∧ C.alpha ≤ 1) :
    MembershipWeights.Nonnegative C.memberships := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj₁ : j < C.t1
    · have hμ : Γ.muD j ≤ 1 := Advice.muD_le_one_of_admissible Γ hΓ j
      simp [ProfileData.memberships, hj₁, sub_nonneg.mpr hμ]
    · by_cases hj₂ : j = C.t1
      · have hα' : 0 ≤ 1 - C.alpha := sub_nonneg.mpr hα.2
        have hμ' : 0 ≤ 1 - Γ.muD j :=
          sub_nonneg.mpr (Advice.muD_le_one_of_admissible Γ hΓ j)
        have hμ'' : 0 ≤ 1 - Γ.muD C.t1 := by simpa [hj₂] using hμ'
        simpa [ProfileData.memberships, hj₂] using
          (mul_nonneg hα' hμ'' : 0 ≤ (1 - C.alpha) * (1 - Γ.muD C.t1))
      · simp [ProfileData.memberships, hj₁, hj₂]
  · intro j
    by_cases hj₁ : j = C.t1
    · have hμ' : 0 ≤ 1 - Γ.muD j :=
        sub_nonneg.mpr (Advice.muD_le_one_of_admissible Γ hΓ j)
      have hμ'' : 0 ≤ 1 - Γ.muD C.t1 := by simpa [hj₁] using hμ'
      simpa [ProfileData.memberships, hj₁] using
        (mul_nonneg hα.1 hμ'' : 0 ≤ C.alpha * (1 - Γ.muD C.t1))
    · by_cases hj₂ : C.t1 < j ∧ j ≤ C.t2
      · have hμ : Γ.muD j ≤ 1 := Advice.muD_le_one_of_admissible Γ hΓ j
        simp [ProfileData.memberships, hj₁, hj₂, sub_nonneg.mpr hμ]
      · simp [ProfileData.memberships, hj₁, hj₂]
  · intro j
    by_cases hj : C.t2 < j ∧ j ≤ Γ.t3Star
    · have hμ : Γ.muD j ≤ 1 := Advice.muD_le_one_of_admissible Γ hΓ j
      simp [ProfileData.memberships, hj, sub_nonneg.mpr hμ]
    · simp [ProfileData.memberships, hj]
  · intro j
    simpa [ProfileData.memberships] using Advice.muD_nonneg_of_admissible Γ hΓ j

theorem muC_pos_implies_t2_lt
    (C : ProfileData I Γ) {j : Idx n} (hj : 0 < (C.memberships).muC j) :
    C.t2 < j := by
  by_cases hcond : C.t2 < j ∧ j ≤ Γ.t3Star
  · exact hcond.1
  · have hzero : (C.memberships).muC j = 0 := by
      simp [ProfileData.memberships, hcond]
    linarith

theorem beforeBudget_le_barTau_of_muC_pos
    (C : ProfileData I Γ) {j : Idx n} (hj : 0 < (C.memberships).muC j) :
    beforeBudget C.hatG j ≤ I.program.barTau := by
  have ht2j : C.t2 < j := C.muC_pos_implies_t2_lt hj
  have ht1j : C.t1 < j := lt_of_le_of_lt C.t1_le_t2 ht2j
  have hphase : C.phaseTwo.beforeBudget j < I.program.barTau :=
    C.phaseTwo_beforeBudget_lt_barTau_above_t1 ht1j
  rw [C.beforeBudget_eq_phaseTwo_beforeBudget_of_lt_t1 ht1j]
  linarith

end ProfileData

end

end KMedian195


