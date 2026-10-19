-- Prove2me | Definitions.Def_InnovContest_Rewards_Model
-- name    : InnovContest_Rewards_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:32.230906+00:00
-- url     : https://prove2.me/theorems/3fb21d3a-a2a8-4b37-a2ba-d23d402ad9cb
-- title:
--   Innovation contest with costly entry and rank rewards
-- statement:
--   There are $n\ge2$ potential solvers with independent abilities distributed on $[0,1]$ according to a common CDF $F$ with continuous, strictly positive density $f$. A feasible reward allocation gives weakly decreasing, nonnegative rank rewards $r_1,\ldots,r_n$ whose sum does not exceed the budget $B$.
--
--   The model defines the expected rank reward $R(a)$, the entry threshold $a_{\min}$, equilibrium submission performance $x^*(a)$, and the firm's objective
--
--   $$\mathbb E\!\left[\max_{1\le i\le n}\{x^*(A_i)\mathbf1_{\{A_i\ge a_{\min}\}}\}\right]-c_f\Pr\{N=0\}.$$
--
--   Both $a_{\min}$ and $x^*$ are recomputed for each allocation. The number of rewards counts strictly positive rank rewards; the participation-optimal number $m_p^*$ is the largest number of equal awards minimizing $a_{\min}$. This model supports the paper's optimal design comparison.
--
--   **Formalization Note** Ranks start at one, with rewards beyond rank $n$ set to zero. The unused coordinate $r_0$ is fixed at zero. When no ability meets the expected-reward threshold, $a_{\min}=1$. All profiles use the product of the density-based ability measure.
-- source:
--   Stouras, Hutchison-Krupat & Chao, The Role of Participation in Innovation Contests, SSRN 2924224 (accepted version), pp. 6–12, Sections 3–5.1, equations (1), (3), (4), (6), and p. ec1 (PDF 35)

import Mathlib
import Definitions.Def_InnovContest_Rewards_OrderStats

open MeasureTheory Set

namespace InnovContest.Rewards

/-- The ability distribution and population assumed in Sections 3–5 of the paper. -/
structure AbilityModel where
  n : ℕ
  hn : 2 ≤ n
  F : ℝ → ℝ
  f : ℝ → ℝ
  hf : ContinuousOn f (Icc 0 1)
  hpos : ∀ a ∈ Icc (0 : ℝ) 1, 0 < f a
  hF : ∀ a ∈ Icc (0 : ℝ) 1, F a = ∫ y in (0 : ℝ)..a, f y
  hF1 : F 1 = 1

/-- Reward allocations are nonnegative and weakly decreasing on ranks `1,…,n`, with no reward
beyond rank `n`; the budget is an upper bound on the sum of the announced rewards. -/
def Feasible (n : ℕ) (budget : ℝ) (r : ℕ → ℝ) : Prop :=
  r 0 = 0 ∧
  (∀ j, 1 ≤ j → j ≤ n → r (j + 1) ≤ r j) ∧
  (∀ j, n < j → r j = 0) ∧ 0 ≤ r n ∧
  ∑ j ∈ Finset.Icc 1 n, r j ≤ budget

/-- The number of strictly positive announced rewards. -/
noncomputable def numRewards (n : ℕ) (r : ℕ → ℝ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun j => 0 < r j)).card

/-- The equal allocation of `budget` over ranks `1,…,m`. -/
noncomputable def equalSplit (budget : ℝ) (m : ℕ) : ℕ → ℝ :=
  fun j => if 1 ≤ j ∧ j ≤ m then budget / m else 0

/-- The expected rank reward for ability `a` when the other solvers are ranked by ability.
The rank `j` is the `j`-th *highest*, while `ordCDF` indexes from the lowest. -/
def expReward (M : AbilityModel) (r : ℕ → ℝ) (a : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 M.n,
    (r j - r (j + 1)) * ordCDF (M.n - 1) (M.n - j) (M.F a)

/-- The lower ability threshold. The empty sublevel complement gives the boundary value `1`. -/
noncomputable def amin (M : AbilityModel) (r : ℕ → ℝ) (cp : ℝ) : ℝ :=
  by
    classical
    exact if {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧ cp ≤ expReward M r a}.Nonempty then
      sInf {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧ cp ≤ expReward M r a}
    else 1

/-- Equation (4): the equilibrium submission performance. It is zero below `a_min`. -/
noncomputable def xstar (M : AbilityModel) (r : ℕ → ℝ) (cp a : ℝ) : ℝ :=
  if a < amin M r cp then 0 else
    ∑ j ∈ Finset.Icc 1 (M.n - 1),
      (r j - r (j + 1)) *
        ∫ y in (amin M r cp)..a,
          y * ordPDF (M.n - 1) (M.n - j) M.F M.f y

/-- A single solver's ability law, supported on `[0,1]`. -/
noncomputable def abilityLaw (M : AbilityModel) : Measure ℝ :=
  (volume.restrict (Icc (0 : ℝ) 1)).withDensity
    (fun y => ENNReal.ofReal (M.f y))

/-- The independent ability profile of all `n` solvers. -/
noncomputable def profileLaw (M : AbilityModel) : Measure (Fin M.n → ℝ) :=
  Measure.pi (fun _ : Fin M.n => abilityLaw M)

/-- The best performance among entrants in an ability profile; zero performance is assigned to
a solver who does not enter. The maximum is well-defined because `n ≥ 2`. -/
noncomputable def bestSubmission (M : AbilityModel) (r : ℕ → ℝ) (cp : ℝ)
    (A : Fin M.n → ℝ) : ℝ := by
  have hn : 0 < M.n := lt_of_lt_of_le (by decide : 0 < 2) M.hn
  have h : (Finset.univ : Finset (Fin M.n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  exact Finset.univ.sup' h
    (fun i => if amin M r cp ≤ A i then xstar M r cp (A i) else 0)

/-- The expected best submission, the first term of equation (6). -/
noncomputable def bestExpected (M : AbilityModel) (r : ℕ → ℝ) (cp : ℝ) : ℝ :=
  ∫ A, bestSubmission M r cp A ∂profileLaw M

/-- The probability that no solver enters. -/
noncomputable def failProb (M : AbilityModel) (r : ℕ → ℝ) (cp : ℝ) : ℝ :=
  (profileLaw M).real {A | ∀ i : Fin M.n, A i < amin M r cp}

/-- Equation (6), evaluated afresh for every allocation `r`. -/
noncomputable def firmObjective (M : AbilityModel) (r : ℕ → ℝ)
    (cp cf : ℝ) : ℝ :=
  bestExpected M r cp - cf * failProb M r cp

/-- Optimality is over every feasible reward allocation at the same budget. -/
def IsOptimal (M : AbilityModel) (budget cp cf : ℝ) (r : ℕ → ℝ) : Prop :=
  Feasible M.n budget r ∧
  ∀ s : ℕ → ℝ, Feasible M.n budget s →
    firmObjective M s cp cf ≤ firmObjective M r cp cf

/-- The largest number of equal awards minimizing the participation threshold. -/
noncomputable def mstarP (M : AbilityModel) (budget cp : ℝ) : ℕ :=
  by
    classical
    exact ((Finset.Icc 1 M.n).filter (fun m =>
      ∀ k ∈ Finset.Icc 1 M.n,
        amin M (equalSplit budget m) cp ≤ amin M (equalSplit budget k) cp)).sup id

end InnovContest.Rewards


