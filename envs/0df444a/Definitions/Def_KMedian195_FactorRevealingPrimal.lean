-- Prove2me | Definitions.Def_KMedian195_FactorRevealingPrimal
-- name    : KMedian195_FactorRevealingPrimal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:43:57.049065+00:00
-- url     : https://prove2.me/theorems/eda40cae-d9e9-4892-9ab8-30436b45c69f
-- title:
--   KMedian195.FactorRevealingPrimal
-- statement:
--   This is module `KMedian195.FactorRevealingPrimal` of the library KMedian195: the proof that the factor-revealing program of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) (Part I, Definition 4.1, with the bid $[\alpha-\gamma d]^+$) has value at most $2-(\gamma-1)^2$ for $\gamma\in[1,1.224]$ (Part I, Theorem 4.4). The library was written by Codex in [epfl-thl2/project-k-median](https://github.com/epfl-thl2/project-k-median) (project `bound-195`, commit `d87e2a2`) and is taken from its copy in [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0).
--
--   **Contents.** The module is published as a whole: 94 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_KMedian195_FactorRevealingPrimal`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Imported/KMedian195/FactorRevealingPrimal.lean

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`,
file `bound-195/KMedian195/FactorRevealingPrimal.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`), and:
* The definitions `TimeIdx`, `TimeIdx.last`, `TimeIdx.ofIdx`, `TimeIdx.succ`,
  `OriginalPrimalSolution`, `OriginalPrimalSolution.bidValue`, `OriginalPrimalSolution.objective`,
  `OriginalPrimalSolution.Feasible` and `OriginalPrimalUpperBound` are moved to
  `Imported/KMedian195/Program.lean`, and the last three theorems (`originalPrimalUpperBound_exact`,
  `originalPrimalUpperBound_153_div_125_exact`, `originalPrimalUpperBound_195`) to
  `Imported/KMedian195/Main.lean`.
* In 6 places, `simpa ... using e` is `simpa ... using! e`: our Lean's `simpa` matches the
  simplified `e` against the goal only up to reducible unfolding; `using!` matches as before.
* `if_true` (deprecated) is `ite_true`.
* In `originalPrimalUpperBound_of_familyUpperBound`, `let` instead of `letI` for a `NeZero`
  instance (linter).
-/
module

public import Definitions.Def_KMedian195_UpperBound
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `KMedian195.FactorRevealingPrimal` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
@[expose] public section

namespace KMedian195

noncomputable section

namespace TimeIdx

@[simp] theorem ofIdx_val (i : Idx n) : (ofIdx i).1 = i.1 := rfl

@[simp] theorem succ_val (i : Idx n) : (succ i).1 = i.1 + 1 := rfl

@[simp] theorem ofIdx_lt_succ (i : Idx n) : ofIdx i < succ i := by
  exact Fin.lt_def.mpr (Nat.lt_succ_self _)

@[simp] theorem succ_eq_last [NeZero n] (i : Idx n) :
    succ i = last n ↔ i = lastIdx n := by
  constructor
  · intro h
    have hval : i.1 + 1 = n := by
      simpa [succ, last] using congrArg Fin.val h
    have hi : i.1 = n - 1 := by
      omega
    apply Fin.ext
    simpa [lastIdx, Nat.pred_eq_sub_one] using hi
  · intro h
    subst h
    apply Fin.ext
    simpa [succ, last, lastIdx, Nat.pred_eq_sub_one] using
      Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_neZero n))

end TimeIdx

/-- Strict prefix `{j | j < i}`. -/
def strictPrefixRange (i : Idx n) : Finset (Idx n) :=
  Finset.univ.filter fun j => j < i

@[simp] theorem mem_strictPrefixRange {i j : Idx n} :
    j ∈ strictPrefixRange i ↔ j < i := by
  simp [strictPrefixRange]

theorem strictPrefixRange_nonempty [NeZero n] {i : Idx n} (hi : firstIdx n < i) :
    (strictPrefixRange i).Nonempty := by
  refine ⟨firstIdx n, ?_⟩
  simpa using hi

/--
The linearized primal variables used in the corrected bridge to the current strict-`s` dual.

We keep `m` as a total function on `Idx n` for convenience, but the first entry `m_1`
is only a dummy coordinate: the metric rewrite below uses `m_i` only for rows `i > 1`.
-/
structure LinearizedPrimalSolution (n : ℕ) where
  d : Idx n → ℝ
  f : ℝ
  m : Idx n → ℝ
  r : Idx n → Idx n → ℝ
  aux : Idx n → Idx n → ℝ

namespace OriginalPrimalSolution

variable {n : ℕ}

/-- Increasing the bid's distance multiplier only relaxes the facility constraints. -/
theorem Feasible.mono_gamma {gamma gamma' : ℝ} {x : OriginalPrimalSolution n}
    (hx : x.Feasible gamma) (hγ : gamma ≤ gamma') : x.Feasible gamma' := by
  rcases hx with ⟨hnorm, hrow, htriangle, hmetric, hfacility, hf, hd, hr⟩
  refine ⟨hnorm, hrow, htriangle, hmetric, ?_, hf, hd, hr⟩
  intro k
  refine le_trans (Finset.sum_le_sum ?_) (hfacility k)
  intro j _
  split_ifs <;>
    exact max_le_max (sub_le_sub_left (mul_le_mul_of_nonneg_right hγ (hd j)) _) le_rfl

/-- For a fixed finite configuration, its objective is continuous in the bid parameter. -/
theorem continuous_objective (x : OriginalPrimalSolution n) :
    Continuous (fun gamma => x.objective gamma) := by
  unfold objective bidValue
  fun_prop

end OriginalPrimalSolution

namespace OriginalPrimalSolution

variable {n : ℕ} [NeZero n]

/-- A predecessor of `i` minimizing `r_{j,i} + d_j` over all strict predecessors `j < i`. -/
noncomputable def predecessorArgmin
    (x : OriginalPrimalSolution n) (i : Idx n) (hi : firstIdx n < i) : Idx n :=
  Classical.choose <|
    Finset.exists_min_image (strictPrefixRange i)
      (fun j => x.r j (TimeIdx.ofIdx i) + x.d j)
      (strictPrefixRange_nonempty hi)

theorem predecessorArgmin_mem
    (x : OriginalPrimalSolution n) (i : Idx n) (hi : firstIdx n < i) :
    x.predecessorArgmin i hi ∈ strictPrefixRange i :=
  (Classical.choose_spec
    (Finset.exists_min_image (strictPrefixRange i)
      (fun j => x.r j (TimeIdx.ofIdx i) + x.d j)
      (strictPrefixRange_nonempty hi))).1

theorem predecessorArgmin_lt
    (x : OriginalPrimalSolution n) (i : Idx n) (hi : firstIdx n < i) :
    x.predecessorArgmin i hi < i := by
  simpa using x.predecessorArgmin_mem i hi

theorem predecessorArgmin_spec
    (x : OriginalPrimalSolution n) (i : Idx n) (hi : firstIdx n < i)
    {j : Idx n} (hj : j ∈ strictPrefixRange i) :
    x.r (x.predecessorArgmin i hi) (TimeIdx.ofIdx i) + x.d (x.predecessorArgmin i hi) ≤
      x.r j (TimeIdx.ofIdx i) + x.d j :=
  (Classical.choose_spec
    (Finset.exists_min_image (strictPrefixRange i)
      (fun j => x.r j (TimeIdx.ofIdx i) + x.d j)
      (strictPrefixRange_nonempty hi))).2 j hj

/-- The corrected auxiliary metric variable `m_i`. -/
def mValue (x : OriginalPrimalSolution n) (i : Idx n) : ℝ :=
  if hi : firstIdx n < i then
    x.r (x.predecessorArgmin i hi) (TimeIdx.ofIdx i) + x.d (x.predecessorArgmin i hi)
  else
    0

@[simp] theorem mValue_eq_of_firstIdx_lt
    (x : OriginalPrimalSolution n) {i : Idx n} (hi : firstIdx n < i) :
    x.mValue i =
      x.r (x.predecessorArgmin i hi) (TimeIdx.ofIdx i) + x.d (x.predecessorArgmin i hi) := by
  simp [mValue, hi]

/-- The linearized bidding auxiliary term chosen from the original nonlinear bid. -/
def liftedAux (gamma : ℝ) (x : OriginalPrimalSolution n) (i j : Idx n) : ℝ :=
  if _h : j < i then
    bidValue gamma (x.r j (TimeIdx.ofIdx i)) (x.d j)
  else
    bidValue gamma (x.r i (TimeIdx.ofIdx i)) (x.d j)

/-- The canonical lift of an original FRP solution to the corrected linearized primal. -/
noncomputable def toLinearized (gamma : ℝ) (x : OriginalPrimalSolution n) :
    LinearizedPrimalSolution n where
  d := x.d
  f := x.f
  m := x.mValue
  r := fun j i => x.r j (TimeIdx.ofIdx i)
  aux := x.liftedAux gamma

@[simp] theorem toLinearized_d (gamma : ℝ) (x : OriginalPrimalSolution n) (j : Idx n) :
    (x.toLinearized gamma).d j = x.d j := rfl

@[simp] theorem toLinearized_f (gamma : ℝ) (x : OriginalPrimalSolution n) :
    (x.toLinearized gamma).f = x.f := rfl

@[simp] theorem toLinearized_m (gamma : ℝ) (x : OriginalPrimalSolution n) (i : Idx n) :
    (x.toLinearized gamma).m i = x.mValue i := rfl

@[simp] theorem toLinearized_r
    (gamma : ℝ) (x : OriginalPrimalSolution n) (j i : Idx n) :
    (x.toLinearized gamma).r j i = x.r j (TimeIdx.ofIdx i) := rfl

@[simp] theorem toLinearized_aux
    (gamma : ℝ) (x : OriginalPrimalSolution n) (i j : Idx n) :
    (x.toLinearized gamma).aux i j = x.liftedAux gamma i j := rfl

end OriginalPrimalSolution

namespace LinearizedPrimalSolution

variable {n : ℕ} [NeZero n]

def objectiveTerm (gamma : ℝ) (bidding : BiddingMatrix n)
    (x : LinearizedPrimalSolution n) (i j : Idx n) : ℝ :=
  if h : i < lastIdx n then
    bidding.coeff i j * (x.r j i - gamma * x.r j (succIdx i h))
  else
    bidding.coeff i j * x.r j i

def objective (gamma : ℝ) (bidding : BiddingMatrix n)
    (x : LinearizedPrimalSolution n) : ℝ :=
  (Finset.sum Finset.univ fun j =>
    Finset.sum (suffixRange j) (fun i => x.objectiveTerm gamma bidding i j)) - x.f

/--
The corrected metric rewrite uses `m_i` only for `i > 1`.

For a fixed row `i > 1`, the lower metric constraint only appears for `j < i`, while the
upper metric constraint appears for all `j ≤ i`. This is the primal-side source of the
strict-lower `s_{i,j}` terms and the still-present diagonal `t_{i,i}` terms in the dual.
-/
def Feasible (gamma : ℝ) (x : LinearizedPrimalSolution n) : Prop :=
  (Finset.sum Finset.univ x.d ≤ 1) ∧
    (∀ ⦃j i : Idx n⦄, j < i → x.m i ≤ x.r j i + x.d j) ∧
    (∀ ⦃j i : Idx n⦄, j ≤ i → firstIdx n < i → x.r j i ≤ x.m i + x.d j) ∧
    (∀ ⦃j i : Idx n⦄, j ≤ i → ∀ h : i < lastIdx n, x.r j (succIdx i h) ≤ x.r j i) ∧
    (∀ ⦃i : Idx n⦄, firstIdx n < i → ∀ h : i < lastIdx n, x.m (succIdx i h) ≤ x.m i) ∧
    (∀ ⦃j i : Idx n⦄, j < i → x.r j i - gamma * x.d j ≤ x.aux i j) ∧
    (∀ ⦃i j : Idx n⦄, i ≤ j → x.r i i - gamma * x.d j ≤ x.aux i j) ∧
    (∀ i : Idx n, Finset.sum Finset.univ (x.aux i) ≤ x.f) ∧
    (0 ≤ x.f) ∧
    (∀ j, 0 ≤ x.d j) ∧
    (∀ i, 0 ≤ x.m i) ∧
    (∀ j i, 0 ≤ x.r j i) ∧
    (∀ i j, 0 ≤ x.aux i j)

end LinearizedPrimalSolution

namespace OriginalPrimalSolution

variable {n : ℕ} [NeZero n]

theorem toLinearized_feasible
    {gamma : ℝ} {x : OriginalPrimalSolution n} (hx : x.Feasible gamma) :
    (x.toLinearized gamma).Feasible gamma := by
  rcases hx with ⟨hNorm, hMono, hTriangle, hMetric, hFacility, hf, hdNonneg, hrNonneg⟩
  refine ⟨le_of_eq hNorm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hf, ?_, ?_, ?_, ?_⟩
  · intro j i hji
    have hi : firstIdx n < i := lt_of_le_of_lt (firstIdx_le j) hji
    change x.mValue i ≤ x.r j (TimeIdx.ofIdx i) + x.d j
    rw [x.mValue_eq_of_firstIdx_lt hi]
    exact x.predecessorArgmin_spec i hi (by simpa using hji)
  · intro j i hji hi
    change x.r j (TimeIdx.ofIdx i) ≤ x.mValue i + x.d j
    rw [x.mValue_eq_of_firstIdx_lt hi]
    let k := x.predecessorArgmin i hi
    have hk : k < i := x.predecessorArgmin_lt i hi
    by_cases hjk : j = k
    · subst hjk
      nlinarith [hdNonneg k]
    · by_cases hji' : j < i
      · have hjof : TimeIdx.ofIdx j < TimeIdx.ofIdx i := by
          simpa using! hji'
        have hkof : TimeIdx.ofIdx k < TimeIdx.ofIdx i := by
          simpa [k] using! hk
        have hmetric := hMetric hjk hjof hkof
        simpa [k, add_assoc, add_left_comm, add_comm] using hmetric
      · have hEq : j = i := le_antisymm hji (not_lt.mp hji')
        subst hEq
        have htri := hTriangle hk
        simpa [k, add_assoc, add_left_comm, add_comm] using htri
  · intro j i hji hlast
    change x.r j (TimeIdx.ofIdx (succIdx i hlast)) ≤ x.r j (TimeIdx.ofIdx i)
    have hsucc : TimeIdx.ofIdx (succIdx i hlast) = TimeIdx.succ i := by
      apply Fin.ext
      simp [TimeIdx.ofIdx, TimeIdx.succ, succIdx_val]
    rw [hsucc]
    exact hMono hji
  · intro i hi hlast
    have hiSucc : firstIdx n < succIdx i hlast := lt_trans hi (lt_succIdx i hlast)
    change x.mValue (succIdx i hlast) ≤ x.mValue i
    rw [x.mValue_eq_of_firstIdx_lt hiSucc, x.mValue_eq_of_firstIdx_lt hi]
    let k := x.predecessorArgmin i hi
    have hk : k < i := x.predecessorArgmin_lt i hi
    have hkSucc : k ∈ strictPrefixRange (succIdx i hlast) := by
      simpa using lt_of_lt_of_le hk (le_of_lt (lt_succIdx i hlast))
    have hmin :=
      x.predecessorArgmin_spec (succIdx i hlast) hiSucc hkSucc
    have hsucc : TimeIdx.ofIdx (succIdx i hlast) = TimeIdx.succ i := by
      apply Fin.ext
      simp [TimeIdx.ofIdx, TimeIdx.succ, succIdx_val]
    have hmono' : x.r k (TimeIdx.ofIdx (succIdx i hlast)) ≤ x.r k (TimeIdx.ofIdx i) := by
      rw [hsucc]
      exact hMono (le_of_lt hk)
    nlinarith
  · intro j i hji
    change x.r j (TimeIdx.ofIdx i) - gamma * x.d j ≤ x.liftedAux gamma i j
    unfold OriginalPrimalSolution.liftedAux OriginalPrimalSolution.bidValue
    simp [hji]
  · intro i j hij
    change x.r i (TimeIdx.ofIdx i) - gamma * x.d j ≤ x.liftedAux gamma i j
    unfold OriginalPrimalSolution.liftedAux OriginalPrimalSolution.bidValue
    simp [not_lt_of_ge hij]
  · intro i
    simpa [OriginalPrimalSolution.toLinearized, OriginalPrimalSolution.liftedAux] using!
      hFacility i
  · intro j
    simpa using hdNonneg j
  · intro i
    change 0 ≤ x.mValue i
    by_cases hi : firstIdx n < i
    · rw [x.mValue_eq_of_firstIdx_lt hi]
      nlinarith [hrNonneg (x.predecessorArgmin i hi) (TimeIdx.ofIdx i),
        hdNonneg (x.predecessorArgmin i hi)]
    · simp [OriginalPrimalSolution.mValue, hi]
  · intro j i
    simpa using hrNonneg j (TimeIdx.ofIdx i)
  · intro i j
    change 0 ≤ x.liftedAux gamma i j
    unfold OriginalPrimalSolution.liftedAux OriginalPrimalSolution.bidValue
    by_cases hji : j < i <;> simp [hji]

end OriginalPrimalSolution

/--
The direct dual of the corrected linearized primal keeps the client and pool slack variables
explicit instead of telescoping them away.
-/
structure DirectDualSolution (n : ℕ) where
  rho : ℝ
  hatG : Idx n → ℝ
  g : Idx n → Idx n → ℝ
  s : Idx n → Idx n → ℝ
  t : Idx n → Idx n → ℝ
  clientSlack : Idx n → Idx n → ℝ
  poolSlack : Idx n → ℝ

namespace DirectDualSolution

variable {n : ℕ} [NeZero n]

def predIdx (i : Idx n) (hi : firstIdx n < i) : Idx n :=
  ⟨i.1 - 1, by
    have hi0 : 0 < i.1 := by
      simpa [firstIdx] using hi
    omega⟩

def toDualSolution (x : DirectDualSolution n) : DualSolution n where
  rho := x.rho
  hatG := x.hatG
  g := x.g
  s := x.s
  t := x.t

def rowValue (x : DirectDualSolution n) (i : Idx n) : ℝ :=
  Finset.sum (prefixRange i) (fun j => x.toDualSolution.strictS i j - x.t i j)

def Feasible (gamma : ℝ) (bidding : BiddingMatrix n) (x : DirectDualSolution n) : Prop :=
  let P : DualProgram n := { Mcoeff := gamma, bidding := bidding }
  x.toDualSolution.BoundedHatG ∧
    x.toDualSolution.DominatesColumns ∧
    (∀ j : Idx n, x.toDualSolution.clientCredit j j - x.clientSlack j j ≥ P.bid j j) ∧
    (∀ ⦃i j : Idx n⦄, j ≤ i → ∀ h : i < lastIdx n,
      x.clientSlack i j +
          (x.g (succIdx i h) j + x.t (succIdx i h) j -
            x.toDualSolution.strictS (succIdx i h) j) -
          x.clientSlack (succIdx i h) j ≥
        P.bid (succIdx i h) j - gamma * P.bid i j) ∧
    (∀ j : Idx n, x.clientSlack (lastIdx n) j = 0) ∧
    (∀ ⦃i : Idx n⦄, (hi : firstIdx n < i) →
      x.poolSlack (predIdx i hi) + x.rowValue i - x.poolSlack i ≥ 0) ∧
    x.poolSlack (firstIdx n) = 0 ∧
    x.poolSlack (lastIdx n) = 0 ∧
    x.toDualSolution.SatisfiesValueConstraints P ∧
    x.toDualSolution.Nonnegative ∧
    (x.t (firstIdx n) (firstIdx n) = 0) ∧
    (∀ ⦃i j : Idx n⦄, j ≤ i → 0 ≤ x.clientSlack i j) ∧
    (∀ i, 0 ≤ x.poolSlack i)

end DirectDualSolution

/-- The client slack variables recovered from a feasible solution of the telescoped dual. -/
def clientSlackOfDual {n : ℕ} [NeZero n] (gamma : ℝ) (P : DualProgram n)
    (x : DualSolution n) (i j : Idx n) : ℝ :=
  if _h : i < lastIdx n then
    x.clientCredit i j - P.bid i j +
      (gamma - 1) * Finset.sum (halfOpenIntervalRange j i) (fun p => P.bid p j)
  else
    0

/-- The pool slack variables recovered from a feasible solution of the telescoped dual. -/
def poolSlackOfDual {n : ℕ} [NeZero n] (x : DualSolution n) (i : Idx n) : ℝ :=
  if i < lastIdx n then x.poolCredit i else 0

/-- Turn a feasible solution of the telescoped dual into one for the direct dual by recovering
the slack variables explicitly. -/
def DirectDualSolution.ofDualSolution {n : ℕ} [NeZero n] (gamma : ℝ) (bidding : BiddingMatrix n)
    (x : DualSolution n) : DirectDualSolution n where
  rho := x.rho
  hatG := x.hatG
  g := x.g
  s := x.s
  t := x.t
  clientSlack := clientSlackOfDual gamma { Mcoeff := gamma, bidding := bidding } x
  poolSlack := poolSlackOfDual x

theorem intervalRange_succ_eq_insert {n : ℕ} [NeZero n] {i j : Idx n}
    (hji : j ≤ i) (h : i < lastIdx n) :
    intervalRange j (succIdx i h) = insert (succIdx i h) (intervalRange j i) := by
  ext p
  constructor
  · intro hp
    rcases mem_intervalRange.mp hp with ⟨hjp, hps⟩
    by_cases hpeq : p = succIdx i h
    · simp [hpeq]
    · have hpi : p ≤ i := by
        have hlt : p < succIdx i h := lt_of_le_of_ne hps hpeq
        exact (lt_succIdx_iff h).1 hlt
      simp [hpeq, mem_intervalRange.mpr ⟨hjp, hpi⟩]
  · intro hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact mem_intervalRange.mpr ⟨le_trans hji (le_of_lt (lt_succIdx i h)), le_rfl⟩
    · rcases mem_intervalRange.mp hp with ⟨hjp, hpi⟩
      exact mem_intervalRange.mpr ⟨hjp, le_trans hpi (le_of_lt (lt_succIdx i h))⟩

theorem halfOpenIntervalRange_succ_eq_insert {n : ℕ} [NeZero n] {i j : Idx n}
    (hji : j ≤ i) (h : i < lastIdx n) :
    halfOpenIntervalRange j (succIdx i h) = insert i (halfOpenIntervalRange j i) := by
  ext p
  constructor
  · intro hp
    rcases mem_halfOpenIntervalRange.mp hp with ⟨hjp, hps⟩
    by_cases hpeq : p = i
    · simp [hpeq, mem_halfOpenIntervalRange, hji]
    · have hpi : p < i := by
        have hle : p ≤ i := (lt_succIdx_iff h).1 hps
        exact lt_of_le_of_ne hle hpeq
      simp [hpeq, mem_halfOpenIntervalRange.mpr ⟨hjp, hpi⟩]
  · intro hp
    rcases Finset.mem_insert.mp hp with hp | hp
    · subst hp
      exact mem_halfOpenIntervalRange.mpr ⟨hji, lt_succIdx _ h⟩
    · rcases mem_halfOpenIntervalRange.mp hp with ⟨hjp, hpi⟩
      exact mem_halfOpenIntervalRange.mpr ⟨hjp, lt_of_lt_of_le hpi (le_of_lt (lt_succIdx i h))⟩

theorem DirectDualSolution.predIdx_lt {n : ℕ} [NeZero n] (i : Idx n) (hi : firstIdx n < i) :
    DirectDualSolution.predIdx i hi < i := by
  change (DirectDualSolution.predIdx i hi).1 < i.1
  dsimp [DirectDualSolution.predIdx]
  have hi0 : 0 < i.1 := by
    simpa [firstIdx] using hi
  omega

theorem DirectDualSolution.succ_predIdx {n : ℕ} [NeZero n] {i : Idx n} (hi : firstIdx n < i) :
    succIdx (DirectDualSolution.predIdx i hi)
      (lt_of_lt_of_le (DirectDualSolution.predIdx_lt i hi) (le_lastIdx i)) = i := by
  apply Fin.ext
  change i.1 - 1 + 1 = i.1
  have hi0 : 0 < i.1 := by
    simpa [firstIdx] using hi
  omega

theorem DirectDualSolution.predIdx_succ {n : ℕ} [NeZero n] {i : Idx n} (h : i < lastIdx n) :
    DirectDualSolution.predIdx (succIdx i h)
      (lt_of_le_of_lt (firstIdx_le i) (lt_succIdx i h)) = i := by
  apply Fin.ext
  change i.1 + 1 - 1 = i.1
  omega

theorem suffixRange_eq_insert_strictSuffix {n : ℕ} (j : Idx n) :
    suffixRange j = insert j (strictSuffixRange j) := by
  ext i
  constructor
  · intro hi
    by_cases hij : i = j
    · simp [hij]
    · have hgt : j < i := lt_of_le_of_ne (mem_suffixRange.mp hi) (by
          intro hEq
          exact hij hEq.symm)
      exact Finset.mem_insert.mpr (Or.inr (mem_strictSuffixRange.mpr hgt))
  · intro hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact mem_suffixRange.mpr le_rfl
    · exact mem_suffixRange.mpr (le_of_lt (mem_strictSuffixRange.mp hi'))

theorem prefixRange_eq_insert_strictPrefix {n : ℕ} (i : Idx n) :
    prefixRange i = insert i (strictPrefixRange i) := by
  ext j
  constructor
  · intro hj
    by_cases hji : j = i
    · simp [hji]
    · have hjlt : j < i := lt_of_le_of_ne (mem_prefixRange.mp hj) hji
      exact Finset.mem_insert.mpr (Or.inr (mem_strictPrefixRange.mpr hjlt))
  · intro hj
    rcases Finset.mem_insert.mp hj with rfl | hj'
    · exact mem_prefixRange.mpr le_rfl
    · exact mem_prefixRange.mpr (le_of_lt (mem_strictPrefixRange.mp hj'))

theorem strictSuffixRange_eq_suffixRange_succ {n : ℕ} [NeZero n] {i : Idx n}
    (hi : i < lastIdx n) :
    strictSuffixRange i = suffixRange (succIdx i hi) := by
  ext j
  simp [mem_strictSuffixRange, mem_suffixRange, succIdx_le_iff hi]

theorem sum_suffixRange_succ_eq_sum_strictSuffix {n : ℕ} [NeZero n] (j : Idx n)
    (f : Idx n → ℝ) :
    Finset.sum (suffixRange j) (fun i => if h : i < lastIdx n then f (succIdx i h) else 0) =
      Finset.sum (strictSuffixRange j) f := by
  classical
  let g : Idx n → ℝ := fun i => if h : i < lastIdx n then f (succIdx i h) else 0
  have hfilter :
      Finset.sum (suffixRange j) g =
        Finset.sum ((suffixRange j).filter fun i => i < lastIdx n) g := by
    calc
      Finset.sum (suffixRange j) g =
          Finset.sum (suffixRange j) (fun i => if i < lastIdx n then g i else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases h : i < lastIdx n <;> simp [h, g]
      _ = Finset.sum ((suffixRange j).filter fun i => i < lastIdx n) g := by
            symm
            exact Finset.sum_filter (s := suffixRange j) (p := fun i => i < lastIdx n) g
  rw [hfilter]
  refine Finset.sum_bij
    (fun i hi => succIdx i (Finset.mem_filter.mp hi).2)
    ?_ ?_ ?_ ?_
  · intro i hi
    have hji : j ≤ i := mem_suffixRange.mp (Finset.mem_filter.mp hi).1
    exact mem_strictSuffixRange.mpr (lt_of_le_of_lt hji (lt_succIdx i (Finset.mem_filter.mp hi).2))
  · intro i₁ hi₁ i₂ hi₂ hEq
    apply Fin.ext
    simpa [succIdx_val] using congrArg Fin.val hEq
  · intro i hi
    refine ⟨DirectDualSolution.predIdx i
        (lt_of_le_of_lt (firstIdx_le j) (mem_strictSuffixRange.mp hi)), ?_,
      ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · have hji : j < i := mem_strictSuffixRange.mp hi
        have hpred :
            j ≤ DirectDualSolution.predIdx i (lt_of_le_of_lt (firstIdx_le j) hji) := by
          change j.1 ≤
            (DirectDualSolution.predIdx i (lt_of_le_of_lt (firstIdx_le j) hji)).1
          have hji' : j.1 < i.1 := hji
          dsimp [DirectDualSolution.predIdx]
          omega
        exact mem_suffixRange.mpr hpred
      · exact lt_of_lt_of_le
          (DirectDualSolution.predIdx_lt i
            (lt_of_le_of_lt (firstIdx_le j) (mem_strictSuffixRange.mp hi)))
          (le_lastIdx i)
    · exact DirectDualSolution.succ_predIdx
        (lt_of_le_of_lt (firstIdx_le j) (mem_strictSuffixRange.mp hi))
  · intro i hi
    simp [(Finset.mem_filter.mp hi).2]

theorem prefixRange_eq_insert_pred {n : ℕ} [NeZero n] {i : Idx n} (hi : firstIdx n < i) :
    prefixRange i = insert i (prefixRange (DirectDualSolution.predIdx i hi)) := by
  ext p
  constructor
  · intro hp
    by_cases hpeq : p = i
    · subst hpeq
      simp
    · have hpi : p ≤ DirectDualSolution.predIdx i hi := by
        have hlt : p < i := lt_of_le_of_ne (mem_prefixRange.mp hp) hpeq
        change p.1 ≤ (DirectDualSolution.predIdx i hi).1
        have hltv : p.1 < i.1 := hlt
        dsimp [DirectDualSolution.predIdx]
        omega
      exact Finset.mem_insert.mpr (Or.inr (mem_prefixRange.mpr hpi))
  · intro hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact mem_prefixRange.mpr le_rfl
    · exact mem_prefixRange.mpr (le_trans (mem_prefixRange.mp hp) (le_of_lt
        (DirectDualSolution.predIdx_lt i hi)))

theorem clientCredit_succ_eq {n : ℕ} [NeZero n] (x : DualSolution n) {i j : Idx n}
    (hji : j ≤ i) (h : i < lastIdx n) :
    x.clientCredit (succIdx i h) j =
      x.clientCredit i j +
        (x.g (succIdx i h) j + x.t (succIdx i h) j - x.strictS (succIdx i h) j) := by
  unfold DualSolution.clientCredit
  have hset := intervalRange_succ_eq_insert hji h
  have hnot : succIdx i h ∉ intervalRange j i := by
    simp [mem_intervalRange, not_le_of_gt (lt_succIdx i h)]
  rw [hset, Finset.sum_insert hnot]
  ring

theorem poolCredit_step_eq {n : ℕ} [NeZero n] (x : DualSolution n) {i : Idx n}
    (hi : firstIdx n < i) :
    x.poolCredit i =
      x.poolCredit (DirectDualSolution.predIdx i hi) +
        Finset.sum (prefixRange i) (fun j => x.strictS i j - x.t i j) := by
  unfold DualSolution.poolCredit
  have hset := prefixRange_eq_insert_pred hi
  have hnot : i ∉ prefixRange (DirectDualSolution.predIdx i hi) := by
    simp [mem_prefixRange, not_le_of_gt (DirectDualSolution.predIdx_lt i hi)]
  rw [hset, Finset.sum_insert hnot]
  conv_rhs => rw [← hset]
  ring_nf

theorem t_first_first_eq_zero_of_feasible {n : ℕ} [NeZero n] {P : DualProgram n}
    {x : DualSolution n} (hx : x.Feasible P) :
    x.t (firstIdx n) (firstIdx n) = 0 := by
  rcases hx with ⟨_, _, _, hPool, _, hNonneg⟩
  rcases hNonneg with ⟨_, _, _, hTnonneg⟩
  have hfirstPool : x.poolCredit (firstIdx n) = -x.t (firstIdx n) (firstIdx n) := by
    have hprefix : prefixRange (firstIdx n) = ({firstIdx n} : Finset (Idx n)) := by
      ext j
      simp [prefixRange, firstIdx]
    simp [DualSolution.poolCredit, DualSolution.strictS, hprefix]
  have hpoolNonneg := hPool (firstIdx n)
  rw [hfirstPool] at hpoolNonneg
  nlinarith [hTnonneg (firstIdx n) (firstIdx n)]

theorem DirectDualSolution.rowValue_first_eq_zero {n : ℕ} [NeZero n] {x : DirectDualSolution n}
    (ht11 : x.t (firstIdx n) (firstIdx n) = 0) :
    x.rowValue (firstIdx n) = 0 := by
  have hprefix : prefixRange (firstIdx n) = ({firstIdx n} : Finset (Idx n)) := by
    ext j
    simp [prefixRange, firstIdx]
  simp [DirectDualSolution.rowValue, DualSolution.strictS, hprefix, ht11]

theorem sum_prefixRange_eq_sum_suffixRange {n : ℕ} (f : Idx n → Idx n → ℝ) :
    Finset.sum Finset.univ (fun i => Finset.sum (prefixRange i) (fun j => f i j)) =
      Finset.sum Finset.univ (fun j => Finset.sum (suffixRange j) (fun i => f i j)) := by
  classical
  calc
    Finset.sum Finset.univ (fun i => Finset.sum (prefixRange i) (fun j => f i j)) =
      Finset.sum Finset.univ (fun i =>
        Finset.sum Finset.univ (fun j => if j ≤ i then f i j else 0)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [show prefixRange i = Finset.univ.filter (fun j : Idx n => j ≤ i) by rfl]
        exact Finset.sum_filter (s := Finset.univ) (p := fun j : Idx n => j ≤ i)
          (f := fun j => f i j)
    _ = Finset.sum Finset.univ (fun j =>
          Finset.sum Finset.univ (fun i => if j ≤ i then f i j else 0)) := by
        rw [Finset.sum_comm]
    _ = Finset.sum Finset.univ (fun j => Finset.sum (suffixRange j) (fun i => f i j)) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [show suffixRange j = Finset.univ.filter (fun i : Idx n => j ≤ i) by rfl]
        exact (Finset.sum_filter (s := Finset.univ) (p := fun i : Idx n => j ≤ i)
          (f := fun i => f i j)).symm

theorem sum_strictPrefix_eq_sum_strictSuffix {n : ℕ} (f : Idx n → Idx n → ℝ) :
    Finset.sum Finset.univ (fun i => Finset.sum (strictPrefixRange i) (fun j => f i j)) =
      Finset.sum Finset.univ (fun j => Finset.sum (strictSuffixRange j) (fun i => f i j)) := by
  have hmain := sum_prefixRange_eq_sum_suffixRange (f := f)
  have hleft :
      Finset.sum Finset.univ (fun i => Finset.sum (prefixRange i) (fun j => f i j)) =
        Finset.sum Finset.univ (fun i => f i i) +
          Finset.sum Finset.univ (fun i => Finset.sum (strictPrefixRange i) (fun j => f i j)) := by
    calc
      Finset.sum Finset.univ (fun i => Finset.sum (prefixRange i) (fun j => f i j)) =
        Finset.sum Finset.univ
          (fun i => f i i + Finset.sum (strictPrefixRange i) (fun j => f i j)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [prefixRange_eq_insert_strictPrefix]
          simp
      _ =
        Finset.sum Finset.univ (fun i => f i i) +
          Finset.sum Finset.univ (fun i => Finset.sum (strictPrefixRange i) (fun j => f i j)) := by
          rw [Finset.sum_add_distrib]
  have hright :
      Finset.sum Finset.univ (fun j => Finset.sum (suffixRange j) (fun i => f i j)) =
        Finset.sum Finset.univ (fun j => f j j) +
          Finset.sum Finset.univ (fun j => Finset.sum (strictSuffixRange j) (fun i => f i j)) := by
    calc
      Finset.sum Finset.univ (fun j => Finset.sum (suffixRange j) (fun i => f i j)) =
        Finset.sum Finset.univ
          (fun j => f j j + Finset.sum (strictSuffixRange j) (fun i => f i j)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [suffixRange_eq_insert_strictSuffix]
          simp
      _ =
        Finset.sum Finset.univ (fun j => f j j) +
          Finset.sum Finset.univ (fun j => Finset.sum (strictSuffixRange j) (fun i => f i j)) := by
          rw [Finset.sum_add_distrib]
  rw [hleft, hright] at hmain
  nlinarith

def LinearizedPrimalSolution.auxLeft {n : ℕ}
    (x : LinearizedPrimalSolution n) (i j : Idx n) : ℝ :=
  if i ≤ j then x.r i i else x.r j i

def predBidCoeff {n : ℕ} [NeZero n] (bidding : BiddingMatrix n) (j i : Idx n) : ℝ :=
  if hi : firstIdx n < i then
    bidding.coeff (DirectDualSolution.predIdx i hi) j
  else
    0

def predClientSlack {n : ℕ} [NeZero n] (x : DirectDualSolution n) (j i : Idx n) : ℝ :=
  if hi : firstIdx n < i then
    x.clientSlack (DirectDualSolution.predIdx i hi) j
  else
    0

def predPoolSlack {n : ℕ} [NeZero n] (x : DirectDualSolution n) (i : Idx n) : ℝ :=
  if hi : firstIdx n < i then
    x.poolSlack (DirectDualSolution.predIdx i hi)
  else
    0

theorem predBidCoeff_eq_of_strictSuffix {n : ℕ} [NeZero n] (bidding : BiddingMatrix n)
    {j i : Idx n} (hji : j < i) :
    predBidCoeff bidding j i =
      bidding.coeff (DirectDualSolution.predIdx i (lt_of_le_of_lt (firstIdx_le j) hji)) j := by
  simp [predBidCoeff, lt_of_le_of_lt (firstIdx_le j) hji]

theorem predClientSlack_eq_of_strictSuffix {n : ℕ} [NeZero n] (x : DirectDualSolution n)
    {j i : Idx n} (hji : j < i) :
    predClientSlack x j i =
      x.clientSlack (DirectDualSolution.predIdx i (lt_of_le_of_lt (firstIdx_le j) hji)) j := by
  simp [predClientSlack, lt_of_le_of_lt (firstIdx_le j) hji]

theorem predClientSlack_succ {n : ℕ} [NeZero n] (x : DirectDualSolution n)
    {j i : Idx n} (h : i < lastIdx n) :
    predClientSlack x j (succIdx i h) = x.clientSlack i j := by
  have hsucc : firstIdx n < succIdx i h := lt_of_le_of_lt (firstIdx_le i) (lt_succIdx i h)
  simp [predClientSlack, hsucc, DirectDualSolution.predIdx_succ h]

theorem predPoolSlack_succ {n : ℕ} [NeZero n] (x : DirectDualSolution n)
    {i : Idx n} (h : i < lastIdx n) :
    predPoolSlack x (succIdx i h) = x.poolSlack i := by
  have hsucc : firstIdx n < succIdx i h := lt_of_le_of_lt (firstIdx_le i) (lt_succIdx i h)
  simp [predPoolSlack, hsucc, DirectDualSolution.predIdx_succ h]

theorem LinearizedPrimalSolution.objectiveColumn_eq_base_add_strictSuffix
    {n : ℕ} [NeZero n] (gamma : ℝ) (bidding : BiddingMatrix n)
    (x : LinearizedPrimalSolution n) (j : Idx n) :
    Finset.sum (suffixRange j) (fun i => x.objectiveTerm gamma bidding i j) =
      bidding.coeff j j * x.r j j +
        Finset.sum (strictSuffixRange j) (fun i =>
          (bidding.coeff i j - gamma * predBidCoeff bidding j i) * x.r j i) := by
  have hpos :
      Finset.sum (suffixRange j) (fun i => bidding.coeff i j * x.r j i) =
        bidding.coeff j j * x.r j j +
          Finset.sum (strictSuffixRange j) (fun i => bidding.coeff i j * x.r j i) := by
    rw [suffixRange_eq_insert_strictSuffix, Finset.sum_insert]
    simp
  have hneg :
      Finset.sum (suffixRange j)
          (fun i =>
            if h : i < lastIdx n then
              gamma * bidding.coeff i j * x.r j (succIdx i h)
            else
              0) =
        Finset.sum (strictSuffixRange j) (fun i => gamma * predBidCoeff bidding j i * x.r j i) := by
    simpa [predBidCoeff, mul_assoc, mul_left_comm, mul_comm] using!
      sum_suffixRange_succ_eq_sum_strictSuffix j
        (fun i => gamma * predBidCoeff bidding j i * x.r j i)
  have hsplit :
      Finset.sum (suffixRange j) (fun i => x.objectiveTerm gamma bidding i j) =
        Finset.sum (suffixRange j) (fun i => bidding.coeff i j * x.r j i) -
          Finset.sum (suffixRange j)
            (fun i =>
              if h : i < lastIdx n then
                gamma * bidding.coeff i j * x.r j (succIdx i h)
              else
                0) := by
    calc
      Finset.sum (suffixRange j) (fun i => x.objectiveTerm gamma bidding i j) =
          Finset.sum (suffixRange j) (fun i =>
            bidding.coeff i j * x.r j i -
              (if h : i < lastIdx n then
                gamma * bidding.coeff i j * x.r j (succIdx i h)
              else
                0)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases h : i < lastIdx n
            · simp [LinearizedPrimalSolution.objectiveTerm, h]
              ring
            · simp [LinearizedPrimalSolution.objectiveTerm, h]
      _ = Finset.sum (suffixRange j) (fun i => bidding.coeff i j * x.r j i) -
            Finset.sum (suffixRange j)
              (fun i =>
                if h : i < lastIdx n then
                  gamma * bidding.coeff i j * x.r j (succIdx i h)
                else
                  0) := by
            rw [Finset.sum_sub_distrib]
  rw [hsplit, hpos, hneg]
  calc
    bidding.coeff j j * x.r j j + ∑ x_1 ∈ strictSuffixRange j, bidding.coeff x_1 j * x.r j x_1 -
        ∑ x_1 ∈ strictSuffixRange j, gamma * predBidCoeff bidding j x_1 * x.r j x_1 =
      bidding.coeff j j * x.r j j +
        ((∑ x_1 ∈ strictSuffixRange j, bidding.coeff x_1 j * x.r j x_1) -
          ∑ x_1 ∈ strictSuffixRange j, gamma * predBidCoeff bidding j x_1 * x.r j x_1) := by
        ring
    _ = bidding.coeff j j * x.r j j +
        ∑ x_1 ∈ strictSuffixRange j,
          (bidding.coeff x_1 j * x.r j x_1 - gamma * predBidCoeff bidding j x_1 * x.r j x_1) := by
        rw [← Finset.sum_sub_distrib]
    _ = bidding.coeff j j * x.r j j +
        ∑ x_1 ∈ strictSuffixRange j,
          (bidding.coeff x_1 j - gamma * predBidCoeff bidding j x_1) * x.r j x_1 := by
        apply congrArg (fun z => bidding.coeff j j * x.r j j + z)
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring

theorem LinearizedPrimalSolution.objectiveColumn_le_clientAdjustedTerms
    {n : ℕ} [NeZero n] {gamma : ℝ} {bidding : BiddingMatrix n}
    {x : LinearizedPrimalSolution n} {y : DirectDualSolution n}
    (hx : x.Feasible gamma) (hy : y.Feasible gamma bidding) (j : Idx n) :
    Finset.sum (suffixRange j) (fun i => x.objectiveTerm gamma bidding i j) ≤
      x.r j j * (y.toDualSolution.clientCredit j j - y.clientSlack j j) +
        Finset.sum (strictSuffixRange j)
          (fun i =>
            x.r j i *
              (predClientSlack y j i +
                (y.g i j + y.t i j - y.toDualSolution.strictS i j) -
                y.clientSlack i j)) := by
  rcases hx with ⟨_, _, _, _, _, _, _, _, _, _, _, hrNonneg, _⟩
  rcases hy with ⟨_, _, hBase, hStep, _, _, _, _, _, _, _, _ , _⟩
  rw [LinearizedPrimalSolution.objectiveColumn_eq_base_add_strictSuffix gamma bidding x j]
  refine add_le_add ?_ (Finset.sum_le_sum ?_)
  · simpa [DualProgram.bid, mul_comm] using
      mul_le_mul_of_nonneg_right (hBase j) (hrNonneg j j)
  · intro i hi
    have hji : j < i := mem_strictSuffixRange.mp hi
    have hi0 : firstIdx n < i := lt_of_le_of_lt (firstIdx_le j) hji
    have hpredle : j ≤ DirectDualSolution.predIdx i hi0 := by
      change j.1 ≤ (DirectDualSolution.predIdx i hi0).1
      have hji' : j.1 < i.1 := hji
      dsimp [DirectDualSolution.predIdx]
      omega
    have hpredlt : DirectDualSolution.predIdx i hi0 < lastIdx n :=
      lt_of_lt_of_le (DirectDualSolution.predIdx_lt i hi0) (le_lastIdx i)
    have hstepi :=
      hStep (i := DirectDualSolution.predIdx i hi0) (j := j) hpredle hpredlt
    have hstepi' :
        bidding.coeff i j - gamma * predBidCoeff bidding j i ≤
          predClientSlack y j i +
            (y.g i j + y.t i j - y.toDualSolution.strictS i j) -
            y.clientSlack i j := by
      simpa [predBidCoeff_eq_of_strictSuffix bidding hji, predClientSlack_eq_of_strictSuffix y hji,
        DirectDualSolution.succ_predIdx hi0] using! hstepi
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hstepi' (hrNonneg j i)

theorem LinearizedPrimalSolution.sum_suffix_clientSlack_eq_base_add_strictSuffix
    {n : ℕ} [NeZero n] {x : LinearizedPrimalSolution n} {y : DirectDualSolution n}
    (hLast : ∀ j : Idx n, y.clientSlack (lastIdx n) j = 0) (j : Idx n) :
    Finset.sum (suffixRange j)
        (fun i => if i < lastIdx n then x.r j i * y.clientSlack i j else 0) =
      x.r j j * y.clientSlack j j +
        Finset.sum (strictSuffixRange j) (fun i => x.r j i * y.clientSlack i j) := by
  by_cases hj : j < lastIdx n
  · rw [suffixRange_eq_insert_strictSuffix, Finset.sum_insert]
    · simp only [hj, ite_true]
      have hsum :
          ∑ x_1 ∈ strictSuffixRange j,
              (if x_1 < lastIdx n then x.r j x_1 * y.clientSlack x_1 j else 0) =
            ∑ i ∈ strictSuffixRange j, x.r j i * y.clientSlack i j := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hiLast : i < lastIdx n
        · simp only [hiLast, ite_true]
        · have hilast : i = lastIdx n := le_antisymm (le_lastIdx i) (not_lt.mp hiLast)
          subst hilast
          simp [hLast j]
      rw [hsum]
    · simp
  · have hjlast : j = lastIdx n := le_antisymm (le_lastIdx j) (not_lt.mp hj)
    subst hjlast
    have hstrictEmpty : strictSuffixRange (lastIdx n) = ∅ := by
      ext i
      simp [mem_strictSuffixRange]
    rw [suffixRange_eq_insert_strictSuffix, hstrictEmpty, Finset.sum_empty]
    simp [hLast]

theorem LinearizedPrimalSolution.clientSlackTelescope_nonpos
    {n : ℕ} [NeZero n] {gamma : ℝ} {bidding : BiddingMatrix n}
    {x : LinearizedPrimalSolution n} {y : DirectDualSolution n}
    (hx : x.Feasible gamma) (hy : y.Feasible gamma bidding) (j : Idx n) :
    Finset.sum (strictSuffixRange j) (fun i => x.r j i * predClientSlack y j i) ≤
      x.r j j * y.clientSlack j j +
        Finset.sum (strictSuffixRange j) (fun i => x.r j i * y.clientSlack i j) := by
  rcases hx with ⟨_, _, _, hRmono, _, _, _, _, _, _, _, _, _⟩
  rcases hy with ⟨_, _, _, _, hLast, _, _, _, _, _, _, hSlackNonneg, _⟩
  have hshift :
      Finset.sum (strictSuffixRange j) (fun i => x.r j i * predClientSlack y j i) =
        Finset.sum (suffixRange j)
          (fun i => if h : i < lastIdx n then x.r j (succIdx i h) * y.clientSlack i j else 0) := by
    symm
    simpa [predClientSlack_succ y] using
      sum_suffixRange_succ_eq_sum_strictSuffix j (fun i => x.r j i * predClientSlack y j i)
  have hstep :
      Finset.sum (suffixRange j)
          (fun i => if h : i < lastIdx n then x.r j (succIdx i h) * y.clientSlack i j else 0) ≤
        Finset.sum (suffixRange j)
          (fun i => if h : i < lastIdx n then x.r j i * y.clientSlack i j else 0) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    by_cases h : i < lastIdx n
    · have hmono := hRmono (mem_suffixRange.mp hi) h
      have hcs : 0 ≤ y.clientSlack i j := hSlackNonneg (mem_suffixRange.mp hi)
      simp only [dite_eq_ite, h, ite_true]
      exact mul_le_mul_of_nonneg_right hmono hcs
    · simp [h]
  rw [hshift]
  exact le_trans hstep (le_of_eq
    (LinearizedPrimalSolution.sum_suffix_clientSlack_eq_base_add_strictSuffix hLast j))

theorem LinearizedPrimalSolution.predPoolSlack_le_poolSlack
    {n : ℕ} [NeZero n] {gamma : ℝ} {bidding : BiddingMatrix n}
    {x : LinearizedPrimalSolution n} {y : DirectDualSolution n}
    (hx : x.Feasible gamma) (hy : y.Feasible gamma bidding) :
    Finset.sum (strictSuffixRange (firstIdx n)) (fun i => x.m i * predPoolSlack y i) ≤
      Finset.sum (strictSuffixRange (firstIdx n)) (fun i => x.m i * y.poolSlack i) := by
  rcases hx with ⟨_, _, _, _, hMmono, _, _, _, _, _, hmNonneg, _, _⟩
  rcases hy with ⟨_, _, _, _, _, _, hPoolFirst, hPoolLast, _, _, _, _, hPoolSlackNonneg⟩
  have hshift :
      Finset.sum (strictSuffixRange (firstIdx n)) (fun i => x.m i * predPoolSlack y i) =
        Finset.sum (suffixRange (firstIdx n))
          (fun i => if h : i < lastIdx n then x.m (succIdx i h) * y.poolSlack i else 0) := by
    symm
    simpa [predPoolSlack_succ y] using
      sum_suffixRange_succ_eq_sum_strictSuffix (firstIdx n)
        (fun i => x.m i * predPoolSlack y i)
  have hstep :
      Finset.sum (suffixRange (firstIdx n))
          (fun i => if h : i < lastIdx n then x.m (succIdx i h) * y.poolSlack i else 0) ≤
        Finset.sum (suffixRange (firstIdx n))
          (fun i => if h : i < lastIdx n then x.m i * y.poolSlack i else 0) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    by_cases h : i < lastIdx n
    · by_cases hfirst : i = firstIdx n
      · subst hfirst
        simp [h, hPoolFirst]
      · have hi0 : firstIdx n < i := lt_of_le_of_ne (firstIdx_le i) (Ne.symm hfirst)
        have hmmono := hMmono hi0 h
        have hps : 0 ≤ y.poolSlack i := hPoolSlackNonneg i
        simp only [dite_eq_ite, h, ite_true]
        exact mul_le_mul_of_nonneg_right hmmono hps
    · simp [h]
  have hsuffixUniv : suffixRange (firstIdx n) = (Finset.univ : Finset (Idx n)) := by
    ext i
    simp [suffixRange, firstIdx]
  have hcurr :
      Finset.sum (suffixRange (firstIdx n))
          (fun i => if h : i < lastIdx n then x.m i * y.poolSlack i else 0) =
        Finset.sum (strictSuffixRange (firstIdx n)) (fun i => x.m i * y.poolSlack i) := by
    rw [hsuffixUniv]
    let f : Idx n → ℝ := fun i => x.m i * y.poolSlack i
    have hfirstSplit := sum_univ_eq_filter_lt_add_self_add_strictSuffix (f := f) (firstIdx n)
    have hlastSplit := sum_univ_eq_filter_lt_add_self_add_strictSuffix (f := f) (lastIdx n)
    have hcond :
        Finset.sum Finset.univ (fun i => if i < lastIdx n then f i else 0) =
          Finset.sum (Finset.univ.filter fun i : Idx n => i < lastIdx n) f := by
      symm
      exact Finset.sum_filter (s := Finset.univ) (p := fun i : Idx n => i < lastIdx n) f
    have hlastEmpty : strictSuffixRange (lastIdx n) = ∅ := by
      ext i
      simp [mem_strictSuffixRange]
    have hfirstEmpty :
        Finset.univ.filter (fun i : Idx n => i < firstIdx n) = ∅ := by
      ext i
      simp [firstIdx]
    have hfirstZero : f (firstIdx n) = 0 := by
      simp [f, hPoolFirst]
    have hlastZero : f (lastIdx n) = 0 := by
      simp [f, hPoolLast]
    calc
      Finset.sum Finset.univ (fun i => if i < lastIdx n then f i else 0) =
        Finset.sum (Finset.univ.filter fun i : Idx n => i < lastIdx n) f := hcond
      _ = Finset.sum Finset.univ f := by
        simpa [hlastEmpty, hlastZero] using hlastSplit.symm
      _ = Finset.sum (strictSuffixRange (firstIdx n)) f := by
        simpa [hfirstEmpty, hfirstZero] using hfirstSplit
      _ = Finset.sum (strictSuffixRange (firstIdx n)) (fun i => x.m i * y.poolSlack i) := by
        rfl
  rw [hshift]
  exact le_trans hstep (le_of_eq hcurr)

theorem LinearizedPrimalSolution.weightedRowValue_nonneg
    {n : ℕ} [NeZero n] {gamma : ℝ} {bidding : BiddingMatrix n}
    {x : LinearizedPrimalSolution n} {y : DirectDualSolution n}
    (hx : x.Feasible gamma) (hy : y.Feasible gamma bidding) :
    0 ≤ Finset.sum (strictSuffixRange (firstIdx n)) (fun i => x.m i * y.rowValue i) := by
  have hxFeas := hx
  have hyFeas := hy
  rcases hx with ⟨_, _, _, _, _, _, _, _, _, _, hmNonneg, _, _⟩
  rcases hy with ⟨_, _, _, _, _, hPoolStep, _, _, _, _, _, _, _⟩
  let predSum : ℝ :=
    Finset.sum (strictSuffixRange (firstIdx n)) (fun i => x.m i * predPoolSlack y i)
  let rowSum : ℝ :=
    Finset.sum (strictSuffixRange (firstIdx n)) (fun i => x.m i * y.rowValue i)
  let currSum : ℝ :=
    Finset.sum (strictSuffixRange (firstIdx n)) (fun i => x.m i * y.poolSlack i)
  have hsumNonneg : 0 ≤ predSum + rowSum - currSum := by
    have hterm :
        ∀ i ∈ strictSuffixRange (firstIdx n),
          0 ≤ x.m i * predPoolSlack y i + x.m i * y.rowValue i - x.m i * y.poolSlack i := by
      intro i hi
      have hi0 : firstIdx n < i := mem_strictSuffixRange.mp hi
      have hpool := hPoolStep hi0
      have hm : 0 ≤ x.m i := hmNonneg i
      have hpred : predPoolSlack y i = y.poolSlack (DirectDualSolution.predIdx i hi0) := by
        simp [predPoolSlack, hi0]
      rw [hpred]
      nlinarith
    have hsumEq :
        predSum + rowSum - currSum =
          Finset.sum (strictSuffixRange (firstIdx n))
            (fun i =>
              x.m i * predPoolSlack y i + x.m i * y.rowValue i - x.m i * y.poolSlack i) := by
      unfold predSum rowSum currSum
      rw [← Finset.sum_add_distrib]
      rw [← Finset.sum_sub_distrib]
    rw [hsumEq]
    exact Finset.sum_nonneg hterm
  have hpredle : predSum ≤ currSum := by
    exact
      LinearizedPrimalSolution.predPoolSlack_le_poolSlack
        (x := x) (y := y) hxFeas hyFeas
  nlinarith

theorem LinearizedPrimalSolution.objectiveColumn_le_clientTerms
    {n : ℕ} [NeZero n] {gamma : ℝ} {bidding : BiddingMatrix n}
    {x : LinearizedPrimalSolution n} {y : DirectDualSolution n}
    (hx : x.Feasible gamma) (hy : y.Feasible gamma bidding) (j : Idx n) :
    Finset.sum (suffixRange j) (fun i => x.objectiveTerm gamma bidding i j) ≤
      x.r j j * y.toDualSolution.clientCredit j j +
        Finset.sum (strictSuffixRange j)
          (fun i => x.r j i * (y.g i j + y.t i j - y.toDualSolution.strictS i j)) := by
  have hAdjusted := LinearizedPrimalSolution.objectiveColumn_le_clientAdjustedTerms hx hy j
  have hSlack := LinearizedPrimalSolution.clientSlackTelescope_nonpos hx hy j
  have hslack' :
      Finset.sum (strictSuffixRange j) (fun i => x.r j i * predClientSlack y j i) -
          (x.r j j * y.clientSlack j j +
            Finset.sum (strictSuffixRange j) (fun i => x.r j i * y.clientSlack i j)) ≤ 0 := by
    linarith
  let cleanRhs : ℝ :=
    x.r j j * y.toDualSolution.clientCredit j j +
      Finset.sum (strictSuffixRange j)
        (fun i => x.r j i * (y.g i j + y.t i j - y.toDualSolution.strictS i j))
  let adjustedRhs : ℝ :=
    x.r j j * (y.toDualSolution.clientCredit j j - y.clientSlack j j) +
      Finset.sum (strictSuffixRange j)
        (fun i =>
          x.r j i *
            (predClientSlack y j i +
              (y.g i j + y.t i j - y.toDualSolution.strictS i j) -
              y.clientSlack i j))
  have hsumSplit :
      Finset.sum (strictSuffixRange j)
          (fun i =>
            x.r j i *
              (predClientSlack y j i +
                (y.g i j + y.t i j - y.toDualSolution.strictS i j) -
                y.clientSlack i j)) =
        Finset.sum (strictSuffixRange j)
            (fun i => x.r j i * (y.g i j + y.t i j - y.toDualSolution.strictS i j)) +
          Finset.sum (strictSuffixRange j) (fun i => x.r j i * predClientSlack y j i) -
          Finset.sum (strictSuffixRange j) (fun i => x.r j i * y.clientSlack i j) := by
    calc
      Finset.sum (strictSuffixRange j)
          (fun i =>
            x.r j i *
              (predClientSlack y j i +
                (y.g i j + y.t i j - y.toDualSolution.strictS i j) -
                y.clientSlack i j)) =
        Finset.sum (strictSuffixRange j)
          (fun i =>
            x.r j i * (predClientSlack y j i) +
              x.r j i * (y.g i j + y.t i j - y.toDualSolution.strictS i j) -
              x.r j i * y.clientSlack i j) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
      _ =
        Finset.sum (strictSuffixRange j)
          (fun i =>
            x.r j i * predClientSlack y j i +
              x.r j i * (y.g i j + y.t i j - y.toDualSolution.strictS i j)) -
          Finset.sum (strictSuffixRange j) (fun i => x.r j i * y.clientSlack i j) := by
          rw [Finset.sum_sub_distrib]
      _ =
        (Finset.sum (strictSuffixRange j) (fun i => x.r j i * predClientSlack y j i) +
          Finset.sum (strictSuffixRange j)
            (fun i => x.r j i * (y.g i j + y.t i j - y.toDualSolution.strictS i j))) -
          Finset.sum (strictSuffixRange j) (fun i => x.r j i * y.clientSlack i j) := by
          rw [Finset.sum_add_distrib]
      _ =
        Finset.sum (strictSuffixRange j)
            (fun i => x.r j i * (y.g i j + y.t i j - y.toDualSolution.strictS i j)) +
          Finset.sum (strictSuffixRange j) (fun i => x.r j i * predClientSlack y j i) -
          Finset.sum (strictSuffixRange j) (fun i => x.r j i * y.clientSlack i j) := by
          ring
  have hdecomp :
      adjustedRhs = cleanRhs +
        (Finset.sum (strictSuffixRange j) (fun i => x.r j i * predClientSlack y j i) -
          (x.r j j * y.clientSlack j j +
            Finset.sum (strictSuffixRange j) (fun i => x.r j i * y.clientSlack i j))) := by
    unfold adjustedRhs cleanRhs
    rw [hsumSplit]
    ring
  have hAdjustedRhs : adjustedRhs ≤ cleanRhs := by
    rw [hdecomp]
    linarith
  exact le_trans (by simpa [adjustedRhs] using hAdjusted) (by simpa [cleanRhs] using hAdjustedRhs)

theorem LinearizedPrimalSolution.auxLeft_sub_gamma_d_le_aux
    {n : ℕ} [NeZero n] {gamma : ℝ} {x : LinearizedPrimalSolution n}
    (hx : x.Feasible gamma) (i j : Idx n) :
    x.auxLeft i j - gamma * x.d j ≤ x.aux i j := by
  rcases hx with ⟨_, _, _, _, _, hAuxOff, hAuxDiag, _, _, _, _, _, _⟩
  by_cases hij : i ≤ j
  · simp [LinearizedPrimalSolution.auxLeft, hij]
    have h := hAuxDiag hij
    nlinarith
  · have hji : j < i := lt_of_not_ge hij
    simp [LinearizedPrimalSolution.auxLeft, hij]
    have h := hAuxOff hji
    nlinarith

theorem DualSolution.clientCredit_self_eq {n : ℕ} [NeZero n] (x : DualSolution n) (j : Idx n) :
    x.clientCredit j j =
      Finset.sum (strictSuffixRange j) (fun q => x.g j q) + x.g j j + x.t j j := by
  unfold DualSolution.clientCredit
  have hinterval : intervalRange j j = ({j} : Finset (Idx n)) := by
    ext p
    constructor
    · intro hp
      rcases mem_intervalRange.mp hp with ⟨hjp, hpj⟩
      simp [le_antisymm hpj hjp]
    · intro hp
      rcases Finset.mem_singleton.mp hp with rfl
      exact mem_intervalRange.mpr ⟨le_rfl, le_rfl⟩
  rw [hinterval]
  simp [DualSolution.strictS]
  ring

theorem LinearizedPrimalSolution.sum_weightedAuxLeft_mul_g_eq_clientTerms
    {n : ℕ} [NeZero n] (x : LinearizedPrimalSolution n) (y : DirectDualSolution n) :
    Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => x.auxLeft i j * y.g i j)) =
      Finset.sum Finset.univ
        (fun j =>
          x.r j j * (Finset.sum (strictSuffixRange j) (fun q => y.g j q) + y.g j j) +
            Finset.sum (strictSuffixRange j) (fun i => x.r j i * y.g i j)) := by
  have hoffdiag :
      Finset.sum Finset.univ
          (fun i => Finset.sum (strictPrefixRange i) (fun j => x.r j i * y.g i j)) =
        Finset.sum Finset.univ
          (fun j => Finset.sum (strictSuffixRange j) (fun i => x.r j i * y.g i j)) := by
    simpa using
      sum_strictPrefix_eq_sum_strictSuffix (f := fun i j => x.r j i * y.g i j)
  calc
    Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => x.auxLeft i j * y.g i j)) =
      Finset.sum Finset.univ
        (fun i =>
          Finset.sum (strictPrefixRange i) (fun j => x.r j i * y.g i j) +
            x.r i i * y.g i i +
            Finset.sum (strictSuffixRange i) (fun j => x.r i i * y.g i j)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hsplit :=
          sum_univ_eq_filter_lt_add_self_add_strictSuffix
            (f := fun j => x.auxLeft i j * y.g i j) i
        calc
          Finset.sum Finset.univ (fun j => x.auxLeft i j * y.g i j) =
            Finset.sum (strictPrefixRange i) (fun j => x.auxLeft i j * y.g i j) +
              x.auxLeft i i * y.g i i +
              Finset.sum (strictSuffixRange i) (fun j => x.auxLeft i j * y.g i j) := by
              simpa [strictPrefixRange] using hsplit
          _ =
            Finset.sum (strictPrefixRange i) (fun j => x.r j i * y.g i j) +
              x.r i i * y.g i i +
              Finset.sum (strictSuffixRange i) (fun j => x.r i i * y.g i j) := by
              have hprefix :
                  Finset.sum (strictPrefixRange i) (fun j => x.auxLeft i j * y.g i j) =
                    Finset.sum (strictPrefixRange i) (fun j => x.r j i * y.g i j) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                have hji : j < i := mem_strictPrefixRange.mp hj
                simp [LinearizedPrimalSolution.auxLeft, not_le_of_gt hji]
              have hsuffix :
                  Finset.sum (strictSuffixRange i) (fun j => x.auxLeft i j * y.g i j) =
                    Finset.sum (strictSuffixRange i) (fun j => x.r i i * y.g i j) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                have hij : i < j := mem_strictSuffixRange.mp hj
                simp [LinearizedPrimalSolution.auxLeft, le_of_lt hij]
              rw [hprefix, hsuffix]
              simp [LinearizedPrimalSolution.auxLeft]
    _ =
      Finset.sum Finset.univ
        (fun i =>
          x.r i i * (Finset.sum (strictSuffixRange i) (fun j => y.g i j) + y.g i i) +
            Finset.sum (strictPrefixRange i) (fun j => x.r j i * y.g i j)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hsuffix :
            Finset.sum (strictSuffixRange i) (fun j => x.r i i * y.g i j) =
              x.r i i * Finset.sum (strictSuffixRange i) (fun j => y.g i j) := by
          rw [← Finset.mul_sum]
        rw [hsuffix]
        ring
    _ =
      Finset.sum Finset.univ
        (fun i => x.r i i * (Finset.sum (strictSuffixRange i) (fun j => y.g i j) + y.g i i)) +
        Finset.sum Finset.univ
          (fun i => Finset.sum (strictPrefixRange i) (fun j => x.r j i * y.g i j)) := by
        rw [Finset.sum_add_distrib]
    _ =
      Finset.sum Finset.univ
        (fun i => x.r i i * (Finset.sum (strictSuffixRange i) (fun j => y.g i j) + y.g i i)) +
        Finset.sum Finset.univ
          (fun j => Finset.sum (strictSuffixRange j) (fun i => x.r j i * y.g i j)) := by
        rw [hoffdiag]
    _ =
      Finset.sum Finset.univ
        (fun j =>
          x.r j j * (Finset.sum (strictSuffixRange j) (fun q => y.g j q) + y.g j j) +
            Finset.sum (strictSuffixRange j) (fun i => x.r j i * y.g i j)) := by
        rw [← Finset.sum_add_distrib]

theorem LinearizedPrimalSolution.sum_weightedMetric_eq_clientTerms
    {n : ℕ} [NeZero n] (x : LinearizedPrimalSolution n) (y : DirectDualSolution n) :
    Finset.sum Finset.univ
        (fun i => Finset.sum (prefixRange i)
          (fun j => x.r j i * (y.t i j - y.toDualSolution.strictS i j))) =
      Finset.sum Finset.univ
        (fun j =>
          x.r j j * y.t j j +
            Finset.sum (strictSuffixRange j)
              (fun i => x.r j i * (y.t i j - y.toDualSolution.strictS i j))) := by
  calc
    Finset.sum Finset.univ
        (fun i => Finset.sum (prefixRange i)
          (fun j => x.r j i * (y.t i j - y.toDualSolution.strictS i j))) =
      Finset.sum Finset.univ
        (fun j => Finset.sum (suffixRange j)
          (fun i => x.r j i * (y.t i j - y.toDualSolution.strictS i j))) := by
        simpa using
          (sum_prefixRange_eq_sum_suffixRange
            (f := fun i j => x.r j i * (y.t i j - y.toDualSolution.strictS i j)))
    _ =
      Finset.sum Finset.univ
        (fun j =>
          x.r j j * y.t j j +
            Finset.sum (strictSuffixRange j)
              (fun i => x.r j i * (y.t i j - y.toDualSolution.strictS i j))) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [suffixRange_eq_insert_strictSuffix, Finset.sum_insert]
        · simp [DualSolution.strictS]
        · simp

theorem LinearizedPrimalSolution.sum_clientTerms_eq_rowContrib
    {n : ℕ} [NeZero n] (x : LinearizedPrimalSolution n) (y : DirectDualSolution n) :
    Finset.sum Finset.univ
        (fun i =>
          Finset.sum Finset.univ (fun j => x.auxLeft i j * y.g i j) +
            Finset.sum (prefixRange i)
              (fun j => x.r j i * (y.t i j - y.toDualSolution.strictS i j))) =
      Finset.sum Finset.univ
        (fun j =>
          x.r j j * y.toDualSolution.clientCredit j j +
            Finset.sum (strictSuffixRange j)
              (fun i => x.r j i * (y.g i j + y.t i j - y.toDualSolution.strictS i j))) := by
  rw [Finset.sum_add_distrib]
  rw [LinearizedPrimalSolution.sum_weightedAuxLeft_mul_g_eq_clientTerms]
  rw [LinearizedPrimalSolution.sum_weightedMetric_eq_clientTerms]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [DualSolution.clientCredit_self_eq]
  calc
    x.r j j * (Finset.sum (strictSuffixRange j) (fun q => y.g j q) + y.g j j) +
        Finset.sum (strictSuffixRange j) (fun i => x.r j i * y.g i j) +
          (x.r j j * y.t j j +
            Finset.sum (strictSuffixRange j)
              (fun i => x.r j i * (y.t i j - y.toDualSolution.strictS i j))) =
      x.r j j * (Finset.sum (strictSuffixRange j) (fun q => y.g j q) + y.g j j + y.t j j) +
        (Finset.sum (strictSuffixRange j) (fun i => x.r j i * y.g i j) +
          Finset.sum (strictSuffixRange j)
            (fun i => x.r j i * (y.t i j - y.toDualSolution.strictS i j))) := by
        ring
    _ =
      x.r j j * (Finset.sum (strictSuffixRange j) (fun q => y.g j q) + y.g j j + y.t j j) +
        Finset.sum (strictSuffixRange j)
          (fun i => x.r j i * y.g i j + x.r j i * (y.t i j - y.toDualSolution.strictS i j)) := by
        rw [← Finset.sum_add_distrib]
    _ =
      x.r j j * (Finset.sum (strictSuffixRange j) (fun q => y.g j q) + y.g j j + y.t j j) +
        Finset.sum (strictSuffixRange j)
          (fun i => x.r j i * (y.g i j + y.t i j - y.toDualSolution.strictS i j)) := by
        have hsum :
            Finset.sum (strictSuffixRange j)
                (fun i => x.r j i * y.g i j + x.r j i * (y.t i j - y.toDualSolution.strictS i j)) =
              Finset.sum (strictSuffixRange j)
                (fun i => x.r j i * (y.g i j + y.t i j - y.toDualSolution.strictS i j)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        rw [hsum]

theorem LinearizedPrimalSolution.weightedAuxLeft_mul_g_le
    {n : ℕ} [NeZero n] {gamma : ℝ} {bidding : BiddingMatrix n}
    {x : LinearizedPrimalSolution n} {y : DirectDualSolution n}
    (hx : x.Feasible gamma) (hy : y.Feasible gamma bidding) (i : Idx n) :
    Finset.sum Finset.univ (fun j => x.auxLeft i j * y.g i j) ≤
      y.hatG i * Finset.sum Finset.univ (x.aux i) +
        gamma * Finset.sum Finset.univ (fun j => x.d j * y.g i j) := by
  have hxFeas := hx
  rcases hx with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAuxNonneg⟩
  rcases hy with ⟨_, hDom, _, _, _, _, _, _, _, hNonneg, _, _, _⟩
  rcases hNonneg with ⟨_, hGNonneg, _, _⟩
  calc
    Finset.sum Finset.univ (fun j => x.auxLeft i j * y.g i j) ≤
      Finset.sum Finset.univ
        (fun j => x.aux i j * y.hatG i + gamma * (x.d j * y.g i j)) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        have hleft := LinearizedPrimalSolution.auxLeft_sub_gamma_d_le_aux hxFeas i j
        have hg : 0 ≤ y.g i j := hGNonneg i j
        have haux : 0 ≤ x.aux i j := hAuxNonneg i j
        have hdom : y.g i j ≤ y.hatG i := hDom i j
        have hmul :
            x.auxLeft i j * y.g i j ≤ (x.aux i j + gamma * x.d j) * y.g i j := by
          have htmp : x.auxLeft i j ≤ x.aux i j + gamma * x.d j := by
            nlinarith
          exact mul_le_mul_of_nonneg_right htmp hg
        have hauxmul : x.aux i j * y.g i j ≤ x.aux i j * y.hatG i := by
          exact mul_le_mul_of_nonneg_left hdom haux
        calc
          x.auxLeft i j * y.g i j ≤ (x.aux i j + gamma * x.d j) * y.g i j := hmul
          _ = x.aux i j * y.g i j + gamma * (x.d j * y.g i j) := by ring
          _ ≤ x.aux i j * y.hatG i + gamma * (x.d j * y.g i j) := by
            linarith
    _ =
      Finset.sum Finset.univ (fun j => x.aux i j * y.hatG i) +
        gamma * Finset.sum Finset.univ (fun j => x.d j * y.g i j) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ =
      y.hatG i * Finset.sum Finset.univ (x.aux i) +
        gamma * Finset.sum Finset.univ (fun j => x.d j * y.g i j) := by
        have hhat :
            Finset.sum Finset.univ (fun j => x.aux i j * y.hatG i) =
              y.hatG i * Finset.sum Finset.univ (x.aux i) := by
          calc
            Finset.sum Finset.univ (fun j => x.aux i j * y.hatG i) =
              Finset.sum Finset.univ (fun j => y.hatG i * x.aux i j) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                ring
            _ = y.hatG i * Finset.sum Finset.univ (x.aux i) := by
                rw [Finset.mul_sum]
        rw [hhat]

theorem LinearizedPrimalSolution.weightedMetricRow_le
    {n : ℕ} [NeZero n] {gamma : ℝ} {bidding : BiddingMatrix n}
    {x : LinearizedPrimalSolution n} {y : DirectDualSolution n}
    (hx : x.Feasible gamma) (hy : y.Feasible gamma bidding) (i : Idx n) :
    Finset.sum (prefixRange i) (fun j => x.r j i * (y.t i j - y.toDualSolution.strictS i j)) ≤
      Finset.sum (prefixRange i) (fun j => x.d j * (y.t i j + y.toDualSolution.strictS i j)) -
        x.m i * y.rowValue i := by
  rcases hx with ⟨_, hLower, hUpper, _, _, _, _, _, _, hdNonneg, _, _, _⟩
  rcases hy with ⟨_, _, _, _, _, _, _, _, _, hNonneg, ht11, _, _⟩
  rcases hNonneg with ⟨_, _, hSNonneg, hTNonneg⟩
  by_cases hi : firstIdx n < i
  · have hpoint :
        ∀ j ∈ prefixRange i,
          x.r j i * (y.t i j - y.toDualSolution.strictS i j) ≤
            x.d j * (y.t i j + y.toDualSolution.strictS i j) -
              x.m i * (y.toDualSolution.strictS i j - y.t i j) := by
      intro j hj
      have hji : j ≤ i := mem_prefixRange.mp hj
      by_cases hlt : j < i
      · have hlow := hLower hlt
        have hupp := hUpper hji hi
        have ht : 0 ≤ y.t i j := hTNonneg i j
        have hs : 0 ≤ y.s i j := hSNonneg i j
        have hupp' : x.r j i - x.m i - x.d j ≤ 0 := by
          nlinarith
        have hlow' : -x.r j i + x.m i - x.d j ≤ 0 := by
          nlinarith
        simp only [DualSolution.strictS, hlt, ge_iff_le]
        have htmul : (x.r j i - x.m i - x.d j) * y.t i j ≤ 0 := by
          nlinarith
        have hsmul : (-x.r j i + x.m i - x.d j) * y.s i j ≤ 0 := by
          nlinarith
        have hmetric :
            x.r j i * (y.t i j - y.s i j) ≤
              x.d j * (y.t i j + y.s i j) -
                x.m i * (y.s i j - y.t i j) := by
          nlinarith [htmul, hsmul]
        simpa [DualSolution.strictS, hlt] using! hmetric
      · have hEq : j = i := le_antisymm hji (not_lt.mp hlt)
        subst j
        have hupp := hUpper le_rfl hi
        have ht : 0 ≤ y.t i i := hTNonneg i i
        have hupp' : x.r i i - x.m i - x.d i ≤ 0 := by
          nlinarith
        have hmetric :
            x.r i i * (y.t i i - 0) ≤
              x.d i * (y.t i i + 0) - x.m i * (0 - y.t i i) := by
          nlinarith [hupp', ht]
        simpa [DualSolution.strictS] using hmetric
    calc
      Finset.sum (prefixRange i) (fun j => x.r j i * (y.t i j - y.toDualSolution.strictS i j)) ≤
        Finset.sum (prefixRange i)
          (fun j =>
            x.d j * (y.t i j + y.toDualSolution.strictS i j) -
              x.m i * (y.toDualSolution.strictS i j - y.t i j)) := by
          exact Finset.sum_le_sum hpoint
      _ =
        Finset.sum (prefixRange i) (fun j => x.d j * (y.t i j + y.toDualSolution.strictS i j)) -
          x.m i * y.rowValue i := by
          unfold DirectDualSolution.rowValue
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  · have hfirst : i = firstIdx n := le_antisymm (not_lt.mp hi) (firstIdx_le i)
    subst hfirst
    have hprefix : prefixRange (firstIdx n) = ({firstIdx n} : Finset (Idx n)) := by
      ext j
      simp [prefixRange, firstIdx]
    have hrow0 : y.rowValue (firstIdx n) = 0 :=
      DirectDualSolution.rowValue_first_eq_zero ht11
    rw [hprefix, hrow0]
    simp [DualSolution.strictS, ht11]

theorem LinearizedPrimalSolution.rowContribution_le
    {n : ℕ} [NeZero n] {gamma : ℝ} {bidding : BiddingMatrix n}
    {x : LinearizedPrimalSolution n} {y : DirectDualSolution n}
    (hx : x.Feasible gamma) (hy : y.Feasible gamma bidding) (i : Idx n) :
    Finset.sum Finset.univ (fun j => x.auxLeft i j * y.g i j) +
        Finset.sum (prefixRange i) (fun j => x.r j i * (y.t i j - y.toDualSolution.strictS i j)) ≤
      y.hatG i * Finset.sum Finset.univ (x.aux i) +
        gamma * Finset.sum Finset.univ (fun j => x.d j * y.g i j) +
        Finset.sum (prefixRange i) (fun j => x.d j * (y.t i j + y.toDualSolution.strictS i j)) -
          x.m i * y.rowValue i := by
  have hg := LinearizedPrimalSolution.weightedAuxLeft_mul_g_le hx hy i
  have hm := LinearizedPrimalSolution.weightedMetricRow_le hx hy i
  linarith

theorem LinearizedPrimalSolution.weightedAuxRows_le_f
    {n : ℕ} [NeZero n] {gamma : ℝ} {bidding : BiddingMatrix n}
    {x : LinearizedPrimalSolution n} {y : DirectDualSolution n}
    (hx : x.Feasible gamma) (hy : y.Feasible gamma bidding) :
    Finset.sum Finset.univ (fun i => y.hatG i * Finset.sum Finset.univ (x.aux i)) ≤ x.f := by
  rcases hx with ⟨_, _, _, _, _, _, _, hAuxRows, hf, _, _, _, _⟩
  rcases hy with ⟨hBounded, _, _, _, _, _, _, _, _, hNonneg, _, _, _⟩
  rcases hNonneg with ⟨hHatNonneg, _, _, _⟩
  have hBounded' : Finset.sum Finset.univ y.hatG ≤ 1 := by
    simpa [DirectDualSolution.toDualSolution, DualSolution.BoundedHatG, DualSolution.totalHatG]
      using hBounded
  have hpoint :
      ∀ i ∈ (Finset.univ : Finset (Idx n)),
        y.hatG i * Finset.sum Finset.univ (x.aux i) ≤ y.hatG i * x.f := by
    intro i hi
    exact mul_le_mul_of_nonneg_left (hAuxRows i) (hHatNonneg i)
  calc
    Finset.sum Finset.univ (fun i => y.hatG i * Finset.sum Finset.univ (x.aux i)) ≤
      Finset.sum Finset.univ (fun i => y.hatG i * x.f) := by
        exact Finset.sum_le_sum hpoint
    _ = (Finset.sum Finset.univ y.hatG) * x.f := by
      calc
        Finset.sum Finset.univ (fun i => y.hatG i * x.f) =
          Finset.sum Finset.univ (fun i => x.f * y.hatG i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
        _ = x.f * Finset.sum Finset.univ y.hatG := by
          rw [Finset.mul_sum]
        _ = (Finset.sum Finset.univ y.hatG) * x.f := by
          ring
    _ ≤ 1 * x.f := by
      exact mul_le_mul_of_nonneg_right hBounded' hf
    _ = x.f := by ring

theorem LinearizedPrimalSolution.weightedValueTerms_eq_columnValues
    {n : ℕ} [NeZero n] {gamma : ℝ} {bidding : BiddingMatrix n}
    (x : LinearizedPrimalSolution n) (y : DirectDualSolution n) :
    gamma *
        Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => x.d j * y.g i j)) +
        Finset.sum Finset.univ
          (fun i =>
            Finset.sum
              (prefixRange i)
              (fun j => x.d j * (y.t i j + y.toDualSolution.strictS i j))) =
      Finset.sum Finset.univ
        (fun j =>
          x.d j *
            y.toDualSolution.columnValue
              ({ Mcoeff := gamma, bidding := bidding } : DualProgram n) j) := by
  have hg :
      Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => x.d j * y.g i j)) =
        Finset.sum Finset.univ (fun j => x.d j * Finset.sum Finset.univ (fun i => y.g i j)) := by
    calc
      Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => x.d j * y.g i j)) =
        Finset.sum Finset.univ (fun j => Finset.sum Finset.univ (fun i => x.d j * y.g i j)) := by
          rw [Finset.sum_comm]
      _ = Finset.sum Finset.univ (fun j => x.d j * Finset.sum Finset.univ (fun i => y.g i j)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [← Finset.mul_sum]
  have ht :
      Finset.sum Finset.univ (fun i => Finset.sum (prefixRange i) (fun j => x.d j * y.t i j)) =
        Finset.sum Finset.univ
          (fun j => x.d j * Finset.sum (suffixRange j) (fun i => y.t i j)) := by
    calc
      Finset.sum Finset.univ (fun i => Finset.sum (prefixRange i) (fun j => x.d j * y.t i j)) =
        Finset.sum Finset.univ
          (fun j => Finset.sum (suffixRange j) (fun i => x.d j * y.t i j)) := by
          simpa using
            (sum_prefixRange_eq_sum_suffixRange (f := fun i j => x.d j * y.t i j))
      _ = Finset.sum Finset.univ
            (fun j => x.d j * Finset.sum (suffixRange j) (fun i => y.t i j)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [← Finset.mul_sum]
  have hs :
      Finset.sum Finset.univ
          (fun i => Finset.sum (prefixRange i) (fun j => x.d j * y.toDualSolution.strictS i j)) =
        Finset.sum Finset.univ
          (fun j => x.d j * Finset.sum (strictSuffixRange j) (fun i => y.s i j)) := by
    calc
      Finset.sum Finset.univ
          (fun i => Finset.sum (prefixRange i) (fun j => x.d j * y.toDualSolution.strictS i j)) =
        Finset.sum Finset.univ
          (fun j =>
            Finset.sum (suffixRange j) (fun i => x.d j * y.toDualSolution.strictS i j)) := by
          simpa using
            (sum_prefixRange_eq_sum_suffixRange
              (f := fun i j => x.d j * y.toDualSolution.strictS i j))
      _ = Finset.sum Finset.univ
          (fun j => x.d j * Finset.sum (strictSuffixRange j) (fun i => y.s i j)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hsuffix :
              Finset.sum (strictSuffixRange j) (fun i => x.d j * y.toDualSolution.strictS i j) =
                x.d j * Finset.sum (strictSuffixRange j) (fun i => y.s i j) := by
            calc
              Finset.sum (strictSuffixRange j) (fun i => x.d j * y.toDualSolution.strictS i j) =
                x.d j *
                  Finset.sum (strictSuffixRange j) (fun i => y.toDualSolution.strictS i j) := by
                  rw [← Finset.mul_sum]
              _ = x.d j * Finset.sum (strictSuffixRange j) (fun i => y.s i j) := by
                  congr 1
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  have hij : j < i := mem_strictSuffixRange.mp hi
                  simp [DirectDualSolution.toDualSolution, DualSolution.strictS, hij]
          have hstrict :
              Finset.sum (strictSuffixRange j)
                  (fun i => if j < i then x.d j * y.s i j else 0) =
                x.d j * Finset.sum (strictSuffixRange j) (fun i => y.s i j) := by
            calc
              Finset.sum (strictSuffixRange j)
                  (fun i => if j < i then x.d j * y.s i j else 0) =
                Finset.sum (strictSuffixRange j) (fun i => x.d j * y.s i j) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  have hij : j < i := mem_strictSuffixRange.mp hi
                  simp [hij]
              _ = x.d j * Finset.sum (strictSuffixRange j) (fun i => y.s i j) := by
                  rw [← Finset.mul_sum]
          calc
            Finset.sum (suffixRange j) (fun i => x.d j * y.toDualSolution.strictS i j) =
              x.d j * y.toDualSolution.strictS j j +
                Finset.sum
                  (strictSuffixRange j)
                  (fun i => x.d j * y.toDualSolution.strictS i j) := by
                rw [suffixRange_eq_insert_strictSuffix, Finset.sum_insert]
                · simp
            _ = x.d j * Finset.sum (strictSuffixRange j) (fun i => y.s i j) := by
                simp [DirectDualSolution.toDualSolution, DualSolution.strictS, hstrict]
  calc
    gamma *
        Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => x.d j * y.g i j)) +
        Finset.sum Finset.univ
          (fun i =>
            Finset.sum
              (prefixRange i)
              (fun j => x.d j * (y.t i j + y.toDualSolution.strictS i j))) =
      gamma * Finset.sum Finset.univ (fun j => x.d j * Finset.sum Finset.univ (fun i => y.g i j)) +
        (Finset.sum Finset.univ (fun i => Finset.sum (prefixRange i) (fun j => x.d j * y.t i j)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (prefixRange i) (fun j => x.d j * y.toDualSolution.strictS i j))) := by
        rw [hg]
        congr 1
        calc
          Finset.sum Finset.univ
              (fun i =>
                Finset.sum
                  (prefixRange i)
                  (fun j => x.d j * (y.t i j + y.toDualSolution.strictS i j))) =
            Finset.sum Finset.univ
              (fun i =>
                Finset.sum (prefixRange i)
                  (fun j => x.d j * y.t i j + x.d j * y.toDualSolution.strictS i j)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
          _ =
            Finset.sum Finset.univ
              (fun i =>
                Finset.sum (prefixRange i) (fun j => x.d j * y.t i j) +
                  Finset.sum (prefixRange i) (fun j => x.d j * y.toDualSolution.strictS i j)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [Finset.sum_add_distrib]
          _ =
            Finset.sum Finset.univ
              (fun i => Finset.sum (prefixRange i) (fun j => x.d j * y.t i j)) +
              Finset.sum Finset.univ
                (fun i =>
                  Finset.sum (prefixRange i) (fun j => x.d j * y.toDualSolution.strictS i j)) := by
              rw [Finset.sum_add_distrib]
    _ =
      gamma * Finset.sum Finset.univ (fun j => x.d j * Finset.sum Finset.univ (fun i => y.g i j)) +
        Finset.sum Finset.univ (fun j => x.d j * Finset.sum (suffixRange j) (fun i => y.t i j)) +
        Finset.sum Finset.univ
          (fun j => x.d j * Finset.sum (strictSuffixRange j) (fun i => y.s i j)) := by
        rw [ht, hs]
        ring
    _ =
      Finset.sum Finset.univ
        (fun j =>
          gamma * (x.d j * Finset.sum Finset.univ (fun i => y.g i j)) +
            x.d j * Finset.sum (suffixRange j) (fun i => y.t i j) +
            x.d j * Finset.sum (strictSuffixRange j) (fun i => y.s i j)) := by
        let a : Idx n → ℝ :=
          fun j => gamma * (x.d j * Finset.sum Finset.univ (fun i => y.g i j))
        let b : Idx n → ℝ :=
          fun j => x.d j * Finset.sum (suffixRange j) (fun i => y.t i j)
        let c : Idx n → ℝ :=
          fun j => x.d j * Finset.sum (strictSuffixRange j) (fun i => y.s i j)
        have ha :
            gamma *
                Finset.sum Finset.univ
                  (fun j => x.d j * Finset.sum Finset.univ (fun i => y.g i j)) =
            Finset.sum Finset.univ a := by
          simp only [a]
          rw [← Finset.mul_sum]
        have hab : Finset.sum Finset.univ a + Finset.sum Finset.univ b =
            Finset.sum Finset.univ (fun j => a j + b j) := by
          rw [← Finset.sum_add_distrib]
        calc
          gamma *
              Finset.sum Finset.univ
                (fun j => x.d j * Finset.sum Finset.univ (fun i => y.g i j)) +
              Finset.sum Finset.univ
                (fun j => x.d j * Finset.sum (suffixRange j) (fun i => y.t i j)) +
              Finset.sum Finset.univ
                (fun j => x.d j * Finset.sum (strictSuffixRange j) (fun i => y.s i j)) =
            (Finset.sum Finset.univ a + Finset.sum Finset.univ b) + Finset.sum Finset.univ c := by
              rw [ha]
          _ =
            Finset.sum Finset.univ (fun j => a j + b j) + Finset.sum Finset.univ c := by
              rw [hab]
          _ = Finset.sum Finset.univ (fun j => (a j + b j) + c j) := by
              rw [← Finset.sum_add_distrib]
          _ =
            Finset.sum Finset.univ
              (fun j =>
                gamma * (x.d j * Finset.sum Finset.univ (fun i => y.g i j)) +
                  x.d j * Finset.sum (suffixRange j) (fun i => y.t i j) +
                  x.d j * Finset.sum (strictSuffixRange j) (fun i => y.s i j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simp [a, b, c]
    _ =
      Finset.sum Finset.univ
        (fun j =>
          x.d j *
            (gamma * Finset.sum Finset.univ (fun i => y.g i j) +
              Finset.sum (strictSuffixRange j) (fun i => y.s i j) +
              Finset.sum (suffixRange j) (fun i => y.t i j))) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
    _ =
      Finset.sum Finset.univ
        (fun j =>
          x.d j *
            y.toDualSolution.columnValue
              ({ Mcoeff := gamma, bidding := bidding } : DualProgram n) j) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [DirectDualSolution.toDualSolution, DualSolution.columnValue]

theorem DirectDualSolution.rho_nonneg_of_feasible
    {n : ℕ} [NeZero n] {gamma : ℝ} {bidding : BiddingMatrix n}
    {y : DirectDualSolution n} (hy : y.Feasible gamma bidding) (hγ : 0 ≤ gamma) :
    0 ≤ y.rho := by
  rcases hy with ⟨_, _, _, _, _, _, _, _, hValue, hNonneg, _, _, _⟩
  rcases hNonneg with ⟨_, hGNonneg, hSNonneg, hTNonneg⟩
  have hcol := hValue (firstIdx n)
  let P : DualProgram n := { Mcoeff := gamma, bidding := bidding }
  have hgNonneg :
      0 ≤ gamma * Finset.sum Finset.univ (fun i => y.g i (firstIdx n)) := by
    exact mul_nonneg hγ (Finset.sum_nonneg fun i hi => hGNonneg i (firstIdx n))
  have hsNonneg :
      0 ≤ Finset.sum (strictSuffixRange (firstIdx n)) (fun i => y.s i (firstIdx n)) := by
    exact Finset.sum_nonneg fun i hi => hSNonneg i (firstIdx n)
  have htNonneg :
      0 ≤ Finset.sum (suffixRange (firstIdx n)) (fun i => y.t i (firstIdx n)) := by
    exact Finset.sum_nonneg fun i hi => hTNonneg i (firstIdx n)
  have hcolNonnegBase :
      0 ≤ gamma * Finset.sum Finset.univ (fun i => y.g i (firstIdx n)) +
        Finset.sum (strictSuffixRange (firstIdx n)) (fun i => y.s i (firstIdx n)) +
        Finset.sum (suffixRange (firstIdx n)) (fun i => y.t i (firstIdx n)) := by
    exact add_nonneg (add_nonneg hgNonneg hsNonneg) htNonneg
  have hcolNonneg : 0 ≤ y.toDualSolution.columnValue P (firstIdx n) := by
    simpa [P, DualSolution.columnValue, DirectDualSolution.toDualSolution] using hcolNonnegBase
  have hcol' : y.rho ≥ y.toDualSolution.columnValue P (firstIdx n) := by
    simpa [P, DirectDualSolution.toDualSolution] using hcol
  exact le_trans hcolNonneg hcol'

theorem LinearizedPrimalSolution.weightedColumnValues_le_rho
    {n : ℕ} [NeZero n] {gamma : ℝ} {bidding : BiddingMatrix n}
    {x : LinearizedPrimalSolution n} {y : DirectDualSolution n}
    (hx : x.Feasible gamma) (hy : y.Feasible gamma bidding) (hγ : 0 ≤ gamma) :
    Finset.sum Finset.univ
        (fun j =>
          x.d j *
            y.toDualSolution.columnValue
              ({ Mcoeff := gamma, bidding := bidding } : DualProgram n) j) ≤
      y.rho := by
  have hyFeas := hy
  rcases hx with ⟨hNorm, _, _, _, _, _, _, _, _, hdNonneg, _, _, _⟩
  rcases hy with ⟨_, _, _, _, _, _, _, _, hValue, _, _, _, _⟩
  have hρnonneg := DirectDualSolution.rho_nonneg_of_feasible (y := y) hyFeas hγ
  have hpoint :
      ∀ j ∈ (Finset.univ : Finset (Idx n)),
        x.d j *
            y.toDualSolution.columnValue
              ({ Mcoeff := gamma, bidding := bidding } : DualProgram n) j ≤
          x.d j * y.rho := by
    intro j hj
    exact mul_le_mul_of_nonneg_left (hValue j) (hdNonneg j)
  calc
    Finset.sum Finset.univ
        (fun j =>
          x.d j *
            y.toDualSolution.columnValue
              ({ Mcoeff := gamma, bidding := bidding } : DualProgram n) j) ≤
      Finset.sum Finset.univ (fun j => x.d j * y.rho) := by
        exact Finset.sum_le_sum hpoint
    _ = (Finset.sum Finset.univ x.d) * y.rho := by
      rw [← Finset.sum_mul]
    _ ≤ 1 * y.rho := by
      exact mul_le_mul_of_nonneg_right hNorm hρnonneg
    _ = y.rho := by ring

theorem LinearizedPrimalSolution.objective_le_rho_of_directDual
    {n : ℕ} [NeZero n] {gamma : ℝ} {bidding : BiddingMatrix n}
    {x : LinearizedPrimalSolution n} {y : DirectDualSolution n}
    (hx : x.Feasible gamma) (hy : y.Feasible gamma bidding)
    (hγ : 0 ≤ gamma) :
    x.objective gamma bidding ≤ y.rho := by
  let clientTerms : ℝ :=
    Finset.sum Finset.univ
      (fun j =>
        x.r j j * y.toDualSolution.clientCredit j j +
          Finset.sum (strictSuffixRange j)
            (fun i => x.r j i * (y.g i j + y.t i j - y.toDualSolution.strictS i j)))
  let rowTerms : ℝ :=
    Finset.sum Finset.univ
      (fun i =>
        y.hatG i * Finset.sum Finset.univ (x.aux i) +
          gamma * Finset.sum Finset.univ (fun j => x.d j * y.g i j) +
          Finset.sum (prefixRange i) (fun j => x.d j * (y.t i j + y.toDualSolution.strictS i j)) -
            x.m i * y.rowValue i)
  let auxTerms : ℝ :=
    Finset.sum Finset.univ (fun i => y.hatG i * Finset.sum Finset.univ (x.aux i))
  let valueTerms : ℝ :=
    gamma * Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => x.d j * y.g i j)) +
      Finset.sum Finset.univ
        (fun i =>
          Finset.sum (prefixRange i) (fun j => x.d j * (y.t i j + y.toDualSolution.strictS i j)))
  let rowPenalty : ℝ :=
    Finset.sum Finset.univ (fun i => x.m i * y.rowValue i)
  have hobjCols :
      Finset.sum Finset.univ
          (fun j => Finset.sum (suffixRange j) (fun i => x.objectiveTerm gamma bidding i j)) ≤
        clientTerms := by
    unfold clientTerms
    exact Finset.sum_le_sum fun j hj =>
      LinearizedPrimalSolution.objectiveColumn_le_clientTerms hx hy j
  have hclientEq : clientTerms =
      Finset.sum Finset.univ
        (fun i =>
          Finset.sum Finset.univ (fun j => x.auxLeft i j * y.g i j) +
            Finset.sum (prefixRange i)
              (fun j => x.r j i * (y.t i j - y.toDualSolution.strictS i j))) := by
    unfold clientTerms
    simpa using (LinearizedPrimalSolution.sum_clientTerms_eq_rowContrib x y).symm
  have hrowLe : clientTerms ≤ rowTerms := by
    rw [hclientEq]
    unfold rowTerms
    exact Finset.sum_le_sum fun i hi =>
      LinearizedPrimalSolution.rowContribution_le hx hy i
  have hrowDecomp : rowTerms = auxTerms + valueTerms - rowPenalty := by
    unfold rowTerms auxTerms valueTerms rowPenalty
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    ring
  have hauxLe : auxTerms ≤ x.f := by
    unfold auxTerms
    exact LinearizedPrimalSolution.weightedAuxRows_le_f hx hy
  have hvalueEq :
      valueTerms =
        Finset.sum Finset.univ
          (fun j =>
            x.d j *
              y.toDualSolution.columnValue
                ({ Mcoeff := gamma, bidding := bidding } : DualProgram n) j) := by
    unfold valueTerms
    exact LinearizedPrimalSolution.weightedValueTerms_eq_columnValues x y
  have hvalueLe : valueTerms ≤ y.rho := by
    rw [hvalueEq]
    exact LinearizedPrimalSolution.weightedColumnValues_le_rho hx hy hγ
  have hpenaltyNonneg : 0 ≤ rowPenalty := by
    have ht11 : y.t (firstIdx n) (firstIdx n) = 0 := by
      rcases hy with ⟨_, _, _, _, _, _, _, _, _, _, ht11, _, _⟩
      exact ht11
    unfold rowPenalty
    have hsum :
        Finset.sum Finset.univ (fun i => x.m i * y.rowValue i) =
          Finset.sum (strictSuffixRange (firstIdx n)) (fun i => x.m i * y.rowValue i) := by
      let f : Idx n → ℝ := fun i => x.m i * y.rowValue i
      have hsplit := sum_univ_eq_filter_lt_add_self_add_strictSuffix (f := f) (firstIdx n)
      have hfirstEmpty :
          Finset.univ.filter (fun i : Idx n => i < firstIdx n) = ∅ := by
        ext i
        simp [firstIdx]
      have hfirstZero : f (firstIdx n) = 0 := by
        simp [f, DirectDualSolution.rowValue_first_eq_zero ht11]
      simpa [f, hfirstEmpty, hfirstZero] using hsplit
    rw [hsum]
    exact LinearizedPrimalSolution.weightedRowValue_nonneg hx hy
  unfold LinearizedPrimalSolution.objective
  have hmain :
      (Finset.sum Finset.univ
          (fun j => Finset.sum (suffixRange j) (fun i => x.objectiveTerm gamma bidding i j))) -
        x.f ≤
        rowTerms - x.f := by
    exact sub_le_sub_right (le_trans hobjCols hrowLe) x.f
  rw [hrowDecomp] at hmain
  have hauxSub : auxTerms - x.f ≤ 0 := by
    linarith
  have hvaluePenalty : valueTerms - rowPenalty ≤ y.rho := by
    linarith
  have hrowBound : auxTerms + valueTerms - rowPenalty - x.f ≤ y.rho := by
    linarith
  exact le_trans hmain hrowBound

theorem DirectDualSolution.ofDualSolution_feasible {n : ℕ} [NeZero n]
    {gamma : ℝ} {bidding : BiddingMatrix n} {x : DualSolution n}
    (hx : x.Feasible ({ Mcoeff := gamma, bidding := bidding } : DualProgram n)) :
    (DirectDualSolution.ofDualSolution gamma bidding x).Feasible gamma bidding := by
  let P : DualProgram n := { Mcoeff := gamma, bidding := bidding }
  have hfeas := hx
  rcases hx with ⟨hBounded, hDom, hClient, hPool, hValue, hNonneg⟩
  refine ⟨hBounded, hDom, ?_, ?_, ?_, ?_, ?_, ?_, hValue, hNonneg, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j < lastIdx n
    · change P.bid j j ≤ x.clientCredit j j - clientSlackOfDual gamma P x j j
      have hempty : halfOpenIntervalRange j j = ∅ := by
        ext p
        simp [mem_halfOpenIntervalRange]
      simp [clientSlackOfDual, hj, hempty]
    · have hjlast : j = lastIdx n := le_antisymm (le_lastIdx j) (not_lt.mp hj)
      subst hjlast
      change P.bid (lastIdx n) (lastIdx n) ≤
        x.clientCredit (lastIdx n) (lastIdx n) - clientSlackOfDual gamma P x (lastIdx n) (lastIdx n)
      simp [clientSlackOfDual]
      have hlastClient := hClient (j := lastIdx n) (i := lastIdx n) le_rfl
      have hhalfEmpty : halfOpenIntervalRange (lastIdx n) (lastIdx n) = ∅ := by
        ext p
        simp [mem_halfOpenIntervalRange]
      have hempty :
          (∑ p ∈ halfOpenIntervalRange (lastIdx n) (lastIdx n), P.bid p (lastIdx n)) = 0 := by
        simp [hhalfEmpty]
      rw [hempty] at hlastClient
      simpa [DualProgram.Mcoeffmone] using hlastClient
  · intro i j hji h
    have hcc := clientCredit_succ_eq x hji h
    have hset := halfOpenIntervalRange_succ_eq_insert hji h
    have hnot : i ∉ halfOpenIntervalRange j i := by
      simp [mem_halfOpenIntervalRange]
    change clientSlackOfDual gamma P x i j +
        (x.g (succIdx i h) j + x.t (succIdx i h) j - x.strictS (succIdx i h) j) -
        clientSlackOfDual gamma P x (succIdx i h) j ≥
      P.bid (succIdx i h) j - gamma * P.bid i j
    by_cases hsucc : succIdx i h < lastIdx n
    · simp only [clientSlackOfDual, ge_iff_le, tsub_le_iff_right]
      rw [hset, Finset.sum_insert hnot]
      simp [h, hsucc, hcc]
      ring_nf
      exact le_rfl
    · simp only [clientSlackOfDual, ge_iff_le, tsub_le_iff_right]
      have hsuccClient : x.clientCredit (succIdx i h) j ≥
          P.bid (succIdx i h) j -
            (gamma - 1) *
              Finset.sum (halfOpenIntervalRange j (succIdx i h)) (fun p => P.bid p j) :=
        hClient
          (j := j) (i := succIdx i h)
          (le_trans hji (le_of_lt (lt_succIdx i h)))
      rw [hset, Finset.sum_insert hnot] at hsuccClient
      simp [h, hsucc] at hsuccClient ⊢
      nlinarith
  · intro j
    simp [DirectDualSolution.ofDualSolution, clientSlackOfDual]
  · intro i hi
    by_cases hilast : i < lastIdx n
    · have hpredlast : DirectDualSolution.predIdx i hi < lastIdx n :=
        lt_of_lt_of_le (DirectDualSolution.predIdx_lt i hi) (le_of_lt hilast)
      change poolSlackOfDual x (DirectDualSolution.predIdx i hi) +
          Finset.sum (prefixRange i) (fun j => x.strictS i j - x.t i j) -
          poolSlackOfDual x i ≥ 0
      have hstep := poolCredit_step_eq x hi
      have hstep' : x.poolCredit i =
          x.poolCredit (DirectDualSolution.predIdx i hi) +
            (Finset.sum (prefixRange i) (fun j => x.strictS i j) -
              Finset.sum (prefixRange i) (fun j => x.t i j)) := by
        simpa [Finset.sum_sub_distrib] using hstep
      simp [poolSlackOfDual, hilast, hpredlast]
      nlinarith
    · have hlast : i = lastIdx n := le_antisymm (le_lastIdx i) (not_lt.mp hilast)
      subst hlast
      change poolSlackOfDual x (DirectDualSolution.predIdx (lastIdx n) hi) +
          Finset.sum
            (prefixRange (lastIdx n))
            (fun j => x.strictS (lastIdx n) j - x.t (lastIdx n) j) -
          poolSlackOfDual x (lastIdx n) ≥ 0
      simp [poolSlackOfDual]
      have hstep := poolCredit_step_eq x hi
      have hstep' : x.poolCredit (lastIdx n) =
          x.poolCredit (DirectDualSolution.predIdx (lastIdx n) hi) +
            (Finset.sum (prefixRange (lastIdx n)) (fun j => x.strictS (lastIdx n) j) -
              Finset.sum (prefixRange (lastIdx n)) (fun j => x.t (lastIdx n) j)) := by
        simpa [Finset.sum_sub_distrib] using hstep
      have hpoolLast := hPool (lastIdx n)
      have hpredlast : DirectDualSolution.predIdx (lastIdx n) hi < lastIdx n :=
        DirectDualSolution.predIdx_lt (lastIdx n) hi
      simp [hpredlast]
      nlinarith
  · unfold DirectDualSolution.ofDualSolution poolSlackOfDual
    have ht11 := t_first_first_eq_zero_of_feasible hfeas
    have hfirstPool : x.poolCredit (firstIdx n) = -x.t (firstIdx n) (firstIdx n) := by
      have hprefix : prefixRange (firstIdx n) = ({firstIdx n} : Finset (Idx n)) := by
        ext j
        simp [prefixRange, firstIdx]
      simp [DualSolution.poolCredit, DualSolution.strictS, hprefix]
    simp [hfirstPool, ht11]
  · simp [DirectDualSolution.ofDualSolution, poolSlackOfDual]
  · exact t_first_first_eq_zero_of_feasible hfeas
  · intro i j hji
    by_cases hi : i < lastIdx n
    · have h := hClient (j := j) (i := i) hji
      simp [DualProgram.Mcoeffmone] at h
      change 0 ≤ clientSlackOfDual gamma P x i j
      simp [clientSlackOfDual, hi]
      nlinarith
    · have hlast : i = lastIdx n := le_antisymm (le_lastIdx i) (not_lt.mp hi)
      subst hlast
      change 0 ≤ clientSlackOfDual gamma P x (lastIdx n) j
      simp [clientSlackOfDual]
  · intro i
    by_cases hi : i < lastIdx n
    · simpa [DirectDualSolution.ofDualSolution, poolSlackOfDual, hi] using hPool i
    · simp [DirectDualSolution.ofDualSolution, poolSlackOfDual, hi]

theorem LinearizedPrimalSolution.objective_le_rho_of_dual
    {n : ℕ} [NeZero n] {gamma : ℝ} {bidding : BiddingMatrix n}
    {x : LinearizedPrimalSolution n} {y : DualSolution n}
    (hx : x.Feasible gamma)
    (hy : y.Feasible ({ Mcoeff := gamma, bidding := bidding } : DualProgram n))
    (hγ : 0 ≤ gamma) :
    x.objective gamma bidding ≤ y.rho := by
  have hyDirect :
      (DirectDualSolution.ofDualSolution gamma bidding y).Feasible gamma bidding :=
    DirectDualSolution.ofDualSolution_feasible (gamma := gamma) (bidding := bidding) hy
  simpa [DirectDualSolution.ofDualSolution] using
    (LinearizedPrimalSolution.objective_le_rho_of_directDual
      (x := x) (y := DirectDualSolution.ofDualSolution gamma bidding y) hx hyDirect hγ)

/--
The direct dual with explicit slack variables is the clean LP dual of
`LinearizedPrimalSolution.Feasible`.
-/
def StrictSDualBridgeNote : Prop := True

/--
The current formal dual is the telescoped form of the direct dual above: the slack variables are
eliminated by summing the client and pool constraints over time.
-/
def DummyFirstDiagonalTNote : Prop := True

theorem bidValue_add_dist_le_self_of_one_le_gamma
    {gamma alpha dist : ℝ}
    (hγ : 1 ≤ gamma) (hdist : 0 ≤ dist) (hdist_le : dist ≤ alpha) :
    OriginalPrimalSolution.bidValue gamma alpha dist + dist ≤ alpha := by
  unfold OriginalPrimalSolution.bidValue
  by_cases hmain : 0 ≤ alpha - gamma * dist
  · rw [max_eq_left hmain]
    nlinarith
  · rw [max_eq_right (le_of_not_ge hmain)]
    linarith

namespace OriginalPrimalSolution

variable {n : ℕ} [NeZero n]

/-- The bidding pattern extracted from an original FRP solution by activating each nonterminal
entry exactly when the corresponding one-step bid is positive, and forcing the final row to `1`.
-/
def objectiveBidding (gamma : ℝ) (x : OriginalPrimalSolution n) : BiddingMatrix n where
  toFun i j :=
    if hji : j ≤ i then
      if hi : i < lastIdx n then
        decide (0 ≤ x.r j (TimeIdx.ofIdx i) - gamma * x.r j (TimeIdx.succ i))
      else
        true
    else
      false
  upper_zero := by
    intro i j hij
    simp [not_le_of_gt hij]

@[simp] theorem objectiveBidding_coeff_last
    (gamma : ℝ) (x : OriginalPrimalSolution n) (j : Idx n) :
    (x.objectiveBidding gamma).coeff (lastIdx n) j = 1 := by
  simp [OriginalPrimalSolution.objectiveBidding, BiddingMatrix.coeff]

theorem objectiveTerm_eq_bidValue_of_objectiveBidding
    {gamma : ℝ} (x : OriginalPrimalSolution n) {j i : Idx n}
    (hji : j ≤ i) (hi : i < lastIdx n) :
    (x.toLinearized gamma).objectiveTerm gamma (x.objectiveBidding gamma) i j =
      bidValue gamma (x.r j (TimeIdx.ofIdx i)) (x.r j (TimeIdx.succ i)) := by
  have hsucc : TimeIdx.ofIdx (succIdx i hi) = TimeIdx.succ i := by
    apply Fin.ext
    simp [TimeIdx.ofIdx, TimeIdx.succ, succIdx_val]
  by_cases hterm : gamma * x.r j (TimeIdx.succ i) ≤ x.r j (TimeIdx.ofIdx i)
  · have hterm' : 0 ≤ x.r j (TimeIdx.ofIdx i) - gamma * x.r j (TimeIdx.succ i) := by
      linarith
    simp [LinearizedPrimalSolution.objectiveTerm, OriginalPrimalSolution.objectiveBidding,
      BiddingMatrix.coeff, hji, hi, hterm, hterm', OriginalPrimalSolution.bidValue, hsucc]
  · have hterm' : x.r j (TimeIdx.ofIdx i) - gamma * x.r j (TimeIdx.succ i) ≤ 0 := by
      linarith
    simp [LinearizedPrimalSolution.objectiveTerm, OriginalPrimalSolution.objectiveBidding,
      BiddingMatrix.coeff, hji, hi, hterm, OriginalPrimalSolution.bidValue,
      max_eq_right hterm', hsucc]

theorem last_objectiveTerm_ge_bidValue_add_terminal
    {gamma : ℝ} {x : OriginalPrimalSolution n}
    (hx : x.Feasible gamma) (hγ : 1 ≤ gamma) (j : Idx n) :
    bidValue gamma (x.r j (TimeIdx.ofIdx (lastIdx n))) (x.r j (TimeIdx.last n)) +
        x.r j (TimeIdx.last n) ≤
      (x.toLinearized gamma).objectiveTerm gamma (x.objectiveBidding gamma) (lastIdx n) j := by
  rcases hx with ⟨_, hMono, _, _, _, _, _, hrNonneg⟩
  have hterm_nonneg : 0 ≤ x.r j (TimeIdx.last n) := hrNonneg j (TimeIdx.last n)
  have hsuccLast : TimeIdx.succ (lastIdx n) = TimeIdx.last n := by
    exact (TimeIdx.succ_eq_last (i := lastIdx n)).2 rfl
  have hterm_le :
      x.r j (TimeIdx.last n) ≤ x.r j (TimeIdx.ofIdx (lastIdx n)) := by
    simpa [hsuccLast] using hMono (show j ≤ lastIdx n by exact le_lastIdx j)
  have hbound :=
    bidValue_add_dist_le_self_of_one_le_gamma hγ hterm_nonneg hterm_le
  have hlast : ¬ lastIdx n < lastIdx n := by simp
  simpa [LinearizedPrimalSolution.objectiveTerm, hlast,
    OriginalPrimalSolution.objectiveBidding, BiddingMatrix.coeff] using hbound

theorem sum_suffixRange_terminal_indicator
    (x : OriginalPrimalSolution n) (j : Idx n) :
    Finset.sum (suffixRange j)
        (fun i => if i = lastIdx n then x.r j (TimeIdx.last n) else 0) =
      x.r j (TimeIdx.last n) := by
  rw [Finset.sum_eq_single (lastIdx n)]
  · simp
  · intro i hi hineq
    simp [hineq]
  · intro hnot
    exact False.elim (hnot (mem_suffixRange.mpr (le_lastIdx j)))

theorem objectiveColumn_le_of_objectiveBidding
    {gamma : ℝ} {x : OriginalPrimalSolution n}
    (hx : x.Feasible gamma) (hγ : 1 ≤ gamma) (j : Idx n) :
    Finset.sum (suffixRange j) (fun i =>
        bidValue gamma (x.r j (TimeIdx.ofIdx i)) (x.r j (TimeIdx.succ i))) +
      x.r j (TimeIdx.last n) ≤
      Finset.sum (suffixRange j)
        (fun i =>
          (x.toLinearized gamma).objectiveTerm gamma (x.objectiveBidding gamma) i j) := by
  have hsplit :
      Finset.sum (suffixRange j)
          (fun i => bidValue gamma (x.r j (TimeIdx.ofIdx i)) (x.r j (TimeIdx.succ i))) +
        x.r j (TimeIdx.last n) =
        Finset.sum (suffixRange j)
          (fun i =>
            bidValue gamma (x.r j (TimeIdx.ofIdx i)) (x.r j (TimeIdx.succ i)) +
              if i = lastIdx n then x.r j (TimeIdx.last n) else 0) := by
    calc
      Finset.sum (suffixRange j)
          (fun i => bidValue gamma (x.r j (TimeIdx.ofIdx i)) (x.r j (TimeIdx.succ i))) +
          x.r j (TimeIdx.last n) =
        Finset.sum (suffixRange j)
            (fun i => bidValue gamma (x.r j (TimeIdx.ofIdx i)) (x.r j (TimeIdx.succ i))) +
          Finset.sum (suffixRange j)
            (fun i => if i = lastIdx n then x.r j (TimeIdx.last n) else 0) := by
            rw [x.sum_suffixRange_terminal_indicator j]
      _ = Finset.sum (suffixRange j)
            (fun i =>
              bidValue gamma (x.r j (TimeIdx.ofIdx i)) (x.r j (TimeIdx.succ i)) +
                if i = lastIdx n then x.r j (TimeIdx.last n) else 0) := by
            rw [← Finset.sum_add_distrib]
  rw [hsplit]
  refine Finset.sum_le_sum ?_
  intro i hi
  by_cases hilast : i < lastIdx n
  · have hji : j ≤ i := mem_suffixRange.mp hi
    have hineq :=
      x.objectiveTerm_eq_bidValue_of_objectiveBidding (gamma := gamma) hji hilast
    have hne : i ≠ lastIdx n := ne_of_lt hilast
    simpa [hne] using hineq.ge
  · have hEq : i = lastIdx n := by
      exact le_antisymm (le_lastIdx i) (not_lt.mp hilast)
    subst hEq
    have hsuccLast : TimeIdx.succ (lastIdx n) = TimeIdx.last n := by
      exact (TimeIdx.succ_eq_last (i := lastIdx n)).2 rfl
    simpa [hsuccLast] using x.last_objectiveTerm_ge_bidValue_add_terminal hx hγ j

theorem objective_le_toLinearized_of_objectiveBidding
    {gamma : ℝ} {x : OriginalPrimalSolution n}
    (hx : x.Feasible gamma) (hγ : 1 ≤ gamma) :
    x.objective gamma ≤
      (x.toLinearized gamma).objective gamma (x.objectiveBidding gamma) := by
  unfold OriginalPrimalSolution.objective LinearizedPrimalSolution.objective
  have hsum :
      Finset.sum Finset.univ
          (fun j =>
            Finset.sum (suffixRange j)
                (fun i =>
                  bidValue gamma (x.r j (TimeIdx.ofIdx i)) (x.r j (TimeIdx.succ i))) +
              x.r j (TimeIdx.last n)) ≤
        Finset.sum Finset.univ
          (fun j =>
            Finset.sum (suffixRange j)
              (fun i =>
                (x.toLinearized gamma).objectiveTerm gamma (x.objectiveBidding gamma) i j)) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact x.objectiveColumn_le_of_objectiveBidding hx hγ j
  simpa using sub_le_sub_right hsum x.f

end OriginalPrimalSolution

theorem originalPrimalUpperBound_of_familyUpperBound
    {gamma bound : ℝ}
    (hdual : FamilyUpperBound gamma bound) (hγ : 1 ≤ gamma) :
    OriginalPrimalUpperBound gamma bound := by
  intro n hn x hx
  let : NeZero n := ⟨hn⟩
  let bidding := x.objectiveBidding gamma
  rcases hdual n hn bidding with ⟨y, hy, hρ⟩
  have hxLin : (x.toLinearized gamma).Feasible gamma :=
    x.toLinearized_feasible hx
  have hbridge :
      x.objective gamma ≤ (x.toLinearized gamma).objective gamma bidding :=
    x.objective_le_toLinearized_of_objectiveBidding hx hγ
  have hweak :
      (x.toLinearized gamma).objective gamma bidding ≤ y.rho :=
    LinearizedPrimalSolution.objective_le_rho_of_dual
      (x := x.toLinearized gamma) (y := y) hxLin hy (le_trans zero_le_one hγ)
  exact le_trans hbridge (le_trans hweak hρ)

/-- The generic dual construction transfers to the original program for `1 < γ ≤ 1.224`. -/
theorem originalPrimalUpperBound_exact_of_one_lt
    {gamma : ℝ} (hγlo : 1 < gamma) (hγhi : gamma ≤ (153 : ℝ) / 125) :
    OriginalPrimalUpperBound gamma (2 - (gamma - 1) ^ 2) := by
  exact originalPrimalUpperBound_of_familyUpperBound
    (familyUpperBound_exact_of_one_lt hγlo hγhi) (le_of_lt hγlo)

/-- Close the endpoint `γ = 1` by continuity of each feasible configuration's objective. -/
theorem originalPrimalUpperBound_one : OriginalPrimalUpperBound 1 2 := by
  intro n hn x hx
  have hclosed : IsClosed {gamma : ℝ | x.objective gamma ≤ 2} :=
    isClosed_le x.continuous_objective continuous_const
  have hsubset : Set.Ioc (1 : ℝ) ((153 : ℝ) / 125) ⊆
      {gamma : ℝ | x.objective gamma ≤ 2} := by
    intro gamma hγ
    have hbound := originalPrimalUpperBound_exact_of_one_lt hγ.1 hγ.2 n hn x
      (hx.mono_gamma (le_of_lt hγ.1))
    exact le_trans hbound (sub_le_self _ (sq_nonneg _))
  have hmem : (1 : ℝ) ∈ closure (Set.Ioc (1 : ℝ) ((153 : ℝ) / 125)) := by
    rw [closure_Ioc (by norm_num : (1 : ℝ) ≠ (153 : ℝ) / 125)]
    norm_num
  exact closure_minimal hsubset hclosed hmem

end

end KMedian195


