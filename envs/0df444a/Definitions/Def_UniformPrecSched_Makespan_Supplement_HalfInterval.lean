-- Prove2me | Definitions.Def_UniformPrecSched_Makespan_Supplement_HalfInterval
-- name    : UniformPrecSched_Makespan_Supplement_HalfInterval
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:22:16.677112+00:00
-- url     : https://prove2.me/theorems/51c6fb8f-6555-43fb-bc7b-5fe5a73a761f
-- title:
--   Half intervals, filtered assignments, speed-rounded fragments and concatenated output
-- statement:
--   After reversible normalization, solve the interval LP. Let $\ell_1(j)$ be the first prefix containing half of job $j$'s mass and let $\ell_2(j)$ be the first positive level whose dyadic right endpoint is at least $\bar C_j$. Set
--
--   $$\ell(j)=\max\{\ell_1(j),\ell_2(j)\},\qquad
--   \widetilde x_{kj}=\frac{\sum_{t=1}^{\ell(j)}\bar x_{kjt}}{\beta_j},\quad
--   \beta_j=\sum_k\sum_{t=1}^{\ell(j)}\bar x_{kjt}.$$
--
--   Extend the zero-mass grid through all assigned levels. Restrict jobs and precedence to each group, retaining every machine. The associated completion and deadline data are $2\bar C_j$ and $2^{\ell+1}$. Construct original-speed and rounded-speed fragments using the published assignment rule with threshold $\sqrt K+1$ and speed-based list scheduling. Rounding uses $\alpha=\max(1,\lceil\log_2m\rceil)$ and $\beta=68/25$; discarded class mass is moved to the fastest class, then all masses mapping to one rounded class are aggregated. Retain the shorter fragment, lifting rounded machines to their original identities.
--
--   Let $\rho=\max(1,\max_\ell\operatorname{makespan}(F_\ell)/2^{\ell+1})$. The normalized start of job $j\in J_\ell$ is its local start plus $\rho\sum_{t=0}^{\ell}2^t$; divide by the normalization factor to obtain the original start. This measured common ratio implements the source's shifted windows using rational shifts on rational input. Its theoretical approximation bound is a theorem conclusion, not part of the output predicate.
--
--   The output relation fixes this entire pipeline on raw machine/start data. It assumes neither global feasibility nor an approximation inequality. The half-level fallback only totalizes infeasible raw inputs; unit mass ensures the first half-prefix exists on every pipeline input.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 13 (PDF 13), half-interval construction and shifted fragments; pp. 9–10 (PDF 9–10), general speed rounding

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Supplement_IntervalLP

namespace UniformPrecSched.Makespan.Supplement

variable {n m : ℕ}

open Classical in
/-- §4, p. 13, PDF 13: first half-mass prefix. Feasibility guarantees
existence in 1,...,L. The fallback only totalizes infeasible raw data. -/
noncomputable def halfLevel (I : Instance n m) (x : IntervalMass I) (j : Fin n) : ℕ :=
  if h : ∃ l : ℕ, 1 ≤ l ∧ 1 / 2 ≤ prefixMass I x j l then Nat.find h else 1

/-- First dyadic right endpoint at least C, among levels starting at 1. -/
noncomputable def completionLevel (C : ℝ) : ℕ :=
  max 1 ⌈Real.logb 2 (max 1 C)⌉₊

/-- l(j)=max(l₁(j),l₂(j)); no unjustified bound C_j≤2^L is assumed. -/
noncomputable def jobLevel (I : Instance n m) (x : IntervalMass I) (C : Fin n → ℝ)
    (j : Fin n) : ℕ := max (halfLevel I x j) (completionLevel (C j))

/-- Extend the zero-mass grid through every assigned level, including zero-weight jobs. -/
noncomputable def extendedHorizon (I : Instance n m) (L : ℕ) (x : IntervalMass I)
    (C : Fin n → ℝ) : ℕ := max L (Finset.univ.sup (jobLevel I x C))

/-- The filtered/renormalized assignment x̃ of p. 13. Its denominator β_j is
at least 1/2 on feasible inputs. -/
noncomputable def filteredMass (I : Instance n m) (x : IntervalMass I)
    (C : Fin n → ℝ) (k : Fin (numSpeeds I)) (j : Fin n) : ℝ :=
  (∑ t ∈ Finset.Icc 1 (jobLevel I x C j), x k j t) /
    prefixMass I x j (jobLevel I x C j)

/-- Group of jobs assigned to one level; machines are never restricted. -/
noncomputable def groupSet {E : ℕ} (level : Fin n → Fin E) (l : Fin E) : Finset (Fin n) :=
  Finset.univ.filter fun j => level j = l

/-- Increasing enumeration of the group's original job indices. -/
noncomputable def groupEmb {E : ℕ} (level : Fin n → Fin E) (l : Fin E) :
    Fin (groupSet level l).card ↪o Fin n := (groupSet level l).orderEmbOfFin rfl

/-- Restrict jobs and precedence to J_l and retain all original machine speeds. -/
noncomputable def groupInstance (I : Instance n m) {E : ℕ}
    (level : Fin n → Fin E) (l : Fin E) : Instance (groupSet level l).card m where
  p := fun j => I.p (groupEmb level l j)
  s := I.s
  prec := fun i j => I.prec (groupEmb level l i) (groupEmb level l j)
  m_pos := I.m_pos
  p_pos := fun _j => I.p_pos _
  s_pos := I.s_pos
  prec_irrefl := fun _j => I.prec_irrefl _
  prec_trans := fun _i _j _k => I.prec_trans _ _ _

/-- The LP data used by the fragment, p. 13: C̃=2C̄, D̃=2^(l+1). -/
noncomputable def fragmentCompletion (C : Fin n → ℝ) {E : ℕ}
    (level : Fin n → Fin E) (l : Fin E) (j : Fin (groupSet level l).card) : ℝ :=
  2 * C (groupEmb level l j)

def fragmentDeadline (l : ℕ) : ℝ := dyadic (l + 1)

/-- Rational implementation parameters allowed by §3, p. 10, PDF 10.
They retain the 1.89 leading coefficient. -/
noncomputable def roundingAlpha (m : ℕ) : ℝ := (max 1 ⌈Real.logb 2 m⌉₊ : ℕ)

noncomputable def roundingBeta : ℝ := 68 / 25

/-- The published speed rounding with rational-preserving parameters. -/
noncomputable def rationalRound (I : Instance n m) :
    Instance n (keptCount I (roundingAlpha m)) :=
  roundInstance I (roundingAlpha m) roundingBeta
    (by unfold roundingAlpha; exact_mod_cast (Nat.le_max_left 1 ⌈Real.logb 2 m⌉₊))
    (by norm_num [roundingBeta])

/-- Map each old class to its rounded class, sending discarded mass to the fastest
class first, exactly as in §3, pp. 9–10, PDF 9–10. The equality determines the class;
no performance guarantee or LP feasibility is assumed here. -/
def IsClassTransfer (I : Instance n m)
    (π : Fin (numSpeeds I) → Fin (numSpeeds (rationalRound I))) : Prop :=
  ∀ k, classSpeed (rationalRound I) (π k) =
    roundedSpeed I roundingBeta
      (if maxSpeed I / (roundingAlpha m * m) ≤ classSpeed I k
       then classSpeed I k else maxSpeed I)

/-- Aggregate all masses whose source speeds round to the same target speed. -/
noncomputable def transferredMass (I : Instance n m)
    (π : Fin (numSpeeds I) → Fin (numSpeeds (rationalRound I)))
    (x : Fin (numSpeeds I) → Fin n → ℝ)
    (k : Fin (numSpeeds (rationalRound I))) (j : Fin n) : ℝ :=
  ∑ a, if π a = k then x a j else 0

/-- Actual §3 fragment construction on original and rounded speeds. The shorter
of the original schedule and the rounded schedule is used (ties allow either).
The rounded schedule is lifted by retaining starts and original machine identities.
There is no approximation inequality, running-time bound, or optimum scheduler in this predicate. -/
def IsFragment (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (σ : Schedule I) : Prop :=
  ∃ (k : Assignment I) (a : Schedule I)
    (π : Fin (numSpeeds I) → Fin (numSpeeds (rationalRound I)))
    (k' : Assignment (rationalRound I)) (b : Schedule (rationalRound I)),
    IsLPAssignment I x (Real.sqrt (numSpeeds I) + 1) k ∧
    IsSpeedListSchedule I k a ∧ IsClassTransfer I π ∧
    IsLPAssignment (rationalRound I) (transferredMass I π x)
      (Real.sqrt (numSpeeds (rationalRound I)) + 1) k' ∧
    IsSpeedListSchedule (rationalRound I) k' b ∧
    ((a.makespan ≤ b.makespan ∧ σ = a) ∨
      (b.makespan ≤ a.makespan ∧ ∀ j,
        σ.μ j = keptEmb I (roundingAlpha m) (b.μ j) ∧ σ.S j = b.S j))

/-- The measured common fragment ratio. Using actual lengths gives a rational
shift on rational input. It is at most the theoretical ratio used on p. 13, and
at least 1, so the same displayed shifted windows remain valid. -/
noncomputable def fragmentRatio (I : Instance n m) {E : ℕ}
    (level : Fin n → Fin E) (F : ∀ l, Schedule (groupInstance I level l)) : ℝ :=
  (List.ofFn fun l => (F l).makespan / fragmentDeadline (l.val + 1)).foldr max 1

/-- Operational output specification for §4, pp. 12–14, PDF 12–14.
Normalize, solve (15)–(22), take half intervals, filter, run the two §3 fragment
branches, select the shorter fragment and concatenate at the displayed shifted times.
The output is raw machine/start data: its feasibility is a conclusion of Theorem 4.1.
The grid is extended with zero mass when C exceeds the original horizon. -/
def IsPipelineOutput (I : Instance n m) (R : ReleaseWeights n)
    (μ : Fin n → Fin m) (S : Fin n → ℝ) : Prop :=
  let A := scaledInstance I
  let B := scaledReleaseWeights I R
  let L := intervalHorizon A B
  ∃ (x : IntervalMass A) (C : Fin n → ℝ),
    IntervalOptimal A B L x C ∧
    ∃ (level : Fin n → Fin (extendedHorizon A L x C))
      (F : ∀ l, Schedule (groupInstance A level l)),
      (∀ j, (level j).val + 1 = jobLevel A x C j) ∧
      (∀ l, IsFragment (groupInstance A level l)
        (fun k j => filteredMass A x C k (groupEmb level l j)) (F l)) ∧
      ∀ l (j : Fin (groupSet level l).card),
        μ (groupEmb level l j) = (F l).μ j ∧
        S (groupEmb level l j) =
          (fragmentRatio A level F * (∑ t ∈ Finset.range (l.val + 2), dyadic t) +
            (F l).S j) / timeScale I

end UniformPrecSched.Makespan.Supplement


