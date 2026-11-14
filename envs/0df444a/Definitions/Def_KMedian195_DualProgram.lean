-- Prove2me | Definitions.Def_KMedian195_DualProgram
-- name    : KMedian195_DualProgram
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:41.964206+00:00
-- url     : https://prove2.me/theorems/246a2931-2f5e-4806-a2c8-2c6928a1ab7a
-- title:
--   KMedian195.DualProgram
-- statement:
--   This is module `KMedian195.DualProgram` of the library KMedian195: the proof that the factor-revealing program of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) (Part I, Definition 4.1, with the bid $[\alpha-\gamma d]^+$) has value at most $2-(\gamma-1)^2$ for $\gamma\in[1,1.224]$ (Part I, Theorem 4.4). The library was written by Codex in [epfl-thl2/project-k-median](https://github.com/epfl-thl2/project-k-median) (project `bound-195`, commit `d87e2a2`) and is taken from its copy in [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0).
--
--   **Contents.** The module is published as a whole: 26 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_KMedian195_DualProgram`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Imported/KMedian195/DualProgram.lean

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`,
file `bound-195/KMedian195/DualProgram.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`).
-/
module

public import Definitions.Def_KMedian195_Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `KMedian195.DualProgram` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
@[expose] public section

namespace KMedian195

/-- A lower-triangular `0/1` bidding pattern `b_{i,j}`. -/
structure BiddingMatrix (n : ℕ) where
  toFun : Idx n → Idx n → Bool
  upper_zero : ∀ {i j : Idx n}, i < j → toFun i j = false

instance : CoeFun (BiddingMatrix n) (fun _ => Idx n → Idx n → Bool) := ⟨BiddingMatrix.toFun⟩

namespace BiddingMatrix

/-- Real-valued version of the binary coefficient `b_{i,j}`. -/
def coeff (b : BiddingMatrix n) (i j : Idx n) : ℝ :=
  if b i j then 1 else 0

@[simp] theorem coeff_eq_one {b : BiddingMatrix n} {i j : Idx n} (h : b i j = true) :
    b.coeff i j = 1 := by
  simp [coeff, h]

@[simp] theorem coeff_eq_zero {b : BiddingMatrix n} {i j : Idx n} (h : b i j = false) :
    b.coeff i j = 0 := by
  simp [coeff, h]

@[simp] theorem coeff_eq_zero_of_lt {b : BiddingMatrix n} {i j : Idx n} (hij : i < j) :
    b.coeff i j = 0 := by
  simp [coeff, b.upper_zero hij]

theorem coeff_nonneg (b : BiddingMatrix n) (i j : Idx n) : 0 ≤ b.coeff i j := by
  by_cases h : b i j
  · simp [coeff, h]
  · simp [coeff, h]

end BiddingMatrix

/-- A single inner dual LP from Definition `frdual`, determined by `n`, `M`, and `b`. -/
structure DualProgram (n : ℕ) where
  Mcoeff : ℝ
  bidding : BiddingMatrix n

namespace DualProgram

def Mcoeffmone (P : DualProgram n) : ℝ :=
  P.Mcoeff - 1

def bid (P : DualProgram n) (i j : Idx n) : ℝ :=
  P.bidding.coeff i j

@[simp] theorem bid_eq_zero_of_lt (P : DualProgram n) {i j : Idx n} (hij : i < j) :
    P.bid i j = 0 := by
  simpa [bid] using P.bidding.coeff_eq_zero_of_lt hij

end DualProgram

/-- The dual variables `(rho, \hat g, g, s, t)` from Definition `frdual`. -/
structure DualSolution (n : ℕ) where
  rho : ℝ
  hatG : Idx n → ℝ
  g : Idx n → Idx n → ℝ
  /--
  The corrected dual only uses the strict-lower entries `s_{i,j}` with `j < i`.
  We still store `s` as a total function for convenience, but all LP expressions below
  ignore the diagonal.
  -/
  s : Idx n → Idx n → ℝ
  t : Idx n → Idx n → ℝ

namespace DualSolution

def totalHatG (x : DualSolution n) : ℝ :=
  Finset.sum Finset.univ x.hatG

/-- The strict-lower part of `s`, with the diagonal discarded. -/
def strictS (x : DualSolution n) (i j : Idx n) : ℝ :=
  if j < i then x.s i j else 0

/-- Left-hand side of the paper's `(r_{j,i})` constraint. -/
def clientCredit (x : DualSolution n) (i j : Idx n) : ℝ :=
  Finset.sum (strictSuffixRange j) (fun q => x.g j q) +
    Finset.sum (intervalRange j i) (fun p => x.g p j + x.t p j - x.strictS p j)

/-- Left-hand side of the paper's `(m_i)` constraint. -/
def poolCredit (x : DualSolution n) (i : Idx n) : ℝ :=
  Finset.sum (prefixRange i) fun p =>
    Finset.sum (prefixRange p) fun j => x.strictS p j - x.t p j

/-- Right-hand side of the paper's `(d_j)` bound for column `j`. -/
def columnValue (x : DualSolution n) (P : DualProgram n) (j : Idx n) : ℝ :=
  P.Mcoeff * Finset.sum Finset.univ (fun i => x.g i j) +
    Finset.sum (strictSuffixRange j) (fun i => x.s i j) +
    Finset.sum (suffixRange j) (fun i => x.t i j)

def BoundedHatG (x : DualSolution n) : Prop :=
  x.totalHatG ≤ 1

def DominatesColumns (x : DualSolution n) : Prop :=
  ∀ i j, x.g i j ≤ x.hatG i

def SatisfiesClientConstraints (x : DualSolution n) (P : DualProgram n) : Prop :=
  ∀ ⦃j i : Idx n⦄, j ≤ i →
    x.clientCredit i j ≥
      P.bid i j - P.Mcoeffmone * Finset.sum (halfOpenIntervalRange j i) (fun p => P.bid p j)

def SatisfiesPoolConstraints (x : DualSolution n) : Prop :=
  ∀ i, 0 ≤ x.poolCredit i

def SatisfiesValueConstraints (x : DualSolution n) (P : DualProgram n) : Prop :=
  ∀ j, x.rho ≥ x.columnValue P j

def Nonnegative (x : DualSolution n) : Prop :=
  (∀ i, 0 ≤ x.hatG i) ∧
    (∀ i j, 0 ≤ x.g i j) ∧
    (∀ i j, 0 ≤ x.s i j) ∧
    (∀ i j, 0 ≤ x.t i j)

/-- Feasibility for one inner program of the family in Definition `frdual`. -/
def Feasible (x : DualSolution n) (P : DualProgram n) : Prop :=
  x.BoundedHatG ∧
    x.DominatesColumns ∧
    x.SatisfiesClientConstraints P ∧
    x.SatisfiesPoolConstraints ∧
    x.SatisfiesValueConstraints P ∧
    x.Nonnegative

/-- Existence of a feasible certificate of value at most `bound`. -/
def HasValueAtMost (P : DualProgram n) (bound : ℝ) : Prop :=
  ∃ x : DualSolution n, x.Feasible P ∧ x.rho ≤ bound

end DualSolution

/-- A formal target for the paper's global upper-bound statement over all `n ≥ 1`. -/
def FamilyUpperBound (Mcoeff bound : ℝ) : Prop :=
  ∀ n, n ≠ 0 → ∀ bidding : BiddingMatrix n,
    DualSolution.HasValueAtMost ({ Mcoeff := Mcoeff, bidding := bidding } : DualProgram n) bound

end KMedian195


