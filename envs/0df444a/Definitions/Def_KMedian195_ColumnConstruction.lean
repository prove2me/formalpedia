-- Prove2me | Definitions.Def_KMedian195_ColumnConstruction
-- name    : KMedian195_ColumnConstruction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:35.591198+00:00
-- url     : https://prove2.me/theorems/40f83a0b-7835-41ff-97f7-c7d756e0271f
-- title:
--   KMedian195.ColumnConstruction
-- statement:
--   This is module `KMedian195.ColumnConstruction` of the library KMedian195: the proof that the factor-revealing program of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) (Part I, Definition 4.1, with the bid $[\alpha-\gamma d]^+$) has value at most $2-(\gamma-1)^2$ for $\gamma\in[1,1.224]$ (Part I, Theorem 4.4). The library was written by Codex in [epfl-thl2/project-k-median](https://github.com/epfl-thl2/project-k-median) (project `bound-195`, commit `d87e2a2`) and is taken from its copy in [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0).
--
--   **Contents.** The module is published as a whole: 67 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_KMedian195_ColumnConstruction`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Imported/KMedian195/ColumnConstruction.lean

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`,
file `bound-195/KMedian195/ColumnConstruction.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`).
-/
module

public import Definitions.Def_KMedian195_ProfileConstruction

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `KMedian195.ColumnConstruction` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
@[expose] public section

namespace KMedian195

noncomputable section

variable {n : ℕ} [NeZero n] {I : ProcedureInput n} {Γ : Advice I}

/-- The range `\{ i : f_j < i ≤ t_3^\star \}` used in the `δ`-sum condition. -/
def deltaRange (I : ProcedureInput n) (Γ : Advice I) (j : Idx n) : Finset (Idx n) :=
  Finset.univ.filter fun i => I.firstBidTime j < i ∧ i ≤ Γ.t3Star

@[simp] theorem mem_deltaRange {I : ProcedureInput n} {Γ : Advice I} {j i : Idx n} :
    i ∈ deltaRange I Γ j ↔ I.firstBidTime j < i ∧ i ≤ Γ.t3Star := by
  simp [deltaRange]

/-- Predicate expressing `i = f_j + 1` on zero-based `Fin n` indices. -/
def IsNextIndex (i k : Idx n) : Prop :=
  k.1.succ = i.1

instance instDecidableIsNextIndex (i k : Idx n) : Decidable (IsNextIndex i k) := by
  unfold IsNextIndex
  infer_instance

/--
Auxiliary variables `δ_{i,j}` and `σ_{i,j}` together with exactly the side conditions stated
in `new_procedure.tex`. The paper only needs these conditions when `μ_j^A > 0`.
-/
structure AuxiliaryCorrections (C : ProfileData I Γ) where
  delta : Idx n → Idx n → ℝ
  sigma : Idx n → Idx n → ℝ
  delta_nonneg : ∀ i j, 0 < (C.memberships).muA j → 0 ≤ delta i j
  delta_le_hatG : ∀ i j, 0 < (C.memberships).muA j → delta i j ≤ C.hatG i
  delta_eq_zero :
    ∀ i j, 0 < (C.memberships).muA j → i ≤ I.firstBidTime j → delta i j = 0
  delta_sum_eq :
    ∀ j, 0 < (C.memberships).muA j →
      Finset.sum (deltaRange I Γ j) (fun i => delta i j) =
        I.program.epsilon *
          (1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) / I.program.theta)
  sigma_nonneg : ∀ i j, 0 < (C.memberships).muA j → 0 ≤ sigma i j
  sigma_le_hatG : ∀ i j, 0 < (C.memberships).muA j → sigma i j ≤ C.hatG i
  sigma_eq_zero :
    ∀ i j, 0 < (C.memberships).muA j →
      (i < j ∨ I.firstBidTime j < i) → sigma i j = 0
  sigma_sum_eq :
    ∀ j, 0 < (C.memberships).muA j →
      Finset.sum (intervalRange j (I.firstBidTime j)) (fun i => sigma i j) =
        posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j))

/--
Local bounds used in the paper's deferred nonnegativity proof. They isolate exactly the
properties of the profile and coefficients needed to show `g,s,t ≥ 0`.
-/
structure NonnegHypotheses (C : ProfileData I Γ) where
  admissible : Γ.Admissible
  alpha_bounds : 0 ≤ C.alpha ∧ C.alpha ≤ 1
  hatG_nonneg : ∀ i, 0 ≤ C.hatG i
  epsilon_nonneg : 0 ≤ I.program.epsilon
  frac_nonneg : 0 ≤ I.program.frac
  frac_le_one : I.program.frac ≤ 1
  chi_le_one : ∀ j, C.chi j ≤ 1
  boundaryHatGA_nonneg : 0 ≤ C.boundaryHatGA
  boundaryHatGA_le_hatG_t1 : C.boundaryHatGA ≤ C.hatG C.t1
  beforeBudget_le_one : ∀ j, beforeBudget C.hatG j ≤ 1
  beforeBudget_le_barTau_of_muC_pos :
    ∀ j, 0 < (C.memberships).muC j → beforeBudget C.hatG j ≤ I.program.barTau

namespace NonnegHypotheses

theorem of_profile_bounds
    (C : ProfileData I Γ)
    (hΓ : Γ.Admissible)
    (hα : 0 ≤ C.alpha ∧ C.alpha ≤ 1)
    (hhatG : ∀ i, 0 ≤ C.hatG i)
    (hγ : 1 ≤ I.program.Mcoeff)
    (hboundary : 0 ≤ C.boundaryHatGA)
    (hboundary_le : C.boundaryHatGA ≤ C.hatG C.t1)
    (hmuCbar :
      ∀ j, 0 < (C.memberships).muC j → beforeBudget C.hatG j ≤ I.program.barTau) :
    NonnegHypotheses C where
  admissible := hΓ
  alpha_bounds := hα
  hatG_nonneg := hhatG
  epsilon_nonneg := I.program.epsilon_nonneg_of_one_le_Mcoeff hγ
  frac_nonneg := I.program.frac_nonneg_of_one_le_Mcoeff hγ
  frac_le_one := I.program.frac_le_one_of_one_le_Mcoeff hγ
  chi_le_one := by
    intro j
    exact C.chi_le_one_of_hatG_nonneg hhatG (I.program.theta_nonneg_of_one_le_Mcoeff hγ) j
  boundaryHatGA_nonneg := hboundary
  boundaryHatGA_le_hatG_t1 := hboundary_le
  beforeBudget_le_one := by
    intro j
    exact beforeBudget_le_one_of_nonneg_of_total_eq_one hhatG C.total_eq_one j
  beforeBudget_le_barTau_of_muC_pos := hmuCbar

theorem of_profile_construction
    (C : ProfileData I Γ)
    (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    NonnegHypotheses C := by
  let hhatG : ∀ i, 0 ≤ C.hatG i :=
    C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
  exact of_profile_bounds C hΓ C.alpha_bounds hhatG hγlo
    (C.boundaryHatGA_nonneg_of_admissible hΓ hγlo hγhi)
    C.boundaryHatGA_le_hatG_t1_of_admissible
    (fun j hj => C.beforeBudget_le_barTau_of_muC_pos (j := j) hj)

theorem beforeBudget_nonneg
    {C : ProfileData I Γ} (H : NonnegHypotheses C) (j : Idx n) :
    0 ≤ beforeBudget C.hatG j :=
  beforeBudget_nonneg_of_nonneg H.hatG_nonneg j

theorem totalBudget_nonneg
    {C : ProfileData I Γ} (H : NonnegHypotheses C) :
    0 ≤ totalBudget C.hatG :=
  totalBudget_nonneg_of_nonneg H.hatG_nonneg

end NonnegHypotheses

namespace ProfileData

variable {I : ProcedureInput n} {Γ : Advice I}

def gA (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  C.hatG i - AUX.delta i j

def sA (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  if j ≤ i then
    C.hatG i - AUX.sigma i j
  else
    0

def tA (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (_i _j : Idx n) : ℝ :=
  0

def gB (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (i _j : Idx n) : ℝ :=
  C.hatG i

def sB (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  if IsNextIndex i (I.firstBidTime j) then
    C.hatG i + I.program.epsilon
  else if j < i then
    C.hatG i
  else
    0

def tB (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  if i = I.firstBidTime j then
    posPart (1 - beforeBudget C.hatG j - I.program.tau)
  else
    0

def gC (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (i _j : Idx n) : ℝ :=
  C.hatG i

def sC (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  if IsNextIndex i (I.firstBidTime j) then
    C.hatG i + I.program.epsilon
  else if j < i then
    C.hatG i
  else
    0

def tC (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  if i = I.firstBidTime j then
    1 - beforeBudget C.hatG j - I.program.tau
  else
    0

def gD (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  if i < C.t1 then
    C.hatG i - C.chi j * I.program.frac * C.hatG i
  else if i = C.t1 then
    C.hatG i - C.chi j * I.program.frac * C.boundaryHatGA
  else
    C.hatG i

def sD (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (_i _j : Idx n) : ℝ :=
  0

def tD (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  if i = I.firstBidTime j then
    1 - beforeBudget C.hatG j
  else
    0

def gValue (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  let μ := C.memberships
  μ.muA j * C.gA AUX i j +
    μ.muB j * C.gB AUX i j +
    μ.muC j * C.gC AUX i j +
    μ.muD j * C.gD AUX i j

def sValue (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  let μ := C.memberships
  μ.muA j * C.sA AUX i j +
    μ.muB j * C.sB AUX i j +
    μ.muC j * C.sC AUX i j +
    μ.muD j * C.sD AUX i j

/--
The corrected dual removes the diagonal `s_{j,j}` by transferring it into the next row
`s_{j+1,j}`. Entries strictly below the diagonal are otherwise unchanged.
-/
def shiftedSValue (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  if j < i then
    C.sValue AUX i j + if IsNextIndex i j then C.sValue AUX j j else 0
  else
    0

def tValue (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  let μ := C.memberships
  μ.muA j * C.tA AUX i j +
    μ.muB j * C.tB AUX i j +
    μ.muC j * C.tC AUX i j +
    μ.muD j * C.tD AUX i j

theorem memberships_nonnegative (C : ProfileData I Γ) (H : NonnegHypotheses C) :
    MembershipWeights.Nonnegative C.memberships :=
  C.memberships_nonnegative_of_admissible H.admissible H.alpha_bounds

theorem muA_nonneg (C : ProfileData I Γ) (H : NonnegHypotheses C) (j : Idx n) :
    0 ≤ (C.memberships).muA j :=
  (C.memberships_nonnegative H).1 j

theorem muB_nonneg (C : ProfileData I Γ) (H : NonnegHypotheses C) (j : Idx n) :
    0 ≤ (C.memberships).muB j :=
  (C.memberships_nonnegative H).2.1 j

theorem muC_nonneg (C : ProfileData I Γ) (H : NonnegHypotheses C) (j : Idx n) :
    0 ≤ (C.memberships).muC j :=
  (C.memberships_nonnegative H).2.2.1 j

theorem muD_nonneg (C : ProfileData I Γ) (H : NonnegHypotheses C) (j : Idx n) :
    0 ≤ (C.memberships).muD j :=
  (C.memberships_nonnegative H).2.2.2 j

theorem gA_nonneg_of_muA_pos
    (C : ProfileData I Γ) (_H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    {i j : Idx n} (hj : 0 < (C.memberships).muA j) :
    0 ≤ C.gA AUX i j := by
  unfold ProfileData.gA
  exact sub_nonneg.mpr (AUX.delta_le_hatG i j hj)

theorem sA_nonneg_of_muA_pos
    (C : ProfileData I Γ) (_H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    {i j : Idx n} (hj : 0 < (C.memberships).muA j) :
    0 ≤ C.sA AUX i j := by
  unfold ProfileData.sA
  split_ifs with hij
  · exact sub_nonneg.mpr (AUX.sigma_le_hatG i j hj)
  · simp

theorem tA_nonneg
    (C : ProfileData I Γ) (_H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ C.tA AUX i j := by
  simp [ProfileData.tA]

theorem gB_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ C.gB AUX i j := by
  simpa [ProfileData.gB] using H.hatG_nonneg i

theorem sB_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ C.sB AUX i j := by
  unfold ProfileData.sB
  split_ifs with hnext hlt
  · nlinarith [H.hatG_nonneg i, H.epsilon_nonneg]
  · simpa using H.hatG_nonneg i
  · simp

theorem tB_nonneg
    (C : ProfileData I Γ) (_H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ C.tB AUX i j := by
  by_cases hij : i = I.firstBidTime j
  · simp [ProfileData.tB, hij, posPart_nonneg]
  · simp [ProfileData.tB, hij]

theorem gC_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ C.gC AUX i j := by
  simpa [ProfileData.gC] using H.hatG_nonneg i

theorem sC_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ C.sC AUX i j := by
  unfold ProfileData.sC
  split_ifs with hnext hlt
  · nlinarith [H.hatG_nonneg i, H.epsilon_nonneg]
  · simpa using H.hatG_nonneg i
  · simp

theorem tC_nonneg_of_muC_pos
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    {i j : Idx n} (hj : 0 < (C.memberships).muC j) :
    0 ≤ C.tC AUX i j := by
  unfold ProfileData.tC
  split_ifs with hij
  · have hbar : beforeBudget C.hatG j ≤ I.program.barTau :=
      H.beforeBudget_le_barTau_of_muC_pos j hj
    have hbar' : beforeBudget C.hatG j ≤ 1 - I.program.tau := by
      simpa [DualProgram.barTau] using hbar
    linarith
  · simp

theorem gD_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ C.gD AUX i j := by
  by_cases hlt : i < C.t1
  · suffices hmain : 0 ≤ C.hatG i - C.chi j * I.program.frac * C.hatG i by
      simpa [ProfileData.gD, hlt] using hmain
    have hcoeff : C.chi j * I.program.frac ≤ 1 := by
      nlinarith [C.chi_nonneg j, H.chi_le_one j, H.frac_nonneg, H.frac_le_one]
    exact sub_nonneg.mpr (by nlinarith [H.hatG_nonneg i, hcoeff])
  · by_cases heq : i = C.t1
    · have hcoeff : C.chi j * I.program.frac ≤ 1 := by
        nlinarith [C.chi_nonneg j, H.chi_le_one j, H.frac_nonneg, H.frac_le_one]
      have hmul : C.chi j * I.program.frac * C.boundaryHatGA ≤ C.boundaryHatGA := by
        nlinarith [H.boundaryHatGA_nonneg, hcoeff]
      have hmain : 0 ≤ C.hatG C.t1 - C.chi j * I.program.frac * C.boundaryHatGA := by
        exact sub_nonneg.mpr (le_trans hmul H.boundaryHatGA_le_hatG_t1)
      simpa [ProfileData.gD, hlt, heq] using hmain
    · simpa [ProfileData.gD, hlt, heq] using H.hatG_nonneg i

theorem sD_nonneg
    (C : ProfileData I Γ) (_H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ C.sD AUX i j := by
  simp [ProfileData.sD]

theorem tD_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ C.tD AUX i j := by
  unfold ProfileData.tD
  split_ifs with hij
  · linarith [H.beforeBudget_le_one j]
  · simp

theorem weighted_gA_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ (C.memberships).muA j * C.gA AUX i j := by
  by_cases hzero : (C.memberships).muA j = 0
  · simp [hzero]
  · have hμ : 0 ≤ (C.memberships).muA j := C.muA_nonneg H j
    have hpos : 0 < (C.memberships).muA j := by
      exact lt_of_le_of_ne hμ (by simpa [eq_comm] using hzero)
    exact mul_nonneg hμ (C.gA_nonneg_of_muA_pos H AUX hpos)

theorem weighted_sA_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ (C.memberships).muA j * C.sA AUX i j := by
  by_cases hzero : (C.memberships).muA j = 0
  · simp [hzero]
  · have hμ : 0 ≤ (C.memberships).muA j := C.muA_nonneg H j
    have hpos : 0 < (C.memberships).muA j := by
      exact lt_of_le_of_ne hμ (by simpa [eq_comm] using hzero)
    exact mul_nonneg hμ (C.sA_nonneg_of_muA_pos H AUX hpos)

theorem weighted_tA_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ (C.memberships).muA j * C.tA AUX i j := by
  exact mul_nonneg (C.muA_nonneg H j) (C.tA_nonneg H AUX i j)

theorem weighted_gB_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ (C.memberships).muB j * C.gB AUX i j := by
  exact mul_nonneg (C.muB_nonneg H j) (C.gB_nonneg H AUX i j)

theorem weighted_sB_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ (C.memberships).muB j * C.sB AUX i j := by
  exact mul_nonneg (C.muB_nonneg H j) (C.sB_nonneg H AUX i j)

theorem weighted_tB_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ (C.memberships).muB j * C.tB AUX i j := by
  exact mul_nonneg (C.muB_nonneg H j) (C.tB_nonneg H AUX i j)

theorem weighted_gC_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ (C.memberships).muC j * C.gC AUX i j := by
  exact mul_nonneg (C.muC_nonneg H j) (C.gC_nonneg H AUX i j)

theorem weighted_sC_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ (C.memberships).muC j * C.sC AUX i j := by
  exact mul_nonneg (C.muC_nonneg H j) (C.sC_nonneg H AUX i j)

theorem weighted_tC_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ (C.memberships).muC j * C.tC AUX i j := by
  by_cases hzero : (C.memberships).muC j = 0
  · simp [hzero]
  · have hμ : 0 ≤ (C.memberships).muC j := C.muC_nonneg H j
    have hpos : 0 < (C.memberships).muC j := by
      exact lt_of_le_of_ne hμ (by simpa [eq_comm] using hzero)
    exact mul_nonneg hμ (C.tC_nonneg_of_muC_pos H AUX hpos)

theorem weighted_gD_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ (C.memberships).muD j * C.gD AUX i j := by
  exact mul_nonneg (C.muD_nonneg H j) (C.gD_nonneg H AUX i j)

theorem weighted_sD_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ (C.memberships).muD j * C.sD AUX i j := by
  exact mul_nonneg (C.muD_nonneg H j) (C.sD_nonneg H AUX i j)

theorem weighted_tD_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ (C.memberships).muD j * C.tD AUX i j := by
  exact mul_nonneg (C.muD_nonneg H j) (C.tD_nonneg H AUX i j)

theorem gValue_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ C.gValue AUX i j := by
  unfold ProfileData.gValue
  nlinarith [C.weighted_gA_nonneg H AUX i j, C.weighted_gB_nonneg H AUX i j,
    C.weighted_gC_nonneg H AUX i j, C.weighted_gD_nonneg H AUX i j]

theorem sValue_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ C.sValue AUX i j := by
  unfold ProfileData.sValue
  nlinarith [C.weighted_sA_nonneg H AUX i j, C.weighted_sB_nonneg H AUX i j,
    C.weighted_sC_nonneg H AUX i j, C.weighted_sD_nonneg H AUX i j]

theorem shiftedSValue_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ C.shiftedSValue AUX i j := by
  by_cases hij : j < i
  · by_cases hnext : IsNextIndex i j
    · have hs : 0 ≤ C.sValue AUX i j := C.sValue_nonneg H AUX i j
      have hsdiag : 0 ≤ C.sValue AUX j j := C.sValue_nonneg H AUX j j
      simpa [ProfileData.shiftedSValue, hij, hnext] using add_nonneg hs hsdiag
    · simpa [ProfileData.shiftedSValue, hij, hnext] using C.sValue_nonneg H AUX i j
  · simp [ProfileData.shiftedSValue, hij]

theorem sValue_diag_eq_zero_of_t1_lt
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    {i : Idx n} (ht1i : C.t1 < i) :
    C.sValue AUX i i = 0 := by
  have hμA0 : (C.memberships).muA i = 0 := by
    have hnot : ¬ i < C.t1 := not_lt.mpr (le_of_lt ht1i)
    simp [ProfileData.memberships, hnot, ne_of_gt ht1i]
  have hnotNext : ¬ IsNextIndex i (I.firstBidTime i) := by
    intro hnext
    unfold IsNextIndex at hnext
    have hlt : I.firstBidTime i < i := Fin.lt_def.mpr (by omega)
    exact (not_lt_of_ge (I.le_firstBidTime i)) hlt
  simp [ProfileData.sValue, ProfileData.sA, ProfileData.sB, ProfileData.sC, ProfileData.sD,
    hμA0, hnotNext]

theorem tValue_nonneg
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    0 ≤ C.tValue AUX i j := by
  unfold ProfileData.tValue
  nlinarith [C.weighted_tA_nonneg H AUX i j, C.weighted_tB_nonneg H AUX i j,
    C.weighted_tC_nonneg H AUX i j, C.weighted_tD_nonneg H AUX i j]

/--
The dual solution obtained from the table in `new_procedure.tex`, after taking the convex
combination with the membership weights.
-/
def constructedDualSolution
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) : DualSolution n where
  rho := I.program.rhoBound
  hatG := C.hatG
  g := C.gValue AUX
  s := C.shiftedSValue AUX
  t := C.tValue AUX

@[simp] theorem constructedDualSolution_hatG (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) :
    (C.constructedDualSolution AUX).hatG = C.hatG := rfl

@[simp] theorem constructedDualSolution_rho (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) :
    (C.constructedDualSolution AUX).rho = I.program.rhoBound := rfl

@[simp] theorem constructedDualSolution_g (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    (C.constructedDualSolution AUX).g i j = C.gValue AUX i j := rfl

@[simp] theorem constructedDualSolution_s (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    (C.constructedDualSolution AUX).s i j = C.shiftedSValue AUX i j := rfl

@[simp] theorem constructedDualSolution_t (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    (C.constructedDualSolution AUX).t i j = C.tValue AUX i j := rfl

theorem constructedDualSolution_nonnegative
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C) :
    DualSolution.Nonnegative (C.constructedDualSolution AUX) := by
  refine ⟨H.hatG_nonneg, ?_, ?_, ?_⟩
  · intro i j
    simpa using C.gValue_nonneg H AUX i j
  · intro i j
    simpa using C.shiftedSValue_nonneg H AUX i j
  · intro i j
    simpa using C.tValue_nonneg H AUX i j

end ProfileData

end

end KMedian195


