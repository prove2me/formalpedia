-- Prove2me | Definitions.Def_KMedian195_Feasibility
-- name    : KMedian195_Feasibility
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:40:59.333175+00:00
-- url     : https://prove2.me/theorems/f0f0dcaf-b979-4aa3-9783-672423738e2c
-- title:
--   KMedian195.Feasibility
-- statement:
--   This is module `KMedian195.Feasibility` of the library KMedian195: the proof that the factor-revealing program of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) (Part I, Definition 4.1, with the bid $[\alpha-\gamma d]^+$) has value at most $2-(\gamma-1)^2$ for $\gamma\in[1,1.224]$ (Part I, Theorem 4.4). The library was written by Codex in [epfl-thl2/project-k-median](https://github.com/epfl-thl2/project-k-median) (project `bound-195`, commit `d87e2a2`) and is taken from its copy in [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0).
--
--   **Contents.** The module is published as a whole: 16 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_KMedian195_Feasibility`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Imported/KMedian195/Feasibility.lean

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`,
file `bound-195/KMedian195/Feasibility.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`), and:
* `if_pos`, `if_neg`, `dif_pos`, `dif_neg` (deprecated) are `if_pos`, `if_neg`,
  `dif_pos`, `dif_neg`.
-/
module

public import Definitions.Def_KMedian195_PoolConstraints

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `KMedian195.Feasibility` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
@[expose] public section

namespace KMedian195

noncomputable section

variable {n : ℕ} [NeZero n]

namespace ProfileData

variable {I : ProcedureInput n} {Γ : Advice I}

theorem gA_le_hatG_of_muA_pos
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    {i j : Idx n} (hj : 0 < (C.memberships).muA j) :
    C.gA AUX i j ≤ C.hatG i := by
  unfold ProfileData.gA
  linarith [AUX.delta_nonneg i j hj]

theorem gD_le_hatG
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) :
    C.gD AUX i j ≤ C.hatG i := by
  by_cases hlt : i < C.t1
  · rw [ProfileData.gD, if_pos hlt]
    have hnonneg : 0 ≤ C.chi j * I.program.frac * C.hatG i := by
      exact mul_nonneg (mul_nonneg (C.chi_nonneg j) H.frac_nonneg) (H.hatG_nonneg i)
    linarith
  · by_cases heq : i = C.t1
    · rw [ProfileData.gD, if_neg hlt, if_pos heq]
      have hnonneg : 0 ≤ C.chi j * I.program.frac * C.boundaryHatGA := by
        exact mul_nonneg (mul_nonneg (C.chi_nonneg j) H.frac_nonneg) H.boundaryHatGA_nonneg
      linarith
    · rw [ProfileData.gD, if_neg hlt, if_neg heq]

theorem gValue_le_hatG
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (i j : Idx n) :
    C.gValue AUX i j ≤ C.hatG i := by
  let H : NonnegHypotheses C := NonnegHypotheses.of_profile_construction C hΓ hγlo hγhi
  have hμnonneg := C.memberships_nonnegative H
  have hA :
      (C.memberships).muA j * C.gA AUX i j ≤
        (C.memberships).muA j * C.hatG i := by
    by_cases hμA0 : (C.memberships).muA j = 0
    · simp [hμA0]
    · have hμApos : 0 < (C.memberships).muA j :=
        lt_of_le_of_ne (hμnonneg.1 j) (Ne.symm hμA0)
      exact mul_le_mul_of_nonneg_left
        (C.gA_le_hatG_of_muA_pos AUX hμApos) (hμnonneg.1 j)
  have hB :
      (C.memberships).muB j * C.gB AUX i j ≤
        (C.memberships).muB j * C.hatG i := by
    simp [ProfileData.gB]
  have hC :
      (C.memberships).muC j * C.gC AUX i j ≤
        (C.memberships).muC j * C.hatG i := by
    simp [ProfileData.gC]
  have hD :
      (C.memberships).muD j * C.gD AUX i j ≤
        (C.memberships).muD j * C.hatG i := by
    exact mul_le_mul_of_nonneg_left (C.gD_le_hatG H AUX i j) (hμnonneg.2.2.2 j)
  have htotal :
      (C.memberships).muA j + (C.memberships).muB j + (C.memberships).muC j +
          (C.memberships).muD j = 1 := by
    simpa [MembershipWeights.total] using C.memberships_total j
  unfold ProfileData.gValue
  nlinarith [hA, hB, hC, hD, H.hatG_nonneg i, htotal]

theorem constructedDualSolution_boundedHatG
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) :
    DualSolution.BoundedHatG (C.constructedDualSolution AUX) := by
  unfold DualSolution.BoundedHatG DualSolution.totalHatG
  change totalBudget C.hatG ≤ 1
  rw [C.total_eq_one]

theorem constructedDualSolution_dominatesColumns
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    DualSolution.DominatesColumns (C.constructedDualSolution AUX) := by
  intro i j
  simpa using C.gValue_le_hatG AUX hΓ hγlo hγhi i j

theorem constructedDualSolution_feasible
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    DualSolution.Feasible (C.constructedDualSolution AUX) I.program := by
  let H : NonnegHypotheses C := NonnegHypotheses.of_profile_construction C hΓ hγlo hγhi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact C.constructedDualSolution_boundedHatG AUX
  · exact C.constructedDualSolution_dominatesColumns AUX hΓ hγlo hγhi
  · exact C.constructedDualSolution_satisfiesClientConstraints AUX hΓ hγlo hγhi hθpos
  · exact C.constructedDualSolution_satisfiesPoolConstraints AUX hΓ hγlo hγhi hθpos
  · exact C.constructedDualSolution_satisfiesValueConstraints AUX hΓ hγlo hγhi hθpos
  · exact C.constructedDualSolution_nonnegative H AUX

theorem constructedDualSolution_hasValueAtMost
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    DualSolution.HasValueAtMost I.program I.program.rhoBound := by
  refine ⟨C.constructedDualSolution AUX,
    C.constructedDualSolution_feasible AUX hΓ hγlo hγhi hθpos, ?_⟩
  rw [C.constructedDualSolution_rho]

end ProfileData

structure ProcedureCertificate (I : ProcedureInput n) (Γ : Advice I) where
  profile : ProfileData I Γ
  corrections : AuxiliaryCorrections profile
  admissible : Γ.Admissible
  coeff_lower : 1 ≤ I.program.Mcoeff
  coeff_upper : I.program.Mcoeff ≤ (153 : ℝ) / 125
  theta_pos : 0 < I.program.theta

namespace ProcedureCertificate

variable {I : ProcedureInput n} {Γ : Advice I}

def solution (cert : ProcedureCertificate I Γ) : DualSolution n :=
  cert.profile.constructedDualSolution cert.corrections

theorem solution_feasible (cert : ProcedureCertificate I Γ) :
    DualSolution.Feasible cert.solution I.program := by
  exact cert.profile.constructedDualSolution_feasible
    cert.corrections cert.admissible cert.coeff_lower cert.coeff_upper cert.theta_pos

theorem solution_rho_eq (cert : ProcedureCertificate I Γ) :
    cert.solution.rho = I.program.rhoBound := by
  exact cert.profile.constructedDualSolution_rho cert.corrections

end ProcedureCertificate

abbrev CertifiedBuilder (I : ProcedureInput n) :=
  ∀ Γ : Advice I, Option (ProcedureCertificate I Γ)

def certifiedProcedure {I : ProcedureInput n} (build : CertifiedBuilder I) :
    AdaptiveProcedure I := fun Γ =>
  match build Γ with
  | some cert => some cert.solution
  | none => none

theorem certifiedProcedure_eq_some
    {I : ProcedureInput n} (build : CertifiedBuilder I) {Γ : Advice I}
    {cert : ProcedureCertificate I Γ} (h : build Γ = some cert) :
    certifiedProcedure build Γ = some cert.solution := by
  simp [certifiedProcedure, h]

theorem certifiedProcedure_correctAdvice
    {I : ProcedureInput n} (build : CertifiedBuilder I) {Γ : Advice I}
    {cert : ProcedureCertificate I Γ} (h : build Γ = some cert) :
    CorrectAdvice (certifiedProcedure build) Γ := by
  refine ⟨cert.solution, ?_⟩
  exact certifiedProcedure_eq_some build h

theorem certifiedProcedure_boundedBy
    {I : ProcedureInput n} (build : CertifiedBuilder I) :
    ProcedureBoundedBy I (certifiedProcedure build) I.program.rhoBound := by
  intro Γ x hx
  cases hbuild : build Γ with
  | none =>
      simp [certifiedProcedure, hbuild] at hx
  | some cert =>
      have hx' : cert.solution = x := by
        simpa [certifiedProcedure, hbuild] using hx
      subst x
      exact ⟨cert.solution_feasible, cert.solution_rho_eq.le⟩

end

end KMedian195


