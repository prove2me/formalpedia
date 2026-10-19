-- Prove2me | Definitions.Def_QAlgorithms_Defs_AQCSchedules
-- name    : QAlgorithms_Defs_AQCSchedules
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:39:11.047452+00:00
-- url     : https://prove2.me/theorems/c5b207b8-e446-499b-bc67-aee33d9d2b33
-- title:
--   AQCSchedules
-- statement:
--   AQCSchedules
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\AQCSchedules.lean

import Definitions.Def_QAlgorithms_Defs_AQCLinearSystemData
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.AQCP

/-- QAlgorithms.AQCP.scheduleNormalization: arxiv-1909.05500v3 PDF p.4. Source domains are explicit below. -/
def scheduleNormalization (kappa p : ℝ) (hk : 1 ≤ kappa) (hp : 0 < p) : ℝ :=
  ∫ u in (0 : ℝ)..1, (gapLowerBound kappa hk u)^(-p)

/-- QAlgorithms.AQCP.schedule: arxiv-1909.05500v3 PDF p.4, arxiv-1909.05500v3 PDF p.5. Source domains are explicit below. -/
def schedule (kappa p : ℝ) (hk : 1 ≤ kappa) (hp : 0 < p) (s : ℝ) : ℝ :=
  if kappa = 1 then s else if p = 1 then kappa/(kappa-1)*(1-kappa^(-s))
  else kappa/(kappa-1)*(1-(1+s*(kappa^(p-1)-1))^(1/(1-p)))

/-- QAlgorithms.AQCP.hamiltonianPath: arxiv-1909.05500v3 PDF p.3, arxiv-1909.05500v3 PDF p.4. Source domains are explicit below. -/
def hamiltonianPath {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.PosDef) (b : EuclideanSpace ℂ I) (hb : IsState b)
    (hk : 1 ≤ conditionNumber A) (p : ℝ) (hp : 0 < p) (s : ℝ) : Matrix (Bool × I) (Bool × I) ℂ :=
  linInterp (initialHamiltonian b hb) (finalHamiltonian A hA b hb) (schedule (conditionNumber A) p hk hp s)

/-- QAlgorithms.AQCP.IsRun: arxiv-1909.05500v3 PDF p.4, arxiv-1909.05500v3 PDF p.5. Source domains are explicit below. -/
def IsRun {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.PosDef) (b : EuclideanSpace ℂ I) (hb : IsState b)
    (hk : 1 ≤ conditionNumber A) (p : ℝ) (hp : 0 < p) (T : ℝ)
    (psi : ℝ → EuclideanSpace ℂ (Bool × I)) : Prop :=
  0 < T ∧ psi 0 = tensorVec (ket false) b ∧
    SolvesScaledSchrodinger (hamiltonianPath A hA b hb hk p hp) T psi ∧
    ∀ s ∈ Set.Icc (0 : ℝ) 1, IsState (psi s)

example (p s : ℝ) (hp : 0 < p) : schedule 1 p le_rfl hp s = s := by simp [schedule]

example (p : ℝ) (hp : 0 < p) : scheduleNormalization 1 p le_rfl hp = 1 := by
  simp [scheduleNormalization, gapLowerBound]

end QAlgorithms.AQCP


