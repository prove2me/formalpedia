-- Prove2me | Definitions.Def_SpeedScaling_AVR_Canonical
-- name    : SpeedScaling_AVR_Canonical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:07.47553+00:00
-- url     : https://prove2.me/theorems/81cfefc3-0aad-40d1-8002-c7d4cba45b7d
-- title:
--   Type-A and type-B jobs, their costs, order, and nonpreemption
-- statement:
--   A job is type A when its cumulative execution by every time in its window is at least its cumulative average-rate allocation; type B reverses that inequality. A Boolean label chooses a type for every job. The definitions also split average-rate and optimal energy into A and B parts, and define $F_A$ by Eq. (6).
--
--   The A-job order first compares execution speeds, then arrival times in descending order. Equal cases use the job index as a deterministic tie-break. Nonpreemption means that each job's positive-speed execution occupies one interval, up to a set of measure zero, or is null when the job requires no work.
--
--   **Formalization Note.** Execution speed is the job's required work divided by its positive-speed execution time. The value is zero when both are zero. The paper leaves index ties open.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 378, §5.1, Eqs. (3)–(7).

import Definitions.Def_SpeedScaling_AVR_Model

namespace SpeedScaling.AVR
noncomputable section
open MeasureTheory
open scoped Classical

/-- Equation (3): job execution stays ahead of its average-rate allocation. -/
def TypeA {n : ℕ} (J : Instance n) (S : Schedule n) (j : Fin n) : Prop :=
  ∀ t ∈ Set.Icc (J.a j) (J.b j),
    (∫ u in J.a j..t, densityFun J j u) ≤
      (∫ u in J.a j..t, execSpeed S j u)

/-- Equation (4): job execution stays behind its average-rate allocation. -/
def TypeB {n : ℕ} (J : Instance n) (S : Schedule n) (j : Fin n) : Prop :=
  ∀ t ∈ Set.Icc (J.a j) (J.b j),
    (∫ u in J.a j..t, execSpeed S j u) ≤
      (∫ u in J.a j..t, densityFun J j u)

/-- A Boolean bipartition into type A and type B jobs. -/
def IsTyping {n : ℕ} (J : Instance n) (S : Schedule n) (γ : Fin n → Bool) : Prop :=
  ∀ j, (γ j = true → TypeA J S j) ∧ (γ j = false → TypeB J S j)

/-- Mean speed during the positive-speed execution of one job. -/
def jobSpeed {n : ℕ} (J : Instance n) (S : Schedule n) (j : Fin n) : ℝ :=
  J.R j / (volume {t ∈ Set.Icc J.t0 J.t1 | S.job t = some j ∧ 0 < S.s t}).toReal

/-- The paper's A-job order, completed by an index tie-break. -/
def precA {n : ℕ} (J : Instance n) (S : Schedule n) (i j : Fin n) : Prop :=
  jobSpeed J S i > jobSpeed J S j ∨
    (jobSpeed J S i = jobSpeed J S j ∧ J.a i > J.a j) ∨
    (jobSpeed J S i = jobSpeed J S j ∧ J.a i = J.a j ∧ i < j)

/-- Equation (6), for type-A jobs. -/
def fA {n : ℕ} (J : Instance n) (S : Schedule n) (γ : Fin n → Bool) : ℝ :=
  2 * ∑ j ∈ Finset.univ.filter (fun j : Fin n => γ j = true),
    density J j *
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => γ i = true ∧ (i = j ∨ precA J S i j)),
        (∫ t in J.a j..J.b j, execSpeed S i t)

/-- The AVR energy attributable to A-jobs. -/
def AVR_A {n : ℕ} (J : Instance n) (γ : Fin n → Bool) : ℝ :=
  ∫ t in J.t0..J.t1,
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => γ j = true), densityFun J j t) ^ 2

/-- The AVR energy attributable to B-jobs. -/
def AVR_B {n : ℕ} (J : Instance n) (γ : Fin n → Bool) : ℝ :=
  ∫ t in J.t0..J.t1,
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => γ j = false), densityFun J j t) ^ 2

/-- Optimal-schedule energy attributable to A-jobs. -/
def OPT_A {n : ℕ} (J : Instance n) (S : Schedule n) (γ : Fin n → Bool) : ℝ :=
  ∫ t in J.t0..J.t1,
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => γ j = true), execSpeed S j t) ^ 2

/-- Optimal-schedule energy attributable to B-jobs. -/
def OPT_B {n : ℕ} (J : Instance n) (S : Schedule n) (γ : Fin n → Bool) : ℝ :=
  ∫ t in J.t0..J.t1,
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => γ j = false), execSpeed S j t) ^ 2

/-- Each job's positive-speed execution is one interval up to a null set. -/
def IsNonPreemptive {n : ℕ} (J : Instance n) (S : Schedule n) : Prop :=
  ∀ j, (∀ᵐ t ∂volume,
      t ∉ {u ∈ Set.Icc J.t0 J.t1 | S.job u = some j ∧ 0 < S.s u}) ∨
    ∃ u w, J.a j ≤ u ∧ u < w ∧ w ≤ J.b j ∧
      (∀ᵐ t ∂volume,
        (t ∈ {q ∈ Set.Icc J.t0 J.t1 | S.job q = some j ∧ 0 < S.s q}) ↔
          t ∈ Set.Icc u w)

end
end SpeedScaling.AVR


