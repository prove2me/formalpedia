-- Prove2me | Definitions.Def_CloseGaps_DPA_RevenueEvents
-- name    : CloseGaps_DPA_RevenueEvents
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:35:11.432269+00:00
-- url     : https://prove2.me/theorems/a0e0c1fd-12ec-49ab-8a5f-1c59d1e4932b
-- title:
--   DPA events and phase revenues
-- statement:
--   The switch events, containment event, inventory events and four revenue contributions, constructed from the same Poisson driver.
-- source:
--   Wang, Deng, and Ye (2014), Operations Research 62(2), 318–331, DOI 10.1287/opre.2013.1245, §5, equations (28)–(32), pp. 325–326 (PDF 8–9)

import Definitions.Def_CloseGaps_DPA_Execution

open MeasureTheory Set
noncomputable section
open scoped Classical

namespace CloseGaps.DPA

/-- Accessors are used only alongside existence of the complete trace. Their defaults do not
constitute successful construction; every theorem concludes `Experiment`, which excludes them. -/
def us (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) (i : ℕ) : Stage :=
  (uStage a lam n x E i).getD default

def cs (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) (l i : ℕ) : Stage :=
  (cStage a lam n x E l i).getD default

def B (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (N : StageCounts) (i : ℕ) : Set Noise :=
  {E | switchIndex a lam n x E N = i}

def reached (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (N : StageCounts) (i : ℕ) : Set Noise :=
  ⋃ l ∈ Icc i (N.Nu + 1), B a lam n x N l

def switched (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (N : StageCounts) : Set Noise :=
  ⋃ l ∈ Icc 1 N.Nu, B a lam n x N l

def activeBranch (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) (N : StageCounts) : ℕ :=
  min (switchIndex a lam n x E N) N.Nu

def A0 (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (N : StageCounts) : Set Noise :=
  {E | let l := switchIndex a lam n x E N
    (l = N.Nu + 1 → ∀ i ∈ Icc 1 N.Nu,
      dOpt a x 1 lam ∈ Icc (us a lam n x E i).lo (us a lam n x E i).hi) ∧
    (l ≤ N.Nu → uOpt a lam ≤ cOpt a x 1 lam ∧
      (∀ i ∈ Icc 1 l, dOpt a x 1 lam ∈ Icc (us a lam n x E i).lo (us a lam n x E i).hi) ∧
      ∀ j ∈ Icc 1 N.Nc, dOpt a x 1 lam ∈ Icc (cs a lam n x E l j).lo (cs a lam n x E l j).hi)}

def sumU (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) (l : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 l, ∑ j ∈ Finset.range (us a lam n x E i).k,
    ((us a lam n x E i).counts j : ℝ)

def sumC (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) (N : StageCounts) (l : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 N.Nc, ∑ j ∈ Finset.range (cs a lam n x E l i).k,
    ((cs a lam n x E l i).counts j : ℝ)

def A1 (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (N : StageCounts) : Set Noise :=
  A0 a lam n x N ∩ {E | sumU a lam n x E N.Nu < n * x}

def A2 (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (N : StageCounts) : Set Noise :=
  A0 a lam n x N ∩ {E | sumU a lam n x E N.Nu +
    sumC a lam n x E N (activeBranch a lam n x E N) < n * x}

def indicator (A : Set Noise) (E : Noise) : ℝ := by
  classical
  exact if E ∈ A then 1 else 0

def probability (A : Set Noise) : ℝ := (clockLaw A).toReal

def pTilde (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) (N : StageCounts) : ℝ :=
  (us a lam n x E N.Nu).center + 2 * Real.sqrt (Real.log n) * (us a lam n x E N.Nu).gap

def qTilde (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) (N : StageCounts) (l : ℕ) : ℝ :=
  let s := cs a lam n x E l N.Nc
  s.grid s.bestC

def finalCountU (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) (N : StageCounts) : ℝ :=
  let v := (us a lam n x E N.Nu).endClock
  (poissonCount E (v + n * lam (pTilde a lam n x E N) * (1 - timeU n N.Nu)) - poissonCount E v : ℕ)

def finalCountC (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) (N : StageCounts) (l : ℕ) : ℝ :=
  let v := (cs a lam n x E l N.Nc).endClock
  (poissonCount E (v + n * lam (qTilde a lam n x E N l) *
    (1 - timeU n l - timeC n N.Nc)) - poissonCount E v : ℕ)

def revenue4 (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (N : StageCounts) (E : Noise) : ℝ :=
  ∑ i ∈ Finset.Icc 1 N.Nu, ∑ j ∈ Finset.range (us a lam n x E i).k,
    (us a lam n x E i).grid j * (us a lam n x E i).counts j *
      indicator (reached a lam n x N i) E * indicator (A1 a lam n x N) E

def revenue5 (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (N : StageCounts) (E : Noise) : ℝ :=
  pTilde a lam n x E N * min (finalCountU a lam n x E N)
    (max (n * x - sumU a lam n x E N.Nu) 0) * indicator (B a lam n x N (N.Nu + 1)) E

def revenue6 (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (N : StageCounts) (E : Noise) : ℝ :=
  let l := activeBranch a lam n x E N
  ∑ i ∈ Finset.Icc 1 N.Nc, ∑ j ∈ Finset.range (cs a lam n x E l i).k,
    (cs a lam n x E l i).grid j * (cs a lam n x E l i).counts j *
      indicator (switched a lam n x N) E * indicator (A2 a lam n x N) E

def revenue7 (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (N : StageCounts) (l : ℕ) (E : Noise) : ℝ :=
  qTilde a lam n x E N l * min (finalCountC a lam n x E N l)
    (max (n * x - sumU a lam n x E l - sumC a lam n x E N l) 0) * indicator (B a lam n x N l) E

/-- The §5 experiment is constructed, and all displayed expectations/probabilities are meaningful.
These are construction obligations in theorem conclusions, never assumptions on the size.
The final u-demand intensity must be nonnegative on the branch where it is used;
feasibility of that posted price is part of the main theorem, not this definition. -/
def Experiment (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (π : PriceRule) (N : StageCounts) : Prop :=
  generated a lam n x 1 π N ∧
  (∀ᵐ E ∂clockLaw, completeTrace a lam n x N E ∧
    0 ≤ 1 - timeU n N.Nu ∧
    (∀ l ∈ Icc 1 N.Nu, 0 ≤ 1 - timeU n l - timeC n N.Nc) ∧
    (E ∈ B a lam n x N (N.Nu + 1) → 0 ≤ lam (pTilde a lam n x E N))) ∧
  MeasurableSet (A0 a lam n x N) ∧ MeasurableSet (A1 a lam n x N) ∧ MeasurableSet (A2 a lam n x N) ∧
  (∀ i, MeasurableSet (B a lam n x N i)) ∧
  Integrable (revenue4 a lam n x N) clockLaw ∧ Integrable (revenue5 a lam n x N) clockLaw ∧
  Integrable (revenue6 a lam n x N) clockLaw ∧
  (∀ l ∈ Icc 1 N.Nu, Integrable (revenue7 a lam n x N l) clockLaw)

end CloseGaps.DPA


