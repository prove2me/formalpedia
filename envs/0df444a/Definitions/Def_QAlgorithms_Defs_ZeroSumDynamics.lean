-- Prove2me | Definitions.Def_QAlgorithms_Defs_ZeroSumDynamics
-- name    : QAlgorithms_Defs_ZeroSumDynamics
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:38.288659+00:00
-- url     : https://prove2.me/theorems/d9e03dbd-affd-45e5-9802-c6fb357b7b3f
-- title:
--   ZeroSumDynamics
-- statement:
--   ZeroSumDynamics
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ZeroSumDynamics.lean

import Definitions.Def_QAlgorithms_Defs_ClassicalEntryPrograms
noncomputable section

namespace QAlgorithms.ZeroSum

variable {n m d k b w M K N c out : ℕ}

/-- Probability-mass normalization, 1904.03180 pp.3–5.
Negative coordinates or zero mass return no strategy. -/
def normalizeMass {I : Type*} [Fintype I] (v : I → ℝ) : Option (I → ℝ) :=
  if (∀ i, 0 ≤ v i) ∧ 0 < ∑ i, v i then some (fun i => v i / ∑ j, v j) else none

/-- Algorithm 1 with constant eta=epsilon/4, 1904.03180 pp.3–5.
t counts completed updates from the initialized zero pair. -/
def fixedAccuracyAccumulators {n m : ℕ} [NeZero n] [NeZero m]
    (A : Matrix (Fin n) (Fin m) ℝ) (eps : ℝ) :
    ℕ → PMF ((Fin n → ℝ) × (Fin m → ℝ))
  | 0 => PMF.pure (0, 0)
  | t + 1 => (fixedAccuracyAccumulators A eps t).bind fun xy =>
      (classicalGibbs (-A.transpose.mulVec xy.1)).bind fun a =>
        (classicalGibbs (A.mulVec xy.2)).map fun b =>
          (xy.1 + (eps / 4) • Pi.single b 1, xy.2 + (eps / 4) • Pi.single a 1)

/-- Final strategy law of fixed-accuracy Algorithm 1,
1904.03180 pp.3–5. The accumulators are normalized by coordinate mass.
At zero updates or nonpositive mass no strategy is returned; valid
positive-accuracy schedules have positive mass in both registers. -/
def fixedAccuracyRun {n m : ℕ} [NeZero n] [NeZero m]
    (A : Matrix (Fin n) (Fin m) ℝ) (eps : ℝ) (T : ℕ) :
    PMF (Option ((Fin n → ℝ) × (Fin m → ℝ))) :=
  (fixedAccuracyAccumulators A eps T).map fun xy => do
    let x ← normalizeMass xy.1
    let y ← normalizeMass xy.2
    pure (x,y)

/-- Fixed-accuracy update count, 1904.03180 p.3 Lemma 1 (ceiling is
suppressed in Lemma 3 p.6). Out-of-domain inputs return no schedule. -/
def fixedAccuracyIterations (n m : ℕ) (eps delta : ℝ) : Option ℕ :=
  if 0 < n ∧ 0 < m ∧ 0 < eps ∧ eps < 1 ∧ 0 < delta ∧ delta < 1 / 3 then
    some ⌈16 * Real.log ((n : ℝ) * m / delta) / eps ^ 2⌉₊ else none

/-- Dense classical implementation, 1904.03180 p.6.
Memory layout x,y,u,v is followed by exp arrays and scalar scratch.
Every update reads a full row and column, including their shared entry twice.
Setup, exp/CDF scans, accumulator updates and final mass normalization are counted. -/
def denseImplementation (n m : ℕ) (eps : ℝ) (T : ℕ) : ClassicalEntryProgram :=
  let x := 0
  let y := n
  let u := n + m
  let v := n + 2 * m
  let p := 2 * n + 2 * m
  let q := 2 * n + 3 * m
  let a := 3 * n + 3 * m
  let b := a + 1
  let eta := a + 2
  let negEta := a + 3
  let idx := a + 4
  let val := a + 5
  let tmp := a + 6
  let mass := a + 7
  let setup := (List.range (2 * n + 2 * m)).map (fun i => EntryInstruction.constant i 0) ++
    [.constant eta (eps / 4), .constant negEta (-eps / 4)]
  let update := ((List.range m).map fun j => EntryInstruction.exp (p + j) (u + j)) ++
    ((List.range n).map fun i => EntryInstruction.exp (q + i) (v + i)) ++
    [.sample a p m, .sample b q n, .load val y a, .add val val eta, .store y a val,
      .load val x b, .add val val eta, .store x b val] ++
    ((List.range m).flatMap fun j =>
      [.constant idx j, .entry val b idx, .mul tmp val negEta, .add (u + j) (u + j) tmp]) ++
    ((List.range n).flatMap fun i =>
      [.constant idx i, .entry val idx a, .mul tmp val eta, .add (v + i) (v + i) tmp])
  let finish := [.sum mass x n] ++
    ((List.range n).map fun i => EntryInstruction.div (x + i) (x + i) mass) ++
    [.sum mass y m] ++
    ((List.range m).map fun j => EntryInstruction.div (y + j) (y + j) mass)
  entryThen (entrySteps setup) (.loop T (entrySteps update) (entrySteps finish))

/-- Sanity check for the modeled source objects (arxiv-1904.03180v1, PDF pp.3,4,5,6). -/
example {I : Type*} [Fintype I] : normalizeMass (0 : I → ℝ) = none := by
  simp [normalizeMass]

/-- Sanity check for the modeled source objects (arxiv-1904.03180v1, PDF pp.3,4,5,6). -/
example : normalizeMass (fun _ : Fin 1 => (2 : ℝ)) = some (fun _ => 1) := by
  simp [normalizeMass]

/-- Sanity check for the modeled source objects (arxiv-1904.03180v1, PDF pp.3,4,5,6). -/
example {n m : ℕ} [NeZero n] [NeZero m] (A B : Matrix (Fin n) (Fin m) ℝ) (eps : ℝ) :
    fixedAccuracyRun A eps 0 = fixedAccuracyRun B eps 0 := rfl

end QAlgorithms.ZeroSum


