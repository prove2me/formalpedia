-- Prove2me | Definitions.Def_FirstPassageLinearTransport_FiniteBallot
-- name    : FirstPassageLinearTransport_FiniteBallot
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:26:48.069682+00:00
-- url     : https://prove2.me/theorems/7d01a6fb-259b-4948-a767-c7361624c020
-- title:
--   Finite Ballot
-- statement:
--   Definitions and structural lemmas for Finite Ballot, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
def bernoulliAverage (p x₀ x₁ : ℝ) : ℝ :=
  (1 - p) * x₀ + p * x₁
noncomputable def stoppedWalkMean
    (p : ℝ) (x : Bool → ℝ) (lo hi : ℝ) : ℕ → ℝ → ℝ
  | 0, z => z
  | r + 1, z =>
      if z < lo ∨ hi ≤ z then z
      else bernoulliAverage p
        (stoppedWalkMean p x lo hi r (z + x false))
        (stoppedWalkMean p x lo hi r (z + x true))
noncomputable def stoppedWalkSecond
    (p : ℝ) (x : Bool → ℝ) (lo hi : ℝ) : ℕ → ℝ → ℝ
  | 0, z => z ^ 2
  | r + 1, z =>
      if z < lo ∨ hi ≤ z then z ^ 2
      else bernoulliAverage p
        (stoppedWalkSecond p x lo hi r (z + x false))
        (stoppedWalkSecond p x lo hi r (z + x true))
noncomputable def stoppedWalkTime
    (p : ℝ) (x : Bool → ℝ) (lo hi : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | r + 1, z =>
      if z < lo ∨ hi ≤ z then 0
      else 1 + bernoulliAverage p
        (stoppedWalkTime p x lo hi r (z + x false))
        (stoppedWalkTime p x lo hi r (z + x true))
noncomputable def stoppedUpperMass
    (p : ℝ) (x : Bool → ℝ) (lo hi : ℝ) : ℕ → ℝ → ℝ
  | 0, z => if hi ≤ z then 1 else 0
  | r + 1, z =>
      if hi ≤ z then 1
      else if z < lo then 0
      else bernoulliAverage p
        (stoppedUpperMass p x lo hi r (z + x false))
        (stoppedUpperMass p x lo hi r (z + x true))
noncomputable def stoppedHorizonMass
    (p : ℝ) (x : Bool → ℝ) (lo hi : ℝ) : ℕ → ℝ → ℝ
  | 0, z => if z < lo ∨ hi ≤ z then 0 else 1
  | r + 1, z =>
      if z < lo ∨ hi ≤ z then 0
      else bernoulliAverage p
        (stoppedHorizonMass p x lo hi r (z + x false))
        (stoppedHorizonMass p x lo hi r (z + x true))
noncomputable def lowerSurvivalMass
    (p : ℝ) (x : Bool → ℝ) (lo : ℝ) : ℕ → ℝ → ℝ
  | 0, z => if lo ≤ z then 1 else 0
  | r + 1, z =>
      if lo ≤ z then bernoulliAverage p
        (lowerSurvivalMass p x lo r (z + x false))
        (lowerSurvivalMass p x lo r (z + x true))
      else 0
noncomputable def tiltedBinomialMass (p : ℝ) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
def wordIncrementSum {r : ℕ} (x : Bool → ℝ) (v : Fin r → Bool) : ℝ :=
  ∑ i, x (v i)
@[simp] theorem wordIncrementSum_cons
    {r : ℕ} (x : Bool → ℝ) (b : Bool) (w : Fin r → Bool) :
    wordIncrementSum x (Fin.cons b w) =
      x b + wordIncrementSum x w := by
  unfold wordIncrementSum
  rw [Fin.sum_univ_succ]
  simp
@[simp] theorem wordIncrementSum_append
    {r s : ℕ} (x : Bool → ℝ) (v : Fin r → Bool) (w : Fin s → Bool) :
    wordIncrementSum x (Fin.append v w) =
      wordIncrementSum x v + wordIncrementSum x w := by
  unfold wordIncrementSum
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _hi
    simp [Fin.append]
  · apply Finset.sum_congr rfl
    intro i _hi
    simp [Fin.append]
def collatzLogIncrement (b : Bool) : ℝ :=
  if b then Real.log 3 - Real.log 2 else -Real.log 2
def collatzMiddleInterval {r : ℕ} (a : ℝ) (v : Fin r → Bool) : Prop :=
  a ≤ wordIncrementSum collatzLogIncrement v ∧
    wordIncrementSum collatzLogIncrement v < a + 1
noncomputable def collatzMiddleIntervalIndicator
    {r : ℕ} (a : ℝ) (v : Fin r → Bool) : ℝ := by
  classical
  exact if collatzMiddleInterval a v then 1 else 0
def collatzTilt : ℝ := Real.log 2 / Real.log 3
def collatzTiltVariance : ℝ :=
  bernoulliAverage collatzTilt
    ((collatzLogIncrement false) ^ 2)
    ((collatzLogIncrement true) ^ 2)
def bernoulliWordWeight {r : ℕ} (p : ℝ) (v : Fin r → Bool) : ℝ :=
  ∏ i, if v i then p else 1 - p
def wordSurvivesFrom (lo : ℝ) (x : Bool → ℝ) :
    (r : ℕ) → ℝ → (Fin r → Bool) → Prop
  | 0, z, _ => lo ≤ z
  | r + 1, z, v =>
      lo ≤ z ∧ wordSurvivesFrom lo x r (z + x (v 0)) (fun i => v i.succ)
noncomputable def wordSurvivalIndicator
    {r : ℕ} (lo : ℝ) (x : Bool → ℝ) (z : ℝ) (v : Fin r → Bool) : ℝ := by
  classical
  exact if wordSurvivesFrom lo x r z v then 1 else 0
def listIncrementSum (x : Bool → ℝ) (l : List Bool) : ℝ :=
  (l.map x).sum
def listSurvivesFrom (lo : ℝ) (x : Bool → ℝ) : ℝ → List Bool → Prop
  | z, [] => lo ≤ z
  | z, b :: l => lo ≤ z ∧ listSurvivesFrom lo x (z + x b) l
@[simp] theorem listIncrementSum_nil (x : Bool → ℝ) :
    listIncrementSum x [] = 0 := rfl
@[simp] theorem listIncrementSum_cons (x : Bool → ℝ) (b : Bool)
    (l : List Bool) :
    listIncrementSum x (b :: l) = x b + listIncrementSum x l := by
  simp [listIncrementSum]
@[simp] theorem listIncrementSum_append (x : Bool → ℝ)
    (l r : List Bool) :
    listIncrementSum x (l ++ r) =
      listIncrementSum x l + listIncrementSum x r := by
  simp [listIncrementSum]
def wordPrefix {r : ℕ} (v : Fin r → Bool) (j : Fin (r + 1)) :
    Fin j → Bool :=
  fun i => v (Fin.castLE (Nat.le_of_lt_succ j.isLt) i)
@[simp] theorem wordIncrementSum_wordPrefix_zero
    {r : ℕ} (x : Bool → ℝ) (v : Fin r → Bool) :
    wordIncrementSum x (wordPrefix v (0 : Fin (r + 1))) = 0 := by
  unfold wordIncrementSum
  apply Finset.sum_eq_zero
  intro i _hi
  exact Fin.elim0 i
noncomputable def weightedSurvivalWordMass
    (p : ℝ) (x : Bool → ℝ) (lo : ℝ) (r : ℕ) (z : ℝ) : ℝ := by
  classical
  exact ∑ v : Fin r → Bool,
    bernoulliWordWeight p v * if wordSurvivesFrom lo x r z v then 1 else 0
@[simp] theorem bernoulliWordWeight_cons
    {p : ℝ} {r : ℕ} (b : Bool) (w : Fin r → Bool) :
    bernoulliWordWeight p (Fin.cons b w) =
      (if b then p else 1 - p) * bernoulliWordWeight p w := by
  unfold bernoulliWordWeight
  rw [Fin.prod_univ_succ]
  simp
@[simp] theorem bernoulliWordWeight_append
    {p : ℝ} {r s : ℕ} (v : Fin r → Bool) (w : Fin s → Bool) :
    bernoulliWordWeight p (Fin.append v w) =
      bernoulliWordWeight p v * bernoulliWordWeight p w := by
  unfold bernoulliWordWeight
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _hi
    simp [Fin.append]
  · apply Finset.prod_congr rfl
    intro i _hi
    simp [Fin.append]
@[simp] theorem wordSurvivesFrom_cons
    {lo : ℝ} {x : Bool → ℝ} {r : ℕ} {z : ℝ}
    (b : Bool) (w : Fin r → Bool) :
    wordSurvivesFrom lo x (r + 1) z (Fin.cons b w) ↔
      lo ≤ z ∧ wordSurvivesFrom lo x r (z + x b) w := by
  simp [wordSurvivesFrom]
noncomputable def collatzMiddleIntervalMass (n : ℕ) (a : ℝ) : ℝ :=
  ∑ v : Fin n → Bool,
    bernoulliWordWeight collatzTilt v * collatzMiddleIntervalIndicator a v
def collatzTiltLambda : ℝ :=
  (Real.log collatzTilt - Real.log (1 - collatzTilt)) / Real.log 3
def collatzFairTiltRate : ℝ :=
  collatzTiltLambda * Real.log 2 + Real.log 2 + Real.log (1 - collatzTilt)
noncomputable def weightedSurvivalFactor
    (p : ℝ) (x : Bool → ℝ) (lo z : ℝ) {r : ℕ} (v : Fin r → Bool) : ℝ :=
  bernoulliWordWeight p v * wordSurvivalIndicator lo x z v
noncomputable def collatzThreeBlockEnvelopeMass
    (a b : ℕ) (B q center : ℝ) : ℝ :=
  ∑ u : Fin a → Bool,
    weightedSurvivalFactor collatzTilt collatzLogIncrement (-B) 0 u *
      ∑ w : Fin a → Bool,
        weightedSurvivalFactor collatzTilt
            (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) 0 w *
          collatzMiddleIntervalMass b
            (center - wordIncrementSum collatzLogIncrement u +
              wordIncrementSum (fun bit ↦ -collatzLogIncrement bit) w)
def collatzThreeBlockEnvelopeEvent
    {a b : ℕ} (B q : ℝ)
    (u : Fin a → Bool) (v : Fin b → Bool) (w : Fin a → Bool) : Prop :=
  wordSurvivesFrom (-B) collatzLogIncrement a 0 u ∧
    wordSurvivesFrom (-(q + 1))
      (fun bit ↦ -collatzLogIncrement bit) a 0 w ∧
    collatzMiddleInterval
      (q - B - wordIncrementSum collatzLogIncrement u +
        wordIncrementSum (fun bit ↦ -collatzLogIncrement bit) w) v
def collatzThreeBlockWord {a b : ℕ}
    (u : Fin a → Bool) (v : Fin b → Bool) (w : Fin a → Bool) :
    Fin (a + (b + a)) → Bool :=
  Fin.append u (Fin.append v (fun i => w (Fin.rev i)))
def reverseBoolWordEquiv (a : ℕ) :
    (Fin a → Bool) ≃ (Fin a → Bool) :=
  Function.Involutive.toPerm
    (fun w : Fin a → Bool => fun i => w (Fin.rev i))
    (by
      intro w
      funext i
      simp)
def collatzThreeBlockSummationEquiv (a b : ℕ) :
    ((Fin a → Bool) × ((Fin a → Bool) × (Fin b → Bool))) ≃
      (Fin (a + (b + a)) → Bool) :=
  (Equiv.prodCongr (Equiv.refl _)
      ((Equiv.prodComm _ _).trans
        (Equiv.prodCongr (Equiv.refl _) (reverseBoolWordEquiv a)))).trans
    ((Equiv.prodCongr (Equiv.refl _) (Fin.appendEquiv b a)).trans
      (Fin.appendEquiv a (b + a)))
@[simp] theorem collatzThreeBlockSummationEquiv_apply
    {a b : ℕ}
    (u : Fin a → Bool) (w : Fin a → Bool) (v : Fin b → Bool) :
    collatzThreeBlockSummationEquiv a b (u, w, v) =
      collatzThreeBlockWord u v w := by
  simp [collatzThreeBlockSummationEquiv, reverseBoolWordEquiv,
    collatzThreeBlockWord]
  funext i
  rfl
def collatzFullBarrierBinEvent {m : ℕ} (B q : ℝ)
    (v : Fin m → Bool) : Prop :=
  wordSurvivesFrom (-B) collatzLogIncrement m 0 v ∧
    collatzMiddleInterval (q - B) v
noncomputable def collatzThreeBlockEnvelopeIndicator
    {a b : ℕ} (B q : ℝ)
    (u : Fin a → Bool) (v : Fin b → Bool) (w : Fin a → Bool) : ℝ := by
  classical
  exact if collatzThreeBlockEnvelopeEvent B q u v w then 1 else 0
noncomputable def collatzThreeBlockFlatMass
    (p : ℝ) (a b : ℕ) (B q : ℝ) : ℝ :=
  ∑ u : Fin a → Bool, ∑ w : Fin a → Bool, ∑ v : Fin b → Bool,
    (bernoulliWordWeight p u * bernoulliWordWeight p v *
      bernoulliWordWeight p w) *
        collatzThreeBlockEnvelopeIndicator B q u v w
noncomputable def collatzFullBarrierBinIndicator
    {m : ℕ} (B q : ℝ) (v : Fin m → Bool) : ℝ := by
  classical
  exact if collatzFullBarrierBinEvent B q v then 1 else 0
noncomputable def collatzFullThreeBlockMass
    (p : ℝ) (a b : ℕ) (B q : ℝ) : ℝ :=
  ∑ u : Fin a → Bool, ∑ w : Fin a → Bool, ∑ v : Fin b → Bool,
    (bernoulliWordWeight p u * bernoulliWordWeight p v *
      bernoulliWordWeight p w) *
        collatzFullBarrierBinIndicator B q
          (collatzThreeBlockWord u v w)
noncomputable def collatzFullWordMass
    (p : ℝ) (m : ℕ) (B q : ℝ) : ℝ :=
  ∑ word : Fin m → Bool,
    bernoulliWordWeight p word * collatzFullBarrierBinIndicator B q word
def collatzBallotOuterLength (m : ℕ) : ℕ := m / 4
def collatzBallotMiddleLength (m : ℕ) : ℕ :=
  m - 2 * collatzBallotOuterLength m
def ballotMultiplier (b : Bool) : ℝ :=
  if b then 3 / 2 else 1 / 2
@[simp] theorem ballotMultiplier_false : ballotMultiplier false = 1 / 2 := rfl
@[simp] theorem ballotMultiplier_true : ballotMultiplier true = 3 / 2 := rfl
def crossesMultiplicativeFrom (u : ℝ) :
    (r : ℕ) → ℝ → (Fin r → Bool) → Prop
  | 0, z, _ => u < z
  | r + 1, z, v =>
      u < z ∨
        crossesMultiplicativeFrom u r (z * ballotMultiplier (v 0))
          (fun i => v i.succ)
noncomputable def multiplicativeHitCount (u : ℝ) (r : ℕ) (z : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (crossesMultiplicativeFrom u r z)).card
noncomputable def safeMultiplicativeHitSuccEquiv
    {u z : ℝ} {r : ℕ} (hz : ¬u < z) :
    {v : Fin (r + 1) → Bool //
      crossesMultiplicativeFrom u (r + 1) z v} ≃
      Σ b : Bool,
        {w : Fin r → Bool //
          crossesMultiplicativeFrom u r (z * ballotMultiplier b) w} :=
  ((Fin.consEquiv (fun _ : Fin (r + 1) => Bool)).symm.subtypeEquiv
      (fun v => by
        change
          crossesMultiplicativeFrom u (r + 1) z v ↔
            crossesMultiplicativeFrom u r
              (z * ballotMultiplier (v 0)) (fun i => v i.succ)
        simp [crossesMultiplicativeFrom, hz])).trans
    (Equiv.subtypeProdEquivSigmaSubtype
      (fun b w => crossesMultiplicativeFrom u r
        (z * ballotMultiplier b) w))
noncomputable def threeQuarterLowerTailMass
    (eps : ℝ) (r : ℕ) : ℝ := by
  classical
  exact ∑ v : Fin r → Bool,
    bernoulliWordWeight (3 / 4) v *
      if ((boolSupport v).card : ℝ) ≤ (3 / 4 - eps) * r then 1 else 0
def ballotWordValue {r : ℕ} (z : ℝ) (v : Fin r → Bool) : ℝ :=
  z * ∏ i, ballotMultiplier (v i)
def stoppedBallotValue (u : ℝ) :
    (r : ℕ) → ℝ → (Fin r → Bool) → ℝ
  | 0, z, _ => z
  | r + 1, z, v =>
      if u < z then z
      else stoppedBallotValue u r
        (z * ballotMultiplier (v 0)) (fun i => v i.succ)
noncomputable def safeTerminalSum (u : ℝ) (r : ℕ) (z : ℝ) : ℝ := by
  classical
  exact ∑ v : Fin r → Bool,
    if crossesMultiplicativeFrom u r z v then 0
    else ballotWordValue z v
def reciprocalMaximumEpsilon : ℝ :=
  (3 / 4 - collatzTilt) / 2
def reciprocalMaximumConstant : ℝ :=
  3 / (16 * reciprocalMaximumEpsilon ^ 2)
end
end FirstPassageLinearTransport


