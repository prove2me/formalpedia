-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementB
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:52.523978+00:00
-- url     : https://prove2.me/theorems/517d8ed6-ef1e-4bee-889a-0ce19de6c0f4
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/StatementB.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_DefsCol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
def HStrip {n : ℕ} (ν μ : Fin n → ℤ) (b : ℕ) : Prop :=
  (∀ m, μ m ≤ ν m) ∧ (∀ m m' : Fin n, m.val + 1 = m'.val → ν m' ≤ μ m) ∧ ∑ m, ν m - ∑ m, μ m = (b : ℤ)
def IsPath (n : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ) (N : ℕ) : Prop :=
  μ 0 = 0 ∧ (∀ i ≤ N, Antitone (μ i)) ∧
    ∀ i < N, if isVec i then HStrip (μ (i + 1)) (μ i) (B i) else HStrip (μ i) (μ (i + 1)) (B i)
def CondC {r K : ℕ} (isVec : ℕ → Bool) (ν : ℕ → Fin r → ℤ) (κ : ℕ → Fin K → ℤ) (i : ℕ) : Prop :=
  ∀ (a : Fin r) (b : Fin K), a.val + 1 = r → b.val = 0 →
    if isVec i then κ (i + 1) b ≤ ν i a else κ i b ≤ ν (i + 1) a
def StripPathSplitting : Prop :=
  ∀ (r K N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ), 1 ≤ r → 1 ≤ K →
    (∀ μ : ℕ → Fin (r + K) → ℤ,
      IsPath (r + K) isVec B μ N ↔
        ∃ b' b'' : ℕ → ℕ, (∀ i < N, b' i + b'' i = B i) ∧
          IsPath r isVec b' (fun i a => μ i (Fin.castAdd K a)) N ∧
          IsPath K isVec b'' (fun i b => μ i (Fin.natAdd r b)) N ∧
          ∀ i < N, CondC isVec (fun i a => μ i (Fin.castAdd K a)) (fun i b => μ i (Fin.natAdd r b)) i) ∧
    (∀ (ν : ℕ → Fin r → ℤ) (κ : ℕ → Fin K → ℤ),
      (fun i a => (Fin.append (ν i) (κ i)) (Fin.castAdd K a)) = ν ∧
      (fun i b => (Fin.append (ν i) (κ i)) (Fin.natAdd r b)) = κ)
def colHeight {n : ℕ} (μ : Fin n → ℤ) (c : ℤ) : ℕ := (univ.filter fun m => c ≤ μ m).card
def PathColumns : Prop :=
  ∀ (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ), IsPath n isVec B μ N →
    (∀ i ≤ N, ∀ c (m : Fin n), c ≤ μ i m ↔ m.val < colHeight (μ i) c) ∧
    (∀ c : ℤ, colHeight (μ 0) c = if 1 ≤ c then 0 else n) ∧
    (∀ i < N, ∀ c : ℤ,
      if isVec i then
        colHeight (μ (i + 1)) c = colHeight (μ i) c ∨ colHeight (μ (i + 1)) c = colHeight (μ i) c + 1
      else
        colHeight (μ (i + 1)) c = colHeight (μ i) c ∨ colHeight (μ (i + 1)) c + 1 = colHeight (μ i) c) ∧
    (∀ i < N, {c : ℤ | colHeight (μ (i + 1)) c ≠ colHeight (μ i) c}.ncard = B i)
variable {ι : Type*}
def ordW (r K : ℕ) (isVec : ι → Bool) (om : ι → ℝ) : ι × Fin (r + K) → ℝ :=
  fun x => if (isVec x.1 = true ↔ r ≤ x.2.val) then om x.1 else 0
def OrdGe {σ R : Type*} [CommRing R] (w : σ → ℝ) (f : MvPolynomial σ R) (o : ℝ) : Prop :=
  ∀ e ∈ f.support, o ≤ Finsupp.weight w e
def colOrd (r : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (om : ι → ℝ) (l : ℕ) : ℝ :=
  ∑ m ∈ (range l).filter (fun m => colCostly r primal isVec lt m), om (lt m)
def rowX (R : Type*) [CommRing R] (r K : ℕ) (i : ι) : Fin (r + K) → MvPolynomial (ι × Fin (r + K)) R :=
  fun a => X (i, a)
def rowPl (R : Type*) [CommRing R] (r K : ℕ) (i : ι) : Fin r → MvPolynomial (ι × Fin (r + K)) R :=
  fun a => X (i, Fin.castAdd K a)
def rowNm (R : Type*) [CommRing R] (r K : ℕ) (i : ι) : Fin K → MvPolynomial (ι × Fin (r + K)) R :=
  fun b => X (i, Fin.natAdd r b)
def LowestPart (R : Type*) [CommRing R] (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (om : ι → ℝ) (L : ℕ) : Prop :=
  ∀ l ≤ L, ∀ I : Finset (Fin (r + K)),
    OrdGe (ordW r K isVec om) (colWord primal isVec lt (rowX R r K) l I) (colOrd r primal isVec lt om l) ∧
    weightedHomogeneousComponent (ordW r K isVec om) (colOrd r primal isVec lt om l)
        (colWord primal isVec lt (rowX R r K) l I) =
      joinF (colPl primal isVec lt (rowPl R r K) l) (colTan r primal isVec lt (rowNm R r K) l) I
def LowestComponent : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (om : ι → ℝ) (L : ℕ), 1 ≤ r → 1 ≤ K → ColValid r K primal isVec lt L →
    Set.InjOn lt (Set.Iio L) → (∀ l < L, 0 < om (lt l)) →
    (∀ l, l + 1 < L → om (lt (l + 1)) < om (lt l)) →
    LowestPart R r K primal isVec lt om L
def LemmaB2plus : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (om : ι → ℝ) (L : ℕ), 1 ≤ r → 1 ≤ K → ColValid r K primal isVec lt L →
    Set.InjOn lt (Set.Iio L) → (∀ l < L, 0 < om (lt l)) →
    (∀ l, l + 1 < L → om (lt (l + 1)) < om (lt l)) →
    ∀ l < L, ∀ I : Finset (Fin (r + K)),
      (if primal then ((planePart I).card : ℤ) < min (colDeg primal isVec lt (l + 1)) (r : ℤ)
        else (planePart I).Nonempty) →
      OrdGe (ordW r K isVec om) (colWord primal isVec lt (rowX R r K) (l + 1) I)
        (colOrd r primal isVec lt om (l + 1) + om (lt l))
def LemmaB2tie : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (om : ι → ℝ) (L : ℕ), 1 ≤ r → 1 ≤ K → ColValid r K primal isVec lt L →
    Set.InjOn lt (Set.Iio L) → (∀ l < L, 0 < om (lt l)) →
    (∀ l, l + 1 < L → om (lt (l + 1)) ≤ om (lt l)) →
    (∀ l, l + 1 < L → colCostly r primal isVec lt (l + 1) → om (lt (l + 1)) < om (lt l)) →
    LowestPart R r K primal isVec lt om L
def LemmaB2necessity : Prop :=
  ¬ LowestPart ℤ 1 1 true (fun i : Fin 2 => decide (i = 0)) (fun l => if l = 0 then 0 else 1)
      (fun _ => 1) 2
def FirstStepFree : Prop :=
  ∀ (ι : Type) (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (L : ℕ), 1 ≤ r → 1 ≤ L →
    ColValid r K primal isVec lt L → ¬ colCostly r primal isVec lt 0
def SymbolWordSupport : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) [DecidableEq ι] (r K : ℕ) (primal : Bool) (isVec : ι → Bool)
    (lt : ℕ → ι) (L : ℕ), 1 ≤ r → 1 ≤ K → ColValid r K primal isVec lt L → Set.InjOn lt (Set.Iio L) →
    ∀ l ≤ L, ∀ I : Finset (Fin (r + K)),
      (symWord primal isVec lt (rowPl R r K) (rowNm R r K) l I ≠ 0 →
        Nominal primal I ∧ (I.card : ℤ) = colDeg primal isVec lt l) ∧
      ∀ i : ι, IsWeightedHomogeneous (fun x : ι × Fin (r + K) => if x.1 = i then 1 else 0)
        (symWord primal isVec lt (rowPl R r K) (rowNm R r K) l I)
        (if ∃ m < l, lt m = i then 1 else 0)
def SymbolWordJoin : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (pl : ι → Fin r → R) (nm : ι → Fin K → R) (L : ℕ), 1 ≤ r → 1 ≤ K → ColValid r K primal isVec lt L →
    ∀ l ≤ L, symWord primal isVec lt pl nm l =
      joinF (colPl primal isVec lt pl l) (colTan r primal isVec lt nm l)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


