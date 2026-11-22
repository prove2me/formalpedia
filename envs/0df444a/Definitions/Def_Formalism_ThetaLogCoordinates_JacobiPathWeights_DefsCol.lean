-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_DefsCol
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_DefsCol
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:45.036351+00:00
-- url     : https://prove2.me/theorems/c807be1f-6261-413d-952a-148962d3aae1
-- title:
--   Defs Col
-- statement:
--   Definitions and structural lemmas for Defs Col, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/DefsCol.lean

import Mathlib
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
open Finset
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
abbrev Form (R : Type*) (n : ℕ) := Finset (Fin n) → R
def sg {n : ℕ} (I : Finset (Fin n)) (m : Fin n) : ℤ := (-1) ^ (I.filter fun j => m < j).card
variable {R : Type*} [CommRing R] {n : ℕ}
def oneF : Form R n := fun I => if I = ∅ then 1 else 0
def wedgeF (K : Form R n) (X : Fin n → R) : Form R n :=
  fun I => ∑ m ∈ I, ((sg I m : ℤ) : R) * K (I.erase m) * X m
def contrF (K : Form R n) (X : Fin n → R) : Form R n :=
  fun I => ∑ m ∈ Iᶜ, ((sg I m : ℤ) : R) * X m * K (insert m I)
def powF (K : Form R n) (Q : ℕ) : Form R n := fun I => K I ^ Q
def stepF (up : Bool) (K : Form R n) (X : Fin n → R) : Form R n :=
  if up then wedgeF K X else contrF K X
variable {ι : Type*}
def colUp (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (l : ℕ) : Bool := isVec (lt l) == primal
def colDeg (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) : ℕ → ℤ
  | 0 => 0
  | l + 1 => colDeg primal isVec lt l + (if colUp primal isVec lt l then 1 else -1)
def ColValid (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (L : ℕ) : Prop :=
  ∀ l ≤ L, 0 ≤ colDeg primal isVec lt l ∧
    colDeg primal isVec lt l ≤ (if primal then ((r + K : ℕ) : ℤ) else (K : ℤ))
def colCostly (r : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (l : ℕ) : Prop :=
  if primal then
    (if isVec (lt l) then (r : ℤ) ≤ colDeg primal isVec lt l else colDeg primal isVec lt l ≤ (r : ℤ))
  else isVec (lt l) = true
instance (r : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (l : ℕ) :
    Decidable (colCostly r primal isVec lt l) := by unfold colCostly; infer_instance
def colWord (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (X : ι → Fin n → R) : ℕ → Form R n
  | 0 => oneF
  | l + 1 => stepF (colUp primal isVec lt l) (colWord primal isVec lt X l) (X (lt l))
def planePart {r K : ℕ} (I : Finset (Fin (r + K))) : Finset (Fin r) :=
  univ.filter fun a => Fin.castAdd K a ∈ I
def normalPart {r K : ℕ} (I : Finset (Fin (r + K))) : Finset (Fin K) :=
  univ.filter fun b => Fin.natAdd r b ∈ I
def colPl {r : ℕ} (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (pl : ι → Fin r → R) : ℕ → Form R r
  | 0 => oneF
  | l + 1 =>
    if primal then
      (if isVec (lt l) then
        (if colDeg primal isVec lt l < (r : ℤ) then wedgeF (colPl primal isVec lt pl l) (pl (lt l))
          else colPl primal isVec lt pl l)
      else
        (if colDeg primal isVec lt l ≤ (r : ℤ) then contrF (colPl primal isVec lt pl l) (pl (lt l))
          else colPl primal isVec lt pl l))
    else colPl primal isVec lt pl l
def colTan {K : ℕ} (r : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (nm : ι → Fin K → R) :
    ℕ → Form R K
  | 0 => oneF
  | l + 1 =>
    if primal then
      (if isVec (lt l) then
        (if (r : ℤ) ≤ colDeg primal isVec lt l then wedgeF (colTan r primal isVec lt nm l) (nm (lt l))
          else colTan r primal isVec lt nm l)
      else
        (if (r : ℤ) < colDeg primal isVec lt l then contrF (colTan r primal isVec lt nm l) (nm (lt l))
          else colTan r primal isVec lt nm l))
    else stepF (colUp primal isVec lt l) (colTan r primal isVec lt nm l) (nm (lt l))
def joinF {r K : ℕ} (A : Form R r) (B : Form R K) : Form R (r + K) :=
  fun I => A (planePart I) * B (normalPart I)
def nomPart {r K : ℕ} (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (pl : ι → Fin r → R) (nm : ι → Fin K → R) (l : ℕ) : Fin (r + K) → R :=
  if (isVec (lt l) = true ↔ colCostly r primal isVec lt l) then
    Fin.append (fun _ => 0) (nm (lt l))
  else Fin.append (pl (lt l)) (fun _ => 0)
def symWord {r K : ℕ} (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (pl : ι → Fin r → R) (nm : ι → Fin K → R) : ℕ → Form R (r + K)
  | 0 => oneF
  | l + 1 => stepF (colUp primal isVec lt l) (symWord primal isVec lt pl nm l)
      (nomPart primal isVec lt pl nm l)
def Nominal {r K : ℕ} (primal : Bool) (J : Finset (Fin (r + K))) : Prop :=
  if primal then
    (r ≤ J.card → ∀ a : Fin r, Fin.castAdd K a ∈ J) ∧ (J.card ≤ r → ∀ b : Fin K, Fin.natAdd r b ∉ J)
  else ∀ a : Fin r, Fin.castAdd K a ∉ J
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


