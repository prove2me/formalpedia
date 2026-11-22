-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_IndefiniteWeightData
-- name    : Formalism_LocalToGlobal_IndefiniteReal_IndefiniteWeightData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:27.761228+00:00
-- url     : https://prove2.me/theorems/e354873d-da18-471e-9dd6-5e5bbaea98e3
-- title:
--   Indefinite Weight Data
-- statement:
--   Definitions and structural lemmas for Indefinite Weight Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/IndefiniteWeightData.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.IndefR.IndefiniteWeightData
structure WeightData where
  k : ℕ
  m : ℕ
  t : ℕ
  j : ℕ
  e : ℤ
  v : ℕ → ℤ
  b : ℕ → ℤ
namespace WeightData
variable (D : WeightData)
def p : ℕ := D.k + D.j - 1
def q : ℕ := D.m - D.j
def r : ℕ := D.k + D.m - 1
def nV : ℕ := D.r + D.t
def lam (i : ℕ) : ℤ := if i ≤ D.k - 1 then D.v (i + 1) else -D.b (i - (D.k - 1))
def lamGeo (i : ℕ) : ℚ := (D.lam i : ℚ) + D.e
def aPlus (i : ℕ) : ℚ :=
  ((D.lam i : ℚ) + D.e) - ((D.nV : ℚ) + 1 - 2 * (i : ℚ)) / 2 - ((D.p : ℚ) - D.q) / 2
def aMinus (s : ℕ) : ℚ :=
  ((D.b (D.j + (D.q + 1 - s)) : ℚ) - D.e) + (1 - (D.t : ℚ) - 2 * ((D.q + 1 - s : ℕ) : ℚ)) / 2
def fibreWt (i : ℕ) : ℚ := if i ≤ D.p then -D.aPlus (D.p + 1 - i) else D.aMinus (i - D.p)
def blockDual (w : ℕ → ℚ) (i : ℕ) : ℚ :=
  if i ≤ D.p then -w (D.p + 1 - i) else -w (D.p + (D.q + 1 - (i - D.p)))
def deDual (i : ℕ) : ℚ := if i ≤ D.p then (D.nV : ℚ) / 2 else -(D.nV : ℚ) / 2
def LamGeo (i : ℕ) : ℚ := D.blockDual D.fibreWt i + D.deDual i
def LamGeoFormula (i : ℕ) : ℚ :=
  if i ≤ D.p then D.aPlus i + (D.nV : ℚ) / 2 else -D.aMinus (D.q + 1 - (i - D.p)) - (D.nV : ℚ) / 2
def rhoN (i : ℕ) : ℚ := if i ≤ D.p then (D.q : ℚ) / 2 else -(D.p : ℚ) / 2
def rhoC (i : ℕ) : ℚ :=
  if i ≤ D.p then ((D.p : ℚ) + 1 - 2 * (i : ℚ)) / 2
  else ((D.q : ℚ) + 1 - 2 * ((i : ℚ) - D.p)) / 2
def dTau : ℚ := ((D.p : ℚ) - D.q) / 2 - D.e - 1 / 2
def thetaWt (i : ℕ) : ℚ :=
  if i ≤ D.p then D.aPlus i
  else if i ≤ D.p + D.t then 0
  else -D.aMinus (D.q + 1 - (i - D.p - D.t))
def lamPrime (i : ℕ) : ℚ := D.thetaWt i + D.dTau
def rhoNV (i : ℕ) : ℚ := ((D.nV : ℚ) + 1 - 2 * (i : ℚ)) / 2
def uSideTarget (i : ℕ) : ℚ :=
  if i ≤ D.p then (D.lam i : ℚ)
  else if i ≤ D.p + D.t then -(D.e : ℚ) + ((D.t : ℚ) + 1 - 2 * ((i : ℚ) - D.p)) / 2
  else -(D.b (D.j + (i - D.p - D.t)) : ℚ)
def Hyp : Prop :=
  1 ≤ D.k ∧ 1 ≤ D.j ∧ D.j ≤ D.m ∧ Odd D.r ∧ Odd D.t ∧
  (∀ i : ℕ, 1 ≤ i → i < D.r → D.lam (i + 1) < D.lam i) ∧
  D.b D.j < D.e ∧ (D.j < D.m → D.e < D.b (D.j + 1))
def GapHyp : Prop :=
  ((D.t : ℚ) + 3) / 2 ≤ (D.e : ℚ) - D.b D.j ∧
  (D.j < D.m → ((D.t : ℚ) + 3) / 2 ≤ (D.b (D.j + 1) : ℚ) - D.e)
def Concl : Prop :=
  (∀ i : ℕ, 1 ≤ i → i ≤ D.r → D.LamGeo i = D.LamGeoFormula i) ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ D.r → D.LamGeoFormula i = D.lamGeo i + D.rhoN i - D.rhoC i) ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ D.p → 0 < D.lamGeo i) ∧
  (∀ i : ℕ, D.p < i → i ≤ D.r → D.lamGeo i < 0) ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ D.p → ∃ z : ℤ, D.aPlus i = z) ∧
  (∀ s : ℕ, 1 ≤ s → s ≤ D.q → ∃ z : ℤ, D.aMinus s = z) ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ D.r → ∃ z : ℤ, D.LamGeo i = z) ∧
  (∀ i : ℕ, 1 ≤ i → i < D.p → D.LamGeo (i + 1) ≤ D.LamGeo i) ∧
  (∀ i : ℕ, D.p < i → i < D.r → D.LamGeo (i + 1) ≤ D.LamGeo i)
def ThetaSideConcl : Prop :=
  (∀ i : ℕ, 1 ≤ i → i ≤ D.nV →
      D.thetaWt i + ((D.p : ℚ) - D.q) / 2 - D.e + D.rhoNV i = D.uSideTarget i) ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ D.nV → D.lamPrime i + D.rhoNV i = D.uSideTarget i - 1 / 2) ∧
  (∃ z : ℤ, D.dTau = z) ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ D.nV → ∃ z : ℤ, D.lamPrime i = z) ∧
  (∀ i : ℕ, 1 ≤ i → i < D.nV → D.lamPrime (i + 1) ≤ D.lamPrime i) ∧
  (∀ i : ℕ, 1 ≤ i → i < D.nV →
      D.lamPrime (i + 1) + D.rhoNV (i + 1) < D.lamPrime i + D.rhoNV i)
end WeightData
def LowestTypeStatement : Prop := ∀ D : WeightData, D.Hyp → D.Concl
def ThetaSideStatement : Prop := ∀ D : WeightData, D.Hyp → D.GapHyp → D.ThetaSideConcl
def Statement2 : Prop := LowestTypeStatement ∧ ThetaSideStatement
end Formalism.IndefR.IndefiniteWeightData


