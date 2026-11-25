-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_Comp1Scalar
-- name    : Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_Comp1Scalar
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:28:40.708639+00:00
-- url     : https://prove2.me/theorems/b708405b-051c-4c16-a1dd-85f2e8fec5a9
-- title:
--   Comp1 Scalar
-- statement:
--   Definitions and structural lemmas for Comp1 Scalar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/Comp1Scalar.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Germ_ev_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Germ_ev_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
noncomputable section
namespace GlobalTheory.AdditiveBiext
variable {R : Type} [CommRing R] {d : ℕ}
lemma comp1_scalar {n : ℕ} (a : R) (p : Pt R n d) (hp : ∀ i, constantCoeff (p i) = 0) :
    comp1 (fun i => (C a * X ((0:Fin 1), i) : PS R 1 d)) p = fun i => C a * p i := by
  funext i
  have h : ∀ (j : Fin 1) (l : Fin d), constantCoeff ((![p] : Fin 1 → Pt R n d) j l) = 0 := by
    intro j l; fin_cases j; simpa using hp l
  unfold comp1
  rw [ev_mul _ h, ev_C, ev_X _ h]; simp
lemma addLaw_add {n : ℕ} (p q : Pt R n d) (hp : ∀ i, constantCoeff (p i) = 0) (hq : ∀ i, constantCoeff (q i) = 0) :
    (addLaw R d).add p q = fun i => p i + q i := by
  funext i
  have h : ∀ (j : Fin 2) (l : Fin d), constantCoeff ((![p, q] : Fin 2 → Pt R n d) j l) = 0 := by
    intro j l; fin_cases j
    · simpa using hp l
    · simpa using hq l
  show ev ![p, q] (X ((0 : Fin 2), i) + X ((1 : Fin 2), i)) = _
  rw [ev_add _ h, ev_X _ h, ev_X _ h]; simp
def scalarAct (R : Type) [CommRing R] (d : ℕ) : OAct R (addLaw R d) where
  act := fun a i => C a * X ((0:Fin 1), i)
  const := by intro a i; simp
  hom := by
    intro a
    rw [addLaw_add _ _ (by simp [pt]) (by simp [pt]), comp1_scalar _ _ (by simp [pt]), comp1_scalar _ _ (by simp [pt]), comp1_scalar _ _ (by simp [pt]), addLaw_add _ _ (by simp [pt]) (by simp [pt])]
    funext i; ring
  add_act := by
    intro a b
    rw [addLaw_add _ _ (by simp) (by simp)]
    funext i; rw [map_add]; ring
  mul_act := by
    intro a b
    rw [comp1_scalar _ _ (by simp)]
    funext i; rw [map_mul]; ring
  one_act := by funext i; simp [pt]
def additiveFB (R : Type) [CommRing R] [StarRing R] (d : ℕ) : FB R d R := FB.triv (addLaw R d) (scalarAct R d)
end GlobalTheory.AdditiveBiext


