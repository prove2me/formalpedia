-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P24
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P24
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T22:54:50.579688+00:00
-- url     : https://prove2.me/theorems/4a86ded1-6283-4c5d-b57d-1745d99c7662
-- title:
--   Definitions for Decomposition of Normal Operators and Its Application to Spectral Theorem
-- statement:
--   The objects the formalized statements of *Decomposition of Normal Operators and Its Application to Spectral Theorem* (arXiv:2006.04644) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `pvmOperatorIntegral`: The PVM-to-operator integral, PDF pp.1,3–4: evaluate the unique full Borel calculus agreeing with the PVM on indicators. The accepted calculus_from_pvm supplies existence and uniqueness whenever PVM E holds. The zero-graph fallback is used only on invalid inputs. The returned graph includes the full natural domain; this is not a Bochner integral with a default value outside its domain. Distinct from accepted Bridge50.P02.spectralIntegral, which takes finite matrices A,B and a real function and returns a real scalar (line 58); that quantity cannot represent an unbounded operator graph on arbitrary H.
--   - `IsProductSpectralMeasure`: The defining property of the product spectral measure, PDF p.3, Theorem 3.1: normalized strong PVM additivity and the rectangle identity.
--   - `productSpectralMeasure`: The source's product PVM, PDF p.3, definition after Theorem 3.1. Choose a map with exactly the defining PVM and rectangle properties; return the zero-graph map if there is none. Theorem 3.2 below includes existence, uniqueness and the selected map's specification in its conclusion. Thus its integral can never silently use this fallback under the theorem's hypotheses.
-- source:
--   Decomposition of Normal Operators and Its Application to Spectral Theorem, arXiv:2006.04644v2, https://arxiv.org/abs/2006.04644v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

/-! Nakagawa, arXiv:2006.04644v2, PDF pp.1–4.
The accepted graph calculus retains actual domains on arbitrary Hilbert spaces.
The three normal-operator statements use the explicit closedness correction
recorded below. Compilation is pending the batch mechanical handoff. -/

noncomputable section

attribute [local instance] Classical.propDecidable

open Set MeasureTheory
open scoped Topology
open QAlgorithms.Papers.Independent.Claimed50.P05

namespace QAlgorithms.Papers.Independent.Intakenext100.P24

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The PVM-to-operator integral, PDF pp.1,3–4: evaluate the unique full Borel calculus
agreeing with the PVM on indicators. The accepted calculus_from_pvm supplies
existence and uniqueness whenever PVM E holds. The zero-graph fallback is used
only on invalid inputs. The returned graph includes the full natural domain;
this is not a Bochner integral with a default value outside its domain.
Distinct from accepted Bridge50.P02.spectralIntegral, which takes finite
matrices A,B and a real function and returns a real scalar (line 58); that
quantity cannot represent an unbounded operator graph on arbitrary H. -/
def pvmOperatorIntegral
    (E : {A : Set X // MeasurableSet A} → Relation H)
    (f : QAlgorithms.Papers.Independent.Claimed50.P05.Symbol X ℂ) : Relation H :=
  if h : ∃ F : QAlgorithms.Papers.Independent.Claimed50.P05.Symbol X ℂ → Relation H,
      Calculus F ∧ ∀ A (hA : MeasurableSet A), E ⟨A, hA⟩ = F (indicator A hA) then
    (Classical.choose h) f
  else zeroGraph

-- `calculus_from_pvm` (Claimed50.P05) is an open statement on prove2me, so this check takes its conclusion as a hypothesis
example (E : {A : Set X // MeasurableSet A} → Relation H)
    (hcalc : ∃! F : QAlgorithms.Papers.Independent.Claimed50.P05.Symbol X ℂ → Relation H,
      Calculus F ∧ ∀ B (hB : MeasurableSet B), E ⟨B, hB⟩ = F (indicator B hB)) (A : Set X) (hA : MeasurableSet A) :
    pvmOperatorIntegral E (indicator A hA) = E ⟨A, hA⟩ := by
  classical
  have hex : ∃ F : QAlgorithms.Papers.Independent.Claimed50.P05.Symbol X ℂ → Relation H,
      Calculus F ∧ ∀ B (hB : MeasurableSet B), E ⟨B, hB⟩ = F (indicator B hB) :=
    hcalc.exists
  unfold pvmOperatorIntegral
  rw [dif_pos hex]
  exact ((Classical.choose_spec hex).2 A hA).symm

-- `calculus_from_pvm` (Claimed50.P05) is an open statement on prove2me, so this check takes its conclusion as a hypothesis
example (E : {A : Set X // MeasurableSet A} → Relation H)
    (hcalc : ∃! F : QAlgorithms.Papers.Independent.Claimed50.P05.Symbol X ℂ → Relation H,
      Calculus F ∧ ∀ B (hB : MeasurableSet B), E ⟨B, hB⟩ = F (indicator B hB)) :
    pvmOperatorIntegral E (constant (1 : ℂ)) = identity := by
  classical
  have hex : ∃ F : QAlgorithms.Papers.Independent.Claimed50.P05.Symbol X ℂ → Relation H,
      Calculus F ∧ ∀ B (hB : MeasurableSet B), E ⟨B, hB⟩ = F (indicator B hB) :=
    hcalc.exists
  unfold pvmOperatorIntegral
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).1.2.1.1

/-- The defining property of the product spectral measure, PDF p.3,
Theorem 3.1: normalized strong PVM additivity and the rectangle identity. -/
def IsProductSpectralMeasure
    (E1 : {A : Set X // MeasurableSet A} → Relation H)
    (E2 : {B : Set Y // MeasurableSet B} → Relation H)
    (P : {C : Set (X × Y) // MeasurableSet C} → Relation H) : Prop :=
  PVM (k := ℂ) P ∧
  ∀ (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B),
    P ⟨A ×ˢ B, hA.prod hB⟩ = mul (E1 ⟨A, hA⟩) (E2 ⟨B, hB⟩)

/-- The source's product PVM, PDF p.3, definition after Theorem 3.1.
Choose a map with exactly the defining PVM and rectangle properties; return
the zero-graph map if there is none. Theorem 3.2 below includes existence,
uniqueness and the selected map's specification in its conclusion. Thus its
integral can never silently use this fallback under the theorem's hypotheses. -/
def productSpectralMeasure
    (E1 : {A : Set X // MeasurableSet A} → Relation H)
    (E2 : {B : Set Y // MeasurableSet B} → Relation H) :
    {C : Set (X × Y) // MeasurableSet C} → Relation H :=
  if h : ∃ P, IsProductSpectralMeasure E1 E2 P then Classical.choose h
  else fun _ => zeroGraph

example (E1 : {A : Set X // MeasurableSet A} → Relation H)
    (E2 : {B : Set Y // MeasurableSet B} → Relation H)
    (hex : ∃ P, IsProductSpectralMeasure E1 E2 P) :
    IsProductSpectralMeasure E1 E2 (productSpectralMeasure E1 E2) := by
  classical
  unfold productSpectralMeasure
  rw [dif_pos hex]
  exact Classical.choose_spec hex

example (E1 : {A : Set X // MeasurableSet A} → Relation H)
    (E2 : {B : Set Y // MeasurableSet B} → Relation H)
    (hE1 : PVM (k := ℂ) E1) (hE2 : PVM (k := ℂ) E2)
    (P : {C : Set (X × Y) // MeasurableSet C} → Relation H)
    (hP : IsProductSpectralMeasure E1 E2 P) :
    P ⟨(Set.univ : Set X) ×ˢ (Set.univ : Set Y),
      MeasurableSet.univ.prod MeasurableSet.univ⟩ = identity := by
  have h1 : E1 ⟨Set.univ, MeasurableSet.univ⟩ = identity := hE1.2.2.1
  have h2 : E2 ⟨Set.univ, MeasurableSet.univ⟩ = identity := hE2.2.2.1
  have hid : mul (identity : Relation H) identity = identity := by
    ext p
    constructor
    · rintro ⟨z, hz, hp⟩
      exact hp.trans hz
    · intro hp
      exact ⟨p.1, rfl, hp⟩
  simpa only [h1, h2, hid] using
    hP.2 Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ

end QAlgorithms.Papers.Independent.Intakenext100.P24


