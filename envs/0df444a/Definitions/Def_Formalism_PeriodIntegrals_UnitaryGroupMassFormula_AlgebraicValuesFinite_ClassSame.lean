-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:18.895895+00:00
-- url     : https://prove2.me/theorems/5bf62c22-9ce7-484d-8a30-c5fb44209db7
-- title:
--   Class Same
-- statement:
--   Definitions and structural lemmas for Class Same, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/ClassSame.lean

import Definitions.Def_Formalism_PeriodIntegrals_AlgValsFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1
namespace PI.AlgValsFin.W
variable (L : Type) [Field L] [NumberField L]
def UFin : Set (Ideles L) :=
  {x | (x : AdeleRing (𝓞 L) L).1 = 1 ∧
    ∀ v : HeightOneSpectrum (𝓞 L), Valued.v ((x : AdeleRing (𝓞 L) L).2 v) = 1}
def TorsUnits : Prop :=
  ∀ χ : HChar L, ∃ N : ℕ, 0 < N ∧ ∀ x ∈ UFin L, (χ.1 x) ^ N = 1
def Decomp : Prop :=
  ∀ (k : Lˣ) (T : Finset (HeightOneSpectrum (𝓞 L))), (∀ v, v ∉ T → ordF v k = 0) →
    ∃ r ∈ UFin L, diagUnits L k = infDiag k * (∏ v ∈ T, localIdele L v (atFin v k)) * r
def LocVal : Prop :=
  ∀ (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ), χ.UnrAt v →
    χ.loc v (atFin v k) = χ.val v ^ ordF v k
def ProdNorm : Prop :=
  ∀ (k : Lˣ) (T : Finset (HeightOneSpectrum (𝓞 L))), (∀ v, v ∉ T → ordF v k = 0) →
    ∏ φ : L →+* ℂ, ‖φ (k : L)‖ = ∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ordF v k
open Classical in

def ClassPow : Prop :=
  ∃ h : ℕ, 0 < h ∧ ∀ v : HeightOneSpectrum (𝓞 L), ∃ k : Lˣ,
    ∀ u : HeightOneSpectrum (𝓞 L), ordF u k = if u = v then (h : ℤ) else 0
open Classical in

def ClassSame : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (c : HeightOneSpectrum (𝓞 L) → ι),
    ∀ v w, c v = c w → ∃ k : Lˣ, ∀ u : HeightOneSpectrum (𝓞 L),
      ordF u k = (if u = v then 1 else 0) - (if u = w then 1 else 0)
def KeyId : Prop :=
  ∀ (χ : HChar L) (s : ℝ) (m : (L →+* ℂ) → ℤ),
    (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) * ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ) =
      ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) →
    ∀ (k : Lˣ) (T : Finset (HeightOneSpectrum (𝓞 L))), (∀ v, v ∉ T → ordF v k = 0) →
      (∀ v ∈ T, χ.UnrAt v) →
      ∃ r ∈ UFin L, (∏ v ∈ T, χ.valTw s v ^ ordF v k) * (∏ φ : L →+* ℂ, φ (k : L) ^ m φ) *
        ((χ.1 r : ℂˣ) : ℂ) = 1
def KeyIdOf : Prop := Decomp L → LocVal L → ProdNorm L → KeyId L
def Assemble : Prop := TorsUnits L → KeyId L → ClassPow L → ClassSame L → AlgValsFin L
end PI.AlgValsFin.W


