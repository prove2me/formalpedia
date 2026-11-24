-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GeneratedModOfSubsingleton
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GeneratedModOfSubsingleton
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:08.272919+00:00
-- url     : https://prove2.me/theorems/615a263c-7a3d-425e-8c20-632078ee894e
-- title:
--   Generated Mod Of Subsingleton
-- statement:
--   Definitions and structural lemmas for Generated Mod Of Subsingleton, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/GeneratedModOfSubsingleton.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsKleimanScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
def GeneratedMod (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M]
    [Module S M] [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) : Prop :=
  ∀ I : KH.Cell K ι 0, ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d,
    ∃ (t : MRingOver S ι) (a : K → ℕ) (r : ℕ) (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
      t ∈ KH.cellMon S I.1 ∧ IsMultiHomog t a ∧ (∀ j, IsMultiHomog (p j) a) ∧
      (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ t • x = ∑ j, p j • z j I
def H1GenAmple (S : Type) [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M),
    Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
    ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c →
      Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1) ∧ GeneratedMod S ι 𝓜 (e + c • N)
section Point
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [∀ k, Subsingleton (ι k)]
end Point
abbrev pointIdx : Unit → Type := fun _ => Fin 1
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


