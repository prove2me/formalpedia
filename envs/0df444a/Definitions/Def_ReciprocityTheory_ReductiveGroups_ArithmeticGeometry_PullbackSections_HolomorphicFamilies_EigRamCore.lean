-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:04:11.362558+00:00
-- url     : https://prove2.me/theorems/afb57aba-dd88-4bdc-ab16-bb01143e5f47
-- title:
--   Eig Ram Core
-- statement:
--   Definitions and structural lemmas for Eig Ram Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamCore.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
section Mat
variable {O k : Type} [CommRing O] [CommRing k] {d : ℕ}
def actD (M : O →+* Matrix (Fin d) (Fin d) k) {n : ℕ} (b : Fin n → O) (c : Fin n → k) :
    Matrix (Fin d) (Fin d) k :=
  ∑ i, c i • M (b i)
def evD (χ : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k) : k := ∑ i, c i * χ (b i)
def IsEqv (χ : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k) : Prop :=
  ∀ a : O, ∃ m : Fin n → Fin n → ℤ, (∀ i, a * b i = ∑ j, m i j • b j) ∧
    ∀ j, ∑ i, (m i j : k) * c i = χ a * c j
end Mat
section Pair
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [Field k] [Algebra ℚ k] [Algebra R k]
def actP (B : FB R d O) {n : ℕ} (b : Fin n → O) (c : Fin n → k) (ξ : (Fin d → k) × (Fin d → k)) :
    (Fin d → k) × (Fin d → k) :=
  ((actD (EigA.dActH k B) b c).mulVec ξ.1, (actD (EigA.dActS k B) b c).mulVec ξ.2)
end Pair
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam


