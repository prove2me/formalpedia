-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:20.934656+00:00
-- url     : https://prove2.me/theorems/9cf5d9f7-88ff-4db6-b0c4-6d7fa6bf535f
-- title:
--   Chart Glue Lat
-- statement:
--   Definitions and structural lemmas for Chart Glue Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
section Generic
variable {Ω : Type} [Field Ω] {τ : Type} {x : τ → Ω} {r : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
end Generic
section Glue
variable {Ω : Type} [Field Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]
abbrev primeTo (p : Nat.Primes) : Submonoid ℤ := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl
instance (p : S) : IsLocalization (primeTo (p : Nat.Primes)) (o p) := inferInstance
def primeProdErase (S : Finset Nat.Primes) (p : Nat.Primes) : ℤ := ∏ q ∈ S.erase p, ((q : ℕ) : ℤ)
variable (B₀ : ChartBundle o₀ x r E) (Bp : ∀ p, ChartBundle (o p) x r E)
def glueLat (i : τ) : AddSubgroup E := B₀.lat i ⊓ ⨅ p, (Bp p).lat i
variable {B₀ Bp}
end Glue
end GroundTheory.Heights₂.Heights.Model


