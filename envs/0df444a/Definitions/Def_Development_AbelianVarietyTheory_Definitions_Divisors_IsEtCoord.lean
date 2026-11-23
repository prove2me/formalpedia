-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsEtCoord
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_IsEtCoord
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:29.762676+00:00
-- url     : https://prove2.me/theorems/137e401b-834b-4f47-955a-421b6e2cc439
-- title:
--   Is Et Coord
-- statement:
--   Definitions and structural lemmas for Is Et Coord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsEtCoord.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.LogPair
variable {R : Type} [CommRing R] {X : Scheme.{0}}
def cstOn (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top).hom
def IsEtCoord (p : X ⟶ Sp R) (U : X.Opens) {d : ℕ} (t : Fin d → Γ(X, U)) : Prop :=
  (MvPolynomial.eval₂Hom (cstOn p U) t).Etale
structure SncChart (p : X ⟶ Sp R) (d : ℕ) {s : ℕ} (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) where

  U : X.Opens
  affine : IsAffineOpen U

  t : Fin d → Γ(X, U)
  etale : IsEtCoord p U t

  c : ∀ i, (L i).ι
  le : ∀ i, U ≤ (L i).U (c i)

  e : Fin s → Option (Fin d)
  inj : ∀ i j a, e i = some a → e j = some a → i = j

  u : Fin s → Γ(X, U)ˣ
  eq : ∀ i, resG X (le i) ((σ i).f (c i)) = (u i : Γ(X, U)) * (e i).elim 1 t
structure RelSnc (p : X ⟶ Sp R) (d : ℕ) {s : ℕ} (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) : Prop where
  isLB : ∀ i, (L i).IsLB
  chart : ∀ x : X, ∃ C : SncChart p d L σ, x ∈ C.U
end GlobalTheory.LogPair


