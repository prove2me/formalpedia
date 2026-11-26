-- Prove2me | Definitions.Def_TunnellMap_OrbitRanking
-- name    : TunnellMap_OrbitRanking
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:43:05.948445+00:00
-- url     : https://prove2.me/theorems/7c1f7dfe-4a77-4aff-90af-836a251bb2da
-- title:
--   Orbit Ranking
-- statement:
--   Definitions and structural lemmas for Orbit Ranking, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitRanking.lean

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ResidualBalance
import Theorems.Thm_TunnellMap_FreeInvolution_orbit_canonicalRepresentative
import Theorems.Thm_TunnellMap_GloballyRanked_exists_unique_stable
import Theorems.Thm_TunnellMap_representativeEdgeKey_source_orbit_injective
import Theorems.Thm_TunnellMap_representativeEdgeKey_target_orbit_injective

set_option autoImplicit true
namespace TunnellMap
abbrev TripleLexKey := ℤ ×ₗ (ℤ ×ₗ ℤ)
def tripleLexKey (v : Triple) : TripleLexKey :=
  toLex (v.x, toLex (v.y, v.z))
theorem tripleLexKey_injective : Function.Injective tripleLexKey := by
  intro v w h
  apply Triple.ext
  · exact congrArg (fun k : TripleLexKey => (ofLex k).1) h
  · exact congrArg (fun k : TripleLexKey => (ofLex (ofLex k).2).1) h
  · exact congrArg (fun k : TripleLexKey => (ofLex (ofLex k).2).2) h
def bResidualLexKey {n : ℤ} (s : BResidual n) : TripleLexKey :=
  tripleLexKey s.1.1
def aResidualLexKey {n : ℤ} (t : AResidual n) : TripleLexKey :=
  tripleLexKey t.1.1
theorem bResidualLexKey_injective {n : ℤ} :
    Function.Injective (bResidualLexKey (n := n)) := by
  intro s t h
  apply Subtype.ext
  apply Subtype.ext
  exact tripleLexKey_injective h
theorem aResidualLexKey_injective {n : ℤ} :
    Function.Injective (aResidualLexKey (n := n)) := by
  intro s t h
  apply Subtype.ext
  apply Subtype.ext
  exact tripleLexKey_injective h
def canonicalBResidualRepresentative {n : ℤ} :
    (bResidualInvolution n).Orbit → BResidual n :=
  (bResidualInvolution n).canonicalRepresentative bResidualLexKey
    bResidualLexKey_injective
def canonicalAResidualRepresentative {n : ℤ} (hnpos : 0 < n) :
    (aResidualInvolution n hnpos).Orbit → AResidual n :=
  (aResidualInvolution n hnpos).canonicalRepresentative aResidualLexKey
    aResidualLexKey_injective
noncomputable def orbitEdgeKey {n : ℤ} (hnpos : 0 < n)
    (s : (bResidualInvolution n).Orbit)
    (t : (aResidualInvolution n hnpos).Orbit) : DirectionKey :=
  representativeEdgeKey
    (canonicalBResidualRepresentative s)
    (canonicalAResidualRepresentative hnpos t)
noncomputable def residualOrbitRanking {n : ℤ} (hnpos : 0 < n) :
    GloballyRanked DirectionKey (bResidualInvolution n).Orbit
      (aResidualInvolution n hnpos).Orbit where
  rank := orbitEdgeKey hnpos
  source_injective := by
    intro s t₁ t₂ hkey
    have horbit := representativeEdgeKey_source_orbit_injective hnpos
      (canonicalBResidualRepresentative s) hkey
    let AI := aResidualInvolution n hnpos
    calc
      t₁ = AI.orbit (canonicalAResidualRepresentative hnpos t₁) :=
        (AI.orbit_canonicalRepresentative aResidualLexKey
          aResidualLexKey_injective t₁).symm
      _ = AI.orbit (canonicalAResidualRepresentative hnpos t₂) := horbit
      _ = t₂ := AI.orbit_canonicalRepresentative aResidualLexKey
        aResidualLexKey_injective t₂
  target_injective := by
    intro t s₁ s₂ hkey
    have horbit := representativeEdgeKey_target_orbit_injective
      (canonicalAResidualRepresentative hnpos t) hkey
    let BI := bResidualInvolution n
    calc
      s₁ = BI.orbit (canonicalBResidualRepresentative s₁) :=
        (BI.orbit_canonicalRepresentative bResidualLexKey
          bResidualLexKey_injective s₁).symm
      _ = BI.orbit (canonicalBResidualRepresentative s₂) := horbit
      _ = s₂ := BI.orbit_canonicalRepresentative bResidualLexKey
        bResidualLexKey_injective s₂
section Finite
variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]
noncomputable def residualOrbitMatching
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (bResidualInvolution n).Orbit ≃ (aResidualInvolution n hnpos).Orbit := by
  classical
  exact Classical.choose
    (GloballyRanked.exists_unique_stable (residualOrbitRanking hnpos) hcard)
end Finite
end TunnellMap


