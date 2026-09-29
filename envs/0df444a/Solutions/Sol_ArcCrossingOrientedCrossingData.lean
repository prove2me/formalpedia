-- Prove2me | solution 1 for ArcCrossingOrientedCrossingData
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T21:51:39.138996+00:00
-- url     : https://prove2.me/submissions/4e6dad26-2350-4c59-b4bf-5305a1232735

import Definitions.Def_PolygonalArcReverse
import Definitions.Def_PolygonalPathInGeneralPosition

open Classical
noncomputable section

-- [TABLET NODE: ArcCrossingOrientedCrossingData]
theorem solution
    (K : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalArc)
    (Γ : FinitePolygonalSet) (α : PolygonalPath) :
    Γ.carrier = γ.carrier →
      (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ γ.vertices → v ∈ Γ.points) →
        γ.source ∉ α.carrier →
          γ.target ∉ α.carrier →
            PolygonalPathInGeneralPosition α Γ →
              ((γ.carrier ∩ K =
                  ({γ.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                    γ.target ∉ K) ∨
                (γ.carrier ∩ K =
                  ({γ.target} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                    γ.source ∉ K)) →
                ∃ δ : PolygonalArc,
                  δ.carrier = γ.carrier ∧
                    δ.relativeInterior = γ.relativeInterior ∧
                      (∀ v : EuclideanSpace ℝ (Fin 2),
                        v ∈ δ.vertices → v ∈ Γ.points) ∧
                        (∀ v : EuclideanSpace ℝ (Fin 2),
                          v ∈ δ.vertices → v ∉ α.carrier) ∧
                          Set.Finite (α.carrier ∩ δ.carrier) ∧
                            δ.source ∉ α.carrier ∧
                              δ.target ∉ α.carrier ∧
                                δ.carrier ∩ K =
                                  ({δ.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                                  δ.target ∉ K := by
  intro hΓcarrier hγvertices hγsourceα hγtargetα hgp hattach
  have hfiniteΓ : Set.Finite (α.carrier ∩ Γ.carrier) := hgp.2.2.2.2
  have hpointsAvoid :
      ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ Γ.points → v ∉ α.carrier := hgp.2.1
  have hγverticesAvoid :
      ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ γ.vertices → v ∉ α.carrier := by
    intro v hv
    exact hpointsAvoid v (hγvertices v hv)
  rcases hattach with hsource | htarget
  · refine ⟨γ, rfl, rfl, hγvertices, hγverticesAvoid, ?_, hγsourceα,
      hγtargetα, hsource.1, hsource.2⟩
    simpa [hΓcarrier] using hfiniteΓ
  · refine ⟨PolygonalArcReverse γ, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      exact hγvertices v (by simpa [PolygonalArcReverse] using hv)
    · intro v hv
      exact hγverticesAvoid v (by simpa [PolygonalArcReverse] using hv)
    · simpa [PolygonalArcReverse, hΓcarrier] using hfiniteΓ
    · simpa [PolygonalArcReverse] using hγtargetα
    · simpa [PolygonalArcReverse] using hγsourceα
    · simpa [PolygonalArcReverse] using htarget.1
    · simpa [PolygonalArcReverse] using htarget.2
