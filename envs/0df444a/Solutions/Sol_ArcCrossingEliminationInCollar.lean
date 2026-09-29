-- Prove2me | solution 1 for ArcCrossingEliminationInCollar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T20:47:06.68506+00:00
-- url     : https://prove2.me/submissions/69ad3a79-4bb5-46be-8e65-3438836882e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ArcCrossingBypassRegionData
import Theorems.Thm_ArcCrossingLocalSideApproaches
import Definitions.Def_PolygonalArc
import Definitions.Def_FinitePolygonalSet
import Definitions.Def_PolygonalPathInGeneralPosition

open Classical
noncomputable section

-- [TABLET NODE: ArcCrossingEliminationInCollar]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingEliminationInCollar.lean#L1-L31
theorem solution
    (K : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalArc)
    (Γ : FinitePolygonalSet) (α : PolygonalPath) :
    IsCompact K →
      Γ.carrier = γ.carrier →
        (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ γ.vertices → v ∈ Γ.points) →
          α.carrier ⊆ Kᶜ →
            α.source ∈ (K ∪ γ.carrier)ᶜ →
              α.target ∈ (K ∪ γ.carrier)ᶜ →
                γ.source ∉ α.carrier →
                  γ.target ∉ α.carrier →
                    PolygonalPathInGeneralPosition α Γ →
                      ((γ.carrier ∩ K =
                          ({γ.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                            γ.target ∉ K) ∨
                        (γ.carrier ∩ K =
                          ({γ.target} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                            γ.source ∉ K)) →
                        ∃ α' : PolygonalPath,
                          α'.source = α.source ∧
                            α'.target = α.target ∧
                              α'.carrier ⊆ (K ∪ γ.carrier)ᶜ := by
  intro hK hΓ hvertices hαK hαsource hαtarget hγsource hγtarget hgp hpendant
  have hXfinite : Set.Finite (α.carrier ∩ γ.carrier) := by
    simpa [hΓ] using hgp.2.2.2.2
  have hαverticesAvoidγ :
      ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ α.vertices → v ∉ γ.carrier := by
    intro v hv hvγ
    exact (hgp.1 v hv) (by simpa [hΓ] using hvγ)
  by_cases hXempty :
      α.carrier ∩ γ.carrier = (∅ : Set (EuclideanSpace ℝ (Fin 2)))
  · refine ⟨α, rfl, rfl, ?_⟩
    intro x hxα
    have hxK : x ∉ K := hαK hxα
    have hxγ : x ∉ γ.carrier := by
      intro hxγ
      have hxX : x ∈ α.carrier ∩ γ.carrier := ⟨hxα, hxγ⟩
      rw [hXempty] at hxX
      exact hxX
    intro hxUnion
    exact hxUnion.elim hxK hxγ
  have hXnonempty : (α.carrier ∩ γ.carrier).Nonempty :=
    Set.nonempty_iff_ne_empty.2 hXempty
  rcases
    ArcCrossingBypassRegionData K γ Γ α
      hK hΓ hvertices hαK hαsource hαtarget hγsource hγtarget hgp hpendant
      hXnonempty with
    ⟨W, cutBefore, cutAfter, hWsub, hWpath, hcut, hordered, hcover⟩
  exact
    ArcCrossingLocalSideApproaches K γ α W cutBefore cutAfter
      hXfinite hαK hαsource hαtarget hWsub hWpath hαverticesAvoidγ hcut hordered hcover
