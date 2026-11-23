-- Prove2me | solution 1 for ArcKayles192.PSPACE.reductionInstance_correct
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:24:31.820138+00:00
-- url     : https://prove2.me/submissions/dd9d707a-4b05-440c-bd2a-18107bb3d498
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_ArcKayles192_PSPACE_PosCNF
import Definitions.Def_ArcKayles192_PSPACE_ReductionInstance
import Theorems.Thm_ArcKayles192_PSPACE_claim_9
import Theorems.Thm_ArcKayles192_PSPACE_claim_10
import Theorems.Thm_ArcKayles192_PSPACE_oddPad_outcome

open ArcKayles192.PSPACE

private lemma firstPlayerWins_map {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ≃ W)
    (hAdj : ∀ u v, H.Adj (e u) (e v) ↔ G.Adj u v) (S : Finset V) :
    ArcKayles192.PSPACE.FirstPlayerWins H (S.map e.toEmbedding) ↔
      ArcKayles192.PSPACE.FirstPlayerWins G S := by
  generalize hn : S.card = n
  induction n using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    have hmap (u v : V) : S.map e.toEmbedding \ {e u, e v} =
        (S \ {u, v}).map e.toEmbedding := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_map]
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hx⟩
        exact ⟨y, ⟨hy, by simpa using hx⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hxy⟩, rfl⟩
        exact ⟨⟨y, hy, rfl⟩, by simpa using hxy⟩
    rw [ArcKayles192.PSPACE.FirstPlayerWins, ArcKayles192.PSPACE.FirstPlayerWins]
    constructor
    · rintro ⟨u, v, ⟨hu, hv, huv⟩, hlose⟩
      obtain ⟨u', hu', rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
      refine ⟨u', v', ⟨hu', hv', (hAdj u' v').mp huv⟩, ?_⟩
      change ¬ArcKayles192.PSPACE.FirstPlayerWins H (S.map e.toEmbedding \ {e u', e v'}) at hlose
      rw [hmap] at hlose
      intro hwin
      have hlt : (S \ {u', v'}).card < n := by
        rw [← hn]
        exact card_sdiff_pair_lt v' hu'
      exact hlose ((ih _ hlt _ rfl).mpr hwin)
    · rintro ⟨u, v, ⟨hu, hv, huv⟩, hlose⟩
      refine ⟨e u, e v, ⟨Finset.mem_map.mpr ⟨u, hu, rfl⟩,
        Finset.mem_map.mpr ⟨v, hv, rfl⟩, (hAdj u v).mpr huv⟩, ?_⟩
      rw [hmap]
      intro hwin
      have hlt : (S \ {u, v}).card < n := by
        rw [← hn]
        exact card_sdiff_pair_lt v hu
      exact hlose ((ih _ hlt _ rfl).mp hwin)

private lemma graphInstance_outcome (φ : PosCNF) :
    arcKayles (graphInstance φ) ↔ FirstPlayerWins (Gphi φ) Finset.univ := by
  have h := firstPlayerWins_map (Gphi φ) (graphInstance φ).graph (vtxEquiv φ.n φ.m)
    (fun u w => graphInstance_adj φ u w) Finset.univ
  have he : (Finset.univ.map (vtxEquiv φ.n φ.m).toEmbedding) =
      (Finset.univ : Finset (Fin (vertexCount φ.n φ.m))) := by
    ext x
    simp
  change FirstPlayerWins (graphInstance φ).graph Finset.univ ↔ _
  exact he ▸ h

private lemma trueWins_of_no_clauses (φ : PosCNF) (hm : φ.m = 0)
    (T F : Finset (Fin φ.n)) (b : Bool) : PosCNF.TrueWins φ T F b := by
  generalize hn : (Finset.univ \ (T ∪ F)).card = c
  induction c using Nat.strong_induction_on generalizing T F b with
  | _ c ih =>
    rw [PosCNF.TrueWins]
    split_ifs with hterm hb
    · intro j
      exact Fin.elim0 (Fin.cast hm j)
    · have hx : ∃ x : Fin φ.n, x ∉ T ∪ F := by
        by_contra h
        apply hterm
        apply Finset.eq_univ_of_forall
        intro x
        by_contra hx
        exact h ⟨x, hx⟩
      obtain ⟨x, hx⟩ := hx
      refine ⟨x, hx, ?_⟩
      apply ih (Finset.univ \ (insert x T ∪ F)).card
      · rw [← hn]
        exact PosCNF.card_unclaimed_lt hx _ _ (by rw [Finset.insert_union])
      · rfl
    · intro x hx
      apply ih (Finset.univ \ (T ∪ insert x F)).card
      · rw [← hn]
        exact PosCNF.card_unclaimed_lt hx _ _ (by rw [Finset.union_insert])
      · rfl

private lemma oneEdge_winning : arcKayles oneEdgeInstance := by
  rw [arcKayles, FirstPlayerWins]
  let i0 : Fin oneEdgeInstance.n := ⟨0, by decide⟩
  let i1 : Fin oneEdgeInstance.n := ⟨1, by decide⟩
  refine ⟨i0, i1, ⟨by simp, by simp, ?_⟩, ?_⟩
  · change decide (i0 ≠ i1) = true
    decide
  · have he : (Finset.univ : Finset (Fin oneEdgeInstance.n)) \ {i0, i1} = ∅ := by decide
    rw [he]
    rw [FirstPlayerWins]
    simp

theorem solution (φ : PosCNF) : posCNF φ ↔ arcKayles (reductionInstance φ) := by
  by_cases hm : φ.m = 0
  · rw [reductionInstance, if_pos hm]
    exact ⟨fun _ => oneEdge_winning, fun _ => trueWins_of_no_clauses φ hm ∅ ∅ true⟩
  · have hmpos : 0 < φ.m := Nat.pos_of_ne_zero hm
    rw [reductionInstance, if_neg hm, graphInstance_outcome, ← oddPad_outcome φ]
    constructor
    · intro hT
      exact claim_10 _ (oddPad_odd φ hmpos) hT
    · intro hW
      by_contra hF
      exact (claim_9 _ (oddPad_odd φ hmpos) hF) hW
