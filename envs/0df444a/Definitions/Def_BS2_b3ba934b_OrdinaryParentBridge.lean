-- Prove2me | Definitions.Def_BS2_b3ba934b_OrdinaryParentBridge
-- name    : BS2_b3ba934b_OrdinaryParentBridge
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:24:15.506564+00:00
-- url     : https://prove2.me/theorems/32fb1110-5cfd-4122-8ce9-be99686416d7
-- title:
--   Sensitivity separation: OrdinaryParentBridge (complete source module)
-- statement:
--   Complete Lean source module `OrdinaryParentBridge` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/OrdinaryParentBridge.lean; original SHA-256 0ff90a6595c898c3e1b50e3d8e33a431225db74a8316121663c0345dca8d093d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exact coordinate and predicate bridge from the accepted ordinary proofs to
   the actual Bool-child family used by the current certificate. -/
import Definitions.Def_BS2_b3ba934b_ArchivedOrdinaryStrict
import Definitions.Def_BS2_b3ba934b_SelectedOrdinaryCaps
import Definitions.Def_BS2_b3ba934b_StrictPositive
import Definitions.Def_BS2_b3ba934b_SelectedBoolCaps

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical
noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

theorem flipsTo_reindex_card (e : I ≃ J) (f : (I → Bool) → Bool)
    (b : Bool) (x : J → Bool) :
    (flipsTo (reindex e f) b x).card = (flipsTo f b (fun i => x (e i))).card := by
  have hs : (flipsTo (reindex e f) b x).map e.symm.toEmbedding =
      flipsTo f b (fun i => x (e i)) := by
    ext i
    simp only [Finset.mem_map_equiv,Equiv.symm_symm,flipsTo,
      Finset.mem_filter,Finset.mem_univ,true_and]
    change f (fun a => flip x {e i} (e a))=b ↔ _
    rw [flip_reindex_singleton]
  simpa only [Finset.card_map] using congrArg Finset.card hs

variable {n k : ℕ}

def ordinaryCoordEquiv : ((Fin k × Fin 2) × I) ≃ ((Fin k × Bool) × I) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) finTwoEquiv) (Equiv.refl _)

theorem ordinary_archive_eq (S : Stage (Fin n) I (Fin k))
    (T : ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
    (ell : Fin k → Fin k → Fin 2)
    (hAdj : ∀ v w, T.Adj v w ↔ S.Adj v w)
    (hLabel : ∀ v w, finTwoEquiv (ell v w)=S.label v w)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ) :
    reindex (ordinaryCoordEquiv (I:=I))
      (ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily T ell F t g q) =
      ordinaryParent S F t g q := by
  funext x
  let xx : ((Fin k × Fin 2) × I) → Bool := fun a => x (ordinaryCoordEquiv a)
  have hchild (v : Fin k) (c : Fin 2) :
      ThreeBoundOrdinaryArchive.OAI.Paper320.recursiveChild xx v c = child x v (finTwoEquiv c) := rfl
  have hfailed (v : Fin k) :
      ThreeBoundOrdinaryArchive.Sensitivity2075.failedGuards T ell F g xx v = guardFailures S F g x v := by
    ext w
    simp only [ThreeBoundOrdinaryArchive.Sensitivity2075.failedGuards,guardFailures,
      Finset.mem_filter,Finset.mem_univ,true_and,hchild,hAdj,hLabel]
  have hiff : ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily T ell F t g q xx=true ↔
      ordinaryParent S F t g q x=true := by
    rw [ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily_true,ordinary_parent_true]
    apply exists_congr
    intro v
    rw [ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantRow_true,hfailed]
    apply and_congr
    · constructor
      · intro h c
        have hh := h (finTwoEquiv.symm c)
        simpa only [hchild,Equiv.apply_symm_apply] using hh
      · intro h c
        simpa only [hchild] using h (finTwoEquiv c)
    · rfl
  change ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily T ell F t g q xx =
    ordinaryParent S F t g q x
  cases h₁ : ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily T ell F t g q xx <;>
    cases h₂ : ordinaryParent S F t g q x <;> simp_all

theorem ordinary_archive_flips_card (S : Stage (Fin n) I (Fin k))
    (T : ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
    (ell : Fin k → Fin k → Fin 2)
    (hAdj : ∀ v w, T.Adj v w ↔ S.Adj v w)
    (hLabel : ∀ v w, finTwoEquiv (ell v w)=S.label v w)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (b : Bool) (x : ((Fin k × Bool) × I) → Bool) :
    (flipsTo (ordinaryParent S F t g q) b x).card =
      (ThreeBoundOrdinaryArchive.ZT.flipsTo
        (ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily T ell F t g q) b
          (fun a => x (ordinaryCoordEquiv a))).card := by
  rw [← ordinary_archive_eq S T ell hAdj hLabel F t g q]
  exact flipsTo_reindex_card _ _ _ _

/-- The exact chosen Fin-2 label agrees with the Bool label in the current recipe. -/
theorem selected_archive_label (v w : Fin 10007) :
    finTwoEquiv (ThreeBoundOrdinarySelected.label v w) = Sensitivity10007BoolCaps.label v w := by
  change finTwoEquiv (Sensitivity10007Labeling.Labeling10007.selectedLabel (v,w)) =
    decide (Sensitivity10007Labeling.Labeling10007.selectedLabel (v,w)=1)
  generalize Sensitivity10007Labeling.Labeling10007.selectedLabel (v,w)=c
  fin_cases c <;> decide

/-- Current constant-target parent representation, with no coordinate change. -/
theorem parent_eq_ordinary (S : Stage (Fin n) I (Fin k))
    (F : Fin n → (I → Bool) → Bool) (l t : Fin n)
    (hconstant : ∀ d u z, S.target l d u z = (F t u && F t z)) :
    parent S F l = ordinaryParent S F t (S.guard l) (S.tolerance l) := by
  funext x
  have hiff : parent S F l x=true ↔ ordinaryParent S F t (S.guard l) (S.tolerance l) x=true := by
    rw [parent_true_iff,ordinary_parent_true]
    apply exists_congr
    intro v
    simp only [hconstant,Bool.and_eq_true,ordinaryRow]
    have hfailed : failed S F l x v=guardFailures S F (S.guard l) x v := rfl
    rw [hfailed]
    constructor
    · rintro ⟨hcount,hfalse,htrue⟩
      exact ⟨fun c => by cases c <;> assumption,hcount⟩
    · rintro ⟨ht,hcount⟩
      exact ⟨hcount,ht false,ht true⟩
  cases h₁ : parent S F l x <;>
    cases h₂ : ordinaryParent S F t (S.guard l) (S.tolerance l) x <;> simp_all


/-- Full ordinary positive-tolerance raw-A theorem for the actual chosen labeling. -/
theorem ordinary_positive_bound (S : Stage (Fin n) I (Fin 10007))
    (hAdj : S.Adj=ThreeBoundOrdinarySelected.Adj)
    (hLabel : S.label=Sensitivity10007BoolCaps.label)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hga : ga ≤ ta)
    (qa q : ℕ) (hq : q ≤ qa) (hpos : 0<q) (hq8 : q ≤ 8)
    (a b s j z : ℕ) (hjs : j ≤ s)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (hs : BBound F gb ga s) (hj : BBound F gb tb j)
    (hcases : ∀ m u, m ≤ (if qa=q then 2*q+3 else 0) → u ≤ 2*q+1 →
      (u+m).choose 2 ≤ q*u+(q+1)*m →
      u ≤ ThreeBoundOrdinaryArchive.ZT.candidateTotalCap q m u →
      (0<u → gb ≠ ta) → ThreeBoundOrdinaryArchive.ZT.positiveCaseCost q m u a b s j ≤ z)
    (x : ((Fin 10007 × Bool) × I) → Bool)
    (hx : ordinaryParent S F ta ga qa x=false) :
    (flipsTo (ordinaryParent S F tb gb q) true x).card ≤ z := by
  have hrel : ∀ v w, ThreeBoundOrdinarySelected.tournament.Adj v w ↔ S.Adj v w := by
    intro v w
    rw [hAdj]
    rfl
  have hlab : ∀ v w, finTwoEquiv (ThreeBoundOrdinarySelected.label v w)=S.label v w := by
    intro v w
    rw [hLabel]
    exact selected_archive_label v w
  rw [ordinary_archive_flips_card S ThreeBoundOrdinarySelected.tournament ThreeBoundOrdinarySelected.label
    hrel hlab F tb gb q true x]
  rw [← ordinary_archive_eq S ThreeBoundOrdinarySelected.tournament ThreeBoundOrdinarySelected.label
    hrel hlab F ta ga qa] at hx
  dsimp only [reindex] at hx
  exact ThreeBoundOrdinaryArchive.Paley11987Verified.CompactBooleanTransfer.ordinary_positive_of_cases
    ThreeBoundOrdinarySelected.tournament ThreeBoundOrdinarySelected.label ThreeBoundOrdinarySelected.labelCaps
    F ⟨fun {i j} {y} hij hy => hF i j hij y hy⟩ ta tb ga gb ht hg hga qa q hq hpos hq8
    a b s j z hjs ha hb hs hj hcases (fun a => x (ordinaryCoordEquiv a)) hx

/-- Complete strict ordinary raw-A theorem, including shared target/guard union. -/
theorem ordinary_zero_equal_bound (S : Stage (Fin n) I (Fin 10007))
    (hAdj : S.Adj=ThreeBoundOrdinarySelected.Adj)
    (hLabel : S.label=Sensitivity10007BoolCaps.label)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hga : ga ≤ ta)
    (a b s j d : ℕ) (hjs : j ≤ s)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (hs : BBound F gb ga s) (hj : BBound F gb tb j) (hd : DBound F gb ga ta tb d)
    (x : ((Fin 10007 × Bool) × I) → Bool)
    (hx : ordinaryParent S F ta ga 0 x=false) :
    (flipsTo (ordinaryParent S F tb gb 0) true x).card ≤
      ThreeBoundOrdinaryArchive.ZT.zeroCost a b s j d := by
  have hrel : ∀ v w, ThreeBoundOrdinarySelected.tournament.Adj v w ↔ S.Adj v w := by
    intro v w
    rw [hAdj]
    rfl
  have hlab : ∀ v w, finTwoEquiv (ThreeBoundOrdinarySelected.label v w)=S.label v w := by
    intro v w
    rw [hLabel]
    exact selected_archive_label v w
  rw [ordinary_archive_flips_card S ThreeBoundOrdinarySelected.tournament ThreeBoundOrdinarySelected.label
    hrel hlab F tb gb 0 true x]
  rw [← ordinary_archive_eq S ThreeBoundOrdinarySelected.tournament ThreeBoundOrdinarySelected.label
    hrel hlab F ta ga 0] at hx
  dsimp only [reindex] at hx
  exact ThreeBoundOrdinaryArchive.Paley11987Verified.CompactBooleanTransfer.ordinary_zero_tolerance
    ThreeBoundOrdinarySelected.tournament ThreeBoundOrdinarySelected.label
    F ⟨fun {i j} {y} hij hy => hF i j hij y hy⟩ ta tb ga gb ht hg hga
    a b s j d hjs ha hb hs hj hd
    (ThreeBoundOrdinarySelected.labelCaps.ordinary 0 (by decide))
    ThreeBoundOrdinarySelected.labelCaps.source ThreeBoundOrdinarySelected.labelCaps.double
    (fun a => x (ordinaryCoordEquiv a)) hx

/-- Unequal tolerance removes all guard candidates and yields the two-term cap. -/
theorem ordinary_zero_strict_bound (S : Stage (Fin n) I (Fin 10007))
    (hAdj : S.Adj=ThreeBoundOrdinarySelected.Adj)
    (hLabel : S.label=Sensitivity10007BoolCaps.label)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hga : ga ≤ ta)
    (qa : ℕ) (hqa : 0<qa) (a b : ℕ)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (x : ((Fin 10007 × Bool) × I) → Bool)
    (hx : ordinaryParent S F ta ga qa x=false) :
    (flipsTo (ordinaryParent S F tb gb 0) true x).card ≤ max (22*b) (a+19*b) := by
  have hrel : ∀ v w, ThreeBoundOrdinarySelected.tournament.Adj v w ↔ S.Adj v w := by
    intro v w
    rw [hAdj]
    rfl
  have hlab : ∀ v w, finTwoEquiv (ThreeBoundOrdinarySelected.label v w)=S.label v w := by
    intro v w
    rw [hLabel]
    exact selected_archive_label v w
  rw [ordinary_archive_flips_card S ThreeBoundOrdinarySelected.tournament ThreeBoundOrdinarySelected.label
    hrel hlab F tb gb 0 true x]
  rw [← ordinary_archive_eq S ThreeBoundOrdinarySelected.tournament ThreeBoundOrdinarySelected.label
    hrel hlab F ta ga qa] at hx
  dsimp only [reindex] at hx
  exact ThreeBoundOrdinaryArchive.ZT.strict_zero_tolerance
    ThreeBoundOrdinarySelected.tournament ThreeBoundOrdinarySelected.label
    F ⟨fun {i j} {y} hij hy => hF i j hij y hy⟩ ta tb ga gb ht hg hga
    qa hqa a b ha hb (ThreeBoundOrdinarySelected.labelCaps.ordinary 0 (by decide))
    ThreeBoundOrdinarySelected.labelCaps.source (fun a => x (ordinaryCoordEquiv a)) hx

end
end ThreeBoundConditional

#print axioms ThreeBoundConditional.ordinary_positive_bound
#print axioms ThreeBoundConditional.ordinary_zero_equal_bound
#print axioms ThreeBoundConditional.ordinary_zero_strict_bound


