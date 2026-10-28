-- Prove2me | Definitions.Def_BS2_b3ba934b_ArchivedOrdinaryZero
-- name    : BS2_b3ba934b_ArchivedOrdinaryZero
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:03:09.453107+00:00
-- url     : https://prove2.me/theorems/d96958af-c840-4c99-bbcc-f1ea6b2e924a
-- title:
--   Sensitivity separation: ArchivedOrdinaryZero (complete source module)
-- statement:
--   Complete Lean source module `ArchivedOrdinaryZero` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ArchivedOrdinaryZero.lean; original SHA-256 3d50b311c7ac8a52a9f924c89576c84e7131724e045e1bccdd469a1d32c2b4dd; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/
import Definitions.Def_BS2_b3ba934b_ArchivedOrdinaryPositive

open OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- Sol_Paley11987Verified_CompactBooleanTransfer_ordinary_zero_tolerance.lean -/
set_option autoImplicit false
set_option Elab.async false
section z29

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
noncomputable section
open scoped Classical BigOperators
namespace OAI.Paper320













namespace Tournament
variable {k : ℕ} (T : Tournament k)



end Tournament









theorem card_biUnion_le_mul {J I : Type} [DecidableEq I] (A : Finset J) (B : J → Finset I) (n : ℕ)
    (hn : ∀ j ∈ A, (B j).card ≤ n) : (A.biUnion B).card ≤ A.card * n := by
  calc
    (A.biUnion B).card ≤ ∑ j ∈ A, (B j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ A, n := Finset.sum_le_sum hn
    _ = A.card * n := by simp

end OAI.Paper320
namespace Sensitivity205
open OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open OAI.Paper320 Sensitivity205













section Flips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

















end Flips

section RowFlips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)





end RowFlips

section Nesting
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F)

end Nesting



section JointCandidates
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F) (Ai Aj Gi Gj : Fin n)
  (hA : Ai ≤ Aj) (hG : Gj ≤ Gi)
  (x : ((Fin k × Fin r) × I) → Bool)



end JointCandidates





end Sensitivity2075
end
end z29

section z30

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity205 Sensitivity2075

namespace ZT

variable {I : Type} [Fintype I]



end ZT
end
end z30

section z31

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075
namespace ZT

variable {n k r : ℕ} {I : Type} [Fintype I]



end ZT
end
end z31

section z32
set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators
namespace OAI.Paper320.Tournament
variable {k : ℕ} (T : Tournament k)



end OAI.Paper320.Tournament
namespace SensitivityQ



end SensitivityQ
namespace SensitivitySourceZero
variable {n k r : ℕ} {I : Type}





theorem target_no_edge_to_full_gate (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k)
    (hi : i ∈ tolerantTargets T label F A G 0 x)
    (hj : ∀ c, F G (recursiveChild x j c) = true) : ¬ T.Adj i j := by
  intro hij
  have hz : (failedGuards T label F G x i).card = 0 := by
    have hh := (Finset.mem_filter.mp hi).2.2
    omega
  have hempty := Finset.card_eq_zero.mp hz
  have hmem : j ∈ failedGuards T label F G x i :=
    (mem_failedGuards T label F G x i j).mpr ⟨hij, hj _⟩
  simpa only [hempty, Finset.notMem_empty] using hmem

theorem guard_not_target_zero (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ tolerantGuards T label F A G 0 x) :
    i ∉ tolerantTargets T label F A G 0 x := by
  intro hit
  have hone := (Finset.mem_filter.mp hit).2.1
  have hempty := (Finset.mem_filter.mp hi).2.1
  simp only [hempty, Finset.card_empty] at hone
  omega



theorem guard_dominates_target_zero (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k)
    (hi : i ∈ tolerantGuards T label F A G 0 x)
    (hj : j ∈ tolerantTargets T label F A G 0 x) : T.Adj i j := by
  have hne : i ≠ j := by
    intro he
    subst j
    exact guard_not_target_zero T label F A G x i hi hj
  have hfull : ∀ c, F G (recursiveChild x i c) = true := by
    intro c
    exact hF.accepts_of_le hGA
      ((missingTargets_empty F A x i).mp (Finset.mem_filter.mp hi).2.1 c)
  exact (T.adj_or_reverse hne).resolve_right
    (target_no_edge_to_full_gate T label F A G x j i hj hfull)









end SensitivitySourceZero
end
end z32

section z33

set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





end ZT
end
end z33

section z34

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]









end ZT
end
end z34

section z35

set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
namespace ZT

end ZT
end
end z35

section z36
set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace SensitivityOrdinaryGuard
end SensitivityOrdinaryGuard
end
end z36

section z37

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





end ZT
end
end z37

section z40

set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators

namespace ZT
variable {n k : ℕ} {I : Type}

end ZT
end
end z40

section z41

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



theorem remaining_targets_marked_zero_all (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    let P := positiveTargets T label F t g 0 x (by decide)
    let G := tolerantGuards T label F t g 0 x
    ZL.MarkedGood T.Adj (fun e => label e.1 e.2)
      (remainingOrdinaryTargets T label F t g 0 x) (P ∪ G) P 0 0
      (missingWitness F t x (by decide)) := by
  let A := remainingOrdinaryTargets T label F t g 0 x
  let P := positiveTargets T label F t g 0 x (by decide)
  let G := tolerantGuards T label F t g 0 x
  apply candidates_markedGood T label F hF t g hgt 0 0 x A (P ∪ G) P
    (remaining_targets_subset T label F t g 0 x) (Finset.Subset.refl _) (Finset.Subset.refl _)
  · apply Finset.disjoint_left.mpr
    intro v hv hmark
    rcases Finset.mem_union.mp hmark with hp | hg
    · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2 hp
    · exact Finset.disjoint_left.mp (target_guard_disjoint T label F t g 0 x)
        (remaining_targets_subset T label F t g 0 x hv) hg
  · have hempty : ∀ v ∈ P ∪ G, ZL.mismatch T.Adj (fun e => label e.1 e.2)
        A (missingWitness F t x (by decide)) v = ∅ := by
      intro v hv
      rcases Finset.mem_union.mp hv with hp | hg
      · have hsub := target_mismatch_failed T label F hF t g hgt 0 x A
          (remaining_targets_subset T label F t g 0 x) v
        have hz : failedGuards T label F g x v = ∅ := by
          apply Finset.card_eq_zero.mp
          have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
          omega
        exact Finset.eq_empty_iff_forall_notMem.mpr (by
          intro w hw
          have hh := hsub hw
          simpa only [hz,Finset.notMem_empty] using hh)
      · exact remaining_targets_guard_mismatch_empty T label F hF t g hgt 0 x v hg
    exact (show (∑ v ∈ P ∪ G, (ZL.mismatch T.Adj (fun e => label e.1 e.2)
      A (missingWitness F t x (by decide)) v).card)=0 by
        apply Finset.sum_eq_zero
        intro v hv
        rw [hempty v hv]
        rfl).le

end ZT
end
end z41

section z42

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 ZL

namespace ZT
variable {k : ℕ}

theorem zero_marked_domination (T : Tournament k) (ell : Fin k × Fin k → Fin 2)
    (A M P : Finset (Fin k)) (color : Fin k → Fin 2)
    (hdis : Disjoint A M) (hgood : MarkedGood T.Adj ell A M P 0 0 color) :
    ∀ i ∈ M, ∀ j ∈ A, T.Adj i j := by
  intro i hi j hj
  have hne : i ≠ j := by
    intro he
    subst j
    exact Finset.disjoint_left.mp hdis hj hi
  apply (T.adj_or_reverse hne).resolve_right
  intro hji
  have hmem : i ∈ outOn T.Adj M j := Finset.mem_filter.mpr ⟨hi,hji⟩
  have hp := Finset.card_pos.mpr ⟨i,hmem⟩
  have hz := hgood.1 j hj
  omega

theorem zero_marked_coherent (T : Tournament k) (ell : Fin k × Fin k → Fin 2)
    (A M P : Finset (Fin k)) (color : Fin k → Fin 2)
    (hgood : MarkedGood T.Adj ell A M P 0 0 color) :
    Coherent T.Adj ell A M color := by
  intro e he
  rcases Finset.mem_union.mp he with heA | heM
  · obtain ⟨heprod,hedge⟩ := Finset.mem_filter.mp heA
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp heprod
    by_contra hn
    have hp := Finset.card_pos.mpr (⟨e.2,Finset.mem_filter.mpr ⟨hy,hedge,hn⟩⟩ :
      (mismatch T.Adj ell A color e.1).Nonempty)
    have hz := hgood.1 e.1 hx
    omega
  · obtain ⟨heprod,hedge⟩ := Finset.mem_filter.mp heM
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp heprod
    by_contra hn
    have hp := Finset.card_pos.mpr (⟨e.2,Finset.mem_filter.mpr ⟨hy,hedge,hn⟩⟩ :
      (mismatch T.Adj ell A color e.1).Nonempty)
    have hs : (mismatch T.Adj ell A color e.1).card ≤
        ∑ i ∈ M, (mismatch T.Adj ell A color i).card :=
      Finset.single_le_sum (f := fun i => (mismatch T.Adj ell A color i).card)
        (fun _ _ => Nat.zero_le _) hx
    have hz := hgood.2.2
    omega

theorem zero_marked_twoDominator (T : Tournament k)
    (ell : Fin k × Fin k → Fin 2) (A M P M' : Finset (Fin k))
    (color : Fin k → Fin 2) (hdis : Disjoint A M)
    (hgood : MarkedGood T.Adj ell A M P 0 0 color)
    (hsub : M' ⊆ M) (hcard : M'.card = 2) :
    TwoDominatorGood T.Adj ell A M' color := by
  refine ⟨hdis.mono_right hsub,hcard,?_,?_⟩
  · exact fun i hi j hj => zero_marked_domination T ell A M P color hdis hgood i (hsub hi) j hj
  · intro e he
    apply zero_marked_coherent T ell A M P color hgood
    rcases Finset.mem_union.mp he with heA | heM
    · exact Finset.mem_union_left _ heA
    · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp heM
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hsub (Finset.mem_product.mp hp).1,
          (Finset.mem_product.mp hp).2⟩,hr⟩)

theorem zero_marked_source_card (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (A M P : Finset (Fin k))
    (color : Fin k → Fin 2) (hdis : Disjoint A M)
    (hgood : MarkedGood T.Adj (fun e => label e.1 e.2) A M P 0 0 color)
    (hne : M.Nonempty) (w : ℕ) (hsource : SensitivitySourceZero.SourceBound T label w) :
    A.card + 1 < w := by
  obtain ⟨i,hi⟩ := hne
  have hinot : i ∉ A := fun h => Finset.disjoint_left.mp hdis h hi
  have hdom := zero_marked_domination T (fun e => label e.1 e.2) A M P color hdis hgood
  have hcoh := zero_marked_coherent T (fun e => label e.1 e.2) A M P color hgood
  have hlocal : ∀ u ∈ insert i A, ∀ v ∈ insert i A,
      T.Adj u v → label u v = color v := by
    intro u hu v hv huv
    have hvA : v ∈ A := by
      rcases Finset.mem_insert.mp hv with he | hvA
      · subst v
        rcases Finset.mem_insert.mp hu with he | huA
        · exact False.elim (T.ne_of_adj huv he)
        · exact False.elim (T.not_adj_reverse (hdom i hi u huA) huv)
      · exact hvA
    rcases Finset.mem_insert.mp hu with he | huA
    · subst u
      exact hcoh (i,v) (Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hi,hvA⟩,huv⟩))
    · exact hcoh (u,v) (Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨huA,hvA⟩,huv⟩))
  have hs : SensitivitySourceZero.HasSource T (insert i A) := by
    refine ⟨i,Finset.mem_insert_self _ _,?_⟩
    intro j hj hji
    exact hdom i hi j ((Finset.mem_insert.mp hj).resolve_left hji)
  have hd : ∀ u ∈ insert i A,
      ((insert i A).filter fun v => T.Adj u v ∧ label u v ≠ color v).card ≤ 0 := by
    intro u hu
    have hempty : (insert i A).filter (fun v => T.Adj u v ∧ label u v ≠ color v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hvA,huv,hn⟩ := Finset.mem_filter.mp hv
      exact hn (hlocal u hu v hvA huv)
    simp only [hempty, Finset.card_empty, le_refl]
  have hh := hsource (insert i A) color hs hd
  simpa only [Finset.card_insert_of_notMem hinot] using hh

end ZT
end
end z42

section z43

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ ZL
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]















theorem remaining_card_source_zero (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (w : ℕ)
    (hsource : SensitivitySourceZero.SourceBound T label w)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hne : (positiveTargets T label F t g 0 x (by decide) ∪ tolerantGuards T label F t g 0 x).Nonempty) :
    (remainingOrdinaryTargets T label F t g 0 x).card+1 < w := by
  let A := remainingOrdinaryTargets T label F t g 0 x
  let P := positiveTargets T label F t g 0 x (by decide)
  let G := tolerantGuards T label F t g 0 x
  have hdis : Disjoint A (P ∪ G) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    rcases Finset.mem_union.mp hw with hp | hg
    · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2 hp
    · exact Finset.disjoint_left.mp (target_guard_disjoint T label F t g 0 x)
        (remaining_targets_subset T label F t g 0 x hv) hg
  exact zero_marked_source_card T label A (P ∪ G) P _ hdis
    (remaining_targets_marked_zero_all T label F hF t g hgt x) hne w hsource

theorem remaining_card_double_zero (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (w : ℕ) (hdouble : DoubleCardBound T label w)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hne : 2 ≤ (positiveTargets T label F t g 0 x (by decide) ∪ tolerantGuards T label F t g 0 x).card) :
    (remainingOrdinaryTargets T label F t g 0 x).card < w := by
  let A := remainingOrdinaryTargets T label F t g 0 x
  let P := positiveTargets T label F t g 0 x (by decide)
  let G := tolerantGuards T label F t g 0 x
  have hdis : Disjoint A (P ∪ G) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    rcases Finset.mem_union.mp hw with hp | hg
    · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2 hp
    · exact Finset.disjoint_left.mp (target_guard_disjoint T label F t g 0 x)
        (remaining_targets_subset T label F t g 0 x hv) hg
  obtain ⟨M',hM',hc⟩ := Finset.exists_subset_card_eq hne
  exact hdouble A M' _ (zero_marked_twoDominator T (fun e => label e.1 e.2) A (P ∪ G) P M' _
    hdis (remaining_targets_marked_zero_all T label F hF t g hgt x) hM' hc)

end ZT
end
end z43

section z58

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ SensitivityOrdinaryGuard
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

end ZT
end
end z58

section z60

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



end ZT
end
end z60

section z62

set_option maxHeartbeats 5000000
namespace ZT



theorem zeroCost_lower (a b s j d : ℕ) :
    22*b ≤ zeroCost a b s j d ∧ a+19*b ≤ zeroCost a b s j d ∧
    17*b+max (min (a+s) d) (a+j) ≤ zeroCost a b s j d ∧
    19*b+s ≤ zeroCost a b s j d ∧ 20*b+j ≤ zeroCost a b s j d ∧
    17*b+s+j ≤ zeroCost a b s j d ∧ 18*b+2*j ≤ zeroCost a b s j d ∧
    17*b+3*j ≤ zeroCost a b s j d := by unfold zeroCost; omega

theorem zero_candidate_cases (z t u m δ a b s j d : ℕ)
    (hu : u ≤ 1) (hm : m ≤ 3) (hc : (u+m).choose 2 ≤ m)
    (ht : t ≤ 22)
    (hδ : δ+((u*m+u.choose 2)-0*u) ≤ m*(0+1)-m.choose 2)
    (hsource : 1 ≤ u+m → t-u ≤ 19+δ)
    (hdouble : 2 ≤ u+m → t-u ≤ 17+δ)
    (hraw : z ≤ candidateCost 0 t u m δ a b s j)
    (hshared : u=1 → m=1 → z ≤ (t-1)*b+max (min (a+s) d) (a+j)) :
    z ≤ zeroCost a b s j d := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := zeroCost_lower a b s j d
  interval_cases u
  · interval_cases m
    · have hd : δ=0 := by norm_num at hδ; omega
      subst δ
      norm_num [candidateCost] at hraw
      exact (hraw.trans (Nat.mul_le_mul_right b ht)).trans h0
    · have hd : δ ≤ 1 := by norm_num at hδ; exact hδ
      have hs := hsource (by decide)
      norm_num at hs
      interval_cases δ
      · norm_num [candidateCost] at hraw
        have hb := Nat.mul_le_mul_right b hs
        exact (by omega : z ≤ 19*b+s).trans h3
      · norm_num [candidateCost] at hraw
        have hb := Nat.mul_le_mul_right b hs
        exact (by omega : z ≤ 20*b+j).trans h4
    · have hd : δ ≤ 1 := by norm_num at hδ; exact hδ
      have hs := hdouble (by decide)
      norm_num at hs
      interval_cases δ
      · norm_num [candidateCost] at hraw
        have hb := Nat.mul_le_mul_right b hs
        exact (by omega : z ≤ 17*b+s+j).trans h5
      · norm_num [candidateCost] at hraw
        have hb := Nat.mul_le_mul_right b hs
        exact (by omega : z ≤ 18*b+2*j).trans h6
    · have hd : δ=0 := by norm_num at hδ; omega
      subst δ
      have hs := hdouble (by decide)
      norm_num at hs
      norm_num [candidateCost] at hraw
      have hb := Nat.mul_le_mul_right b hs
      exact (by omega : z ≤ 17*b+3*j).trans h7
  · interval_cases m
    · have hd : δ=0 := by norm_num at hδ; omega
      subst δ
      have hs : t-1 ≤ 19 := by simpa only [Nat.add_zero] using hsource (by decide)
      norm_num [candidateCost] at hraw
      have hb := Nat.mul_le_mul_right b hs
      exact (by omega : z ≤ a+19*b).trans h1
    · have hd : δ=0 := by norm_num at hδ; omega
      subst δ
      have hs : t-1 ≤ 17 := by simpa only [Nat.add_zero] using hdouble (by decide)
      have hr := hshared rfl rfl
      have hb := Nat.mul_le_mul_right b hs
      exact (by omega : z ≤ 17*b+max (min (a+s) d) (a+j)).trans h2
    · norm_num [Nat.choose] at hc
    · norm_num [Nat.choose] at hc



end ZT
end z62

section z63

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ SensitivitySourceZero
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

theorem childFlips_union_card (F : Fin n → (I → Bool) → Bool) (g t : Fin n)
    (x : ((Fin k × Fin 2) × I) → Bool) (v : Fin k) (c : Fin 2) :
    (childFlipsTo F t true x v c ∪ childFlipsTo F g false x v c).card =
      (flipsTo (F g) false (recursiveChild x v c) ∪
        flipsTo (F t) true (recursiveChild x v c)).card := by
  rw [Finset.union_comm]
  change ((childLift (v,c) (flipsTo (F g) false (recursiveChild x v c))) ∪
    childLift (v,c) (flipsTo (F t) true (recursiveChild x v c))).card = _
  rw [show childLift (v,c) (flipsTo (F g) false (recursiveChild x v c)) ∪
      childLift (v,c) (flipsTo (F t) true (recursiveChild x v c)) =
      childLift (v,c) (flipsTo (F g) false (recursiveChild x v c) ∪
        flipsTo (F t) true (recursiveChild x v c)) by
    simp only [childLift,Finset.map_union]]
  exact childLift_card _ _

theorem zero_shared_target_guard (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hga : ga ≤ ta)
    (a b s j d : ℕ) (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (hs : BBound F gb ga s) (hj : BBound F gb tb j) (hd : DBound F gb ga ta tb d)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga 0 x = false)
    (u v : Fin k)
    (hU : positiveTargets T label F tb gb 0 x (by decide) = {u})
    (hG : tolerantGuards T label F tb gb 0 x = {v}) :
    (flipsTo (tolerantFamily T label F tb gb 0) true x).card ≤
      ((tolerantTargets T label F tb gb 0 x).card-1)*b+
        max (min (a+s) d) (a+j) := by
  let TC := tolerantTargets T label F tb gb 0 x
  let tw := missingWitness F tb x (by decide)
  let Q := (TC.erase u).biUnion fun w => childFlipsTo F tb true x w (tw w)
  let A := childFlipsTo F tb true x u (tw u)
  let B := childFlipsTo F gb false x u (label v u)
  have huU : u ∈ positiveTargets T label F tb gb 0 x (by decide) := by rw [hU]; simp
  have huT : u ∈ TC := (Finset.mem_filter.mp huU).1
  have hgb : F gb (recursiveChild x u (tw u)) = true := (Finset.mem_filter.mp huU).2
  have hta := tolerant_target_weak_false T label F hF ta tb ga gb ht hg x (le_refl 0)
    (by decide) hx huT
  have hvG : v ∈ tolerantGuards T label F tb gb 0 x := by rw [hG]; simp
  have hvu : T.Adj v u := guard_dominates_target_zero T label F hF tb gb
    (hg.trans (hga.trans ht)) x v u hvG huT
  have hfull : ∀ c, F gb (recursiveChild x u c) = true :=
    SensitivityOrdinaryGuard.positive_gate_true T label F hF tb gb (hg.trans (hga.trans ht))
      0 x (by decide) u huU
  have hufailed : u ∈ failedGuards T label F gb x v :=
    (mem_failedGuards T label F gb x v u).mpr ⟨hvu,hfull _⟩
  have hfailed : failedGuards T label F gb x v = {u} := by
    have hc : (failedGuards T label F gb x v).card = 1 := by
      simpa using (Finset.mem_filter.mp hvG).2.2
    exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hufailed,fun w hw => by
      obtain ⟨w₀,hw₀⟩ := Finset.card_eq_one.mp hc
      have he : u = w₀ := by simpa [hw₀] using hufailed
      simpa [hw₀,←he] using hw⟩
  have hguard : guardRepairs T label F tb gb 0 x = B := by
    simp [guardRepairs,hG,hfailed,B]
  have hweak : F ga (recursiveChild x u (label v u)) = true :=
    selected_guard_weak_true T label F hF ta tb ga gb ht hg 0 x hx (v,u)
      ((mem_guardArcs _ _ _ _ _ _ _ _).mpr ⟨hvG,hufailed⟩)
  have hQ : Q.card ≤ (TC.card-1)*b := by
    have hh : Q.card ≤ (TC.erase u).card*b := by
      apply card_biUnion_le_mul
      intro w hw
      have hwT := Finset.mem_of_mem_erase hw
      have hwne := Finset.ne_of_mem_erase hw
      have hnot : w ∉ positiveTargets T label F tb gb 0 x (by decide) := by
        simpa [hU] using hwne
      have hfalse : F gb (recursiveChild x w (tw w)) = false := by
        have hn : ¬ F gb (recursiveChild x w (tw w)) = true := by
          intro hon
          exact hnot (Finset.mem_filter.mpr ⟨hwT,hon⟩)
        simpa only [Bool.not_eq_true] using hn
      simpa only [childFlipsTo_card] using hb _ hfalse
    simpa [Finset.card_erase_of_mem huT] using hh
  have hA : A.card ≤ a := by simpa only [A,childFlipsTo_card] using ha _ hgb hta
  have hAB : (A ∪ B).card ≤ max (min (a+s) d) (a+j) := by
    by_cases hc : label v u = tw u
    · have hB : B.card ≤ s := by simpa only [B,childFlipsTo_card] using hs _ hweak
      have hab : (A ∪ B).card ≤ a+s :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add hA hB)
      have hd' : (A ∪ B).card ≤ d := by
        have hweak' : F ga (recursiveChild x u (tw u)) = true := by simpa [hc] using hweak
        simpa only [A,B,hc,childFlips_union_card] using hd _ hweak' hta
      exact (le_min hab hd').trans (le_max_left _ _)
    · have htrue : F tb (recursiveChild x u (label v u)) = true :=
        missingWitness_other_true F tb x (by decide) u (Finset.mem_filter.mp huT).2.1 _ hc
      have hB : B.card ≤ j := by simpa only [B,childFlipsTo_card] using hj _ htrue
      exact ((Finset.card_union_le _ _).trans (Nat.add_le_add hA hB)).trans (le_max_right _ _)
  have hfalse : tolerantFamily T label F tb gb 0 x = false := by
    cases hh : tolerantFamily T label F tb gb 0 x
    · rfl
    · have hw := family_nested T label F hF ht hg (le_refl 0) x hh
      simp [hx] at hw
  have hcover : flipsTo (tolerantFamily T label F tb gb 0) true x ⊆ Q ∪ (A ∪ B) := by
    intro p hp
    rcases Finset.mem_union.mp (up_subset_repairs T label F tb gb 0 x hfalse hp) with htar | hgr
    · obtain ⟨w,hw,hp⟩ := Finset.mem_biUnion.mp htar
      by_cases he : w = u
      · subst w
        exact Finset.mem_union_right _ (Finset.mem_union_left _ hp)
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨w,Finset.mem_erase.mpr ⟨he,hw⟩,hp⟩)
    · rw [hguard] at hgr
      exact Finset.mem_union_right _ (Finset.mem_union_right _ hgr)
  exact (Finset.card_le_card hcover).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hQ hAB))

end ZT
end
end z63

section z64

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

theorem _root_.ThreeBoundOrdinaryArchive.Paley11987Verified.CompactBooleanTransfer.ordinary_zero_tolerance (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hga : ga ≤ ta)
    (a b s j d : ℕ) (hjs : j ≤ s)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (hs : BBound F gb ga s) (hj : BBound F gb tb j) (hd : DBound F gb ga ta tb d)
    (hordinary : DefectBound T label 0 23)
    (hsource : SensitivitySourceZero.SourceBound T label 21)
    (hdouble : DoubleCardBound T label 18)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga 0 x = false) :
    (flipsTo (tolerantFamily T label F tb gb 0) true x).card ≤ zeroCost a b s j d := by
  let TC := tolerantTargets T label F tb gb 0 x
  let P := positiveTargets T label F tb gb 0 x (by decide)
  let G := tolerantGuards T label F tb gb 0 x
  let δ := (crossedTargetHeads T label F tb gb 0 x).card
  have hgt : gb ≤ tb := hg.trans (hga.trans ht)
  have hpart := remaining_targets_card T label F tb gb 0 x
  have hmark : (P ∪ G).card=P.card+G.card :=
    Finset.card_union_of_disjoint (SensitivityOrdinaryGuard.positive_guards_disjoint
      T label F tb gb 0 x (by decide))
  have hu : P.card ≤ 1 := by simpa using positiveTargets_card T label F hF tb gb hgt 0 x (by decide)
  have hm : G.card ≤ 3 := by simpa using guards_card T label F hF tb gb hgt 0 x
  have hc : (P.card+G.card).choose 2 ≤ G.card := by
    simpa using positiveTargets_guards_coupling T label F hF tb gb hgt 0 x (by decide)
  have htcard : TC.card ≤ 22 := by
    have hh := targets_card_of_exclusion T label F hF tb gb hgt 0 23 hordinary x
    change TC.card < 23 at hh
    omega
  have hδ := crossedTargetHeads_budget T label F hF tb gb hgt 0 x
  have hsrc : 1 ≤ P.card+G.card → TC.card-P.card ≤ 19+δ := by
    intro hn
    have hne : (P ∪ G).Nonempty := Finset.card_pos.mp (by rw [hmark]; omega)
    have hh := remaining_card_source_zero T label F hF tb gb hgt 21 hsource x hne
    change (remainingOrdinaryTargets T label F tb gb 0 x).card+δ+P.card=TC.card at hpart
    omega
  have hdbl : 2 ≤ P.card+G.card → TC.card-P.card ≤ 17+δ := by
    intro hn
    have hne : 2 ≤ (P ∪ G).card := by rw [hmark]; exact hn
    have hh := remaining_card_double_zero T label F hF tb gb hgt 18 hdouble x hne
    change (remainingOrdinaryTargets T label F tb gb 0 x).card+δ+P.card=TC.card at hpart
    omega
  have hraw := ordinary_zero_candidate_cost T label F hF ta tb ga gb ht hg hga 0 a b s j
    hjs ha hb hs hj x hx
  apply zero_candidate_cases _ TC.card P.card G.card δ a b s j d hu hm hc htcard hδ hsrc hdbl hraw
  intro hpc hgc
  obtain ⟨u,hu⟩ := Finset.card_eq_one.mp hpc
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hgc
  exact zero_shared_target_guard T label F hF ta tb ga gb ht hg hga a b s j d
    ha hb hs hj hd x hx u v hu hv



end ZT
end
end z64

end ThreeBoundOrdinaryArchive


