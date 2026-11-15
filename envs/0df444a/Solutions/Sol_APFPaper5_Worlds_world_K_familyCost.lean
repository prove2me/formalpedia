-- Prove2me | solution 1 for APFPaper5.Worlds.world_K_familyCost
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T03:49:18.332286+00:00
-- url     : https://prove2.me/submissions/1c489be7-3c4b-4532-8721-0ba8f62d5339

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFB05_Worlds_one_protocol_keeps_all
title: A supplied world in which the declared forms of B03, B04 and B05 and B02's second sentence hold with infinitely many distinctions at capacity 1
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: supplied data. The declared forms are those of FOUNDATION_INPUTS.json B03 (APFB03.B03TaskCost), B04
 (APFB04.B04FiniteCapacity) and B05 (APFB05.MarginalFloor); B02's second sentence is
 APFB02.EveryCombinationHeld. Paper 1 Supplement v9.28:2615-2617 (support novelty).
consumes_inputs: none as hypotheses. Declared forms are PROVED of supplied data, which certifies nothing about
 the physical inputs.
statement: World K has one context, the natural numbers as distinctions, one protocol that keeps every record
 and bills 1, and the alignments as states. (world_K_familyCost) every family costs 1.
 (world_K_nothing_is_support_novel) no distinction is support-novel over any family.
 (world_K_every_family_admissible) every finite family is ledger-admissible at capacity 1.
 (world_K_meets_B03_B04_B05_and_second_sentence) the declared forms of B03, B04 (capacity 1) and B05
 (floor 1) hold, and every combination of sides of every finite family is held.
reading: B03, B04, B05 and B02's second sentence do not bound the number of distinctions of a region at one
 context. The bound of Thm_APFB05_fineness_floor_at_one_interface needs its chain condition: each distinction
 support-novel over those before it.
not_claimed: that World K meets the other declared forms (B01, B02's first sentence, B06, A2, BW); they are
 not checked here. That a physical context is like World K.
-/
import Definitions.Def_APF_B03_DeclaredInput_r2
import Definitions.Def_APF_B04_DeclaredInput
import Definitions.Def_APF_B05_DeclaredInput_r2
import Definitions.Def_APFB02_EachTakesBothSides

set_option autoImplicit false
namespace APFPaper5.Worlds

open APFPaper1.Source

theorem world_K_familyCost (S : Finset ℕ) :
    familyCost (D := ℕ) (P := Unit) (R := Unit) (Record := Unit) (fun _ => ())
      (fun _ => (1 : NNReal)) (fun _ => Set.univ) (fun _ _ _ => True) (fun _ _ _ => True) S
      = 1 := by
  unfold familyCost
  have hmem : (1 : ℝ) ∈ {c : ℝ | ∃ p : Unit,
      (∀ d ∈ S, ∃ sigma : Set Unit, sigma ⊆ (Set.univ : Set Unit) ∧ True ∧ True) ∧
      (((1 : NNReal) : ℝ)) = c} :=
    ⟨(), fun _ _ => ⟨Set.univ, subset_rfl, trivial, trivial⟩, NNReal.coe_one⟩
  refine le_antisymm (csInf_le ⟨0, ?_⟩ hmem) (le_csInf ⟨1, hmem⟩ ?_)
  · rintro c ⟨_, _, rfl⟩
    exact NNReal.coe_nonneg _
  · rintro c ⟨_, _, rfl⟩
    exact le_of_eq NNReal.coe_one.symm

theorem world_K_nothing_is_support_novel (S : Finset ℕ) (d : ℕ) :
    ¬ supportNovel (D := ℕ) (P := Unit) (R := Unit) (Record := Unit) (fun _ => ())
      (fun _ => (1 : NNReal)) (fun _ => Set.univ) (fun _ _ _ => True) (fun _ _ _ => True) S d := by
  rintro ⟨eta, heta, h⟩
  refine h () (fun _ _ => ⟨Set.univ, subset_rfl, trivial, trivial⟩) ?_
    ⟨Set.univ, subset_rfl, trivial⟩
  rw [world_K_familyCost S]
  have e : (((1 : NNReal) : ℝ)) = 1 := NNReal.coe_one
  show (((1 : NNReal) : ℝ)) ≤ 1 + eta
  rw [e]
  linarith

theorem world_K_every_family_admissible (S : Finset ℕ) :
    familyAdmissible (D := ℕ) (P := Unit) (R := Unit) (Record := Unit) (fun _ => ())
      (fun _ => (1 : NNReal)) (fun _ => Set.univ) (fun _ _ _ => True) (fun _ _ _ => True) 1 S :=
  ⟨⟨(), fun _ _ => ⟨Set.univ, subset_rfl, trivial, trivial⟩⟩, le_of_eq (world_K_familyCost S)⟩

theorem world_K_meets_B03_B04_B05_and_second_sentence :
    APFB03.B03TaskCost (Context := Unit) (D := fun _ => ℕ) (P := fun _ => Unit)
        (R := fun _ => Unit) (Record := fun _ => Unit) (fun _ _ => ())
        (fun _ _ => (1 : NNReal)) (fun _ _ => Set.univ) (fun _ _ _ _ => True)
        (fun _ _ _ _ => True) ∧
    APFB04.B04FiniteCapacity (Context := Unit) (fun _ => 1) ∧
    APFB05.MarginalFloor (Context := Unit) (D := fun _ => ℕ) (P := fun _ => Unit)
        (R := fun _ => Unit) (Record := fun _ => Unit) (fun _ _ => ())
        (fun _ _ => (1 : NNReal)) (fun _ _ => Set.univ) (fun _ _ _ _ => True)
        (fun _ _ _ _ => True) (fun _ _ => True) (fun _ => 1) (fun _ => 1) ∧
    APFB02.EveryCombinationHeld (fun (d : ℕ) (x : ℕ → Bool) => x d) := by
  refine ⟨fun _ d => ?_, fun _ => zero_le_one, fun _ => ⟨zero_lt_one, fun S d _ _ _ hnov => ?_⟩,
    fun _ v => ⟨v, fun _ _ => rfl⟩⟩
  · have e := world_K_familyCost {d}
    show 0 < familyCost (D := ℕ) (P := Unit) (R := Unit) (Record := Unit) (fun _ => ())
      (fun _ => (1 : NNReal)) (fun _ => Set.univ) (fun _ _ _ => True) (fun _ _ _ => True) {d}
    rw [e]
    exact zero_lt_one
  · exact absurd hnov (world_K_nothing_is_support_novel S d)

end APFPaper5.Worlds


theorem solution :
∀ (S : Finset.{0} Nat),
  @Eq.{1} Real
    (@APFPaper1.Source.familyCost.{0, 0, 0, 0} Nat Unit Unit Unit (fun (x : Unit) => Unit.unit)
      (fun (x : Unit) => @OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne))
      (fun (x : Unit) => @Set.univ.{0} Unit) (fun (x : Unit) (x_1 : Set.{0} Unit) (x_2 : Nat) => True)
      (fun (x : Unit) (x_1 : Nat) (x_2 : Set.{0} Unit) => True) S)
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) := by
  exact @APFPaper5.Worlds.world_K_familyCost
