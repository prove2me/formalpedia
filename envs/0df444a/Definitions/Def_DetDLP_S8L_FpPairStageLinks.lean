-- Prove2me | Definitions.Def_DetDLP_S8L_FpPairStageLinks
-- name    : DetDLP_S8L_FpPairStageLinks
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:58:21.507799+00:00
-- url     : https://prove2.me/theorems/0ddf9251-bcf7-4e15-aab8-34785c30969d
-- title:
--   Equality links for a modular multiplication stage
-- statement:
--   Two sets of Boolean equality gates connect the full multiplier outputs to the two corresponding adder registers. With the operand, remainder, and modulus pins, the satisfying wire assignments of this graph are in bijection with the checked modular multiplication certificates. Including the equality gates, the number of incidences is less than 5010 times the width plus two in parentheses.

import Definitions.Def_DetDLP_S8L_FpPairStage

set_option autoImplicit false
namespace DetDLP.S8L.FpPair.Stage.Links
open S8J S8C.AddLayout w4_M5PortTensor
attribute [-simp] Fin.natAdd_eq_addNat

abbrev Bit {d : ℕ} (hd : 1 ≤ d) := Fin (stage d hd).nb

def mul1 {d : ℕ} (hd : 1 ≤ d) (i : Fin (4*d)) : Bit hd := Fin.castAdd _ (Fin.castAdd _ (ext hd i))
def mul2 {d : ℕ} (hd : 1 ≤ d) (i : Fin (4*d)) : Bit hd := Fin.castAdd _ (Fin.natAdd _ (ext hd i))
def addr {d : ℕ} (hd : 1 ≤ d) (i : Fin (2*d)) (l : Fin 4) : Bit hd := Fin.natAdd _ (reg i l)

def left {d : ℕ} (hd : 1 ≤ d) : Fin (2*d+2*d) → Bit hd :=
  Fin.addCases (fun i => addr hd i 0) (fun i => addr hd i 2)
def right {d : ℕ} (hd : 1 ≤ d) : Fin (2*d+2*d) → Bit hd :=
  Fin.addCases (fun i => mul2 hd (outPos i)) (fun i => mul1 hd (outPos i))

def layout {d : ℕ} (hd : 1 ≤ d) : w3_FactorLayout := links (stage d hd) (left hd) (right hd)
def linkedTests {d : ℕ} (hd : 1 ≤ d) : w3_factorTest (layout hd) := linksTest (left hd) (right hd) (tests hd)

/-- Only the two input buses, public modulus, and remainder are exposed outside a linked stage. -/
def Boundary {d : ℕ} (hd : 1 ≤ d) (p x y z : ℕ) (w : StageBits hd) :=
  (∀ i, w (mul1 hd (inPos false i)) = x.testBit i.val) ∧
  (∀ i, w (mul1 hd (inPos true i)) = y.testBit i.val) ∧
  (∀ i, w (mul2 hd (inPos true i)) = p.testBit i.val) ∧
  (∀ i, w (addr hd i 1) = z.testBit i.val)

theorem linked_iff {d : ℕ} (hd : 1 ≤ d) (p x y z : ℕ) (w : StageBits hd) :
    Accept (layout hd) (linkedTests hd) w ∧ Boundary hd p x y z w ↔
    Accept _ (tests hd) w ∧ buses hd p x y z w := by
  erw [linkedTests,links_iff]
  constructor
  · rintro ⟨⟨ht,h⟩,a,b,c,e⟩
    refine ⟨ht,a,b,c,fun i => ?_,e,fun i => ?_⟩
    · have H := h (Fin.castAdd (2*d) i)
      simp only [left,right,Fin.addCases_left] at H; exact H
    · have H := h (Fin.natAdd (2*d) i)
      simp only [left,right,Fin.addCases_right] at H; exact H
  · rintro ⟨ht,a,b,c,l,e,r⟩; refine ⟨⟨ht,?_⟩,a,b,c,e⟩
    intro i; induction i using Fin.addCases with
    | left i => simp only [left,right,Fin.addCases_left]; exact l i
    | right i => simp only [left,right,Fin.addCases_right]; exact r i

/-- Pin an arbitrary collection of bit addresses at their incidences, without assuming the addresses are disjoint. -/
noncomputable def atPins {A : w3_FactorLayout} {k : ℕ} (t : w3_factorTest A)
    (index : Fin k → Fin A.nb) (val : Vec k) : w3_factorTest A := by
  classical exact fun g a => t g a && decide (∀ e i, A.bit e.val = index i → a e = val i)

theorem atPins_iff {A : w3_FactorLayout} {k : ℕ} (t : w3_factorTest A) (f : Fin k → Fin A.nb)
    (v : Vec k) (w : Vec A.nb) : Accept A (atPins t f v) w ↔ Accept A t w ∧ ∀ i, w (f i) = v i := by
  classical
  simp only [Accept,atPins,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · intro h; refine ⟨fun g => (h g).1,fun i => ?_⟩
    let e := A.rep (f i)
    exact (congrArg w (A.rep_bit (f i))).symm.trans ((h (A.gate e)).2 ⟨e,rfl⟩ i (A.rep_bit (f i)))
  · rintro ⟨h,k⟩ g; exact ⟨h g,fun e i hi => (congrArg w hi).trans (k i)⟩

noncomputable def pinned {d : ℕ} (hd : 1 ≤ d) (p x y z : ℕ) : w3_factorTest (layout hd) :=
  atPins (atPins (atPins (atPins (linkedTests hd) (fun i => mul1 hd (inPos false i)) (fun i => x.testBit i.val))
    (fun i => mul1 hd (inPos true i)) (fun i => y.testBit i.val))
    (fun i => mul2 hd (inPos true i)) (fun i => p.testBit i.val)) (fun i => addr hd i 1) (fun i => z.testBit i.val)

theorem pinned_iff {d : ℕ} (hd : 1 ≤ d) (p x y z : ℕ) (w : StageBits hd) :
    Accept (layout hd) (pinned hd p x y z) w ↔ Accept _ (tests hd) w ∧ buses hd p x y z w := by
  unfold pinned; erw [atPins_iff,atPins_iff,atPins_iff,atPins_iff,← linked_iff]
  unfold Boundary; tauto

noncomputable def pinnedEquiv {d : ℕ} (hd : 1 ≤ d) (p x y z : ℕ) (hz : z < 2^(2*d)) :
    {w // (w3_factorGraph (layout hd)).Satisfies (w3_factorChecks _ (pinned hd p x y z)) w} ≃
    {r : Cert d hd // w3_modTwo hd p x y z r} :=
  (w3_factorEquiv _ _).trans ((Equiv.subtypeEquivRight (pinned_iff hd p x y z)).trans (equiv hd p x y z hz))

theorem edges {d : ℕ} (hd : 1 ≤ d) : (layout hd).ne < 5010*(d+2) := by
  have h := stage_edges hd; change (stage d hd).ne + ((2*d+2*d)+(2*d+2*d)) < _; omega

attribute [simp] Fin.natAdd_eq_addNat
end DetDLP.S8L.FpPair.Stage.Links


