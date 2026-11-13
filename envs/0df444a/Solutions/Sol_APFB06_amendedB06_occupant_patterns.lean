-- Prove2me | solution 1 for APFB06.amendedB06_occupant_patterns
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-12T19:48:44.359632+00:00
-- url     : https://prove2.me/submissions/e4eda9c8-79cd-418b-ae47-9f3e1e18a5f8

import Theorems.Thm_APFB06_amendedB06_extract_E
import Definitions.Def_APF_B06_DeclaredInput
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.ByContra
set_option autoImplicit false
open APFB06
namespace APFB06

theorem two_le_of_pow_bound (k N : ℕ) (hk : 1 ≤ k) (h : k + 1 ≤ 2 ^ (N - 1)) : 2 ≤ N := by
  by_contra hlt
  have hN : N - 1 = 0 := by omega
  rw [hN, pow_zero] at h
  omega

theorem pattern_count_bound {Ω Q : Type*} [Fintype Q] (read : Q → Ω → Bool) (a : Ω)
    (active : ∀ d, read d a = true)
    (nontrivial : ∀ d, ∃ x y, read d x ≠ read d y)
    (distinct : Function.Injective read) :
    Fintype.card Q + 1 ≤
      2 ^ (Nat.card (Set.range (fun (x : Ω) (d : Q) => read d x)) - 1) := by
  classical
  let P := Set.range (fun (x : Ω) (d : Q) => read d x)
  haveI : Fintype P := Fintype.ofFinite P
  let obs : Ω → P := fun x => ⟨fun d => read d x, ⟨x, rfl⟩⟩
  have alt : ∀ d, ∃ w : P, w ≠ obs a ∧ w.val d = false := by
    intro d
    obtain ⟨x, y, hxy⟩ := nontrivial d
    have hx : ∃ z, read d z = false := by
      cases hx : read d x with
      | false => exact ⟨x, hx⟩
      | true =>
        cases hy : read d y with
        | false => exact ⟨y, hy⟩
        | true => exact False.elim (hxy (hx.trans hy.symm))
    obtain ⟨z, hz⟩ := hx
    refine ⟨obs z, ?_, hz⟩
    intro heq
    have h : read d z = read d a := congrArg (fun w : P => w.val d) heq
    rw [hz, active d] at h
    cases h
  let W := {w : P // w ≠ obs a}
  let col : Option Q → W → Bool := fun q w =>
    match q with
    | none => true
    | some d => w.val.val d
  have neqconst : ∀ d, col (some d) ≠ col none := by
    intro d h
    obtain ⟨w, hw, hf⟩ := alt d
    have he : w.val d = true := congrFun h ⟨w, hw⟩
    rw [hf] at he
    cases he
  have hcol : Function.Injective col := by
    intro q r h
    cases q with
    | none =>
      cases r with
      | none => rfl
      | some e => exact False.elim (neqconst e h.symm)
    | some d =>
      cases r with
      | none => exact False.elim (neqconst d h)
      | some e =>
        congr 1
        apply distinct
        funext x
        by_cases hx : obs x = obs a
        · have hd : read d x = read d a := congrArg (fun w : P => w.val d) hx
          have he : read e x = read e a := congrArg (fun w : P => w.val e) hx
          rw [hd, he, active d, active e]
        · exact congrFun h ⟨obs x, hx⟩
  have hcard := Fintype.card_le_of_injective col hcol
  have hwcard : Fintype.card W = Fintype.card P - 1 := by
    simpa [W] using Fintype.card_subtype_compl (fun w : P => w = obs a)
  have hP : Nat.card P = Fintype.card P := Nat.card_eq_fintype_card
  show Fintype.card Q + 1 ≤ 2 ^ (Nat.card P - 1)
  rw [hP]
  simpa only [Fintype.card_option, Fintype.card_fun, Fintype.card_bool, hwcard] using hcard

end APFB06

open APFB06 in
theorem solution
    {Context : Type*} {Raw FullProcess Resource : Context → Type*}
    (Cont : (g : Context) → Raw g → FullProcess g → Prop)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont g) → Bool))
    (protocols : (g : Context) → Set (FullProcess g))
    (J : (g : Context) → Finset (Task (Cont g) (D g)) → Set {p // p ∈ protocols g})
    (wholeResource : (g : Context) → {p // p ∈ protocols g} → Resource g)
    (calibration : (g : Context) → Resource g → NNReal)
    (C : Context → NNReal)
    (actualJoint : Set (Sigma fun g => OriginalAlignment (Cont g) (D g)))
    (hnt : ∀ (g : Context) (d : Task (Cont g) (D g)),
      ∃ s t : APFB01.PhysicalState (Cont g), d.val s ≠ d.val t)
    (h : AmendedB06_20260914 Cont D protocols J wholeResource calibration C actualJoint) :
    ∃ (o : Sigma fun g => OriginalAlignment (Cont g) (D g))
      (p : {p // p ∈ protocols o.1}) (x : Raw o.1),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧ p ∈ J o.1 o.2.carried ∧ Cont o.1 x p.val ∧
      o.2.carried.card + 1 ≤
        2 ^ (Nat.card (Set.range (fun (s : APFB01.PhysicalState (Cont o.1))
          (d : {d // d ∈ o.2.carried}) => d.val.val s)) - 1) ∧
      2 ≤ Nat.card (Set.range (fun (s : APFB01.PhysicalState (Cont o.1))
          (d : {d // d ∈ o.2.carried}) => d.val.val s)) := by
  obtain ⟨o, p, x, ho, hne, hp, hx⟩ :=
    amendedB06_extract_E Cont D protocols J wholeResource calibration C actualJoint h
  have hb := pattern_count_bound
    (fun (d : {d // d ∈ o.2.carried}) (s : APFB01.PhysicalState (Cont o.1)) => d.val.val s)
    o.2.carrier
    (fun d => o.2.active d.val d.property)
    (fun d => hnt o.1 d.val)
    (fun d e hde => Subtype.ext (Subtype.ext hde))
  rw [Fintype.card_coe] at hb
  exact ⟨o, p, x, ho, hne, hp, hx, hb, two_le_of_pow_bound _ _ (Finset.card_pos.mpr hne) hb⟩
