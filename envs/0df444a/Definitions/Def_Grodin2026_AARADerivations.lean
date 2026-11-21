-- Prove2me | Definitions.Def_Grodin2026_AARADerivations
-- name    : Grodin2026_AARADerivations
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-20T19:13:53.076179+00:00
-- url     : https://prove2.me/theorems/e1f4bd41-6b6a-459b-9af2-32d36263cf52
-- title:
--   Graded typing derivations in the positive AARA fragment of Giralf
-- statement:
--   The inductive typing derivations for the terminating positive fragment. A derivation gives a cost and a value on each input environment and is interpreted by a lax Calf homomorphism from its credited context to the result type. The abstract homomorphism preserves the input cost and introduces no new cost.
-- source:
--   Grodin, Chu, Li, Hoffmann, and Harper (2026), Potential Functions as Types, §§5.1–5.2. https://arxiv.org/abs/2607.08547v2

import Definitions.Def_Grodin2026_AARATypes

/-!
# Graded derivations for the positive fragment of Giralf

This module interprets syntax for terminating AARA programs over the positive types of
Grodin, Chu, Li, Hoffmann, and Harper (2026), Sections 5.1–5.2. Linear contexts are
represented by their tensor, with `top` for the empty context. Pure values in the
structural context are represented by Lean values. Computation costs are introduced
by the spend rule and composed by evaluating the immediate subderivations.
-/

namespace Grodin2026.Revised

/-- A derivation of a linear program taking context `Γ` to result type `A` with grade `q`.
Positive sums, tensors and units have their usual linear rules. Linear list elimination
uses a right fold, and quadratic list elimination uses the indexed fold from §5.1.4. -/
inductive AARADerivation : AARAType → AARAType → Nat → Type 1 where
  | var {A : AARAType} (q : Nat) : AARADerivation A A q
  | letBind {Γ₁ Γ₂ A B : AARAType} {q q₁ q₂ : Nat} (h : q₁ + q₂ ≤ q)
      (value : AARADerivation Γ₁ A q₁) (body : AARADerivation (.tensor Γ₂ A) B q₂) :
      AARADerivation (.tensor Γ₁ Γ₂) B q
  | spend {Γ A : AARAType} {q p q' : Nat} (h : p + q' ≤ q)
      (body : AARADerivation Γ A q') : AARADerivation Γ A q
  | weaken {Γ A : AARAType} {q q' : Nat} (h : q' ≤ q)
      (body : AARADerivation Γ A q') : AARADerivation Γ A q
  | ret {X : Type} (x : X) (q : Nat) : AARADerivation .top (.free X) q
  | read {X : Type} {Γ A : AARAType} {q : Nat}
      (body : X → AARADerivation Γ A q) : AARADerivation (.tensor (.free X) Γ) A q
  | tensorIntro {Γ₁ Γ₂ A B : AARAType} {q q₁ q₂ : Nat} (h : q₁ + q₂ ≤ q)
      (left : AARADerivation Γ₁ A q₁) (right : AARADerivation Γ₂ B q₂) :
      AARADerivation (.tensor Γ₁ Γ₂) (.tensor A B) q
  | swap {Γ₁ Γ₂ A : AARAType} {q : Nat} (body : AARADerivation (.tensor Γ₂ Γ₁) A q) :
      AARADerivation (.tensor Γ₁ Γ₂) A q
  | assocLeft {Γ₁ Γ₂ Γ₃ A : AARAType} {q : Nat}
      (body : AARADerivation (.tensor (.tensor Γ₁ Γ₂) Γ₃) A q) :
      AARADerivation (.tensor Γ₁ (.tensor Γ₂ Γ₃)) A q
  | assocRight {Γ₁ Γ₂ Γ₃ A : AARAType} {q : Nat}
      (body : AARADerivation (.tensor Γ₁ (.tensor Γ₂ Γ₃)) A q) :
      AARADerivation (.tensor (.tensor Γ₁ Γ₂) Γ₃) A q
  | unitLeft {Γ A : AARAType} {q : Nat} (body : AARADerivation Γ A q) :
      AARADerivation (.tensor .top Γ) A q
  | insertUnitLeft {Γ A : AARAType} {q : Nat} (body : AARADerivation (.tensor .top Γ) A q) :
      AARADerivation Γ A q
  | inl {Γ A B : AARAType} {q : Nat} (body : AARADerivation Γ A q) :
      AARADerivation Γ (.sum A B) q
  | inr {Γ A B : AARAType} {q : Nat} (body : AARADerivation Γ B q) :
      AARADerivation Γ (.sum A B) q
  | caseSum {Γ A B C : AARAType} {q : Nat}
      (left : AARADerivation (.tensor Γ A) C q) (right : AARADerivation (.tensor Γ B) C q) :
      AARADerivation (.tensor Γ (.sum A B)) C q
  | store {Γ A : AARAType} {q p q' : Nat} (h : p + q' ≤ q)
      (body : AARADerivation Γ A q') : AARADerivation Γ (.credit p A) q
  | release {Γ₁ Γ₂ A B : AARAType} {q p q₁ q₂ : Nat} (h : q₁ + q₂ ≤ q)
      (value : AARADerivation Γ₁ (.credit p A) q₁)
      (body : AARADerivation (.tensor Γ₂ A) B (p + q₂)) :
      AARADerivation (.tensor Γ₁ Γ₂) B q
  | nil1 {A : AARAType} (p q : Nat) : AARADerivation .top (.clist1 p A) q
  | cons1 {Γ₁ Γ₂ A : AARAType} {q p q₁ q₂ : Nat} (h : p + q₁ + q₂ ≤ q)
      (head : AARADerivation Γ₁ A q₁) (tail : AARADerivation Γ₂ (.clist1 p A) q₂) :
      AARADerivation (.tensor Γ₁ Γ₂) (.clist1 p A) q
  | fold1 {Γ A B : AARAType} {q p : Nat} (base : AARADerivation .top B 0)
      (step : AARADerivation (.tensor A B) B p) (list : AARADerivation Γ (.clist1 p A) q) :
      AARADerivation Γ B q
  | nil2 {A : AARAType} (p₁ p₂ q : Nat) : AARADerivation .top (.clist2 p₁ p₂ A) q
  | cons2 {Γ₁ Γ₂ A : AARAType} {q p₁ p₂ q₁ q₂ : Nat} (h : p₁ + q₁ + q₂ ≤ q)
      (head : AARADerivation Γ₁ A q₁)
      (tail : AARADerivation Γ₂ (.clist2 (p₂ + p₁) p₂ A) q₂) :
      AARADerivation (.tensor Γ₁ Γ₂) (.clist2 p₁ p₂ A) q
  | fold2 {Γ A : AARAType} {B : Nat → AARAType} {q p₁ p₂ : Nat}
      (base : (r : Nat) → AARADerivation .top (B r) 0)
      (step : (r : Nat) → AARADerivation (.tensor A (B (p₂ + r))) (B r) r)
      (list : AARADerivation Γ (.clist2 p₁ p₂ A) q) : AARADerivation Γ (B p₁) q

namespace AARADerivation

private def evalListFold {X : Type} {Y : Nat → Type} (next : Nat → Nat)
    (base : (r : Nat) → Nat × Y r) (step : (r : Nat) → X × Y (next r) → Nat × Y r) :
    (r : Nat) → List X → Nat × Y r
  | r, [] => base r
  | r, x :: xs =>
      let tail := evalListFold next base step (next r) xs
      let result := step r (x, tail.2)
      (tail.1 + result.1, result.2)

/-- Evaluate a derivation on a linear environment, returning concrete cost and value. -/
def eval {Γ A : AARAType} {q : Nat} (d : AARADerivation Γ A q) :
    aaraValues Γ → Nat × aaraValues A :=
  match d with
  | .var _ => fun x ↦ (0, x)
  | .letBind _ value body => fun (x, y) ↦
      let v := value.eval x
      let result := body.eval (y, v.2)
      (v.1 + result.1, result.2)
  | .spend (p := p) _ body => fun x ↦
      let result := body.eval x
      (p + result.1, result.2)
  | .weaken _ body => body.eval
  | .ret x _ => fun _ ↦ (0, x)
  | .read body => fun (x, δ) ↦ (body x).eval δ
  | .tensorIntro _ left right => fun (x, y) ↦
      let a := left.eval x
      let b := right.eval y
      (a.1 + b.1, (a.2, b.2))
  | .swap body => fun (x, y) ↦ body.eval (y, x)
  | .assocLeft body => fun (x, y, z) ↦ body.eval ((x, y), z)
  | .assocRight body => fun ((x, y), z) ↦ body.eval (x, y, z)
  | .unitLeft body => fun (_, x) ↦ body.eval x
  | .insertUnitLeft body => fun x ↦ body.eval (PUnit.unit, x)
  | .inl body => fun x ↦
      let result := body.eval x
      (result.1, .inl result.2)
  | .inr body => fun x ↦
      let result := body.eval x
      (result.1, .inr result.2)
  | .caseSum left right => fun (δ, s) ↦
      match s with
      | .inl x => left.eval (δ, x)
      | .inr y => right.eval (δ, y)
  | .store _ body => body.eval
  | .release _ value body => fun (x, y) ↦
      let v := value.eval x
      let result := body.eval (y, v.2)
      (v.1 + result.1, result.2)
  | .nil1 _ _ => fun _ ↦ (0, [])
  | .cons1 _ head tail => fun (x, y) ↦
      let h := head.eval x
      let t := tail.eval y
      (h.1 + t.1, h.2 :: t.2)
  | .fold1 (B := B) (p := p) base step list => fun x ↦
      let v := list.eval x
      let result := evalListFold (Y := fun _ ↦ aaraValues B) id
        (fun _ ↦ base.eval PUnit.unit) (fun _ ↦ step.eval) p v.2
      (v.1 + result.1, result.2)
  | .nil2 _ _ _ => fun _ ↦ (0, [])
  | .cons2 _ head tail => fun (x, y) ↦
      let h := head.eval x
      let t := tail.eval y
      (h.1 + t.1, h.2 :: t.2)
  | .fold2 (B := B) (p₁ := p₁) (p₂ := p₂) base step list => fun x ↦
      let v := list.eval x
      let result := evalListFold (Y := fun r ↦ aaraValues (B r)) (p₂ + ·)
        (fun r ↦ (base r).eval PUnit.unit) (fun r ↦ (step r).eval) p₁ v.2
      (v.1 + result.1, result.2)
termination_by structural d

private theorem evalListFold_bound {X : Type} {Y : Nat → Type} (next : Nat → Nat)
    (base : (r : Nat) → Nat × Y r) (step : (r : Nat) → X × Y (next r) → Nat × Y r)
    (credit : Nat → Nat) (inputPotential : X → Nat) (listPotential : Nat → List X → Nat)
    (outputPotential : (r : Nat) → Y r → Nat)
    (hCons : ∀ r x xs, listPotential r (x :: xs) =
      credit r + inputPotential x + listPotential (next r) xs)
    (hBase : ∀ r, (base r).1 + outputPotential r (base r).2 ≤ listPotential r [])
    (hStep : ∀ r x y, (step r (x, y)).1 + outputPotential r (step r (x, y)).2 ≤
      inputPotential x + outputPotential (next r) y + credit r)
    (r : Nat) (xs : List X) :
    (evalListFold next base step r xs).1 +
      outputPotential r (evalListFold next base step r xs).2 ≤ listPotential r xs := by
  induction xs generalizing r with
  | nil => exact hBase r
  | cons x xs ih =>
      rw [hCons]
      let tail := evalListFold next base step (next r) xs
      change tail.1 + (step r (x, tail.2)).1 + outputPotential r (step r (x, tail.2)).2 ≤ _
      have hTail : tail.1 + outputPotential (next r) tail.2 ≤ listPotential (next r) xs :=
        ih (next r)
      have hHead := hStep r x tail.2
      omega

/-- Every rule preserves the available credits, accounting for the evaluated subterms and
for the transfer of credits into and out of the value. -/
private theorem eval_bound {Γ A : AARAType} {q : Nat} (d : AARADerivation Γ A q)
    (x : aaraValues Γ) : (d.eval x).1 + aaraPotential A (d.eval x).2 ≤ aaraPotential Γ x + q := by
  induction d with
  | var => simp [eval]
  | letBind _ value body ihValue ihBody =>
      rcases x with ⟨x, y⟩
      have hValue := ihValue x
      have hBody := ihBody (y, (value.eval x).2)
      simp only [eval, aaraPotential] at hBody ⊢
      omega
  | spend _ body ih =>
      have hBody := ih x
      simp only [eval]
      omega
  | weaken h _ ih => exact Nat.le_trans (ih x) (Nat.add_le_add_left h _)
  | ret => simp [eval, aaraPotential]
  | read body ih =>
      rcases x with ⟨x, y⟩
      simpa only [eval, aaraPotential, Nat.zero_add] using ih x y
  | tensorIntro _ _ _ ihLeft ihRight =>
      rcases x with ⟨x, y⟩
      have hLeft := ihLeft x
      have hRight := ihRight y
      simp only [eval, aaraPotential]
      omega
  | swap _ ih =>
      rcases x with ⟨x, y⟩
      have h := ih (y, x)
      simp only [eval, aaraPotential] at h ⊢
      omega
  | assocLeft _ ih =>
      rcases x with ⟨x, y, z⟩
      simpa only [eval, aaraPotential, Nat.add_assoc] using ih ((x, y), z)
  | assocRight _ ih =>
      rcases x with ⟨⟨x, y⟩, z⟩
      simpa only [eval, aaraPotential, Nat.add_assoc] using ih (x, y, z)
  | unitLeft _ ih =>
      rcases x with ⟨_, x⟩
      simpa only [eval, aaraPotential, Nat.zero_add] using ih x
  | insertUnitLeft _ ih =>
      simpa only [eval, aaraPotential, Nat.zero_add] using ih (PUnit.unit, x)
  | inl _ ih => simpa only [eval, aaraPotential] using ih x
  | inr _ ih => simpa only [eval, aaraPotential] using ih x
  | caseSum _ _ ihLeft ihRight =>
      rcases x with ⟨δ, a | b⟩
      · simpa only [eval, aaraPotential] using ihLeft (δ, a)
      · simpa only [eval, aaraPotential] using ihRight (δ, b)
  | store _ body ih =>
      have hBody := ih x
      simp only [eval, aaraPotential]
      omega
  | release _ value body ihValue ihBody =>
      rcases x with ⟨x, y⟩
      have hValue := ihValue x
      have hBody := ihBody (y, (value.eval x).2)
      simp only [aaraPotential] at hValue hBody
      simp only [eval, aaraPotential]
      omega
  | nil1 => simp [eval, aaraPotential, listPotentialSum]
  | cons1 _ _ _ ihHead ihTail =>
      rcases x with ⟨x, y⟩
      have hHead := ihHead x
      have hTail := ihTail y
      simp only [eval]
      erw [aaraPotential_clist1_cons]
      simp only [aaraPotential] at hTail ⊢
      omega
  | @fold1 Γ A B q p base step list ihBase ihStep ihList =>
      have hFold := evalListFold_bound (Y := fun _ ↦ aaraValues B) id
        (fun _ ↦ base.eval PUnit.unit) (fun _ ↦ step.eval) (fun _ ↦ p) (aaraPotential A)
        (fun _ ↦ aaraPotential (.clist1 p A)) (fun _ ↦ aaraPotential B)
        (fun _ y ys ↦ aaraPotential_clist1_cons p A y ys)
        (fun _ ↦ by simpa [aaraPotential, listPotentialSum] using ihBase PUnit.unit)
        (fun _ y z ↦ by simpa only [aaraPotential] using ihStep (y, z)) p (list.eval x).2
      have hList := ihList x
      simp only [eval]
      omega
  | nil2 => simp [eval, aaraPotential, listPotentialSum, binom2]
  | cons2 _ _ _ ihHead ihTail =>
      rcases x with ⟨x, y⟩
      have hHead := ihHead x
      have hTail := ihTail y
      simp only [eval]
      erw [aaraPotential_clist2_cons]
      simp only [aaraPotential] at hTail ⊢
      omega
  | @fold2 Γ A B q p₁ p₂ base step list ihBase ihStep ihList =>
      have hFold := evalListFold_bound (Y := fun r ↦ aaraValues (B r)) (p₂ + ·)
        (fun r ↦ (base r).eval PUnit.unit) (fun r ↦ (step r).eval) (fun r ↦ r) (aaraPotential A)
        (fun r ↦ aaraPotential (.clist2 r p₂ A)) (fun r ↦ aaraPotential (B r))
        (fun r y ys ↦ aaraPotential_clist2_cons r p₂ A y ys)
        (fun r ↦ by simpa [aaraPotential, listPotentialSum, binom2] using ihBase r PUnit.unit)
        (fun r y z ↦ by simpa only [aaraPotential] using ihStep r (y, z)) p₁ (list.eval x).2
      have hList := ihList x
      simp only [eval]
      omega

private def evalFreeHom {X Y : Type} (f : X → Nat × Y) :
    CostHom (FreeCostAlg X) (FreeCostAlg Y) where
  fn := fun (c, x) ↦ (c + (f x).1, (f x).2)
  map_charge := fun c (c', x) ↦ Prod.ext (Nat.add_assoc c c' (f x).1) rfl
  mono := by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨h, rfl⟩
    exact ⟨Nat.add_le_add_right h _, rfl⟩

/-- Interpret a derivation as a Calf program from its credited tensor context.
Its abstract homomorphism runs the same program on values with zero added cost. -/
def interpret {Γ A : AARAType} {q : Nat} (d : AARADerivation Γ A q) :
    LaxCompHom (CreditComp q (interpPositiveAARA Γ)) (interpPositiveAARA A) where
  hom_top := evalFreeHom d.eval
  hom_abs := evalFreeHom (fun x ↦ (0, (d.eval x).2))
  lax_comm := by
    rintro ⟨c, x⟩
    change (FreeCostAlg (aaraValues A)).le
      ((interpPositiveAARA A).alpha.fn (c + (d.eval x).1, (d.eval x).2))
      ((q + ((interpPositiveAARA Γ).alpha.fn (c, x)).1) + 0,
        (d.eval ((interpPositiveAARA Γ).alpha.fn (c, x)).2).2)
    rw [interpPositiveAARA_alpha, interpPositiveAARA_alpha]
    have h := eval_bound d x
    exact ⟨by dsimp; omega, rfl⟩

@[simp]
theorem interpret_top_fn {Γ A : AARAType} {q : Nat} (d : AARADerivation Γ A q)
    (c : Nat) (x : aaraValues Γ) :
    d.interpret.hom_top.fn (c, x) = (c + (d.eval x).1, (d.eval x).2) := rfl

@[simp]
theorem interpret_abs_fn {Γ A : AARAType} {q : Nat} (d : AARADerivation Γ A q)
    (c : Nat) (x : aaraValues Γ) : d.interpret.hom_abs.fn (c, x) = (c, (d.eval x).2) := rfl

end AARADerivation
end Grodin2026.Revised


