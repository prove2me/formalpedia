-- Prove2me | Definitions.Def_KirkmanLib_Constructions
-- name    : KirkmanLib_Constructions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:40:13.547558+00:00
-- url     : https://prove2.me/theorems/44e41d04-fa75-42b4-b179-a890b560a7ef
-- title:
--   Constructions
-- statement:
--   Definitions and structural lemmas for Constructions, from Juan Pablo Traverso Gianini (jtraverso/kirkman-steiner-triple-systems; see pinned Apache-2.0 LICENSE and source headers)'s pinned Kirkman theorem on existence of Steiner triple systems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Constructions.lean

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Kirkman
structure CQ (Q : Type*) where
  /-- The multiplication. -/
  L : Q → Q → Q
  /-- The left division: `L x (D x y) = y`. -/
  D : Q → Q → Q
  comm : ∀ x y, L x y = L y x
  LD : ∀ x y, L x (D x y) = y
  DL : ∀ x y, D x (L x y) = y
section ZThree
lemma z3_succ_ne (i : ZMod 3) : i + 1 ≠ i := by revert i; decide
lemma z3_succ_ne' (i : ZMod 3) : i ≠ i + 1 := fun h => z3_succ_ne i h.symm
lemma z3_pred_ne (i : ZMod 3) : i - 1 ≠ i := by revert i; decide
lemma z3_third_ne {i j : ZMod 3} (h : i ≠ j) : -(i + j) ≠ i := by revert i j; decide
lemma z3_third_third {i j : ZMod 3} (h : i ≠ j) : -(i + -(i + j)) = j := by revert i j; decide
lemma z3_other {i j : ZMod 3} (h : i ≠ j) (h' : j ≠ i + 1) : i = j + 1 := by revert i j; decide
lemma z3_not_both {i j : ZMod 3} (h : j = i + 1) : i ≠ j + 1 := by revert i j; decide
lemma z3_pred_ne_succ (i : ZMod 3) : i - 1 ≠ i + 1 := by revert i; decide
lemma z3_eq_pred {i j : ZMod 3} (h : i = j + 1) : j = i - 1 := by rw [h]; ring
end ZThree
namespace CQ
variable {Q : Type*} (q : CQ Q)
lemma L_inj {x y y' : Q} (h : q.L x y = q.L x y') : y = y' := by
  rw [← q.DL x y, h, q.DL]
lemma D_eq_iff {x y a : Q} : q.D x y = a ↔ q.L x a = y := by
  constructor
  · rintro rfl; exact q.LD x y
  · rintro rfl; exact q.DL x a
end CQ
section Bose
variable {Q : Type*} [DecidableEq Q] (q : CQ Q) (hid : ∀ x, q.L x x = x)
def boseOp (p r : Q × ZMod 3) : Q × ZMod 3 :=
  if p.2 = r.2 then (if p.1 = r.1 then p else (q.L p.1 r.1, p.2 + 1))
  else if p.1 = r.1 then (p.1, -(p.2 + r.2))
  else if r.2 = p.2 + 1 then (q.D p.1 r.1, p.2)
  else (q.D r.1 p.1, r.2)
include hid
omit [DecidableEq Q] in
lemma bose_L_ne {x y : Q} (h : x ≠ y) : q.L x y ≠ x := by
  intro e
  have e' : q.L x y = q.L x x := by rw [hid]; exact e
  exact h (q.L_inj e').symm
omit [DecidableEq Q] in
lemma bose_D_ne {x y : Q} (h : x ≠ y) : q.D x y ≠ x := by
  intro e; apply h; rw [q.D_eq_iff, hid] at e; exact e
omit hid in
lemma bose_comm (p r : Q × ZMod 3) : boseOp q p r = boseOp q r p := by
  obtain ⟨x, i⟩ := p
  obtain ⟨y, j⟩ := r
  simp only [boseOp]
  by_cases hij : i = j
  · subst hij
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy, Ne.symm hxy, q.comm x y]
  · have hji : j ≠ i := Ne.symm hij
    rw [if_neg hij, if_neg hji]
    by_cases hxy : x = y
    · subst hxy; simp [add_comm]
    · rw [if_neg hxy, if_neg (Ne.symm hxy)]
      by_cases h1 : j = i + 1
      · rw [if_pos h1, if_neg (z3_not_both h1)]
      · rw [if_neg h1, if_pos (z3_other hij h1)]
lemma bose_cancel (p r : Q × ZMod 3) : boseOp q p (boseOp q p r) = r := by
  obtain ⟨x, i⟩ := p
  obtain ⟨y, j⟩ := r
  by_cases hij : i = j
  · subst hij
    by_cases hxy : x = y
    · subst hxy; simp [boseOp]
    · have h1 : boseOp q (x, i) (y, i) = (q.L x y, i + 1) := by simp [boseOp, hxy]
      rw [h1]
      simp only [↓reduceIte, boseOp, if_neg (z3_succ_ne' i),
        if_neg (Ne.symm (bose_L_ne q hid hxy)),
        q.DL]
  · by_cases hxy : x = y
    · subst hxy
      have h1 : boseOp q (x, i) (x, j) = (x, -(i + j)) := by simp [boseOp, hij]
      rw [h1]
      simp only [↓reduceIte, boseOp, if_neg (Ne.symm (z3_third_ne hij)), z3_third_third hij]
    · by_cases h2 : j = i + 1
      · have h1 : boseOp q (x, i) (y, j) = (q.D x y, i) := by simp [boseOp, hxy, h2]
        rw [h1]
        simp only [↓reduceIte, boseOp, if_neg (Ne.symm (bose_D_ne q hid hxy)), q.LD, h2]
      · have h1 : boseOp q (x, i) (y, j) = (q.D y x, j) := by simp [boseOp, hij, hxy, h2]
        rw [h1]
        have hi : i = j + 1 := z3_other hij h2
        have hne : x ≠ q.D y x := by
          intro e
          rw [eq_comm, q.D_eq_iff] at e
          have e2 : q.L x y = q.L x x := by rw [q.comm, e, hid]
          exact hxy (q.L_inj e2).symm
        have hdd : q.D (q.D y x) x = y := by
          rw [q.D_eq_iff, q.comm, q.LD]
        simp only [boseOp, if_neg hij, if_neg hne, if_neg h2, hdd]
def boseSteiner : SteinerOp (Q × ZMod 3) where
  op := boseOp q
  comm := bose_comm q
  idem := fun p => by simp [boseOp]
  cancel := bose_cancel q hid
end Bose
structure HalfIdem (Q : Type*) extends CQ Q where
  /-- The involution. -/
  τ : Q → Q
  /-- The first half. -/
  H : Q → Prop
  [decH : DecidablePred H]
  ττ : ∀ x, τ (τ x) = x
  Hτ : ∀ x, H (τ x) ↔ ¬ H x
  Lτ : ∀ x, L (τ x) (τ x) = L x x
  LH : ∀ x, H x → L x x = x
attribute [instance] HalfIdem.decH
namespace HalfIdem
variable {Q : Type*} (q : HalfIdem Q)
lemma L_self_not {x : Q} (hx : ¬ q.H x) : q.L x x = q.τ x := by
  have h1 := q.Lτ (q.τ x)
  rw [q.ττ] at h1
  rw [h1]
  exact q.LH _ ((q.Hτ x).2 hx)
lemma τ_ne (x : Q) : q.τ x ≠ x := by
  intro e
  have := q.Hτ x
  rw [e] at this
  tauto
end HalfIdem
section Skolem
variable {Q : Type*} [DecidableEq Q] (q : HalfIdem Q)
def skInf (z : Q) (i : ZMod 3) : Q × ZMod 3 := (q.τ z, if q.H z then i - 1 else i + 1)
def skOp : Option (Q × ZMod 3) → Option (Q × ZMod 3) → Option (Q × ZMod 3)
  | none, none => none
  | none, some (z, i) => some (skInf q z i)
  | some (z, i), none => some (skInf q z i)
  | some (x, i), some (y, j) =>
    if i = j then (if x = y then some (x, i) else some (q.L x y, i + 1))
    else if x = y ∧ q.H x then some (x, -(i + j))
    else if j = i + 1 then (if q.D x y = x then none else some (q.D x y, i))
    else (if q.D y x = y then none else some (q.D y x, j))
omit [DecidableEq Q] in
lemma sk_inf_inf (z : Q) (i : ZMod 3) : skInf q (skInf q z i).1 (skInf q z i).2 = (z, i) := by
  unfold skInf
  by_cases hz : q.H z
  · have : ¬ q.H (q.τ z) := by rw [q.Hτ]; exact not_not.2 hz
    simp [hz, this, q.ττ]
  · have : q.H (q.τ z) := (q.Hτ z).2 hz
    simp [hz, this, q.ττ]
lemma sk_comm (p r : Option (Q × ZMod 3)) : skOp q p r = skOp q r p := by
  rcases p with _ | ⟨x, i⟩ <;> rcases r with _ | ⟨y, j⟩
  · rfl
  · rfl
  · rfl
  · simp only [skOp]
    by_cases hij : i = j
    · subst hij
      by_cases hxy : x = y
      · subst hxy; simp
      · simp [hxy, Ne.symm hxy, q.comm x y]
    · rw [if_neg hij, if_neg (Ne.symm hij)]
      by_cases hxy : x = y ∧ q.H x
      · obtain ⟨rfl, hx⟩ := hxy
        simp [hx, add_comm]
      · have hyx : ¬ (y = x ∧ q.H y) := by
          rintro ⟨rfl, hy⟩; exact hxy ⟨rfl, hy⟩
        rw [if_neg hxy, if_neg hyx]
        by_cases h1 : j = i + 1
        · rw [if_pos h1, if_neg (z3_not_both h1)]
        · rw [if_neg h1, if_pos (z3_other hij h1)]
lemma sk_cancel (p r : Option (Q × ZMod 3)) : skOp q p (skOp q p r) = r := by
  rcases p with _ | ⟨x, i⟩ <;> rcases r with _ | ⟨y, j⟩
  · rfl
  · change skOp q none (some (skInf q y j)) = some (y, j)
    simp only [skOp, sk_inf_inf]
  · change skOp q (some (x, i)) (some (skInf q x i)) = none
    unfold skInf
    by_cases hx : q.H x
    · simp only [skOp, if_pos hx]
      rw [if_neg (Ne.symm (z3_pred_ne i)),
        if_neg (fun h : x = q.τ x ∧ q.H x => q.τ_ne x h.1.symm),
        if_neg (z3_pred_ne_succ i)]
      have : q.D (q.τ x) x = q.τ x := by rw [q.D_eq_iff, q.Lτ, q.LH x hx]
      rw [if_pos this]
    · simp only [↓reduceIte, skOp, if_neg hx]
      rw [if_neg (z3_succ_ne' i), if_neg (fun h : x = q.τ x ∧ q.H x => hx h.2)]
      have : q.D x (q.τ x) = x := by rw [q.D_eq_iff, q.L_self_not hx]
      rw [if_pos this]
  · by_cases hij : i = j
    · subst hij
      by_cases hxy : x = y
      · subst hxy; simp [skOp]
      · have h1 : skOp q (some (x, i)) (some (y, i)) = some (q.L x y, i + 1) := by
          simp [skOp, hxy]
        rw [h1]
        have hnot : ¬ (x = q.L x y ∧ q.H x) := by
          rintro ⟨e, hx⟩
          have e2 : q.L x y = q.L x x := by rw [q.LH x hx]; exact e.symm
          exact hxy (q.L_inj e2).symm
        have hD : q.D x (q.L x y) ≠ x := by rw [q.DL]; exact Ne.symm hxy
        simp only [↓reduceIte, skOp, if_neg (z3_succ_ne' i), if_neg hnot,
          q.DL, if_neg (Ne.symm hxy)]
    · by_cases hxy : x = y ∧ q.H x
      · obtain ⟨rfl, hx⟩ := hxy
        have h1 : skOp q (some (x, i)) (some (x, j)) = some (x, -(i + j)) := by
          simp [skOp, hij, hx]
        rw [h1]
        simp only [↓reduceIte, skOp, if_neg (Ne.symm (z3_third_ne hij)),
          true_and, if_pos hx, z3_third_third hij]
      · by_cases h2 : j = i + 1
        · by_cases hD : q.D x y = x
          · have h1 : skOp q (some (x, i)) (some (y, j)) = none := by
              simp only [skOp, if_neg hij, if_neg hxy, if_pos h2,
                if_pos hD]
            rw [h1]
            have hy : y = q.L x x := by have := q.LD x y; rw [hD] at this; exact this.symm
            have hx : ¬ q.H x := by
              intro hx; exact hxy ⟨by rw [hy, q.LH x hx], hx⟩
            change some (skInf q x i) = some (y, j)
            simp only [skInf, if_neg hx, hy, q.L_self_not hx, h2]
          · have h1 : skOp q (some (x, i)) (some (y, j)) = some (q.D x y, i) := by
              simp only [skOp, if_neg hij, if_neg hxy, if_pos h2,
                if_neg hD]
            rw [h1]
            simp only [↓reduceIte, skOp, if_neg (Ne.symm hD), q.LD, h2]
        · have hi : i = j + 1 := z3_other hij h2
          by_cases hD : q.D y x = y
          · have h1 : skOp q (some (x, i)) (some (y, j)) = none := by
              simp only [skOp, if_neg hij, if_neg hxy, if_neg h2,
                if_pos hD]
            rw [h1]
            have hx' : x = q.L y y := by have := q.LD y x; rw [hD] at this; exact this.symm
            have hy : ¬ q.H y := by
              intro hy
              have : x = y := by rw [hx', q.LH y hy]
              exact hxy ⟨this, this ▸ hy⟩
            have hxτ : x = q.τ y := by rw [hx', q.L_self_not hy]
            have hHx : q.H x := by rw [hxτ]; exact (q.Hτ y).2 hy
            change some (skInf q x i) = some (y, j)
            have hHτ : q.H (q.τ y) := (q.Hτ y).2 hy
            simp only [skInf, hxτ, q.ττ, z3_eq_pred hi,
              if_pos hHτ]
          · have h1 : skOp q (some (x, i)) (some (y, j)) = some (q.D y x, j) := by
              simp only [skOp, if_neg hij, if_neg hxy, if_neg h2,
                if_neg hD]
            rw [h1]
            set z := q.D y x with hz
            have hLz : q.L z y = x := by rw [q.comm, hz, q.LD]
            have hdz : q.D z x = y := by rw [q.D_eq_iff, hLz]
            have hnot : ¬ (x = z ∧ q.H x) := by
              rintro ⟨e, hx⟩
              apply hxy
              refine ⟨?_, hx⟩
              have : q.L x y = q.L x x := by rw [q.LH x hx]; nth_rewrite 1 [e]; exact hLz
              exact (q.L_inj this).symm
            have hzy : q.D z x ≠ z := by rw [hdz]; exact Ne.symm hD
            simp only [skOp, if_neg hij, if_neg hnot, if_neg h2,
              hdz, if_neg (Ne.symm hD)]
def skolemSteiner : SteinerOp (Option (Q × ZMod 3)) where
  op := skOp q
  comm := sk_comm q
  idem := fun p => by rcases p with _ | ⟨x, i⟩ <;> simp [skOp]
  cancel := sk_cancel q
end Skolem
end Kirkman


