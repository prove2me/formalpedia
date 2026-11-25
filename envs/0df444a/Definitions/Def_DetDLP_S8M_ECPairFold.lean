-- Prove2me | Definitions.Def_DetDLP_S8M_ECPairFold
-- name    : DetDLP_S8M_ECPairFold
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:48:10.934751+00:00
-- url     : https://prove2.me/theorems/71d5816b-a18b-46bd-a253-3ada99bb8655
-- title:
--   Certified short Weierstrass addition fold
-- statement:
--   Replaying a list of short-form addition tiles checks the sum from an initial accumulator, with one certificate per remaining point. Every valid input has a unique trace for the correct sum.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8K_ECAddArithmetic

set_option autoImplicit false
namespace DetDLP.S8M.ECPair.Fold
open S8K S8K.ECAddArithmetic S8H.ECPointArithmetic

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))

abbrev Step (p : ℕ) := Coords p × AddCert p

/-- A replay checks every intermediate output on its own addition tile;
    the initial accumulator is supplied by the first conversion tile. -/
def replay (a : Coords p) (xs : List (Coords p)) (target : Coords p) (cs : List (Step p)) : Prop :=
  match xs,cs with
  | [],[] => a = target
  | x::xs, c::cs => swAddOK E a x c.1 c.2 ∧ replay c.1 xs target cs
  | _,_ => False

theorem replay_length {a o : Coords p} {xs : List (Coords p)} {cs : List (Step p)}
    (h : replay E a xs o cs) : cs.length = xs.length := by
  induction xs generalizing a cs with
  | nil => cases cs <;> simp_all [replay]
  | cons x xs ih => cases cs with
    | nil => exact False.elim h
    | cons c cs => exact congrArg Nat.succ (ih h.2)

abbrev P := (SWEquiv.short E).toAffine.Point

theorem replay_sound (mul : w3_modMulInterface) (a : P E) (xs : List (P E)) (o : Coords p)
    (cs : List (Step p)) (h : replay E (coords a) (xs.map coords) o cs) :
    o = coords (a + xs.sum) := by
  induction xs generalizing a cs with
  | nil => cases cs with
    | nil => simpa using (show coords a = o from h).symm
    | cons _ _ => exact False.elim h
  | cons x xs ih => cases cs with
    | nil => exact False.elim h
    | cons c cs =>
      have hh : swAddOK E (coords a) (coords x) c.1 c.2 ∧ replay E c.1 (xs.map coords) o cs := h
      have eq := swAdd_sound E mul a x _ _ hh.1
      have ht := hh.2
      rw [eq] at ht
      simpa [List.sum_cons,add_assoc] using ih (a+x) cs ht

theorem replay_unique (mul : w3_modMulInterface) (a : P E) (xs : List (P E)) :
    ∃! cs, replay E (coords a) (xs.map coords) (coords (a+xs.sum)) cs := by
  induction xs generalizing a with
  | nil =>
    refine ⟨[],by simp [replay],?_⟩
    intro cs h; cases cs with
    | nil => rfl
    | cons _ _ => exact False.elim h
  | cons x xs ih =>
    obtain ⟨d,hd,ud⟩ := swAdd_unique E mul a x
    obtain ⟨s,hs,us⟩ := ih (a+x)
    rw [List.sum_cons,← add_assoc]
    refine ⟨(coords (a+x),d)::s,⟨hd,hs⟩,?_⟩
    intro l h
    cases l with
    | nil => exact False.elim h
    | cons c tail =>
      rcases c with ⟨out,cert⟩
      have hh : swAddOK E (coords a) (coords x) out cert ∧
          replay E out (xs.map coords) (coords ((a+x)+xs.sum)) tail := h
      obtain rfl := swAdd_sound E mul a x out cert hh.1
      rw [ud cert hh.1,us tail hh.2]

end DetDLP.S8M.ECPair.Fold


