-- Prove2me | Definitions.Def_DetDLP_S8M_ECPairWitness
-- name    : DetDLP_S8M_ECPairWitness
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:33:54.853177+00:00
-- url     : https://prove2.me/theorems/d32f1ba5-ae68-4eca-a5ca-9bd0c0f59149
-- title:
--   Elliptic curve tuple-pair trace equivalence
-- statement:
--   Private helper definition in the elliptic-curve pair-query development.
-- source:
--   S. Liu, B. Zhang, and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University Preprint, Section 2.4 and 3.1–3.2

import Definitions.Def_DetDLP_S8M_ECPairFold

set_option autoImplicit false
namespace DetDLP.S8M.ECPair.Witness
open S8K S8K.ECAddArithmetic S8H.ECPointArithmetic

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (hp : 3 < p)
abbrev P := E.toAffine.Point
abbrev Conv (p : ℕ) := Coords p × MapCert p

def mapOK (xs : List (P E)) (cs : List (Conv p)) : Prop :=
  match xs,cs with
  | [], [] => True
  | x::xs, c::cs => ecToSWOK E (coords x) c.1 c.2 ∧ mapOK xs cs
  | _,_ => False

noncomputable def sw (hp : 3 < p) := SWEquiv.equiv E (SWEquiv.six_ne_zero hp)

theorem map_sound (hp : 3 < p) (mul : w3_modMulInterface) (xs : List (P E)) (cs : List (Conv p)) (h : mapOK E xs cs) :
    cs.map Prod.fst = (xs.map (sw E hp)).map coords := by
  induction xs generalizing cs with
  | nil => cases cs with
    | nil => rfl
    | cons _ _ => exact False.elim h
  | cons x xs ih => cases cs with
    | nil => exact False.elim h
    | cons c cs => exact congrArg₂ List.cons (ecToSW_sound E hp mul x _ _ h.1) (ih _ h.2)

theorem map_unique (hp : 3 < p) (mul : w3_modMulInterface) (xs : List (P E)) : ∃! cs, mapOK E xs cs := by
  induction xs with
  | nil =>
    refine ⟨[],trivial,?_⟩; intro l h; cases l with
    | nil => rfl
    | cons _ _ => exact False.elim h
  | cons x xs ih =>
    obtain ⟨c,hc,uc⟩ := ecToSW_unique E hp mul x
    obtain ⟨s,hs,us⟩ := ih
    refine ⟨(coords (sw E hp x),c)::s,⟨hc,hs⟩,?_⟩
    intro l h; cases l with
    | nil => exact False.elim h
    | cons z zs =>
      rcases z with ⟨out,d⟩
      have H : ecToSWOK E (coords x) out d ∧ mapOK E xs zs := h
      obtain rfl := ecToSW_sound E hp mul x out d H.1
      rw [uc d H.1,us zs H.2]; rfl

def interleave {G : Type} {m : ℕ} (ab : (Fin m → G) × (Fin m → G)) :=
  (List.ofFn fun i => [ab.1 i, ab.2 i]).flatten

theorem interleave_length {G : Type} {m : ℕ} (ab : (Fin m → G) × (Fin m → G)) :
    (interleave ab).length = 2*m := by
  simp [interleave,List.length_flatten,List.map_ofFn,Function.comp_def]; omega

theorem interleave_sum {G : Type} [AddCommMonoid G] {m : ℕ} (ab : (Fin m → G) × (Fin m → G)) :
    (interleave ab).sum = ∑ i, (ab.1 i + ab.2 i) := by
  simp [interleave,List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]

def checkFold (o : Coords p) (xs : List (Coords p)) (cs : List (Fold.Step p)) :=
  match xs with
  | [] => False
  | a::ys => Fold.replay E a ys o cs

abbrev Trace (p : ℕ) := List (Conv p) × List (Fold.Step p)

def ok (xs : List (P E)) (o : Coords p) (w : Trace p) :=
  mapOK E xs w.1 ∧ checkFold E o (w.1.map Prod.fst) w.2

private theorem coord_inj {A : WeierstrassCurve (ZMod p)} {a b : A.toAffine.Point} (h : coords a = coords b) : a = b := by
  cases a <;> cases b <;> simp_all [coords]

theorem sound (mul : w3_modMulInterface) (a : P E) (ys : List (P E)) (X : P E) (w : Trace p)
    (h : ok E (a::ys) (coords (sw E hp X)) w) : (a::ys).sum = X := by
  have H := h.2
  rw [map_sound E hp mul _ _ h.1] at H
  have r := Fold.replay_sound E mul (sw E hp a) (ys.map (sw E hp)) _ _ H
  apply (sw E hp).injective
  apply coord_inj
  simpa [List.sum_cons,map_add,map_list_sum] using r.symm

theorem complete (mul : w3_modMulInterface) (a : P E) (ys : List (P E)) :
    ∃! w, ok E (a::ys) (coords (sw E hp (a::ys).sum)) w := by
  obtain ⟨c,hc,uc⟩ := map_unique E hp mul (a::ys)
  obtain ⟨d,hd,ud⟩ := Fold.replay_unique E mul (sw E hp a) (ys.map (sw E hp))
  have H (ds : List (Fold.Step p)) : checkFold E (coords (sw E hp (a::ys).sum)) (c.map Prod.fst) ds ↔
      Fold.replay E (coords (sw E hp a)) ((ys.map (sw E hp)).map coords)
        (coords (sw E hp a+(ys.map (sw E hp)).sum)) ds := by
    rw [map_sound E hp mul _ _ hc]; simp [List.sum_cons,map_add,map_list_sum,checkFold]
  refine ⟨(c,d),⟨hc,(H d).mpr hd⟩,?_⟩
  rintro ⟨t,s⟩ ⟨ht,hs⟩; obtain rfl := uc t ht; exact Prod.ext rfl (ud s ((H s).mp hs))

end DetDLP.S8M.ECPair.Witness


