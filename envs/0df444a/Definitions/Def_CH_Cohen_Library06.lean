-- Prove2me | Definitions.Def_CH_Cohen_Library06
-- name    : CH_Cohen_Library06
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-26T01:52:28.692745+00:00
-- url     : https://prove2.me/theorems/314abdc9-952c-4862-a3e5-f8817aadd6cb
-- title:
--   Boolean-valued set theory: Bfol, SetTheoryExt, RegularOpenAlgebra, CantorSpace, Colimit
-- statement:
--   This module provides Boolean-valued structures and formula interpretation; topological bases and finite-set combinatorial interfaces; the complete Boolean algebra of regular open sets; finite-coordinate basic open sets in binary product spaces; direct-limit constructions for language extensions. These objects form the language and model interfaces used in the forcing and completeness arguments.
--
--   **Formalization Note** The module retains the structural normalization facts needed by these definitions and their constructor proofs. The principal forcing and model-existence assertions are separate theorem nodes.
--
--   Original formalization: Jesse Han and Floris van Doorn. Lean 4 port: Ian Klatzco, with Claude (Apache-2.0). Adapted to the pinned Prove2Me environment.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Bfol.lean; https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/SetTheoryExt.lean; https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/RegularOpenAlgebra.lean; https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/CantorSpace.lean; https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Colimit.lean

import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.Sets.Opens
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Order.Zorn
import Mathlib.Data.Set.Card
import Mathlib.Topology.Clopen
import Mathlib.Topology.Constructions
import Mathlib.Data.PFun
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_CH_Cohen_Library05
/-
Physical source: Flypitch, Jesse Han and Floris van Doorn (Apache-2.0).
Lean 4 port: Ian Klatzco, with Claude.
Upstream commit ad649f89e9f3107b7e2ea97a58b2eafdfc80b815.
Original notices and source statements are retained.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/- Source module: Definitions.Flypitch4.Bfol -/
section CohenSource_Bfol
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/bfol.lean lines 1-450:
   Boolean-valued first-order logic — bStructure + early semantics. -/




set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open DVec

namespace Fol

section bfol

/-! ## bStructure — boolean-valued L-structure -/

/-- An L-Structure valued in a complete boolean algebra β.
    Analogous to `Structure L` from Fol.lean, but interpretations of relations
    return values in β rather than Prop. -/
structure bStructure (L : Language.{u}) (β : Type v) [CompleteBooleanAlgebra β] where
  carrier : Type u
  fun_map : ∀ {n}, L.functions n → DVec carrier n → carrier
  rel_map : ∀ {n}, L.relations n → DVec carrier n → β
  /-- Boolean equality on the carrier -/
  eq : carrier → carrier → β
  eq_refl : ∀ x, eq x x = ⊤
  eq_symm : ∀ x y, eq x y = eq y x
  eq_trans : ∀ {x} (y : carrier) {z}, eq x y ⊓ eq y z ≤ eq x z
  fun_congr : ∀ {n} (f : L.functions n) (x y : DVec carrier n),
    (DVec.map2 (eq) x y).fInf ≤ eq (fun_map f x) (fun_map f y)
  rel_congr : ∀ {n} (R : L.relations n) (x y : DVec carrier n),
    (DVec.map2 (eq) x y).fInf ⊓ rel_map R x ≤ rel_map R y

variable {L : Language.{u}} {β : Type v} [CompleteBooleanAlgebra β]

instance : CoeSort (bStructure L β) (Type u) := ⟨bStructure.carrier⟩

attribute [simp] bStructure.eq_refl

variable {S : bStructure L β}

@[simp] lemma eq_drefl : ∀ {n} (x : DVec S n),
    (DVec.map2 S.eq x x).fInf = ⊤
  | _, DVec.nil => rfl
  | _, DVec.cons x xs => by
      simp only [DVec.map2, DVec.fInf_cons, S.eq_refl, eq_drefl xs, inf_top_eq]









/-! ## boolean_realize_term -/

@[simp] def boolean_realize_term (v : ℕ → S) :
    ∀ {l} (t : @preterm L l) (xs : DVec S l), S.carrier
  | _, preterm.var k, _ => v k
  | _, preterm.func f, xs => S.fun_map f xs
  | _, preterm.app t₁ t₂, xs =>
      boolean_realize_term v t₁ (DVec.cons (boolean_realize_term v t₂ DVec.nil) xs)

lemma boolean_realize_term_congr' {v v' : ℕ → S} (h : ∀ n, v n = v' n) :
    ∀ {l} (t : @preterm L l) (xs : DVec S l),
    boolean_realize_term v t xs = boolean_realize_term v' t xs
  | _, preterm.var k, _ => h k
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, xs => by
      simp only [boolean_realize_term]
      rw [boolean_realize_term_congr' h t₂, boolean_realize_term_congr' h t₁]



lemma boolean_realize_term_subst_lift (v : ℕ → S) (x : S) (m : ℕ) :
    ∀ {l} (t : @preterm L l) (xs : DVec S l),
    boolean_realize_term (subst_realize v x m) (lift_term_at t 1 m) xs =
    boolean_realize_term v t xs
  | _, preterm.var k, DVec.nil => by
      simp only [boolean_realize_term, lift_term_at]
      by_cases h : m ≤ k
      · have hmk1 : m < k + 1 := Nat.lt_succ_of_le h
        simp only [if_pos h, subst_realize_gt _ _ hmk1, Nat.add_sub_cancel]
      · have hkm : k < m := Nat.lt_of_not_le h
        simp only [if_neg h, boolean_realize_term, subst_realize_lt _ _ hkm]
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, xs => by
      simp only [boolean_realize_term, lift_term_at]
      rw [boolean_realize_term_subst_lift v x m t₂ DVec.nil,
          boolean_realize_term_subst_lift v x m t₁]







/-! ## boolean_realize_formula -/

@[simp] def boolean_realize_formula : ∀ {l}, (ℕ → S) → @preformula L l → DVec S l → β
  | _, v, preformula.falsum, _ => ⊥
  | _, v, preformula.equal t₁ t₂, _ =>
      S.eq (boolean_realize_term v t₁ DVec.nil) (boolean_realize_term v t₂ DVec.nil)
  | _, v, preformula.rel R, xs => S.rel_map R xs
  | _, v, preformula.apprel f t, xs =>
      boolean_realize_formula v f (DVec.cons (boolean_realize_term v t DVec.nil) xs)
  | _, v, preformula.imp f₁ f₂, xs =>
      imp (boolean_realize_formula v f₁ xs) (boolean_realize_formula v f₂ xs)
  | _, v, preformula.all f, xs =>
      ⨅ x : S, boolean_realize_formula (subst_realize v x 0) f xs

lemma boolean_realize_formula_congr' : ∀ {l} {v v' : ℕ → S} (h : ∀ n, v n = v' n)
    (f : @preformula L l) (xs : DVec S l),
    boolean_realize_formula v f xs = boolean_realize_formula v' f xs
  | _, _, _, h, preformula.falsum, _ => rfl
  | _, _, _, h, preformula.equal t₁ t₂, _ => by
      simp only [boolean_realize_formula, boolean_realize_term_congr' h]
  | _, _, _, h, preformula.rel R, _ => rfl
  | _, v, v', h, preformula.apprel f t, xs => by
      simp only [boolean_realize_formula, boolean_realize_term_congr' h]
      exact boolean_realize_formula_congr' h f _
  | _, v, v', h, preformula.imp f₁ f₂, xs => by
      simp only [boolean_realize_formula]
      congr 1
      · exact boolean_realize_formula_congr' h f₁ xs
      · exact boolean_realize_formula_congr' h f₂ xs
  | _, v, v', h, preformula.all f, xs => by
      simp only [boolean_realize_formula]
      congr 1; funext x
      exact boolean_realize_formula_congr' (fun k => subst_realize_congr h x 0 k) f xs





lemma boolean_realize_formula_subst_lift : ∀ {l} (v : ℕ → S) (x : S) (m : ℕ)
    (f : @preformula L l) (xs : DVec S l),
    boolean_realize_formula (subst_realize v x m) (lift_formula_at f 1 m) xs =
    boolean_realize_formula v f xs
  | _, v, x, m, preformula.falsum, xs => rfl
  | _, v, x, m, preformula.equal t₁ t₂, xs => by
      simp [boolean_realize_term_subst_lift]
  | _, v, x, m, preformula.rel R, xs => rfl
  | _, v, x, m, preformula.apprel f t, xs => by
      simp only [boolean_realize_formula, lift_formula_at, boolean_realize_term_subst_lift]
      rw [boolean_realize_formula_subst_lift v x m f]
  | _, v, x, m, preformula.imp f₁ f₂, xs => by
      simp only [boolean_realize_formula, lift_formula_at]
      congr 1
      · exact boolean_realize_formula_subst_lift v x m f₁ xs
      · exact boolean_realize_formula_subst_lift v x m f₂ xs
  | _, v, x, m, preformula.all f, xs => by
      simp only [boolean_realize_formula, lift_formula_at]
      congr 1; funext x'
      rw [boolean_realize_formula_congr' (subst_realize2_0 v x' x m) (lift_formula_at f 1 (m + 1)) xs]
      exact boolean_realize_formula_subst_lift (subst_realize v x' 0) x (m + 1) f xs









@[simp] lemma boolean_realize_formula_not (v : ℕ → S) (f : formula L) :
    boolean_realize_formula v (not' f) DVec.nil = (boolean_realize_formula v f DVec.nil)ᶜ := by
  simp [not', boolean_realize_formula, imp]

/-! ## Satisfiability — boolean_realize_formula_glb, bstatisfied -/

def boolean_realize_formula_glb (S : bStructure L β) (f : formula L) : β :=
  ⨅ v : ℕ → S, boolean_realize_formula v f DVec.nil

notation "⟦" f "⟧[" S "]ᵤ" => Fol.boolean_realize_formula_glb S f

variable (β) in
def bstatisfied (T : Set (formula L)) (f : formula L) : Prop :=
  ∀ (S : bStructure L β) (v : ℕ → S),
    (⨅ f' ∈ T, boolean_realize_formula v (f' : formula L) DVec.nil) ≤
    boolean_realize_formula v f DVec.nil

notation:51 T " ⊨ᵤ[" β "] " f => Fol.bstatisfied β T f

def bstatisfied_of_mem {T : Set (formula L)} {f : formula L} (hf : f ∈ T) : T ⊨ᵤ[β] f :=
  fun S v => le_trans (iInf_le _ f) (iInf_le _ hf)



/-! ## boolean_formula_soundness -/



/-! ## boolean_realize_bounded_term -/

@[simp] def boolean_realize_bounded_term {n} (v : DVec S n) :
    ∀ {l} (t : bounded_preterm L n l) (xs : DVec S l), S.carrier
  | _, bd_var k, _ => v.nth k.1 k.2
  | _, bd_func f, xs => S.fun_map f xs
  | _, bd_app t₁ t₂, xs =>
      boolean_realize_bounded_term v t₁
        (DVec.cons (boolean_realize_bounded_term v t₂ DVec.nil) xs)

@[reducible] def boolean_realize_closed_term (S : bStructure L β) (t : closed_term L) : S :=
  boolean_realize_bounded_term DVec.nil t DVec.nil

lemma boolean_realize_bounded_term_eq {n} {v₁ : DVec S n} {v₂ : ℕ → S}
    (hv : ∀ k (hk : k < n), v₂ k = v₁.nth k hk) :
    ∀ {l} (t : bounded_preterm L n l) (xs : DVec S l),
    boolean_realize_term v₂ t.fst xs = boolean_realize_bounded_term v₁ t xs
  | _, bd_var k, _ => hv k.1 k.2
  | _, bd_func f, xs => rfl
  | _, bd_app t₁ t₂, xs => by
      simp only [boolean_realize_term, boolean_realize_bounded_term, bounded_preterm.fst]
      rw [boolean_realize_bounded_term_eq hv t₂ DVec.nil,
          boolean_realize_bounded_term_eq hv t₁]

lemma boolean_realize_bounded_term_irrel' {n n'} {v₁ : DVec S n} {v₂ : DVec S n'}
    (h : ∀ m (hn : m < n) (hn' : m < n'), v₁.nth m hn = v₂.nth m hn')
    {l} (t : bounded_preterm L n l) (t' : bounded_preterm L n' l)
    (ht : t.fst = t'.fst) (xs : DVec S l) :
    boolean_realize_bounded_term v₁ t xs = boolean_realize_bounded_term v₂ t' xs := by
  induction t generalizing n' with
  | bd_var k =>
    cases t' with
    | bd_var k' =>
      simp only [bounded_preterm.fst, preterm.var.injEq] at ht
      simp only [boolean_realize_bounded_term]
      have hk : k.1 = k'.1 := ht
      calc v₁.nth k.1 k.2 = v₂.nth k.1 (hk ▸ k'.2) := h k.1 k.2 (hk ▸ k'.2)
        _ = v₂.nth k'.1 k'.2 := by congr 1
    | bd_func => simp [bounded_preterm.fst] at ht
    | bd_app => simp [bounded_preterm.fst] at ht
  | bd_func f =>
    cases t' with
    | bd_var => simp [bounded_preterm.fst] at ht
    | bd_func f' =>
      simp only [bounded_preterm.fst, preterm.func.injEq] at ht
      simp [boolean_realize_bounded_term, ht]
    | bd_app => simp [bounded_preterm.fst] at ht
  | bd_app t₁ t₂ iht ihs =>
    cases t' with
    | bd_var => simp [bounded_preterm.fst] at ht
    | bd_func => simp [bounded_preterm.fst] at ht
    | bd_app t₁' t₂' =>
      simp only [bounded_preterm.fst, preterm.app.injEq] at ht
      simp only [boolean_realize_bounded_term]
      rw [ihs h t₂' ht.2 DVec.nil, iht h t₁' ht.1]



@[simp] lemma boolean_realize_bounded_term_cast_eq_irrel {n m l} {h : n = m}
    {v : DVec S m} {t : bounded_preterm L n l} (xs : DVec S l) :
    boolean_realize_bounded_term v (t.cast_eq h) xs =
    boolean_realize_bounded_term (v.cast h.symm) t xs := by
  subst h
  simp only [bounded_preterm.cast_eq, bounded_preterm.cast_rfl, DVec.cast]

@[simp] lemma boolean_realize_bounded_term_dvector_cast_irrel {n m l} {h : n = m}
    {v : DVec S n} {t : bounded_preterm L n l} {xs : DVec S l} :
    boolean_realize_bounded_term (v.cast h) (t.cast (Nat.le_of_eq h)) xs =
    boolean_realize_bounded_term v t xs := by
  subst h
  simp only [DVec.cast, bounded_preterm.cast_rfl]

@[simp] lemma boolean_realize_bounded_term_bd_app {n l}
    (t : bounded_preterm L n (l + 1)) (s : bounded_term L n) (xs : DVec S n)
    (xs' : DVec S l) :
    boolean_realize_bounded_term xs (bd_app t s) xs' =
    boolean_realize_bounded_term xs t
      (DVec.cons (boolean_realize_bounded_term xs s DVec.nil) xs') := rfl

@[simp] lemma boolean_realize_closed_term_bd_apps {l} (t : closed_preterm L l)
    (ts : DVec (closed_term L) l) :
    boolean_realize_closed_term S (bd_apps t ts) =
    boolean_realize_bounded_term (DVec.nil : DVec S 0) t
      (ts.map (fun t' => boolean_realize_bounded_term (DVec.nil : DVec S 0) t' DVec.nil)) := by
  induction ts with
  | nil => rfl
  | cons x xs ih => exact ih (bd_app t x)



@[simp] lemma boolean_realize_cast_bounded_term {n m} {h : n ≤ m} {t : bounded_term L n}
    {v : DVec S m} :
    boolean_realize_bounded_term v (t.cast h) DVec.nil =
    boolean_realize_bounded_term (v.trunc n h) t DVec.nil := by
  apply boolean_realize_bounded_term_irrel'
  · intro k hk hk'
    simp [DVec.trunc_nth]
  · simp [bounded_preterm.cast]

/-- When realizing a closed term, the realizing dvector is irrelevant. -/
@[simp] lemma boolean_realize_closed_term_v_irrel {n} {v : DVec S n} {t : bounded_term L 0} :
    boolean_realize_bounded_term v (t.cast (Nat.zero_le n)) DVec.nil =
    boolean_realize_closed_term S t := by
  simp [boolean_realize_cast_bounded_term]

lemma boolean_realize_bounded_term_subst_lift' {n} (v : DVec S n) (x : S) :
    ∀ {l} (t : bounded_preterm L n l) (xs : DVec S l),
    boolean_realize_bounded_term (DVec.cons x v) (t ↑ᵇ 1) xs =
    boolean_realize_bounded_term v t xs
  | _, bd_var k, _ => by
      simp only [boolean_realize_bounded_term, lift_bounded_term, lift_bounded_term_at,
                 Nat.zero_le, if_true]
      simp [DVec.nth]
  | _, bd_func f, xs => rfl
  | _, bd_app t₁ t₂, xs => by
      simp only [boolean_realize_bounded_term, lift_bounded_term, lift_bounded_term_at]
      rw [boolean_realize_bounded_term_subst_lift' v x t₂ DVec.nil,
          boolean_realize_bounded_term_subst_lift' v x t₁]

@[simp] lemma boolean_realize_bounded_term_subst_lift {n} (v : DVec S n) (x : S)
    {l} (t : bounded_preterm L n l) (xs : DVec S l) :
    boolean_realize_bounded_term (DVec.cons x v) (t ↑ᵇ 1) xs =
    boolean_realize_bounded_term v t xs :=
  boolean_realize_bounded_term_subst_lift' v x t xs

/-! ## boolean_realize_bounded_formula -/

@[simp] def boolean_realize_bounded_formula :
    ∀ {n l} (v : DVec S n) (f : bounded_preformula L n l) (xs : DVec S l), β
  | _, _, v, bd_falsum, _ => ⊥
  | _, _, v, bd_equal t₁ t₂, _ =>
      S.eq (boolean_realize_bounded_term v t₁ DVec.nil)
           (boolean_realize_bounded_term v t₂ DVec.nil)
  | _, _, _, bd_rel R, xs => S.rel_map R xs
  | _, _, v, bd_apprel f t, xs =>
      boolean_realize_bounded_formula v f
        (DVec.cons (boolean_realize_bounded_term v t DVec.nil) xs)
  | _, _, v, bd_imp f₁ f₂, xs =>
      imp (boolean_realize_bounded_formula v f₁ xs)
          (boolean_realize_bounded_formula v f₂ xs)
  | _, _, v, bd_all f, xs =>
      ⨅ x : S, boolean_realize_bounded_formula (DVec.cons x v) f xs

/-! ## boolean_realize_sentence — src/bfol.lean:456-459 -/

@[reducible] def boolean_realize_sentence (S : bStructure L β) (f : sentence L) : β :=
  boolean_realize_bounded_formula (DVec.nil : DVec S 0) f DVec.nil

notation "⟦" f "⟧[" S "]" => Fol.boolean_realize_sentence S f

/-! ## boolean_realize_bounded_formula_eq — src/bfol.lean:461-475 -/

lemma boolean_realize_bounded_formula_eq : ∀ {n} {v₁ : DVec S n} {v₂ : ℕ → S}
    (hv : ∀ k (hk : k < n), v₂ k = v₁.nth k hk) {l} (t : bounded_preformula L n l)
    (xs : DVec S l), boolean_realize_formula v₂ t.fst xs = boolean_realize_bounded_formula v₁ t xs
  | _, v₁, v₂, hv, _, bd_falsum, _ => rfl
  | _, v₁, v₂, hv, _, bd_equal t₁ t₂, _ => by
      simp only [bounded_preformula.fst, boolean_realize_formula, boolean_realize_bounded_formula]
      congr 1 <;> apply boolean_realize_bounded_term_eq hv
  | _, v₁, v₂, hv, _, bd_rel R, _ => rfl
  | _, v₁, v₂, hv, _, bd_apprel f t, xs => by
      simp only [bounded_preformula.fst, boolean_realize_formula, boolean_realize_bounded_formula]
      rw [boolean_realize_bounded_term_eq hv, boolean_realize_bounded_formula_eq hv]
  | _, v₁, v₂, hv, _, bd_imp f₁ f₂, xs => by
      simp only [bounded_preformula.fst, boolean_realize_formula, boolean_realize_bounded_formula]
      rw [boolean_realize_bounded_formula_eq hv, boolean_realize_bounded_formula_eq hv]
  | _, v₁, v₂, hv, _, bd_all f, xs => by
      simp only [bounded_preformula.fst, boolean_realize_formula, boolean_realize_bounded_formula]
      congr 1
      ext x
      apply boolean_realize_bounded_formula_eq
      intro k hk
      cases k with
      | zero => rfl
      | succ k => exact hv k (Nat.lt_of_succ_lt_succ hk)

lemma boolean_realize_bounded_formula_eq' {n} {v₁ : DVec S n} (x : S)
    {l} (t : bounded_preformula L n l) (xs : DVec S l) :
    boolean_realize_bounded_formula v₁ t xs =
    boolean_realize_formula (fun k => if h : k < n then v₁.nth k h else x) t.fst xs := by
  symm
  apply boolean_realize_bounded_formula_eq
  intro k hk
  rw [dif_pos hk]



/-! ## boolean_realize_bounded_formula_congr — src/bfol.lean:489-503 -/



/-! ## boolean_realize_bounded_formula_irrel' — src/bfol.lean:513-528 -/

lemma boolean_realize_bounded_formula_irrel' {n n'} {v₁ : DVec S n} {v₂ : DVec S n'}
    (h : ∀ m (hn : m < n) (hn' : m < n'), v₁.nth m hn = v₂.nth m hn')
    {l} (f : bounded_preformula L n l) (f' : bounded_preformula L n' l)
    (hf : f.fst = f'.fst) (xs : DVec S l) :
    boolean_realize_bounded_formula v₁ f xs = boolean_realize_bounded_formula v₂ f' xs := by
  induction f generalizing n' with
  | bd_falsum =>
    cases f' with
    | bd_falsum => rfl
    | _ => simp [bounded_preformula.fst] at hf
  | bd_equal t₁ t₂ =>
    cases f' with
    | bd_equal t₁' t₂' =>
      simp only [bounded_preformula.fst, preformula.equal.injEq] at hf
      simp only [boolean_realize_bounded_formula]
      rw [boolean_realize_bounded_term_irrel' h t₁ t₁' hf.1,
          boolean_realize_bounded_term_irrel' h t₂ t₂' hf.2]
    | _ => simp [bounded_preformula.fst] at hf
  | bd_rel R =>
    cases f' with
    | bd_rel R' =>
      simp only [bounded_preformula.fst, preformula.rel.injEq] at hf
      simp [boolean_realize_bounded_formula, hf]
    | _ => simp [bounded_preformula.fst] at hf
  | bd_apprel f t ihf =>
    cases f' with
    | bd_apprel f' t' =>
      simp only [bounded_preformula.fst, preformula.apprel.injEq] at hf
      simp only [boolean_realize_bounded_formula]
      rw [boolean_realize_bounded_term_irrel' h t t' hf.2,
          ihf h f' hf.1]
    | _ => simp [bounded_preformula.fst] at hf
  | bd_imp f₁ f₂ ih₁ ih₂ =>
    cases f' with
    | bd_imp f₁' f₂' =>
      simp only [bounded_preformula.fst, preformula.imp.injEq] at hf
      simp only [boolean_realize_bounded_formula]
      rw [ih₁ h f₁' hf.1, ih₂ h f₂' hf.2]
    | _ => simp [bounded_preformula.fst] at hf
  | bd_all f ih =>
    cases f' with
    | bd_all f' =>
      simp only [bounded_preformula.fst, preformula.all.injEq] at hf
      simp only [boolean_realize_bounded_formula]
      congr 1; ext x
      apply ih
      · intro m hm hm'
        cases m with
        | zero => rfl
        | succ m => exact h m (Nat.lt_of_succ_lt_succ hm) (Nat.lt_of_succ_lt_succ hm')
      · exact hf
    | _ => simp [bounded_preformula.fst] at hf



/-! ## boolean_realize_bounded_formula_cast_eq_irrel — src/bfol.lean:536-538 -/

@[simp] lemma boolean_realize_bounded_formula_cast_eq_irrel {n m l} {h : n = m}
    {v : DVec S m} {f : bounded_preformula L n l} {xs : DVec S l} :
    boolean_realize_bounded_formula v (f.cast_eq h) xs =
    boolean_realize_bounded_formula (v.cast h.symm) f xs := by
  subst h
  simp [bounded_preformula.cast_eq, DVec.cast]

/-! ## basic simp lemmas for boolean_realize_sentence — src/bfol.lean:543-559 -/

@[simp] lemma boolean_realize_sentence_false :
    ⟦(bd_falsum : sentence L)⟧[S] = (⊥ : β) := rfl

@[simp] lemma boolean_realize_sentence_imp {f₁ f₂ : sentence L} :
    ⟦bd_imp f₁ f₂⟧[S] = imp ⟦f₁⟧[S] ⟦f₂⟧[S] := rfl

@[simp] lemma boolean_realize_sentence_not {f : sentence L} :
    ⟦bd_not f⟧[S] = (⟦f⟧[S])ᶜ := by
  simp [boolean_realize_sentence, bd_not, imp]



@[simp] lemma boolean_realize_sentence_all {f : bounded_formula L 1} :
    ⟦bd_all f⟧[S] = ⨅ x : S, boolean_realize_bounded_formula (DVec.cons x DVec.nil) f DVec.nil :=
  rfl

@[simp] lemma boolean_realize_bounded_formula_not {n} {v : DVec S n}
    {f : bounded_formula L n} :
    boolean_realize_bounded_formula v (bd_not f) DVec.nil =
    (boolean_realize_bounded_formula v f DVec.nil)ᶜ := by
  simp [bd_not, imp]

@[simp] lemma boolean_realize_bounded_formula_or {n} {v : DVec S n}
    {f g : bounded_formula L n} :
    boolean_realize_bounded_formula v (bd_or f g) DVec.nil =
    boolean_realize_bounded_formula v f DVec.nil ⊔
    boolean_realize_bounded_formula v g DVec.nil := by
  simp [bd_or, bd_not, imp]

@[simp] lemma boolean_realize_bounded_formula_and {n} {v : DVec S n}
    {f g : bounded_formula L n} :
    boolean_realize_bounded_formula v (bd_and f g) DVec.nil =
    boolean_realize_bounded_formula v f DVec.nil ⊓
    boolean_realize_bounded_formula v g DVec.nil := by
  simp [bd_and, bd_not, bd_or, imp]

@[simp] lemma boolean_realize_bounded_formula_ex {n} {v : DVec S n}
    {f : bounded_formula L (n + 1)} :
    boolean_realize_bounded_formula v (bd_ex f) DVec.nil =
    ⨆ x : S, boolean_realize_bounded_formula (DVec.cons x v) f DVec.nil := by
  simp [bd_ex, bd_not, bd_all, imp, compl_iInf]



@[simp] lemma boolean_realize_bounded_formula_biimp {n} {v : DVec S n}
    {f g : bounded_formula L n} :
    boolean_realize_bounded_formula v (bd_biimp f g) DVec.nil =
    bihimp (boolean_realize_bounded_formula v f DVec.nil)
           (boolean_realize_bounded_formula v g DVec.nil) := by
  simp only [bd_biimp, boolean_realize_bounded_formula_and, boolean_realize_bounded_formula,
             bihimp, himp_eq, sup_comm, inf_comm, imp]

/-! ## boolean_realize_bounded_formula_bd_apps_rel — src/bfol.lean:596-602 -/



/-! ## boolean_realize_cast_bounded_formula — src/bfol.lean:604-619 -/

@[simp] lemma boolean_realize_cast_bounded_formula {n m} {h : n ≤ m}
    {f : bounded_formula L n} {v : DVec S m} :
    boolean_realize_bounded_formula v (f.cast h) DVec.nil =
    boolean_realize_bounded_formula (v.trunc n h) f DVec.nil := by
  by_cases hn : n = m
  · subst hn; simp
  · have hlt : n < m := Nat.lt_of_le_of_ne h hn
    apply boolean_realize_bounded_formula_irrel'
    · intro k hk _; simp [DVec.trunc_nth]
    · simp [bounded_preformula.cast]

@[simp] lemma boolean_realize_cast1_bounded_formula {n} {f : bounded_formula L n}
    {v : DVec S (n + 1)} :
    boolean_realize_bounded_formula v f.cast1 DVec.nil =
    boolean_realize_bounded_formula (v.trunc n (Nat.le_add_right n 1)) f DVec.nil :=
  boolean_realize_cast_bounded_formula

/-! ## boolean_realize_sentence_bd_apps_rel — src/bfol.lean:621-634 -/







lemma boolean_realize_sentence_eq (v : ℕ → S) (f : sentence L) :
    boolean_realize_formula v f.fst DVec.nil = ⟦f⟧[S] :=
  boolean_realize_bounded_formula_eq
    (fun k hk => absurd hk (Nat.not_lt_zero k)) f DVec.nil



/-! ## forced_in, all_forced_in — src/bfol.lean:647-658 -/

def forced_in (x : β) (S : bStructure L β) (f : sentence L) : Prop :=
  x ≤ ⟦f⟧[S]

scoped notation:52 x " ⊩[" S "] " f => Fol.forced_in x S f

def all_forced_in (x : β) (S : bStructure L β) (T : SentTheory L) : Prop :=
  x ≤ ⨅ f ∈ T, ⟦f⟧[S]

scoped notation:52 x " ⊩ₜ[" S "] " T => Fol.all_forced_in x S T

@[simp] lemma forced_in_not {f : sentence L} {b : β} :
    (b ⊩[S] (bd_not (bd_not f) : sentence L)) ↔ (b ⊩[S] f) := by
  simp [forced_in, boolean_realize_sentence, bd_not, imp]

/-! ## forced — src/bfol.lean:674-677 -/

variable (β) in
def forced (T : SentTheory L) (f : sentence L) : Prop :=
  ∀ {{S : bStructure L β}}, Nonempty S → (⨅ g ∈ T, ⟦g⟧[S]) ⊩[S] f

scoped notation:51 T " ⊨[" β "] " f => Fol.forced β T f

/-! ## bsatisfied_of_forced, forced_of_bsatisfied — src/bfol.lean:680-698 -/



def forced_of_bsatisfied {T : SentTheory L} {f : sentence L}
    (H : T.fst ⊨ᵤ[β] f.fst) : T ⊨[β] f := by
  intro S hS
  obtain ⟨s⟩ := hS
  show (⨅ g ∈ T, ⟦g⟧[S]) ≤ ⟦f⟧[S]
  rw [← boolean_realize_sentence_eq (fun _ => s)]
  refine le_trans ?_ (H S (fun _ => s))
  rw [le_iInf_iff]
  intro f'
  rw [le_iInf_iff]
  intro hf'
  rcases hf' with ⟨f'', ⟨hf'', rfl⟩⟩
  rw [boolean_realize_sentence_eq]
  exact le_trans (iInf_le _ f'') (iInf_le _ hf'')

@[simp] lemma inf_axioms_top_of_models {S : bStructure L β} {T : SentTheory L}
    (H : ⊤ ⊩ₜ[S] T) : (⨅ f ∈ T, ⟦f⟧[S]) = ⊤ := by
  apply top_unique
  exact le_trans H (le_refl _)



/-! ## bModel — src/bfol.lean:720-721 -/



/-! ## boolean_soundness, unprovable_of_model_neg — src/bfol.lean:730-739 -/





/-! ## boolean_realize_subst_preterm — src/bfol.lean:741-761 -/





/-! ## boolean_realize_sentence_bd_alls — src/bfol.lean:763-778 -/



/-! ## consis_of_exists_bmodel — src/bfol.lean:785-793 -/



/-! ## subst0_bounded_formula_not — src/bfol.lean:799-801 -/

@[simp] lemma subst0_bounded_formula_not {n} (f : bounded_formula L (n + 1))
    (s : bounded_term L n) :
    subst0_bounded_formula (bd_not f) s = bd_not (subst0_bounded_formula f s) := by
  apply bounded_preformula.eq
  simp [bd_not, subst0_bounded_formula_fst]

/-! ## subst0_bounded_formula_and — src/bfol.lean:803-805 -/

@[simp] lemma subst0_bounded_formula_and {n} (f g : bounded_formula L (n + 1))
    (s : bounded_term L n) :
    subst0_bounded_formula (bd_and f g) s =
    bd_and (subst0_bounded_formula f s) (subst0_bounded_formula g s) := by
  apply bounded_preformula.eq
  simp [bd_and, bd_not, subst0_bounded_formula_fst]

/-! ## boolean_realize_bounded_formula_insert_lift — src/bfol.lean:854-872 -/

lemma boolean_realize_bounded_formula_insert_lift {n l} (v : DVec S n) (x : S) (m : ℕ) (hm : m ≤ n)
    (f : bounded_preformula L n l) (xs : DVec S l) :
    boolean_realize_bounded_formula (v.insert x m) (f ↑ᶠᵇ' 1 # m) xs =
    boolean_realize_bounded_formula v f xs := by
  -- Reduce to unbounded formula semantics
  rw [boolean_realize_bounded_formula_eq' (v₁ := v.insert x m) x,
      boolean_realize_bounded_formula_eq' (v₁ := v) x]
  simp only [lift_bounded_formula_fst]
  -- Now use boolean_realize_formula_subst_lift
  rw [show (fun k => if h : k < n + 1 then (v.insert x m).nth k h else x) =
          subst_realize (fun k => if h : k < n then v.nth k h else x) x m from by
        funext k
        simp only [subst_realize]
        by_cases hkm : k < m
        · simp only [hkm, if_true]
          have hkn : k < n := Nat.lt_of_lt_of_le hkm hm
          have hkn1 : k < n + 1 := Nat.lt_succ_of_le (Nat.le_of_lt hkn)
          simp only [dif_pos hkn1, dif_pos hkn]
          simp [DVec.insert_nth_lt x v (by exact hkn) hkn1 (by exact hkm)]
        · by_cases hkm' : k = m
          · subst hkm'
            simp [hkm, DVec.insert_nth]
          · have hkm2 : m < k := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hkm) (Ne.symm hkm')
            simp only [Nat.lt_asymm hkm2, hkm2, if_false, if_true]
            by_cases hkn1 : k < n + 1
            · have hk1 : k - 1 < n := by omega
              simp only [dif_pos hkn1, dif_pos hk1]
              rw [DVec.insert_nth_gt_simp x v hkn1 hkm2]
            · have hk1 : ¬(k - 1 < n) := by omega
              simp only [dif_neg hkn1, dif_neg hk1]]
  exact boolean_realize_formula_subst_lift _ _ _ _ _

/-! ## boolean_realize_formula_insert_lift2 — src/bfol.lean:874-879 -/

@[simp] lemma boolean_realize_formula_insert_lift2 {n} (v : DVec S n) (x y z : S)
    (f : bounded_formula L (n + 2)) :
    boolean_realize_bounded_formula (DVec.cons x (DVec.cons y (DVec.cons z v)))
      (f ↑ᶠᵇ' 1 # 2) DVec.nil =
    boolean_realize_bounded_formula (DVec.cons x (DVec.cons y v)) f DVec.nil := by
  -- Use boolean_realize_bounded_formula_insert_lift with m=2, v=(x::y::v), x=z
  convert boolean_realize_bounded_formula_insert_lift (DVec.cons x (DVec.cons y v)) z 2
    (by omega) f DVec.nil using 2
  rfl

/-! ## boolean_realize_subst_formula0 — src/bfol.lean:881-897 -/



end bfol

end Fol


end CohenSource_Bfol


/- Source module: Definitions.Flypitch4.SetTheoryExt -/
section CohenSource_SetTheoryExt
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/set_theory.lean -/






set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! ## Lean 3 → Lean 4 Port: scope-narrowed slice of `src/set_theory.lean`

The original Lean 3 `set_theory.lean` (713 lines) bundles two largely independent
chunks of infrastructure:

1. **The delta-system lemma** and its supporting machinery (lines 1–388).
2. **CCC (Countable Chain Condition)** plus the **product topology** section
   (lines 389–713).

Cross-flypitch grep confirms only **two** symbols from this file are used by any
other Lean 3 source:

- `countable_chain_condition` — used by `src/regular_open_algebra.lean`.
- `countable_chain_condition_pi` — called once at `src/cantor_space.lean:436`.

Everything else (`is_delta_system` and friends, the `delta_system_lemma_*`
theorems, `pi_basis`, `pi_subbasis`, `support`, `extend`, `eq_on'`, …) is
internal scaffolding that the Lean 3 authors wrote but never ended up using on
the path to `independence_of_CH`. It has been dropped from the port.

If a future port needs the dropped material, the Lean 3 source remains
verbatim in `src/set_theory.lean` as a reference.

### Renames (Lean 3 → Lean 4)

- `pairwise_disjoint s` (set-valued, Lean 3) → `s.PairwiseDisjoint id`
-/

universe u v

open Set TopologicalSpace Cardinal

/-! ## CCC: Countable Chain Condition -/

section CCC

variable (α : Type u) [TopologicalSpace α]

/-- The countable chain condition: every pairwise disjoint family of open sets is countable. -/
def countable_chain_condition : Prop :=
  ∀ s : Set (Set α), (∀ ⦃o⦄, o ∈ s → IsOpen o) → s.PairwiseDisjoint id → s.Countable

variable {α}









end CCC

/-! ## Δ-system lemma (uncountable case, for finite-set families) -/

/-- A family of sets `A : ι → Set α` forms a Δ-system (sunflower) with root `r`
if every pair of distinct values intersects exactly in `r`. -/
def IsDeltaSystem {ι : Type*} {α : Type*} (A : ι → Set α) : Prop :=
  ∃ root : Set α, ∀ ⦃x y : ι⦄, x ≠ y → A x ∩ A y = root

namespace DeltaSystemAux









end DeltaSystemAux



/-! ## CCC for product topologies -/

variable {α : Type u} {β : α → Type v} [∀ x, TopologicalSpace (β x)]

/-- The standard pi-basis from mathlib's `isTopologicalBasis_pi`, instantiated
to allow any open set as the per-coordinate basis. -/
 def piOpenBasis : Set (Set (∀ x, β x)) :=
  { S | ∃ (U : ∀ x, Set (β x)) (F : Finset α),
        (∀ x, x ∈ F → IsOpen (U x)) ∧ S = (F : Set α).pi U }










end CohenSource_SetTheoryExt


/- Source module: Definitions.Flypitch4.RegularOpenAlgebra -/
section CohenSource_RegularOpenAlgebra
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/regular_open_algebra.lean (complete, lines 1-722).

Namespace: everything lives in `Flypitch` namespace to avoid clashing with mathlib's `IsRegular`.
The `ᵖ` postfix for `perp` is declared globally after the namespace.
-/






set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace

universe u

namespace Flypitch

/-! ## topology_lemmas section -/

section topology_lemmas

variable {α : Type u} [TopologicalSpace α]




























end topology_lemmas

/-! ## regular section -/

section regular

variable {α : Type u} [TopologicalSpace α]

/-- A set S is regular open if S = interior(closure S). -/
def IsRegularOpen (S : Set α) : Prop := S = interior (closure S)

/-- The perp of S: the complement of the closure. -/
def perp (S : Set α) : Set α := (closure S)ᶜ

end regular

end Flypitch

-- Declare ᵖ postfix globally (outside namespace)
postfix:80 "ᵖ" => Flypitch.perp

/-! ## Lemmas about perp and IsRegularOpen in namespace Flypitch.Regular -/

namespace Flypitch.Regular

open Flypitch

variable {α : Type u} [TopologicalSpace α]

@[simp] lemma perp_unfold (S : Set α) : Sᵖ = (closure S)ᶜ := rfl





@[simp] lemma isOpen_perp {S : Set α} : IsOpen (Sᵖ) := isClosed_closure.isOpen_compl
@[simp] lemma perp_univ : (Set.univ : Set α)ᵖ = ∅ := by simp [Flypitch.perp]
@[simp] lemma perp_empty : (∅ : Set α)ᵖ = Set.univ := by simp [Flypitch.perp]

@[simp] lemma isOpen_of_isRegularOpen {S : Set α} (H : IsRegularOpen S) : IsOpen S := by
  rw [H]; exact isOpen_interior

@[simp] lemma isRegularOpen_of_isClopen {S : Set α} (H : IsClopen S) : IsRegularOpen S := by
  unfold IsRegularOpen; rw [H.1.closure_eq, H.2.interior_eq]

lemma p_p_eq_int_cl {S : Set α} : Sᵖᵖ = interior (closure S) := by
  simp only [perp_unfold, closure_compl, compl_compl]



lemma regular_iff_p_p {S : Set α} : IsRegularOpen S ↔ Sᵖᵖ = S := by
  rw [IsRegularOpen, ← p_p_eq_int_cl]
  exact ⟨fun h => h.symm, fun h => h.symm⟩



lemma isOpen_of_p_p {S : Set α} (H : Sᵖᵖ = S) : IsOpen S := by
  rw [p_p_eq_int_cl] at H; exact H ▸ isOpen_interior

@[simp] lemma isRegularOpen_empty : IsRegularOpen (∅ : Set α) := by simp [IsRegularOpen]
@[simp] lemma isRegularOpen_univ : IsRegularOpen (Set.univ : Set α) := by simp [IsRegularOpen]

lemma p_anti {P Q : Set α} (H : P ⊆ Q) : Qᵖ ⊆ Pᵖ :=
  compl_subset_compl.mpr (closure_mono H)

lemma p_p_mono {P Q : Set α} (H : P ⊆ Q) : Pᵖᵖ ⊆ Qᵖᵖ := p_anti (p_anti H)

lemma in_p_p_of_open {S : Set α} (H : IsOpen S) : S ⊆ Sᵖᵖ := by
  rw [p_p_eq_int_cl]; exact H.subset_interior_iff.mpr subset_closure

@[simp] lemma isRegularOpen_eq_p_p {S : Set α} (H : IsRegularOpen S) : Sᵖᵖ = S := by
  rw [regular_iff_p_p] at H; exact H

lemma isRegularOpen_stable_subset {S₁ S₂ : Set α} (H : IsRegularOpen S₂) (H₂ : S₁ ⊆ S₂) :
    S₁ᵖᵖ ⊆ S₂ := by
  have h := p_p_mono H₂; rwa [isRegularOpen_eq_p_p H] at h

lemma subset_p_p_of_open {S : Set α} (H : IsOpen S) : S ⊆ Sᵖᵖ := in_p_p_of_open H



lemma p_eq_p_p_p {S : Set α} (H : IsOpen S) : Sᵖ = Sᵖᵖᵖ :=
  le_antisymm (in_p_p_of_open isOpen_perp) (p_anti (in_p_p_of_open H))

@[simp] lemma p_p_p_p_eq_p_p {S : Set α} : Sᵖᵖᵖᵖ = Sᵖᵖ :=
  (p_eq_p_p_p (isOpen_perp (S := S))).symm

@[simp] lemma isOpen_of_p_p' {S : Set α} : IsOpen (Sᵖᵖ) := by
  rw [p_p_eq_int_cl]; exact isOpen_interior

@[simp] lemma isRegularOpen_p_p {S : Set α} : IsRegularOpen (Sᵖᵖ) := by
  rw [regular_iff_p_p]; exact p_p_p_p_eq_p_p



/-- For open S₁: S₁ ∩ closure S₂ ⊆ closure (S₁ ∩ S₂). -/
lemma inter_eq_inter_aux (S₁ S₂ : Set α) (H : IsOpen S₁) :
    S₁ ∩ closure S₂ ⊆ closure (S₁ ∩ S₂) := by
  intro x ⟨hx1, hx2⟩
  have := H.closure_inter (s := S₂) ⟨hx2, hx1⟩
  rwa [Set.inter_comm S₂ S₁] at this

@[simp] lemma cl_compl_of_isOpen (S : Set α) (H : IsOpen S) : closure Sᶜ = Sᶜ :=
  H.isClosed_compl.closure_eq

lemma inter_eq_inter_aux₂ (S₁ S₂ : Set α) (H₁ : IsOpen S₁) (_H₂ : IsOpen S₂) :
    S₁ ∩ S₂ᵖᵖ ⊆ (S₁ ∩ S₂)ᵖᵖ := by
  rw [p_p_eq_int_cl, p_p_eq_int_cl]
  intro x ⟨hx1, hx2⟩
  rw [mem_interior] at hx2 ⊢
  rcases hx2 with ⟨t, ht_sub, ht_open, hxt⟩
  exact ⟨S₁ ∩ t, (Set.inter_subset_inter_right S₁ ht_sub).trans (inter_eq_inter_aux S₁ S₂ H₁),
    H₁.inter ht_open, hx1, hxt⟩

lemma p_p_inter_eq_inter_p_p {S₁ S₂ : Set α} (H₁ : IsOpen S₁) (H₂ : IsOpen S₂) :
    (S₁ ∩ S₂)ᵖᵖ = S₁ᵖᵖ ∩ S₂ᵖᵖ := by
  apply le_antisymm
  · exact fun x hx => ⟨p_p_mono Set.inter_subset_left hx,
                        p_p_mono Set.inter_subset_right hx⟩
  · intro x ⟨hx1, hx2⟩
    have sub1 : S₁ᵖᵖ ∩ S₂ ⊆ (S₁ ∩ S₂)ᵖᵖ := by
      intro y ⟨hy1, hy2⟩
      have h := inter_eq_inter_aux₂ S₂ S₁ H₂ H₁ ⟨hy2, hy1⟩
      rwa [Set.inter_comm] at h
    have sub2 : (S₁ᵖᵖ ∩ S₂)ᵖᵖ ⊆ (S₁ ∩ S₂)ᵖᵖ := by
      have := p_p_mono sub1; rwa [p_p_p_p_eq_p_p] at this
    have step := inter_eq_inter_aux₂ (S₁ᵖᵖ) S₂ (isOpen_of_p_p' (S := S₁)) H₂
    exact sub2 (step ⟨hx1, hx2⟩)

@[simp] lemma isRegularOpen_inter {S₁ S₂ : Set α} (H₁ : IsRegularOpen S₁)
    (H₂ : IsRegularOpen S₂) : IsRegularOpen (S₁ ∩ S₂) := by
  rw [regular_iff_p_p] at *
  rw [p_p_inter_eq_inter_p_p (isOpen_of_p_p H₁) (isOpen_of_p_p H₂), H₁, H₂]





end Flypitch.Regular

/-! ## regular_algebra section

Port of: `section regular_algebra` (src/regular_open_algebra.lean lines 349-722).
Builds the complete Boolean algebra structure on regular open sets.
-/

namespace Flypitch

open Flypitch.Regular

/-! ### The type of regular open sets -/

/-- The type of regular open sets of a topological space.
Port of: `def regular_opens` (src/regular_open_algebra.lean:364). -/
def RegularOpens (α : Type u) [TopologicalSpace α] : Type u :=
  {S : Set α // IsRegularOpen S}

namespace RegularOpens

variable {α : Type u} [TopologicalSpace α]

instance instCoe : CoeTC (RegularOpens α) (Set α) := ⟨Subtype.val⟩



-- Helper: extract val image of a set of regular opens
-- (using Set.image (·.val) avoids the ↑𝒮 coercion issue in where blocks)
 def roVals (𝒮 : Set (RegularOpens α)) : Set (Set α) := Set.image (·.val) 𝒮

@[simp] lemma mem_roVals {𝒮 : Set (RegularOpens α)} {S : Set α} :
    S ∈ roVals 𝒮 ↔ ∃ r ∈ 𝒮, r.val = S := Iff.rfl



/-! ### Key set lemmas -/

 lemma compl_isRO' (x : RegularOpens α) : IsRegularOpen (Flypitch.perp x.val) := by
  rw [regular_iff_p_p]
  exact (p_eq_p_p_p (isOpen_of_isRegularOpen x.property)).symm

 lemma val_inter_perp_empty' (x : RegularOpens α) : x.val ∩ x.valᵖ = ∅ := by
  ext y; simp only [Flypitch.perp, Set.mem_inter_iff, Set.mem_compl_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro hy; exact fun h => h (subset_closure hy)

 lemma union_perp_pp_eq_univ' (x : RegularOpens α) :
    (x.val ∪ x.valᵖ)ᵖᵖ = Set.univ := by
  rw [p_p_eq_int_cl]
  suffices h : closure (x.val ∪ x.valᵖ) = Set.univ by rw [h]; exact interior_univ
  rw [Set.eq_univ_iff_forall]; intro y
  by_cases hy : y ∈ closure x.val
  · rw [mem_closure_iff]; intro V hV hyV
    by_cases hVne : (V ∩ x.valᵖ).Nonempty
    · rcases hVne with ⟨z, hzV, hzp⟩
      exact ⟨z, hzV, Set.mem_union_right _ hzp⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hVne
      have hVcl : V ⊆ closure x.val := by
        intro z hz
        by_contra hzncl
        have hmem : z ∈ V ∩ x.valᵖ := ⟨hz, by simp [Flypitch.perp, hzncl]⟩
        rw [hVne] at hmem; simp at hmem
      have hVx : V ⊆ x.val := by
        have h1 : V ⊆ interior (closure x.val) := hV.subset_interior_iff.mpr hVcl
        rwa [← x.property] at h1
      exact ⟨y, hyV, Set.mem_union_left _ (hVx hyV)⟩
  · exact subset_closure (Set.mem_union_right _ (by simp [Flypitch.perp, hy]))

/-! ### Order on RegularOpens (needed before instance) -/

instance instLE : LE (RegularOpens α) := ⟨fun a b => a.val ⊆ b.val⟩

/-! ### Auxiliary lemmas for the CBA instance -/

 lemma le_sup_left' (a b : RegularOpens α) : a.val ⊆ (a.val ∪ b.val)ᵖᵖ :=
  Set.Subset.trans Set.subset_union_left
    (subset_p_p_of_open ((isOpen_of_isRegularOpen a.property).union
      (isOpen_of_isRegularOpen b.property)))

 lemma le_sup_right' (a b : RegularOpens α) : b.val ⊆ (a.val ∪ b.val)ᵖᵖ :=
  Set.Subset.trans Set.subset_union_right
    (subset_p_p_of_open ((isOpen_of_isRegularOpen a.property).union
      (isOpen_of_isRegularOpen b.property)))

 lemma sup_le' (a b c : RegularOpens α) (h1 : a.val ⊆ c.val) (h2 : b.val ⊆ c.val) :
    (a.val ∪ b.val)ᵖᵖ ⊆ c.val := by
  apply isRegularOpen_stable_subset c.property
  intro x hx
  rcases hx with hxa | hxb
  · exact h1 hxa
  · exact h2 hxb

 lemma le_sup_inf' (x y z : RegularOpens α) :
    (x.val ∪ y.val)ᵖᵖ ∩ (x.val ∪ z.val)ᵖᵖ ⊆ (x.val ∪ y.val ∩ z.val)ᵖᵖ := by
  have hxy : IsOpen (x.val ∪ y.val) :=
    (isOpen_of_isRegularOpen x.property).union (isOpen_of_isRegularOpen y.property)
  have hxz : IsOpen (x.val ∪ z.val) :=
    (isOpen_of_isRegularOpen x.property).union (isOpen_of_isRegularOpen z.property)
  rw [← p_p_inter_eq_inter_p_p hxy hxz]
  apply p_p_mono
  intro a ⟨haux, hazx⟩
  rcases haux with hax | hay <;> rcases hazx with hax' | haz
  · exact Or.inl hax
  · exact Or.inl hax
  · exact Or.inl hax'
  · exact Or.inr ⟨hay, haz⟩

-- Auxiliary: sSup upper bound for a ∈ s
 lemma sSup_ub' (s : Set (RegularOpens α)) (a : RegularOpens α) (ha : a ∈ s) :
    a.val ⊆ (⋃₀ Set.image (·.val) s)ᵖᵖ :=
  (subset_p_p_of_open (isOpen_of_isRegularOpen a.property)).trans
    (p_p_mono (fun x hx => ⟨a.val, ⟨a, ha, rfl⟩, hx⟩))

-- Auxiliary: sSup is least upper bound
 lemma sSup_lub' (s : Set (RegularOpens α)) (a : RegularOpens α)
    (ha : ∀ b ∈ s, b.val ⊆ a.val) :
    (⋃₀ Set.image (·.val) s)ᵖᵖ ⊆ a.val := by
  apply isRegularOpen_stable_subset a.property
  intro x hx
  rcases hx with ⟨S, ⟨b, hb, rfl⟩, hxS⟩
  exact ha b hb hxS

-- Auxiliary: sInf lower bound for a ∈ s
 lemma sInf_lb' (s : Set (RegularOpens α)) (a : RegularOpens α) (ha : a ∈ s) :
    (⋂₀ Set.image (·.val) s)ᵖᵖ ⊆ a.val := by
  apply isRegularOpen_stable_subset a.property
  intro x hx
  rw [Set.mem_sInter] at hx
  exact hx a.val ⟨a, ha, rfl⟩

-- Auxiliary: a ≤ sInf s when a ≤ all b ∈ s
 lemma le_sInf' (s : Set (RegularOpens α)) (a : RegularOpens α)
    (ha : ∀ b ∈ s, a.val ⊆ b.val) :
    a.val ⊆ (⋂₀ Set.image (·.val) s)ᵖᵖ := by
  have hSub : a.val ⊆ ⋂₀ Set.image (·.val) s := by
    intro x hx
    rw [Set.mem_sInter]
    intro S hS
    rcases hS with ⟨b, hb, rfl⟩
    exact ha b hb hx
  rw [← isRegularOpen_eq_p_p a.property]
  exact p_p_mono hSub

/-! ### Complete Boolean Algebra instance

Build everything in one `where` block to avoid coherence issues.
-/

set_option maxHeartbeats 800000 in
/-- Regular opens form a complete Boolean algebra.
Port of: `regular_open_algebra` (src/regular_open_algebra.lean:507-647). -/
noncomputable instance instCompleteBooleanAlgebra : CompleteBooleanAlgebra (RegularOpens α) where
  -- Binary operations
  sup a b := ⟨(a.val ∪ b.val)ᵖᵖ, isRegularOpen_p_p⟩
  inf a b := ⟨a.val ∩ b.val, isRegularOpen_inter a.property b.property⟩
  compl a := ⟨Flypitch.perp a.val, compl_isRO' a⟩
  top := ⟨Set.univ, isRegularOpen_univ⟩
  bot := ⟨∅, isRegularOpen_empty⟩
  -- Order
  le a b := a.val ⊆ b.val
  le_refl _ := le_refl _
  le_trans _ _ _ h1 h2 := Set.Subset.trans h1 h2
  le_antisymm _ _ h1 h2 := Subtype.ext (Set.Subset.antisymm h1 h2)
  -- Sup lattice axioms
  le_sup_left a b := le_sup_left' a b
  le_sup_right a b := le_sup_right' a b
  sup_le a b c h1 h2 := sup_le' a b c h1 h2
  -- Inf lattice axioms
  inf_le_left a b := Set.inter_subset_left
  inf_le_right a b := Set.inter_subset_right
  le_inf a b c h1 h2 := Set.subset_inter h1 h2
  -- Distributivity
  le_sup_inf x y z := le_sup_inf' x y z
  -- Boolean algebra axioms
  inf_compl_le_bot a := by
    -- a ⊓ aᶜ ≤ ⊥ means a.val ∩ (Flypitch.perp a.val) ⊆ ∅
    show a.val ∩ Flypitch.perp a.val ⊆ ∅
    exact val_inter_perp_empty' a ▸ le_refl _
  top_le_sup_compl a := by
    -- ⊤ ≤ a ⊔ aᶜ means Set.univ ⊆ (a.val ∪ (Flypitch.perp a.val))ᵖᵖ
    show Set.univ ⊆ (a.val ∪ Flypitch.perp a.val)ᵖᵖ
    exact union_perp_pp_eq_univ' a ▸ le_refl _
  le_top _ := Set.subset_univ _
  bot_le _ := Set.empty_subset _
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl
  -- Complete lattice operations
  sSup 𝒮 := ⟨(⋃₀ Set.image (·.val) 𝒮)ᵖᵖ, isRegularOpen_p_p⟩
  sInf 𝒮 := ⟨(⋂₀ Set.image (·.val) 𝒮)ᵖᵖ, isRegularOpen_p_p⟩
  isLUB_sSup s := by
    refine ⟨fun a ha => sSup_ub' s a ha, fun a ha => ?_⟩
    exact sSup_lub' s a (fun b hb => ha hb)
  isGLB_sInf s := by
    refine ⟨fun a ha => sInf_lb' s a ha, fun a ha => ?_⟩
    exact le_sInf' s a (fun b hb => ha hb)

/-! ### Convenience simp lemmas (work once the instance is defined) -/

@[simp] lemma sup_val (x₁ x₂ : RegularOpens α) :
    (x₁ ⊔ x₂ : RegularOpens α).val = ((x₁ : Set α) ∪ x₂)ᵖᵖ := rfl

@[simp] lemma inf_val (x₁ x₂ : RegularOpens α) :
    (x₁ ⊓ x₂ : RegularOpens α).val = (x₁ : Set α) ∩ x₂ := rfl

@[simp] lemma top_val : (⊤ : RegularOpens α).val = Set.univ := rfl
@[simp] lemma bot_val : (⊥ : RegularOpens α).val = ∅ := rfl
@[simp] lemma coe_bot : ((⊥ : RegularOpens α) : Set α) = ∅ := rfl

@[simp] lemma compl_val (x : RegularOpens α) : (xᶜ : RegularOpens α).val = x.valᵖ := rfl

@[simp] lemma sSup_val (𝒜 : Set (RegularOpens α)) :
    (sSup 𝒜 : RegularOpens α).val = (⋃₀ Set.image (·.val) 𝒜)ᵖᵖ := rfl

@[simp] lemma sInf_val (s : Set (RegularOpens α)) :
    (sInf s : RegularOpens α).val = (⋂₀ Set.image (·.val) s)ᵖᵖ := rfl



/-! ### NontrivialCompleteBooleanAlgebra -/

/-- Regular opens form a nontrivial CBA when α is nonempty.
Port of: `def regular_open_algebra` (src/regular_open_algebra.lean:635). -/
noncomputable instance instNontrivialCBA [Nonempty α] :
    NontrivialCompleteBooleanAlgebra (RegularOpens α) where
  bot_lt_top := by
    refine lt_of_le_of_ne bot_le (fun h => ?_)
    have : (⊥ : RegularOpens α).val = (⊤ : RegularOpens α).val := congr_arg (·.val) h
    rw [bot_val, top_val] at this
    exact absurd (this ▸ Set.mem_univ (‹Nonempty α›.some)) (by simp)

/-! ### Density lemmas -/









/-! ### CCC for regular opens -/



/-! ### bot_lt and fst lemmas -/



/-- ↑(sSup f) = (⋃₀ (val '' f))ᵖᵖ. Port of src:696. -/
@[simp] lemma fst_sSup {f : Set (RegularOpens α)} :
    (sSup f : RegularOpens α).val = (⋃₀ Set.image (·.val) f)ᵖᵖ := rfl



/-- ↑(sInf f) = (⋂₀ (val '' f))ᵖᵖ. Port of src:702. -/
@[simp] lemma fst_sInf {f : Set (RegularOpens α)} :
    (sInf f : RegularOpens α).val = (⋂₀ Set.image (·.val) f)ᵖᵖ := rfl



end RegularOpens

end Flypitch


end CohenSource_RegularOpenAlgebra


/- Source module: Definitions.Flypitch4.CantorSpace -/
section CohenSource_CantorSpace
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/cantor_space.lean (446 lines). -/







set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace

universe u v

/-! ## Global topology on `Set α` -/

/-- Discrete topology on `Prop` (⊥ = discrete in Lean 4 = all sets open). -/
@[implicit_reducible] instance Prop_space : TopologicalSpace Prop := ⊥

instance discrete_Prop : DiscreteTopology Prop := ⟨rfl⟩

/-- The product (Pi) topology on `Set α = α → Prop`,
using the discrete topology on each `Prop` factor. -/
@[implicit_reducible] instance product_topology {α : Type*} : TopologicalSpace (Set α) :=
  Pi.topologicalSpace





@[reducible, simp] noncomputable def Prop_to_bool (p : Prop) : Bool :=
  haveI := Classical.propDecidable p; decide p

@[simp] lemma Prop_to_bool_true : Prop_to_bool True = true := by
  simp [Prop_to_bool]

@[simp] lemma Prop_to_bool_false : Prop_to_bool False = false := by
  simp [Prop_to_bool]

noncomputable def equiv_Prop_bool : Equiv Prop Bool where
  toFun := Prop_to_bool
  invFun := fun b => b = true
  left_inv := fun p => by
    simp only [Prop_to_bool]
    haveI := Classical.propDecidable p
    by_cases h : p <;> simp [h]
  right_inv := fun b => by
    cases b <;> simp [Prop_to_bool]

noncomputable instance Prop_encodable : Encodable Prop :=
  Encodable.ofEquiv Bool equiv_Prop_bool

instance Prop_separable : SeparableSpace Prop where
  exists_countable_dense := ⟨Set.univ, Set.countable_univ, dense_univ⟩



lemma is_closed_of_compl_open {α : Type*} [TopologicalSpace α] {S : Set α}
    (H : IsOpen Sᶜ) : IsClosed S :=
  isOpen_compl_iff.mp H

/-- The type of clopen sets in a topological space. -/
def Clopens (α : Type u) [TopologicalSpace α] : Type u := {S : Set α // IsClopen S}

instance clopens_lattice {α : Type u} [TopologicalSpace α] : Lattice (Clopens α) where
  sup := fun S₁ S₂ => ⟨S₁.1 ∪ S₂.1, S₁.2.union S₂.2⟩
  le := fun S₁ S₂ => S₁.1 ⊆ S₂.1
  le_refl := fun _ => Set.Subset.refl _
  le_trans := fun _ _ _ h1 h2 => Set.Subset.trans h1 h2
  le_antisymm := fun a b h1 h2 => Subtype.ext (Set.Subset.antisymm h1 h2)
  le_sup_left := fun S₁ _ _ hx => Set.mem_union_left _ hx
  le_sup_right := fun _ S₂ _ hx => Set.mem_union_right _ hx
  sup_le := fun _ _ _ h1 h2 _ hx => hx.elim (h1 ·) (h2 ·)
  inf := fun S₁ S₂ => ⟨S₁.1 ∩ S₂.1, S₁.2.inter S₂.2⟩
  inf_le_left := fun _ _ _ hx => hx.1
  inf_le_right := fun _ _ _ hx => hx.2
  le_inf := fun _ _ _ h1 h2 _ hx => ⟨h1 hx, h2 hx⟩

instance clopens_order_top {α : Type u} [TopologicalSpace α] : OrderTop (Clopens α) where
  top := ⟨Set.univ, isClopen_univ⟩
  le_top := fun _ _ _ => trivial

instance clopens_order_bot {α : Type u} [TopologicalSpace α] : OrderBot (Clopens α) where
  bot := ⟨∅, isClopen_empty⟩
  bot_le := fun _ _ hx => False.elim hx

/-- A finite intersection of clopen sets (via Finset.inf and a function) is clopen. -/
lemma is_clopen_finite_inter' {α : Type u} [TopologicalSpace α]
    {α' : Type v} {X : Finset α'} {f : α' → Set α}
    (H_f : ∀ x ∈ X, IsClopen (f x)) : IsClopen (X.inf f) := by
  classical
  revert H_f
  induction X using Finset.induction with
  | empty => intro _; simp only [Finset.inf_empty]; exact isClopen_univ
  | insert _ _ =>
    rename_i a A ha ih
    intro H_f
    rw [Finset.inf_insert]
    apply IsClopen.inter
    · exact H_f _ (Finset.mem_insert_self _ _)
    · apply ih; intro x hx; exact H_f x (Finset.mem_insert_of_mem hx)



/-! ## CantorSpace namespace -/

namespace CantorSpace

variable {α : Type u}

/-- The basic open set: all sets containing a given element. -/
def principalOpen (x : α) : Set (Set α) := {S | x ∈ S}

/-- The basic open set: all sets not containing a given element. -/
def coPrincipalOpen (x : α) : Set (Set α) := {S | x ∉ S}

@[simp] lemma neg_principalOpen {x : α} : coPrincipalOpen x = (principalOpen x)ᶜ := by
  ext S; simp [principalOpen, coPrincipalOpen]

@[simp] lemma neg_coPrincipalOpen {x : α} : (coPrincipalOpen x)ᶜ = principalOpen x := by
  ext S; simp [principalOpen, coPrincipalOpen]

/-- The four-element subbasis for the topology at projection `x`. -/
def opensOver (x : α) : Set (Set (Set α)) :=
  {principalOpen x, coPrincipalOpen x, Set.univ, ∅}

@[simp] lemma principalOpen_mem_opensOver {x : α} : principalOpen x ∈ opensOver x := by
  simp [opensOver, Set.mem_insert_iff]

@[simp] lemma coPrincipalOpen_mem_opensOver {x : α} : coPrincipalOpen x ∈ opensOver x := by
  simp [opensOver, Set.mem_insert_iff]

@[simp] lemma univ_mem_opensOver {x : α} : Set.univ ∈ opensOver x := by
  simp [opensOver, Set.mem_insert_iff]

@[simp] lemma empty_mem_opensOver {x : α} : (∅ : Set (Set α)) ∈ opensOver x := by
  simp [opensOver, Set.mem_insert_iff]

/-- The topology induced by pulling back the discrete topology on Prop along the `a`-th projection. -/
@[reducible] def τ (a : α) : TopologicalSpace (Set α) :=
  @TopologicalSpace.induced (Set α) Prop (fun S => a ∈ S) Prop_space





/-- The four basic open sets of `opensOver a` are open in `τ a`. -/
lemma opensOver_sub_τ (a : α) : opensOver a ⊆ {S | (τ a).IsOpen S} := by
  intro S HS
  simp only [opensOver, Set.mem_insert_iff, Set.mem_singleton_iff] at HS
  rcases HS with rfl | rfl | rfl | rfl
  · -- principalOpen a: preimage of {True} under (a ∈ ·)
    show @IsOpen (Set α) (@TopologicalSpace.induced (Set α) Prop (fun S => a ∈ S) Prop_space)
      (principalOpen a)
    rw [isOpen_induced_iff]
    exact ⟨{True}, isOpen_discrete _, Set.ext (fun _ => by simp [principalOpen])⟩
  · -- coPrincipalOpen a: preimage of {False}
    show @IsOpen (Set α) (@TopologicalSpace.induced (Set α) Prop (fun S => a ∈ S) Prop_space)
      (coPrincipalOpen a)
    rw [isOpen_induced_iff]
    exact ⟨{False}, isOpen_discrete _, Set.ext (fun _ => by simp [coPrincipalOpen])⟩
  · exact @isOpen_univ _ (τ a)
  · exact @isOpen_empty _ (τ a)

/-- `τ a` is coarser than the topology generated by `opensOver a` (since opensOver ⊆ opens of τ a). -/
lemma opensOver_le_τ (a : α) : τ a ≤ generateFrom (opensOver a) := by
  rw [le_generateFrom_iff_subset_isOpen]
  exact opensOver_sub_τ a

/-- The product topology on `Set α` is coarser than each factor topology `τ a`. -/
lemma τ_le_product_topology (a : α) :
    (product_topology : TopologicalSpace (Set α)) ≤ τ a := by
  show (Pi.topologicalSpace : TopologicalSpace (Set α)) ≤ τ a
  unfold τ Pi.topologicalSpace
  exact iInf_le (fun i => @TopologicalSpace.induced (Set α) Prop
    (fun S => i ∈ S) Prop_space) a



@[simp] lemma isOpen_generated_from_basic {β : Type*} [TopologicalSpace β]
    {s : Set (Set β)} {x : Set β} (hx : x ∈ s) : (generateFrom s).IsOpen x :=
  isOpen_generateFrom_of_mem hx

/-- `principalOpen a` is open in the product topology. -/
lemma isOpen_principalOpen {a : α} : IsOpen (principalOpen a) := by
  -- principalOpen a ∈ opensOver a ⊆ opens(τ a)
  -- τ a ≤ generateFrom(opensOver a)
  -- product_topology ≤ τ a
  -- so product_topology ≤ generateFrom(opensOver a)
  -- and principalOpen a ∈ generateFrom(opensOver a) (it's a basic open)
  -- so it's open in product_topology (which has more opens in Lean 4's order)
  apply (le_trans (τ_le_product_topology _) (opensOver_le_τ a))
  exact isOpen_generateFrom_of_mem (principalOpen_mem_opensOver)

/-- `coPrincipalOpen a` is open in the product topology. -/
lemma isOpen_coPrincipalOpen {a : α} : IsOpen (coPrincipalOpen a) := by
  apply (le_trans (τ_le_product_topology _) (opensOver_le_τ a))
  exact isOpen_generateFrom_of_mem (coPrincipalOpen_mem_opensOver)

lemma isClosed_principalOpen {a : α} : IsClosed (principalOpen a) :=
  is_closed_of_compl_open (neg_principalOpen ▸ isOpen_coPrincipalOpen)

lemma isClosed_coPrincipalOpen {a : α} : IsClosed (coPrincipalOpen a) :=
  is_closed_of_compl_open (neg_coPrincipalOpen ▸ isOpen_principalOpen)

lemma isClopen_principalOpen {a : α} : IsClopen (principalOpen a) :=
  ⟨isClosed_principalOpen, isOpen_principalOpen⟩

lemma isClopen_coPrincipalOpen {a : α} : IsClopen (coPrincipalOpen a) :=
  ⟨isClosed_coPrincipalOpen, isOpen_coPrincipalOpen⟩

@[reducible] def principalOpenFinset (F : Finset α) : Set (Set α) :=
  {S | (↑F : Set α) ⊆ S}

lemma mem_principalOpenFinset_iff {F : Finset α} {x : Set α} :
    x ∈ principalOpenFinset F ↔ (↑F : Set α) ⊆ x := Iff.rfl

@[simp] lemma principalOpenFinset_insert [DecidableEq α] {F : Finset α} {a : α} :
    principalOpenFinset (insert a F) = principalOpenFinset {a} ∩ principalOpenFinset F := by
  ext x
  simp only [principalOpenFinset, Set.mem_setOf_eq, Set.mem_inter_iff,
    Finset.coe_singleton, Set.singleton_subset_iff, Finset.coe_insert, Set.insert_subset_iff]

lemma principalOpenFinset_eq_inter [DecidableEq α] (F : Finset α) :
    principalOpenFinset F = F.inf principalOpen := by
  induction F using Finset.induction with
  | empty => ext x; simp [principalOpenFinset, Finset.inf_empty]
  | insert _ _ =>
    rename_i a A ha ih
    rw [Finset.inf_insert, ← ih]
    ext x
    simp only [principalOpenFinset, principalOpen, Set.mem_setOf_eq,
      Finset.coe_insert, Set.insert_subset_iff]
    simp [Set.mem_inter_iff, Set.mem_setOf_eq]

@[reducible] def coPrincipalOpenFinset (F : Finset α) : Set (Set α) :=
  {S | (↑F : Set α) ⊆ Sᶜ}

@[simp] lemma coPrincipalOpenFinset_insert [DecidableEq α] {F : Finset α} {a : α} :
    coPrincipalOpenFinset (insert a F) = coPrincipalOpenFinset {a} ∩ coPrincipalOpenFinset F := by
  ext x
  simp only [coPrincipalOpenFinset, Set.mem_setOf_eq, Set.mem_inter_iff,
    Finset.coe_singleton, Set.singleton_subset_iff, Finset.coe_insert, Set.insert_subset_iff]

lemma coPrincipalOpenFinset_eq_inter [DecidableEq α] (F : Finset α) :
    coPrincipalOpenFinset F = F.inf coPrincipalOpen := by
  induction F using Finset.induction with
  | empty => ext x; simp [coPrincipalOpenFinset, Finset.inf_empty]
  | insert _ _ =>
    rename_i a A ha ih
    rw [Finset.inf_insert, ← ih]
    ext x
    simp only [coPrincipalOpenFinset, coPrincipalOpen, Set.mem_setOf_eq,
      Finset.coe_insert, Set.insert_subset_iff]
    simp [Set.mem_inter_iff, Set.mem_setOf_eq]

lemma isClopen_principalOpenFinset [DecidableEq α] (F : Finset α) :
    IsClopen (principalOpenFinset F) := by
  rw [principalOpenFinset_eq_inter]
  exact is_clopen_finite_inter' (fun _ _ => isClopen_principalOpen)

lemma isClopen_coPrincipalOpenFinset [DecidableEq α] (F : Finset α) :
    IsClopen (coPrincipalOpenFinset F) := by
  rw [coPrincipalOpenFinset_eq_inter]
  exact is_clopen_finite_inter' (fun _ _ => isClopen_coPrincipalOpen)



/-- The standard basis for the product topology on `Set α`. -/
def standardBasis : Set (Set (Set α)) :=
  {T : Set (Set α) | ∃ p_ins p_out : Finset α,
    T = (p_ins.inf principalOpen) ∩ (p_out.inf coPrincipalOpen) ∧
    Disjoint p_ins p_out} ∪ {∅}



@[simp] lemma principalOpen_mem_standardBasis {a : α} :
    principalOpen a ∈ @standardBasis α := by
  simp only [standardBasis, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
  left
  classical
  exact ⟨{a}, ∅, by simp [Finset.inf_singleton], by simp⟩

@[simp] lemma coPrincipalOpen_mem_standardBasis {a : α} :
    coPrincipalOpen a ∈ @standardBasis α := by
  simp only [standardBasis, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
  left
  classical
  exact ⟨∅, {a}, by simp [Finset.inf_singleton], by simp⟩











open Cardinal



end CantorSpace


end CohenSource_CantorSpace


/- Source module: Definitions.Flypitch4.Colimit -/
section CohenSource_Colimit
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/colimit.lean -/



set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! ## Lean 3 → Lean 4 Port: Notes for Colimit.lean

### Scope
Only declarations needed by `src/henkin.lean` are ported. The following are dropped:
- `constant_functor` — 0 uses outside colimit.lean
- `trans` (the colimit lemma) — 0 uses outside colimit.lean; `Trans` in Lean 4 is a typeclass

### Quotient API choices
- `colimit` is `@[reducible]` so that `Quotient.lift`, `Quotient.sound`, etc. can unify with it
- Lean 3 `quotient.mk`   → Lean 4 `Quotient.mk (coproduct_setoid F)`
- Lean 3 `quotient.lift` → Lean 4 `Quotient.lift`
- Lean 3 `quotient.eq`   → Lean 4 `Quotient.exact` / `Quotient.sound`

### `cocone_of_colimit` kept as an internal helper
Used internally to prove `same_fiber_as_push_to_r/l`, which henkin.lean uses directly.

### Structures: `Reflexive` / `Transitive` deprecated in Lean 4
Use explicit `∀` hypotheses in `directed_type`.
-/

universe u v

namespace colimit

structure directed_type : Type (u + 1) where
  carrier : Type u
  rel : carrier → carrier → Prop
  h_reflexive : ∀ x : carrier, rel x x
  h_transitive : ∀ {x y z : carrier}, rel x y → rel y z → rel x z
  h_directed : ∀ x y : carrier, ∃ z : carrier, rel x z ∧ rel y z

structure directed_diagram (D : directed_type.{u}) : Type (max (u + 1) (v + 1)) where
  obj : D.carrier → Type v
  mor : ∀ {x y : D.carrier}, D.rel x y → (obj x → obj y)
  h_mor : ∀ {x y z : D.carrier} {f1 : D.rel x y} {f2 : D.rel y z} {f3 : D.rel x z},
          mor f3 = mor f2 ∘ mor f1

@[reducible] def directed_type_of_nat : directed_type where
  carrier := ℕ
  rel := (· ≤ ·)
  h_reflexive := Nat.le_refl
  h_transitive := Nat.le_trans
  h_directed := fun x y => ⟨x + y, Nat.le_add_right x y, Nat.le_add_left y x⟩

notation "ℕ'" => directed_type_of_nat

def coproduct_of_directed_diagram {D : directed_type.{u}} (F : directed_diagram.{u, v} D) :
    Type (max u v) :=
  Σ a : D.carrier, F.obj a



def germ_relation {D : directed_type.{u}} (F : directed_diagram.{u, v} D) :
    coproduct_of_directed_diagram F → coproduct_of_directed_diagram F → Prop :=
  fun ⟨i, x⟩ ⟨j, y⟩ =>
    ∃ k : D.carrier, ∃ z : F.obj k, ∃ f_x : D.rel i k, ∃ f_y : D.rel j k,
    F.mor f_x x = z ∧ F.mor f_y y = z

lemma germ_equivalence {D : directed_type.{u}} (F : directed_diagram.{u, v} D) :
    Equivalence (germ_relation F) where
  refl := fun ⟨i, x⟩ => by
    have h_refl := D.h_reflexive i
    exact ⟨i, F.mor h_refl x, h_refl, h_refl, rfl, rfl⟩
  symm := fun {a b} h => by
    obtain ⟨i, x⟩ := a; obtain ⟨j, y⟩ := b
    obtain ⟨ℓ, z, f_x, f_y, H1, H2⟩ := h
    exact ⟨ℓ, z, f_y, f_x, H2, H1⟩
  trans := fun {a b c} hab hbc => by
    obtain ⟨i, x⟩ := a; obtain ⟨j, y⟩ := b; obtain ⟨k, z⟩ := c
    obtain ⟨ℓ₁, _w₁, fi, fj1, Hil, Hjl1⟩ := hab
    obtain ⟨ℓ₂, _w₂, fj2, fk, Hjl2, Hkl2⟩ := hbc
    obtain ⟨ℓ₃, g1, g2⟩ := D.h_directed ℓ₁ ℓ₂
    have f1 : D.rel i ℓ₃ := D.h_transitive fi g1
    have f2 : D.rel j ℓ₃ := D.h_transitive fj1 g1
    have f3 : D.rel k ℓ₃ := D.h_transitive fk g2
    -- By h_mor, all compositions commute
    have H1 : F.mor f1 = F.mor g1 ∘ F.mor fi := F.h_mor
    have H2l : F.mor f2 = F.mor g1 ∘ F.mor fj1 := F.h_mor
    have H2r : F.mor f2 = F.mor g2 ∘ F.mor fj2 := F.h_mor
    have H3 : F.mor f3 = F.mor g2 ∘ F.mor fk := F.h_mor
    -- F.mor f1 x = F.mor g1 (F.mor fi x) = F.mor g1 w₁ = F.mor g1 (F.mor fj1 y) = F.mor f2 y
    have Hf1_f2 : F.mor f1 x = F.mor f2 y := by
      rw [H1, H2l]; simp only [Function.comp_apply]; rw [Hil, Hjl1]
    -- F.mor f3 z = F.mor g2 (F.mor fk z) = F.mor g2 w₂ = F.mor g2 (F.mor fj2 y) = F.mor f2 y
    have Hf3_f2 : F.mor f3 z = F.mor f2 y := by
      rw [H3, H2r]; simp only [Function.comp_apply]; rw [Hkl2, Hjl2]
    exact ⟨ℓ₃, F.mor f2 y, f1, f3, Hf1_f2, Hf3_f2⟩

/-- The setoid on the coproduct given by germ equivalence -/
def coproduct_setoid {D : directed_type} (F : directed_diagram D) :
    Setoid (coproduct_of_directed_diagram F) :=
  ⟨germ_relation F, germ_equivalence F⟩

@[reducible] def colimit {D : directed_type.{u}} (F : directed_diagram.{u, v} D) :
    Type (max u v) :=
  Quotient (coproduct_setoid F)

def canonical_map {D : directed_type} {F : directed_diagram D} (i : D.carrier) :
    F.obj i → colimit F :=
  fun x => Quotient.mk (coproduct_setoid F) ⟨i, x⟩

lemma canonical_map_inj_of_transition_maps_inj {D : directed_type} {F : directed_diagram D}
    (i : D.carrier)
    (H : ∀ {i j : D.carrier}, ∀ h : D.rel i j, Function.Injective (F.mor h)) :
    Function.Injective (@canonical_map D F i) := by
  intro x y heq
  simp only [canonical_map] at heq
  have heq' := Quotient.exact heq
  -- heq' : (coproduct_setoid F).r ⟨i, x⟩ ⟨i, y⟩
  -- i.e., germ_relation F ⟨i,x⟩ ⟨i,y⟩
  change germ_relation F ⟨i, x⟩ ⟨i, y⟩ at heq'
  obtain ⟨j, _z, edge_x, edge_y, H1, H2⟩ := heq'
  exact H edge_x (by rw [H1, H2])

structure cocone {D : directed_type} (F : directed_diagram D) where
  vertex : Type*
  map : ∀ i : D.carrier, F.obj i → vertex
  h_compat : ∀ {i j : D.carrier}, ∀ h : D.rel i j, map i = map j ∘ F.mor h

/- The colimit is itself a cocone over its diagram -/
def cocone_of_colimit {D : directed_type} (F : directed_diagram D) : cocone F where
  vertex := colimit F
  map := canonical_map
  h_compat := by
    intro i j H
    funext x
    simp only [canonical_map, Function.comp_apply]
    apply Quotient.sound
    -- Need: (coproduct_setoid F).r ⟨i, x⟩ ⟨j, F.mor H x⟩
    -- i.e., germ_relation F ⟨i, x⟩ ⟨j, F.mor H x⟩
    show germ_relation F ⟨i, x⟩ ⟨j, F.mor H x⟩
    have h_refl_j := D.h_reflexive j
    refine ⟨j, F.mor H x, H, h_refl_j, rfl, ?_⟩
    -- F.mor h_refl_j (F.mor H x) = F.mor H x
    -- By h_mor with f1=H, f2=h_refl_j, f3=H: F.mor H = F.mor h_refl_j ∘ F.mor H
    have hmor : F.mor H = F.mor h_refl_j ∘ F.mor H := @F.h_mor i j j H h_refl_j H
    exact (congr_fun hmor x).symm

/- Given a cocone V over a diagram D, return the canonical map colim D → V -/
def universal_map {D : directed_type} {F : directed_diagram D} {V : cocone F} :
    colimit F → V.vertex :=
  Quotient.lift (fun p => V.map p.1 p.2) (by
    intro ⟨i, x⟩ ⟨j, y⟩ h
    -- h : (coproduct_setoid F).r ⟨i, x⟩ ⟨j, y⟩, i.e., germ_relation F ⟨i, x⟩ ⟨j, y⟩
    change germ_relation F ⟨i, x⟩ ⟨j, y⟩ at h
    obtain ⟨k, _z, f1, f2, H1, H2⟩ := h
    show V.map i x = V.map j y
    have e1 : V.map i x = V.map k (F.mor f1 x) := congr_fun (V.h_compat f1) x
    have e2 : V.map j y = V.map k (F.mor f2 y) := congr_fun (V.h_compat f2) y
    rw [e1, e2, H1, H2])

@[simp] lemma universal_map_property {D : directed_type} {F : directed_diagram D}
    {V : cocone F} (i : D.carrier) (x : F.obj i) :
    universal_map (V := V) (canonical_map i x) = V.map i x := rfl

lemma universal_map_inj_of_components_inj {D : directed_type} {F : directed_diagram D}
    {V : cocone F} (h_inj : ∀ i : D.carrier, Function.Injective (V.map i)) :
    Function.Injective (universal_map (V := V) : colimit F → V.vertex) := by
  intro a b h
  induction a using Quotient.inductionOn with | _ p => ?_
  induction b using Quotient.inductionOn with | _ q => ?_
  obtain ⟨i, x⟩ := p; obtain ⟨j, y⟩ := q
  -- h : universal_map ⟦⟨i,x⟩⟧ = universal_map ⟦⟨j,y⟩⟧
  -- i.e. V.map i x = V.map j y
  simp only [universal_map, Quotient.lift_mk] at h
  -- h : V.map i x = V.map j y
  apply Quotient.sound
  show germ_relation F ⟨i, x⟩ ⟨j, y⟩
  obtain ⟨k, Hik, Hjk⟩ := D.h_directed i j
  refine ⟨k, F.mor Hik x, Hik, Hjk, rfl, ?_⟩
  -- Goal: F.mor Hjk y = F.mor Hik x
  apply h_inj k
  -- Goal: V.map k (F.mor Hjk y) = V.map k (F.mor Hik x)
  have e1 : V.map i x = V.map k (F.mor Hik x) := congr_fun (V.h_compat Hik) x
  have e2 : V.map j y = V.map k (F.mor Hjk y) := congr_fun (V.h_compat Hjk) y
  rw [← e2, ← e1]; exact h.symm

/- Given a germ-equivalence class from the colimit, return a representative from the coproduct
   and a proof that this is a lift -/
noncomputable def germ_rep {D : directed_type} {F : directed_diagram D} (a : colimit F) :
    Σ' x : coproduct_of_directed_diagram F,
      Quotient.mk (coproduct_setoid F) x = a :=
  Classical.psigma_of_exists (Quotient.exists_rep a)

@[simp] lemma canonical_map_quotient {D : directed_type} {F : directed_diagram D}
    (a : coproduct_of_directed_diagram F) :
    canonical_map a.1 a.2 = Quotient.mk (coproduct_setoid F) a := by
  simp only [canonical_map]
  congr 1

/- Assuming canonical maps into the colimit are injective, ⟨i,x⟩ and ⟨j,y⟩ in the same fiber
   over a z : colimit F are related by any transition map i → j. -/
@[simp] lemma eq_mor_of_same_fiber {D : directed_type} {F : directed_diagram D}
    (a b : coproduct_of_directed_diagram F) {z : colimit F}
    (Ha : Quotient.mk (coproduct_setoid F) a = z)
    (Hb : Quotient.mk (coproduct_setoid F) b = z)
    (H_inj : ∀ i : D.carrier, Function.Injective (@canonical_map D F i))
    (H_rel : D.rel a.1 b.1) : F.mor H_rel a.2 = b.2 := by
  -- The cocone_of_colimit h_compat gives:
  -- canonical_map a.1 a.2 = canonical_map b.1 (F.mor H_rel a.2)
  have H_eq : z = canonical_map b.1 (F.mor H_rel a.2) := by
    have hcompat := (cocone_of_colimit F).h_compat H_rel
    have hcf := congr_fun hcompat a.2
    simp only [cocone_of_colimit, Function.comp_apply] at hcf
    rw [canonical_map_quotient a, Ha] at hcf
    exact hcf
  -- canonical_map b.1 b.2 = canonical_map b.1 (F.mor H_rel a.2)
  have heq : canonical_map b.1 b.2 = canonical_map b.1 (F.mor H_rel a.2) := by
    rw [canonical_map_quotient b, Hb, H_eq]
  exact (H_inj b.1 heq).symm

@[simp] lemma eq_mor_of_same_fiber' {D : directed_type} {F : directed_diagram D}
    (a_fst b_fst : D.carrier) (a_snd : F.obj a_fst) (b_snd : F.obj b_fst)
    {z : colimit F}
    (Ha : Quotient.mk (coproduct_setoid F) (⟨a_fst, a_snd⟩ : coproduct_of_directed_diagram F) = z)
    (Hb : Quotient.mk (coproduct_setoid F) (⟨b_fst, b_snd⟩ : coproduct_of_directed_diagram F) = z)
    (H_inj : ∀ i : D.carrier, Function.Injective (@canonical_map D F i))
    (H_rel : D.rel a_fst b_fst) : F.mor H_rel a_snd = b_snd :=
  eq_mor_of_same_fiber ⟨a_fst, a_snd⟩ ⟨b_fst, b_snd⟩ Ha Hb H_inj H_rel

/- Given an x : F_i and j : ℕ, apply the transition map to obtain x' : F_{i+j} -/
@[reducible] def push_to_sum_r {F : directed_diagram ℕ'} {i : ℕ} (x : F.obj i) (j : ℕ) :
    F.obj (i + j) :=
  F.mor (D := ℕ') (Nat.le_add_right i j) x

@[reducible] def push_to_sum_l {F : directed_diagram ℕ'} {j : ℕ} (x : F.obj j) (i : ℕ) :
    F.obj (i + j) :=
  F.mor (D := ℕ') (Nat.le_add_left j i) x

/- The push_to of x is in the same germ-equivalence class as x -/
lemma same_fiber_as_push_to_r {F : directed_diagram ℕ'} {i : ℕ} (x : F.obj i) (j : ℕ) :
    @canonical_map ℕ' F i x = @canonical_map ℕ' F (i + j) (push_to_sum_r x j) :=
  congr_fun ((cocone_of_colimit F).h_compat (D := ℕ') (Nat.le_add_right i j)) x

lemma same_fiber_as_push_to_l {F : directed_diagram ℕ'} {j : ℕ} (x : F.obj j) (i : ℕ) :
    @canonical_map ℕ' F j x = @canonical_map ℕ' F (i + j) (push_to_sum_l x i) :=
  congr_fun ((cocone_of_colimit F).h_compat (D := ℕ') (Nat.le_add_left j i)) x

end colimit

namespace omega_colimit

open colimit

/- Facts about directed colimits indexed by ℕ'. -/

/- Build transition maps from a successor-step map by induction on the target.
   Uses an auxiliary explicit-argument version to avoid implicit-argument
   inference failures in recursive calls. -/
 def map_aux (F : ℕ → Type*) (h_succ : ∀ {i : ℕ}, F i → F (i + 1)) :
    ∀ (x y : ℕ), x ≤ y → F x → F y
  | x, 0, h => by rw [Nat.eq_zero_of_le_zero h]; exact id
  | x, y + 1, h =>
      if hx : x = y + 1 then by rw [hx]; exact id
      else h_succ ∘ map_aux F h_succ x y (Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne h hx))

def diagram.mk.map {F : ℕ → Type*} {h_succ : ∀ {i : ℕ}, F i → F (i + 1)}
    (x y : ℕ) (h : x ≤ y) : F x → F y :=
  map_aux F h_succ x y h

@[simp] lemma diagram.mk.map_self_id {F : ℕ → Type*}
    {h_succ : ∀ (i : ℕ), F i → F (i + 1)} (x : ℕ) :
    @diagram.mk.map F (fun {i} => h_succ i) x x (Nat.le_refl x) = id := by
  induction x with
  | zero => simp [diagram.mk.map, map_aux]
  | succ n ih =>
    simp only [diagram.mk.map, map_aux]
    rfl

/- If the successive maps of h_succ are injective, then all their compositions are injective -/


/- Functoriality lemma for map_aux -/


/- Given a ℕ-indexed family of types and a way of assigning maps between successive objects
   in this family, return the induced directed_diagram over ℕ'. -/


end omega_colimit


end CohenSource_Colimit


