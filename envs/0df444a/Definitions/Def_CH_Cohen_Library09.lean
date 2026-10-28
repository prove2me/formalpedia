-- Prove2me | Definitions.Def_CH_Cohen_Library09
-- name    : CH_Cohen_Library09
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-26T01:58:07.421649+00:00
-- url     : https://prove2.me/theorems/cf12b337-119f-4362-81e1-e34100e3e3e9
-- title:
--   Boolean-valued set theory: Henkin, Forcing
-- statement:
--   This module provides Henkin witness languages and the ordinary term-model construction; the Cohen algebra and its binary-sequence names. These objects form the language and model interfaces used in the forcing and completeness arguments.
--
--   **Formalization Note** The module retains the structural normalization facts needed by these definitions and their constructor proofs. The principal forcing and model-existence assertions are separate theorem nodes.
--
--   Original formalization: Jesse Han and Floris van Doorn. Lean 4 port: Ian Klatzco, with Claude (Apache-2.0). Adapted to the pinned Prove2Me environment.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Henkin.lean; https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Forcing.lean

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
import Definitions.Def_CH_Cohen_Library08
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

/- Source module: Definitions.Flypitch4.Henkin -/
section CohenSource_Henkin
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/henkin.lean — Part 1 (lines 1-450).
   Task 16a; Task 16b will continue from line 451. -/





set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Fol

open colimit omega_colimit

universe u

/-!
## Directed colimits of languages

These are fieldwise (and then indexwise) colimits of types.
For the Henkin construction, the directed type is always ℕ' (carrier = ℕ : Type 0),
so we can use a single universe u for the language symbols.
-/

/-- A directed diagram of Languages at universe u indexed by ℕ -/
structure directed_diagram_language : Type (u + 1) where
  obj : ℕ → Language.{u}
  mor : ∀ {x y : ℕ}, x ≤ y → (obj x →ᴸ obj y)
  h_mor : ∀ {x y z : ℕ} {f1 : x ≤ y} {f2 : y ≤ z} {f3 : x ≤ z},
    mor f3 = (mor f2).comp (mor f1)

/-- Restrict to n-ary function family -/
def diagram_functions (F : directed_diagram_language.{u}) (n : ℕ) : directed_diagram ℕ' where
  obj x := (F.obj x).functions n
  mor h := (F.mor h).on_function
  h_mor := by
    intro x y z f1 f2 f3
    have key := F.h_mor (f1 := f1) (f2 := f2) (f3 := f3)
    funext a
    exact congr_fun (show (F.mor f3).on_function = (F.mor f2).on_function ∘ (F.mor f1).on_function
      from by rw [key]) a

/-- Restrict to n-ary relation family -/
def diagram_relations (F : directed_diagram_language.{u}) (n : ℕ) : directed_diagram ℕ' where
  obj x := (F.obj x).relations n
  mor h := (F.mor h).on_relation
  h_mor := by
    intro x y z f1 f2 f3
    have key := F.h_mor (f1 := f1) (f2 := f2) (f3 := f3)
    funext a
    exact congr_fun (show (F.mor f3).on_relation = (F.mor f2).on_relation ∘ (F.mor f1).on_relation
      from by rw [key]) a

/-- The colimit language -/
def colimit_language (F : directed_diagram_language.{u}) : Language.{u} :=
  ⟨fun n => colimit (diagram_functions F n),
   fun n => colimit (diagram_relations F n)⟩

/-- Canonical map from stage i into the colimit language -/
def canonical_map_language {F : directed_diagram_language.{u}} (i : ℕ) :
    F.obj i →ᴸ colimit_language F :=
  ⟨fun {n} => @canonical_map _ (diagram_functions F n) i,
   fun {n} => @canonical_map _ (diagram_relations F n) i⟩

/-- A cocone over a directed diagram of languages -/
structure cocone_language (F : directed_diagram_language.{u}) where
  vertex : Language.{u}
  map : ∀ i : ℕ, F.obj i →ᴸ vertex
  h_compat : ∀ {i j : ℕ}, ∀ h : i ≤ j, map i = (map j).comp (F.mor h)

/-- The colimit is itself a cocone -/
def cocone_of_colimit_language (F : directed_diagram_language.{u}) :
    cocone_language F where
  vertex := colimit_language F
  map := canonical_map_language
  h_compat := by
    intro i j H
    apply Lhom.Lhom_funext
    · funext n; funext f
      simp only [canonical_map_language, Lhom.comp, Function.comp]
      exact congr_fun ((cocone_of_colimit (diagram_functions F n)).h_compat H) f
    · funext n; funext R
      simp only [canonical_map_language, Lhom.comp, Function.comp]
      exact congr_fun ((cocone_of_colimit (diagram_relations F n)).h_compat H) R

/-!
## The Henkin construction
-/

/-- Inductive type of function symbols for one Henkin step.
    `inc` embeds L-symbols; `wit` introduces witness constants. -/
inductive henkin_language_functions (L : Language.{u}) : ℕ → Type u
  | inc : ∀ {n}, L.functions n → henkin_language_functions L n
  | wit : bounded_formula L 1 → henkin_language_functions L 0

open henkin_language_functions

/-- One Henkin step on languages -/
@[reducible] def henkin_language_step (L : Language.{u}) : Language.{u} :=
  ⟨henkin_language_functions L, L.relations⟩

def wit' {L : Language.{u}} : bounded_formula L 1 → (henkin_language_step L).constants :=
  wit

def henkin_language_inclusion {L : Language.{u}} : L →ᴸ henkin_language_step L :=
  ⟨fun {_} f => inc f, fun {_} => id⟩

lemma henkin_language_inclusion_inj {L : Language.{u}} :
    Lhom.is_injective (@henkin_language_inclusion L) :=
  ⟨fun {_} _ _ H => henkin_language_functions.inc.inj H, fun {_} _ _ H => H⟩

/-! ## wit_property and henkin_theory_step -/

/-- The witnessing sentence: (∃ᵇf) → f[c/0] -/
@[reducible] def wit_property {L : Language.{u}} (f : bounded_formula L 1) (c : L.constants) :
    sentence L :=
  bd_imp (bd_ex f) (subst0_bounded_formula f (bd_const c))

/-- One Henkin step on theories -/
def henkin_theory_step {L : Language.{u}} (T : SentTheory L) :
    SentTheory (henkin_language_step L) :=
  henkin_language_inclusion.Theory_induced T ∪
  (fun f : bounded_formula L 1 =>
    wit_property (henkin_language_inclusion.on_bounded_formula f) (wit' f)) '' Set.univ

/-- Auxiliary tautology: `T ⊢ₛ' ∃ x, (∃ y, f y) → f x`. -/
 lemma henkin_witness_tautology {L : Language.{u}} (T : SentTheory L)
    (f : bounded_formula L 1) :
    T ⊢ₛ' bd_ex (bd_imp (bd_ex f).cast1 f) := by
  show T.fst ⊢' (bd_ex (bd_imp (bd_ex f).cast1 f)).fst
  refine ⟨?_⟩
  -- Goal: T.fst ⊢ (bd_ex (bd_imp (bd_ex f).cast1 f)).fst
  -- = ∃' ((∃' f.fst) ⟹ f.fst)  (since cast1.fst = .fst)
  show T.fst ⊢ ∃' ((bd_ex f).cast1.fst ⟹ f.fst)
  apply prf.falsumE
  apply prf.impE (∃' f.fst)
  · -- Goal: insert ¬∃' ... ⊢ (∃' f.fst) ⟹ ⊥'
    apply prf.impI
    apply prf.impE _ axm2
    apply exE axm1
    -- Goal: insert f.fst (lift_formula1 '' insert (∃'f.fst) (insert ¬∃' ... T.fst)) ⊢
    --       lift_formula1 (∃' ((bd_ex f).cast1.fst ⟹ f.fst))
    apply exI &0
    rw [lift_subst_formula_cancel]
    -- Now we need: ⊢ (bd_ex f).cast1.fst ⟹ f.fst
    -- (bd_ex f).cast1.fst = (bd_ex f).fst, so this is (∃' f.fst) ⟹ f.fst
    rw [bounded_preformula.cast1_fst]
    apply prf.impI
    exact axm2
  · -- Goal: insert (∼∃' ...) T.fst ⊢ ∃' f.fst
    apply prf.falsumE
    apply prf.impE _ axm2
    apply exI &0
    -- Goal: ... ⊢ ((bd_ex f).cast1.fst ⟹ f.fst)[&0 // 0]f
    -- = (bd_ex f).cast1.fst[&0/0] ⟹ f.fst[&0/0]
    apply prf.impI
    apply exfalso
    apply prf.impE _ axm2
    -- Goal: ⊢ ∃' f.fst
    show _ ⊢ ∃' f.fst
    have key : (bd_ex f).cast1.fst [&0 // 0]f = ∃' f.fst := by
      rw [bounded_preformula.cast1_fst, subst_sentence_irrel]; rfl
    rw [← key]
    exact axm1

/-- The Henkin extension of a consistent theory is consistent -/
lemma is_consistent_henkin_theory_step {L : Language.{u}} {T : SentTheory L}
    (hT : T.is_consistent) : (henkin_theory_step T).is_consistent := by
  -- Apply is_consistent_extend with h := λ f, (∃' f).cast1 ⟹ f and g := wit'.
  have hwit_inj : Function.Injective (@wit' L) := by
    intro f f' h
    -- wit' f = wit f, so this comes from injection on `wit`
    exact henkin_language_functions.wit.inj h
  have hwit_not_in : ∀ x : bounded_formula L 1,
      wit' x ∉ Set.range ((@henkin_language_inclusion L).on_function : L.functions 0 →
        (henkin_language_step L).functions 0) := by
    intro x ⟨g, hg⟩
    -- hg : henkin_language_inclusion.on_function g = wit' x
    -- on_function g = inc g, wit' x = wit x — different constructors
    simp [henkin_language_inclusion, wit'] at hg
  have hext :=
    Lhom.is_consistent_extend hT henkin_language_inclusion_inj
      (fun f => bd_imp (bd_ex f).cast1 f)
      (fun f => henkin_witness_tautology T f)
      wit' hwit_inj hwit_not_in
  -- hext : (henkin_language_inclusion.Theory_induced T ∪
  --   (fun f => subst0 (incl.on_bf (bd_imp (bd_ex f).cast1 f)) (bd_const (wit' f))) '' Set.univ)
  --   .is_consistent
  -- Goal: henkin_theory_step T = the above set, modulo the witness shape.
  -- The witness sentence simplifies to wit_property (incl.on_bf f) (wit' f).
  have hset : henkin_theory_step T =
      (@henkin_language_inclusion L).Theory_induced T ∪
        (fun f => subst0_bounded_formula
          ((@henkin_language_inclusion L).on_bounded_formula
            (bd_imp (bd_ex f).cast1 f))
          (bd_const (wit' f))) '' Set.univ := by
    show henkin_theory_step T = _
    unfold henkin_theory_step
    congr 1
    apply Set.image_congr'
    intro f
    -- Goal: wit_property (incl.on_bf f) (wit' f) =
    --       subst0 (incl.on_bf (bd_imp (bd_ex f).cast1 f)) (bd_const (wit' f))
    apply bounded_preformula.eq
    -- compare via .fst
    simp only [wit_property, subst0_bounded_formula_fst, Lhom.on_bounded_formula,
               bounded_preformula.fst_bd_imp, bounded_preformula.fst_bd_ex,
               bounded_preformula.cast1_fst, subst_formula]
    -- Now the goal is:
    -- ∃' (incl.on_formula f.fst) ⟹ (incl.on_formula f.fst)[c/0] =
    -- subst (incl.on_formula (∃' f.fst)) c 0 ⟹ (incl.on_formula f.fst)[c/0]
    -- The RHS first arg equals the LHS first arg because (incl.on_formula (∃' f.fst))
    -- is a sentence (closed bounded_formula).
    congr 1
    -- Goal: ∃' (incl.on_bf f).fst = (incl.on_bf (cast1 (bd_ex f))).fst [c // 0]f
    -- RHS: (incl.on_bf (cast1 (bd_ex f))).fst = (cast1 (bd_ex f)).cast1 ... no wait
    -- (incl.on_bf cast1(X)).fst = on_formula (cast1 X).fst = on_formula X.fst
    -- So RHS = on_formula (bd_ex f).fst [c//0]f = on_formula (∃' f.fst) [c//0]f
    --       = (∃' (on_formula f.fst)) [c//0]f
    -- And subst sentence_irrel gives ∃' (on_formula f.fst).
    have hRHS : ((@henkin_language_inclusion L).on_bounded_formula
        (bounded_preformula.cast1 (bd_ex f))).fst =
        ∃' ((@henkin_language_inclusion L).on_bounded_formula f).fst := by
      simp only [Lhom.on_bounded_formula_fst, bounded_preformula.cast1_fst,
          bounded_preformula.fst_bd_ex]
      rfl
    rw [hRHS]
    -- Goal: ∃' (incl.on_bf f).fst = (∃' (incl.on_bf f).fst) [c//0]f
    -- ∃' X is closed if X is bounded_formula L 1, so use subst_sentence_irrel via casting
    -- to a sentence
    have hSent : (bd_ex ((@henkin_language_inclusion L).on_bounded_formula f) :
        sentence (henkin_language_step L)).fst =
        ∃' ((@henkin_language_inclusion L).on_bounded_formula f).fst := by
      simp only [bounded_preformula.fst_bd_ex]
    rw [← hSent, subst_sentence_irrel]
  rw [hset]
  exact hext

/-! ## Henkin language chain -/

/-- Objects of the Henkin language chain -/
@[reducible] def henkin_language_chain_objects {L : Language.{u}} : ℕ → Language.{u}
  | 0 => L
  | (n + 1) => henkin_language_step (@henkin_language_chain_objects L n)



/-- Transition maps of the Henkin language chain -/
def henkin_language_chain_maps (L : Language.{u}) :
    ∀ (x y : ℕ), x ≤ y →
      Lhom (@henkin_language_chain_objects L x) (@henkin_language_chain_objects L y)
  | _, 0, H => Nat.eq_zero_of_le_zero H ▸ Lhom.id _
  | x, y + 1, H =>
      if hx : x = y + 1 then hx ▸ Lhom.id _
      else henkin_language_inclusion.comp
             (henkin_language_chain_maps L x y
               (Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne H hx)))

-- Private helper: the zero-zero case gives identity
 lemma hcm_zero_zero (L : Language.{u}) (H : 0 ≤ 0) :
    henkin_language_chain_maps L 0 0 H = Lhom.id L := rfl

-- Private helper: the self case gives identity
 lemma hcm_self (L : Language.{u}) (k : ℕ) (H : k ≤ k) :
    henkin_language_chain_maps L k k H = Lhom.id (@henkin_language_chain_objects L k) := by
  cases k with
  | zero => exact hcm_zero_zero L H
  | succ n =>
      simp only [henkin_language_chain_maps, dif_pos rfl]
      rfl

-- Private helper: the non-equal successor case gives a composition
 lemma hcm_succ_ne (L : Language.{u}) (x y : ℕ) (H : x ≤ y + 1) (hne : x ≠ y + 1) :
    henkin_language_chain_maps L x (y + 1) H =
    henkin_language_inclusion.comp
      (henkin_language_chain_maps L x y (Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne H hne))) := by
  simp only [henkin_language_chain_maps, dif_neg hne]

lemma henkin_language_chain_maps_inj (L : Language.{u}) (i j : ℕ) (h : i ≤ j) :
    Lhom.is_injective (henkin_language_chain_maps L i j h) := by
  induction j with
  | zero =>
    have h0 : i = 0 := Nat.eq_zero_of_le_zero h; subst h0
    rw [hcm_zero_zero]; exact ⟨fun {_} _ _ H => H, fun {_} _ _ H => H⟩
  | succ n ih =>
    by_cases hx : i = n + 1
    · subst hx
      rw [hcm_self]; exact ⟨fun {_} _ _ H => H, fun {_} _ _ H => H⟩
    · have hle : i ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne h hx)
      rw [hcm_succ_ne L i n h hx]
      have ih' := ih hle
      exact ⟨fun {m} x y H => ih'.on_function (henkin_language_inclusion_inj.on_function H),
             fun {m} x y H => ih'.on_relation (henkin_language_inclusion_inj.on_relation H)⟩

/-- Functoriality of the Henkin language chain maps -/
lemma henkin_language_chain_maps_functorial (L : Language.{u}) :
    ∀ (x y z : ℕ) (f1 : x ≤ y) (f2 : y ≤ z) (f3 : x ≤ z),
      henkin_language_chain_maps L x z f3 =
      (henkin_language_chain_maps L y z f2).comp (henkin_language_chain_maps L x y f1) := by
  intro x y z f1 f2 f3
  induction z with
  | zero =>
    have hy0 : y = 0 := Nat.eq_zero_of_le_zero f2
    have hx0 : x = 0 := Nat.le_antisymm (hy0 ▸ f1) (Nat.zero_le _)
    subst hx0; subst hy0
    simp [hcm_zero_zero, Lhom.id_is_left_identity]
  | succ n ih =>
    by_cases hy : y = n + 1
    · subst hy
      by_cases hx : x = n + 1
      · subst hx; simp [hcm_self, Lhom.id_is_left_identity]
      · have hxn : x ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne f3 hx)
        rw [hcm_succ_ne L x n f3 hx, hcm_self, Lhom.id_is_left_identity]
    · have hyn : y ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne f2 hy)
      by_cases hx : x = n + 1
      · exfalso; exact absurd (Nat.le_trans f1 hyn) (hx ▸ Nat.not_succ_le_self n)
      · have hxn : x ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne f3 hx)
        rw [hcm_succ_ne L x n f3 hx, hcm_succ_ne L y n f2 hy,
            ih hyn hxn]
        apply Lhom.Lhom_funext <;> (funext n; simp [Lhom.comp, Function.comp_assoc])

/-- The Henkin language chain as a directed diagram of languages -/
def henkin_language_chain {L : Language.{u}} : directed_diagram_language.{u} where
  obj := @henkin_language_chain_objects L
  mor := fun {x y} H => henkin_language_chain_maps L x y H
  h_mor := fun {x y z f1 f2 f3} =>
    henkin_language_chain_maps_functorial L x y z f1 f2 f3



lemma henkin_language_inclusion_chain_map {i : ℕ} {L : Language.{u}} :
    @henkin_language_inclusion (@henkin_language_chain_objects L i) =
    henkin_language_chain_maps L i (i + 1) (Nat.le_succ i) := by
  rw [hcm_succ_ne L i i (Nat.le_succ i) (Nat.ne_of_lt (Nat.lt_succ_self i))]
  rw [hcm_self L i (Nat.le_refl i)]
  rw [Lhom.id_is_right_identity]

/-! ## The limit language L_∞ -/

/-- The colimit of the Henkin language chain -/
def L_infty (L : Language.{u}) : Language.{u} :=
  colimit_language (@henkin_language_chain L)

/-- Canonical inclusion L_m → L_∞ -/
def henkin_language_canonical_map {L : Language.{u}} (m : ℕ) :
    (@henkin_language_chain L).obj m →ᴸ L_infty L :=
  canonical_map_language m

@[simp] lemma henkin_language_canonical_map_inj {L : Language.{u}} (m : ℕ) :
    Lhom.is_injective (@henkin_language_canonical_map L m) := by
  constructor
  · intro n
    simp only [henkin_language_canonical_map, canonical_map_language]
    apply canonical_map_inj_of_transition_maps_inj
    intro i j H
    exact (henkin_language_chain_maps_inj L i j H).on_function
  · intro n
    simp only [henkin_language_canonical_map, canonical_map_language]
    apply canonical_map_inj_of_transition_maps_inj
    intro i j H
    exact (henkin_language_chain_maps_inj L i j H).on_relation

/-! ## Directed diagrams of terms and formulas -/





/-- Chain of bounded preterms at bound n, level l -/
def henkin_bounded_term_chain {L : Language.{u}} (n l : ℕ) : directed_diagram ℕ' where
  obj k := bounded_preterm (@henkin_language_chain_objects L k) n l
  mor H := Lhom.on_bounded_term (henkin_language_chain_maps L _ _ H)
  h_mor := by
    intro x y z f1 f2 f3
    have hcomp := henkin_language_chain_maps_functorial L x y z f1 f2 f3
    rw [hcomp, Lhom.comp_on_bounded_term]



/-- Chain of bounded preformulas at bound n, level l -/
def henkin_bounded_formula_chain {L : Language.{u}} (n l : ℕ) : directed_diagram ℕ' where
  obj k := bounded_preformula (@henkin_language_chain_objects L k) n l
  mor H := Lhom.on_bounded_formula (henkin_language_chain_maps L _ _ H)
  h_mor := by
    intro x y z f1 f2 f3
    have hcomp := henkin_language_chain_maps_functorial L x y z f1 f2 f3
    rw [hcomp, Lhom.comp_on_bounded_formula]

@[reducible] def henkin_bounded_formula_chain' {L : Language.{u}} : directed_diagram ℕ' :=
  @henkin_bounded_formula_chain L 1 0

/-! ## Cocones with vertex L_∞ -/

/-- L_∞ is a cocone over the diagram of languages -/
def cocone_of_L_infty {L : Language.{u}} : cocone_language (@henkin_language_chain L) :=
  cocone_of_colimit_language _





/-- Cocone over the bounded term chain with vertex bounded_preterm (L_∞ L) n l -/
def cocone_of_bounded_term_L_infty {L : Language.{u}} (n l : ℕ) :
    cocone (@henkin_bounded_term_chain L n l) where
  vertex := bounded_preterm (L_infty L) n l
  map i := Lhom.on_bounded_term (henkin_language_canonical_map i)
  h_compat := by
    intro i j H
    have hc : henkin_language_canonical_map i =
        (henkin_language_canonical_map j).comp (henkin_language_chain_maps L i j H) :=
      (@cocone_of_L_infty L).h_compat H
    funext t
    simp only [Function.comp, henkin_bounded_term_chain]
    have := congr_arg (fun ϕ : @henkin_language_chain_objects L i →ᴸ L_infty L =>
        ϕ.on_bounded_term t) hc
    simpa [Lhom.comp] using this

/-! ## Cocone over the bounded formula chain (Task 16b, src/henkin.lean:452-499) -/

/-- Cocone over the bounded preformula chain with vertex bounded_preformula (L_∞ L) n l -/
def cocone_of_bounded_formula_L_infty {L : Language.{u}} (n l : ℕ) :
    cocone (@henkin_bounded_formula_chain L n l) where
  vertex := bounded_preformula (L_infty L) n l
  map i := Lhom.on_bounded_formula (henkin_language_canonical_map i)
  h_compat := by
    intro i j H
    have hc : henkin_language_canonical_map i =
        (henkin_language_canonical_map j).comp (henkin_language_chain_maps L i j H) :=
      (@cocone_of_L_infty L).h_compat H
    funext f
    simp only [Function.comp, henkin_bounded_formula_chain]
    have := congr_arg (fun ϕ : @henkin_language_chain_objects L i →ᴸ L_infty L =>
        ϕ.on_bounded_formula f) hc
    simpa [Lhom.comp] using this

/-- bounded_formula (L_∞ L) 1 is naturally a cocone over the diagram of bounded_formulas -/
def cocone_of_bounded_formula'_L_infty {L : Language.{u}} :
    cocone (@henkin_bounded_formula_chain' L) where
  vertex := bounded_formula (L_infty L) 1
  map i := Lhom.on_bounded_formula (henkin_language_canonical_map i)
  h_compat := by
    intro i j H
    have hc : henkin_language_canonical_map i =
        (henkin_language_canonical_map j).comp (henkin_language_chain_maps L i j H) :=
      (@cocone_of_L_infty L).h_compat H
    funext f
    simp only [Function.comp, henkin_bounded_formula_chain', henkin_bounded_formula_chain]
    have := congr_arg (fun ϕ : @henkin_language_chain_objects L i →ᴸ L_infty L =>
        ϕ.on_bounded_formula f) hc
    simpa [Lhom.comp] using this

/-! ## Comparison maps (universal maps from colimits to L_∞) -/





def bounded_term_comparison {L : Language.{u}} (n l) :
    colimit (@henkin_bounded_term_chain L n l) → bounded_preterm (L_infty L) n l :=
  universal_map (V := cocone_of_bounded_term_L_infty n l)



def bounded_formula_comparison {L : Language.{u}} (n l) :
    colimit (@henkin_bounded_formula_chain L n l) → bounded_preformula (L_infty L) n l :=
  universal_map (V := cocone_of_bounded_formula_L_infty n l)

@[reducible] def bounded_formula'_comparison {L : Language.{u}} :
    colimit (@henkin_bounded_formula_chain' L) → bounded_formula (L_infty L) 1 :=
  @bounded_formula_comparison L 1 0

/-! ## Bijectivity of comparison maps (src/henkin.lean:508-655) -/

-- These are complex structural induction arguments; sorried pending full port.









/-- Auxiliary: surjectivity of bounded_term_comparison by structural induction -/
 lemma bounded_term_comparison_surj {L : Language.{u}} :
    ∀ {n l} (t : bounded_preterm (L_infty L) n l),
    ∃ x : colimit (@henkin_bounded_term_chain L n l),
      bounded_term_comparison n l x = t := by
  intro n l t
  induction t with
  | bd_var k =>
      exact ⟨canonical_map 0 (bd_var k), by
        apply bounded_preterm.eq
        simp [bounded_term_comparison, universal_map_property, cocone_of_bounded_term_L_infty]⟩
  | bd_func ff =>
      obtain ⟨⟨i, x⟩, Hx⟩ := germ_rep ff
      exact ⟨canonical_map i (bd_func x), by
        apply bounded_preterm.eq
        simp only [bounded_term_comparison, universal_map_property, cocone_of_bounded_term_L_infty,
                   Lhom.on_bounded_term, bounded_preterm.fst]
        simp only [henkin_language_canonical_map, canonical_map_language]
        rw [← Hx]; rfl⟩
  | bd_app t s iht ihs =>
      obtain ⟨qt, Hqt⟩ := iht
      obtain ⟨qs, Hqs⟩ := ihs
      obtain ⟨⟨i, xt⟩, Hit⟩ := germ_rep qt
      obtain ⟨⟨j, xs⟩, Hjs⟩ := germ_rep qs
      -- Pre-compute back-tracking
      have Hbt : bounded_term_comparison _ _ (canonical_map i xt) = t := by
        have : canonical_map i xt = qt := Hit.symm ▸ rfl; rw [this]; exact Hqt
      have Hbs : bounded_term_comparison _ 0 (canonical_map j xs) = s := by
        have : canonical_map j xs = qs := Hjs.symm ▸ rfl; rw [this]; exact Hqs
      have keyt : bounded_term_comparison _ _ (canonical_map (i + j) (push_to_sum_r xt j)) = t := by
        rw [← same_fiber_as_push_to_r]; exact Hbt
      have keys : bounded_term_comparison _ 0 (canonical_map (i + j) (push_to_sum_l xs i)) = s := by
        rw [← same_fiber_as_push_to_l]; exact Hbs
      refine ⟨canonical_map (i + j) (bd_app (push_to_sum_r xt j) (push_to_sum_l xs i)), ?_⟩
      apply bounded_preterm.eq
      simp only [bounded_term_comparison, universal_map_property, cocone_of_bounded_term_L_infty,
                 Lhom.on_bounded_term, bounded_preterm.fst]
      congr 1
      · have h_eq := congrArg bounded_preterm.fst keyt
        simp only [bounded_term_comparison, universal_map_property, cocone_of_bounded_term_L_infty] at h_eq
        exact (Lhom.on_bounded_term_fst _ _) ▸ h_eq
      · have h_eq := congrArg bounded_preterm.fst keys
        simp only [bounded_term_comparison, universal_map_property, cocone_of_bounded_term_L_infty] at h_eq
        exact (Lhom.on_bounded_term_fst _ _) ▸ h_eq

@[simp] lemma bounded_term_comparison_bijective {L : Language.{u}} (n l) :
    Function.Bijective (@bounded_term_comparison L n l) :=
  ⟨universal_map_inj_of_components_inj (fun m => Lhom.on_bounded_term_inj (henkin_language_canonical_map_inj m)),
   bounded_term_comparison_surj⟩

/-- Auxiliary: surjectivity of bounded_formula_comparison by structural induction -/
 lemma bounded_formula_comparison_surj {L : Language.{u}} :
    ∀ {n l} (f : bounded_preformula (L_infty L) n l),
    ∃ x : colimit (@henkin_bounded_formula_chain L n l),
      bounded_formula_comparison n l x = f := by
  intro n l f
  induction f with
  | bd_falsum =>
      exact ⟨canonical_map 0 bd_falsum, by
        simp [bounded_formula_comparison, universal_map_property, cocone_of_bounded_formula_L_infty]⟩
  | bd_equal t₁ t₂ =>
      obtain ⟨qt₁, Hqt₁⟩ := bounded_term_comparison_bijective _ 0 |>.right t₁
      obtain ⟨qt₂, Hqt₂⟩ := bounded_term_comparison_bijective _ 0 |>.right t₂
      obtain ⟨⟨i, xt₁⟩, Hit₁⟩ := germ_rep qt₁
      obtain ⟨⟨j, xt₂⟩, Hit₂⟩ := germ_rep qt₂
      -- Pre-compute that bounded_term_comparison maps back correctly
      have Hbt₁ : bounded_term_comparison _ 0 (canonical_map i xt₁) = t₁ := by
        have : canonical_map i xt₁ = qt₁ := Hit₁.symm ▸ rfl
        rw [this]; exact Hqt₁
      have Hbt₂ : bounded_term_comparison _ 0 (canonical_map j xt₂) = t₂ := by
        have : canonical_map j xt₂ = qt₂ := Hit₂.symm ▸ rfl
        rw [this]; exact Hqt₂
      refine ⟨canonical_map (i + j) (bd_equal (push_to_sum_r xt₁ j) (push_to_sum_l xt₂ i)), ?_⟩
      -- bounded_formula_comparison (canonical_map (i+j) (bd_equal ...)) = bd_equal t₁ t₂
      -- Use the fact that bounded_term_comparison respects same-fiber
      have key₁ : bounded_term_comparison _ 0 (canonical_map (i + j) (push_to_sum_r xt₁ j)) = t₁ := by
        rw [← same_fiber_as_push_to_r]; exact Hbt₁
      have key₂ : bounded_term_comparison _ 0 (canonical_map (i + j) (push_to_sum_l xt₂ i)) = t₂ := by
        rw [← same_fiber_as_push_to_l]; exact Hbt₂
      apply bounded_preformula.eq
      simp only [bounded_formula_comparison, universal_map_property, cocone_of_bounded_formula_L_infty,
                 Lhom.on_bounded_formula, bounded_preformula.fst]
      -- Goal: preformula.equal (...).fst (...).fst = preformula.equal t₁.fst t₂.fst
      congr 1
      · -- (on_bounded_term (canonical_map (i+j)) (push_r xt₁ j)).fst = t₁.fst
        have h_eq := congrArg bounded_preterm.fst key₁
        simp only [bounded_term_comparison, universal_map_property, cocone_of_bounded_term_L_infty] at h_eq
        exact (Lhom.on_bounded_term_fst _ _) ▸ h_eq
      · have h_eq := congrArg bounded_preterm.fst key₂
        simp only [bounded_term_comparison, universal_map_property, cocone_of_bounded_term_L_infty] at h_eq
        exact (Lhom.on_bounded_term_fst _ _) ▸ h_eq
  | bd_rel R =>
      obtain ⟨⟨i, x⟩, Hx⟩ := germ_rep R
      exact ⟨canonical_map i (bd_rel x), by
        apply bounded_preformula.eq
        simp only [bounded_formula_comparison, universal_map_property, cocone_of_bounded_formula_L_infty,
                   Lhom.on_bounded_formula, bounded_preformula.fst, bd_rel]
        simp only [henkin_language_canonical_map, canonical_map_language]
        rw [← Hx]
        rfl⟩
  | bd_apprel f t ihf =>
      obtain ⟨qf, Hqf⟩ := ihf
      obtain ⟨qt, Hqt⟩ := bounded_term_comparison_bijective _ 0 |>.right t
      obtain ⟨⟨i, xf⟩, Hif⟩ := germ_rep qf
      obtain ⟨⟨j, xt⟩, Hjt⟩ := germ_rep qt
      -- Pre-compute back-tracking equalities
      have Hbf : bounded_formula_comparison _ _ (canonical_map i xf) = f := by
        have : canonical_map i xf = qf := Hif.symm ▸ rfl
        rw [this]; exact Hqf
      have Hbt : bounded_term_comparison _ 0 (canonical_map j xt) = t := by
        have : canonical_map j xt = qt := Hjt.symm ▸ rfl
        rw [this]; exact Hqt
      have keyf : bounded_formula_comparison _ _ (canonical_map (i + j) (push_to_sum_r xf j)) = f := by
        rw [← same_fiber_as_push_to_r]; exact Hbf
      have keyt : bounded_term_comparison _ 0 (canonical_map (i + j) (push_to_sum_l xt i)) = t := by
        rw [← same_fiber_as_push_to_l]; exact Hbt
      refine ⟨canonical_map (i + j) (bd_apprel (push_to_sum_r xf j) (push_to_sum_l xt i)), ?_⟩
      apply bounded_preformula.eq
      simp only [bounded_formula_comparison, universal_map_property, cocone_of_bounded_formula_L_infty,
                 Lhom.on_bounded_formula, bounded_preformula.fst]
      congr 1
      · have hf_eq := congrArg bounded_preformula.fst keyf
        simp only [bounded_formula_comparison, universal_map_property, cocone_of_bounded_formula_L_infty] at hf_eq
        exact (Lhom.on_bounded_formula_fst _ _) ▸ hf_eq
      · have ht_eq := congrArg bounded_preterm.fst keyt
        simp only [bounded_term_comparison, universal_map_property, cocone_of_bounded_term_L_infty] at ht_eq
        exact (Lhom.on_bounded_term_fst _ _) ▸ ht_eq
  | bd_imp f₁ f₂ ihf₁ ihf₂ =>
      obtain ⟨qf₁, Hqf₁⟩ := ihf₁
      obtain ⟨qf₂, Hqf₂⟩ := ihf₂
      obtain ⟨⟨i, xf₁⟩, Hif₁⟩ := germ_rep qf₁
      obtain ⟨⟨j, xf₂⟩, Hjf₂⟩ := germ_rep qf₂
      have Hbf₁ : bounded_formula_comparison _ _ (canonical_map i xf₁) = f₁ := by
        have : canonical_map i xf₁ = qf₁ := Hif₁.symm ▸ rfl; rw [this]; exact Hqf₁
      have Hbf₂ : bounded_formula_comparison _ _ (canonical_map j xf₂) = f₂ := by
        have : canonical_map j xf₂ = qf₂ := Hjf₂.symm ▸ rfl; rw [this]; exact Hqf₂
      have keyf₁ : bounded_formula_comparison _ _ (canonical_map (i + j) (push_to_sum_r xf₁ j)) = f₁ := by
        rw [← same_fiber_as_push_to_r]; exact Hbf₁
      have keyf₂ : bounded_formula_comparison _ _ (canonical_map (i + j) (push_to_sum_l xf₂ i)) = f₂ := by
        rw [← same_fiber_as_push_to_l]; exact Hbf₂
      refine ⟨canonical_map (i + j) (bd_imp (push_to_sum_r xf₁ j) (push_to_sum_l xf₂ i)), ?_⟩
      apply bounded_preformula.eq
      simp only [bounded_formula_comparison, universal_map_property, cocone_of_bounded_formula_L_infty,
                 Lhom.on_bounded_formula, bounded_preformula.fst]
      congr 1
      · have h_eq := congrArg bounded_preformula.fst keyf₁
        simp only [bounded_formula_comparison, universal_map_property, cocone_of_bounded_formula_L_infty] at h_eq
        exact (Lhom.on_bounded_formula_fst _ _) ▸ h_eq
      · have h_eq := congrArg bounded_preformula.fst keyf₂
        simp only [bounded_formula_comparison, universal_map_property, cocone_of_bounded_formula_L_infty] at h_eq
        exact (Lhom.on_bounded_formula_fst _ _) ▸ h_eq
  | bd_all f ihf =>
      obtain ⟨qf, Hqf⟩ := ihf
      obtain ⟨⟨i, xf⟩, Hif⟩ := germ_rep qf
      have Hbf : bounded_formula_comparison _ _ (canonical_map i xf) = f := by
        have : canonical_map i xf = qf := Hif.symm ▸ rfl; rw [this]; exact Hqf
      refine ⟨canonical_map i (bd_all xf), ?_⟩
      apply bounded_preformula.eq
      simp only [bounded_formula_comparison, universal_map_property, cocone_of_bounded_formula_L_infty,
                 Lhom.on_bounded_formula, bounded_preformula.fst]
      congr 1
      have h_eq := congrArg bounded_preformula.fst Hbf
      simp only [bounded_formula_comparison, universal_map_property, cocone_of_bounded_formula_L_infty] at h_eq
      exact (Lhom.on_bounded_formula_fst _ _) ▸ h_eq

@[simp] lemma bounded_formula_comparison_bijective {L : Language.{u}} (n l) :
    Function.Bijective (@bounded_formula_comparison L n l) :=
  ⟨universal_map_inj_of_components_inj (fun m => Lhom.on_bounded_formula_inj (henkin_language_canonical_map_inj m)),
   bounded_formula_comparison_surj⟩

@[simp] lemma bounded_formula'_comparison_bijective {L : Language.{u}} :
    Function.Bijective (@bounded_formula'_comparison L) :=
  bounded_formula_comparison_bijective 1 0



/-! ## Henkin theory chain (src/henkin.lean:661-734) -/

/-- The Henkin theory chain: T_n = Henkin^n step applied to T -/
def henkin_theory_chain {L : Language.{u}} (T : SentTheory L) :
    ∀ (n : ℕ), SentTheory ((@henkin_language_chain L).obj n)
  | 0 => T
  | n + 1 => henkin_theory_step (henkin_theory_chain T n)

lemma is_consistent_henkin_theory_chain {L : Language.{u}} {T : SentTheory L}
    (hT : T.is_consistent) (n : ℕ) : (henkin_theory_chain T n).is_consistent := by
  induction n with
  | zero => exact hT
  | succ n ih => exact is_consistent_henkin_theory_step ih

/-! ## has_enough_constants (from src/fol.lean:2482) -/

/-- A theory has enough constants if every bounded formula has a Henkin witness -/
def has_enough_constants {L : Language.{u}} (T : SentTheory L) : Prop :=
  ∃ (C : ∀ (f : bounded_formula L 1), L.constants),
    ∀ (f : bounded_formula L 1),
      T.fst ⊢' (wit_property f (C f)).fst

lemma has_enough_constants.intro {L : Language.{u}} (T : SentTheory L)
    (H : ∀ (f : bounded_formula L 1), ∃ c : L.constants,
      T.fst ⊢' (wit_property f c).fst) :
    has_enough_constants T :=
  Classical.axiom_of_choice H

/-! ## ι: pushing T_n into Theory L_∞ -/

/-- Given T_n from henkin_theory_chain, ι T_n is the expansion of T_n to an L_infty theory -/
def ι {L : Language.{u}} {T : SentTheory L} (m : ℕ) : SentTheory (L_infty L) :=
  Lhom.on_sentence (henkin_language_canonical_map m) '' (henkin_theory_chain T m)

@[simp] lemma in_iota_of_in_step {L : Language.{u}} (i : ℕ) {T : SentTheory L}
    (f : sentence ((@henkin_language_chain L).obj (i + 1))) :
    f ∈ (henkin_theory_chain T (i + 1)) →
    Lhom.on_bounded_formula (henkin_language_canonical_map (i + 1)) f ∈ @ι L T (i + 1) :=
  fun H => Set.mem_image_of_mem _ H

@[simp] lemma is_consistent_iota {L : Language.{u}} {T : SentTheory L}
    (hT : T.is_consistent) (m : ℕ) : (@ι L T m).is_consistent := by
  -- ι m = (henkin_language_canonical_map m).Theory_induced (henkin_theory_chain T m)
  -- and henkin_language_canonical_map m is injective, and henkin_theory_chain T m is consistent
  have hm := is_consistent_henkin_theory_chain hT m
  exact Lhom.is_consistent_Theory_induced (henkin_language_canonical_map_inj m) hm

/-! ## Monotonicity: ι is increasing (src/henkin.lean:736-751) -/

lemma henkin_theory_chain_inclusion_step {L : Language.{u}} {T : SentTheory L} {i : ℕ}
    {f : sentence ((@henkin_language_chain L).obj i)}
    (hf : f ∈ henkin_theory_chain T i) :
    Lhom.on_bounded_formula (henkin_language_chain_maps L i (i + 1) (Nat.le_succ i)) f ∈
    henkin_theory_chain T (i + 1) := by
  simp only [henkin_theory_chain, henkin_theory_step]
  apply Set.mem_union_left
  -- Lhom.Theory_induced = on_sentence '' ...
  -- henkin_language_chain_maps L i (i+1) = henkin_language_inclusion.comp ...
  -- so on_bounded_formula (hcm i (i+1)) f = on_sentence (hcm i (i+1)) f
  -- = on_sentence (henkin_language_inclusion ∘ hcm i i) f
  -- = henkin_language_inclusion.on_sentence (on_sentence (hcm i i) f)
  -- = henkin_language_inclusion.on_sentence f  (since hcm i i = id)
  rw [← henkin_language_inclusion_chain_map]
  exact Set.mem_image_of_mem _ hf

lemma iota_inclusion_of_le {L : Language.{u}} {T : SentTheory L} :
    ∀ {i j : ℕ}, i ≤ j → (@ι L T i) ⊆ (@ι L T j) := by
  intro i j h
  induction j with
  | zero =>
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero h
    subst hi0; exact le_refl _
  | succ n ih =>
    by_cases hx : i = n + 1
    · subst hx; exact le_refl _
    · have hle : i ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne h hx)
      intro ψ hψ
      -- first lift ψ to ι n
      have hψn : ψ ∈ @ι L T n := ih hle hψ
      obtain ⟨g, hgT, hgψ⟩ := hψn
      -- push g from stage n to stage n+1 in the theory chain
      have hg_step := henkin_theory_chain_inclusion_step hgT
      -- The witness in ι (n+1) is on_sentence (hcm (n+1)) (on_bf (hcm n (n+1)) g)
      -- By cocone compat: on_sentence (canonical_map n) = on_sentence (canonical_map (n+1)) ∘ on_bf (hcm n (n+1))
      refine ⟨Lhom.on_bounded_formula (henkin_language_chain_maps L n (n + 1) (Nat.le_succ n)) g,
              hg_step, ?_⟩
      -- on_sentence (canonical_map (n+1)) (on_bf (hcm n (n+1)) g)
      -- = on_bf ((canonical_map (n+1)).comp (hcm n (n+1))) g
      -- = on_bf (canonical_map n) g   [by cocone compat]
      -- = ψ
      have hc : henkin_language_canonical_map n =
          (henkin_language_canonical_map (n + 1)).comp (henkin_language_chain_maps L n (n + 1) (Nat.le_succ n)) :=
        (@cocone_of_L_infty L).h_compat (Nat.le_succ n)
      -- The goal is: (canonical_map (n+1)).on_sentence ((hcm n (n+1)).on_bounded_formula g) = ψ
      -- comp_on_bounded_formula: ((f.comp g).on_bounded_formula x) = f.on_bounded_formula (g.on_bounded_formula x)
      -- so lhs = ((canonical_map (n+1)).comp (hcm n (n+1))).on_bounded_formula g = (canonical_map n).on_bounded_formula g = ψ
      have key : (henkin_language_canonical_map (n + 1)).on_bounded_formula
          ((henkin_language_chain_maps L n (n + 1) (Nat.le_succ n)).on_bounded_formula g) =
          (henkin_language_canonical_map n).on_bounded_formula g := by
        -- comp_on_bounded_formula: (f.comp g).on_bf x = f.on_bf (g.on_bf x)
        -- hc: canonical_map n = (canonical_map (n+1)).comp (hcm n (n+1))
        -- so (canonical_map n).on_bf g = ((canonical_map (n+1)).comp (hcm n (n+1))).on_bf g
        --    = (canonical_map (n+1)).on_bf ((hcm n (n+1)).on_bf g)
        calc (henkin_language_canonical_map (n + 1)).on_bounded_formula
                 ((henkin_language_chain_maps L n (n + 1) (Nat.le_succ n)).on_bounded_formula g)
            = ((henkin_language_canonical_map (n + 1)).comp
                (henkin_language_chain_maps L n (n + 1) (Nat.le_succ n))).on_bounded_formula g :=
              (congr_fun (Lhom.comp_on_bounded_formula _ _) g).symm
          _ = (henkin_language_canonical_map n).on_bounded_formula g :=
              congr_arg (fun ϕ : _ →ᴸ _ => ϕ.on_bounded_formula g) hc.symm
      simp only [Lhom.on_sentence] at hgψ ⊢
      rw [key]
      exact hgψ

/-! ## T_infty: the henkinization (src/henkin.lean:753-774) -/

/-- T_infty is the henkinization of T; we define it to be the union ⋃ (n : ℕ), ι(T n). -/
@[reducible] def T_infty {L : Language.{u}} (T : SentTheory L) : SentTheory (L_infty L) :=
  ⋃ n : ℕ, @ι L T n

@[reducible] def henkin_language {L : Language.{u}} {T : SentTheory L}
    {_hT : T.is_consistent} : Language.{u} := L_infty L





@[reducible] def henkinization {L : Language.{u}} {T : SentTheory L}
    (hT : T.is_consistent) : SentTheory (@henkin_language L T hT) := T_infty T

/-! ## wit_infty: find a Henkin witness in henkinization (src/henkin.lean:778-783) -/

noncomputable def wit_infty {L : Language.{u}} {T : SentTheory L} {hT : T.is_consistent}
    (f : bounded_formula (@henkin_language L T hT) 1) :
    Σ c : (@henkin_language L T hT).constants,
      Σ (f' : Σ' (x : colimit (@henkin_bounded_formula_chain' L)),
          bounded_formula'_comparison x = f),
        Σ' (f'' : coproduct_of_directed_diagram (@henkin_bounded_formula_chain' L)),
          ⟦f''⟧ = f'.fst ∧
          c = (henkin_language_canonical_map (f''.1 + 1)).on_function (wit' f''.2) := by
  have f_lift1 := Classical.psigma_of_exists (bounded_formula'_comparison_bijective.right f)
  have f_lift2 := germ_rep f_lift1.fst
  exact ⟨(henkin_language_canonical_map (f_lift2.fst.1 + 1)).on_function (wit' f_lift2.fst.2),
         f_lift1, f_lift2.fst, f_lift2.snd, rfl⟩

/-! ## henkinization has enough constants (src/henkin.lean:785-831) -/

-- Helper: on_bounded_formula commutes with subst0_bounded_formula
 lemma on_bounded_formula_subst0 {L L' : Language.{u}} (ϕ : L →ᴸ L')
    {n l} (f : bounded_preformula L (n + 1) l) (s : bounded_term L n) :
    ϕ.on_bounded_formula (subst0_bounded_formula f s) =
    subst0_bounded_formula (ϕ.on_bounded_formula f) (ϕ.on_bounded_term s) := by
  apply bounded_preformula.eq
  simp only [subst0_bounded_formula_fst, Lhom.on_bounded_formula_fst,
             Lhom.on_bounded_term_fst, Lhom.on_formula_subst]

@[simp] lemma henkinization_is_henkin {L : Language.{u}} {T : SentTheory L}
    (hT : T.is_consistent) : has_enough_constants (henkinization hT) := by
  apply has_enough_constants.intro
  intro f
  have big_sigma := wit_infty (hT := hT) f
  obtain ⟨c, ⟨f', Hf'⟩, ⟨i, f''⟩, Heq, Hc⟩ := big_sigma
  -- The witnessing sentence at stage i+1
  let wp_step : sentence ((@henkin_language_chain L).obj (i + 1)) :=
    wit_property (henkin_language_inclusion.on_bounded_formula f'') (wit' f'')
  -- wp_step ∈ henkin_theory_chain T (i+1) = henkin_theory_step (henkin_theory_chain T i)
  have hwp_step : wp_step ∈ henkin_theory_chain T (i + 1) := by
    simp only [henkin_theory_chain, henkin_theory_step, Set.mem_image, Set.mem_univ]
    right
    exact ⟨f'', Set.mem_univ _, rfl⟩
  -- (hcm (i+1)).on_bounded_formula wp_step ∈ ι (i+1)
  have hwp_iota : (henkin_language_canonical_map (i + 1)).on_bounded_formula wp_step ∈
      @ι L T (i + 1) := in_iota_of_in_step i wp_step hwp_step
  -- Key: (hcm i).on_bounded_formula f'' = f
  -- This uses bounded_formula'_comparison ⟦⟨i, f''⟩⟧ = (cocone_of_bounded_formula'_L_infty).map i f''
  -- = (hcm i).on_bounded_formula f''
  have hf_eq : (henkin_language_canonical_map i).on_bounded_formula f'' = f := by
    have : (henkin_language_canonical_map i).on_bounded_formula f'' =
        bounded_formula'_comparison (canonical_map i f'') := by
      simp only [bounded_formula'_comparison, bounded_formula_comparison,
                 universal_map_property, cocone_of_bounded_formula_L_infty]
    simp only [canonical_map] at this
    rw [this, show (Quotient.mk _ ⟨i, f''⟩ : colimit _) = f' from Heq, Hf']
  -- Key: (hcm (i+1)).on_bf (inclusion.on_bf f'') = f
  -- via cocone_of_bounded_formula'_L_infty.h_compat at i ≤ i+1:
  -- (hcm i).on_bf = (hcm (i+1)).on_bf ∘ incl.on_bf
  have hinc_eq : (henkin_language_canonical_map (i + 1)).on_bounded_formula
      (henkin_language_inclusion.on_bounded_formula f'') = f := by
    -- Use cocone_of_bounded_formula'_L_infty.h_compat to get the key equality
    have hcompat := (@cocone_of_bounded_formula'_L_infty L).h_compat (Nat.le_succ i)
    -- hcompat : (hcm i).on_bf = (hcm (i+1)).on_bf ∘ (chain_maps i (i+1)).on_bf
    have hc_bf := congr_fun hcompat f''
    simp only [Function.comp, henkin_bounded_formula_chain', henkin_bounded_formula_chain,
               cocone_of_bounded_formula'_L_infty, cocone_of_bounded_formula_L_infty] at hc_bf
    -- hc_bf : (hcm i).on_bf f'' = (hcm (i+1)).on_bf ((chain_maps i (i+1)).on_bf f'')
    rw [← henkin_language_inclusion_chain_map] at hc_bf
    -- hc_bf : (hcm i).on_bf f'' = (hcm (i+1)).on_bf (incl.on_bf f'')
    rw [← hc_bf, hf_eq]
  -- Key: (hcm (i+1)).on_bounded_formula wp_step = wit_property f c
  have heq : (henkin_language_canonical_map (i + 1)).on_bounded_formula wp_step =
      wit_property f c := by
    simp only [wp_step, wit_property, Lhom.on_bounded_formula]
    congr 1
    · -- bd_ex (incl.on_bf f'') maps to bd_ex f
      simp only [bd_ex, bd_not, Lhom.on_bounded_formula]
      exact congrArg (fun g => bd_imp (bd_all (bd_imp g bd_falsum)) bd_falsum) hinc_eq
    · -- subst0 (incl.on_bf f'') (bd_const (wit' f'')) maps to subst0 f (bd_const c)
      rw [on_bounded_formula_subst0, hinc_eq]
      congr 1
      simp only [bd_const, Lhom.on_bounded_term]
      exact congrArg bounded_preterm.bd_func Hc.symm
  -- wit_property f c ∈ henkinization hT = ⋃ n, ι T n
  have hmem : wit_property f c ∈ henkinization hT := by
    simp only [henkinization, T_infty, Set.mem_iUnion]
    exact ⟨i + 1, heq ▸ hwp_iota⟩
  exact ⟨c, saxm' hmem⟩

/-! ## Directed union infrastructure (src/henkin.lean:833-874) -/



def henkin_theory_schain {L : Language.{u}} (T : SentTheory L) (hT : T.is_consistent) :
    Set (Theory_over (@ι L T 0) (is_consistent_iota hT 0)) :=
  { T' | ∃ k : ℕ, @ι L T k = T'.val }

lemma iota_union_rw {L : Language.{u}} (T : SentTheory L) (hT : T.is_consistent) :
    @ι L T 0 ∪ ⋃₀ (Subtype.val '' henkin_theory_schain T hT) = henkinization hT := by
  -- henkinization hT = T_infty T = ⋃ n, ι n
  -- LHS = ι 0 ∪ (⋃ { ι k | k : ℕ })  = ⋃ n, ι n
  apply Set.eq_of_subset_of_subset
  · -- LHS ⊆ henkinization
    apply Set.union_subset
    · exact Set.subset_iUnion (@ι L T) 0
    · intro ψ hψ
      obtain ⟨S, hS, hψS⟩ := hψ
      obtain ⟨To, hTo, hSTo⟩ := hS
      -- hTo : To ∈ henkin_theory_schain T hT
      simp only [henkin_theory_schain, Set.mem_setOf_eq] at hTo
      obtain ⟨k, hk⟩ := hTo
      -- hk : ι k = To.val, hSTo : To.val = S
      simp only [henkinization, T_infty, Set.mem_iUnion]
      exact ⟨k, hk ▸ hSTo ▸ hψS⟩
  · -- henkinization ⊆ LHS
    intro ψ hψ
    simp only [henkinization, T_infty, Set.mem_iUnion] at hψ
    obtain ⟨k, hk⟩ := hψ
    cases k with
    | zero => exact Set.mem_union_left _ hk
    | succ n =>
      apply Set.mem_union_right
      refine ⟨@ι L T (n + 1), ?_, hk⟩
      -- Need: ι (n+1) ∈ Subtype.val '' henkin_theory_schain T hT
      -- i.e., ∃ To ∈ henkin_theory_schain T hT, To.val = ι (n+1)
      let To : Theory_over (@ι L T 0) (is_consistent_iota hT 0) :=
        ⟨@ι L T (n + 1), iota_inclusion_of_le (Nat.zero_le _), is_consistent_iota hT _⟩
      refine ⟨To, ?_, rfl⟩
      simp only [henkin_theory_schain, Set.mem_setOf_eq]
      exact ⟨n + 1, rfl⟩

lemma chain_henkin_theory_chain {L : Language.{u}} (T : SentTheory L) (hT : T.is_consistent) :
    IsChain Theory_over_subset (henkin_theory_schain T hT) := by
  intro T₁ hT₁ T₂ hT₂ hne
  simp only [henkin_theory_schain, Set.mem_setOf_eq] at hT₁ hT₂
  obtain ⟨i, hi⟩ := hT₁; obtain ⟨j, hj⟩ := hT₂
  by_cases h : i ≤ j
  · left
    -- T₁.val = ι i ⊆ ι j = T₂.val
    intro f hf
    rw [← hj]
    exact iota_inclusion_of_le h (hi ▸ hf)
  · right
    -- T₂.val = ι j ⊆ ι i = T₁.val
    intro f hf
    rw [← hi]
    exact iota_inclusion_of_le (Nat.le_of_lt (Nat.lt_of_not_le h)) (hj ▸ hf)

lemma is_consistent_henkinization {L : Language.{u}} {T : SentTheory L} (hT : T.is_consistent) :
    (henkinization hT).is_consistent := by
  have key := @consis_limit _ _ _ (henkin_theory_schain T hT)
  rw [iota_union_rw] at key
  exact key (chain_henkin_theory_chain T hT)

/-! ## Completion of henkinization (src/henkin.lean:891-911) -/

/-- The core completion: henkinization extends to a complete consistent theory -/
noncomputable def completion_of_henkinization_core {L : Language.{u}} {T : SentTheory L}
    (hT : T.is_consistent) :
    Σ' (T' : Theory_over (henkinization hT) (is_consistent_henkinization hT)),
        T'.val.is_complete :=
  completion_of_consis (henkinization hT) (is_consistent_henkinization hT)

/-- The completed henkinization theory -/
noncomputable def completion_of_henkinization {L : Language.{u}} {T : SentTheory L}
    (hT : T.is_consistent) : SentTheory (@henkin_language L T hT) :=
  (completion_of_henkinization_core hT).fst.val

/-- The completed theory contains the henkinization -/
lemma completion_of_henkinization_contains {L : Language.{u}} {T : SentTheory L}
    (hT : T.is_consistent) : henkinization hT ⊆ completion_of_henkinization hT :=
  (completion_of_henkinization_core hT).fst.property.left



/-- The completed theory is complete -/
def completion_of_henkinization_complete {L : Language.{u}} {T : SentTheory L}
    (hT : T.is_consistent) : (completion_of_henkinization hT).is_complete :=
  (completion_of_henkinization_core hT).snd

/-- The completed theory is Henkin -/
@[simp] lemma completion_of_henkinization_is_henkin {L : Language.{u}} {T : SentTheory L}
    (hT : T.is_consistent) : has_enough_constants (completion_of_henkinization hT) := by
  apply has_enough_constants.intro
  intro f
  obtain ⟨C, HC⟩ := henkinization_is_henkin hT
  refine ⟨C f, ?_⟩
  apply weakening' (Γ := (henkinization hT).fst)
  · exact Set.image_mono (completion_of_henkinization_contains hT)
  · exact HC f

/-! ## Helpers for the term model (ported from src/fol.lean:2445-2498) -/



/-- If T is complete and T ⊬ₛ' f, then T ⊢ₛ' bd_not f -/
lemma notI_of_is_complete {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.is_complete) {f : sentence L} (hf : ¬T ⊢ₛ' f) : T ⊢ₛ' bd_not f := by
  rcases hcomp.2 f with h | h
  · exact absurd ⟨prf.axm (Set.mem_image_of_mem _ h)⟩ hf
  · exact ⟨prf.axm (Set.mem_image_of_mem _ h)⟩

/-- If T is complete, T ⊢ₛ' (bd_imp φ ψ) follows from (T ⊢ₛ' φ → T ⊢ₛ' ψ) -/
lemma impI_of_is_complete {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.is_complete) {φ ψ : sentence L}
    (h : SentTheory.sprovable T φ → SentTheory.sprovable T ψ) :
    SentTheory.sprovable T (bd_imp φ ψ) := by
  simp only [SentTheory.sprovable, SentTheory.fst, bounded_preformula.fst]
  rcases hcomp.2 φ with h₁ | h₁
  · -- φ ∈ T
    exact impI' (weakening1' (h ⟨prf.axm (Set.mem_image_of_mem _ h₁)⟩))
  · -- bd_not φ ∈ T (h₁ : bd_not φ ∈ T)
    apply impI'
    apply falsumE'
    apply weakening1'
    -- need: insert φ.fst T.fst ⊢' ⊥'
    -- h₁ : bd_not φ ∈ T  →  (φ.fst ⟹ ⊥') ∈ T.fst  →  ∈ insert φ.fst T.fst
    have hmem : bounded_preformula.fst φ ⟹ ⊥' ∈ bounded_preformula.fst '' T :=
      Set.mem_image_of_mem _ h₁
    exact impE' _ ⟨prf.axm (Set.mem_insert_of_mem _ hmem)⟩ ⟨axm1⟩

/-- Given a complete Henkin theory, universal failure yields a counterexample -/
lemma find_counterexample_of_henkin {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.is_complete) (henk : has_enough_constants T)
    (f : bounded_formula L 1) (hf : ¬T ⊢ₛ' bd_all f) :
    ∃ t : closed_term L, T ⊢ₛ' bd_not (subst0_bounded_formula f t) := by
  obtain ⟨C, hC⟩ := henk
  refine ⟨bd_const (C (bd_not f)), ?_⟩
  have hwit : T.fst ⊢' (wit_property (bd_not f) (C (bd_not f))).fst := hC (bd_not f)
  -- hwit : T.fst ⊢' (bd_ex (bd_not f)).fst ⟹ (bd_not f)[c/0].fst
  -- We need T.fst ⊢' (bd_not (subst0_bounded_formula f (bd_const (C (bd_not f))))).fst
  -- Strategy: use ex_not_of_not_all to get ∃'(∼f), then apply hwit
  -- Get ∼(∀'f) as a prf and apply ex_not_of_not_all:
  have hnotall_prf : T.fst ⊢ ∼(∀' f.fst) := (notI_of_is_complete hcomp hf).some
  -- ex_not_of_not_all gives ∃'(∼f.fst) = (bd_ex (bd_not f)).fst
  have hex : T.fst ⊢' (bd_ex (bd_not f)).fst :=
    ⟨ex_not_of_not_all hnotall_prf⟩
  -- Apply hwit: T.fst ⊢' (bd_ex (bd_not f)).fst ⟹ (bd_not (subst0_bf f c)).fst
  -- Result: T.fst ⊢' (bd_not (subst0_bf f c)).fst = (subst0_bf f c).fst ⟹ ⊥'
  -- which equals T.fst ⊢ₛ' bd_not (subst0_bf f (bd_const (C (bd_not f))))
  simp only [SentTheory.sprovable, SentTheory.fst]
  simp only [wit_property, bounded_preformula.fst, bd_imp, bd_not] at hwit
  -- hwit : T.fst ⊢' (bd_ex (bd_not f)).fst ⟹ (subst0_bounded_formula (bd_not f) c).fst
  -- (subst0_bounded_formula (bd_not f) c).fst = (bd_not (subst0_bounded_formula f c)).fst
  -- Goal: T.fst ⊢' (bd_not (subst0_bounded_formula f (bd_const (C (bd_not f))))).fst
  exact impE' _ hwit hex

/-! ## Term model construction (src/fol.lean:2500-2559) -/

/-- The term equality relation: t₁ ~ t₂ iff T ⊢ₛ' t₁ ≃ t₂ -/
def term_rel {L : Language.{u}} (T : SentTheory L) (t₁ t₂ : closed_term L) : Prop :=
  T ⊢ₛ' bd_equal t₁ t₂

/-- The term equality setoid -/
noncomputable def term_setoid {L : Language.{u}} (T : SentTheory L) : Setoid (closed_term L) :=
  { r := term_rel T
    iseqv := {
      refl := fun t => ⟨prf.ref T.fst t.fst⟩
      symm := fun h => h.map prf_symm
      trans := fun h₁ h₂ => h₁.map2 prf_trans h₂
    }
  }

/-- The carrier of the term model: closed terms modulo provable equality -/
noncomputable def term_model' {L : Language.{u}} (T : SentTheory L) : Type u :=
  @Quotient (closed_term L) (term_setoid T)

/-- The function interpretation helper for the term model -/
noncomputable def term_model_fun' {L : Language.{u}} (T : SentTheory L)
    {l} (t : closed_preterm L l) (ts : DVec (closed_term L) l) : term_model' T :=
  @Quotient.mk'' _ (term_setoid T) (bd_apps t ts)

/-- Core congr: given equal_preterms and DVecRel, bd_apps preserves term_rel -/
 lemma bd_apps_congr_equal_preterms {L : Language.{u}} {T : SentTheory L}
    {l} {t t' : closed_preterm L l}
    (Ht : equal_preterms T.fst t.fst t'.fst) :
    ∀ {xs xs' : DVec (closed_term L) l},
    @DVec.DVecRel _ (term_setoid T) _ xs xs' →
    term_rel T (bd_apps t xs) (bd_apps t' xs') := by
  intro xs xs' hxs
  induction hxs with
  | rnil =>
    simp only [term_rel, SentTheory.sprovable, SentTheory.fst, bd_apps]
    exact ⟨Ht DVec.nil⟩
  | rcons hx hxs ih =>
    -- hx : term_rel T x x' = T ⊢ₛ' bd_equal x x'
    -- hxs : DVecRel xs xs'
    -- ih is: equal_preterms T.fst (bd_app t x).fst (bd_app t' x').fst → ...
    -- No, ih is the claim for bd_app t x, bd_app t' x', hxs
    simp only [term_rel, SentTheory.sprovable, SentTheory.fst, bd_apps] at *
    -- Need: T.fst ⊢' bd_apps (bd_app t x) xs ≃ bd_apps (bd_app t' x') xs'
    -- But ih gives us: for (bd_app t x) and (bd_app t' x') vs xs and xs'
    -- Ht' : equal_preterms T.fst (bd_app t x).fst (bd_app t' x').fst follows from Ht and hx
    exact ih (equal_preterms_app Ht hx.some)

/-- Helper: term_model_fun' is compatible with term_rel on each argument -/
 lemma term_model_fun'_congr {L : Language.{u}} {T : SentTheory L}
    {l} (t : closed_preterm L l) :
    ∀ {xs xs' : DVec (closed_term L) l},
    @DVec.DVecRel _ (term_setoid T) _ xs xs' →
    term_model_fun' T t xs = term_model_fun' T t xs' := by
  intro xs xs' hxs
  simp only [term_model_fun']
  apply Quotient.sound
  show term_rel T _ _
  exact bd_apps_congr_equal_preterms (equal_preterms_refl T.fst t.fst) hxs

/-- The function interpretation in the term model, using quotient_lift -/
noncomputable def term_model_fun {L : Language.{u}} (T : SentTheory L)
    {l} (t : closed_preterm L l) (ts : DVec (term_model' T) l) : term_model' T :=
  @DVec.quotient_lift _ _ (term_setoid T) _ (term_model_fun' T t)
    (term_model_fun'_congr t) ts

/-- The relation interpretation helper -/
noncomputable def term_model_rel' {L : Language.{u}} (T : SentTheory L)
    {l} (f : presentence L l) (ts : DVec (closed_term L) l) : Prop :=
  T ⊢ₛ' bd_apps_rel f ts

/-- Core congr: given equiv_preformulae and DVecRel, bd_apps_rel preserves provability -/
 lemma bd_apps_rel_congr_equiv {L : Language.{u}} {T : SentTheory L}
    {l} {f f' : presentence L l}
    (Hf : equiv_preformulae T.fst f.fst f'.fst) :
    ∀ {xs xs' : DVec (closed_term L) l},
    @DVec.DVecRel _ (term_setoid T) _ xs xs' →
    (T ⊢ₛ' bd_apps_rel f xs) = (T ⊢ₛ' bd_apps_rel f' xs') := by
  intro xs xs' hxs
  induction hxs with
  | rnil =>
    simp only [bd_apps_rel, SentTheory.sprovable, SentTheory.fst]
    exact propext (iff_of_biimp ⟨Hf DVec.nil⟩)
  | rcons hx hxs ih =>
    simp only [bd_apps_rel]
    exact ih (equiv_preformulae_apprel Hf hx.some)

/-- Helper: term_model_rel' is compatible with term_rel on each argument -/
 lemma term_model_rel'_congr {L : Language.{u}} {T : SentTheory L}
    {l} (f : presentence L l) :
    ∀ {xs xs' : DVec (closed_term L) l},
    @DVec.DVecRel _ (term_setoid T) _ xs xs' →
    term_model_rel' T f xs = term_model_rel' T f xs' := by
  intro xs xs' hxs
  simp only [term_model_rel']
  exact bd_apps_rel_congr_equiv (equiv_preformulae_refl T.fst f.fst) hxs

/-- The relation interpretation in the term model -/
noncomputable def term_model_rel {L : Language.{u}} (T : SentTheory L)
    {l} (f : presentence L l) (ts : DVec (term_model' T) l) : Prop :=
  @DVec.quotient_lift _ _ (term_setoid T) _ (term_model_rel' T f)
    (term_model_rel'_congr f) ts

/-! ## Term model and main completeness theorem -/

/-- term_model of a complete Henkin theory (src/fol.lean:2559-2562) -/
noncomputable def term_model {L : Language.{u}} {T : SentTheory L}
    (_hcomp : T.is_complete) (_henk : has_enough_constants T) : Structure L :=
  { carrier := term_model' T
    fun_map := fun {_n} f ts => term_model_fun T (bd_func f) ts
    rel_map := fun {_n} R ts => term_model_rel T (bd_rel R) ts }

/-- Canonical quotient map from closed terms to the term model -/
@[reducible] noncomputable def term_mk {L : Language.{u}} (T : SentTheory L)
    (t : closed_term L) : term_model' T :=
  @Quotient.mk'' _ (term_setoid T) t

/-! ### Realization in the term model (src/fol.lean:2568-2627) -/

/-- Realizing a closed preterm in the term model recovers `bd_apps`. -/
 lemma realize_closed_preterm_term_model {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.is_complete) (henk : has_enough_constants T) :
    ∀ {l} (ts : DVec (closed_term L) l) (t : closed_preterm L l),
    realize_bounded_term (DVec.nil : DVec (term_model hcomp henk) 0) t
      (ts.map (term_mk T)) =
    term_mk T (bd_apps t ts) := by
  intro l ts t
  induction t with
  | bd_var k => exact absurd k.2 (Nat.not_lt_zero k.1)
  | bd_func f =>
    -- realize_bounded_term [] (bd_func f) (ts.map term_mk) = (term_model).fun_map f (ts.map term_mk)
    --   = term_model_fun T (bd_func f) (ts.map term_mk)
    --   = term_model_fun' T (bd_func f) ts (by quotient_beta) = ⟦bd_apps (bd_func f) ts⟧ = term_mk ...
    show term_model_fun T (bd_func f) (ts.map (term_mk T)) = term_mk T (bd_apps (bd_func f) ts)
    simp only [term_model_fun]
    rw [show (ts.map (term_mk T)) = DVec.map Quotient.mk'' ts from rfl]
    rw [DVec.quotient_beta]
    rfl
  | bd_app t₁ t₂ ih₁ ih₂ =>
    -- bd_app t₁ t₂ has type closed_preterm L l, t₁ has level (l+1), t₂ has level 0
    rw [realize_bounded_term_bd_app]
    -- Goal: realize_bounded_term [] t₁ (rbt t₂ DVec.nil :: ts.map term_mk)
    --     = term_mk T (bd_apps (bd_app t₁ t₂) ts)
    have h2 : realize_bounded_term (DVec.nil : DVec (term_model hcomp henk) 0) t₂ DVec.nil
              = term_mk T t₂ := by
      have := ih₂ DVec.nil
      simp only [DVec.map, bd_apps] at this
      exact this
    rw [h2]
    -- Goal: realize_bounded_term [] t₁ (term_mk T t₂ :: ts.map term_mk)
    --     = term_mk T (bd_apps (bd_app t₁ t₂) ts)
    -- which equals  term_mk T (bd_apps t₁ (t₂ :: ts))
    have h1 := ih₁ (DVec.cons t₂ ts)
    simp only [DVec.map, bd_apps] at h1
    exact h1

/-- Realizing a closed term in the term model is the canonical quotient map. -/
@[simp]  lemma realize_closed_term_term_model {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.is_complete) (henk : has_enough_constants T) (t : closed_term L) :
    realize_closed_term (term_model hcomp henk) t = term_mk T t := by
  have := realize_closed_preterm_term_model hcomp henk (DVec.nil : DVec (closed_term L) 0) t
  simp only [DVec.map, bd_apps] at this
  exact this





/-- Substitution commutes with realization for formulas. -/
 lemma realize_subst_formula {L : Language.{u}} (S : Structure L) {n}
    (f : bounded_formula L (n+1)) (t : closed_term L) (v : DVec S n) :
    realize_bounded_formula v (substmax_bounded_formula f t) DVec.nil ↔
    realize_bounded_formula (v.concat (realize_closed_term S t)) f DVec.nil := by
  set y := realize_closed_term S t with hy_def
  -- Choose a base extension for `v`:
  let φ : ℕ → S := fun k => if h : k < n then v.nth k h else y
  -- LHS via realize_bounded_formula_iff
  rw [realize_bounded_formula_iff (v₁ := v) (v₂ := φ)
        (fun k hk => by simp [φ, hk]) (substmax_bounded_formula f t) DVec.nil]
  -- RHS via realize_bounded_formula_iff with extension subst_realize φ y n
  rw [realize_bounded_formula_iff (v₁ := v.concat y) (v₂ := subst_realize φ y n)
        (fun k hk => by
          by_cases hkn : k < n
          · rw [DVec.concat_nth v _ k hk hkn]
            have hnek : k ≠ n := Nat.ne_of_lt hkn
            have hnotlt : ¬ n < k := Nat.not_lt.mpr (Nat.le_of_lt hkn)
            simp only [subst_realize, if_true, hnotlt, if_false, φ, hkn, dif_pos]
          · have hkeq : k = n := Nat.le_antisymm (Nat.lt_succ_iff.mp hk) (Nat.le_of_not_lt hkn)
            subst hkeq
            simp [DVec.concat_nth_last]) f DVec.nil]
  -- Formula side
  simp only [substmax_bounded_formula_fst]
  -- realize_formula_subst gives:
  --   realize_formula (subst_realize φ (realize_term φ (lift_term t.fst n) []) n) f.fst []
  --     ↔ realize_formula φ (subst_formula f.fst t.fst n) []
  -- We need: realize_formula (subst_realize φ y n) f.fst [] ↔ realize_formula φ (subst_formula ...) []
  have hreal_t : realize_term φ (lift_term t.fst n) DVec.nil = y := by
    rw [hy_def]
    rw [show realize_closed_term S t = realize_bounded_term (DVec.nil : DVec S 0) t DVec.nil from rfl]
    -- realize_term φ (lift_term t.fst n) [] = realize_term φ t.fst []
    --   (since closed terms ignore the valuation, lifting is irrelevant)
    -- = realize_bounded_term [] t []
    have hlift : realize_term φ (lift_term t.fst n) DVec.nil = realize_term φ t.fst DVec.nil := by
      have hfst_eq : (lift_term t.fst n) = t.fst := lift_bounded_term_irrel t n (Nat.zero_le _)
      rw [hfst_eq]
    rw [hlift]
    exact (realize_bounded_term_eq (v₁ := (DVec.nil : DVec S 0)) (v₂ := φ)
      (fun k hk => absurd hk (Nat.not_lt_zero k)) t DVec.nil).symm
  rw [← hreal_t]
  exact (realize_formula_subst φ n f.fst t.fst DVec.nil).symm

/-- Substitution at position 0 commutes with realization. -/
 lemma realize_subst_formula0 {L : Language.{u}} (S : Structure L)
    (f : bounded_formula L 1) (t : closed_term L) :
    realize_sentence S (subst0_bounded_formula f t) ↔
    realize_bounded_formula (DVec.cons (realize_closed_term S t) DVec.nil) f DVec.nil := by
  rw [show subst0_bounded_formula f t = substmax_bounded_formula f t from
      substmax_eq_subst0_formula f t]
  -- realize_sentence S g = realize_bounded_formula DVec.nil g DVec.nil
  -- and (DVec.nil).concat (realize_closed_term S t) = DVec.cons (...) DVec.nil
  show realize_bounded_formula (DVec.nil : DVec S 0) (substmax_bounded_formula f t) DVec.nil ↔ _
  rw [realize_subst_formula S f t DVec.nil]
  -- (DVec.nil).concat y = DVec.cons y DVec.nil
  rfl

/-- Substituting in the term model: relate to realization at the quotient class. -/
 lemma term_model_subst0 {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.is_complete) (henk : has_enough_constants T)
    (f : bounded_formula L 1) (t : closed_term L) :
    realize_sentence (term_model hcomp henk) (subst0_bounded_formula f t) ↔
    realize_bounded_formula
      (DVec.cons (term_mk T t : (term_model hcomp henk).carrier)
        (DVec.nil : DVec (term_model hcomp henk).carrier 0)) f DVec.nil := by
  rw [realize_subst_formula0 (term_model hcomp henk) f t]
  rw [realize_closed_term_term_model hcomp henk t]



/-- Structural recursion on a `bounded_preformula L 0 l` for the term-model iff,
    parameterized by an external IH on smaller quantifier-counts.

    Implemented via direct structural pattern matching on `f` to avoid issues
    with `induction` on a non-variable index `n = 0`. -/
 noncomputable def term_model_ssatisfied_iff_struct
    {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.is_complete) (henk : has_enough_constants T)
    (n : ℕ)
    (n_ih : ∀ m, m < n → ∀ {l'} (f' : presentence L l') (ts' : DVec (closed_term L) l'),
        count_quantifiers f'.fst < m →
        ((T ⊢ₛ' bd_apps_rel f' ts') ↔
         realize_sentence (term_model hcomp henk) (bd_apps_rel f' ts'))) :
    ∀ {l} (f : bounded_preformula L 0 l) (ts : DVec (closed_term L) l),
      count_quantifiers f.fst < n →
      ((T ⊢ₛ' bd_apps_rel f ts) ↔
       realize_sentence (term_model hcomp henk) (bd_apps_rel f ts))
  | _, bd_falsum, ts, _ => by
      cases ts
      simp only [bd_apps_rel]
      refine ⟨fun h => absurd h hcomp.1, fun h => ?_⟩
      exfalso; exact h
  | _, bd_equal t₁ t₂, ts, _ => by
      cases ts
      simp only [bd_apps_rel]
      rw [show realize_sentence (term_model hcomp henk) (bd_equal t₁ t₂) ↔
              realize_closed_term (term_model hcomp henk) t₁ =
              realize_closed_term (term_model hcomp henk) t₂ from realize_sentence_equal t₁ t₂]
      rw [realize_closed_term_term_model hcomp henk t₁,
          realize_closed_term_term_model hcomp henk t₂]
      refine ⟨fun h => Quotient.sound (show term_rel T t₁ t₂ from h), fun h => ?_⟩
      exact (Quotient.exact h : term_rel T t₁ t₂)
  | _, bd_rel R, ts, _ => by
      rw [realize_bd_apps_rel R ts]
      show _ ↔ (term_model hcomp henk).rel_map R
                (ts.map (realize_closed_term (term_model hcomp henk)))
      have h_eq : ts.map (realize_closed_term (term_model hcomp henk)) = ts.map (term_mk T) := by
        apply DVec.map_congr
        intro x
        exact realize_closed_term_term_model hcomp henk x
      rw [h_eq]
      show _ ↔ term_model_rel T (bd_rel R) (ts.map (term_mk T))
      simp only [term_model_rel]
      rw [show (ts.map (term_mk T)) = DVec.map Quotient.mk'' ts from rfl]
      rw [DVec.quotient_beta]
      rfl
  | _, bd_apprel f t, ts, hn => by
      have heq : bd_apps_rel (bd_apprel f t) ts = bd_apps_rel f (DVec.cons t ts) := rfl
      rw [heq]
      have hn' : count_quantifiers f.fst < n := by
        rw [count_quantifiers_succ]
        simp only [bounded_preformula.fst, count_quantifiers] at hn
        exact hn
      exact term_model_ssatisfied_iff_struct hcomp henk n n_ih f (DVec.cons t ts) hn'
  | _, bd_imp f₁ f₂, ts, hn => by
      cases ts
      simp only [bd_apps_rel]
      have hn1 : count_quantifiers f₁.fst < n := by
        simp only [bounded_preformula.fst, count_quantifiers] at hn
        exact lt_of_le_of_lt (Nat.le_add_right _ _) hn
      have hn2 : count_quantifiers f₂.fst < n := by
        simp only [bounded_preformula.fst, count_quantifiers] at hn
        exact lt_of_le_of_lt (Nat.le_add_left _ _) hn
      have ih1 := term_model_ssatisfied_iff_struct hcomp henk n n_ih f₁ DVec.nil hn1
      have ih2 := term_model_ssatisfied_iff_struct hcomp henk n n_ih f₂ DVec.nil hn2
      simp only [bd_apps_rel] at ih1 ih2
      rw [show realize_sentence (term_model hcomp henk) (bd_imp f₁ f₂) ↔
              (realize_sentence (term_model hcomp henk) f₁ →
               realize_sentence (term_model hcomp henk) f₂) from realize_sentence_imp]
      refine ⟨fun hp h1 => ?_, fun hsem => ?_⟩
      · apply ih2.mp
        have hp1 : T ⊢ₛ' f₁ := ih1.mpr h1
        exact hp.map2 (prf.impE _) hp1
      · apply impI_of_is_complete hcomp
        intro hf1
        exact ih2.mpr (hsem (ih1.mp hf1))
  | _, bd_all f, ts, hn => by
      cases ts
      simp only [bd_apps_rel]
      rw [show realize_sentence (term_model hcomp henk) (bd_all f) ↔
              ∀ x : (term_model hcomp henk).carrier,
                realize_bounded_formula (DVec.cons x DVec.nil) f DVec.nil
          from realize_sentence_all]
      have hm : count_quantifiers f.fst + 1 < n := by
        simp only [bounded_preformula.fst, count_quantifiers] at hn
        omega
      refine ⟨fun hp x => ?_, fun hsem => ?_⟩
      · induction x using Quotient.ind with
        | _ t =>
        apply (term_model_subst0 hcomp henk f t).mp
        have h := (n_ih (count_quantifiers f.fst + 1) hm
                    (l' := 0) (subst0_bounded_formula f t) DVec.nil ?_).mp ?_
        · simp only [bd_apps_rel] at h
          exact h
        · rw [subst0_bounded_formula_fst]
          rw [count_quantifiers_subst]
          exact Nat.lt_succ_self _
        · simp only [bd_apps_rel]
          refine hp.map (fun pall => ?_)
          rw [subst0_bounded_formula_fst]
          exact prf.allE₂ f.fst t.fst pall
      · by_contra H
        obtain ⟨t, ht⟩ := find_counterexample_of_henkin hcomp henk f H
        have hsem_t := hsem (term_mk T t)
        have hsubst : realize_sentence (term_model hcomp henk) (subst0_bounded_formula f t) :=
          (term_model_subst0 hcomp henk f t).mpr hsem_t
        have h := (n_ih (count_quantifiers f.fst + 1) hm
                    (l' := 0) (subst0_bounded_formula f t) DVec.nil ?_).mpr ?_
        · simp only [bd_apps_rel] at h
          apply hcomp.1
          exact ht.map2 (fun pn p => prf.impE _ pn p) h
        · rw [subst0_bounded_formula_fst]
          rw [count_quantifiers_subst]
          exact Nat.lt_succ_self _
        · simp only [bd_apps_rel]
          exact hsubst

/-- The key term-model satisfaction iff (src/fol.lean:2634-2670). -/
 lemma term_model_ssatisfied_iff {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.is_complete) (henk : has_enough_constants T) {n} :
    ∀ {l} (f : presentence L l) (ts : DVec (closed_term L) l)
      (_ : count_quantifiers f.fst < n),
      ((T ⊢ₛ' bd_apps_rel f ts) ↔
       realize_sentence (term_model hcomp henk) (bd_apps_rel f ts)) := by
  induction n using Nat.strong_induction_on with
  | _ n n_ih =>
  intro l f ts hn
  exact term_model_ssatisfied_iff_struct hcomp henk n n_ih f ts hn

/-- The term model satisfies T (src/fol.lean:2672) -/
lemma term_model_ssatisfied {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.is_complete) (henk : has_enough_constants T) :
    all_realize_sentence (term_model hcomp henk) T := by
  intro f hf
  have hprov : T ⊢ₛ' bd_apps_rel f (DVec.nil : DVec (closed_term L) 0) := by
    simp only [bd_apps_rel]
    exact ⟨prf.axm (Set.mem_image_of_mem _ hf)⟩
  have h := (term_model_ssatisfied_iff hcomp henk (n := count_quantifiers f.fst + 1)
              f DVec.nil (Nat.lt_succ_self _)).mp hprov
  simp only [bd_apps_rel] at h
  exact h

/-- The reduct of the term model of the complete henkinization satisfies T -/
@[simp] lemma reduct_of_complete_henkinization_models_T {L : Language.{u}} {T : SentTheory L}
    (hT : T.is_consistent) :
    Lhom.reduct (@henkin_language_canonical_map L 0)
      (term_model (completion_of_henkinization_complete hT)
                  (completion_of_henkinization_is_henkin hT)) ⊨ₜ T := by
  apply Lhom.reduct_all_ssatisfied (henkin_language_canonical_map_inj 0)
  -- Goal: all_realize_sentence (term_model ...) ((hcm 0).on_sentence '' T)
  intro f hf
  -- hf : f ∈ (hcm 0).on_sentence '' T
  obtain ⟨f₀, hf₀, rfl⟩ := hf
  apply term_model_ssatisfied
  apply completion_of_henkinization_contains hT
  simp only [henkinization, T_infty]
  exact Set.mem_iUnion.mpr ⟨0, Set.mem_image_of_mem _ hf₀⟩

/-- Given ψ ∈ T, the term model satisfies ψ -/
@[simp] lemma reduct_of_complete_henkinization_satisfies {L : Language.{u}} {T : SentTheory L}
    (hT : T.is_consistent) (ψ : sentence L) (hψ : ψ ∈ T) :
    Lhom.reduct (@henkin_language_canonical_map L 0)
      (term_model (completion_of_henkinization_complete hT)
                  (completion_of_henkinization_is_henkin hT)) ⊨ₘ ψ :=
  reduct_of_complete_henkinization_models_T hT hψ

end Fol


end CohenSource_Henkin


/- Source module: Definitions.Flypitch4.Forcing -/
section CohenSource_Forcing
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/forcing.lean (567 lines) — Task 18 -/





set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Compatibility with the source port's Mathlib revision.
 abbrev Finset.toSet {α : Type*} (s : Finset α) : Set α := (s : Set α)

open scoped Cardinal
open Flypitch Flypitch.Regular

universe u

namespace bSet

-- ============================================================
-- src/forcing.lean:34-103: section cardinal_preservation
-- ============================================================

section cardinal_preservation

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/forcing.lean:36-48


-- src/forcing.lean:50-56


-- src/forcing.lean:58-62


-- src/forcing.lean:63-100: not_CCC_of_uncountable_fiber
variable
  (η₁ η₂ : PSet.{u}) (H_infinite : Cardinal.aleph0 ≤ #(η₁.Type))
  (H_lt : #(η₁.Type) < #(η₂.Type))
  (H_inj₂ : ∀ x y, x ≠ y → ¬ PSet.Equiv (η₂.Func x) (η₂.Func y))
  (f : bSet 𝔹) (g : η₂.Type → η₁.Type)
  (H : ∀ β : η₂.Type, (⊥ : 𝔹) < is_func f ⊓ pair (check (η₁.Func (g β))) (check (η₂.Func β)) ∈ᴮ f)



end cardinal_preservation

end bSet

open bSet

-- ============================================================
-- src/forcing.lean:107-121: namespace PSet
-- ============================================================

namespace PSet

-- src/forcing.lean:109: ℵ₁ (as PSet)


-- src/forcing.lean:111: ℵ₂ (as PSet)
@[reducible] noncomputable def pSet_aleph2 : PSet.{0} := ordinalMk (Cardinal.aleph 2).ord

-- src/forcing.lean:113


-- src/forcing.lean:115-120: Union lemmas (not needed for the main result)

end PSet

open PSet

-- ============================================================
-- src/forcing.lean:125-133: 𝔹_cohen and instances
-- ============================================================

/-- The Cohen boolean algebra: regular opens on Set(PSet.pSet_aleph2.Type × ℕ) -/
noncomputable def 𝔹_cohen : Type :=
  @Flypitch.RegularOpens (Set (PSet.pSet_aleph2.Type × ℕ)) inferInstance

local notation "𝔹" => 𝔹_cohen

instance H_nonempty : Nonempty (Set (PSet.pSet_aleph2.Type × ℕ)) := ⟨∅⟩

noncomputable instance 𝔹_boolean_algebra :
    NontrivialCompleteBooleanAlgebra 𝔹 :=
  @Flypitch.RegularOpens.instNontrivialCBA _ _ H_nonempty

-- src/forcing.lean:134


-- src/forcing.lean:136


-- Type equality lemmas for cast operations
-- These hold because check x has .type = x.Type by the definition of check
 lemma eq₀ : (check (PSet.pSet_aleph2) : bSet 𝔹).type = PSet.pSet_aleph2.Type :=
  check_type'

 lemma eq₁ :
    ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ) = (PSet.pSet_aleph2.Type × ℕ) :=
  congr_arg (· × ℕ) eq₀

 lemma eq₂ :
    Set ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ) = Set (PSet.pSet_aleph2.Type × ℕ) :=
  congr_arg Set eq₁

 lemma eq₃ :
    Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ) = Finset (PSet.pSet_aleph2.Type × ℕ) :=
  congr_arg Finset eq₁

-- src/forcing.lean:149-176: cast helper lemmas










-- src/forcing.lean:178-179


local notation "𝒳" => Set (PSet.pSet_aleph2.Type × ℕ)

-- src/forcing.lean:187-191
/-- The principal regular open associated to a pair (ν, n) -/
noncomputable def principal_open (ν : (check (PSet.pSet_aleph2) : bSet 𝔹).type) (n : ℕ) : 𝔹 :=
  ⟨CantorSpace.principalOpen (cast eq₁ (ν, n)),
   isRegularOpen_of_isClopen CantorSpace.isClopen_principalOpen⟩



-- src/forcing.lean:202-203


-- src/forcing.lean:205-209


-- src/forcing.lean:211-214: structure 𝒞
structure 𝒞 : Type where
  ins : Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ)
  out : Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ)
  H : ins ∩ out = ∅

-- src/forcing.lean:216
@[reducible] def π₂ : (check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ → ℕ := fun x => x.2

-- src/forcing.lean:223-245: ι definition
 noncomputable def ι : 𝒞 → 𝔹 :=
  fun p => ⟨{S | (p.ins.toSet) ⊆ (cast eq₂.symm S) ∧
                  (p.out.toSet) ⊆ (cast eq₂.symm Sᶜ)},
    isRegularOpen_of_isClopen (by
      -- Cast membership: x ∈ cast eq₂.symm S ↔ cast eq₁ x ∈ S
      have cast_mem_iff : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T2) (x : T1),
          x ∈ cast (congr_arg Set h).symm T ↔ cast h x ∈ T := by
        intro T1 T2 h; subst h; intro T x; simp
      -- The set equals principalOpenFinset (cast eq₃ p.ins) ∩ coPrincipalOpenFinset (cast eq₃ p.out)
      have hset : {S : Set (PSet.pSet_aleph2.Type × ℕ) |
                    p.ins.toSet ⊆ cast eq₂.symm S ∧ p.out.toSet ⊆ cast eq₂.symm Sᶜ} =
                  CantorSpace.principalOpenFinset (cast eq₃ p.ins) ∩
                  CantorSpace.coPrincipalOpenFinset (cast eq₃ p.out) := by
        ext S
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, CantorSpace.mem_principalOpenFinset_iff,
          CantorSpace.coPrincipalOpenFinset, Set.mem_setOf_eq]
        -- LHS: ∀ x ∈ p.ins.toSet, cast eq₁ x ∈ S  and  ∀ x ∈ p.out.toSet, cast eq₁ x ∉ S
        -- RHS: (cast eq₃ p.ins).toSet ⊆ S  and  (cast eq₃ p.out).toSet ⊆ Sᶜ
        -- Key: use cast_mem_iff directly to relate membership
        -- For x ∈ cast eq₃ F ↔ cast eq₁.symm x ∈ F, we use:
        -- eq₃ = congr_arg Finset eq₁, so cast eq₃ F = cast (congr_arg Finset eq₁) F
        -- and x ∈ cast (congr_arg Finset h) F ↔ cast h.symm x ∈ F (by subst h)
        have cast_finset_mem : ∀ (F : Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ))
            (x : PSet.pSet_aleph2.Type × ℕ),
            x ∈ (cast eq₃ F : Finset (PSet.pSet_aleph2.Type × ℕ)) ↔ cast eq₁.symm x ∈ F := by
          intro F x
          -- cast eq₃ F : Finset B. Membership: x ∈ cast eq₃ F ↔ eq₁.symm cast x ∈ F
          -- Use: cast eq₃ = Equiv.cast of the Finset type equality
          -- Since eq₃ = congr_arg Finset eq₁, cast eq₃ maps Finset A → Finset B
          -- and is the image map: cast eq₃ F = F.image (cast eq₁)
          -- So x ∈ cast eq₃ F ↔ cast eq₁.symm x ∈ F (bijective)
          have key : ∀ {A B : Type} (h : A = B) (F : Finset A) (x : B),
              x ∈ cast (congr_arg Finset h) F ↔ cast h.symm x ∈ F := by
            intro A B h; subst h; intro F x; simp
          have heq : eq₃ = congr_arg Finset eq₁ := rfl
          rw [heq]; exact key eq₁ F x
        constructor
        · intro ⟨h₁, h₂⟩
          constructor
          · -- S ∈ principalOpenFinset (cast eq₃ p.ins): ∀ x ∈ cast eq₃ p.ins, x ∈ S
            intro x hx
            rw [Finset.mem_coe, cast_finset_mem] at hx
            -- hx : cast eq₁.symm x ∈ p.ins
            have hmem := (cast_mem_iff eq₁ S (cast eq₁.symm x)).mp (h₁ (Finset.mem_coe.mpr hx))
            -- hmem : cast eq₁ (cast eq₁.symm x) ∈ S; reduce to x ∈ S
            have hx_eq : cast eq₁ (cast eq₁.symm x) = x := by
              rw [cast_eq_iff_heq]; exact cast_heq eq₁.symm x
            rw [hx_eq] at hmem; exact hmem
          · intro x hx
            rw [Finset.mem_coe, cast_finset_mem] at hx
            have hmem := (cast_mem_iff eq₁ Sᶜ (cast eq₁.symm x)).mp (h₂ (Finset.mem_coe.mpr hx))
            have hx_eq : cast eq₁ (cast eq₁.symm x) = x := by
              rw [cast_eq_iff_heq]; exact cast_heq eq₁.symm x
            rw [hx_eq] at hmem; exact hmem
        · intro ⟨h₁, h₂⟩
          constructor
          · intro y hy
            rw [cast_mem_iff eq₁]
            apply h₁
            rw [Finset.mem_coe, cast_finset_mem]
            -- Goal: cast eq₁.symm (cast eq₁ y) ∈ p.ins; reduce to y ∈ p.ins
            have hcast : cast eq₁.symm (cast eq₁ y) = y := by
              rw [cast_eq_iff_heq]; exact cast_heq eq₁ y
            rw [hcast]; exact hy
          · intro y hy
            rw [cast_mem_iff eq₁]
            apply h₂
            rw [Finset.mem_coe, cast_finset_mem]
            have hcast : cast eq₁.symm (cast eq₁ y) = y := by
              rw [cast_eq_iff_heq]; exact cast_heq eq₁ y
            rw [hcast]; exact hy
      rw [hset]
      exact (CantorSpace.isClopen_principalOpenFinset _).inter
        (CantorSpace.isClopen_coPrincipalOpenFinset _))⟩

open CantorSpace

-- src/forcing.lean:249-250


-- src/forcing.lean:252-272: 𝒞_dense_basis


-- src/forcing.lean:274-284: 𝒞_dense


-- src/forcing.lean:286-288


-- src/forcing.lean:292-299


-- src/forcing.lean:301-303


-- src/forcing.lean:305-319: 𝒞_nonzero


-- src/forcing.lean:323-350: 𝒞_disjoint_row


-- src/forcing.lean:352-353


-- ============================================================
-- src/forcing.lean:355-441: namespace cohen_real (inside namespace bSet)
-- ============================================================

namespace bSet

namespace cohen_real

/-- `cohen_real.χ ν` is the indicator function on ℕ -/
noncomputable def χ (ν : (check (PSet.pSet_aleph2) : bSet 𝔹).type) : ℕ → 𝔹 :=
  fun n => principal_open ν n

/-- `cohen_real.mk ν` is the subset of (ω : bSet 𝔹) -/
noncomputable def mk (ν : (check (PSet.pSet_aleph2) : bSet 𝔹).type) : bSet 𝔹 :=
  @set_of_indicator 𝔹 _ omega (fun n => χ ν n.down)

@[simp] lemma mk_type {ν} : (mk ν).type = ULift ℕ := rfl

@[simp] lemma mk_func {ν} {n} : (mk ν).func n = of_nat (n.down) := rfl

@[simp] lemma mk_bval {ν} {n} : (mk ν).bval n = (χ ν) (n.down) := rfl





-- src/forcing.lean:379-386


-- src/forcing.lean:388-398


-- src/forcing.lean:400-406




end cohen_real

-- ============================================================
-- src/forcing.lean:443-567: section neg_CH
-- ============================================================

section neg_CH
-- (still inside namespace bSet)

local notation "ℵ₀" => (omega : bSet 𝔹)
local notation "𝔠" => (bv_powerset ℵ₀ : bSet 𝔹)

-- src/forcing.lean:450-457


-- src/forcing.lean:459-466


-- src/forcing.lean:468-487


-- src/forcing.lean:489-504


-- src/forcing.lean:507-509




-- src/forcing.lean:513-529: cohen_real.mk_ext
lemma cohen_real.mk_ext : ∀ (i j : (check (PSet.pSet_aleph2) : bSet 𝔹).type),
    (check (PSet.pSet_aleph2) : bSet 𝔹).func i =ᴮ (check (PSet.pSet_aleph2) : bSet 𝔹).func j ≤
      (fun x : (check (PSet.pSet_aleph2) : bSet 𝔹).type => cohen_real.mk x) i =ᴮ
      (fun x : (check (PSet.pSet_aleph2) : bSet 𝔹).type => cohen_real.mk x) j := by
  intro i j; by_cases h : i = j
  · simp [h]
  · apply poset_yoneda; intro Γ a
    rw [check_func, check_func] at a
    suffices h_bot : (check (PSet.pSet_aleph2.Func (check_cast i)) : bSet 𝔹) =ᴮ
        check (PSet.pSet_aleph2.Func (check_cast j)) ≤ ⊥ by
      exact le_trans a (le_trans h_bot bot_le)
    rw [le_bot_iff]
    apply check_bv_eq_bot_of_not_equiv
    -- pSet_aleph2 = ordinalMk (aleph 2).ord
    -- pSet_aleph2.Func (check_cast i) ≠ pSet_aleph2.Func (check_cast j) when i ≠ j
    apply PSet.ordinalMk_inj (Cardinal.aleph 2).ord
    intro H; exact h (by simp [check_cast] at H ⊢; exact H)

-- src/forcing.lean:531-532
noncomputable def neg_CH_func : bSet 𝔹 :=
  @functionMk _ _ (check PSet.pSet_aleph2) (fun x => cohen_real.mk x) cohen_real.mk_ext

-- src/forcing.lean:534-546


-- src/forcing.lean:548-550




-- src/forcing.lean:552-562


-- src/forcing.lean:564-565


end neg_CH

end bSet


end CohenSource_Forcing


