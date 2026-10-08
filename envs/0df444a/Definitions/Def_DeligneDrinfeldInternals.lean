-- Prove2me | Definitions.Def_DeligneDrinfeldInternals
-- name    : DeligneDrinfeldInternals
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-07T18:32:17.478986+00:00
-- url     : https://prove2.me/theorems/00d730a9-5878-4890-90ed-a5b66837bf8d
-- title:
--   OpenAI's Deligne–Drinfeld proof — internal definitions I (associative models, mod-2 degeneration, leading projections, integral families, KZ transport)
-- statement:
--   The definitions needed to state the intermediate lemmas of OpenAI's proof of the Deligne–Drinfeld conjecture (*The Deligne–Drinfeld conjecture*, OpenAI Math Release, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), [paper](https://github.com/openai/math/blob/main/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf)). They are taken from OpenAI's Lean development `lean/OAI/Algebra/Drinfeld` (Apache License 2.0), with comments removed and line-level edits for this platform's Lean and Mathlib, keep OpenAI's names, and import the published bundle `DeligneDrinfeld`. Each declaration is included because a published statement uses it, directly or through another definition; the lemmas in the bundle are those the definitions need (proof fields, well-definedness) and simp lemmas about them. The main groups, in the paper's order:
--
--   1. **Associative models (§2).** The free associative algebra on an alphabet as a monoid algebra of the free monoid (`AssociativeElimination.A`), the embedding of the free Lie algebra with the commutator bracket (`AssociativeElimination.embed`), word gradings, homogeneous and filtered pieces (`WordGrading`, `LieGrading`), and Lie gradings with chosen homogeneous components (`LieGrading.piece`).
--   2. **The mod-2 degeneration of the pentagon (§3).** The slot alphabet $A, C, B$ (`RowTwo.Slot`) with the substitution $A \mapsto x^2$, $C \mapsto [x, y]$, $B \mapsto y$ (`QuadraticLeading.under`), the mod-2 forms of the defining equations (`BaseChangeEquations.antisymmetry`, `special`, `pentagon`), the five-term pentagon map and the source model (`ExactPentagon`, `SourceModel`), and the normal-ordering maps $S$, $C$, $T$ of the count comparison (`ExactCountOrdering`, `CountTables`, `SecondStage`).
--   3. **Deletion operators and leading projections (§§4–5).** The four rows of deletion coefficients and the row equation (`DeletionTable`, `RowKernel.Equation`), the letter retraction $A \mapsto 0$ (`LetterRetraction.lie`), the leading part at count $r$ and the generators $(\mathrm{ad}\,x)^{k+1}y$ (`ImageBound.leading`, `ImageBound.positiveInput`).
--   4. **Integral families (§8).** Ihara evaluation of free Lie words (`GenericIhara.evalIhara`), families of values $V \subseteq W$ closed under the Ihara bracket and their odd values (`IntegralFamily.Values`, `OddValues`), and normalized families of mod-2 generators (`NormalizedFamily.Data`).
--   5. **Real KZ transport (§7).** Nilpotent filtrations of finite-dimensional normed algebras (`FinitePicard.NilpotentFiltration`), truncated Picard series and the regularized KZ associator (`KZCollar.associator`), the truncated free algebras (`CutoffDepth.Q`, `TruncatedWords`), and OpenAI's real-coefficient versions of the comparator objects (`RealDeligneDrinfeld.L`, `eval`, `T4`, `t`).
-- source:
--   OpenAI, The Deligne–Drinfeld conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf, Sections 2-8 (associative models, the mod-2 degeneration of the pentagon, deletion operators and leading projections, integral families, real KZ transport); Lean: https://github.com/openai/math/tree/main/lean/OAI/Algebra/Drinfeld (Apache-2.0)

import Mathlib
import Definitions.Def_DeligneDrinfeld

/-!
# OpenAI's proof of the Deligne–Drinfeld conjecture: internal definitions

OpenAI, *The Deligne–Drinfeld conjecture*, OpenAI Math Release, September 23, 2026,
https://github.com/openai/math (paper:
`preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf`).

The definitions, structures and instances below, with the lemmas they need, are taken from
OpenAI's Lean development `lean/OAI/Algebra/Drinfeld` in that repository (Apache License,
Version 2.0), with comments removed and line-level edits for this Lean and Mathlib version.
They are the declarations needed to state the published intermediate lemmas of that proof.
-/

universe u v

section

namespace OAI

noncomputable section
namespace DeligneDrinfeld

theorem freeLie_induction {R α : Type*} [CommRing R]
    {P : FreeLieAlgebra R α → Prop} (h0 : P 0)
    (hg : ∀ a, P (FreeLieAlgebra.of R a))
    (ha : ∀ a b, P a → P b → P (a+b))
    (hs : ∀ (r : R) a, P a → P (r • a))
    (hl : ∀ a b, P a → P b → P ⁅a,b⁆) (q : FreeLieAlgebra R α) : P q := by
  let K : LieSubalgebra R (FreeLieAlgebra R α) :=
    { carrier := {a | P a}
      zero_mem' := h0
      add_mem' := fun ha' hb' => ha _ _ ha' hb'
      smul_mem' := fun r a h => hs r a h
      lie_mem' := fun ha' hb' => hl _ _ ha' hb' }
  let f : FreeLieAlgebra R α →ₗ⁅R⁆ K :=
    FreeLieAlgebra.lift R (fun a => ⟨FreeLieAlgebra.of R a, hg a⟩)
  have hf : K.incl.comp f = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [f]
  have h := (f q).property
  change P ((K.incl.comp f) q) at h
  simpa only [hf, LieHom.id_apply] using h

@[ext] theorem Tangent.ext {a b : Tangent} (h : a.base = b.base)
    (k : a.velocity = b.velocity) : a = b := by cases a; cases b; simp_all

@[simp] theorem Tangent.base_zero : (0 : Tangent).base = 0 := rfl
@[simp] theorem Tangent.velocity_zero : (0 : Tangent).velocity = 0 := rfl
@[simp] theorem Tangent.base_add (a b : Tangent) : (a+b).base = a.base+b.base := rfl
@[simp] theorem Tangent.velocity_add (a b : Tangent) :
    (a+b).velocity = a.velocity+b.velocity := rfl
@[simp] theorem Tangent.base_smul (q : ℚ) (a : Tangent) : (q • a).base = q • a.base := rfl
@[simp] theorem Tangent.velocity_smul (q : ℚ) (a : Tangent) :
    (q • a).velocity = q • a.velocity := rfl
@[simp] theorem Tangent.base_lie (a b : Tangent) : ⁅a,b⁆.base = ⁅a.base,b.base⁆ := rfl
@[simp] theorem Tangent.velocity_lie (a b : Tangent) :
    ⁅a,b⁆.velocity = ⁅a.velocity,b.base⁆ + ⁅a.base,b.velocity⁆ := rfl

@[simp] theorem eval_x {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) :
    eval a b x = a := by simp [eval, x]
@[simp] theorem eval_y {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) :
    eval a b y = b := by simp [eval, y]

def Tangent.baseHom : Tangent →ₗ⁅ℚ⁆ L where
  toFun := Tangent.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

@[simp] theorem tangentLift_base (p q : L) : (tangentLift p q).base = q := by
  have h : Tangent.baseHom.comp (tangentLift p) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [tangentLift, Tangent.baseHom, x, y] <;> rfl
  exact LieHom.congr_fun h q

@[simp] theorem D_x (p : L) : D p x = 0 := by simp [D, tangentLift, x]
@[simp] theorem D_y (p : L) : D p y = ⁅y,p⁆ := by simp [D, tangentLift, y]
@[simp] theorem D_zero (p : L) : D p 0 = 0 := by simp [D]
@[simp] theorem D_add (p q r : L) : D p (q+r) = D p q + D p r := by simp [D]
@[simp] theorem D_smul (p q : L) (a : ℚ) : D p (a • q) = a • D p q := by simp [D]
theorem D_lie (p q r : L) : D p ⁅q,r⁆ = ⁅D p q,r⁆ + ⁅q,D p r⁆ := by
  simp [D, LieHom.map_lie]

def derivation (p : L) : LieDerivation ℚ L L where
  toFun := D p
  map_add' := D_add p
  map_smul' a q := D_smul p q a
  leibniz' a b := by
    change D p ⁅a,b⁆ = ⁅a,D p b⁆ - ⁅b,D p a⁆
    rw [D_lie, sub_eq_add_neg, lie_skew, add_comm]

@[simp] theorem derivation_apply (p q : L) : derivation p q = D p q := rfl

theorem derivation_ext {d₁ d₂ : LieDerivation ℚ L L}
    (hx : d₁ x = d₂ x) (hy : d₁ y = d₂ y) : d₁ = d₂ := by
  ext q
  induction q using freeLie_induction with
  | h0 => simp
  | hg i => cases i; exact hx; exact hy
  | ha a b ha hb => simp [ha, hb]
  | hs r a ha => simp [ha]
  | hl a b ha hb => simp [ha, hb]

@[simp] theorem D_zero_left (q : L) : D 0 q = 0 := by
  have h : derivation 0 = 0 := by
    apply derivation_ext <;> simp
  exact LieDerivation.congr_fun h q

@[simp] theorem D_add_left (p q r : L) : D (p+q) r = D p r + D q r := by
  have h : derivation (p+q) = derivation p + derivation q := by
    apply derivation_ext <;> simp [lie_add]
  exact LieDerivation.congr_fun h r

@[simp] theorem D_smul_left (p q : L) (a : ℚ) : D (a • p) q = a • D p q := by
  have h : derivation (a • p) = a • derivation p := by
    apply derivation_ext <;> simp
  exact LieDerivation.congr_fun h q

namespace AssociativeModel

variable {α : Type*}
abbrev A (α : Type*) := MonoidAlgebra ℚ (FreeMonoid α)
attribute [local instance] LieRing.ofAssociativeRing

end AssociativeModel

namespace FreeDerivations

variable {R : Type*} [CommRing R]
variable {M : Type*} [LieRing M] [LieAlgebra R M]

structure Jet (R M : Type*) [CommRing R] [LieRing M] [LieAlgebra R M] where
  base : M
  velocity : M

def Jet.equiv : Jet R M ≃ M × M where
  toFun z := (z.base, z.velocity)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (Jet R M) := Jet.equiv.addCommGroup
instance : Module R (Jet R M) := Jet.equiv.addEquiv.module R
instance : Bracket (Jet R M) (Jet R M) :=
  ⟨fun a b => ⟨⁅a.base, b.base⁆,
    ⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆⟩⟩

@[ext] theorem Jet.ext {a b : Jet R M} (h : a.base = b.base)
    (k : a.velocity = b.velocity) : a = b := by cases a; cases b; simp_all

@[simp] theorem Jet.base_zero : (0 : Jet R M).base = 0 := rfl
@[simp] theorem Jet.velocity_zero : (0 : Jet R M).velocity = 0 := rfl
@[simp] theorem Jet.base_add (a b : Jet R M) : (a+b).base = a.base+b.base := rfl
@[simp] theorem Jet.velocity_add (a b : Jet R M) :
    (a+b).velocity = a.velocity+b.velocity := rfl
@[simp] theorem Jet.base_smul (q : R) (a : Jet R M) : (q • a).base = q • a.base := rfl
@[simp] theorem Jet.velocity_smul (q : R) (a : Jet R M) :
    (q • a).velocity = q • a.velocity := rfl
@[simp] theorem Jet.base_lie (a b : Jet R M) : ⁅a,b⁆.base = ⁅a.base,b.base⁆ := rfl
@[simp] theorem Jet.velocity_lie (a b : Jet R M) :
    ⁅a,b⁆.velocity = ⁅a.velocity,b.base⁆ + ⁅a.base,b.velocity⁆ := rfl

instance : LieRing (Jet R M) where
  add_lie a b c := by (ext <;> simp [add_lie]); abel
  lie_add a b c := by (ext <;> simp [lie_add]); abel
  lie_self a := by
    ext
    · simp
    · change ⁅a.velocity, a.base⁆ + ⁅a.base, a.velocity⁆ = 0
      rw [← lie_skew a.velocity a.base]
      exact neg_add_cancel _
  leibniz_lie a b c := by (ext <;> simp [lie_add, add_lie, lie_lie]); abel
instance : LieAlgebra R (Jet R M) where
  lie_smul q a b := by ext <;> simp [lie_smul, smul_add]

def Jet.baseHom : Jet R M →ₗ⁅R⁆ M where
  toFun := Jet.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' {_ _} := rfl

variable {α : Type*}
local notation "F" => FreeLieAlgebra R α

def jetLift (f : α → F) : F →ₗ⁅R⁆ Jet R F :=
  FreeLieAlgebra.lift R (fun a => ⟨FreeLieAlgebra.of R a, f a⟩)

@[simp] theorem jetLift_base (f : α → F) (p : F) :
    (jetLift f p).base = p := by
  have h : Jet.baseHom.comp (jetLift f) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [jetLift, Jet.baseHom]
    rfl
  exact LieHom.congr_fun h p

def extend (f : α → F) : LieDerivation R F F where
  toFun q := (jetLift f q).velocity
  map_add' a b := by
    change (jetLift f (a+b)).velocity = _
    rw [map_add]
    rfl
  map_smul' r a := by
    change (jetLift f (r • a)).velocity = _
    rw [map_smul]
    rfl
  leibniz' a b := by
    change (jetLift f ⁅a,b⁆).velocity = ⁅a,(jetLift f b).velocity⁆ - ⁅b,(jetLift f a).velocity⁆
    rw [LieHom.map_lie, Jet.velocity_lie, jetLift_base, jetLift_base]
    rw [sub_eq_add_neg, lie_skew, add_comm]

@[simp] theorem extend_of (f : α → F) (a : α) :
    extend f (FreeLieAlgebra.of R a) = f a := by
  change (jetLift f (FreeLieAlgebra.of R a)).velocity = _
  simp [jetLift]

@[ext] theorem ext {d₁ d₂ : LieDerivation R F F}
    (h : ∀ a, d₁ (FreeLieAlgebra.of R a) = d₂ (FreeLieAlgebra.of R a)) : d₁ = d₂ := by
  ext q
  induction q using freeLie_induction with
  | h0 => simp
  | hg a => exact h a
  | ha a b ha hb => simp [ha, hb]
  | hs r a ha => simp [ha]
  | hl a b ha hb => simp [ha, hb]

variable [DecidableEq α]
def pair (i j : α) : LieDerivation R F F :=
  extend (fun k => if k = i then ⁅FreeLieAlgebra.of R i, FreeLieAlgebra.of R j⁆
    else if k = j then ⁅FreeLieAlgebra.of R j, FreeLieAlgebra.of R i⁆ else 0)

@[simp] theorem pair_of_left (i j : α) :
    pair (R := R) i j (FreeLieAlgebra.of R i) = ⁅FreeLieAlgebra.of R i,FreeLieAlgebra.of R j⁆ := by
  simp [pair]

@[simp] theorem pair_of_right (i j : α) :
    pair (R := R) i j (FreeLieAlgebra.of R j) = ⁅FreeLieAlgebra.of R j,FreeLieAlgebra.of R i⁆ := by
  by_cases h : j = i
  · subst j; simp
  · simp [pair, h]

@[simp] theorem pair_of_other (i j k : α) (hi : k ≠ i) (hj : k ≠ j) :
    pair (R := R) i j (FreeLieAlgebra.of R k) = 0 := by
  simp [pair, hi, hj]

theorem pair_comm (i j : α) : pair (R := R) i j = pair j i := by
  apply ext
  intro a
  by_cases hi : a=i
  · subst a; simp
  by_cases hj : a=j
  · subst a; simp
  simp [hi,hj]

theorem pair_self (i : α) : pair (R := R) i i = 0 := by
  apply ext
  intro a
  by_cases hi : a=i
  · subst a; simp
  simp [hi]

theorem pair_disjoint (i j k l : α)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ⁅pair (R := R) i j,pair (R := R) k l⁆ = 0 := by
  apply ext
  intro a
  by_cases hai : a=i
  · subst a; simp [hik,hil,hjk,hjl]
  by_cases haj : a=j
  · subst a; simp [hik,hil,hjk,hjl]
  by_cases hak : a=k
  · subst a; simp [hik.symm,hjk.symm,hil.symm,hjl.symm]
  by_cases hal : a=l
  · subst a; simp [hik.symm,hjk.symm,hil.symm,hjl.symm]
  simp [hai,haj,hak,hal]

theorem pair_three (i j k : α) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅pair (R := R) i j, pair (R := R) i k + pair (R := R) j k⁆ = 0 := by
  apply ext
  intro a
  by_cases hai : a=i
  · subst a
    simp [hik,hij,hjk,hij.symm,hik.symm,hjk.symm]
    grind [lie_skew, lie_lie]
  by_cases haj : a=j
  · subst a
    simp [hik,hij,hjk,hij.symm,hik.symm,hjk.symm]
    grind [lie_skew, lie_lie]
  by_cases hak : a=k
  · subst a
    simp [hik.symm,hjk.symm]
    grind [lie_skew, lie_lie]
  simp [hai,haj,hak]

end FreeDerivations

namespace BraidRepresentation
open FreeDerivations LieAlgebra
variable {R α : Type*} [CommRing R] [DecidableEq α]
local notation "F" => FreeLieAlgebra R α
local notation "Der" => LieDerivation R F F
local notation "SD" => SemiDirectSum F Der (LieHom.id : Der →ₗ⁅R⁆ Der)

def fiber (i : α) : SD := SemiDirectSum.inl LieHom.id (FreeLieAlgebra.of R i)
def base (i j : α) : SD := SemiDirectSum.inr LieHom.id (pair i j)

def chord : Option α → Option α → SD
  | none, none => 0
  | none, some j => fiber j
  | some i, none => fiber i
  | some i, some j => base i j

@[simp] theorem chord_none_none : chord (R := R) (α := α) none none = 0 := rfl
@[simp] theorem chord_none_some (j : α) : chord (R := R) none (some j) = fiber j := rfl
@[simp] theorem chord_some_none (i : α) : chord (R := R) (some i) none = fiber i := rfl
@[simp] theorem chord_some_some (i j : α) : chord (R := R) (some i) (some j) = base i j := rfl

@[simp] theorem chord_self (i : Option α) : chord (R := R) i i = 0 := by
  cases i <;> simp [base, pair_self]

end BraidRepresentation

namespace BraidModel
open LieAlgebra
abbrev Fiber := FreeLieAlgebra ℚ (Fin 3)
abbrev Der := LieDerivation ℚ Fiber Fiber
abbrev Model := SemiDirectSum Fiber Der (LieHom.id : Der →ₗ⁅ℚ⁆ Der)
def chord (i j : Fin 4) : Model :=
  BraidRepresentation.chord (finSuccEquiv' (1 : Fin 4) i) (finSuccEquiv' (1 : Fin 4) j)

@[simp] theorem chord_self (i : Fin 4) : chord i i = 0 :=
  BraidRepresentation.chord_self _

end BraidModel

theorem map_eval {M N : Type*} [LieRing M] [LieAlgebra ℚ M]
    [LieRing N] [LieAlgebra ℚ N] (f : M →ₗ⁅ℚ⁆ N) (a b : M) (p : L) :
    f (eval a b p) = eval (f a) (f b) p := by
  have h : f.comp (eval a b) = eval (f a) (f b) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [eval]
  exact LieHom.congr_fun h p

@[simp] theorem chord_comm (i j : Fin 4) : chord i j = chord j i := by
  unfold chord
  split_ifs <;> first | rfl | omega

@[simp] theorem t_comm (i j : Fin 4) : t i j = t j i := by
  unfold t
  rw [chord_comm]

@[simp] theorem t_self (i : Fin 4) : t i i = 0 := by simp [t, chord]

namespace InnerSemiDirect
open LieAlgebra
variable {R K B Z : Type*} [CommRing R]
  [LieRing K] [LieAlgebra R K] [LieRing B] [LieAlgebra R B]
  [LieRing Z] [LieAlgebra R Z]
variable (action : B →ₗ⁅R⁆ LieDerivation R K K)
  (f : K →ₗ⁅R⁆ Z) (g : B →ₗ⁅R⁆ Z)
  (h : ∀ q p, f (action q p) = ⁅g q,f p⁆)

def lift : SemiDirectSum K B action →ₗ⁅R⁆ Z where
  toFun z := f z.left + g z.right
  map_add' z t := by simp; abel
  map_smul' c z := by simp [smul_add]
  map_lie' {z t} := by
    simp only [SemiDirectSum.lie_eq_mk, map_sub, map_add, LieHom.map_lie, h,
      add_lie, lie_add]
    rw [sub_eq_add_neg, lie_skew]
    abel

@[simp] theorem lift_inl (p : K) : lift action f g h (SemiDirectSum.inl action p) = f p := by
  simp [lift]
@[simp] theorem lift_inr (p : B) : lift action f g h (SemiDirectSum.inr action p) = g p := by
  simp [lift]
end InnerSemiDirect

namespace SpecialFiber
open LieAlgebra FreeDerivations
abbrev F := FreeLieAlgebra ℚ (Fin 3)
def fa : F := FreeLieAlgebra.of ℚ 0

def action : L →ₗ⁅ℚ⁆ LieDerivation ℚ F F := eval (pair 0 1) (pair 1 2)

end SpecialFiber

namespace Differentiation
open FreeDerivations

variable {M N : Type} [LieRing M] [LieAlgebra ℚ M] [LieRing N] [LieAlgebra ℚ N]

@[simp] theorem Jet.base_neg (p : Jet ℚ M) : (-p).base = -p.base := rfl
@[simp] theorem Jet.velocity_neg (p : Jet ℚ M) : (-p).velocity = -p.velocity := rfl
@[simp] theorem Jet.base_sub (p q : Jet ℚ M) : (p-q).base = p.base-q.base := rfl
@[simp] theorem Jet.velocity_sub (p q : Jet ℚ M) : (p-q).velocity = p.velocity-q.velocity := rfl

@[simp] theorem Jet.mk_add (a b da db : M) :
    (Jet.mk a da : Jet ℚ M) + Jet.mk b db = Jet.mk (a+b) (da+db) := rfl
@[simp] theorem Jet.mk_neg (a da : M) :
    -(Jet.mk a da : Jet ℚ M) = Jet.mk (-a) (-da) := rfl
@[simp] theorem Jet.mk_sub (a b da db : M) :
    (Jet.mk a da : Jet ℚ M) - Jet.mk b db = Jet.mk (a-b) (da-db) := rfl

@[simp] theorem eval_base (a b : Jet ℚ M) (p : L) :
    (eval a b p).base = eval a.base b.base p := map_eval Jet.baseHom a b p

end Differentiation

namespace Elimination
open LieAlgebra
variable {R α : Type*} [CommRing R]
attribute [local instance] LieRing.ofAssociativeRing
abbrev F (R α : Type*) [CommRing R] := FreeLieAlgebra R (ℕ × α)
abbrev G (R α : Type*) [CommRing R] := FreeLieAlgebra R (Option α)
def X : G R α := FreeLieAlgebra.of R none
def Y (a : α) : G R α := FreeLieAlgebra.of R (some a)
def E (n : ℕ) (a : α) : F R α := FreeLieAlgebra.of R (n,a)
def shift : LieDerivation R (F R α) (F R α) :=
  FreeDerivations.extend (fun (i,a) => E (i+1) a)
@[simp] theorem shift_E (n : ℕ) (a : α) : shift (E n a : F R α) = E (n+1) a := by
  simp [shift,E]
def action : R →ₗ⁅R⁆ LieDerivation R (F R α) (F R α) where
  toFun r := r • shift
  map_add' r s := add_smul r s shift
  map_smul' r s := mul_smul r s shift
  map_lie' {r s} := by simp [Ring.lie_def,mul_comm,smul_lie,lie_smul]
abbrev M (R α : Type*) [CommRing R] := SemiDirectSum (F R α) R action

def expand : G R α →ₗ⁅R⁆ M R α :=
  FreeLieAlgebra.lift R (fun a => match a with
    | none => SemiDirectSum.inr action 1
    | some a => SemiDirectSum.inl action (E 0 a))
@[simp] theorem expand_X : expand (X : G R α) = SemiDirectSum.inr action 1 := by
  simp [expand,X]
@[simp] theorem expand_Y (a : α) : expand (Y a : G R α) = SemiDirectSum.inl action (E 0 a) := by
  simp [expand,Y]

def adWord (n : ℕ) (a : α) : G R α :=
  (LieAlgebra.ad R (G R α) X)^[n] (Y a)
@[simp] theorem adWord_zero (a : α) : adWord 0 a = (Y a : G R α) := rfl
@[simp] theorem adWord_succ (n : ℕ) (a : α) :
    (adWord (n+1) a : G R α) = ⁅(X : G R α),adWord n a⁆ := by
  exact Function.iterate_succ_apply' _ n _
def collapseFiber : F R α →ₗ⁅R⁆ G R α := FreeLieAlgebra.lift R (fun (n,a) => adWord n a)
@[simp] theorem collapseFiber_E (n : ℕ) (a : α) :
    collapseFiber (E n a : F R α) = adWord n a := by simp [collapseFiber,E]

theorem collapse_shift (p : F R α) : collapseFiber (shift p) = ⁅(X : G R α),collapseFiber p⁆ := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => cases a; simp [shift,collapseFiber,E,adWord_succ]
  | ha p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,hp,hq]
    simpa only [add_comm] using (leibniz_lie (X : G R α) (collapseFiber p) (collapseFiber q)).symm

def scalarX : R →ₗ⁅R⁆ G R α where
  toFun r := r • X
  map_add' r s := add_smul r s X
  map_smul' r s := mul_smul r s X
  map_lie' {r s} := by simp [Ring.lie_def,mul_comm,smul_lie,lie_smul]

def collapse : M R α →ₗ⁅R⁆ G R α :=
  InnerSemiDirect.lift action collapseFiber scalarX (by
    intro r p
    change collapseFiber (r • shift p) = ⁅r • X,collapseFiber p⁆
    rw [map_smul,collapse_shift,smul_lie])

@[simp] theorem collapse_inl (p : F R α) :
    collapse (SemiDirectSum.inl action p) = collapseFiber p := by simp [collapse,InnerSemiDirect.lift]
@[simp] theorem collapse_inr (r : R) :
    collapse (SemiDirectSum.inr action r : M R α) = r • X := by simp [collapse,InnerSemiDirect.lift,scalarX]

theorem collapse_expand (p : G R α) : collapse (expand p) = p := by
  have h : collapse.comp (expand : G R α →ₗ⁅R⁆ M R α) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [expand,collapse,InnerSemiDirect.lift,scalarX,collapseFiber,E,X,Y]
  exact LieHom.congr_fun h p

end Elimination

namespace AssociativeElimination
open LieAlgebra
variable {R α β : Type*} [CommRing R]
attribute [local instance] LieRing.ofAssociativeRing
abbrev A (R α : Type*) [CommRing R] := MonoidAlgebra R (FreeMonoid α)
def atom (a : α) : A R α := MonoidAlgebra.single (FreeMonoid.of a) 1

def lift {B : Type*} [Ring B] [Algebra R B] (f : α → B) : A R α →ₐ[R] B :=
  MonoidAlgebra.lift R B (FreeMonoid α) (FreeMonoid.lift f)
@[simp] theorem lift_atom {B : Type*} [Ring B] [Algebra R B] (f : α → B) (a : α) :
    lift (R := R) f (atom a) = f a := by simp [lift,atom]

@[ext] theorem hom_ext {B : Type*} [Semiring B] [Algebra R B] {f g : A R α →ₐ[R] B}
    (h : ∀ a, f (atom a) = g (atom a)) : f=g := by
  apply (MonoidAlgebra.lift R B (FreeMonoid α)).symm.injective
  apply FreeMonoid.hom_eq
  intro a
  exact h a

def embed : FreeLieAlgebra R α →ₗ⁅R⁆ A R α := FreeLieAlgebra.lift R atom
@[simp] theorem embed_of (a : α) : embed (FreeLieAlgebra.of R a) = atom a := by simp [embed]

def dualLift (f : α → A R α) : A R α →ₐ[R] DualNumber (A R α) :=
  lift (fun a => TrivSqZeroExt.inl (atom a) + TrivSqZeroExt.inr (f a))
@[simp] theorem dualLift_base (f : α → A R α) (p : A R α) :
    (dualLift f p).fst = p := by
  have h : (TrivSqZeroExt.fstHom R (A R α) (A R α)).comp (dualLift f) = AlgHom.id R (A R α) := by
    apply hom_ext
    intro a
    simp [dualLift]
  exact AlgHom.congr_fun h p

def deriv (f : α → A R α) : A R α →ₗ[R] A R α :=
  ((TrivSqZeroExt.sndHom (A R α) (A R α)).restrictScalars R).comp (dualLift f).toLinearMap
@[simp] theorem deriv_atom (f : α → A R α) (a : α) : deriv f (atom a) = f a := by
  simp [deriv,dualLift]
@[simp] theorem deriv_one (f : α → A R α) : deriv f 1 = 0 := by simp [deriv]
theorem deriv_mul (f : α → A R α) (p q : A R α) :
    deriv f (p*q) = deriv f p*q + p*deriv f q := by
  change (dualLift f (p*q)).snd = _
  rw [map_mul,DualNumber.snd_mul,dualLift_base,dualLift_base]
  exact add_comm _ _
theorem deriv_lie (f : α → A R α) (p q : A R α) :
    deriv f ⁅p,q⁆ = ⁅deriv f p,q⁆ + ⁅p,deriv f q⁆ := by
  simp only [Ring.lie_def,map_sub,deriv_mul]
  abel

def shift : A R (ℕ×α) →ₗ[R] A R (ℕ×α) := deriv (fun (i,a) => atom (i+1,a))
@[simp] theorem shift_atom (i : ℕ) (a : α) : shift (atom (i,a) : A R (ℕ×α)) = atom (i+1,a) := by
  simp [shift]
@[simp] theorem shift_one : shift (1 : A R (ℕ×α)) = 0 := deriv_one _
theorem shift_mul (p q : A R (ℕ×α)) : shift (p*q) = shift p*q + p*shift q := deriv_mul _ _ _

theorem embed_shift (p : Elimination.F R α) : embed (Elimination.shift p) = shift (embed p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => cases a; simp [Elimination.shift,Elimination.E]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,hp,hq]
    simpa only [shift,add_comm] using (deriv_lie (fun (i,a) => (atom (i+1,a) : A R (ℕ×α))) (embed p) (embed q)).symm

def leftMul : A R α →ₐ[R] Module.End R (A R α) := Algebra.lsmul R R (A R α)
@[simp] theorem leftMul_apply (p q : A R α) : leftMul p q = p*q := rfl
@[simp] theorem comm_shift_left (p : A R (ℕ×α)) :
    ⁅(shift : Module.End R (A R (ℕ×α))),leftMul p⁆ = leftMul (shift p) := by
  apply LinearMap.ext
  intro q
  change shift (p*q)-p*shift q = shift p*q
  rw [shift_mul,add_sub_cancel_right]

def scalarShift : R →ₗ⁅R⁆ Module.End R (A R (ℕ×α)) where
  toFun r := r • shift
  map_add' r s := add_smul r s shift
  map_smul' r s := mul_smul r s shift
  map_lie' {r s} := by simp [Ring.lie_def,smul_smul,mul_comm]

def representation : Elimination.M R α →ₗ⁅R⁆ Module.End R (A R (ℕ×α)) :=
  InnerSemiDirect.lift Elimination.action (leftMul.toLieHom.comp embed) scalarShift (by
    intro r p
    change leftMul (embed (r • Elimination.shift p)) = ⁅r • (shift : Module.End R (A R (ℕ×α))),leftMul (embed p)⁆
    rw [map_smul,map_smul,embed_shift]
    apply LinearMap.ext
    intro q
    change r • (shift (embed p)*q) = r • shift (embed p*q) - embed p*(r • shift q)
    rw [shift_mul,smul_add,mul_smul_comm,add_sub_cancel_right])

def operator : A R (Option α) →ₐ[R] Module.End R (A R (ℕ×α)) :=
  lift (fun | none => shift | some a => leftMul (atom (0,a)))

@[simp] theorem representation_inl (p : Elimination.F R α) :
    representation (SemiDirectSum.inl Elimination.action p) = leftMul (embed p) := by simp [representation,InnerSemiDirect.lift]
@[simp] theorem representation_inr (r : R) :
    representation (SemiDirectSum.inr Elimination.action r : Elimination.M R α) = r • shift := by
  simp [representation,InnerSemiDirect.lift,scalarShift]

theorem operator_embed (p : Elimination.G R α) :
    operator (embed p) = representation (Elimination.expand p) := by
  have h : operator.toLieHom.comp embed = representation.comp (Elimination.expand : Elimination.G R α →ₗ⁅R⁆ Elimination.M R α) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [operator,Elimination.expand,Elimination.E,representation,InnerSemiDirect.lift,scalarShift]
  exact LieHom.congr_fun h p

def extract : A R (Option α) →ₗ[R] A R (ℕ×α) :=
  (LinearMap.applyₗ 1).comp operator.toLinearMap

theorem extract_embed (p : Elimination.G R α) :
    extract (embed p) = embed (Elimination.expand p).left := by
  change operator (embed p) 1 = _
  rw [operator_embed]
  change (leftMul (embed (Elimination.expand p).left) + (Elimination.expand p).right • (shift : Module.End R (A R (ℕ×α)))) 1 = _
  simp

end AssociativeElimination

namespace IntegralWords
open Classical
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {α β : Type*}

def countSome : List (Option α) → ℕ
  | [] => 0
  | none::w => countSome w
  | some _::w => countSome w + 1

theorem countSome_le (w : List (Option α)) : countSome w ≤ w.length := by
  induction w with
  | nil => simp [countSome]
  | cons a w ih => cases a <;> simp [countSome] <;> omega

theorem countSome_lt {w : List (Option α)} (hw : none ∈ w) : countSome w < w.length := by
  induction w with
  | nil => simp at hw
  | cons a w ih =>
    cases a with
    | none => simpa [countSome] using Nat.lt_succ_of_le (countSome_le w)
    | some a =>
      have h := ih (by simpa using hw)
      simp [countSome]
      omega

def tag (a b : α) : Option α := if a=b then none else some b

def untag (a : α) : Option α → α
  | none => a
  | some b => b

end IntegralWords

namespace UniversalEmbedding
open Classical LieAlgebra AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α β : Type*} [CommRing R]
abbrev FL (R α : Type*) [CommRing R] := FreeLieAlgebra R α

inductive Tree (α : Type*)
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

def Tree.leaves : Tree α → List α
  | .leaf a => [a]
  | .node t u => t.leaves ++ u.leaves

def Tree.eval : Tree α → FL R α
  | .leaf a => FreeLieAlgebra.of R a
  | .node t u => ⁅t.eval,u.eval⁆

def Tree.map (f : α → β) : Tree α → Tree β
  | .leaf a => .leaf (f a)
  | .node t u => .node (t.map f) (u.map f)

@[simp] theorem Tree.leaves_map (f : α → β) (t : Tree α) :
    (t.map f).leaves = t.leaves.map f := by
  induction t <;> simp_all [Tree.map,Tree.leaves]

theorem Tree.positive (t : Tree α) : 0<t.leaves.length := by
  induction t <;> simp_all [Tree.leaves]

def bounded (n : ℕ) (S : Finset α) : Submodule R (FL R α) :=
  Submodule.span R {p | ∃ t : Tree α, t.leaves.length≤n ∧ (∀ a ∈ t.leaves, a∈S) ∧ t.eval=p}
def small (n : ℕ) : Submodule R (FL R α) :=
  Submodule.span R {p | ∃ t : Tree α, t.leaves.length≤n ∧ t.eval=p}

theorem eval_bounded (t : Tree α) {n : ℕ} {S : Finset α}
    (hn : t.leaves.length≤n) (hS : ∀ a ∈ t.leaves, a∈S) :
    (t.eval : FL R α) ∈ bounded n S := Submodule.subset_span ⟨t,hn,hS,rfl⟩
theorem eval_small (t : Tree α) {n : ℕ} (hn : t.leaves.length≤n) :
    (t.eval : FL R α) ∈ small n := Submodule.subset_span ⟨t,hn,rfl⟩

theorem bounded_mono {n m : ℕ} {S T : Finset α} (hn : n ≤ m) (hS : S ⊆ T) :
    (bounded n S : Submodule R (FL R α)) ≤ bounded m T := by
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,hs,rfl⟩
  exact eval_bounded t (ht.trans hn) (fun a ha => hS (hs a ha))
theorem bounded_small (n : ℕ) (S : Finset α) :
    (bounded n S : Submodule R (FL R α)) ≤ small n := by
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,_,rfl⟩
  exact eval_small t ht

theorem small_mono {n m : ℕ} (h : n ≤ m) :
    (small n : Submodule R (FL R α)) ≤ small m := by
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,rfl⟩
  exact eval_small t (ht.trans h)

theorem bracket_small {n m : ℕ} {p q : FL R α} (hp : p∈small n) (hq : q∈small m) :
    ⁅p,q⁆ ∈ small (n+m) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨t,ht,rfl⟩
    induction hq using Submodule.span_induction with
    | mem q hq =>
      rcases hq with ⟨u,hu,rfl⟩
      exact eval_small (.node t u) (by simpa [Tree.leaves] using Nat.add_le_add ht hu)
    | zero => simp
    | add p q _ _ hp hq => simpa only [lie_add] using (small _).add_mem hp hq
    | smul r p _ hp => simpa only [lie_smul] using (small _).smul_mem r hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [add_lie] using (small _).add_mem hp hq
  | smul r p _ hp => simpa only [smul_lie] using (small _).smul_mem r hp

theorem small_exists_support {p : FL R α} {n : ℕ} (hp : p∈small n) :
    ∃ S : Finset α, p∈bounded n S := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨t,ht,rfl⟩
    exact ⟨t.leaves.toFinset,eval_bounded t ht (by simp)⟩
  | zero => exact ⟨∅,Submodule.zero_mem _⟩
  | add p q _ _ hp hq =>
    rcases hp with ⟨S,hS⟩
    rcases hq with ⟨T,hT⟩
    exact ⟨S∪T,(bounded _ _).add_mem
      (bounded_mono le_rfl Finset.subset_union_left hS)
      (bounded_mono le_rfl Finset.subset_union_right hT)⟩
  | smul r p _ hp =>
    obtain ⟨S,hS⟩ := hp
    exact ⟨S,(bounded _ _).smul_mem r hS⟩

theorem small_exists (p : FL R α) : ∃ n, p∈small n := by
  induction p using freeLie_induction with
  | h0 => exact ⟨0,Submodule.zero_mem _⟩
  | hg a => exact ⟨1,eval_small (.leaf a) le_rfl⟩
  | ha p q hp hq =>
    obtain ⟨n,hn⟩ := hp
    obtain ⟨m,hm⟩ := hq
    exact ⟨n+m,(small _).add_mem (small_mono (Nat.le_add_right _ _) hn)
      (small_mono (Nat.le_add_left _ _) hm)⟩
  | hs r p hp => obtain ⟨n,hn⟩ := hp; exact ⟨n,(small _).smul_mem r hn⟩
  | hl p q hp hq =>
    obtain ⟨n,hn⟩ := hp
    obtain ⟨m,hm⟩ := hq
    exact ⟨n+m,bracket_small hn hm⟩

theorem small_zero {p : FL R α} (hp : p∈small 0) : p=0 := by
  have h : (small 0 : Submodule R (FL R α)) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro p ⟨t,ht,_⟩
    have := t.positive
    omega
  exact h hp

theorem bounded_empty {p : FL R α} {n : ℕ} (hp : p∈bounded n ∅) : p=0 := by
  have h : (bounded n ∅ : Submodule R (FL R α)) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro p ⟨t,_,ht,_⟩
    obtain ⟨a,ha⟩ := List.exists_mem_of_length_pos t.positive
    exact (Finset.notMem_empty a (ht a ha)).elim
  exact h hp

def rename (f : α → β) : FL R α →ₗ⁅R⁆ FL R β :=
  FreeLieAlgebra.lift R (fun a => FreeLieAlgebra.of R (f a))
def renameAssoc (f : α → β) : A R α →ₐ[R] A R β := lift (fun a => atom (f a))
@[simp] theorem rename_of (f : α → β) (a : α) :
    rename f (FreeLieAlgebra.of R a) = FreeLieAlgebra.of R (f a) := by simp [rename]
@[simp] theorem rename_eval (f : α → β) (t : Tree α) :
    rename f (t.eval : FL R α) = (t.map f).eval := by
  induction t <;> simp_all [Tree.eval,Tree.map,LieHom.map_lie]

theorem rename_embed (f : α → β) (p : FL R α) :
    embed (rename f p) = renameAssoc f (embed p) := by
  have h : (embed : FL R β →ₗ⁅R⁆ A R β).comp (rename f) =
      (renameAssoc f).toLieHom.comp embed := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [renameAssoc]
  exact LieHom.congr_fun h p

def kill (a : α) : FL R α →ₗ⁅R⁆ FL R α :=
  FreeLieAlgebra.lift R (fun b => if b=a then 0 else FreeLieAlgebra.of R b)
def killAssoc (a : α) : A R α →ₐ[R] A R α :=
  lift (fun b => if b=a then 0 else atom b)
@[simp] theorem kill_of (a b : α) : kill a (FreeLieAlgebra.of R b) =
    if b=a then 0 else FreeLieAlgebra.of R b := by simp [kill]

theorem kill_embed (a : α) (p : FL R α) : embed (kill a p) = killAssoc a (embed p) := by
  have h : (embed : FL R α →ₗ⁅R⁆ A R α).comp (kill a) = (killAssoc a).toLieHom.comp embed := by
    apply FreeLieAlgebra.hom_ext
    intro b
    simp only [LieHom.comp_apply,kill_of,embed_of,killAssoc,lift_atom,AlgHom.toLieHom_apply]
    split_ifs <;> simp
  exact LieHom.congr_fun h p

theorem kill_eval (a : α) (t : Tree α) :
    kill a (t.eval : FL R α) = if a∈t.leaves then 0 else t.eval := by
  induction t with
  | leaf b => simp [Tree.eval,Tree.leaves,eq_comm]
  | node t u ht hu =>
    simp only [Tree.eval,LieHom.map_lie,ht,hu,Tree.leaves,List.mem_append]
    split_ifs <;> simp_all

theorem kill_bounded (a : α) (S : Finset α) {n : ℕ} {p : FL R α}
    (hp : p∈bounded n (insert a S)) : kill a p∈bounded n S := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨t,ht,hs,rfl⟩
    rw [kill_eval]
    split_ifs with ha
    · exact (bounded _ _).zero_mem
    · exact eval_bounded t ht (fun b hb => (Finset.mem_insert.mp (hs b hb)).resolve_left
        (fun h => ha (h ▸ hb)))
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (bounded _ _).add_mem hp hq
  | smul r p _ hp => simpa only [map_smul] using (bounded _ _).smul_mem r hp

def fiber : Elimination.G R α →ₗ[R] Elimination.F R α :=
  { toFun := fun p => (Elimination.expand p).left
    map_add' := by intro p q; simp
    map_smul' := by intro r p; simp }

@[simp] theorem fiber_X : fiber (Elimination.X : Elimination.G R α) = 0 := by
  simp [fiber]
@[simp] theorem fiber_Y (a : α) : fiber (Elimination.Y a : Elimination.G R α) = Elimination.E 0 a := by
  simp [fiber]
theorem fiber_lie (p q : Elimination.G R α) :
    fiber ⁅p,q⁆ = ⁅fiber p,fiber q⁆ + (Elimination.expand p).right • Elimination.shift (fiber q) -
      (Elimination.expand q).right • Elimination.shift (fiber p) := by
  simp [fiber,LieHom.map_lie,Elimination.action]

theorem shift_small {p : Elimination.F R α} {n : ℕ} (hp : p∈small n) :
    Elimination.shift p∈small n := by
  have ht : ∀ t : Tree (ℕ×α), Elimination.shift (t.eval : Elimination.F R α)∈small t.leaves.length := by
    intro t
    induction t with
    | leaf a =>
      rcases a with ⟨i,a⟩
      simpa [Tree.eval,Tree.leaves,Elimination.shift,Elimination.E] using
        eval_small (R := R) (.leaf (i+1,a)) le_rfl
    | node t u ht hu =>
      simp only [Tree.eval,Tree.leaves,List.length_append,LieDerivation.apply_lie_eq_add]
      exact (small _).add_mem (bracket_small (eval_small t le_rfl) hu)
        (bracket_small ht (eval_small u le_rfl))
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨t,hn,rfl⟩ := hp; exact small_mono hn (ht t)
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (small _).add_mem hp hq
  | smul r p _ hp => simpa only [map_smul] using (small _).smul_mem r hp

theorem countSome_append (u v : List (Option α)) :
    IntegralWords.countSome (u++v) = IntegralWords.countSome u+IntegralWords.countSome v := by
  induction u with
  | nil => simp [IntegralWords.countSome]
  | cons a u ih =>
    cases a <;> simp only [List.cons_append,IntegralWords.countSome,ih]
    omega

theorem fiber_eval (t : Tree (Option α)) :
    fiber (t.eval : Elimination.G R α)∈small (IntegralWords.countSome t.leaves) := by
  induction t with
  | leaf a =>
    cases a with
    | none =>
      change fiber (Elimination.X : Elimination.G R α)∈small 0
      simp
    | some a =>
      change fiber (Elimination.Y a : Elimination.G R α)∈small 1
      rw [fiber_Y]
      exact eval_small (.leaf (0,a)) le_rfl
  | node t u ht hu =>
    rw [Tree.eval,fiber_lie,Tree.leaves,countSome_append]
    exact (small _).sub_mem
      ((small _).add_mem (bracket_small ht hu)
        ((small _).smul_mem _ (small_mono (Nat.le_add_left _ _) (shift_small hu))))
      ((small _).smul_mem _ (small_mono (Nat.le_add_right _ _) (shift_small ht)))

theorem fiber_remainder (a : α) {p : FL R α} {n : ℕ} (hp : p∈small (n+1)) :
    fiber (rename (IntegralWords.tag a) (p-kill a p))∈small n := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,ht,rfl⟩ := hp
    rw [kill_eval]
    split_ifs with ha
    · rw [sub_zero,rename_eval]
      apply small_mono _ (fiber_eval (R := R) (t.map (IntegralWords.tag a)))
      have hnone : none∈(t.map (IntegralWords.tag a)).leaves := by
        rw [Tree.leaves_map]
        exact List.mem_map.mpr ⟨a,ha,by simp [IntegralWords.tag]⟩
      have hlt := IntegralWords.countSome_lt hnone
      simp only [Tree.leaves_map,List.length_map] at hlt ⊢
      omega
    · simp
  | zero => simp
  | add p q _ _ hp hq =>
    have h : p+q-kill a (p+q) = (p-kill a p)+(q-kill a q) := by rw [map_add]; abel
    rw [h,map_add,map_add]
    exact (small _).add_mem hp hq
  | smul r p _ hp =>
    simpa only [map_smul,← smul_sub] using (small _).smul_mem r hp

def traceAssoc : A R (Option α) →ₐ[R] R := lift (fun | none => 1 | some _ => 0)
theorem trace_embed (p : Elimination.G R α) :
    traceAssoc (embed p) = (Elimination.expand p).right := by
  have h : (traceAssoc : A R (Option α) →ₐ[R] R).toLieHom.comp embed =
      (SemiDirectSum.projr Elimination.action).comp Elimination.expand := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [traceAssoc,Elimination.expand]
  exact LieHom.congr_fun h p

theorem untag_tag (a : α) (p : FL R α) :
    rename (IntegralWords.untag a) (rename (IntegralWords.tag a) p) = p := by
  have h : (rename (IntegralWords.untag a) : FL R (Option α) →ₗ⁅R⁆ FL R α).comp
      (rename (IntegralWords.tag a)) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro b
    simp [IntegralWords.tag,IntegralWords.untag]
    split_ifs <;> simp_all
  exact LieHom.congr_fun h p

theorem kernel_bounded (R : Type v) [CommRing R] (n : ℕ) :
    ∀ (α : Type u) (p : FL R α), p∈small n → embed p=0 → p=0 := by
  induction n with
  | zero => intro α p hp _; exact small_zero hp
  | succ n ih =>
    intro α p hp hzero
    have hs : ∀ S : Finset α, ∀ p : FL R α, p∈bounded (n+1) S → embed p=0 → p=0 := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro p hp _; exact bounded_empty hp
      | @insert a S ha ihS =>
        intro p hp hz
        have hk : kill a p=0 := ihS (kill a p) (kill_bounded a S hp) (by rw [kill_embed,hz,map_zero])
        have ht : embed (rename (IntegralWords.tag a) p)=0 := by rw [rename_embed,hz,map_zero]
        have hf : fiber (rename (IntegralWords.tag a) p)=0 := by
          apply ih (ℕ×α) _
          · simpa only [hk,sub_zero] using fiber_remainder a (bounded_small _ _ hp)
          · change embed (Elimination.expand (rename (IntegralWords.tag a) p)).left=0
            rw [← extract_embed,ht,map_zero]
        have hr : (Elimination.expand (rename (IntegralWords.tag a) p)).right=0 := by
          rw [← trace_embed,ht,map_zero]
        have he : Elimination.expand (rename (IntegralWords.tag a) p)=0 := by
          apply SemiDirectSum.ext
          · exact hf
          · exact hr
        have hz' : rename (IntegralWords.tag a) p=0 := by
          rw [← Elimination.collapse_expand (rename (IntegralWords.tag a) p),he,map_zero]
        rw [← untag_tag a p,hz',map_zero]
    obtain ⟨S,hS⟩ := small_exists_support hp
    exact hs S p hS hzero

theorem injective : Function.Injective (embed : FL R α →ₗ⁅R⁆ A R α) := by
  intro p q h
  obtain ⟨n,hn⟩ := small_exists (p-q)
  have h0 : embed (p-q)=0 := by rw [map_sub,h,sub_self]
  exact sub_eq_zero.mp (kernel_bounded R n α (p-q) hn h0)

end UniversalEmbedding

namespace QuadraticAlphabet
open AssociativeElimination LieAlgebra
attribute [local instance] LieRing.ofAssociativeRing

theorem algebra_induction {R α : Type*} [CommRing R] {P : A R α → Prop}
    (p : A R α) (h1 : P 1) (ha : ∀ a, P (atom a))
    (hadd : ∀ p q, P p → P q → P (p+q))
    (hs : ∀ (r : R) p, P p → P (r • p))
    (hm : ∀ p q, P p → P q → P (p*q)) : P p := by
  apply MonoidAlgebra.induction_on p ?_ hadd hs
  intro w
  change P (MonoidAlgebra.single w 1)
  have hh : ∀ v : List α, P (MonoidAlgebra.single (FreeMonoid.ofList v) 1) := by
    intro v
    induction v with
    | nil => exact h1
    | cons a v ih =>
      convert hm (atom a) (MonoidAlgebra.single (FreeMonoid.ofList v) 1) (ha a) ih using 1
      simp only [atom,MonoidAlgebra.single_mul_single,one_mul,FreeMonoid.ofList_cons]
  simpa using hh w.toList

end QuadraticAlphabet

namespace AssociativeDerivations
open LieAlgebra AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]
local notation "FL" => FreeLieAlgebra R α

def extend (d : LieDerivation R FL FL) : Module.End R (A R α) :=
  deriv (fun a => embed (d (FreeLieAlgebra.of R a)))
@[simp] theorem extend_atom (d : LieDerivation R FL FL) (a : α) :
    extend d (atom a) = embed (d (FreeLieAlgebra.of R a)) := by simp [extend]
@[simp] theorem extend_one (d : LieDerivation R FL FL) :
    extend d 1=0 := deriv_one _
theorem extend_mul (d : LieDerivation R FL FL) (p q : A R α) :
    extend d (p*q)=extend d p*q+p*extend d q := deriv_mul _ p q

theorem extend_embed (d : LieDerivation R FL FL) (p : FL) :
    extend d (embed p)=embed (d p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieHom.map_lie,extend,deriv_lie] at *
    rw [hp,hq,LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,LieHom.map_lie]
    exact add_comm _ _

theorem linear_ext {f g : Module.End R (A R α)}
    (h1 : f 1=g 1) (ha : ∀ a, f (atom a)=g (atom a))
    (hf : ∀ p q, f (p*q)=f p*q+p*f q)
    (hg : ∀ p q, g (p*q)=g p*q+p*g q) : f=g := by
  apply LinearMap.ext
  intro p
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => exact h1
  | ha a => exact ha a
  | hadd p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hm p q hp hq => rw [hf,hg,hp,hq]

theorem comm_mul (f g : Module.End R (A R α))
    (hf : ∀ p q, f (p*q)=f p*q+p*f q)
    (hg : ∀ p q, g (p*q)=g p*q+p*g q) (p q : A R α) :
    ⁅f,g⁆ (p*q)=⁅f,g⁆ p*q+p*⁅f,g⁆ q := by
  change f (g (p*q))-g (f (p*q))=(f (g p)-g (f p))*q+p*(f (g q)-g (f q))
  rw [hf,hg,map_add,map_add,hf,hf,hg,hg]
  noncomm_ring

def hom : LieDerivation R FL FL →ₗ⁅R⁆ Module.End R (A R α) where
  toFun := extend
  map_add' d e := by
    apply linear_ext
    · simp
    · intro a; simp [LieDerivation.add_apply]
    · exact extend_mul _
    · intro p q; simp only [LinearMap.add_apply,extend_mul]; noncomm_ring
  map_smul' r d := by
    apply linear_ext
    · simp
    · intro a; simp
    · exact extend_mul _
    · intro p q; simp [extend_mul,smul_add]
  map_lie' {d e} := by
    apply linear_ext
    · change extend ⁅d,e⁆ 1=extend d (extend e 1)-extend e (extend d 1)
      simp
    · intro a
      change extend ⁅d,e⁆ (atom a)=extend d (extend e (atom a))-extend e (extend d (atom a))
      simp [extend_embed]
    · exact extend_mul _
    · exact comm_mul _ _ (extend_mul d) (extend_mul e)

@[simp] theorem hom_apply (d : LieDerivation R FL FL) (p : A R α) :
    hom d p=extend d p := rfl

end AssociativeDerivations

namespace FiberPBW
open AssociativeElimination LieAlgebra
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α G : Type*} [CommRing R] [LieRing G] [LieAlgebra R G]
  (act : G →ₗ⁅R⁆ LieDerivation R (FreeLieAlgebra R α) (FreeLieAlgebra R α))
local notation "F" => FreeLieAlgebra R α
local notation "B" => UniversalEnvelopingAlgebra R G
local notation "V" => A R α ⊗[R] B

def fiber : F →ₗ⁅R⁆ Module.End R V :=
  (Module.End.rTensorAlgHom R (A R α) B).toLieHom.comp (leftMul.toLieHom.comp embed)

def action : G →ₗ⁅R⁆ Module.End R V :=
  (Module.End.rTensorAlgHom R (A R α) B).toLieHom.comp (AssociativeDerivations.hom.comp act)

@[simp] theorem fiber_tmul (p : F) (q : A R α) (b : B) :
    fiber p (q⊗ₜ b)=(embed p*q)⊗ₜ b := rfl

end FiberPBW

namespace GenericBraid
open LieAlgebra FreeDerivations
variable {R α : Type*} [CommRing R]
abbrev Free (R α : Type*) [CommRing R] := FreeLieAlgebra R (α×α)
def gen (i j : α) : Free R α := FreeLieAlgebra.of R (i,j)
def relations : Set (Free R α) := {q |
  (∃ i, q=gen (R:=R) i i) ∨ (∃ i j, q=gen (R:=R) i j-gen (R:=R) j i) ∨
  (∃ i j k l, i≠k ∧ i≠l ∧ j≠k ∧ j≠l ∧ q=⁅gen (R:=R) i j,gen (R:=R) k l⁆) ∨
  (∃ i j k, i≠j ∧ i≠k ∧ j≠k ∧ q=⁅gen (R:=R) i j,gen (R:=R) i k+gen (R:=R) j k⁆)}
def ideal : LieIdeal R (Free R α) := LieSubmodule.lieSpan R _ relations
abbrev T (R α : Type*) [CommRing R] := Free R α ⧸ (ideal (R:=R) (α:=α))
def t (i j : α) : T R α := (ideal (R:=R) (α:=α)).mkQ (gen i j)

theorem relation_zero {q : Free R α} (h : q∈relations) :
    (ideal (R:=R) (α:=α)).mkQ q=0 := by
  exact (LieSubmodule.Quotient.mk_eq_zero _).mpr (LieSubmodule.subset_lieSpan h)
@[simp] theorem t_self (i : α) : t (R:=R) i i=0 :=
  relation_zero (Or.inl ⟨i,rfl⟩)
theorem t_comm (i j : α) : t (R:=R) i j=t j i := by
  have h := relation_zero (R:=R) (Or.inr (Or.inl ⟨i,j,rfl⟩))
  simpa only [map_sub,sub_eq_zero,t] using h
theorem t_disjoint (i j k l : α) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅t (R:=R) i j,t (R:=R) k l⁆=0 := by
  change (ideal (R:=R) (α:=α)).mkQ (⁅gen i j,gen k l⁆)=0
  exact relation_zero (Or.inr (Or.inr (Or.inl ⟨i,j,k,l,hik,hil,hjk,hjl,rfl⟩)))
theorem t_three (i j k : α) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅t (R:=R) i j,t (R:=R) i k+t (R:=R) j k⁆=0 := by
  change (ideal (R:=R) (α:=α)).mkQ (⁅gen i j,gen i k+gen j k⁆)=0
  exact relation_zero (Or.inr (Or.inr (Or.inr ⟨i,j,k,hij,hik,hjk,rfl⟩)))

variable {E : Type*} [LieRing E] [LieAlgebra R E]
def lift (f : α → α → E) (hz : ∀ i, f i i=0) (hs : ∀ i j,f i j=f j i)
    (hd : ∀ i j k l,i≠k → i≠l → j≠k → j≠l → ⁅f i j,f k l⁆=0)
    (ht : ∀ i j k,i≠j → i≠k → j≠k → ⁅f i j,f i k+f j k⁆=0) : T R α →ₗ⁅R⁆ E := by
  let p := FreeLieAlgebra.lift R (fun ij : α×α => f ij.1 ij.2)
  have hker : ideal (R:=R) (α:=α) ≤ p.ker := by
    rw [ideal,LieSubmodule.lieSpan_le]
    intro q hq
    change p q=0
    rcases hq with ⟨i,rfl⟩ | ⟨i,j,rfl⟩ | ⟨i,j,k,l,hik,hil,hjk,hjl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
    · simpa only [p,gen,FreeLieAlgebra.lift_of_apply] using hz i
    · simpa only [map_sub,p,gen,FreeLieAlgebra.lift_of_apply,sub_eq_zero] using hs i j
    · simpa only [LieHom.map_lie,p,gen,FreeLieAlgebra.lift_of_apply] using hd i j k l hik hil hjk hjl
    · simpa only [LieHom.map_lie,map_add,p,gen,FreeLieAlgebra.lift_of_apply] using ht i j k hij hik hjk
  exact { (ideal (R:=R) (α:=α)).toSubmodule.liftQ p.toLinearMap hker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact p.map_lie a b }
@[simp] theorem lift_t (f : α → α → E) (hz hs hd ht) (i j : α) :
    lift f hz hs hd ht (t (R:=R) i j)=f i j := by
  change FreeLieAlgebra.lift R (fun ij : α×α => f ij.1 ij.2) (FreeLieAlgebra.of R (i,j))=f i j
  simp only [FreeLieAlgebra.lift_of_apply]

variable [DecidableEq α]
def action : T R α →ₗ⁅R⁆ LieDerivation R (FreeLieAlgebra R α) (FreeLieAlgebra R α) :=
  lift pair pair_self pair_comm pair_disjoint pair_three
local notation "F" => FreeLieAlgebra R α
local notation "SD" => SemiDirectSum F (T R α) action
@[simp] theorem action_t (i j : α) : action (t (R:=R) i j)=pair i j := by simp [action]
end GenericBraid

namespace RestrictedAlphabet
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
inductive Letter (α : Type*) | a | c (i : α) | b (i : α)
variable {α : Type*}

end RestrictedAlphabet

namespace GenericBraid
open LieAlgebra AssociativeElimination
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R] [DecidableEq α]
abbrev Env (R α : Type*) [CommRing R] := UniversalEnvelopingAlgebra R (T R α)

def baseLie : T R α →ₗ⁅R⁆ T R (Option α) :=
  lift (fun i j => t (some i) (some j)) (fun i => t_self (some i))
    (fun i j => t_comm (some i) (some j)) (fun i j k l hik hil hjk hjl =>
      t_disjoint (some i) (some j) (some k) (some l) (fun h => hik (Option.some.inj h))
        (fun h => hil (Option.some.inj h)) (fun h => hjk (Option.some.inj h))
        (fun h => hjl (Option.some.inj h)))
    (fun i j k hij hik hjk => t_three (some i) (some j) (some k) (fun h => hij (Option.some.inj h))
      (fun h => hik (Option.some.inj h)) (fun h => hjk (Option.some.inj h)))
omit [DecidableEq α] in
@[simp] theorem baseLie_t (i j : α) : baseLie (t (R:=R) i j)=t (some i) (some j) := by
  simp [baseLie]

def fiberIn : A R α →ₐ[R] Env R (Option α) :=
  AssociativeElimination.lift (fun i => UniversalEnvelopingAlgebra.ι R (t none (some i)))
def baseIn : Env R α →ₐ[R] Env R (Option α) :=
  UniversalEnvelopingAlgebra.lift R ((UniversalEnvelopingAlgebra.ι R).comp baseLie)

end GenericBraid

namespace Deletion

section
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]
def word (w : List α) : A R α := MonoidAlgebra.single (FreeMonoid.ofList w) 1
@[simp] theorem word_nil : word ([] : List α)=(1 : A R α) := rfl

def raw (ν : α → α → R) (l r : α) : List α → A R α
  | [] => 0
  | a::s => (ν a (s.headD r)-ν l a) • word s+atom a*raw ν a r s

def op (ν : α → α → R) (l r : α) : Module.End R (A R α) :=
  (Finsupp.linearCombination R (fun w : FreeMonoid α => raw ν l r w.toList)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
@[simp] theorem op_word (ν : α → α → R) (l r : α) (s : List α) :
    op ν l r (word s)=raw ν l r s := by
  change Finsupp.linearCombination R (fun monoidWord : FreeMonoid α => raw ν l r monoidWord.toList) (Finsupp.single (FreeMonoid.ofList s) 1) = _; simp
@[simp] theorem op_one (ν : α → α → R) (l r : α) : op ν l r 1=0 := by
  exact op_word ν l r []

end

open AssociativeElimination
variable {R α : Type*} [CommRing R]
theorem linear_ext {M : Type*} [AddCommGroup M] [Module R M]
    {f g : A R α →ₗ[R] M} (h : ∀ s : List α,f (word s)=g (word s)) : f=g := by
  apply LinearMap.ext
  intro p
  induction p using MonoidAlgebra.induction_on with
  | of w => simpa only [word,FreeMonoid.ofList_toList,MonoidAlgebra.of_apply] using h w.toList
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

theorem raw_add (ν μ : α → α → R) (l r : α) (s : List α) :
    raw (fun a b => ν a b+μ a b) l r s=raw ν l r s+raw μ l r s := by
  induction s generalizing l with
  | nil => simp [raw]
  | cons a s ih => simp only [raw,ih,mul_add]; module
@[simp] theorem op_add (ν μ : α → α → R) (l r : α) :
    op (fun a b => ν a b+μ a b) l r=op ν l r+op μ l r := by
  apply linear_ext
  intro s
  simp only [LinearMap.add_apply,op_word,raw_add]
@[simp] theorem op_zero (l r : α) : op (fun _ _ => (0 : R)) l r=0 := by
  apply linear_ext
  intro s
  simp only [LinearMap.zero_apply,op_word]
  induction s generalizing l with
  | nil => rfl
  | cons a s ih => simp [raw,ih]

end Deletion

namespace DeletionTable
open Deletion AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
inductive Letter | o | e | p | w deriving DecidableEq
inductive Hyperplane | a1 | a2 | a3 | p12 | m12 | p13 | m13 | p23 | m23 deriving DecidableEq
open Letter Hyperplane

end DeletionTable

attribute [local instance 2000] FreeLieAlgebra.instLieAlgebra

namespace BaseChangeEquations
variable {R : Type*} [CommRing R]
def x : FreeLieAlgebra R Bool := FreeLieAlgebra.of R false
def y : FreeLieAlgebra R Bool := FreeLieAlgebra.of R true
def eval {M : Type*} [LieRing M] [LieAlgebra R M] (a b : M) : FreeLieAlgebra R Bool →ₗ⁅R⁆ M :=
  FreeLieAlgebra.lift R (fun i => if i then b else a)
@[simp] theorem eval_x {M : Type*} [LieRing M] [LieAlgebra R M] (a b : M) : eval (R:=R) a b x=a := by simp [eval,x]
@[simp] theorem eval_y {M : Type*} [LieRing M] [LieAlgebra R M] (a b : M) : eval (R:=R) a b y=b := by simp [eval,y]
def antisymmetry (q : FreeLieAlgebra R Bool) := q+eval y x q
def pentagon (q : FreeLieAlgebra R Bool) : GenericBraid.T R (Fin 4) :=
  let t := GenericBraid.t (R:=R)
  eval (t 0 1) (t 1 2+t 1 3) q+eval (t 0 2+t 1 2) (t 2 3) q-
    eval (t 1 2) (t 2 3) q-eval (t 0 1+t 0 2) (t 1 3+t 2 3) q-eval (t 0 1) (t 1 2) q

variable {S : Type*} [CommRing S]

end BaseChangeEquations

namespace PolynomialOrdering
open AssociativeElimination
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α β : Type*} [CommRing R]
abbrev V := A R α ⊗[R] A R β
variable (δ : β → α → A R α)
def fiberOp (a : α) : Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  TensorProduct.map (leftMul (atom a)) LinearMap.id
def baseOp (b : β) : Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  TensorProduct.map (deriv (δ b)) LinearMap.id+
    TensorProduct.map LinearMap.id (leftMul (atom b))
def op : Sum α β → Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  Sum.elim fiberOp (baseOp δ)
@[simp] theorem fiberOp_tmul (a : α) (p : A R α) (q : A R β) :
    fiberOp a (p⊗ₜ q)=(atom a*p)⊗ₜ q := rfl
@[simp] theorem baseOp_tmul (b : β) (p : A R α) (q : A R β) :
    baseOp δ b (p⊗ₜ q)=deriv (δ b) p⊗ₜ q+p⊗ₜ (atom b*q) := rfl

def operators : A R (Sum α β) →ₐ[R] Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  lift (op δ)
def normalize : A R (Sum α β) →ₗ[R] V (R:=R) (α:=α) (β:=β) :=
  (LinearMap.applyₗ ((1 : A R α)⊗ₜ (1 : A R β))).comp (operators δ).toLinearMap
@[simp] theorem normalize_one : normalize δ 1=1⊗ₜ 1 := by
  change operators δ 1 (1⊗ₜ 1)=_; simp
@[simp] theorem normalize_atom_mul (s : Sum α β) (p : A R (Sum α β)) :
    normalize δ (atom s*p)=op δ s (normalize δ p) := by
  change operators δ (atom s*p) (1⊗ₜ 1)=_
  rw [map_mul,Module.End.mul_apply]
  simp only [operators,lift_atom]
  rfl

variable {U : Type*} [Ring U] [Algebra R U]
def interpret (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U) : V (R:=R) (α:=α) (β:=β) →ₗ[R] U :=
  TensorProduct.lift
    { toFun := fun p =>
        { toFun := fun q => f p*g q
          map_add' := by intro q r; simp [mul_add]
          map_smul' := by intro c q; simp }
      map_add' := by intro p r; ext q; simp [add_mul]
      map_smul' := by intro c p; ext q; simp }
@[simp] theorem interpret_tmul (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U)
    (p : A R α) (q : A R β) : interpret f g (p⊗ₜ q)=f p*g q := rfl

def evaluate (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U) : A R (Sum α β) →ₐ[R] U :=
  lift (Sum.elim (fun a => f (atom a)) (fun b => g (atom b)))

variable (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U)
variable (hδ : ∀ b a,g (atom b)*f (atom a)-f (atom a)*g (atom b)=f (δ b a))
include hδ

omit hδ
def fiberIn : A R α →ₐ[R] A R (Sum α β) := lift (fun a => atom (.inl a))
def baseIn : A R β →ₐ[R] A R (Sum α β) := lift (fun b => atom (.inr b))

end PolynomialOrdering

namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]
def word (w : FreeMonoid α) : A R α := MonoidAlgebra.single w 1
@[simp] theorem word_one : word (1 : FreeMonoid α)=(1 : A R α) := rfl
@[simp] theorem word_of (a : α) : word (FreeMonoid.of a)=(atom a : A R α) := rfl
@[simp] theorem word_mul (u v : FreeMonoid α) : word (R:=R) (u*v)=word u*word v := by
  simp [word,MonoidAlgebra.single_mul_single]
def space (P : FreeMonoid α → Prop) : Submodule R (A R α) :=
  Submodule.span R {p | ∃ w,P w ∧ p=word w}
theorem word_mem {P : FreeMonoid α → Prop} (w : FreeMonoid α) (hw : P w) : word (R:=R) w∈space P :=
  Submodule.subset_span ⟨w,hw,rfl⟩
theorem space_mono {P Q : FreeMonoid α → Prop} (h : ∀ w,P w → Q w) :
    space (R:=R) P ≤ space Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w,hw,rfl⟩
  exact word_mem w (h w hw)
theorem coeff_support {P : FreeMonoid α → Prop} {p : A R α} (hp : p∈space P)
    (w : FreeMonoid α) (hw : ¬P w) : p.coeff w=0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨v,hv,rfl⟩ := hp
    have hne : v≠w := fun h => hw (h ▸ hv)
    simp [word,hne]
  | zero => simp
  | add p q _ _ hp hq => simp [hp,hq]
  | smul c p _ hp => simp [hp]
theorem mem_space {P : FreeMonoid α → Prop} {p : A R α}
    (h : ∀ w,p.coeff w≠0 → P w) : p∈space P := by
  classical
  rw [← MonoidAlgebra.sum_coeff_single p]
  apply Submodule.sum_mem
  intro w hw
  have hp := h w (Finsupp.mem_support_iff.mp hw)
  have he : MonoidAlgebra.single w (p.coeff w)=p.coeff w • word (R:=R) w := by simp [word]
  rw [he]
  exact (space P).smul_mem _ (word_mem w hp)

theorem mul_mem {P Q T : FreeMonoid α → Prop} (h : ∀ u v,P u → Q v → T (u*v))
    {p q : A R α} (hp : p∈space P) (hq : q∈space Q) : p*q∈space T := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq => obtain ⟨v,hv,rfl⟩ := hq; rw [← word_mul]; exact word_mem _ (h u v hu hv)
    | zero => simp
    | add p q _ _ hp hq => simpa only [mul_add] using (space T).add_mem hp hq
    | smul c p _ hp => simpa only [mul_smul_comm] using (space T).smul_mem c hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [add_mul] using (space T).add_mem hp hq
  | smul c p _ hp => simpa only [smul_mul_assoc] using (space T).smul_mem c hp

def project (P : FreeMonoid α → Prop) [DecidablePred P] : A R α →ₗ[R] A R α :=
  (Finsupp.linearCombination R (fun w => if P w then word w else 0)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
@[simp] theorem project_word (P : FreeMonoid α → Prop) [DecidablePred P] (w : FreeMonoid α) :
    project (R:=R) P (word w)=if P w then word w else 0 := by
  change Finsupp.linearCombination R (fun monoidWord => if P monoidWord then word monoidWord else 0) (Finsupp.single w 1) = _; simp
theorem project_coeff (P : FreeMonoid α → Prop) [DecidablePred P] (p : A R α) (w : FreeMonoid α) :
    (project P p).coeff w=if P w then p.coeff w else 0 := by
  classical
  induction p using MonoidAlgebra.induction_on with
  | of v =>
    change (project P (word v)).coeff w=_
    rw [project_word]
    by_cases hv : P v <;> by_cases hw : P w <;> simp [hv,hw,word]
    · apply Finsupp.single_eq_of_ne
      intro h
      exact hw (h ▸ hv)
    · symm
      apply Finsupp.single_eq_of_ne
      intro h
      exact hv (h ▸ hw)
  | add p q hp hq => simp only [map_add,MonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hq]; split_ifs <;> simp
  | smul c p hp => simp only [map_smul,MonoidAlgebra.coeff_smul,Finsupp.smul_apply,hp]; split_ifs <;> simp

theorem project_mem (P : FreeMonoid α → Prop) [DecidablePred P] (p : A R α) : project P p∈space P := by
  apply mem_space
  intro w hw
  by_contra hn
  exact hw (by rw [project_coeff,if_neg hn])
theorem project_eq_self {P : FreeMonoid α → Prop} [DecidablePred P] {p : A R α}
    (hp : p∈space P) : project P p=p := by
  ext w
  rw [project_coeff]
  split_ifs with h
  · rfl
  · exact (coeff_support hp w h).symm
theorem project_eq_zero {P Q : FreeMonoid α → Prop} [DecidablePred Q] {p : A R α}
    (hp : p∈space P) (h : ∀ w,P w → ¬Q w) : project Q p=0 := by
  ext w
  rw [project_coeff]
  split_ifs with hw
  · exact coeff_support hp w (fun hp => h w hp hw)
  · rfl

def degree (wt : α → ℕ) (w : FreeMonoid α) : ℕ := (w.toList.map wt).sum
@[simp] theorem degree_one (wt : α → ℕ) : degree wt 1=0 := rfl
@[simp] theorem degree_of (wt : α → ℕ) (a : α) : degree wt (FreeMonoid.of a)=wt a := by simp [degree]
@[simp] theorem degree_mul (wt : α → ℕ) (u v : FreeMonoid α) : degree wt (u*v)=degree wt u+degree wt v := by
  simp [degree]
def homogeneous (wt : α → ℕ) (n : ℕ) := space (R:=R) (fun w => degree wt w=n)
def above (wt : α → ℕ) (n : ℕ) := space (R:=R) (fun w => n≤degree wt w)
def below (wt : α → ℕ) (n : ℕ) := space (R:=R) (fun w => degree wt w≤n)
def piece (wt : α → ℕ) (n : ℕ) : A R α →ₗ[R] A R α := project (fun w => degree wt w=n)
theorem homogeneous_mul {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈homogeneous wt n) (hq : q∈homogeneous wt m) : p*q∈homogeneous wt (n+m) :=
  mul_mem (by intros; simp_all) hp hq
theorem above_mul {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈above wt n) (hq : q∈above wt m) : p*q∈above wt (n+m) :=
  mul_mem (by intros; simp_all; omega) hp hq

end WordGrading

namespace TriangularWords
open AssociativeElimination WordGrading
variable {R α V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
def action (f : α → Module.End R V) : A R α →ₐ[R] Module.End R V := lift f
@[simp] theorem action_atom (f : α → Module.End R V) (a : α) : action f (atom a)=f a := lift_atom f a

end TriangularWords
namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]
def strictlyBelow (wt : α → ℕ) (n : ℕ) := space (R:=R) (fun w => degree wt w<n)

end WordGrading
namespace CountTables

section
open AssociativeElimination
abbrev K := ZMod 2
abbrev F := Fin 5
abbrev B := Fin 4

def H : A K F := atom 0
def U (i : Fin 2) : A K F := atom ⟨i.val+1,by omega⟩
def V (i : Fin 2) : A K F := atom ⟨i.val+3,by omega⟩
def bracket {R α : Type*} [CommRing R] (p q : A R α) := p*q-q*p
def R' (i : Fin 2) := bracket H (U i)
def Q (i : Fin 2) := bracket (H+V i) (U i)
def W := bracket (V 0) (U 1)+bracket (U 0) (V 1)
def common : B → F → A K F
  | 0,0 => bracket H (V 0)
  | 0,1 => Q 0
  | 0,3 => bracket H (V 0)
  | 1,0 => bracket H (V 1)
  | 1,2 => Q 1
  | 1,4 => bracket H (V 1)
  | 2,1 | 2,2 => bracket (U 0) (U 1)
  | 2,3 | 2,4 => W
  | 3,1 => bracket (U 0) (V 1)
  | 3,2 => bracket (U 1) (V 0)
  | 3,3 | 3,4 => bracket (V 0) (V 1)
  | _,_ => 0
def higher : B → F → A K F
  | 0,0 => bracket (R' 0) (U 0)
  | 0,3 => bracket (bracket (V 0) (U 0)) (U 0)
  | 0,4 => bracket (Q 0) (U 1)
  | 1,0 => bracket (R' 1) (U 1)
  | 1,4 => bracket (bracket (V 1) (U 1)) (U 1)
  | 1,3 => bracket (Q 1) (U 0)
  | 3,0 => bracket H (bracket (U 0) (U 1))
  | 3,3 => bracket W (U 0)+bracket (U 0) (R' 1)
  | 3,4 => bracket W (U 1)+bracket (U 1) (R' 0)
  | _,_ => 0
def lower : B → F → A K F
  | 2,3 | 2,4 => bracket (V 0) (V 1)
  | _,_ => 0
def source (b : B) (a : F) := common b a+higher b a
def target (b : B) (a : F) := common b a+lower b a

def fiberCount : F → ℕ | 1 | 2 => 1 | _ => 0
def baseCount : B → ℕ | 2 => 1 | _ => 0

open WordGrading

end

open AssociativeElimination
abbrev G := Fin 3
def X : A K G := atom 0
def Y (i : Fin 2) : A K G := atom ⟨i.val+1,by omega⟩
def C (i : Fin 2) := bracket X (Y i)
def realize : A K F →ₐ[K] A K G := lift (fun a => match a with
  | 0 => X*X | 1 => Y 0 | 2 => Y 1 | 3 => C 0 | _ => C 1)

@[simp] theorem realize_H : realize H=X*X := by simp [realize,H]
@[simp] theorem realize_U (i : Fin 2) : realize (U i)=Y i := by fin_cases i <;> simp [realize,U]
@[simp] theorem realize_V (i : Fin 2) : realize (V i)=C i := by fin_cases i <;> simp [realize,V]
@[simp] theorem realize_bracket (p q : A K F) : realize (bracket p q)=bracket (realize p) (realize q) := by simp [bracket]
@[simp] theorem deriv_bracket {R α : Type*} [CommRing R] (f : α → A R α) (p q : A R α) :
    deriv f (bracket p q)=bracket (deriv f p) q+bracket p (deriv f q) := by
  simp only [bracket,map_sub,AssociativeElimination.deriv_mul]; abel

@[simp] theorem bracket_add_left (p q r : A K G) : bracket (p+q) r=bracket p r+bracket q r := by simp [bracket,add_mul,mul_add]; abel
@[simp] theorem bracket_add_right (p q r : A K G) : bracket p (q+r)=bracket p q+bracket p r := by simp [bracket,add_mul,mul_add]; abel
@[simp] theorem bracket_sub_left (p q r : A K G) : bracket (p-q) r=bracket p r-bracket q r := by simp [bracket,sub_mul,mul_sub]; abel
@[simp] theorem bracket_sub_right (p q r : A K G) : bracket p (q-r)=bracket p q-bracket p r := by simp [bracket,sub_mul,mul_sub]; abel
@[simp] theorem bracket_zero_left (r : A K G) : bracket 0 r=0 := by simp [bracket]
@[simp] theorem bracket_zero_right (r : A K G) : bracket r 0=0 := by simp [bracket]
@[simp] theorem bracket_self (r : A K G) : bracket r r=0 := by simp [bracket]

@[simp] theorem realize_atom_zero : realize (atom (0 : F))=X*X := realize_H
@[simp] theorem realize_atom_one : realize (atom (1 : F))=Y 0 := realize_U 0
@[simp] theorem realize_atom_two : realize (atom (2 : F))=Y 1 := realize_U 1
@[simp] theorem realize_atom_three : realize (atom (3 : F))=C 0 := realize_V 0
@[simp] theorem realize_atom_four : realize (atom (4 : F))=C 1 := realize_V 1

attribute [local irreducible] X Y C H U V
end CountTables
namespace WeightedDeletion
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]
def raw (κ : α → α → α → R) (l r : α) : List α → A R α
  | [] => 0
  | a::s => κ l a (s.headD r) • word (FreeMonoid.ofList s)+atom a*raw κ a r s

def op (κ : α → α → α → R) (l r : α) : Module.End R (A R α) :=
  (Finsupp.linearCombination R (fun w : FreeMonoid α => raw κ l r w.toList)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
@[simp] theorem op_word (κ : α → α → α → R) (l r : α) (s : List α) :
    op κ l r (word (FreeMonoid.ofList s))=raw κ l r s := by change Finsupp.linearCombination R (fun monoidWord : FreeMonoid α => raw κ l r monoidWord.toList) (Finsupp.single (FreeMonoid.ofList s) 1) = _; simp

end WeightedDeletion

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld
namespace PolynomialOrdering
open AssociativeElimination WordGrading
open scoped TensorProduct
variable {R α β γ : Type*} [CommRing R]

def merge : V (R:=R) (α:=α) (β:=β) →ₗ[R] A R (Sum α β) :=
  interpret fiberIn baseIn
@[simp] theorem merge_tmul (p : A R α) (q : A R β) :
    merge (p⊗ₜ q)=fiberIn p*baseIn q := rfl

def ordered (δ : β → α → A R α) : A R (Sum α β) →ₗ[R] A R (Sum α β) :=
  merge.comp (normalize δ)

variable (wa : α → ℕ) (wb : β → ℕ)

variable {δ δ₀ : β → α → A R α}

def baseStage (f : A R β →ₗ[R] A R β) : V (R:=R) (α:=α) (β:=β) →ₗ[R] A R (Sum α β) :=
  merge.comp (TensorProduct.map LinearMap.id f)
@[simp] theorem baseStage_tmul (f : A R β →ₗ[R] A R β) (p : A R α) (q : A R β) :
    baseStage f (p⊗ₜ q)=fiberIn p*baseIn (f q) := rfl

def iterated (δ : β → α → A R α) (f : A R β →ₗ[R] A R β) :
    A R (Sum α β) →ₗ[R] A R (Sum α β) := (baseStage f).comp (normalize δ)

end PolynomialOrdering

namespace AlphabetTransport
open AssociativeElimination WordGrading
variable {R α β : Type*} [CommRing R]
def map (e : α → β) : A R α →ₐ[R] A R β := lift (fun a => atom (e a))
@[simp] theorem map_atom (e : α → β) (a : α) : map (R:=R) e (atom a)=atom (e a) := lift_atom _ _
theorem map_inverse (e : α ≃ β) (p : A R α) : map e.symm (map e p)=p := by
  have h : (map (R:=R) e.symm).comp (map e)=AlgHom.id R (A R α) := by
    apply hom_ext
    intro a
    simp
  exact AlgHom.congr_fun h p

end AlphabetTransport

namespace SecondStage
open AssociativeElimination WordGrading PolynomialOrdering
abbrev K := ZMod 2
abbrev F := Fin 3
abbrev B := Unit
abbrev E := Sum F B
abbrev Old := CountTables.B

def toOld : E → Old | .inl 0 => 1 | .inl 1 => 2 | .inl 2 => 3 | .inr _ => 0
def fromOld : Old → E | 0 => .inr () | 1 => .inl 0 | 2 => .inl 1 | 3 => .inl 2
def equiv : E ≃ Old where
  toFun := toOld
  invFun := fromOld
  left_inv s := by cases s with
    | inl a => fin_cases a <;> rfl
    | inr a => cases a; rfl
  right_inv a := by fin_cases a <;> rfl

def outward : A K E →ₐ[K] A K Old := AlphabetTransport.map toOld
def inward : A K Old →ₐ[K] A K E := AlphabetTransport.map fromOld
@[simp] theorem outward_inward (p : A K Old) : outward (inward p)=p :=
  AlphabetTransport.map_inverse equiv.symm p
@[simp] theorem inward_outward (p : A K E) : inward (outward p)=p :=
  AlphabetTransport.map_inverse equiv p

def H : A K F := atom 0
def U : A K F := atom 1
def V : A K F := atom 2
abbrev bracket := @CountTables.bracket
def common (_ : B) : F → A K F
  | 0 | 2 => bracket H V
  | 1 => bracket (H+V) U
def higher (_ : B) : F → A K F
  | 0 => bracket (bracket H U) U
  | 2 => bracket (bracket V U) U
  | _ => 0
def source (b : B) (a : F) := common b a+higher b a

def order (δ : B → F → A K F) : A K Old →ₗ[K] A K Old :=
  outward.toLinearMap.comp ((ordered δ).comp inward.toLinearMap)

end SecondStage
namespace ExactCountOrdering
open AssociativeElimination WordGrading PolynomialOrdering
abbrev K := ZMod 2
abbrev E := Sum CountTables.F CountTables.B
def count : E → ℕ := Sum.elim CountTables.fiberCount CountTables.baseCount
def S : A K E →ₗ[K] A K E := iterated CountTables.source (SecondStage.order SecondStage.source)
def C : A K E →ₗ[K] A K E := iterated CountTables.common (SecondStage.order SecondStage.common)
def T : A K E →ₗ[K] A K E := iterated CountTables.target (SecondStage.order SecondStage.common)

end ExactCountOrdering

namespace PolynomialOrdering
open AssociativeElimination
open scoped TensorProduct
variable {R α β U : Type*} [CommRing R] [Ring U] [Algebra R U]
variable (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U)

@[simp] theorem evaluate_fiber (p : A R α) : evaluate f g (fiberIn p)=f p := by
  have h : (evaluate f g).comp fiberIn=f := by
    apply hom_ext
    intro a
    simp [evaluate,fiberIn]
  exact AlgHom.congr_fun h p

@[simp] theorem evaluate_base (p : A R β) : evaluate f g (baseIn p)=g p := by
  have h : (evaluate f g).comp baseIn=g := by
    apply hom_ext
    intro a
    simp [evaluate,baseIn]
  exact AlgHom.congr_fun h p

end PolynomialOrdering

namespace SourceEnveloping
open AssociativeElimination WordGrading
attribute [local instance] LieRing.ofAssociativeRing
abbrev K := ZMod 2
abbrev Env (α : Type*) := GenericBraid.Env K α
open scoped TensorProduct

@[simp] theorem fiberIn_atom {α : Type*} [DecidableEq α] (a : α) :
    GenericBraid.fiberIn (atom a : A K α)=
      UniversalEnvelopingAlgebra.ι K (GenericBraid.t none (some a)) := by
  simp [GenericBraid.fiberIn]

@[simp] theorem baseIn_ι {α : Type*} [DecidableEq α] (g : GenericBraid.T K α) :
    GenericBraid.baseIn (UniversalEnvelopingAlgebra.ι K g)=
      UniversalEnvelopingAlgebra.ι K (GenericBraid.baseLie g) := by
  simp [GenericBraid.baseIn]

def chord {α : Type*} (i j : α) : Env α := UniversalEnvelopingAlgebra.ι K (GenericBraid.t i j)
@[simp] theorem chord_self {α : Type*} (i : α) : chord i i=0 := by simp [chord]

@[simp] theorem base_chord {α : Type*} [DecidableEq α] (i j : α) :
    GenericBraid.baseIn (chord i j)=chord (some i) (some j) := by
  change GenericBraid.baseIn (UniversalEnvelopingAlgebra.ι K (GenericBraid.t i j))=_
  rw [baseIn_ι,GenericBraid.baseLie_t]
  rfl

@[simp] theorem fiber_chord {α : Type*} [DecidableEq α] (a : α) :
    GenericBraid.fiberIn (atom a : A K α)=chord none (some a) := fiberIn_atom a

end SourceEnveloping
namespace SourceAlphabet
open AssociativeElimination AlphabetTransport
variable {α β : Type*}

def letter5 : CountTables.F ≃ RestrictedAlphabet.Letter (Fin 2) where
  toFun a := match a with | 0 => .a | 1 => .b 0 | 2 => .b 1 | 3 => .c 0 | 4 => .c 1
  invFun s := match s with | .a => 0 | .b i => ⟨i.val+1,by omega⟩ | .c i => ⟨i.val+3,by omega⟩
  left_inv a := by fin_cases a <;> rfl
  right_inv s := by cases s with
    | a => rfl
    | b i => fin_cases i <;> rfl
    | c i => fin_cases i <;> rfl

def letter3 : CountTables.G ≃ Option (Fin 2) where
  toFun a := match a with | 0 => none | 1 => some 0 | 2 => some 1
  invFun a := match a with | none => 0 | some i => ⟨i.val+1,by omega⟩
  left_inv a := by fin_cases a <;> rfl
  right_inv s := by cases s with
    | none => rfl
    | some i => fin_cases i <;> rfl

end SourceAlphabet
namespace SourceModel
open AssociativeElimination AlphabetTransport SourceEnveloping
open scoped TensorProduct
abbrev K := ZMod 2
abbrev S1 := Option Unit
abbrev S2 := Option S1
abbrev S3 := Option S2

def topLetters : CountTables.G ≃ S2 where
  toFun | 0 => some (some ()) | 1 => some none | 2 => none
  invFun | none => 2 | some none => 1 | some (some _) => 0
  left_inv a := by fin_cases a <;> rfl
  right_inv a := by cases a with
    | none => rfl
    | some a => cases a with | none => rfl | some a => cases a; rfl

def topRealize : A K CountTables.F →ₐ[K] A K S2 :=
  (map topLetters).comp CountTables.realize

def topFiber : A K CountTables.F →ₐ[K] Env S3 := GenericBraid.fiberIn.comp topRealize

end SourceModel

namespace SourceModel

section
open AssociativeElimination AlphabetTransport SourceEnveloping
attribute [local instance] LieRing.ofAssociativeRing

def root : S2 := some (some ())
def one : S2 := some none
def two : S2 := none
def oldX : Fin 2 → Env S2 | 0 => SourceEnveloping.chord root one | 1 => SourceEnveloping.chord root two
def oldU : Env S2 := SourceEnveloping.chord one two

def oldBase : A K CountTables.B →ₐ[K] Env S2 := lift (fun b => match b with
  | 0 => oldX 0*oldX 0
  | 1 => oldX 1*oldX 1
  | 2 => oldU
  | _ => ⁅oldX 0,oldU⁆)
def topBase : A K CountTables.B →ₐ[K] Env S3 := GenericBraid.baseIn.comp oldBase

end

section
open AssociativeElimination AlphabetTransport SourceEnveloping
attribute [local instance] LieRing.ofAssociativeRing

end

open AssociativeElimination PolynomialOrdering
open scoped TensorProduct

end SourceModel

namespace WeightedDeletion

section
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]

variable {β : Type*}
def action (κ : β → α → α → α → R) (l r : α) : A R β →ₐ[R] Module.End R (A R α) :=
  lift (fun b => op (κ b) l r)
@[simp] theorem action_atom (κ : β → α → α → α → R) (l r : α) (b : β) :
    action κ l r (atom b)=op (κ b) l r := lift_atom _ _

end

open AssociativeElimination WordGrading
variable {R α β : Type*} [CommRing R]

end WeightedDeletion

namespace RowTwo
open AssociativeElimination WordGrading WeightedDeletion
abbrev K := ZMod 2
inductive Letter | o | e | p | w deriving DecidableEq
inductive Slot | A | C | B deriving DecidableEq
open Letter Slot

def κ : Slot → Letter → Letter → Letter → K
  | .A,_,a,b => if a=.e ∧ b=.w then 1 else 0
  | .C,l,a,b => if a=.p then (if l=.e ∨ l=.w then 1 else 0)+(if b=.e ∨ b=.w then 1 else 0) else 0
  | .B,l,a,b => if a=.o then (if l=.p then 1 else 0)+(if b=.p then 1 else 0) else 0

end RowTwo

namespace TargetDeletion
open AssociativeElimination DeletionTable
attribute [local instance] LieRing.ofAssociativeRing
abbrev F := CountTables.F
abbrev B := CountTables.B
abbrev E := Sum F B

variable {α : Type*}

end TargetDeletion

namespace WeightedDeletion
open AssociativeElimination WordGrading
variable {R α β : Type*} [CommRing R]

def scalar (κ : β → α → α → α → R) (l r : α) (s : FreeMonoid α) : A R β →ₗ[R] R where
  toFun p := (action κ l r p (word s)).coeff 1
  map_add' p q := by simp only [map_add,LinearMap.add_apply,MonoidAlgebra.coeff_add,Finsupp.add_apply]
  map_smul' c p := by simp only [map_smul,LinearMap.smul_apply,MonoidAlgebra.coeff_smul,Finsupp.smul_apply,RingHom.id_apply]

end WeightedDeletion

namespace RowKernel
open AssociativeElimination WordGrading WeightedDeletion RowTwo
open RowTwo.Letter RowTwo.Slot

inductive Row | one | two | three | four deriving DecidableEq

def κ : Row → Slot → Letter → Letter → Letter → K
  | .one, .A, _, a, b | .one, .C, _, a, b => if a=.e ∧ b=.w then 1 else 0
  | .one, .B, _, a, b => if a=.o ∧ b=.w then 1 else 0
  | .two, .A, l, a, b => RowTwo.κ .A l a b
  | .two, .C, l, a, b => RowTwo.κ .C l a b +
      if a=.e then (if l=.p then 1 else 0)+(if b=.p then 1 else 0) else 0
  | .two, .B, l, a, b => RowTwo.κ .B l a b
  | .three, .A, _, _, _ => 0
  | .three, .C, l, a, b =>
      if a=.e then (if l=.p then 1 else 0)+(if b=.p then 1 else 0) else
      if a=.p then (if l=.e then 1 else 0)+(if b=.e then 1 else 0) else 0
  | .three, .B, l, a, b => RowTwo.κ .B l a b
  | .four, .A, _, a, b => if a=.e ∧ b=.w then 1 else 0
  | .four, .C, _, a, b => if (a=.e ∨ a=.p) ∧ b=.w then 1 else 0
  | .four, .B, _, a, b => if a=.o ∧ b=.w then 1 else 0

def enc : Slot → Letter | .A => .e | .C => .p | .B => .o

@[simp] theorem enc_eq_e (a : Slot) : enc a=.e ↔ a=.A := by cases a <;> decide
@[simp] theorem enc_eq_p (a : Slot) : enc a=.p ↔ a=.C := by cases a <;> decide

def test (i : Row) (s : List Slot) : A K Slot →ₗ[K] K :=
  scalar (κ i) .o .w (FreeMonoid.ofList (s.map enc))

def Equation (p : A K Slot) (s : List Slot) : Prop :=
  test .one s p+test .two s p+test .three s p+test .four s p=0

def bCount (k : Slot) : ℕ := if k=.B then 1 else 0

end RowKernel

namespace LetterRetraction
open AssociativeElimination WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]
variable (P : α → Prop) [DecidablePred P]

def lie : FreeLieAlgebra R α →ₗ⁅R⁆ FreeLieAlgebra R α :=
  FreeLieAlgebra.lift R (fun a => if P a then FreeLieAlgebra.of R a else 0)

@[simp] theorem lie_of (a : α) : lie (R:=R) P (FreeLieAlgebra.of R a)=
    if P a then FreeLieAlgebra.of R a else 0 := by simp [lie]

end LetterRetraction

namespace LeadingRows
open AssociativeElimination WordGrading WeightedDeletion RowTwo
open RowKernel
abbrev E := TargetDeletion.E

def slots : Row → Slot → List E
  | .one,.A => [.inr 0]
  | .one,.C => [.inr 3,.inl 3]
  | .one,.B => [.inr 2,.inl 1]
  | .two,.A => [.inr 1,.inr 3]
  | .two,.C => [.inl 4]
  | .two,.B => [.inl 2]
  | .three,.A => [.inr 0,.inr 1,.inr 3]
  | .three,.C => [.inl 3,.inl 4]
  | .three,.B => [.inl 1,.inl 2]
  | .four,.A => [.inr 0]
  | .four,.C => [.inr 3]
  | .four,.B => [.inr 2]

def subst (i : Row) : A K Slot →ₐ[K] A K E :=
  lift (fun k => ((slots i k).map atom).sum)

open PolynomialOrdering
attribute [local instance] LieRing.ofAssociativeRing

end LeadingRows

namespace ExactPentagon
open AssociativeElimination WordGrading RowTwo RowKernel LeadingRows
open PolynomialOrdering

abbrev u12 : A K E := atom (.inr 2)
abbrev u23 : A K E := atom (.inl 2)

def extra : Slot → A K E
  | .A => u12*u12
  | .C => u12*u23-u23*u12
  | .B => 0

def exactTwo : A K Slot →ₐ[K] A K E :=
  lift (fun k => subst .two (atom k)+extra k)

def omitted : A K Slot →ₐ[K] A K E :=
  lift (fun | .A => u12*u12 | .C => u12*u23-u23*u12 | .B => u23)

def weight : Slot → ℕ | .A | .C => 2 | .B => 1

def full (p : A K Slot) : A K E :=
  subst .one p+exactTwo p+omitted p+subst .three p+subst .four p

end ExactPentagon

namespace AssociativeEvaluation
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α U : Type*} [CommRing R] [Ring U] [Algebra R U]

theorem lift_embed (f : α → U) (q : FreeLieAlgebra R α) :
    lift f (embed q)=FreeLieAlgebra.lift R f q := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp only [LieHom.map_lie,Ring.lie_def,map_sub,map_mul,hp,hq]

end AssociativeEvaluation
namespace ExactPentagon
open AssociativeElimination RowTwo RowKernel LeadingRows PolynomialOrdering
open SourceEnveloping SourceModel
abbrev K := ZMod 2
attribute [local instance] LieRing.ofAssociativeRing

def quad : A K Slot →ₐ[K] A K Bool := lift (fun
  | .A => atom false*atom false
  | .C => atom false*atom true-atom true*atom false
  | .B => atom true)

end ExactPentagon
end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section
namespace WordGrading
open AssociativeElimination
variable {R α β : Type*} [CommRing R]

theorem piece_homogeneous {wt : α → ℕ} {k : ℕ} {p : A R α}
    (hp : p∈homogeneous wt k) (n : ℕ) : piece wt n p=if k=n then p else 0 := by
  by_cases h : k=n
  · subst k
    exact (project_eq_self hp).trans (if_pos rfl).symm
  · rw [if_neg h]
    exact project_eq_zero hp (by intro w hw hn; exact h (hw.symm.trans hn))

end WordGrading

namespace LieGrading
open AssociativeElimination UniversalEmbedding WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]

def treeDegree (wt : α → ℕ) (t : UniversalEmbedding.Tree α) : ℕ := (t.leaves.map wt).sum

@[simp] theorem treeDegree_leaf (wt : α → ℕ) (a : α) : treeDegree wt (.leaf a)=wt a := by
  simp [treeDegree,Tree.leaves]
@[simp] theorem treeDegree_node (wt : α → ℕ) (t u : UniversalEmbedding.Tree α) :
    treeDegree wt (.node t u)=treeDegree wt t+treeDegree wt u := by
  simp [treeDegree,Tree.leaves]

theorem embed_eval_homogeneous (wt : α → ℕ) (t : UniversalEmbedding.Tree α) :
    embed (t.eval : FreeLieAlgebra R α)∈homogeneous wt (treeDegree wt t) := by
  induction t with
  | leaf a =>
    simp only [Tree.eval,embed_of,treeDegree_leaf]
    exact word_mem (FreeMonoid.of a) (degree_of wt a)
  | node t u ht hu =>
    simp only [Tree.eval,treeDegree_node,LieHom.map_lie]
    change embed t.eval*embed u.eval-embed u.eval*embed t.eval∈_
    exact (homogeneous _ _).sub_mem (homogeneous_mul ht hu)
      (by simpa only [Nat.add_comm] using homogeneous_mul hu ht)

def homogeneousLie (wt : α → ℕ) (n : ℕ) : Submodule R (FreeLieAlgebra R α) :=
  Submodule.span R {p | ∃ t : UniversalEmbedding.Tree α,treeDegree wt t=n ∧ t.eval=p}

theorem piece_exists (wt : α → ℕ) (n : ℕ) (p : FreeLieAlgebra R α) :
    ∃ q : FreeLieAlgebra R α,q∈homogeneousLie wt n ∧ embed q=piece wt n (embed p) := by
  obtain ⟨k,hk⟩ := small_exists p
  induction hk using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,_,rfl⟩ := hp
    rw [piece_homogeneous (embed_eval_homogeneous (R:=R) wt t)]
    split_ifs with h
    · exact ⟨t.eval,Submodule.subset_span ⟨t,h,rfl⟩,rfl⟩
    · exact ⟨0,(homogeneousLie wt n).zero_mem,map_zero _⟩
  | zero => exact ⟨0,(homogeneousLie wt n).zero_mem,by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨p',hp',he⟩ := hp
    obtain ⟨q',hq',hf⟩ := hq
    exact ⟨p'+q',(homogeneousLie wt n).add_mem hp' hq',by simp only [map_add,he,hf]⟩
  | smul c p _ hp =>
    obtain ⟨p',hp',he⟩ := hp
    exact ⟨c • p',(homogeneousLie wt n).smul_mem c hp',by simp only [map_smul,he]⟩

def piece (wt : α → ℕ) (n : ℕ) (p : FreeLieAlgebra R α) : FreeLieAlgebra R α :=
  (piece_exists wt n p).choose

theorem piece_spec (wt : α → ℕ) (n : ℕ) (p : FreeLieAlgebra R α) :
    piece wt n p∈homogeneousLie wt n ∧ embed (piece wt n p)=WordGrading.piece wt n (embed p) :=
  (piece_exists wt n p).choose_spec

@[simp] theorem embed_piece (wt : α → ℕ) (n : ℕ) (p : FreeLieAlgebra R α) :
    embed (piece wt n p)=WordGrading.piece wt n (embed p) := (piece_spec wt n p).2

theorem homogeneousLie_embed {wt : α → ℕ} {n : ℕ} {p : FreeLieAlgebra R α}
    (hp : p∈homogeneousLie wt n) : embed p∈homogeneous wt n := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨t,ht,rfl⟩ := hp
      simpa only [ht] using embed_eval_homogeneous (R:=R) wt t
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (homogeneous _ _).add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using (homogeneous _ _).smul_mem c hp

end LieGrading
end

namespace PrimitiveWords
open AssociativeElimination
variable {R α : Type*} [CommRing R]
attribute [local instance] LieRing.ofAssociativeRing Classical.propDecidable

abbrev W (α : Type*) := FreeMonoid α

def linear {M : Type*} [AddCommGroup M] [Module R M] (f : W α → M) : A R α →ₗ[R] M :=
  (Finsupp.linearCombination R f).comp (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] theorem linear_single {M : Type*} [AddCommGroup M] [Module R M]
    (f : W α → M) (w : W α) (r : R) : linear f (MonoidAlgebra.single w r)=r • f w := by
  change Finsupp.linearCombination R f (Finsupp.single w r) = _; simp

end PrimitiveWords

namespace WordCoordinates
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]

def coordinates (P : FreeMonoid α → Prop) : space (R:=R) P →ₗ[R] ({w // P w} → R) where
  toFun p w := p.val.coeff w.val
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem coordinates_injective (P : FreeMonoid α → Prop) : Function.Injective (coordinates (R:=R) P) := by
  intro p q h
  apply Subtype.ext
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_cases hw : P w
  · exact congrFun h ⟨w,hw⟩
  · rw [coeff_support p.property w hw,coeff_support q.property w hw]

variable (P : FreeMonoid α → Prop) [Fintype {w // P w}]

def assembly (c : {w // P w} → R) : space (R:=R) P :=
  ⟨∑ w, c w • word w.val,Submodule.sum_mem _ (fun w _ => (space P).smul_mem _ (word_mem _ w.property))⟩

theorem coordinates_assembly (c : {w // P w} → R) : coordinates P (assembly P c)=c := by
  classical
  ext w
  change (∑ v : {w // P w},c v • word v.val).coeff w.val=c w
  simp [word,Finsupp.single_apply,Subtype.val_inj]

def equiv : space (R:=R) P ≃ₗ[R] ({w // P w} → R) :=
  LinearEquiv.ofBijective (coordinates P) ⟨coordinates_injective P,fun c => ⟨assembly P c,coordinates_assembly P c⟩⟩

@[simp] theorem equiv_apply (p : space (R:=R) P) (w : {w // P w}) : equiv P p w=p.val.coeff w.val := rfl

instance finite_space [Module.Finite R R] : Module.Finite R (space (R:=R) P) :=
  Module.Finite.equiv (equiv P).symm

variable {P}

end WordCoordinates

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section
namespace FiniteAlgebraNorm
open scoped Matrix.Norms.Operator
variable (A : Type*) [Ring A] [Algebra ℝ A] [FiniteDimensional ℝ A]

abbrev normedRing : NormedRing A :=
  NormedRing.induced A (Matrix (Fin (Module.finrank ℝ A)) (Fin (Module.finrank ℝ A)) ℝ)
    (Algebra.leftMulMatrix (Module.finBasis ℝ A))
    (Algebra.leftMulMatrix_injective (Module.finBasis ℝ A))

abbrev normedAlgebra : @NormedAlgebra ℝ A _ (normedRing A).toSeminormedRing :=
  NormedAlgebra.induced ℝ A (Matrix (Fin (Module.finrank ℝ A)) (Fin (Module.finrank ℝ A)) ℝ)
    (Algebra.leftMulMatrix (Module.finBasis ℝ A))

variable (K A : Type*) [RCLike K] [Ring A] [Algebra K A] [FiniteDimensional K A]

end FiniteAlgebraNorm

namespace FinitePicard

section
open MeasureTheory Set intervalIntegral
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def term (Ω : ℝ → A) (a : ℝ) : ℕ → ℝ → A
  | 0 => fun _ => 1
  | n+1 => fun t => ∫ s in a..t, Ω s * term Ω a n s

@[simp] theorem term_zero (Ω : ℝ → A) (a t : ℝ) : term Ω a 0 t=1 := rfl
@[simp] theorem term_succ (Ω : ℝ → A) (a t : ℝ) (n : ℕ) :
    term Ω a (n+1) t=∫ s in a..t, Ω s * term Ω a n s := rfl

@[simp] theorem term_base (Ω : ℝ → A) (a : ℝ) (n : ℕ) : term Ω a (n+1) a=0 := by
  simp

variable [CompleteSpace A]

def transport (Ω : ℝ → A) (a : ℝ) (N : ℕ) (t : ℝ) : A :=
  ∑ n∈Finset.range (N+1),term Ω a n t

omit [CompleteSpace A] in
@[simp] theorem transport_base (Ω : ℝ → A) (a : ℝ) (N : ℕ) :
    transport Ω a N a=1 := by
  unfold transport
  rw [Finset.sum_range_succ']
  simp

omit [CompleteSpace A] in

theorem continuousOn_term {Ω : ℝ → A} {a b : ℝ}
    (hΩ : IntervalIntegrable Ω volume a b) (n : ℕ) :
    ContinuousOn (term Ω a n) (uIcc a b) := by
  induction n with
  | zero => exact continuousOn_const
  | succ n ih =>
    exact intervalIntegral.continuousOn_primitive_interval' (hΩ.mul_continuousOn ih) left_mem_uIcc

omit [CompleteSpace A] in
theorem continuousOn_transport {Ω : ℝ → A} {a b : ℝ}
    (hΩ : IntervalIntegrable Ω volume a b) (N : ℕ) :
    ContinuousOn (transport Ω a N) (uIcc a b) :=
  continuousOn_finsetSum _ (fun n _ => continuousOn_term hΩ n)

omit [CompleteSpace A] in
theorem collar_limit {Ω : ℝ → A} {a b : ℝ}
    (hΩ : IntervalIntegrable Ω volume a b) (N : ℕ) :
    Filter.Tendsto (transport Ω a N) (nhdsWithin a (uIcc a b)) (nhds (1:A)) := by
  have h := continuousOn_transport hΩ N a left_mem_uIcc
  change Filter.Tendsto _ _ (nhds (transport Ω a N a)) at h
  simpa only [transport_base] using h

end

open MeasureTheory Set intervalIntegral
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem integral_mem_submodule [FiniteDimensional ℝ A] (S : Submodule ℝ A)
    (f : ℝ → A) (a b : ℝ) (hf : ∀ t, f t ∈ S) :
    (∫ t in a..b, f t) ∈ S := by
  by_cases hi : IntervalIntegrable f volume a b
  · apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp
    intro l hl
    have hz : ∀ t, l (f t)=0 := fun t => (S.mem_dualAnnihilator l).mp hl _ (hf t)
    change l.toContinuousLinearMap (∫ t in a..b, f t)=0
    rw [← l.toContinuousLinearMap.intervalIntegral_comp_comm hi]
    change (∫ t in a..b, l (f t))=0
    simp only [hz, intervalIntegral.integral_zero]
  · rw [integral_undef hi]
    exact S.zero_mem

structure NilpotentFiltration (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] where
  space : ℕ → Submodule ℝ A
  antitone : Antitone space
  one_mem : (1 : A) ∈ space 0
  mul_mem : ∀ m n {x y : A}, x ∈ space m → y ∈ space n → x*y ∈ space (m+n)
  cutoff : ℕ
  terminal : space (cutoff+1)=⊥

variable [FiniteDimensional ℝ A]

omit [FiniteDimensional ℝ A] in
theorem pow_mem (F : NilpotentFiltration A) {X : A} (hX : X ∈ F.space 1) (n : ℕ) :
    X^n ∈ F.space n := by
  induction n with
  | zero => simpa using F.one_mem
  | succ n ih => simpa only [pow_succ] using F.mul_mem n 1 ih hX

omit [FiniteDimensional ℝ A] in
theorem pow_cutoff_eq_zero (F : NilpotentFiltration A) {X : A}
    (hX : X ∈ F.space 1) : X^(F.cutoff+1)=0 := by
  simpa only [F.terminal,Submodule.mem_bot] using pow_mem F hX (F.cutoff+1)

theorem term_mem (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ t, Ω t ∈ F.space 1) (a : ℝ) (n : ℕ) (t : ℝ) :
    term Ω a n t ∈ F.space n := by
  induction n generalizing t with
  | zero => exact F.one_mem
  | succ n ih =>
    apply integral_mem_submodule
    intro s
    simpa only [Nat.add_comm 1 n] using F.mul_mem 1 n (hΩ s) (ih s)

theorem last_term_zero (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ t, Ω t ∈ F.space 1) (a t : ℝ) :
    term Ω a (F.cutoff+1) t=0 := by
  have h := term_mem F hΩ a (F.cutoff+1) t
  simpa only [F.terminal,Submodule.mem_bot] using h

theorem derivative_succ_of_integrable {Ω : ℝ → A} {a b t : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (hc : ContinuousOn Ω (Ioo a b))
    (ht : t ∈ Ioo a b) (n : ℕ) :
    HasDerivAt (term Ω a (n+1)) (Ω t * term Ω a n t) t := by
  have hc' : ∀ x ∈ Ioo a b, ContinuousAt (fun s => Ω s * term Ω a n s) x := by
    intro x hx
    apply (hc.continuousAt (isOpen_Ioo.mem_nhds hx)).mul
    apply (continuousOn_term hi n).continuousAt
    rw [uIcc_of_le (le_trans hx.1.le hx.2.le)]
    exact Icc_mem_nhds hx.1 hx.2
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (hi.mul_continuousOn (continuousOn_term hi n)).mono_set
      (uIcc_subset_uIcc_left (by rw [uIcc_of_le (le_trans ht.1.le ht.2.le)]; exact ⟨ht.1.le,ht.2.le⟩))
  · exact ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hc' t ht
  · exact hc' t ht

theorem derivative_transport_of_integrable {Ω : ℝ → A} {a b t : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (hc : ContinuousOn Ω (Ioo a b))
    (ht : t ∈ Ioo a b) (N : ℕ) :
    HasDerivAt (transport Ω a (N+1)) (Ω t * transport Ω a N t) t := by
  have hf : transport Ω a (N+1) = fun t => 1 + ∑ n∈Finset.range (N+1),term Ω a (n+1) t := by
    funext t
    simp only [transport,Finset.sum_range_succ',term_zero]
    exact add_comm _ _
  have hh := HasDerivAt.fun_sum (u:=Finset.range (N+1))
    (fun n _ => derivative_succ_of_integrable hi hc ht n)
  have he := (hasDerivAt_const t (1:A)).add hh
  have hfun : ((fun _ : ℝ => (1:A)) + fun s => ∑ n∈Finset.range (N+1),term Ω a (n+1) s) = transport Ω a (N+1) := hf.symm
  rw [hfun] at he
  exact he.congr_deriv (by simp only [zero_add,transport,Finset.mul_sum])

theorem derivative_nilpotent_transport (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ s, Ω s ∈ F.space 1) {a b t : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (hc : ContinuousOn Ω (Ioo a b))
    (ht : t ∈ Ioo a b) :
    HasDerivAt (transport Ω a F.cutoff) (Ω t * transport Ω a F.cutoff t) t := by
  have he : transport Ω a (F.cutoff+1)=transport Ω a F.cutoff := by
    funext s
    simp only [transport,Finset.sum_range_succ,last_term_zero F hΩ,add_zero]
  rw [← he]
  have hd := derivative_transport_of_integrable hi hc ht F.cutoff
  rw [he] at hd
  rw [he]
  exact hd

end FinitePicard

namespace TruncatedWords
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]

abbrev wt : α → ℕ := fun _ => 1

def relations (P : Set (A R α)) (N : ℕ) (x y : A R α) : Prop :=
  y=0 ∧ (x∈P ∨ x∈above wt (N+1))

abbrev Q (P : Set (A R α)) (N : ℕ) := RingQuot (relations P N)

def quotient (P : Set (A R α)) (N : ℕ) : A R α →ₐ[R] Q P N :=
  RingQuot.mkAlgHom R (relations P N)

theorem quotient_above (P : Set (A R α)) (N : ℕ) {p : A R α}
    (hp : p∈above wt (N+1)) : quotient P N p=0 := by
  have h := RingQuot.mkAlgHom_rel (S:=R) (show relations P N p 0 from ⟨rfl,Or.inr hp⟩)
  simpa only [quotient,map_zero] using h

def filtration (P : Set (A R α)) (N n : ℕ) : Submodule R (Q P N) :=
  (above wt n).map (quotient P N).toLinearMap

theorem filtration_antitone (P : Set (A R α)) (N : ℕ) : Antitone (filtration P N) := by
  intro m n h
  exact Submodule.map_mono (space_mono (fun _ hw => le_trans h hw))

theorem filtration_one (P : Set (A R α)) (N : ℕ) : (1 : Q P N)∈filtration P N 0 := by
  refine ⟨1,?_,map_one (quotient P N)⟩
  exact word_mem 1 (by simp)

theorem filtration_mul (P : Set (A R α)) (N m n : ℕ) {x y : Q P N}
    (hx : x∈filtration P N m) (hy : y∈filtration P N n) : x*y∈filtration P N (m+n) := by
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  exact ⟨a*b,above_mul ha hb,map_mul (quotient P N) _ _⟩

theorem filtration_terminal (P : Set (A R α)) (N : ℕ) : filtration P N (N+1)=⊥ := by
  apply eq_bot_iff.mpr
  rintro x ⟨p,hp,rfl⟩
  exact quotient_above P N hp

def fromBelow (P : Set (A R α)) (N : ℕ) : below (R:=R) (wt : α → ℕ) N →ₗ[R] Q P N :=
  (quotient P N).toLinearMap.comp (below wt N).subtype

theorem fromBelow_surjective (P : Set (A R α)) (N : ℕ) : Function.Surjective (fromBelow P N) := by
  classical
  intro x
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations P N) x
  refine ⟨⟨project (fun w => degree wt w≤N) p,project_mem _ _⟩,?_⟩
  change quotient P N (project (fun w => degree wt w≤N) p)=quotient P N p
  have hh : p-project (fun w => degree wt w≤N) p∈above wt (N+1) := by
    apply mem_space
    intro w hw
    by_contra hn
    have hle : degree wt w≤N := by omega
    exact hw (by simp only [MonoidAlgebra.coeff_sub,Finsupp.sub_apply,project_coeff,if_pos hle,sub_self])
  have hz := quotient_above P N hh
  rw [map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

variable [Finite α]

theorem finite_words_below (N : ℕ) : {w : FreeMonoid α | degree wt w≤N}.Finite := by
  apply Set.Finite.subset ((List.finite_length_le α N).image FreeMonoid.ofList)
  intro w hw
  exact ⟨w.toList,by simpa [degree] using hw,by simp⟩

instance finite_below (N : ℕ) : Module.Finite R (below (R:=R) (wt : α → ℕ) N) := by
  let : Fintype {w : FreeMonoid α // degree wt w≤N} := (finite_words_below (α:=α) N).fintype
  exact WordCoordinates.finite_space _

instance finite_quotient (P : Set (A R α)) (N : ℕ) : Module.Finite R (Q P N) :=
  Module.Finite.of_surjective (fromBelow P N) (fromBelow_surjective P N)

variable (P : Set (A ℝ α)) (N : ℕ)

end TruncatedWords
end

namespace TruncatedFree
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]
abbrev wt : α → ℕ := fun _ => 1
abbrev B (R α : Type*) [CommRing R] (N : ℕ) := below (R:=R) (wt : α → ℕ) N

def trunc (N : ℕ) : A R α →ₗ[R] B R α N :=
  (project (fun w => degree wt w≤N)).codRestrict _ (project_mem _)

@[simp] theorem trunc_val (N : ℕ) (p : A R α) :
    (trunc N p).val=project (fun w => degree wt w≤N) p := rfl

theorem trunc_above (N : ℕ) {p : A R α} (hp : p∈above wt (N+1)) : trunc N p=0 := by
  apply Subtype.ext
  exact project_eq_zero hp (by intro w hw hh; change N+1≤degree wt w at hw; omega)

theorem sub_trunc_above (N : ℕ) (p : A R α) : p-(trunc N p).val∈above wt (N+1) := by
  apply mem_space
  intro w hw
  by_contra hn
  have hle : degree wt w≤N := by change ¬N+1≤degree wt w at hn; omega
  exact hw (by simp only [MonoidAlgebra.coeff_sub,Finsupp.sub_apply,trunc_val,project_coeff,if_pos hle,sub_self])

theorem all_ge_zero (p : A R α) : p∈above wt 0 := mem_space (by intros; exact Nat.zero_le _)

theorem trunc_mul_trunc_right (N : ℕ) (p q : A R α) :
    trunc N (p*(trunc N q).val)=trunc N (p*q) := by
  have hh : p*(q-(trunc N q).val)∈above wt (N+1) := by
    simpa only [Nat.zero_add] using above_mul (all_ge_zero p) (sub_trunc_above N q)
  have h := trunc_above N hh
  simp only [mul_sub,map_sub] at h
  exact (sub_eq_zero.mp h).symm

def action (N : ℕ) : A R α →ₐ[R] Module.End R (B R α N) where
  toFun p :=
    { toFun := fun q => trunc N (p*q.val)
      map_add' := by intros; simp only [Submodule.coe_add,mul_add,map_add]
      map_smul' := by intros; simp only [SetLike.val_smul,mul_smul_comm,map_smul,RingHom.id_apply] }
  map_one' := by
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    change (trunc N (1*q.val)).val=q.val
    rw [one_mul,trunc_val,project_eq_self q.property]
  map_mul' p q := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    change (trunc N ((p*q)*u.val)).val=(trunc N (p*(trunc N (q*u.val)).val)).val
    rw [trunc_mul_trunc_right,mul_assoc]
  map_zero' := by ext q; simp
  map_add' p q := by ext u; simp only [add_mul,map_add]; rfl
  commutes' r := by
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    change (trunc N (algebraMap R (A R α) r*q.val)).val=r • q.val
    rw [←Algebra.smul_def,map_smul,SetLike.val_smul,trunc_val,project_eq_self q.property]

def quotientAction (N : ℕ) : TruncatedWords.Q (∅ : Set (A R α)) N →ₐ[R] Module.End R (B R α N) :=
  RingQuot.liftAlgHom R ⟨action N,by
    rintro p q ⟨rfl,hp⟩
    rcases hp with hp|hp
    · exact False.elim hp
    · apply LinearMap.ext
      intro u
      apply Subtype.ext
      change (trunc N (p*u.val)).val=0
      have h : p*u.val∈above wt (N+1) := by
        simpa only [Nat.add_zero] using above_mul hp (all_ge_zero u.val)
      rw [trunc_above N h]
      rfl⟩

def oneVector (N : ℕ) : B R α N := ⟨1,word_mem 1 (by simp)⟩

def normal (N : ℕ) : TruncatedWords.Q (∅ : Set (A R α)) N →ₗ[R] B R α N :=
  (LinearMap.applyₗ (R:=R) (oneVector N)).comp (quotientAction N).toLinearMap

@[simp] theorem normal_quotient (N : ℕ) (p : A R α) :
    normal N (TruncatedWords.quotient ∅ N p)=trunc N p := by
  change (quotientAction N (RingQuot.mkAlgHom R _ p)) (oneVector N)=_
  simp only [quotientAction,RingQuot.liftAlgHom_mkAlgHom_apply]
  change trunc N (p*1)=_
  rw [mul_one]

theorem normal_inverse (N : ℕ) (p : B R α N) :
    normal N (TruncatedWords.fromBelow ∅ N p)=p := by
  change normal N (TruncatedWords.quotient ∅ N p.val)=p
  rw [normal_quotient]
  exact Subtype.ext (project_eq_self p.property)

def equiv (N : ℕ) : TruncatedWords.Q (∅ : Set (A R α)) N ≃ₗ[R] B R α N where
  __ := normal N
  invFun := TruncatedWords.fromBelow ∅ N
  left_inv := by
    intro q
    obtain ⟨p,rfl⟩ := TruncatedWords.fromBelow_surjective ∅ N q
    change TruncatedWords.fromBelow ∅ N (normal N (TruncatedWords.fromBelow ∅ N p))=_
    rw [normal_inverse]
  right_inv := normal_inverse N

@[simp] theorem equiv_eq_normal (N : ℕ) : (equiv (R:=R) (α:=α) N).toLinearMap=normal N := rfl

def coefficient (N : ℕ) (w : FreeMonoid α) : TruncatedWords.Q (∅ : Set (A R α)) N →ₗ[R] R :=
  (Finsupp.lapply w).comp ((MonoidAlgebra.coeffLinearEquiv R).toLinearMap.comp
    ((B R α N).subtype.comp (normal N)))

@[simp] theorem coefficient_quotient (N : ℕ) (w : FreeMonoid α) (p : A R α) :
    coefficient N w (TruncatedWords.quotient ∅ N p)=if degree wt w≤N then p.coeff w else 0 := by
  change (normal N (TruncatedWords.quotient ∅ N p)).val.coeff w=_
  rw [normal_quotient,trunc_val,project_coeff]

end TruncatedFree

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld
namespace AlphabetTransport
open AssociativeElimination UniversalEmbedding
variable {R α β γ : Type*} [CommRing R]

@[simp] theorem renameAssoc_atom (f : α → β) (a : α) : renameAssoc (R:=R) f (atom a)=atom (f a) := by
  simp [renameAssoc]

end AlphabetTransport
namespace QuadraticLeading
open AssociativeElimination UniversalEmbedding WordGrading AlphabetTransport
open RowTwo RowKernel ExactPentagon
abbrev K := ZMod 2
attribute [local instance] LieRing.ofAssociativeRing

def bitOption : Bool ≃ Option Unit where
  toFun := fun b => if b then some () else none
  invFun := fun o => o.isSome
  left_inv b := by cases b <;> rfl
  right_inv o := by cases o with | none => rfl | some u => cases u; rfl

def under : FreeLieAlgebra K Slot →ₗ⁅K⁆ A K Bool := quad.toLieHom.comp embed

@[simp] theorem under_apply (p : FreeLieAlgebra K Slot) : under p=quad (embed p) := rfl

end QuadraticLeading

namespace BaseChangeEquations
open AssociativeEvaluation
variable {R S : Type*} [CommRing R] [CommRing S]

def special (q : FreeLieAlgebra R Bool) : FreeLieAlgebra R Bool :=
  ⁅(x : FreeLieAlgebra R Bool),eval y x q⁆+⁅(-x-y : FreeLieAlgebra R Bool),eval y (-x-y) q⁆

end BaseChangeEquations

namespace ResidualKernel

section
open AssociativeElimination UniversalEmbedding WordGrading RowTwo RowKernel ExactPentagon
abbrev K := ZMod 2
attribute [local instance] LieRing.ofAssociativeRing

end

open AssociativeElimination WordGrading RowTwo RowKernel

attribute [local instance] LieRing.ofAssociativeRing

end ResidualKernel

namespace ProjectionKernel
open AssociativeElimination WordGrading RowTwo RowKernel ExactPentagon QuadraticLeading ResidualKernel
attribute [local instance] LieRing.ofAssociativeRing
abbrev K := ZMod 2

end ProjectionKernel

namespace EliminationGraded
open AssociativeElimination UniversalEmbedding WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]

def collapse : A R (ℕ×α) →ₐ[R] A R (Option α) :=
  lift (fun (n,a) => embed (Elimination.adWord n a))

@[simp] theorem collapse_atom (n : ℕ) (a : α) :
    collapse (atom (n,a) : A R (ℕ×α))=embed (Elimination.adWord n a) := by simp [collapse]

end EliminationGraded

namespace EvenIndex

section
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon AlphabetTransport
attribute [local instance] LieRing.ofAssociativeRing
abbrev K := ZMod 2

def abc : Option Bool ≃ Slot where
  toFun := fun | none => .A | some false => .B | some true => .C
  invFun := fun | .A => none | .B => some false | .C => some true
  left_inv a := by cases a with | none => rfl | some b => cases b <;> rfl
  right_inv a := by cases a <;> rfl

def input : A K (ℕ×Unit) →ₐ[K] A K Bool :=
  (renameAssoc bitOption.symm).comp EliminationGraded.collapse

@[simp] theorem input_atom (n : ℕ) : input (atom (n,()))=
    renameAssoc bitOption.symm (embed (Elimination.adWord n () : Elimination.G K Unit)) := by
  simp [input]

end

open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon AlphabetTransport ProjectionKernel
attribute [local instance] LieRing.ofAssociativeRing

end EvenIndex

namespace PositionalDeletion
open AssociativeElimination WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]
local notation "S" => A R Bool

def replaceWord (u : S) : ℕ → List Bool → S
  | _,[] => 0
  | i,false::w => atom false*replaceWord u i w
  | 0,true::w => u*word (FreeMonoid.ofList w)
  | i+1,true::w => atom true*replaceWord u i w

end PositionalDeletion

namespace GeneratorDeletion

section
open AssociativeElimination WordGrading UniversalEmbedding AlphabetTransport PositionalDeletion QuadraticLeading
attribute [local instance] LieRing.ofAssociativeRing
abbrev K := ZMod 2
abbrev I := ℕ × Unit
abbrev Q := A K I

end

open AssociativeElimination WordGrading UniversalEmbedding
attribute [local instance] LieRing.ofAssociativeRing

def includeAssoc : A K ℕ →ₐ[K] Q := lift (fun n => atom (n+1,()))

end GeneratorDeletion

namespace ImageBound

section
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon AlphabetTransport
attribute [local instance] LieRing.ofAssociativeRing
abbrev K := ZMod 2

def positiveInput : A K ℕ →ₐ[K] A K Bool := EvenIndex.input.comp GeneratorDeletion.includeAssoc

@[simp] theorem positiveInput_atom (n : ℕ) : positiveInput (atom n)=EvenIndex.input (atom (n+1,())) := by
  simp [positiveInput,GeneratorDeletion.includeAssoc]

def eraseLie : FreeLieAlgebra K Slot →ₗ⁅K⁆ FreeLieAlgebra K Bool :=
  FreeLieAlgebra.lift K (fun a => match a with
    | .A => 0 | .B => FreeLieAlgebra.of K true | .C => FreeLieAlgebra.of K false)

def leading (r : ℕ) (p : FreeLieAlgebra K Slot) : FreeLieAlgebra K Bool :=
  eraseLie (LieGrading.piece bCount r p)

end

open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon AlphabetTransport
attribute [local instance] LieRing.ofAssociativeRing

def oddWeight (n : ℕ) : ℕ := 2*(n+1)+1

end ImageBound
end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section

namespace GenericIhara
open AssociativeElimination UniversalEmbedding
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]

def D (p : FreeLieAlgebra R Bool) : LieDerivation R (FreeLieAlgebra R Bool) (FreeLieAlgebra R Bool) :=
  FreeDerivations.extend (fun b => if b then ⁅FreeLieAlgebra.of R true,p⁆ else 0)
def ihara (p q : FreeLieAlgebra R Bool) := D p q-D q p+⁅p,q⁆

end GenericIhara

namespace GenericIhara

section
open AssociativeElimination UniversalEmbedding WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]

def depth : Bool → ℕ := fun b => if b then 1 else 0

end

open LieAlgebra
variable {R : Type*} [CommRing R]
local notation "FL" => FreeLieAlgebra R Bool
local notation "Der" => LieDerivation R FL FL

@[simp] theorem D_zero : D (0 : FL)=0 := by
  apply FreeDerivations.ext
  intro b
  cases b <;> simp [D]

@[simp] theorem D_add (p q : FL) : D (p+q)=D p+D q := by
  apply FreeDerivations.ext
  intro b
  cases b <;> simp [D,lie_add]

@[simp] theorem D_smul (c : R) (p : FL) : D (c • p)=c • D p := by
  apply FreeDerivations.ext
  intro b
  cases b <;> simp [D,lie_smul]

@[simp] theorem D_of_false (p : FL) : D p (FreeLieAlgebra.of R false)=0 := by simp [D]
@[simp] theorem D_of_true (p : FL) : D p (FreeLieAlgebra.of R true)=⁅FreeLieAlgebra.of R true,p⁆ := by simp [D]

theorem D_ihara (p q : FL) : D (ihara p q)=⁅D p,D q⁆ := by
  apply FreeDerivations.ext
  intro b
  cases b with
  | false => simp
  | true =>
    simp only [D_of_true,LieDerivation.lie_apply,LieDerivation.apply_lie_eq_add]
    simp only [ihara,lie_add,lie_sub]
    rw [leibniz_lie,←lie_skew p ⁅FreeLieAlgebra.of R true,q⁆]
    abel

abbrev Ambient (R : Type*) [CommRing R] :=
  SemiDirectSum (FreeLieAlgebra R Bool) (LieDerivation R (FreeLieAlgebra R Bool) (FreeLieAlgebra R Bool)) LieHom.id

def graph : LieSubalgebra R (Ambient R) where
  carrier := {p | p.right=D p.left}
  zero_mem' := D_zero.symm
  add_mem' := by
    intro p q hp hq
    change p.right+q.right=D (p.left+q.left)
    rw [D_add,hp,hq]
  smul_mem' := by
    intro c p hp
    change c • p.right=D (c • p.left)
    rw [D_smul,hp]
  lie_mem' := by
    intro p q hp hq
    change ⁅p.right,q.right⁆=D (⁅p.left,q.left⁆+p.right q.left-q.right p.left)
    rw [hp,hq,←D_ihara]
    congr 1
    unfold ihara
    abel

abbrev Algebra (R : Type*) [CommRing R] := graph (R:=R)

def erase : Algebra R ≃ₗ[R] FL where
  toFun p := p.val.left
  invFun p := ⟨⟨p,D p⟩,rfl⟩
  left_inv p := by
    apply Subtype.ext
    change (⟨p.val.left,D p.val.left⟩ : Ambient R)=p.val
    apply SemiDirectSum.ext
    · rfl
    · exact p.property.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {α : Type*}

def lift (f : α → FL) : FreeLieAlgebra R α →ₗ⁅R⁆ Algebra R :=
  FreeLieAlgebra.lift R (fun a => erase.symm (f a))

def evalIhara (f : α → FL) : FreeLieAlgebra R α →ₗ[R] FL := erase.toLinearMap.comp (lift f).toLinearMap

@[simp] theorem evalIhara_of (f : α → FL) (a : α) : evalIhara f (FreeLieAlgebra.of R a)=f a := by
  simp [evalIhara,lift]

end GenericIhara

namespace LieDimension
open AssociativeElimination UniversalEmbedding WordGrading
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {α : Type*}
variable (R : Type*) [CommRing R] (wt : α → ℕ) (n : ℕ)

abbrev Words := {w : FreeMonoid α // degree wt w=n}

def toWords : LieGrading.homogeneousLie (R:=R) wt n →ₗ[R] homogeneous (R:=R) wt n :=
  ((embed (R:=R) (α:=α)).toLinearMap.comp (LieGrading.homogeneousLie wt n).subtype).codRestrict
    (homogeneous wt n) (fun p => LieGrading.homogeneousLie_embed p.property)

def coordinates : LieGrading.homogeneousLie (R:=R) wt n →ₗ[R] (Words wt n → R) :=
  (WordCoordinates.coordinates (fun w => degree wt w=n)).comp (toWords R wt n)

@[simp] theorem coordinates_apply (p : LieGrading.homogeneousLie (R:=R) wt n) (w : Words wt n) :
    coordinates R wt n p w=(embed p.val).coeff w.val := rfl

variable {R wt n}

variable (F : Type*) [Field F] (wt : α → ℕ) (n : ℕ) [Fintype (Words wt n)]

end LieDimension

namespace LieGrading
open AssociativeElimination UniversalEmbedding WordGrading
variable {R α : Type*} [CommRing R]

@[simp] theorem piece_add (wt : α → ℕ) (n : ℕ) (p q : FreeLieAlgebra R α) :
    piece wt n (p+q)=piece wt n p+piece wt n q := by
  apply UniversalEmbedding.injective
  simp only [embed_piece,map_add]

@[simp] theorem piece_smul (wt : α → ℕ) (n : ℕ) (c : R) (p : FreeLieAlgebra R α) :
    piece wt n (c • p)=c • piece wt n p := by
  apply UniversalEmbedding.injective
  simp only [embed_piece,map_smul]

def biPiece (wa wb : α → ℕ) (n r : ℕ) : Submodule R (FreeLieAlgebra R α) :=
  homogeneousLie wa n ⊓ homogeneousLie wb r

variable (F : Type*) [Field F]

end LieGrading
end

section
namespace BaseChangeEquations
variable {R : Type*} [CommRing R]

def antisymmetryMap : FreeLieAlgebra R Bool →ₗ[R] FreeLieAlgebra R Bool :=
  LinearMap.id+(eval y x).toLinearMap

def specialMap : FreeLieAlgebra R Bool →ₗ[R] FreeLieAlgebra R Bool :=
  (LieAlgebra.ad R _ x).comp (eval y x).toLinearMap+
    (LieAlgebra.ad R _ (-x-y)).comp (eval y (-x-y)).toLinearMap

def pentagonMap : FreeLieAlgebra R Bool →ₗ[R] GenericBraid.T R (Fin 4) :=
  let t := GenericBraid.t (R:=R)
  (eval (t 0 1) (t 1 2+t 1 3)).toLinearMap+(eval (t 0 2+t 1 2) (t 2 3)).toLinearMap-
    (eval (t 1 2) (t 2 3)).toLinearMap-(eval (t 0 1+t 0 2) (t 1 3+t 2 3)).toLinearMap-
    (eval (t 0 1) (t 1 2)).toLinearMap

@[simp] theorem antisymmetryMap_apply (p : FreeLieAlgebra R Bool) : antisymmetryMap p=antisymmetry p := rfl
@[simp] theorem specialMap_apply (p : FreeLieAlgebra R Bool) : specialMap p=special p := rfl
@[simp] theorem pentagonMap_apply (p : FreeLieAlgebra R Bool) : pentagonMap p=pentagon p := rfl

end BaseChangeEquations
namespace ReducedDimension
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon ImageBound
attribute [local instance] LieRing.ofAssociativeRing
abbrev K := ZMod 2

def solutions (n : ℕ) : Submodule K (FreeLieAlgebra K Bool) :=
  LieGrading.homogeneousLie (fun _ => 1) n ⊓ BaseChangeEquations.antisymmetryMap.ker ⊓
    BaseChangeEquations.specialMap.ker ⊓ BaseChangeEquations.pentagonMap.ker

end ReducedDimension

open AssociativeElimination UniversalEmbedding WordGrading
open scoped TensorProduct

namespace LieGrading
variable {α : Type*} {wt : α → ℕ}

theorem weightedWord_tree {n : ℕ} {p : FreeLieAlgebra ℚ α} (hp : WeightedWord wt n p) :
    ∃ t : UniversalEmbedding.Tree α,treeDegree wt t=n ∧ t.eval=p := by
  induction hp with
  | generator a => exact ⟨.leaf a,rfl,rfl⟩
  | bracket hp hq hi hj =>
    obtain ⟨t,ht,rfl⟩ := hi
    obtain ⟨u,hu,rfl⟩ := hj
    exact ⟨.node t u,by simp only [treeDegree_node,ht,hu],rfl⟩

theorem tree_weightedWord (t : UniversalEmbedding.Tree α) : WeightedWord wt (treeDegree wt t) t.eval := by
  induction t with
  | leaf a => exact .generator a
  | node t u ht hu => simpa only [treeDegree_node,UniversalEmbedding.Tree.eval] using WeightedWord.bracket ht hu

theorem weightPiece_eq (wt : α → ℕ) (n : ℕ) : weightPiece wt n=homogeneousLie (R:=ℚ) wt n := by
  unfold weightPiece homogeneousLie
  congr 1
  ext p
  constructor
  · exact weightedWord_tree
  · rintro ⟨t,ht,rfl⟩
    rw [←ht]
    exact tree_weightedWord t

end LieGrading
namespace RationalBound
open ReducedDimension
abbrev wt : Bool → ℕ := fun _ => 1
abbrev Words (n : ℕ) := LieDimension.Words wt n

def toHom (n : ℕ) : Wn n →ₗ[ℚ] LieGrading.homogeneousLie (R:=ℚ) wt n :=
  (Wn n).subtype.codRestrict _ (fun p => by
    rw [←LieGrading.weightPiece_eq]
    exact p.property.2)

def coordinates (n : ℕ) : Wn n →ₗ[ℚ] (Words n → ℚ) :=
  (LieDimension.coordinates ℚ wt n).comp (toHom n)

end RationalBound
end

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace GenericIhara
open AssociativeElimination UniversalEmbedding WordGrading LieGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]

def depthOneWord (n : ℕ) : FreeMonoid Bool := FreeMonoid.of false^n*FreeMonoid.of true

end GenericIhara

namespace CutoffDepth
open AssociativeElimination WordGrading
variable {R : Type*} [CommRing R]

abbrev Q (R : Type*) [CommRing R] (N : ℕ) := TruncatedWords.Q (∅ : Set (A R Bool)) N
abbrev quotient (N : ℕ) : A R Bool →ₐ[R] Q R N := TruncatedWords.quotient ∅ N
def gen (N : ℕ) (b : Bool) : Q R N := quotient N (atom b)
abbrev coeff (N : ℕ) (w : FreeMonoid Bool) : Q R N →ₗ[R] R := TruncatedFree.coefficient N w

@[simp] theorem degree_pow (wt : Bool → ℕ) (w : FreeMonoid Bool) (n : ℕ) :
    degree wt (w^n)=n*degree wt w := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ,degree_mul,ih]; ring

@[simp] theorem length_depthOne (m : ℕ) :
    degree TruncatedWords.wt (GenericIhara.depthOneWord m)=m+1 := by
  simp [GenericIhara.depthOneWord,TruncatedWords.wt]

theorem depth_le_length (w : FreeMonoid Bool) :
    degree GenericIhara.depth w≤degree TruncatedWords.wt w := by
  induction w using FreeMonoid.inductionOn with
  | one => simp
  | of b => cases b <;> decide
  | mul u v hu hv => simp only [degree_mul]; omega

def depthSpace (N n : ℕ) : Submodule R (Q R N) :=
  (above GenericIhara.depth n).map (quotient N).toLinearMap

theorem depth_antitone (N : ℕ) : Antitone (depthSpace (R:=R) N) := by
  intro m n h
  exact Submodule.map_mono (space_mono (fun _ hw => le_trans h hw))

theorem depth_one (N : ℕ) : (1:Q R N)∈depthSpace N 0 := by
  exact ⟨1,word_mem 1 (by simp),map_one (quotient N)⟩

theorem depth_mul (N m n : ℕ) {p q : Q R N} (hp : p∈depthSpace N m) (hq : q∈depthSpace N n) :
    p*q∈depthSpace N (m+n) := by
  obtain ⟨a,ha,rfl⟩ := hp
  obtain ⟨b,hb,rfl⟩ := hq
  exact ⟨a*b,above_mul ha hb,map_mul (quotient N) _ _⟩

theorem depth_terminal (N : ℕ) : depthSpace (R:=R) N (N+1)=⊥ := by
  apply eq_bot_iff.mpr
  rintro q ⟨p,hp,rfl⟩
  apply TruncatedWords.quotient_above
  exact space_mono (fun w hw => le_trans hw (depth_le_length w)) hp

theorem gen_depth (N : ℕ) (b : Bool) : gen (R:=R) N b∈depthSpace N (GenericIhara.depth b) := by
  refine ⟨atom b,?_,rfl⟩
  exact word_mem (FreeMonoid.of b) (by simp)

theorem gen_weight (N : ℕ) (b : Bool) : gen (R:=R) N b∈TruncatedWords.filtration ∅ N 1 := by
  refine ⟨atom b,?_,rfl⟩
  exact word_mem (FreeMonoid.of b) (by simp [TruncatedWords.wt])

theorem coeff_zero_of_depth (N n : ℕ) {p : Q R N} (hp : p∈depthSpace N n)
    {w : FreeMonoid Bool} (hw : degree GenericIhara.depth w<n) : coeff N w p=0 := by
  obtain ⟨a,ha,rfl⟩ := hp
  change TruncatedFree.coefficient N w (TruncatedWords.quotient ∅ N a)=0
  rw [TruncatedFree.coefficient_quotient]
  have hz : a.coeff w=0 := coeff_support ha w (not_le.mpr hw)
  split <;> simp only [hz]

theorem left_power_match (i m : ℕ) (v : FreeMonoid Bool) :
    FreeMonoid.of false^i*v=GenericIhara.depthOneWord m ↔
      i ≤ m ∧ v=GenericIhara.depthOneWord (m-i) := by
  induction i generalizing m v with
  | zero => simp
  | succ i ih =>
    cases m with
    | zero =>
      have hn : FreeMonoid.of false^(i+1)*v≠GenericIhara.depthOneWord 0 := by
        intro h
        have hh := congrArg FreeMonoid.toList h
        simp [pow_succ',mul_assoc,GenericIhara.depthOneWord] at hh
      simp [hn]
    | succ m =>
      have he : FreeMonoid.of false^(i+1)*v=GenericIhara.depthOneWord (m+1) ↔
          FreeMonoid.of false^i*v=GenericIhara.depthOneWord m := by
        simp only [pow_succ',GenericIhara.depthOneWord,mul_assoc,mul_left_cancel_iff]
      rw [he,ih]
      simp only [Nat.succ_le_succ_iff,Nat.succ_sub_succ_eq_sub]

theorem coeff_prefix (N i m : ℕ) (hN : m+1≤N) (p : Q R N) :
    coeff N (GenericIhara.depthOneWord m) (gen N false^i*p)=
      if i ≤ m then coeff N (GenericIhara.depthOneWord (m-i)) p else 0 := by
  classical
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective R (TruncatedWords.relations (∅ : Set (A R Bool)) N) p
  change coeff N (GenericIhara.depthOneWord m) (quotient N (atom false)^i*quotient N a)=_
  rw [←map_pow,←map_mul,TruncatedFree.coefficient_quotient,if_pos (by simpa using hN)]
  have he : atom (R:=R) false^i=MonoidAlgebra.single (FreeMonoid.of false^i) 1 := by
    simp [atom,MonoidAlgebra.single_pow]
  rw [he]
  split_ifs with hi
  · rw [MonoidAlgebra.coeff_single_mul_eq_mul_coeff (GenericIhara.depthOneWord (m-i))
      (fun _ _ => by rw [left_power_match]; simp only [hi,true_and]),one_mul]
    change _=TruncatedFree.coefficient N (GenericIhara.depthOneWord (m-i)) (TruncatedWords.quotient ∅ N a)
    rw [TruncatedFree.coefficient_quotient,if_pos (by simp only [length_depthOne]; omega)]
  · exact MonoidAlgebra.coeff_single_mul_of_forall_mul_ne 1 a
      (fun v hv => hi ((left_power_match i m v).mp hv).1)

theorem middle_power_match (i j m : ℕ) :
    FreeMonoid.of false^i*FreeMonoid.of true*FreeMonoid.of false^j=GenericIhara.depthOneWord m ↔
      i=m ∧ j=0 := by
  rw [mul_assoc,left_power_match]
  constructor
  · rintro ⟨hi,h⟩
    have hm : m-i=0 := by
      cases he : m-i with
      | zero => rfl
      | succ k =>
        have hh := congrArg FreeMonoid.toList h
        simp [GenericIhara.depthOneWord,he,pow_succ',mul_assoc] at hh
    have him : i=m := by omega
    subst i
    simp only [Nat.sub_self,GenericIhara.depthOneWord,pow_zero,one_mul,mul_eq_left] at h
    have hd := congrArg (degree TruncatedWords.wt) h
    simp only [degree_pow,degree_of,TruncatedWords.wt,mul_one,degree_one] at hd
    exact ⟨rfl,hd⟩
  · rintro ⟨rfl,rfl⟩
    simp [GenericIhara.depthOneWord]

theorem coeff_monomial (N i j m : ℕ) (hN : m+1 ≤ N) :
    coeff N (GenericIhara.depthOneWord m) (gen (R:=R) N false^i*gen N true*gen N false^j)=
      if i=m ∧ j=0 then 1 else 0 := by
  classical
  change coeff N (GenericIhara.depthOneWord m)
    (quotient N (atom false)^i*quotient N (atom true)*quotient N (atom false)^j)=_
  rw [←map_pow,←map_pow,←map_mul,←map_mul,TruncatedFree.coefficient_quotient,
    if_pos (by simpa using hN)]
  simp only [atom,MonoidAlgebra.single_pow,one_pow,MonoidAlgebra.single_mul_single,one_mul]
  simp only [MonoidAlgebra.coeff_single,Finsupp.single_apply,middle_power_match]

theorem coeff_Y_prefix (N i m : ℕ) (hN : m+1 ≤ N) (hm : 0 < m) (p : Q R N) :
    coeff N (GenericIhara.depthOneWord m) (gen N true^i*p)=
      if i=0 then coeff N (GenericIhara.depthOneWord m) p else 0 := by
  classical
  cases i with
  | zero => simp
  | succ i =>
    simp only [Nat.succ_ne_zero,↓reduceIte]
    obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective R (TruncatedWords.relations (∅ : Set (A R Bool)) N) p
    change coeff N (GenericIhara.depthOneWord m) (quotient N (atom true)^(i+1)*quotient N a)=0
    rw [←map_pow,←map_mul,TruncatedFree.coefficient_quotient,if_pos (by simpa using hN)]
    have he : atom (R:=R) true^(i+1)=MonoidAlgebra.single (FreeMonoid.of true^(i+1)) 1 := by
      simp [atom,MonoidAlgebra.single_pow]
    rw [he]
    apply MonoidAlgebra.coeff_single_mul_of_forall_mul_ne
    intro v hv
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    have hh := congrArg FreeMonoid.toList hv
    simp [pow_succ',GenericIhara.depthOneWord,mul_assoc] at hh

end CutoffDepth

section
namespace LogCollar
open MeasureTheory Set Filter
open scoped Topology

theorem intervalIntegrable_of_at_zero {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (h0 : IntegrableAtFilter f (𝓝[>] 0) volume)
    (hc : ContinuousOn f (Ioi 0)) {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable f volume 0 b := by
  obtain rfl | hb := hb.eq_or_lt
  · exact IntervalIntegrable.refl
  obtain ⟨s,hs,hi⟩ := h0
  obtain ⟨c,hc0,hcs⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hs
  apply IntervalIntegrable.trans (b:=c)
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hc0.le).mpr (hi.mono_set hcs)
  · apply ContinuousOn.intervalIntegrable
    exact hc.mono (by
      intro x hx
      have hle : min c b ≤ x := hx.1
      exact lt_of_lt_of_le (lt_min hc0 hb) hle)

theorem log_pow_at_zero (n : ℕ) :
    IntegrableAtFilter (fun x : ℝ => Real.log x ^ n) (𝓝[>] 0) volume := by
  have ho : (fun x : ℝ => ‖Real.log x ^ n‖) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(1/2):ℝ)) := by
    simpa only [norm_pow,Real.norm_eq_abs,Real.rpow_natCast] using
      (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (n:ℝ) (by norm_num : (-(1/2):ℝ)<0)).isBigO
  apply ho.of_norm_left.integrableAtFilter
  · exact (Real.measurable_log.pow_const n).stronglyMeasurable.stronglyMeasurableAtFilter
  · refine ⟨Ioc 0 1,Ioc_mem_nhdsGT (by norm_num),?_⟩
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ)< -(1/2)))

theorem log_pow (n : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun x : ℝ => Real.log x ^ n) volume 0 b := by
  apply intervalIntegrable_of_at_zero (log_pow_at_zero n) _ hb
  exact (Real.continuousOn_log.mono (by intro x hx; exact ne_of_gt hx)).pow n

end LogCollar

namespace KZCollar
open MeasureTheory Set Filter FinitePicard
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def gauge (X : A) (s : ℝ) : A := NormedSpace.exp (Real.log s • X)

def regularForm (X Y : A) (s : ℝ) : A :=
  gauge (-X) s * ((s-1)⁻¹ • Y) * gauge X s

theorem exp_smul_finite (X : A) {N : ℕ} (hX : X^(N+1)=0) (t : ℝ) :
    NormedSpace.exp (t • X)=∑ i∈Finset.range (N+1),
      (t^i / (i.factorial : ℝ)) • X^i := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  simp only [smul_pow,smul_smul]
  have hh : ∀ i∉Finset.range (N+1),((i.factorial : ℝ)⁻¹*t^i) • X^i=0 := by
    intro i hi
    have hi : N + 1 ≤ i := Nat.le_of_not_lt (by simpa using hi)
    rw [pow_eq_zero_of_le hi hX,smul_zero]
  rw [tsum_eq_sum hh]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

theorem gauge_finite (X : A) {N : ℕ} (hX : X^(N+1)=0) (s : ℝ) :
    gauge X s=∑ i∈Finset.range (N+1),
      (Real.log s^i / (i.factorial : ℝ)) • X^i := exp_smul_finite X hX _

variable [CompleteSpace A]

theorem gauge_neg_mul (X : A) (s : ℝ) : gauge (-X) s*gauge X s=1 := by
  let := NormedAlgebra.restrictScalars ℚ ℝ A
  unfold gauge
  rw [smul_neg,←NormedSpace.exp_add_of_commute (Commute.refl _).neg_left,neg_add_cancel,
    NormedSpace.exp_zero]

theorem gauge_mul_neg (X : A) (s : ℝ) : gauge X s*gauge (-X) s=1 := by
  let := NormedAlgebra.restrictScalars ℚ ℝ A
  unfold gauge
  rw [smul_neg,←NormedSpace.exp_add_of_commute (Commute.refl _).neg_right,add_neg_cancel,
    NormedSpace.exp_zero]

theorem gauge_derivative (X : A) {s : ℝ} (hs : s≠0) :
    HasDerivAt (gauge X) (s⁻¹ • (X*gauge X s)) s := by
  exact (hasDerivAt_exp_smul_const' X (Real.log s)).scomp s (Real.hasDerivAt_log hs)

omit [CompleteSpace A] in
theorem regularForm_finite (X Y : A) {N : ℕ} (hX : X^(N+1)=0) (s : ℝ) :
    regularForm X Y s=∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
      ((Real.log s)^(i+j) * ((-1:ℝ)^i / ((i.factorial:ℝ)*(j.factorial:ℝ))) * (s-1)⁻¹) • (X^i*Y*X^j) := by
  have hnX : (-X)^(N+1)=0 := by rw [neg_pow,hX,mul_zero]
  unfold regularForm
  rw [gauge_finite (-X) hnX,gauge_finite X hX]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [neg_pow]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
  have hp : (-1:A)^i*X^i*Y*X^j=(-1:ℝ)^i • (X^i*Y*X^j) := by
    simp only [Algebra.smul_def,map_pow,map_neg,map_one]
    noncomm_ring
  rw [hp,smul_smul]
  congr 1
  rw [pow_add]
  ring

omit [CompleteSpace A] in

theorem regularForm_integrable (X Y : A) {N : ℕ} (hX : X^(N+1)=0)
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1) :
    IntervalIntegrable (regularForm X Y) volume 0 b := by
  have hc : ContinuousOn (fun s : ℝ => (s-1)⁻¹) (uIcc 0 b) := by
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro s hs
    rw [uIcc_of_le hb] at hs
    exact ne_of_lt (sub_neg.mpr (lt_of_le_of_lt hs.2 hb1))
  have h : regularForm X Y = fun s => ∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
      ((Real.log s)^(i+j) * ((-1:ℝ)^i / ((i.factorial:ℝ)*(j.factorial:ℝ))) * (s-1)⁻¹) • (X^i*Y*X^j) := by
    funext s
    exact regularForm_finite X Y hX s
  rw [h]
  have hh (i j : ℕ) : IntervalIntegrable (fun s =>
      ((Real.log s)^(i+j) * ((-1:ℝ)^i / ((i.factorial:ℝ)*(j.factorial:ℝ))) * (s-1)⁻¹) • (X^i*Y*X^j)) volume 0 b :=
    (((LogCollar.log_pow (i+j) hb).mul_const _).mul_continuousOn hc).smul_continuousOn
      continuousOn_const
  have hz := IntervalIntegrable.sum (ε:=A) (Finset.range (N+1))
    (fun i _ => IntervalIntegrable.sum (ε:=A) (Finset.range (N+1)) (fun j _ => hh i j))
  have he : (∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),fun s =>
      ((Real.log s)^(i+j) * ((-1:ℝ)^i / ((i.factorial:ℝ)*(j.factorial:ℝ))) * (s-1)⁻¹) • (X^i*Y*X^j)) =
      (fun s => ∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
      ((Real.log s)^(i+j) * ((-1:ℝ)^i / ((i.factorial:ℝ)*(j.factorial:ℝ))) * (s-1)⁻¹) • (X^i*Y*X^j)) := by
    ext s
    simp only [Finset.sum_apply]
  rw [he] at hz
  exact hz

theorem regularForm_continuous (X Y : A) {b : ℝ} (hb : b ≤ 1) :
    ContinuousOn (regularForm X Y) (Ioo 0 b) := by
  intro s hs
  have hg : ∀ Z : A, ContinuousAt (gauge Z) s := fun Z =>
    (gauge_derivative Z (ne_of_gt hs.1)).continuousAt
  have hinv : ContinuousAt (fun s : ℝ => (s-1)⁻¹) s := by
    apply (continuousAt_id.sub continuousAt_const).inv₀
    exact ne_of_lt (sub_neg.mpr (lt_of_lt_of_le hs.2 hb))
  exact (((hg (-X)).mul (hinv.smul continuousAt_const)).mul (hg X)).continuousWithinAt

omit [CompleteSpace A] in
theorem regularForm_mem (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) (s : ℝ) :
    regularForm X Y s ∈ F.space 1 := by
  rw [regularForm_finite X Y (pow_cutoff_eq_zero F hX)]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  apply F.antitone (by omega : 1 ≤ i+1+j)
  exact F.mul_mem (i+1) j (F.mul_mem i 1 (pow_mem F hX i) hY) (pow_mem F hX j)

def normalizedSolution (F : NilpotentFiltration A) (X Y : A) (s : ℝ) : A :=
  gauge X s * transport (regularForm X Y) 0 F.cutoff s

variable [FiniteDimensional ℝ A]

theorem normalizedSolution_derivative (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) {b s : ℝ}
    (hb : b < 1) (hs : s ∈ Ioo 0 b) :
    HasDerivAt (normalizedSolution F X Y)
      ((s⁻¹ • X + (s-1)⁻¹ • Y) * normalizedSolution F X Y s) s := by
  have hreg := regularForm_integrable X Y (pow_cutoff_eq_zero F hX)
    (le_trans hs.1.le hs.2.le) hb
  have hsol := derivative_nilpotent_transport F (regularForm_mem F hX hY)
    hreg (regularForm_continuous X Y hb.le) hs
  apply ((gauge_derivative X (ne_of_gt hs.1)).mul hsol).congr_deriv
  let P := transport (regularForm X Y) 0 F.cutoff s
  change (s⁻¹ • (X*gauge X s))*P +
    gauge X s*((gauge (-X) s*((s-1)⁻¹ • Y)*gauge X s)*P) =
    (s⁻¹ • X+(s-1)⁻¹ • Y)*(gauge X s*P)
  rw [←mul_assoc (gauge X s),←mul_assoc (gauge X s),←mul_assoc (gauge X s),gauge_mul_neg,one_mul]
  simp only [add_mul,smul_mul_assoc,mul_assoc]

omit [FiniteDimensional ℝ A] in
theorem normalizedSolution_limit (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Tendsto (fun s => gauge (-X) s * normalizedSolution F X Y s)
      (𝓝[>] 0) (𝓝 (1:A)) := by
  have hh : (fun s => gauge (-X) s * normalizedSolution F X Y s) =
      transport (regularForm X Y) 0 F.cutoff := by
    funext s
    simp only [normalizedSolution,←mul_assoc,gauge_neg_mul,one_mul]
  rw [hh]
  have h := collar_limit (regularForm_integrable X Y (pow_cutoff_eq_zero F hX) hb.le hb1) F.cutoff
  rw [uIcc_of_le hb.le] at h
  rw [nhdsWithin_Icc_eq_nhdsGE hb] at h
  exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

end KZCollar

namespace FinitePicard
open MeasureTheory Set intervalIntegral
open scoped Ring
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

variable [FiniteDimensional ℝ A]

theorem transport_sub_one_mem (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ t, Ω t ∈ F.space 1) (a t : ℝ) (N : ℕ) :
    transport Ω a N t-1 ∈ F.space 1 := by
  simp only [transport,Finset.sum_range_succ',term_zero,add_sub_cancel_right]
  apply Submodule.sum_mem
  intro n hn
  exact F.antitone (by omega : 1 ≤ n+1) (term_mem F hΩ a (n+1) t)

theorem transport_isUnit (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ t, Ω t ∈ F.space 1) (a t : ℝ) (N : ℕ) :
    IsUnit (transport Ω a N t) := by
  have hn : IsNilpotent (transport Ω a N t-1) :=
    ⟨F.cutoff+1,pow_cutoff_eq_zero F (transport_sub_one_mem F hΩ a t N)⟩
  simpa only [sub_add_cancel] using hn.isUnit_add_one

omit [FiniteDimensional ℝ A] in
theorem inverse_derivative [CompleteSpace A] {f : ℝ → A} {f' : A} {s : ℝ}
    (hf : HasDerivAt f f' s) (hu : IsUnit (f s)) :
    HasDerivAt (fun s => Ring.inverse (f s)) (-(Ring.inverse (f s)*f'*Ring.inverse (f s))) s := by
  have h := hasFDerivAt_ringInverse (𝕜:=ℝ) hu.unit
  rw [hu.unit_spec] at h
  have hh := h.comp_hasDerivAt s hf
  simpa only [neg_apply,ContinuousLinearMap.mulLeftRight_apply,
    ←Ring.inverse_of_isUnit hu] using! hh

omit [FiniteDimensional ℝ A] in

theorem transition_derivative [CompleteSpace A] {f g Ω : ℝ → A} {s : ℝ}
    (hf : HasDerivAt f (Ω s*f s) s) (hg : HasDerivAt g (Ω s*g s) s)
    (hu : IsUnit (f s)) :
    HasDerivAt (fun s => Ring.inverse (f s)*g s) 0 s := by
  apply ((inverse_derivative hf hu).mul hg).congr_deriv
  simp only [mul_assoc,neg_mul]
  rw [←mul_assoc (f s),Ring.mul_inverse_cancel _ hu,one_mul,neg_add_cancel]

omit [FiniteDimensional ℝ A] in
theorem transition_constant [CompleteSpace A] {f g Ω : ℝ → A} {a b u v : ℝ}
    (hf : ∀ s ∈ Ioo a b, HasDerivAt f (Ω s*f s) s)
    (hg : ∀ s ∈ Ioo a b, HasDerivAt g (Ω s*g s) s)
    (hu : ∀ s ∈ Ioo a b, IsUnit (f s)) (huv : u ∈ Ioo a b) (hvv : v ∈ Ioo a b) :
    Ring.inverse (f u)*g u=Ring.inverse (f v)*g v := by
  have hh : ∀ s ∈ Ioo a b, HasDerivAt (fun s => Ring.inverse (f s)*g s) 0 s :=
    fun s hs => transition_derivative (hf s hs) (hg s hs) (hu s hs)
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun s hs => (hh s hs).differentiableAt.differentiableWithinAt) _ huv hvv
  intro s hs
  exact (hh s hs).deriv

end FinitePicard

namespace KZCollar
open MeasureTheory Set Filter FinitePicard
open scoped Topology Ring
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def bulkForm (X Y : A) (s : ℝ) : A := s⁻¹ • X+(s-1)⁻¹ • Y

def gaugeUnit (X : A) (s : ℝ) : Aˣ where
  val := gauge X s
  inv := gauge (-X) s
  val_inv := gauge_mul_neg X s
  inv_val := gauge_neg_mul X s

variable [FiniteDimensional ℝ A]

theorem normalizedSolution_isUnit (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) (s : ℝ) :
    IsUnit (normalizedSolution F X Y s) :=
  (gaugeUnit X s).isUnit.mul (transport_isUnit F (regularForm_mem F hX hY) 0 s F.cutoff)

theorem normalizedSolution_derivative_on (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) {s : ℝ} (hs : s ∈ Ioo 0 1) :
    HasDerivAt (normalizedSolution F X Y)
      (bulkForm X Y s * normalizedSolution F X Y s) s := by
  apply normalizedSolution_derivative F hX hY (b:=(s+1)/2)
  · linarith [hs.2]
  · exact ⟨hs.1,by linarith [hs.2]⟩

def rightSolution (F : NilpotentFiltration A) (X Y : A) (s : ℝ) : A :=
  normalizedSolution F Y X (1-s)

theorem rightSolution_isUnit (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) (s : ℝ) :
    IsUnit (rightSolution F X Y s) := normalizedSolution_isUnit F hY hX (1-s)

theorem rightSolution_derivative (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) {s : ℝ} (hs : s ∈ Ioo 0 1) :
    HasDerivAt (rightSolution F X Y)
      (bulkForm X Y s*rightSolution F X Y s) s := by
  have ht : 1-s ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hd := (normalizedSolution_derivative_on F hY hX ht).scomp s
    ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s))
  apply hd.congr_deriv
  change (0-1:ℝ) • (bulkForm Y X (1-s)*rightSolution F X Y s) = _
  have h1 : 1-s= -(s-1) := by ring
  have h2 : 1-s-1= -s := by ring
  dsimp only [bulkForm]
  rw [h2,h1]
  simp only [inv_neg,zero_sub,neg_smul,one_smul,neg_add_rev,neg_neg,neg_mul,add_mul]

def associator (F : NilpotentFiltration A) (X Y : A) : A :=
  Ring.inverse (rightSolution F X Y (1/2))*normalizedSolution F X Y (1/2)

theorem associator_is_transition (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) {s : ℝ} (hs : s ∈ Ioo 0 1) :
    Ring.inverse (rightSolution F X Y s)*normalizedSolution F X Y s=associator F X Y := by
  exact transition_constant (fun _ ht => rightSolution_derivative F hX hY ht)
    (fun _ ht => normalizedSolution_derivative_on F hX hY ht)
    (fun t _ => rightSolution_isUnit F hX hY t) hs (by constructor <;> norm_num)

theorem left_eq_right_mul_associator (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) {s : ℝ} (hs : s ∈ Ioo 0 1) :
    normalizedSolution F X Y s=rightSolution F X Y s*associator F X Y := by
  rw [←associator_is_transition F hX hY hs]
  exact (Ring.mul_inverse_cancel_left _ _ (rightSolution_isUnit F hX hY s)).symm

end KZCollar

namespace KZCollar
open MeasureTheory Set Filter FinitePicard
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A]

omit [FiniteDimensional ℝ A] in
theorem regularTransport_limit (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) :
    Tendsto (transport (regularForm X Y) 0 F.cutoff) (𝓝[>] 0) (𝓝 (1:A)) := by
  have h := normalizedSolution_limit (Y:=Y) F hX (b:=1/2) (by norm_num) (by norm_num)
  simpa only [normalizedSolution,←mul_assoc,gauge_neg_mul,one_mul] using h

end KZCollar
end

namespace DepthIntegral
open MeasureTheory Set Filter intervalIntegral
open scoped Topology

def kernel (m : ℕ) (s : ℝ) : ℝ := (-Real.log s)^m/(1-s)

theorem kernel_left (m : ℕ) {b : ℝ} (h0 : 0≤b) (h1 : b<1) :
    IntervalIntegrable (kernel m) volume 0 b := by
  have hl := (LogCollar.log_pow m h0).const_mul ((-1:ℝ)^m)
  have hc : ContinuousOn (fun s : ℝ => (1-s)⁻¹) (uIcc 0 b) := by
    apply (continuousOn_const.sub continuousOn_id).inv₀
    intro s hs
    rw [uIcc_of_le h0] at hs
    exact ne_of_gt (sub_pos.mpr (lt_of_le_of_lt hs.2 h1))
  have he : kernel m=(fun s => ((-1:ℝ)^m*Real.log s^m)*(1-s)⁻¹) := by
    funext s
    unfold kernel
    rw [neg_pow,div_eq_mul_inv]
  rw [he]
  exact hl.mul_continuousOn hc

theorem slope_continuous : ContinuousOn (dslope Real.log 1) (Ioi 0) := by
  apply (continuousOn_dslope (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))).mpr
  exact ⟨Real.continuousOn_log.mono (fun _ hx => ne_of_gt hx),
    (Real.hasDerivAt_log one_ne_zero).differentiableAt⟩

theorem kernel_eq (m : ℕ) {s : ℝ} (hs : s≠1) :
    kernel (m+1) s=(-Real.log s)^m*dslope Real.log 1 s := by
  rw [dslope_of_ne _ hs]
  simp only [slope,Real.log_one,vsub_eq_sub,sub_zero,smul_eq_mul]
  unfold kernel
  rw [pow_succ]
  field_simp
  ring

theorem kernel_integrable (m : ℕ) (hm : 0 < m) :
    IntervalIntegrable (kernel m) volume 0 1 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  apply (kernel_left (k+1) (b:=1/2) (by norm_num) (by norm_num)).trans
  have hc : ContinuousOn (fun s => (-Real.log s)^k*dslope Real.log 1 s) (Ioi 0) :=
    ((Real.continuousOn_log.mono (fun _ hx => ne_of_gt hx)).neg.pow k).mul slope_continuous
  have hi : IntervalIntegrable (fun s => (-Real.log s)^k*dslope Real.log 1 s) volume (1/2) 1 := (hc.mono (show uIcc (1/2:ℝ) 1⊆Ioi 0 by
    rw [uIcc_of_le (by norm_num : (1/2:ℝ)≤1)]
    intro s hs
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hs.1)).intervalIntegrable
  apply hi.congr_uIoo
  intro s hs
  rw [uIoo_of_lt (by norm_num : (1/2:ℝ)<1)] at hs
  exact (kernel_eq k (ne_of_lt hs.2)).symm

theorem kernel_pos (m : ℕ) {s : ℝ} (hs : s∈Ioo 0 1) : 0<kernel m s := by
  apply div_pos
  · exact pow_pos (neg_pos.mpr (Real.log_neg hs.1 hs.2)) m
  · exact sub_pos.mpr hs.2

theorem integral_pos (m : ℕ) (hm : 0 < m) : 0 < ∫ s in (0:ℝ)..1,kernel m s :=
  intervalIntegral_pos_of_pos_on (kernel_integrable m hm)
    (fun _ hs => kernel_pos m hs) (by norm_num)

theorem coefficient_ne_zero (m : ℕ) (hm : 0 < m) :
    -(1/(m.factorial:ℝ))*(∫ s in (0:ℝ)..1,kernel m s)≠0 := by
  apply mul_ne_zero
  · exact neg_ne_zero.mpr (one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)))
  · exact ne_of_gt (integral_pos m hm)

theorem integral_zero {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    (∫ t in (0:ℝ)..s,kernel 0 t)=-Real.log (1-s) := by
  have hd (t : ℝ) (ht : t∈uIcc 0 s) :
      HasDerivAt (fun t : ℝ => -Real.log (1-t)) (kernel 0 t) t := by
    rw [uIcc_of_le h0] at ht
    have hne : 1-t≠0 := ne_of_gt (sub_pos.mpr (lt_of_le_of_lt ht.2 h1))
    have h := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).log hne).neg
    simpa only [kernel,pow_zero,zero_sub,neg_div,one_div,neg_neg,Pi.sub_apply,Pi.neg_apply,id_eq] using! h
  have h := integral_eq_sub_of_hasDerivAt hd (kernel_left 0 h0 h1)
  simpa using h

theorem integral_limit (m : ℕ) (hm : 0 < m) :
    Tendsto (fun s => ∫ t in (0:ℝ)..s,kernel m t) (𝓝[<] 1)
      (𝓝 (∫ t in (0:ℝ)..1,kernel m t)) := by
  have hc := intervalIntegral.continuousOn_primitive_interval'
    (kernel_integrable m hm) left_mem_uIcc
  have hh := hc 1 right_mem_uIcc
  change Tendsto _ (𝓝[uIcc 0 1] 1) _ at hh
  rw [uIcc_of_le (by norm_num : (0:ℝ)≤1),nhdsWithin_Icc_eq_nhdsLE (by norm_num : (0:ℝ)<1)] at hh
  exact hh.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)

theorem one_sub_limit : Tendsto (fun s : ℝ => 1-s) (𝓝[<] 1) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun s : ℝ => 1-s) := continuous_const.sub continuous_id
    have hh : Tendsto (fun s : ℝ => 1-s) (𝓝 (1:ℝ)) (𝓝 (1-1:ℝ)) := hc.tendsto 1
    simpa only [sub_self] using hh.mono_left (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change 0 < 1-s
    exact sub_pos.mpr (show s < 1 from hs)

theorem log_endpoint_product (m : ℕ) (hm : 0 < m) :
    Tendsto (fun s : ℝ => Real.log s^m*Real.log (1-s)) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have h0 : Tendsto (fun s : ℝ => Real.log (1-s)*(1-s)) (𝓝[<] 1) (𝓝 0) := by
    simpa only [Real.rpow_one,Function.comp_def] using
      (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0:ℝ)<1)).comp one_sub_limit
  have hl := (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.mono_left
    (show 𝓝[<] (1:ℝ)≤𝓝 1 from nhdsWithin_le_nhds)
  have hd := (continuousAt_dslope_same.mpr (Real.hasDerivAt_log one_ne_zero).differentiableAt).tendsto.mono_left
    (show 𝓝[<] (1:ℝ)≤𝓝 1 from nhdsWithin_le_nhds)
  have hh := ((hl.pow k).neg.mul hd).mul h0
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards with s
  have he : (s-1)*dslope Real.log 1 s=Real.log s := by
    simpa only [smul_eq_mul,Real.log_one,sub_zero] using sub_smul_dslope Real.log 1 s
  change -(Real.log s^k)*dslope Real.log 1 s*(Real.log (1-s)*(1-s))=Real.log s^(k+1)*Real.log (1-s)
  rw [pow_succ]
  calc
    _ = Real.log s^k*((s-1)*dslope Real.log 1 s)*Real.log (1-s) := by ring
    _ = _ := by rw [he]

end DepthIntegral

namespace CutoffKZ
open CutoffDepth FinitePicard KZCollar MeasureTheory Set Filter
open scoped Topology

instance normedRing (N : ℕ) : NormedRing (Q ℝ N) := FiniteAlgebraNorm.normedRing _
instance normedAlgebra (N : ℕ) : NormedAlgebra ℝ (Q ℝ N) := FiniteAlgebraNorm.normedAlgebra _

def weight (N : ℕ) : NilpotentFiltration (Q ℝ N) where
  space := TruncatedWords.filtration ∅ N
  antitone := TruncatedWords.filtration_antitone ∅ N
  one_mem := TruncatedWords.filtration_one ∅ N
  mul_mem := TruncatedWords.filtration_mul ∅ N
  cutoff := N
  terminal := TruncatedWords.filtration_terminal ∅ N

def depth (N : ℕ) : NilpotentFiltration (Q ℝ N) where
  space := depthSpace N
  antitone := depth_antitone N
  one_mem := depth_one N
  mul_mem := depth_mul N
  cutoff := N
  terminal := depth_terminal N

abbrev X (N : ℕ) : Q ℝ N := gen N false
abbrev Y (N : ℕ) : Q ℝ N := gen N true
abbrev c (N m : ℕ) : Q ℝ N →ₗ[ℝ] ℝ := coeff N (GenericIhara.depthOneWord m)

theorem X_nilpotent (N : ℕ) : X N^(N+1)=0 := pow_cutoff_eq_zero (weight N) (gen_weight N false)

theorem X_pow_depth (N i : ℕ) : X N^i∈depthSpace N 0 := by
  induction i with
  | zero => simpa using depth_one N
  | succ i ih => simpa only [pow_succ,Nat.zero_add] using depth_mul N 0 0 ih (gen_depth N false)

theorem regularForm_depth (N : ℕ) (s : ℝ) : regularForm (X N) (Y N) s∈depthSpace N 1 := by
  rw [regularForm_finite _ _ (X_nilpotent N)]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact depth_mul N 1 0 (depth_mul N 0 1 (X_pow_depth N i) (gen_depth N true)) (X_pow_depth N j)

theorem coeff_one (N m : ℕ) : c N m 1=0 := by
  rw [←(quotient (R:=ℝ) N).map_one]
  change TruncatedFree.coefficient N _ (TruncatedWords.quotient (∅ : Set (AssociativeElimination.A ℝ Bool)) N (1 : AssociativeElimination.A ℝ Bool))=0
  rw [TruncatedFree.coefficient_quotient]
  have hn : GenericIhara.depthOneWord m≠1 := by
    intro h
    have hh := congrArg (WordGrading.degree TruncatedWords.wt) h
    simp only [length_depthOne,WordGrading.degree_one] at hh
    omega
  classical
  simp [MonoidAlgebra.one_def,MonoidAlgebra.coeff_single,hn]

theorem coeff_high_term (N m k : ℕ) (hk : 2 ≤ k) (s : ℝ) :
    c N m (term (regularForm (X N) (Y N)) 0 k s)=0 := by
  apply coeff_zero_of_depth N k (term_mem (depth N) (regularForm_depth N) 0 k s)
  simpa [GenericIhara.depthOneWord,GenericIhara.depth] using (show 1 < k by omega)

theorem coeff_form (N m : ℕ) (hN : m+1 ≤ N) (s : ℝ) :
    c N m (regularForm (X N) (Y N) s)=-(1/(m.factorial:ℝ))*DepthIntegral.kernel m s := by
  rw [regularForm_finite _ _ (X_nilpotent N),map_sum]
  simp only [map_sum,map_smul,smul_eq_mul,c,coeff_monomial N _ _ m hN]
  rw [Finset.sum_eq_single m]
  · rw [Finset.sum_eq_single 0]
    · simp only [and_self,↓reduceIte,mul_one,Nat.factorial_zero,Nat.cast_one,add_zero]
      unfold DepthIntegral.kernel
      rw [neg_pow,show s-1= -(1-s) by ring,inv_neg,div_eq_mul_inv]
      ring
    · intro j hj hj0
      simp only [hj0,and_false,↓reduceIte,mul_zero]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (Nat.zero_lt_succ N)))
  · intro i hi him
    simp only [him,false_and,↓reduceIte,mul_zero,Finset.sum_const_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

theorem coeff_first_term (N m : ℕ) (hN : m+1 ≤ N) {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    c N m (term (regularForm (X N) (Y N)) 0 1 s)=
      -(1/(m.factorial:ℝ))*(∫ t in (0:ℝ)..s,DepthIntegral.kernel m t) := by
  simp only [term_succ,term_zero,mul_one]
  change (c N m).toContinuousLinearMap (∫ t in (0:ℝ)..s,regularForm (X N) (Y N) t)=_
  rw [←(c N m).toContinuousLinearMap.intervalIntegral_comp_comm
    (regularForm_integrable _ _ (X_nilpotent N) h0 h1)]
  change (∫ t in (0:ℝ)..s,c N m (regularForm (X N) (Y N) t))=_
  simp only [coeff_form N m hN]
  exact intervalIntegral.integral_const_mul _ _

theorem coeff_transport (N m : ℕ) (hN : m+1 ≤ N) {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    c N m (transport (regularForm (X N) (Y N)) 0 N s)=
      -(1/(m.factorial:ℝ))*(∫ t in (0:ℝ)..s,DepthIntegral.kernel m t) := by
  rw [transport,map_sum,Finset.sum_eq_single 1]
  · exact coeff_first_term N m hN h0 h1
  · intro k hk hn
    by_cases hz : k=0
    · subst k; simp only [term_zero,coeff_one]
    · exact coeff_high_term N m k (by omega) s
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

end CutoffKZ

section

end

namespace CutoffDiagonal
open scoped TensorProduct
open CutoffDepth CutoffKZ FinitePicard
local instance (N : ℕ) : NormedRing (Q ℝ N⊗[ℝ]Q ℝ N) := FiniteAlgebraNorm.normedRing _
local instance (N : ℕ) : NormedAlgebra ℝ (Q ℝ N⊗[ℝ]Q ℝ N) := FiniteAlgebraNorm.normedAlgebra _

def left (N : ℕ) : Q ℝ N →ₐ[ℝ] Q ℝ N⊗[ℝ]Q ℝ N := Algebra.TensorProduct.includeLeft

end CutoffDiagonal

namespace RegularSingular
open MeasureTheory Set Filter FinitePicard KZCollar
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def regular (X : A) (R : ℝ → A) (s : ℝ) : A := gauge (-X) s*R s*gauge X s

variable [CompleteSpace A]

variable [FiniteDimensional ℝ A]

end RegularSingular

namespace PowerAsymptotic

section
open MeasureTheory Set Filter Asymptotics FinitePicard KZCollar RegularSingular
open scoped Topology

def Subpower {E : Type*} [Norm E] (f : ℝ → E) : Prop :=
  ∀ p : ℝ,0<p → f =O[𝓝[>] 0] (fun s : ℝ => s^(-p))

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

end

open MeasureTheory Set Filter Asymptotics FinitePicard KZCollar RegularSingular
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

variable [CompleteSpace A]

variable [FiniteDimensional ℝ A]

end PowerAsymptotic

namespace KZCollar
open Set Filter PowerAsymptotic Asymptotics
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

variable [CompleteSpace A]

omit [CompleteSpace A] in
@[simp] theorem gauge_one (X : A) : gauge X 1=1 := by simp [gauge]

end KZCollar

namespace CutoffKZ
open CutoffDepth FinitePicard KZCollar MeasureTheory Set Filter
open scoped Topology

theorem coeff_gauge_Y (N m : ℕ) (hN : m+1 ≤ N) (hm : 0 < m) (p : Q ℝ N) (s : ℝ) :
    c N m (gauge (-Y N) s*p)=c N m p := by
  have hy : (-Y N)^(N+1)=0 := by
    have hh : Y N^(N+1)=0 := pow_cutoff_eq_zero (weight N) (gen_weight N true)
    rw [neg_pow,hh,mul_zero]
  rw [gauge_finite _ hy,Finset.sum_mul,map_sum,Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    rw [smul_mul_assoc,map_smul,neg_pow]
    have he : (-1:Q ℝ N)^i * Y N^i *p = (-1:ℝ)^i • (Y N^i*p) := by
      simp only [Algebra.smul_def,map_pow,map_neg,map_one]
      noncomm_ring
    rw [he,map_smul]
    change _ • (_ • (coeff N (GenericIhara.depthOneWord m) (gen N true^i*p)))=0
    rw [coeff_Y_prefix N i m hN hm,if_neg hi0,smul_zero,smul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (Nat.zero_lt_succ N)))

def prefactor (m i : ℕ) (s : ℝ) : ℝ :=
  (Real.log s^i/(i.factorial:ℝ)) *
    if i ≤ m then -(1/((m-i).factorial:ℝ))*(∫ t in (0:ℝ)..s,DepthIntegral.kernel (m-i) t) else 0

theorem coeff_normalized (N m : ℕ) (hN : m+1 ≤ N) {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    c N m (normalizedSolution (weight N) (X N) (Y N) s)=
      ∑ i∈Finset.range (N+1),prefactor m i s := by
  rw [normalizedSolution,gauge_finite _ (X_nilpotent N),Finset.sum_mul,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_mul_assoc,map_smul]
  change (Real.log s^i/(i.factorial:ℝ))*(coeff N (GenericIhara.depthOneWord m)
    (gen N false^i*transport (regularForm (X N) (Y N)) 0 N s))=_
  rw [coeff_prefix N i m hN]
  unfold prefactor
  split_ifs with him
  · congr 1
    exact coeff_transport N (m-i) (by omega) h0 h1
  · rfl

theorem prefactor_limit (m i : ℕ) (hm : 0 < m) :
    Tendsto (prefactor m i) (𝓝[<] 1)
      (𝓝 (if i=0 then -(1/(m.factorial:ℝ))*(∫ t in (0:ℝ)..1,DepthIntegral.kernel m t) else 0)) := by
  change Tendsto (fun s => prefactor m i s) _ _
  have hl : Tendsto Real.log (𝓝[<] (1:ℝ)) (𝓝 0) := by
    simpa only [Real.log_one] using (Real.continuousAt_log one_ne_zero).tendsto.mono_left
      (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  by_cases hi : i=0
  · subst i
    simpa only [prefactor,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,Nat.zero_le,
      ↓reduceIte,Nat.sub_zero,one_mul] using
      (tendsto_const_nhds (x:= -(1/(m.factorial:ℝ)))).mul (DepthIntegral.integral_limit m hm)
  · rw [if_neg hi]
    by_cases him : i ≤ m
    · by_cases him' : i=m
      · subst i
        have hh := (DepthIntegral.log_endpoint_product m hm).div_const (m.factorial:ℝ)
        simp only [zero_div] at hh
        apply hh.congr'
        filter_upwards [self_mem_nhdsWithin,
          (eventually_gt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with s hs hs0
        unfold prefactor
        rw [if_pos (le_refl m),Nat.sub_self,DepthIntegral.integral_zero hs0.le hs]
        simp only [Nat.factorial_zero,Nat.cast_one,div_one]
        ring
      · have hpos : 0 < m-i := by omega
        have hpow : Tendsto (fun s : ℝ => Real.log s^i/(i.factorial:ℝ)) (𝓝[<] 1) (𝓝 0) := by
          simpa only [zero_pow hi,zero_div] using (hl.pow i).div_const (i.factorial:ℝ)
        have h := hpow.mul ((tendsto_const_nhds (x:= -(1/((m-i).factorial:ℝ)))).mul
          (DepthIntegral.integral_limit (m-i) hpos))
        simpa only [prefactor,if_pos him,zero_mul] using h
    · simp only [prefactor,if_neg him,mul_zero]
      exact tendsto_const_nhds

theorem coeff_normalized_limit (N m : ℕ) (hN : m+1 ≤ N) (hm : 0 < m) :
    Tendsto (fun s => c N m (normalizedSolution (weight N) (X N) (Y N) s)) (𝓝[<] 1)
      (𝓝 (-(1/(m.factorial:ℝ))*(∫ t in (0:ℝ)..1,DepthIntegral.kernel m t))) := by
  have hh := tendsto_finsetSum (Finset.range (N+1)) (fun i _ => prefactor_limit m i hm)
  simp only [Finset.sum_ite_eq',Finset.mem_range,Nat.zero_lt_succ,↓reduceIte] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with s hs hs0
  exact (coeff_normalized N m hN hs0.le hs).symm

theorem left_regularized_limit (N : ℕ) :
    Tendsto (fun s => gauge (-Y N) (1-s)*normalizedSolution (weight N) (X N) (Y N) s)
      (𝓝[<] 1) (𝓝 (associator (weight N) (X N) (Y N))) := by
  have hh := ((regularTransport_limit (Y:=X N) (weight N) (gen_weight N true)).comp
    DepthIntegral.one_sub_limit).mul (tendsto_const_nhds (x:=associator (weight N) (X N) (Y N)))
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with s hs hs0
  rw [left_eq_right_mul_associator (weight N) (gen_weight N false) (gen_weight N true) ⟨hs0,hs⟩]
  simp only [rightSolution,normalizedSolution,←mul_assoc,gauge_neg_mul,one_mul,Function.comp_apply]

theorem associator_coefficient (N m : ℕ) (hN : m+1 ≤ N) (hm : 0 < m) :
    c N m (associator (weight N) (X N) (Y N))=
      -(1/(m.factorial:ℝ))*(∫ t in (0:ℝ)..1,DepthIntegral.kernel m t) := by
  have hh := (c N m).toContinuousLinearMap.continuous.tendsto
    (associator (weight N) (X N) (Y N)) |>.comp (left_regularized_limit N)
  have he : (fun s => c N m (gauge (-Y N) (1-s)*normalizedSolution (weight N) (X N) (Y N) s))=
      (fun s => c N m (normalizedSolution (weight N) (X N) (Y N) s)) := by
    funext s
    exact coeff_gauge_Y N m hN hm _ _
  change Tendsto (fun s => c N m (gauge (-Y N) (1-s)*normalizedSolution (weight N) (X N) (Y N) s)) _ _ at hh
  rw [he] at hh
  exact tendsto_nhds_unique hh (coeff_normalized_limit N m hN hm)

end CutoffKZ

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section
namespace RealDeligneDrinfeld

theorem freeLie_induction {R α : Type*} [CommRing R]
    {P : FreeLieAlgebra R α → Prop} (h0 : P 0)
    (hg : ∀ a, P (FreeLieAlgebra.of R a))
    (ha : ∀ a b, P a → P b → P (a+b))
    (hs : ∀ (r : R) a, P a → P (r • a))
    (hl : ∀ a b, P a → P b → P ⁅a,b⁆) (q : FreeLieAlgebra R α) : P q := by
  let K : LieSubalgebra R (FreeLieAlgebra R α) :=
    { carrier := {a | P a}
      zero_mem' := h0
      add_mem' := fun ha' hb' => ha _ _ ha' hb'
      smul_mem' := fun r a h => hs r a h
      lie_mem' := fun ha' hb' => hl _ _ ha' hb' }
  let f : FreeLieAlgebra R α →ₗ⁅R⁆ K :=
    FreeLieAlgebra.lift R (fun a => ⟨FreeLieAlgebra.of R a, hg a⟩)
  have hf : K.incl.comp f = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [f]
  have h := (f q).property
  change P ((K.incl.comp f) q) at h
  simpa only [hf, LieHom.id_apply] using h

abbrev L := FreeLieAlgebra ℝ Bool

def eval {M : Type*} [LieRing M] [LieAlgebra ℝ M] (a b : M) : L →ₗ⁅ℝ⁆ M :=
  FreeLieAlgebra.lift ℝ (fun i => if i then b else a)

abbrev Edge := {p : Fin 4 × Fin 4 // p.1 < p.2}
abbrev BraidFree := FreeLieAlgebra ℝ Edge

def chord (i j : Fin 4) : BraidFree :=
  if h : i < j then FreeLieAlgebra.of ℝ ⟨(i, j), h⟩
  else if h : j < i then FreeLieAlgebra.of ℝ ⟨(j, i), h⟩ else 0

def braidRelations : Set BraidFree :=
  {z | (∃ i j k l : Fin 4,
    i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      z = ⁅chord i j, chord k l⁆) ∨
    (∃ i j k : Fin 4, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      z = ⁅chord i j, chord i k + chord j k⁆)}

def braidIdeal : LieIdeal ℝ BraidFree :=
  LieSubmodule.lieSpan ℝ BraidFree braidRelations

abbrev T4 := BraidFree ⧸ braidIdeal
def t (i j : Fin 4) : T4 := LieSubmodule.Quotient.mk (chord i j)

namespace FreeDerivations

variable {R : Type*} [CommRing R]
variable {M : Type*} [LieRing M] [LieAlgebra R M]

variable {α : Type*}
local notation "F" => FreeLieAlgebra R α

@[ext] theorem ext {d₁ d₂ : LieDerivation R F F}
    (h : ∀ a, d₁ (FreeLieAlgebra.of R a) = d₂ (FreeLieAlgebra.of R a)) : d₁ = d₂ := by
  apply DFunLike.ext
  intro q
  induction q using freeLie_induction with
  | h0 => simp
  | hg a => exact h a
  | ha a b ha hb => simp [ha, hb]
  | hs r a ha => simp [ha]
  | hl a b ha hb => simp [ha, hb]

variable [DecidableEq α]

end FreeDerivations

@[simp] theorem chord_comm (i j : Fin 4) : chord i j = chord j i := by
  unfold chord
  split_ifs <;> first | rfl | omega

@[simp] theorem t_comm (i j : Fin 4) : t i j = t j i := by
  unfold t
  rw [chord_comm]

@[simp] theorem t_self (i : Fin 4) : t i i = 0 := by simp [t, chord]

end RealDeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld
end DeligneDrinfeld

namespace DeligneDrinfeld
end DeligneDrinfeld

namespace DeligneDrinfeld.LogRectangle
open MeasureTheory Set Filter FinitePicard
open scoped Topology
variable {K A E : Type*} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
  [NormedRing A] [NormedAlgebra K A] [NormedAlgebra ℝ A] [IsScalarTower ℝ K A]
  [Fintype E]

def form (c : E → A) (z v : E → K) : A := ∑ i,(v i/z i) • c i

variable [CompleteSpace A] [FiniteDimensional ℝ A]

end DeligneDrinfeld.LogRectangle

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace HexagonUnits
open FinitePicard KZCollar
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [FiniteDimensional ℝ A]

local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A

def exp (a : A) : Aˣ := (NormedSpace.isUnit_exp a).unit
omit [FiniteDimensional ℝ A] in
@[simp] theorem exp_val (a : A) : (exp a:A)=NormedSpace.exp a := (NormedSpace.isUnit_exp a).unit_spec
omit [FiniteDimensional ℝ A] in
@[simp] theorem exp_neg (a : A) : exp (-a)=(exp a)⁻¹ := by
  apply Units.ext
  rw [exp_val]
  rw [←Ring.inverse_exp,←exp_val,Ring.inverse_unit]

end HexagonUnits

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld
namespace CategoryGauge
variable {R M N O P : Type*} [CommRing R] [LieRing M] [LieAlgebra R M]
    [LieRing N] [LieAlgebra R N]

structure Data (R M O : Type*) [CommRing R] [LieRing M] [LieAlgebra R M] where
  d : LieDerivation R M M
  h : O → M

def unit (g : Data R M O) (p q : O) : M := g.h q-g.h p

def loop (g : Data R M O) (p : O) : LieDerivation R M M :=
  g.d-LieDerivation.inner R M M (g.h p)

@[simp] theorem loop_apply (g : Data R M O) (p : O) (x : M) :
    loop g p x=g.d x+⁅g.h p,x⁆ := by
  change g.d x-⁅x,g.h p⁆=g.d x+⁅g.h p,x⁆
  rw [←lie_skew (g.h p) x]
  abel

theorem loop_change (g : Data R M O) (p q : O) (x : M) :
    loop g q x=loop g p x+⁅unit g p q,x⁆ := by
  simp only [loop_apply,unit,sub_lie]
  abel

def commutator (g k : Data R M O) : Data R M O where
  d := ⁅g.d,k.d⁆
  h p := g.d (k.h p)-k.d (g.h p)+⁅g.h p,k.h p⁆

theorem loop_commutator (g k : Data R M O) (p : O) :
    loop (commutator g k) p=⁅loop g p,loop k p⁆ := by
  ext x
  simp only [loop_apply,commutator,LieDerivation.lie_apply,map_add,
    LieDerivation.apply_lie_eq_add,add_lie,sub_lie,lie_add]
  rw [lie_lie (g.h p) (k.h p) x]
  rw [lie_lie (k.h p) (g.h p) x]
  abel

theorem unit_commutator (g k : Data R M O) (p q : O) :
    unit (commutator g k) p q=
      loop g p (unit k p q)-loop k p (unit g p q)+⁅unit g p q,unit k p q⁆ := by
  simp only [unit,commutator,loop_apply,map_sub,lie_sub,sub_lie]
  rw [←lie_skew (k.h p) (g.h p),←lie_skew (k.h p) (g.h q)]
  abel

def Compatible (F : M →ₗ⁅R⁆ N) (f : O → P) (g : Data R M O) (k : Data R N P) : Prop :=
  (∀ p q,unit k (f p) (f q)=F (unit g p q)) ∧
  (∀ p x,loop k (f p) (F x)=F (loop g p x))

theorem compatible_commutator (F : M →ₗ⁅R⁆ N) (f : O → P)
    {g₁ g₂ : Data R M O} {k₁ k₂ : Data R N P}
    (h₁ : Compatible F f g₁ k₁) (h₂ : Compatible F f g₂ k₂) :
    Compatible F f (commutator g₁ g₂) (commutator k₁ k₂) := by
  constructor
  · intro p q
    rw [unit_commutator,unit_commutator,h₁.1,h₂.1,h₁.2,h₂.2,map_add,map_sub,LieHom.map_lie]
  · intro p x
    rw [loop_commutator,loop_commutator,LieDerivation.lie_apply,LieDerivation.lie_apply,
      h₁.2,h₂.2,h₁.2,h₂.2,map_sub]

def zero : Data R M O := ⟨0,fun _ => 0⟩
def add (g k : Data R M O) : Data R M O := ⟨g.d+k.d,fun p => g.h p+k.h p⟩
def smul (c : R) (g : Data R M O) : Data R M O := ⟨c • g.d,fun p => c • g.h p⟩

@[simp] theorem zero_unit (p q : O) : unit (zero (R:=R) (M:=M)) p q=0 := by simp [unit,zero]
@[simp] theorem zero_loop (p : O) (x : M) : loop (zero (R:=R)) p x=0 := by simp [loop_apply,zero]
@[simp] theorem add_unit (g k : Data R M O) (p q : O) :
    unit (add g k) p q=unit g p q+unit k p q := by simp only [unit,add]; abel
@[simp] theorem add_loop (g k : Data R M O) (p : O) (x : M) :
    loop (add g k) p x=loop g p x+loop k p x := by simp only [loop_apply,add,LieDerivation.add_apply,add_lie]; abel
@[simp] theorem smul_unit (c : R) (g : Data R M O) (p q : O) :
    unit (smul c g) p q=c • unit g p q := by simp [unit,smul,smul_sub]
@[simp] theorem smul_loop (c : R) (g : Data R M O) (p : O) (x : M) :
    loop (smul c g) p x=c • loop g p x := by simp [loop_apply,smul,smul_add]

theorem compatible_zero (F : M →ₗ⁅R⁆ N) (f : O → P) : Compatible F f zero zero := by
  constructor <;> intros <;> simp [zero,unit,loop_apply]

theorem compatible_add (F : M →ₗ⁅R⁆ N) (f : O → P)
    {g₁ g₂ : Data R M O} {k₁ k₂ : Data R N P}
    (h₁ : Compatible F f g₁ k₁) (h₂ : Compatible F f g₂ k₂) :
    Compatible F f (add g₁ g₂) (add k₁ k₂) := by
  constructor
  · intro p q; simp only [add_unit,h₁.1,h₂.1,map_add]
  · intro p x; simp only [add_loop,h₁.2,h₂.2,map_add]

theorem compatible_smul (F : M →ₗ⁅R⁆ N) (f : O → P)
    {g : Data R M O} {k : Data R N P} (h : Compatible F f g k) (c : R) :
    Compatible F f (smul c g) (smul c k) := by
  constructor
  · intro p q; simp only [smul_unit,h.1,map_smul]
  · intro p x; simp only [smul_loop,h.2,map_smul]

end CategoryGauge
end DeligneDrinfeld

namespace DeligneDrinfeld.CategoryGauge
variable {R M N O P : Type*} [CommRing R] [LieRing M] [LieAlgebra R M]
  [LieRing N] [LieAlgebra R N]

def EdgeCompatible (F : M →ₗ⁅R⁆ N) (p q : O) (s t : P)
    (g : Data R M O) (k : Data R N P) : Prop :=
  unit k s t=F (unit g p q) ∧ ∀ x,loop k s (F x)=F (loop g p x)

theorem edge_commutator (F : M →ₗ⁅R⁆ N) {p q : O} {s t : P}
    {g₁ g₂ : Data R M O} {k₁ k₂ : Data R N P}
    (h₁ : EdgeCompatible F p q s t g₁ k₁) (h₂ : EdgeCompatible F p q s t g₂ k₂) :
    EdgeCompatible F p q s t (commutator g₁ g₂) (commutator k₁ k₂) := by
  constructor
  · rw [unit_commutator,unit_commutator,h₁.1,h₂.1,h₁.2,h₂.2,map_add,map_sub,LieHom.map_lie]
  · intro x
    rw [loop_commutator,loop_commutator,LieDerivation.lie_apply,LieDerivation.lie_apply,
      h₁.2,h₂.2,h₁.2,h₂.2,map_sub]

theorem edge_zero (F : M →ₗ⁅R⁆ N) (p q : O) (s t : P) :
    EdgeCompatible F p q s t zero zero := by
  constructor <;> intros <;> simp [zero,unit,loop_apply]

theorem edge_add (F : M →ₗ⁅R⁆ N) {p q : O} {s t : P}
    {g₁ g₂ : Data R M O} {k₁ k₂ : Data R N P}
    (h₁ : EdgeCompatible F p q s t g₁ k₁) (h₂ : EdgeCompatible F p q s t g₂ k₂) :
    EdgeCompatible F p q s t (add g₁ g₂) (add k₁ k₂) := by
  constructor
  · rw [add_unit,add_unit,h₁.1,h₂.1,map_add]
  · intro x; rw [add_loop,add_loop,h₁.2,h₂.2,map_add]

theorem edge_smul (F : M →ₗ⁅R⁆ N) {p q : O} {s t : P}
    {g : Data R M O} {k : Data R N P} (h : EdgeCompatible F p q s t g k) (c : R) :
    EdgeCompatible F p q s t (smul c g) (smul c k) := by
  constructor
  · rw [smul_unit,smul_unit,h.1,map_smul]
  · intro x; rw [smul_loop,smul_loop,h.2,map_smul]

theorem commutator_kills {g k : Data R M O} {p : O} {x : M}
    (hg : loop g p x=0) (hk : loop k p x=0) : loop (commutator g k) p x=0 := by
  rw [loop_commutator,LieDerivation.lie_apply,hg,hk,map_zero,map_zero,sub_zero]

end DeligneDrinfeld.CategoryGauge

end

end OAI

end

section

namespace OAI

noncomputable section

namespace RealDeligneDrinfeld.BraidSix
variable {M : Type*} [LieRing M]

def total (a b c d e f : M) : M := a+b+c+d+e+f

variable {a b c d e f : M}

end RealDeligneDrinfeld.BraidSix

namespace RealDeligneDrinfeld.T4Basic
open BraidSix

def a : T4 := t 0 1
def b : T4 := t 1 2

end RealDeligneDrinfeld.T4Basic

namespace RealDeligneDrinfeld.T4SolutionData
open T4Basic

def A (q : L) : T4 := eval a b q

end RealDeligneDrinfeld.T4SolutionData

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace SaturatedSolutions
open AssociativeElimination UniversalEmbedding WordGrading
open ReducedDimension
variable (n : ℕ) (E : Submodule ℚ (Wn n))

def image : Submodule ℚ (RationalBound.Words n → ℚ) := E.map (RationalBound.coordinates n)

end SaturatedSolutions

namespace NormalizedFamily
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open ImageBound LieGrading RowTwo RowKernel ExactPentagon
attribute [local instance] LieRing.ofAssociativeRing
abbrev K := ZMod 2

structure Data where
  active : ℕ → Prop
  value : ℕ → FreeLieAlgebra K Bool
  solution : ∀ n (p : FreeLieAlgebra K ℕ),p∈homogeneousLie oddWeight n →
    GenericIhara.evalIhara value p∈ReducedDimension.solutions n
  rep : ℕ → FreeLieAlgebra K Slot
  under_rep : ∀ k,under (rep k)=embed (value k)
  above_rep : ∀ k,active k → embed (rep k)∈above bCount 1
  leading_rep : ∀ k,active k → embed (leading 1 (rep k))=positiveInput (atom k)

variable (g : Data)

end NormalizedFamily

namespace IntegralFamily
open LieGrading AssociativeElimination UniversalEmbedding WordGrading
open scoped TensorProduct

structure Values where
  space : Submodule ℚ L
  le_W : space≤W
  bracket : ∀ {p q},p∈space → q∈space → ihara p q∈space

variable (V : Values)

def piece (V : Values) (n : ℕ) : Submodule ℚ (Wn n) := V.space.comap (Wn n).subtype

end IntegralFamily

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace CategoricalValues
open CategoryGauge

def swapObjects : Fin 3 → Fin 3 := ![1,0,2]
def rotateObjects : Fin 3 → Fin 3 := ![1,2,0]
def swapLie : L →ₗ⁅ℚ⁆ L := eval y x
def rotateLie : L →ₗ⁅ℚ⁆ L := eval y (-x-y)

structure Witness where
  three : CategoryGauge.Data ℚ L (Fin 3)
  four : CategoryGauge.Data ℚ T4 (Fin 5)
  swap : Compatible swapLie swapObjects three three
  rotate : Compatible rotateLie rotateObjects three three
  kill_x : loop three 0 x=0
  kill_y : loop three 1 y=0
  AD : EdgeCompatible (eval (t 0 2+t 1 2) (t 2 3)) 0 1 0 3 three four
  DE : EdgeCompatible (eval (t 0 1) (t 1 2+t 1 3)) 0 1 3 4 three four
  AB : EdgeCompatible (eval (t 0 1) (t 1 2)) 0 1 0 1 three four
  BC : EdgeCompatible (eval (t 0 1+t 0 2) (t 1 3+t 2 3)) 0 1 1 2 three four
  CE : EdgeCompatible (eval (t 1 2) (t 2 3)) 0 1 2 4 three four

def value (w : Witness) : L := unit w.three 0 1

theorem value_anti (w : Witness) : value w+eval y x (value w)=0 := by
  have h := w.swap.1 0 1
  change unit w.three 1 0=eval y x (value w) at h
  rw [←h]
  simp only [value,unit]
  abel

theorem rotate_squared : rotateLie.comp rotateLie=eval (-x-y) x := by
  apply FreeLieAlgebra.hom_ext
  intro i
  cases i
  · simp [rotateLie,eval,x,y]
  · simp [rotateLie,eval,x,y]
    abel

theorem value_cyclic (w : Witness) :
    value w+eval y (-x-y) (value w)+eval (-x-y) x (value w)=0 := by
  have h₁ := w.rotate.1 0 1
  have h₂ := w.rotate.1 1 2
  change unit w.three 1 2=rotateLie (value w) at h₁
  change unit w.three 2 0=rotateLie (unit w.three 1 2) at h₂
  rw [h₁] at h₂
  have hsq : rotateLie (rotateLie (value w))=eval (-x-y) x (value w) :=
    LieHom.congr_fun rotate_squared (value w)
  rw [hsq] at h₂
  change value w+rotateLie (value w)+eval (-x-y) x (value w)=0
  rw [←h₁,←h₂]
  simp only [value,unit]
  abel

theorem value_pentagon (w : Witness) :
    eval (t 0 1) (t 1 2+t 1 3) (value w)+eval (t 0 2+t 1 2) (t 2 3) (value w)=
      eval (t 1 2) (t 2 3) (value w)+eval (t 0 1+t 0 2) (t 1 3+t 2 3) (value w)+
        eval (t 0 1) (t 1 2) (value w) := by
  unfold value
  rw [←w.AD.1,←w.DE.1,←w.AB.1,←w.BC.1,←w.CE.1]
  simp only [unit]
  abel

theorem value_mem (w : Witness) : value w∈W :=
  ⟨value_anti w,value_cyclic w,value_pentagon w⟩

theorem source_derivation (w : Witness) : loop w.three 0=derivation (value w) := by
  apply derivation_ext
  · simpa only [derivation_apply,D_x] using w.kill_x
  · have h := loop_change w.three 0 1 y
    rw [w.kill_y] at h
    change 0=loop w.three 0 y+⁅value w,y⁆ at h
    simp only [derivation_apply,D_y]
    rw [←lie_skew y (value w)]
    exact eq_neg_of_add_eq_zero_left h.symm

def zero : Witness where
  three := CategoryGauge.zero
  four := CategoryGauge.zero
  swap := compatible_zero _ _
  rotate := compatible_zero _ _
  kill_x := zero_loop _ _
  kill_y := zero_loop _ _
  AD := edge_zero _ _ _ _ _
  DE := edge_zero _ _ _ _ _
  AB := edge_zero _ _ _ _ _
  BC := edge_zero _ _ _ _ _
  CE := edge_zero _ _ _ _ _

def add (w v : Witness) : Witness where
  three := CategoryGauge.add w.three v.three
  four := CategoryGauge.add w.four v.four
  swap := compatible_add _ _ w.swap v.swap
  rotate := compatible_add _ _ w.rotate v.rotate
  kill_x := by rw [add_loop,w.kill_x,v.kill_x,add_zero]
  kill_y := by rw [add_loop,w.kill_y,v.kill_y,add_zero]
  AD := edge_add _ w.AD v.AD
  DE := edge_add _ w.DE v.DE
  AB := edge_add _ w.AB v.AB
  BC := edge_add _ w.BC v.BC
  CE := edge_add _ w.CE v.CE

def smul (c : ℚ) (w : Witness) : Witness where
  three := CategoryGauge.smul c w.three
  four := CategoryGauge.smul c w.four
  swap := compatible_smul _ _ w.swap c
  rotate := compatible_smul _ _ w.rotate c
  kill_x := by rw [smul_loop,w.kill_x,smul_zero]
  kill_y := by rw [smul_loop,w.kill_y,smul_zero]
  AD := edge_smul _ w.AD c
  DE := edge_smul _ w.DE c
  AB := edge_smul _ w.AB c
  BC := edge_smul _ w.BC c
  CE := edge_smul _ w.CE c

def bracket (w v : Witness) : Witness where
  three := commutator w.three v.three
  four := commutator w.four v.four
  swap := compatible_commutator _ _ w.swap v.swap
  rotate := compatible_commutator _ _ w.rotate v.rotate
  kill_x := commutator_kills w.kill_x v.kill_x
  kill_y := commutator_kills w.kill_y v.kill_y
  AD := edge_commutator _ w.AD v.AD
  DE := edge_commutator _ w.DE v.DE
  AB := edge_commutator _ w.AB v.AB
  BC := edge_commutator _ w.BC v.BC
  CE := edge_commutator _ w.CE v.CE

theorem value_bracket (w v : Witness) : value (bracket w v)=ihara (value w) (value v) := by
  change unit (commutator w.three v.three) 0 1=_
  rw [unit_commutator,source_derivation,source_derivation]
  rfl

def values : IntegralFamily.Values where
  space :=
    { carrier := {p | ∃ w : Witness,value w=p}
      zero_mem' := ⟨zero,zero_unit _ _⟩
      add_mem' := by rintro p q ⟨w,rfl⟩ ⟨v,rfl⟩; exact ⟨add w v,add_unit _ _ _ _⟩
      smul_mem' := by rintro c p ⟨w,rfl⟩; exact ⟨smul c w,smul_unit _ _ _ _⟩ }
  le_W := by rintro p ⟨w,rfl⟩; exact value_mem w
  bracket := by rintro p q ⟨w,rfl⟩ ⟨v,rfl⟩; exact ⟨bracket w v,value_bracket w v⟩

end CategoricalValues

namespace IntegralFamily

section
open LieGrading AssociativeElimination UniversalEmbedding WordGrading
attribute [local instance] LieRing.ofAssociativeRing

variable (V : Values)

end

section
open LieGrading AssociativeElimination UniversalEmbedding WordGrading
open ImageBound RowKernel QuadraticLeading RowTwo
attribute [local instance] LieRing.ofAssociativeRing

variable (V : Values)

variable {V}

end

open LieGrading AssociativeElimination UniversalEmbedding WordGrading
open ImageBound RowKernel QuadraticLeading RowTwo
attribute [local instance] LieRing.ofAssociativeRing

variable (V : Values)

def OddValues : Prop := ∀ k,∃ p : Wn (oddWeight k),p∈piece V (oddWeight k) ∧
  (embed p.val).coeff (GenericIhara.depthOneWord (oddWeight k-1))≠0

end IntegralFamily

end DeligneDrinfeld

end

end OAI

end


