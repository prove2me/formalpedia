-- Prove2me | solution 1 for APFPaper1.Continuation.contextEq_sandwich_all
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:47:42.389194+00:00
-- url     : https://prove2.me/submissions/2b791b8f-1829-4e8e-a7e8-a6278baa51e7

/-
APF Foundation Ledger — theorem node. DRAFT for author and cold review. Not gated, not released, not uploaded.
name: APFPaper1.Continuation.contextEq_sandwich
title: Contextual equivalence is a strong congruence, under ambient heredity; unconditionally when every word is an ambient
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:3284-3298 (lemma and proof), 3301 (W-her).
consumes: no declared input. Named hypothesis in the general form: AmbientHeredity. That hypothesis is NOT an
  adopted input; the Supplement obtains it from W-her, which it calls hypothesized and not derived.
statement:
  (1) ContextEq is reflexive, symmetric and transitive.
  (2) Strong congruence. Under AmbientHeredity, if W and W' are contextually equivalent then so are
      "Lw, then W, then Rw" and "Lw, then W', then Rw", for all words Lw and Rw of matching type.
  (3) With every word an ambient, AmbientHeredity holds trivially, so (2) is unconditional for that relation.
  (4) Contiguous-subword heredity implies AmbientHeredity for the admissible-word ambient class.
  (5) The all-word relation implies the relation restricted to any ambient class. No hypothesis.
  (6) Under AmbientHeredity the restricted relation implies the all-word relation. With (5): under AmbientHeredity
      the two relations are the same.
label: (2) is CONDITIONAL in its general form. (3) is unconditional and is about the all-ambient relation. By (5)
  and (6) that relation coincides with the Supplement's relation whenever AmbientHeredity holds for the
  Supplement's admissible words, which (4) obtains from W-her. Coincidence without heredity is not claimed.
-/
import Definitions.Def_APFPaper1_ContextualEquivalence

set_option autoImplicit false
namespace APFPaper1.Continuation

universe uC uF uX uV
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {Val : Type uV}

/-- Re-bracketing: `P`, then (`Lw`, `M`, `Rw`), then `S` is (`P`,`Lw`), then `M`, then (`Rw`,`S`). -/
theorem sandwich_reassoc {g a' a b b' c : Context} (P : Word Frag g a') (Lw : Word Frag a' a)
    (M : Word Frag a b) (Rw : Word Frag b b') (S : Word Frag b' c) :
    sandwich P (Lw.append (M.append Rw)) S = sandwich (P.append Lw) M (Rw.append S) := by
  simp only [sandwich, Word.append_assoc]

theorem contextEq_refl (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    (Amb : (g h : Context) → Word Frag g h → Prop) {a b : Context} (W : Word Frag a b) :
    ContextEq Defd value Amb W W :=
  fun _ _ _ _ _ _ _ => ⟨Iff.rfl, fun _ _ => rfl⟩

theorem contextEq_symm (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    (Amb : (g h : Context) → Word Frag g h → Prop) {a b : Context} (W W' : Word Frag a b)
    (h : ContextEq Defd value Amb W W') : ContextEq Defd value Amb W' W :=
  fun g c P S x hP hS =>
    ⟨(h g c P S x hP hS).1.symm, fun h1 h2 => ((h g c P S x hP hS).2 h2 h1).symm⟩

theorem contextEq_trans (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    (Amb : (g h : Context) → Word Frag g h → Prop) {a b : Context} (W W' W'' : Word Frag a b)
    (h : ContextEq Defd value Amb W W') (h' : ContextEq Defd value Amb W' W'') :
    ContextEq Defd value Amb W W'' :=
  fun g c P S x hP hS =>
    ⟨(h g c P S x hP hS).1.trans (h' g c P S x hP hS).1,
     fun h1 h3 =>
       have h2 := (h g c P S x hP hS).1.mp h1
       ((h g c P S x hP hS).2 h1 h2).trans ((h' g c P S x hP hS).2 h2 h3)⟩

/-- (2) Strong congruence under ambient heredity. -/
theorem contextEq_sandwich (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    (Amb : (g h : Context) → Word Frag g h → Prop)
    (hher : AmbientHeredity Defd Amb)
    {a' a b b' : Context} (Lw : Word Frag a' a) (Rw : Word Frag b b') (W W' : Word Frag a b)
    (hW : ContextEq Defd value Amb W W') :
    ContextEq Defd value Amb (Lw.append (W.append Rw)) (Lw.append (W'.append Rw)) := by
  intro g c P S x _ _
  rw [sandwich_reassoc P Lw W Rw S, sandwich_reassoc P Lw W' Rw S]
  refine ⟨⟨fun h1 => ?_, fun h2 => ?_⟩, fun h1 h2 => ?_⟩
  · obtain ⟨hA, hB⟩ := hher g a b c (P.append Lw) W (Rw.append S) x h1
    exact (hW g c (P.append Lw) (Rw.append S) x hA hB).1.mp h1
  · obtain ⟨hA, hB⟩ := hher g a b c (P.append Lw) W' (Rw.append S) x h2
    exact (hW g c (P.append Lw) (Rw.append S) x hA hB).1.mpr h2
  · obtain ⟨hA, hB⟩ := hher g a b c (P.append Lw) W (Rw.append S) x h1
    exact (hW g c (P.append Lw) (Rw.append S) x hA hB).2 h1 h2

/-- (3) With every word an ambient, strong congruence needs no hypothesis. -/
theorem contextEq_sandwich_all (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a' a b b' : Context} (Lw : Word Frag a' a) (Rw : Word Frag b b') (W W' : Word Frag a b)
    (hW : ContextEq Defd value (fun _ _ _ => True) W W') :
    ContextEq Defd value (fun _ _ _ => True) (Lw.append (W.append Rw)) (Lw.append (W'.append Rw)) :=
  contextEq_sandwich Defd value (fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩)
    Lw Rw W W' hW

/-- (4) Contiguous-subword heredity gives ambient heredity for the admissible-word class. -/
theorem ambientHeredity_of_subwordHeredity (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (Adm : (g h : Context) → Word Frag g h → Prop)
    (hher : SubwordHeredity Defd Adm) : AmbientHeredity Defd Adm := by
  intro g a b c A M B x hdef
  constructor
  · -- `A` is the middle of: nothing, then `A`, then (`M`,`B`)
    have h : sandwich (Word.nil g) A (M.append B) = sandwich A M B := by
      simp only [sandwich, Word.append]
    exact hher g g a c (Word.nil g) A (M.append B) x (h ▸ hdef)
  · -- `B` is the middle of: (`A`,`M`), then `B`, then nothing
    have h : sandwich (A.append M) B (Word.nil c) = sandwich A M B := by
      simp only [sandwich, Word.append_nil, Word.append_assoc]
    exact hher g b c c (A.append M) B (Word.nil c) x (h ▸ hdef)

/-- (5) The all-ambient relation implies the relation restricted to any ambient class. -/
theorem contextEq_of_all (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    (Amb : (g h : Context) → Word Frag g h → Prop) {a b : Context} (W W' : Word Frag a b)
    (h : ContextEq Defd value (fun _ _ _ => True) W W') : ContextEq Defd value Amb W W' :=
  fun g c P S x _ _ => h g c P S x trivial trivial

/-- (6) Under ambient heredity the restricted relation implies the all-ambient relation. -/
theorem contextEq_all_of_ambientHeredity (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    (Amb : (g h : Context) → Word Frag g h → Prop)
    (hher : AmbientHeredity Defd Amb) {a b : Context} (W W' : Word Frag a b)
    (h : ContextEq Defd value Amb W W') : ContextEq Defd value (fun _ _ _ => True) W W' := by
  intro g c P S x _ _
  refine ⟨⟨fun h1 => ?_, fun h2 => ?_⟩, fun h1 h2 => ?_⟩
  · obtain ⟨hA, hB⟩ := hher g a b c P W S x h1
    exact (h g c P S x hA hB).1.mp h1
  · obtain ⟨hA, hB⟩ := hher g a b c P W' S x h2
    exact (h g c P S x hA hB).1.mpr h2
  · obtain ⟨hA, hB⟩ := hher g a b c P W S x h1
    exact (h g c P S x hA hB).2 h1 h2

end APFPaper1.Continuation


universe uC uF uX uV
theorem solution :
∀ {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX} {Val : Type uV}
  (Defd : (g : Context) → Raw g → APFPaper1.Continuation.WordFrom.{uC, uF} Frag g → Prop)
  (value : (g : Context) → APFPaper1.Continuation.WordFrom.{uC, uF} Frag g → Raw g → Val) {a' a b b' : Context}
  (Lw : APFPaper1.Continuation.Word.{uC, uF} Frag a' a) (Rw : APFPaper1.Continuation.Word.{uC, uF} Frag b b')
  (W W' : APFPaper1.Continuation.Word.{uC, uF} Frag a b),
  APFPaper1.Continuation.ContextEq.{uC, uF, uX, uV} Defd value (fun x x_1 x_2 => True) W W' →
    APFPaper1.Continuation.ContextEq.{uC, uF, uX, uV} Defd value (fun x x_1 x_2 => True)
      (APFPaper1.Continuation.Word.append.{uC, uF} Lw (APFPaper1.Continuation.Word.append.{uC, uF} W Rw))
      (APFPaper1.Continuation.Word.append.{uC, uF} Lw (APFPaper1.Continuation.Word.append.{uC, uF} W' Rw)) := by
  exact @APFPaper1.Continuation.contextEq_sandwich_all
