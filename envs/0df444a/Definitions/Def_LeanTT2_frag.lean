-- Prove2me | Definitions.Def_LeanTT2_frag
-- name    : LeanTT2_frag
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T02:14:38.47851+00:00
-- url     : https://prove2.me/theorems/bf532d9a-f226-4c2f-ba3c-c1e230d220e9
-- title:
--   The extended fragment: judgments, binder apparatus, and the menagerie of thesis section 5.1
-- statement:
--   An abstract interface for a dependent type theory carrying the menagerie of Mario Carneiro's thesis: a carrier of expressions and a carrier of contexts; the judgments of context validity, typehood, propositionhood, typing, the ideal definitional equality, reduction, the algorithmic equality of the kernel, and algorithmic typing; the binder apparatus of context extension, the fresh variable, weakening, and substitution; the menagerie of type formers (sigma, binary sum, universe lift, propositional truncation, W-types, equality, accessibility) together with the unit type and their constructors and recursors; and, as axiom fields, the standard rules: the reflexivity, symmetry, transitivity, and application congruence of the ideal equality, the conversion of reduction to equality, the typing rules of the variable, weakening, the pi former, lambda, and application, beta reduction, proof irrelevance for both equalities, the conversion rule of algorithmic typing, the typing rule of the identity application, and the eight iota rules of page 28 of the thesis. The intended model is the term language of the thesis with the menagerie taken as primitive.
-- source:
--   M. Carneiro, The Type Theory of Lean, 2019, sections 2.2, 2.3, 2.6, 2.7, 3.1.2 and 5.1 (pp. 6-14, 17, 27-28).

import Mathlib

universe u

/-!
# The Type Theory of Lean, part II: the extended fragment

The extended fragment of Mario Carneiro's thesis "The Type Theory of
Lean" (Carnegie Mellon University, 2019): the abstract interface for a
dependent type theory carrying the menagerie of thesis section 5.1. The
structure `Frag` packages the syntax carrier with its contexts, the
judgments (typing, the ideal definitional equality, reduction, the
algorithmic equality of the kernel, and the algorithmic typing judgment),
the binder apparatus, and the eight type constructors of the menagerie
(empty, unit, sigma, sum, ulift, truncation, W, equality, and
accessibility) with their iota rules stated as reduction facts, together
with the conversion rules, the beta rule, and proof irrelevance in both
the ideal and the algorithmic equality (thesis sections 2.2, 2.3, 2.6,
2.7 and 5.1).

The interface is abstract: the carrier and the operations are fields,
and the standard identities live in the axiom fields, so that every
theorem built on the fragment carries the fragment as a hypothesis. The
intended model is the term language of the thesis with the menagerie
taken as primitive (section 5.1), where the iota rules are exactly the
equations displayed on page 28 of the thesis.
-/

namespace LeanTT2

/-- The extended fragment: a dependent type theory with the menagerie of
thesis section 5.1. The fields asserting equations are the standard
rules of the thesis: the conversion rule and the congruences of the
ideal equality, the beta rule, proof irrelevance (in both the ideal and
the algorithmic equality), the algorithmic conversion rule for the
identity application, and the iota rules of the menagerie. -/
structure Frag where
  /-- the expressions of the fragment -/
  E : Type u
  /-- the typing contexts -/
  Ctx : Type u
  /-- the context validity judgment -/
  ok : Ctx → Prop
  /-- the judgment that an expression is a type -/
  isType : Ctx → E → Prop
  /-- the judgment that an expression is a proposition -/
  isProp : Ctx → E → Prop
  /-- the typing judgment -/
  ty : Ctx → E → E → Prop
  /-- the ideal definitional equality of thesis section 2.2 -/
  deq : Ctx → E → E → Prop
  /-- the reduction relation of thesis section 2.3 -/
  red : Ctx → E → E → Prop
  /-- the algorithmic equality of the kernel, thesis section 2.3 -/
  alg : Ctx → E → E → Prop
  /-- the algorithmic typing judgment, thesis section 3.1.2 -/
  aty : Ctx → E → E → Prop
  /-- context extension by one binder -/
  ext : Ctx → E → Ctx
  /-- the freshly bound variable -/
  var0 : E
  /-- weakening of a term under one binder -/
  wkT : E → E
  /-- substitution of a term for the bound variable -/
  substT : E → E → E
  /-- application -/
  app : E → E → E
  /-- lambda abstraction -/
  lamT : E → E → E
  /-- the dependent function type former -/
  piT : E → E → E
  /-- the universe of the fragment's types -/
  Univ : E
  /-- the unit type of the menagerie -/
  oneT : E
  /-- the canonical inhabitant of the unit type -/
  unitT : E
  /-- the identity function at a type -/
  idf : E → E
  /-- the sigma type former -/
  sigmaT : E → E → E
  /-- the pairing of the sigma type -/
  pairT : E → E → E
  /-- the first projection -/
  fst : E → E
  /-- the second projection -/
  snd : E → E
  /-- the binary sum type former -/
  sumT : E → E → E
  /-- the left injection -/
  inl : E → E
  /-- the right injection -/
  inr : E → E
  /-- the case analysis of the binary sum -/
  caseT : E → E → E → E
  /-- the universe lift of a term -/
  up : E → E
  /-- the universe unlift of a term -/
  down : E → E
  /-- the propositional truncation type former -/
  truncT : E → E
  /-- the W-type former of the menagerie -/
  wT : E → E → E
  /-- the supremum constructor of the W-type -/
  supT : E → E → E
  /-- the recursor of the W-type -/
  recW : E → E → E
  /-- the recursive continuation of the W-recursor's computation rule,
  the term for the function b ↦ rec_W e (f b) -/
  recW_cont : E → E → E
  /-- the equality type former -/
  eqT : E → E → E → E
  /-- the reflexivity constructor of the equality type -/
  reflT : E → E
  /-- the recursor of the equality type -/
  recEq : E → E → E → E
  /-- the accessibility type former acc_r x of thesis section 2.6.2 -/
  accT : E → E → E
  /-- the introduction constructor of the accessibility type -/
  introAcc : E → E → E
  /-- the recursor of the accessibility type -/
  recAcc : E → E → E → E
  /-- the recursive continuation of the accessibility recursor's
  computation rule, the term for the function pair (y, h) ↦
  rec_acc e y (f y h) -/
  recAcc_cont : E → E → E
  /-- the ideal equality is reflexive -/
  deq_refl : ∀ (Γ : Ctx) (a : E), deq Γ a a
  /-- the ideal equality is symmetric -/
  deq_symm : ∀ (Γ : Ctx) (a b : E), deq Γ a b → deq Γ b a
  /-- the ideal equality is transitive -/
  deq_trans : ∀ (Γ : Ctx) (a b c : E), deq Γ a b → deq Γ b c → deq Γ a c
  /-- the ideal equality is a congruence for application -/
  deq_app : ∀ (Γ : Ctx) (f g a b : E), deq Γ f g → deq Γ a b →
    deq Γ (app f a) (app g b)
  /-- reduction implies the ideal definitional equality (thesis
  section 2.2) -/
  red_deq : ∀ (Γ : Ctx) (a b : E), red Γ a b → deq Γ a b
  /-- the fresh variable has the type of its binder -/
  ty_var0 : ∀ (Γ : Ctx) (α : E), isType Γ α → ty (ext Γ α) var0 α
  /-- weakening preserves typing under one binder -/
  ty_wk : ∀ (Γ : Ctx) (β a α : E), ty Γ a α → ty (ext Γ β) (wkT a) (wkT α)
  /-- the pi type former produces types -/
  ty_pi : ∀ (Γ : Ctx) (α β : E), isType Γ α → isType (ext Γ α) β →
    isType Γ (piT α β)
  /-- the typing rule of lambda abstraction -/
  ty_lam : ∀ (Γ : Ctx) (α b β : E), isType Γ α → ty (ext Γ α) b β →
    ty Γ (lamT α b) (piT α β)
  /-- the typing rule of application, with the substituted codomain -/
  ty_app : ∀ (Γ : Ctx) (f α β a : E), ty Γ f (piT α β) → ty Γ a α →
    ty Γ (app f a) (substT β a)
  /-- the beta rule, as a reduction fact -/
  ty_beta : ∀ (Γ : Ctx) (α b a : E),
    red Γ (app (lamT α b) a) (substT b a)
  /-- the unit type is a type -/
  isType_one : ∀ (Γ : Ctx), isType Γ oneT
  /-- the canonical inhabitant of the unit type has the unit type -/
  ty_unit : ∀ (Γ : Ctx), ty Γ unitT oneT
  /-- propositions are types -/
  isType_of_isProp : ∀ (Γ : Ctx) (α : E), isProp Γ α → isType Γ α
  /-- the sigma type former produces types -/
  ty_sigma : ∀ (Γ : Ctx) (α β : E), isType Γ α → isType (ext Γ α) β →
    isType Γ (sigmaT α β)
  /-- the binary sum type former produces types -/
  ty_sum : ∀ (Γ : Ctx) (α β : E), isType Γ α → isType Γ β →
    isType Γ (sumT α β)
  /-- the W-type former produces types from a branching type and an
  arity function into the universe -/
  ty_w : ∀ (Γ : Ctx) (A B : E), isType Γ A → ty Γ B (piT A Univ) →
    isType Γ (wT A B)
  /-- the propositional truncation of a type is a proposition -/
  ty_trunc : ∀ (Γ : Ctx) (α : E), isType Γ α → isProp Γ (truncT α)
  /-- proof irrelevance for the ideal equality: any two proofs of the
  same proposition are definitionally equal (thesis section 2.2) -/
  deq_irrel : ∀ (Γ : Ctx) (α a b : E), isProp Γ α → ty Γ a α →
    ty Γ b α → deq Γ a b
  /-- proof irrelevance for the algorithmic equality: the kernel
  accepts any two proofs of the same proposition (thesis sections 2.3
  and 3.1.1) -/
  alg_irrel : ∀ (Γ : Ctx) (α a b : E), isProp Γ α → ty Γ a α →
    ty Γ b α → alg Γ a b
  /-- the algorithmic equality is symmetric -/
  alg_symm : ∀ (Γ : Ctx) (a b : E), alg Γ a b → alg Γ b a
  /-- the conversion rule of the algorithmic typing judgment (thesis
  section 3.1.2) -/
  aty_conv : ∀ (Γ : Ctx) (a α β : E), aty Γ a α → alg Γ α β →
    aty Γ a β
  /-- the algorithmic typing of an identity application: id_α e has
  type α exactly when the inferred type of e is algorithmically equal
  to α (thesis section 3.1.2) -/
  aty_idf : ∀ (Γ : Ctx) (α e γ : E), aty Γ e γ →
    (aty Γ (app (idf α) e) α ↔ alg Γ γ α)
  /-- the identity application reduces to its argument -/
  red_idf : ∀ (Γ : Ctx) (α e : E), red Γ (app (idf α) e) e
  /-- the first projection computes on an explicit pair (page 28) -/
  red_fst : ∀ (Γ : Ctx) (a b : E), red Γ (fst (pairT a b)) a
  /-- the second projection computes on an explicit pair (page 28) -/
  red_snd : ∀ (Γ : Ctx) (a b : E), red Γ (snd (pairT a b)) b
  /-- the case analysis computes on the left injection (page 28) -/
  red_case_inl : ∀ (Γ : Ctx) (a b x : E),
    red Γ (caseT a b (inl x)) (app a x)
  /-- the case analysis computes on the right injection (page 28) -/
  red_case_inr : ∀ (Γ : Ctx) (a b x : E),
    red Γ (caseT a b (inr x)) (app b x)
  /-- the universe unlift computes after a lift (page 28) -/
  red_down_up : ∀ (Γ : Ctx) (x : E), red Γ (down (up x)) x
  /-- the W-recursor computes on an explicit supremum, with the
  recursive continuation (page 28) -/
  red_recW : ∀ (Γ : Ctx) (e a f : E),
    red Γ (recW e (supT a f)) (app (app (app e a) f) (recW_cont e f))
  /-- the equality recursor computes on reflexivity (page 28) -/
  red_recEq : ∀ (Γ : Ctx) (e a : E), red Γ (recEq e a (reflT a)) e
  /-- the accessibility recursor computes on an explicit introduction,
  with the recursive continuation (page 28) -/
  red_recAcc : ∀ (Γ : Ctx) (e x f : E),
    red Γ (recAcc e x (introAcc x f))
      (app (app (app e x) f) (recAcc_cont e f))

end LeanTT2


