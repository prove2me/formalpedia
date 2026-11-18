-- Prove2me | Definitions.Def_LaarakkerOttenVanDenBerg2026_TheoryRevision2
-- name    : LaarakkerOttenVanDenBerg2026_TheoryRevision2
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-17T07:41:24.545195+00:00
-- url     : https://prove2.me/theorems/fb27d9a6-ee45-454d-9d25-1630b00c13d5
-- title:
--   Contextual type theory with large sizes and parametricity
-- statement:
--   The contextual rules of the paper's type theory: dependent products and sums, internal identity and J, function extensionality, a Tarski universe with small constructors and base types, the large size preorder, primitive size recursion with propositional unfolding, small existential and universal size quantifiers, and their substitution coherence. All four parametricity axioms refer to explicitly constructed canonical maps and internal half-adjoint equivalence types. Neither realizability data nor tracker restrictions are assumptions of the abstract theory. Contractibility, quantifier consequences, and the type of fixed-point solutions are defined without assuming their theorem witnesses.
-- source:
--   Laarakker, Otten and van den Berg, Constructing (Co)inductive Types via Large Sizes, arXiv:2602.18921v2, Section 2 and Appendix A, https://arxiv.org/abs/2602.18921v2

import Mathlib.Logic.Basic

/-! Generated from reviewed V2 modules by bundle_v2.py.
See the accompanying manifest for exact input hashes and source order. -/

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_TypeTheoryV2 -/

/-!
# Contextual interfaces for the type theory of large sizes

These interfaces present the structural and type-forming rules of Section 2 and
Appendix A of Laarakker–Otten–van den Berg (2026). `Tm Γ A` is an abstract set of
terms in a context; it is never identified with all metatheoretic functions.
In particular, abstraction accepts a term in an extended context. Realizability
and computability are properties of an interpretation, not additional premises
of these syntactic rules.

The external equalities below describe definitional equality and substitution
coherence. The separate `IdentityTypes.id` represents propositional identity;
no equality reflection or uniqueness of identity proofs is assumed.

This file gives interfaces for individual groups of rules, not a claim that the
full theory has been interpreted. Function extensionality and the four
parametricity equivalence axioms are not yet part of these interfaces.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

set_option linter.checkUnivs false in
/-- A category with families, with transport-explicit substitution equations. -/
structure CwF where
  Ctx : Type u
  Sub : Ctx → Ctx → Type v
  id : {Γ : Ctx} → Sub Γ Γ
  comp : {Γ Δ Θ : Ctx} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  id_comp : ∀ {Γ Δ} (σ : Sub Δ Γ), comp id σ = σ
  comp_id : ∀ {Γ Δ} (σ : Sub Δ Γ), comp σ id = σ
  assoc : ∀ {Γ Δ Θ Ξ} (σ : Sub Δ Γ) (τ : Sub Θ Δ) (υ : Sub Ξ Θ),
    comp (comp σ τ) υ = comp σ (comp τ υ)
  Ty : Ctx → Type w
  Tm : (Γ : Ctx) → Ty Γ → Type t
  tySub : {Γ Δ : Ctx} → Ty Γ → Sub Δ Γ → Ty Δ
  tmSub : {Γ Δ : Ctx} → {A : Ty Γ} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (tySub A σ)
  tySub_id : ∀ {Γ} (A : Ty Γ), tySub A id = A
  tySub_comp : ∀ {Γ Δ Θ} (A : Ty Γ) (σ : Sub Δ Γ) (τ : Sub Θ Δ),
    tySub (tySub A σ) τ = tySub A (comp σ τ)
  tmSub_id : ∀ {Γ} {A : Ty Γ} (a : Tm Γ A), HEq (tmSub a id) a
  tmSub_comp : ∀ {Γ Δ Θ} {A : Ty Γ} (a : Tm Γ A)
    (σ : Sub Δ Γ) (τ : Sub Θ Δ), HEq (tmSub (tmSub a σ) τ) (tmSub a (comp σ τ))
  empty : Ctx
  emptySub : {Γ : Ctx} → Sub Γ empty
  empty_unique : ∀ {Γ} (σ : Sub Γ empty), σ = emptySub
  ext : (Γ : Ctx) → Ty Γ → Ctx
  fst : {Γ : Ctx} → {A : Ty Γ} → Sub (ext Γ A) Γ
  snd : {Γ : Ctx} → {A : Ty Γ} → Tm (ext Γ A) (tySub A fst)
  pair : {Γ Δ : Ctx} → {A : Ty Γ} →
    (σ : Sub Δ Γ) → Tm Δ (tySub A σ) → Sub Δ (ext Γ A)
  pair_fst : ∀ {Γ Δ} {A : Ty Γ} (σ : Sub Δ Γ) (a : Tm Δ (tySub A σ)),
    comp fst (pair σ a) = σ
  pair_snd : ∀ {Γ Δ} {A : Ty Γ} (σ : Sub Δ Γ) (a : Tm Δ (tySub A σ)),
    HEq (tmSub snd (pair σ a)) a
  pair_unique : ∀ {Γ Δ} {A : Ty Γ} (σ : Sub Δ Γ) (a : Tm Δ (tySub A σ))
    (τ : Sub Δ (ext Γ A)), comp fst τ = σ → HEq (tmSub snd τ) a → τ = pair σ a

namespace CwF

variable (C : CwF.{u, v, w, t})

/-- Transport a term along an external (definitional) type equality. -/
def castTm {Γ : C.Ctx} {A B : C.Ty Γ} (h : A = B) (a : C.Tm Γ A) : C.Tm Γ B :=
  h ▸ a

/-- The substitution extending the identity by a term. -/
def termSub {Γ : C.Ctx} {A : C.Ty Γ} (a : C.Tm Γ A) : C.Sub Γ (C.ext Γ A) :=
  C.pair C.id (C.castTm (C.tySub_id A).symm a)

/-- Lift a substitution under one binder. -/
def lift {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : C.Ty Γ) :
    C.Sub (C.ext Δ (C.tySub A σ)) (C.ext Γ A) :=
  C.pair (C.comp σ C.fst) (C.castTm (C.tySub_comp A σ C.fst) C.snd)

/-- The defining equation for the first projection of a term section. -/
theorem termSub_fst {Γ : C.Ctx} {A : C.Ty Γ} (a : C.Tm Γ A) :
    C.comp C.fst (C.termSub a) = C.id :=
  C.pair_fst _ _

/-- External transport does not change the represented term. -/
theorem castTm_heq {Γ : C.Ctx} {A B : C.Ty Γ} (h : A = B) (a : C.Tm Γ A) :
    HEq (C.castTm h a) a := by
  cases h
  rfl

/-- Substitution respects transport of a term's type. -/
theorem tmSub_heq {Γ Δ : C.Ctx} {A B : C.Ty Γ} {a : C.Tm Γ A} {b : C.Tm Γ B}
    (hAB : A = B) (h : HEq a b) (σ : C.Sub Δ Γ) : HEq (C.tmSub a σ) (C.tmSub b σ) := by
  cases hAB
  cases h
  rfl

/-- Substituting a term for the newest variable recovers that term. -/
theorem termSub_snd {Γ : C.Ctx} {A : C.Ty Γ} (a : C.Tm Γ A) :
    HEq (C.tmSub C.snd (C.termSub a)) a :=
  (C.pair_snd _ _).trans (C.castTm_heq _ _)

/-- Weakening a type and then substituting for the fresh variable recovers it. -/
theorem tySub_fst_termSub {Γ : C.Ctx} {A : C.Ty Γ} (B : C.Ty Γ) (a : C.Tm Γ A) :
    C.tySub (C.tySub B C.fst) (C.termSub a) = B := by
  rw [C.tySub_comp, C.termSub_fst, C.tySub_id]

/-- The corresponding equation for a weakened term. -/
theorem tmSub_fst_termSub {Γ : C.Ctx} {A B : C.Ty Γ} (b : C.Tm Γ B) (a : C.Tm Γ A) :
    HEq (C.tmSub (C.tmSub b C.fst) (C.termSub a)) b := by
  have h := C.tmSub_comp b C.fst (C.termSub a)
  rw [C.termSub_fst] at h
  exact h.trans (C.tmSub_id b)

end CwF

/-- Nondependent function types, with contextual abstraction and application.
These are a separately exposed fragment of the source's dependent products. -/
structure FunctionTypes (C : CwF.{u, v, w, t}) where
  arr : {Γ : C.Ctx} → C.Ty Γ → C.Ty Γ → C.Ty Γ
  arr_sub : ∀ {Γ Δ} (A B : C.Ty Γ) (σ : C.Sub Δ Γ),
    C.tySub (arr A B) σ = arr (C.tySub A σ) (C.tySub B σ)
  lam : {Γ : C.Ctx} → {A B : C.Ty Γ} →
    C.Tm (C.ext Γ A) (C.tySub B C.fst) → C.Tm Γ (arr A B)
  app : {Γ : C.Ctx} → {A B : C.Ty Γ} → C.Tm Γ (arr A B) → C.Tm Γ A → C.Tm Γ B
  beta : ∀ {Γ} {A B : C.Ty Γ} (b : C.Tm (C.ext Γ A) (C.tySub B C.fst))
    (a : C.Tm Γ A), HEq (app (lam b) a) (C.tmSub b (C.termSub a))
  eta : ∀ {Γ} {A B : C.Ty Γ} (f : C.Tm Γ (arr A B)),
    lam (app (C.castTm (arr_sub A B C.fst) (C.tmSub f C.fst)) C.snd) = f
  app_sub : ∀ {Γ Δ} {A B : C.Ty Γ} (f : C.Tm Γ (arr A B)) (a : C.Tm Γ A)
    (σ : C.Sub Δ Γ), C.tmSub (app f a) σ =
      app (C.castTm (arr_sub A B σ) (C.tmSub f σ)) (C.tmSub a σ)
  lam_sub : ∀ {Γ Δ} {A B : C.Ty Γ}
    (b : C.Tm (C.ext Γ A) (C.tySub B C.fst)) (σ : C.Sub Δ Γ)
    (b' : C.Tm (C.ext Δ (C.tySub A σ)) (C.tySub (C.tySub B σ) C.fst)),
    HEq (C.tmSub b (C.lift σ A)) b' →
    C.castTm (arr_sub A B σ) (C.tmSub (lam b) σ) = lam b'

namespace FunctionTypes

variable {C : CwF.{u, v, w, t}} (P : FunctionTypes C)

/-- Substitution on an arrow term, transporting its function type. -/
def sub {Γ Δ : C.Ctx} {A B : C.Ty Γ} (f : C.Tm Γ (P.arr A B)) (σ : C.Sub Δ Γ) :
    C.Tm Δ (P.arr (C.tySub A σ) (C.tySub B σ)) :=
  C.castTm (P.arr_sub A B σ) (C.tmSub f σ)

/-- The internal identity function, obtained by contextual abstraction. -/
def identity {Γ : C.Ctx} (A : C.Ty Γ) : C.Tm Γ (P.arr A A) :=
  P.lam C.snd

/-- Internal function composition. -/
def compose {Γ : C.Ctx} {A B D : C.Ty Γ}
    (g : C.Tm Γ (P.arr B D)) (f : C.Tm Γ (P.arr A B)) : C.Tm Γ (P.arr A D) :=
  P.lam (P.app (P.sub g C.fst) (P.app (P.sub f C.fst) C.snd))

end FunctionTypes

/-- Dependent products with contextual abstraction, its inverse, and substitution. -/
structure DependentProducts (C : CwF.{u, v, w, t}) where
  pi : {Γ : C.Ctx} → (A : C.Ty Γ) → C.Ty (C.ext Γ A) → C.Ty Γ
  pi_sub : ∀ {Γ Δ} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (σ : C.Sub Δ Γ),
    C.tySub (pi A B) σ = pi (C.tySub A σ) (C.tySub B (C.lift σ A))
  lam : {Γ : C.Ctx} → {A : C.Ty Γ} → {B : C.Ty (C.ext Γ A)} →
    C.Tm (C.ext Γ A) B → C.Tm Γ (pi A B)
  unlam : {Γ : C.Ctx} → {A : C.Ty Γ} → {B : C.Ty (C.ext Γ A)} →
    C.Tm Γ (pi A B) → C.Tm (C.ext Γ A) B
  beta : ∀ {Γ} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)} (b : C.Tm (C.ext Γ A) B),
    unlam (lam b) = b
  eta : ∀ {Γ} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)} (f : C.Tm Γ (pi A B)),
    lam (unlam f) = f
  lam_sub : ∀ {Γ Δ} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (b : C.Tm (C.ext Γ A) B) (σ : C.Sub Δ Γ),
    C.castTm (pi_sub A B σ) (C.tmSub (lam b) σ) = lam (C.tmSub b (C.lift σ A))

/-- Dependent sums; the projection types retain the dependency on the first component. -/
structure DependentSums (C : CwF.{u, v, w, t}) where
  sigma : {Γ : C.Ctx} → (A : C.Ty Γ) → C.Ty (C.ext Γ A) → C.Ty Γ
  sigma_sub : ∀ {Γ Δ} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (σ : C.Sub Δ Γ),
    C.tySub (sigma A B) σ = sigma (C.tySub A σ) (C.tySub B (C.lift σ A))
  pair : {Γ : C.Ctx} → {A : C.Ty Γ} → {B : C.Ty (C.ext Γ A)} →
    (a : C.Tm Γ A) → C.Tm Γ (C.tySub B (C.termSub a)) → C.Tm Γ (sigma A B)
  fst : {Γ : C.Ctx} → {A : C.Ty Γ} → {B : C.Ty (C.ext Γ A)} →
    C.Tm Γ (sigma A B) → C.Tm Γ A
  snd : {Γ : C.Ctx} → {A : C.Ty Γ} → {B : C.Ty (C.ext Γ A)} →
    (p : C.Tm Γ (sigma A B)) → C.Tm Γ (C.tySub B (C.termSub (fst p)))
  fst_pair : ∀ {Γ} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (a : C.Tm Γ A) (b : C.Tm Γ (C.tySub B (C.termSub a))), fst (pair a b) = a
  snd_pair : ∀ {Γ} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (a : C.Tm Γ A) (b : C.Tm Γ (C.tySub B (C.termSub a))), HEq (snd (pair a b)) b
  eta : ∀ {Γ} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)} (p : C.Tm Γ (sigma A B)),
    pair (fst p) (snd p) = p

/-- Formation, reflexivity, and substitution for internal propositional identity.
There is deliberately no map from an identity term to external Lean equality. -/
structure IdentityTypes (C : CwF.{u, v, w, t}) where
  id : {Γ : C.Ctx} → (A : C.Ty Γ) → C.Tm Γ A → C.Tm Γ A → C.Ty Γ
  refl : {Γ : C.Ctx} → {A : C.Ty Γ} → (a : C.Tm Γ A) → C.Tm Γ (id A a a)
  id_sub : ∀ {Γ Δ} {A : C.Ty Γ} (a b : C.Tm Γ A) (σ : C.Sub Δ Γ),
    C.tySub (id A a b) σ = id (C.tySub A σ) (C.tmSub a σ) (C.tmSub b σ)
  refl_sub : ∀ {Γ Δ} {A : C.Ty Γ} (a : C.Tm Γ A) (σ : C.Sub Δ Γ),
    HEq (C.tmSub (refl a) σ) (refl (C.tmSub a σ))

namespace IdentityTypes

variable {C : CwF.{u, v, w, t}} (I : IdentityTypes C)

/-- Formation respects external transport; this is not equality reflection. -/
theorem id_congr {Γ : C.Ctx} {A B : C.Ty Γ} (h : A = B)
    {a a' : C.Tm Γ A} {b b' : C.Tm Γ B} (ha : HEq a b) (hb : HEq a' b') :
    I.id A a a' = I.id B b b' := by
  cases h
  cases ha
  cases hb
  rfl

/-- In `Γ, y : A`, the type `a = y` with `a` weakened from `Γ`. -/
def basedPath {Γ : C.Ctx} {A : C.Ty Γ} (a : C.Tm Γ A) : C.Ty (C.ext Γ A) :=
  I.id (C.tySub A C.fst) (C.tmSub a C.fst) C.snd

/-- The identity context `Γ, y : A, p : a = y`. -/
def pathContext {Γ : C.Ctx} {A : C.Ty Γ} (a : C.Tm Γ A) : C.Ctx :=
  C.ext (C.ext Γ A) (I.basedPath a)

/-- The identity type in the based path context specializes to `a = b`. -/
theorem basedPath_sub {Γ : C.Ctx} {A : C.Ty Γ} (a b : C.Tm Γ A) :
    C.tySub (I.basedPath a) (C.termSub b) = I.id A a b := by
  rw [basedPath, I.id_sub]
  exact I.id_congr (C.tySub_fst_termSub A b)
    (C.tmSub_fst_termSub a b) (C.termSub_snd b)

/-- Substitute an endpoint and a path into the based identity context. -/
def pathSub {Γ : C.Ctx} {A : C.Ty Γ} (a b : C.Tm Γ A)
    (p : C.Tm Γ (I.id A a b)) : C.Sub Γ (I.pathContext a) :=
  C.pair (C.termSub b) (C.castTm (I.basedPath_sub a b).symm p)

end IdentityTypes

/-- Based identity elimination, equivalent to the source's two-endpoint `J`
after weakening the first endpoint into the context. The motive is an actual
contextual type over endpoints and paths, not an arbitrary Lean function. -/
structure IdentityElimination (C : CwF.{u, v, w, t}) (I : IdentityTypes C) where
  elim : ∀ {Γ} {A : C.Ty Γ} (a : C.Tm Γ A) (M : C.Ty (I.pathContext a)),
    C.Tm Γ (C.tySub M (I.pathSub a a (I.refl a))) →
    (b : C.Tm Γ A) → (p : C.Tm Γ (I.id A a b)) →
    C.Tm Γ (C.tySub M (I.pathSub a b p))
  beta : ∀ {Γ} {A : C.Ty Γ} (a : C.Tm Γ A) (M : C.Ty (I.pathContext a))
    (d : C.Tm Γ (C.tySub M (I.pathSub a a (I.refl a)))),
    elim a M d a (I.refl a) = d

/-- A Tarski universe and its decoding operation, stable under substitution. -/
structure Universe (C : CwF.{u, v, w, t}) where
  type : (Γ : C.Ctx) → C.Ty Γ
  type_sub : ∀ {Γ Δ} (σ : C.Sub Δ Γ), C.tySub (type Γ) σ = type Δ
  el : {Γ : C.Ctx} → C.Tm Γ (type Γ) → C.Ty Γ
  el_sub : ∀ {Γ Δ} (A : C.Tm Γ (type Γ)) (σ : C.Sub Δ Γ),
    C.tySub (el A) σ = el (C.castTm (type_sub σ) (C.tmSub A σ))

namespace Universe

variable {C : CwF.{u, v, w, t}} (U : Universe C)

/-- A small-type code in a context. -/
abbrev Code (Γ : C.Ctx) := C.Tm Γ (U.type Γ)

/-- Substitution on universe codes. -/
def sub {Γ Δ : C.Ctx} (A : U.Code Γ) (σ : C.Sub Δ Γ) : U.Code Δ :=
  C.castTm (U.type_sub σ) (C.tmSub A σ)

/-- The generic universe code in a context extended by `U`. -/
def generic (Γ : C.Ctx) : U.Code (C.ext Γ (U.type Γ)) :=
  C.castTm (U.type_sub C.fst) C.snd

/-- Extend a substitution by a universe code. -/
def extend {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : U.Code Δ) :
    C.Sub Δ (C.ext Γ (U.type Γ)) :=
  C.pair σ (C.castTm (U.type_sub σ).symm A)

/-- Universe-code substitution respects composition. -/
theorem sub_comp {Γ Δ Θ : C.Ctx} (A : U.Code Γ) (σ : C.Sub Δ Γ) (τ : C.Sub Θ Δ) :
    U.sub (U.sub A σ) τ = U.sub A (C.comp σ τ) := by
  apply eq_of_heq
  exact (C.castTm_heq _ _).trans
    ((C.tmSub_heq (U.type_sub σ).symm (C.castTm_heq _ _) τ).trans
      ((C.tmSub_comp A σ τ).trans (C.castTm_heq _ _).symm))

/-- The generic universe code specializes to the code extending a substitution. -/
theorem generic_sub_extend {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : U.Code Δ) :
    U.sub (U.generic Γ) (U.extend σ A) = A := by
  apply eq_of_heq
  exact (C.castTm_heq _ _).trans
    ((C.tmSub_heq (U.type_sub C.fst).symm (C.castTm_heq _ _) (U.extend σ A)).trans
      ((C.pair_snd _ _).trans (C.castTm_heq _ _)))

/-- Forgetting the last universe code recovers the original substitution. -/
theorem extend_fst {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : U.Code Δ) :
    C.comp C.fst (U.extend σ A) = σ :=
  C.pair_fst _ _

end Universe

/-- Closure of the Tarski universe under the source's small type constructors. -/
structure SmallTypeConstructors (C : CwF.{u, v, w, t})
    (U : Universe C) (P : DependentProducts C) (S : DependentSums C)
    (I : IdentityTypes C) where
  pi : {Γ : C.Ctx} → (A : U.Code Γ) → U.Code (C.ext Γ (U.el A)) → U.Code Γ
  sigma : {Γ : C.Ctx} → (A : U.Code Γ) → U.Code (C.ext Γ (U.el A)) → U.Code Γ
  id : {Γ : C.Ctx} → (A : U.Code Γ) → C.Tm Γ (U.el A) → C.Tm Γ (U.el A) → U.Code Γ
  el_pi : ∀ {Γ} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A))),
    U.el (pi A B) = P.pi (U.el A) (U.el B)
  el_sigma : ∀ {Γ} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A))),
    U.el (sigma A B) = S.sigma (U.el A) (U.el B)
  el_id : ∀ {Γ} (A : U.Code Γ) (a b : C.Tm Γ (U.el A)),
    U.el (id A a b) = I.id (U.el A) a b

/-- The large size type, its preorder, and the source's proof-irrelevance rule
for that preorder. Proof irrelevance here is an internal term, not Lean equality. -/
structure SizeRules (C : CwF.{u, v, w, t}) (U : Universe C) (I : IdentityTypes C) where
  type : (Γ : C.Ctx) → C.Ty Γ
  type_sub : ∀ {Γ Δ} (σ : C.Sub Δ Γ), C.tySub (type Γ) σ = type Δ
  zero : {Γ : C.Ctx} → C.Tm Γ (type Γ)
  succ : {Γ : C.Ctx} → C.Tm Γ (type Γ) → C.Tm Γ (type Γ)
  le : {Γ : C.Ctx} → C.Tm Γ (type Γ) → C.Tm Γ (type Γ) → U.Code Γ
  le_zero : ∀ {Γ} (i : C.Tm Γ (type Γ)), C.Tm Γ (U.el (le zero i))
  le_succ : ∀ {Γ} (i : C.Tm Γ (type Γ)), C.Tm Γ (U.el (le i (succ i)))
  le_refl : ∀ {Γ} (i : C.Tm Γ (type Γ)), C.Tm Γ (U.el (le i i))
  le_trans : ∀ {Γ} {i j k : C.Tm Γ (type Γ)},
    C.Tm Γ (U.el (le i j)) → C.Tm Γ (U.el (le j k)) → C.Tm Γ (U.el (le i k))
  le_prop : ∀ {Γ} {i j : C.Tm Γ (type Γ)} (p q : C.Tm Γ (U.el (le i j))),
    C.Tm Γ (I.id (U.el (le i j)) p q)

namespace SizeRules

variable {C : CwF.{u, v, w, t}} {U : Universe C} {I : IdentityTypes C}
    (Z : SizeRules C U I)

/-- Reindex a term of the large size type. -/
def sub {Γ Δ : C.Ctx} (i : C.Tm Γ (Z.type Γ)) (σ : C.Sub Δ Γ) :
    C.Tm Δ (Z.type Δ) :=
  C.castTm (Z.type_sub σ) (C.tmSub i σ)

/-- The generic size in `Γ, i : Size`. -/
def generic (Γ : C.Ctx) : C.Tm (C.ext Γ (Z.type Γ)) (Z.type (C.ext Γ (Z.type Γ))) :=
  C.castTm (Z.type_sub C.fst) C.snd

/-- Extend a substitution by a size term. -/
def extend {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (i : C.Tm Δ (Z.type Δ)) :
    C.Sub Δ (C.ext Γ (Z.type Γ)) :=
  C.pair σ (C.castTm (Z.type_sub σ).symm i)

/-- In `Γ, i : Size, j : Size`, the small type `j < i`. -/
def bound {Γ : C.Ctx} :
    C.Ty (C.ext (C.ext Γ (Z.type Γ)) (Z.type (C.ext Γ (Z.type Γ)))) :=
  U.el (Z.le (Z.succ (Z.generic (C.ext Γ (Z.type Γ))))
    (Z.sub (Z.generic Γ) C.fst))

/-- Select the inner size `j` from `Γ, i : Size, j : Size`. -/
def inner {Γ : C.Ctx} :
    C.Sub (C.ext (C.ext Γ (Z.type Γ)) (Z.type (C.ext Γ (Z.type Γ))))
      (C.ext Γ (Z.type Γ)) :=
  Z.extend (C.comp C.fst C.fst) (Z.generic (C.ext Γ (Z.type Γ)))

/-- The source abbreviation `Π j : Size, j < i → A(j)` in context `Γ, i : Size`.
For a large family the products are large dependent products. -/
def bounded (P : DependentProducts C) (F : FunctionTypes C)
    {Γ : C.Ctx} (A : C.Ty (C.ext Γ (Z.type Γ))) : C.Ty (C.ext Γ (Z.type Γ)) :=
  P.pi (Z.type (C.ext Γ (Z.type Γ))) (F.arr Z.bound (C.tySub A Z.inner))

/-- Restrict an internal dependent function to sizes below the generic size.
This is the source term `λ j < i, h j`, formed solely by contextual abstraction. -/
def restrict (P : DependentProducts C) (F : FunctionTypes C)
    {Γ : C.Ctx} {A : C.Ty (C.ext Γ (Z.type Γ))}
    (h : C.Tm Γ (P.pi (Z.type Γ) A)) :
    C.Tm (C.ext Γ (Z.type Γ)) (Z.bounded P F A) :=
  P.lam (F.lam (C.tmSub (C.tmSub (P.unlam h) Z.inner) C.fst))

end SizeRules

/-- The source's primitive size elimination rule and its propositional β-rule.
Neither uniqueness nor an algebraic fixed-point theorem is a field. -/
structure SizeRecursion (C : CwF.{u, v, w, t}) (U : Universe C)
    (I : IdentityTypes C) (Z : SizeRules C U I)
    (P : DependentProducts C) (F : FunctionTypes C) where
  fix : ∀ {Γ} (A : C.Ty (C.ext Γ (Z.type Γ))),
    C.Tm Γ (P.pi (Z.type Γ) (F.arr (Z.bounded P F A) A)) →
    C.Tm Γ (P.pi (Z.type Γ) A)
  beta : ∀ {Γ} (A : C.Ty (C.ext Γ (Z.type Γ)))
    (f : C.Tm Γ (P.pi (Z.type Γ) (F.arr (Z.bounded P F A) A))),
    C.Tm Γ (P.pi (Z.type Γ)
      (I.id A (P.unlam (fix A f))
        (F.app (P.unlam f) (Z.restrict P F (fix A f)))))

/-- Small universal quantification over the large size type. Both introduction
and generic application act on contextual terms, with the source's β/η equations. -/
structure UniversalSizeQuantifier (C : CwF.{u, v, w, t})
    (U : Universe C) (I : IdentityTypes C) (Z : SizeRules C U I) where
  code : {Γ : C.Ctx} → U.Code (C.ext Γ (Z.type Γ)) → U.Code Γ
  lam : {Γ : C.Ctx} → {A : U.Code (C.ext Γ (Z.type Γ))} →
    C.Tm (C.ext Γ (Z.type Γ)) (U.el A) → C.Tm Γ (U.el (code A))
  unlam : {Γ : C.Ctx} → {A : U.Code (C.ext Γ (Z.type Γ))} →
    C.Tm Γ (U.el (code A)) → C.Tm (C.ext Γ (Z.type Γ)) (U.el A)
  beta : ∀ {Γ} {A : U.Code (C.ext Γ (Z.type Γ))}
    (a : C.Tm (C.ext Γ (Z.type Γ)) (U.el A)), unlam (lam a) = a
  eta : ∀ {Γ} {A : U.Code (C.ext Γ (Z.type Γ))}
    (f : C.Tm Γ (U.el (code A))), lam (unlam f) = f

/-- Small existential quantification, including dependent elimination only to
a small motive. The generic pair lives in `Γ, i : Size, x : A(i)`; the eliminator
takes a contextual branch over precisely that context. -/
structure ExistentialSizeQuantifier (C : CwF.{u, v, w, t})
    (U : Universe C) (I : IdentityTypes C) (Z : SizeRules C U I) where
  code : {Γ : C.Ctx} → U.Code (C.ext Γ (Z.type Γ)) → U.Code Γ
  pair : ∀ {Γ} (A : U.Code (C.ext Γ (Z.type Γ))),
    C.Tm (C.ext (C.ext Γ (Z.type Γ)) (U.el A))
      (C.tySub (U.el (code A)) (C.comp C.fst C.fst))
  elim : ∀ {Γ} (A : U.Code (C.ext Γ (Z.type Γ)))
    (M : U.Code (C.ext Γ (U.el (code A)))),
    C.Tm (C.ext (C.ext Γ (Z.type Γ)) (U.el A))
      (C.tySub (U.el M) (C.pair (C.comp C.fst C.fst) (pair A))) →
    C.Tm (C.ext Γ (U.el (code A))) (U.el M)
  beta : ∀ {Γ} (A : U.Code (C.ext Γ (Z.type Γ)))
    (M : U.Code (C.ext Γ (U.el (code A))))
    (p : C.Tm (C.ext (C.ext Γ (Z.type Γ)) (U.el A))
      (C.tySub (U.el M) (C.pair (C.comp C.fst C.fst) (pair A)))),
    C.tmSub (elim A M p) (C.pair (C.comp C.fst C.fst) (pair A)) = p

/-- The internal contractibility type `Σ x : A, Π y : A, x = y`.
Its identity witnesses remain internal terms. -/
def contractible {C : CwF.{u, v, w, t}} (P : DependentProducts C)
    (S : DependentSums C) (I : IdentityTypes C) {Γ : C.Ctx} (A : C.Ty Γ) : C.Ty Γ :=
  S.sigma A (P.pi (C.tySub A C.fst)
    (I.id (C.tySub (C.tySub A C.fst) C.fst) (C.tmSub C.snd C.fst) C.snd))

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_TypeTheoryRulesV2 -/

/-!
# Further contextual rules and substitution stability

This module supplies the source's base-type rules and the substitution stability
of its size operations and quantifiers. It remains separate from the underlying
CwF interface so that interpretations can be constructed in stages.

No realizability assumptions, external function introduction rules, or
fixed-point uniqueness principles occur here.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

variable {C : CwF.{u, v, w, t}}

/-- The nondependent function interface is the corresponding special case of
dependent products, as required by the source notation `A → B`. -/
structure FunctionProductCompatibility (F : FunctionTypes C) (P : DependentProducts C) where
  arr_eq : ∀ {Γ} (A B : C.Ty Γ), F.arr A B = P.pi A (C.tySub B C.fst)
  lam_eq : ∀ {Γ} {A B : C.Ty Γ} (b : C.Tm (C.ext Γ A) (C.tySub B C.fst)),
    HEq (F.lam b) (P.lam b)

/-- Substitution coherence for dependent sum introduction and projections. -/
structure DependentSumSubstitution (S : DependentSums C) where
  pair_sub : ∀ {Γ Δ} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (a : C.Tm Γ A) (b : C.Tm Γ (C.tySub B (C.termSub a))) (σ : C.Sub Δ Γ)
    (b' : C.Tm Δ (C.tySub (C.tySub B (C.lift σ A)) (C.termSub (C.tmSub a σ)))),
    HEq (C.tmSub b σ) b' → HEq (C.tmSub (S.pair a b) σ) (S.pair (C.tmSub a σ) b')
  fst_sub : ∀ {Γ Δ} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (p : C.Tm Γ (S.sigma A B)) (σ : C.Sub Δ Γ),
    C.tmSub (S.fst p) σ = S.fst (C.castTm (S.sigma_sub A B σ) (C.tmSub p σ))
  snd_sub : ∀ {Γ Δ} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (p : C.Tm Γ (S.sigma A B)) (σ : C.Sub Δ Γ),
    HEq (C.tmSub (S.snd p) σ) (S.snd (C.castTm (S.sigma_sub A B σ) (C.tmSub p σ)))

/-- Empty, unit, and boolean types as codes in the source's Tarski universe,
including their dependent elimination and computation rules. -/
structure BaseTypes (U : Universe C) where
  empty : {Γ : C.Ctx} → U.Code Γ
  unit : {Γ : C.Ctx} → U.Code Γ
  bool : {Γ : C.Ctx} → U.Code Γ
  star : {Γ : C.Ctx} → C.Tm Γ (U.el unit)
  false : {Γ : C.Ctx} → C.Tm Γ (U.el bool)
  true : {Γ : C.Ctx} → C.Tm Γ (U.el bool)
  empty_sub : ∀ {Γ Δ} (σ : C.Sub Δ Γ), U.sub empty σ = empty
  unit_sub : ∀ {Γ Δ} (σ : C.Sub Δ Γ), U.sub unit σ = unit
  bool_sub : ∀ {Γ Δ} (σ : C.Sub Δ Γ), U.sub bool σ = bool
  star_sub : ∀ {Γ Δ} (σ : C.Sub Δ Γ), HEq (C.tmSub star σ) (@star Δ)
  false_sub : ∀ {Γ Δ} (σ : C.Sub Δ Γ), HEq (C.tmSub false σ) (@false Δ)
  true_sub : ∀ {Γ Δ} (σ : C.Sub Δ Γ), HEq (C.tmSub true σ) (@true Δ)
  emptyElim : ∀ {Γ} (M : C.Ty (C.ext Γ (U.el empty))),
    C.Tm (C.ext Γ (U.el empty)) M
  unitElim : ∀ {Γ} (M : C.Ty (C.ext Γ (U.el unit))),
    C.Tm Γ (C.tySub M (C.termSub star)) → C.Tm (C.ext Γ (U.el unit)) M
  unit_beta : ∀ {Γ} (M : C.Ty (C.ext Γ (U.el unit)))
    (d : C.Tm Γ (C.tySub M (C.termSub star))),
    C.tmSub (unitElim M d) (C.termSub star) = d
  boolElim : ∀ {Γ} (M : C.Ty (C.ext Γ (U.el bool))),
    C.Tm Γ (C.tySub M (C.termSub false)) →
    C.Tm Γ (C.tySub M (C.termSub true)) → C.Tm (C.ext Γ (U.el bool)) M
  bool_beta_false : ∀ {Γ} (M : C.Ty (C.ext Γ (U.el bool)))
    (f : C.Tm Γ (C.tySub M (C.termSub false)))
    (t : C.Tm Γ (C.tySub M (C.termSub true))),
    C.tmSub (boolElim M f t) (C.termSub false) = f
  bool_beta_true : ∀ {Γ} (M : C.Ty (C.ext Γ (U.el bool)))
    (f : C.Tm Γ (C.tySub M (C.termSub false)))
    (t : C.Tm Γ (C.tySub M (C.termSub true))),
    C.tmSub (boolElim M f t) (C.termSub true) = t

namespace SizeRules

variable {U : Universe C} {I : IdentityTypes C} (Z : SizeRules C U I)

/-- Lift a substitution under a size binder, accounting for stability of Size. -/
def lift {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) :
    C.Sub (C.ext Δ (Z.type Δ)) (C.ext Γ (Z.type Γ)) :=
  Z.extend (C.comp σ C.fst) (Z.generic Δ)

end SizeRules

/-- Substitution coherence of the source's size constructors and preorder terms. -/
structure SizeSubstitution (U : Universe C) (I : IdentityTypes C) (Z : SizeRules C U I) where
  zero_sub : ∀ {Γ Δ} (σ : C.Sub Δ Γ), Z.sub Z.zero σ = Z.zero
  succ_sub : ∀ {Γ Δ} (i : C.Tm Γ (Z.type Γ)) (σ : C.Sub Δ Γ),
    Z.sub (Z.succ i) σ = Z.succ (Z.sub i σ)
  le_sub : ∀ {Γ Δ} (i j : C.Tm Γ (Z.type Γ)) (σ : C.Sub Δ Γ),
    U.sub (Z.le i j) σ = Z.le (Z.sub i σ) (Z.sub j σ)
  le_zero_sub : ∀ {Γ Δ} (i : C.Tm Γ (Z.type Γ)) (σ : C.Sub Δ Γ),
    HEq (C.tmSub (Z.le_zero i) σ) (Z.le_zero (Z.sub i σ))
  le_succ_sub : ∀ {Γ Δ} (i : C.Tm Γ (Z.type Γ)) (σ : C.Sub Δ Γ),
    HEq (C.tmSub (Z.le_succ i) σ) (Z.le_succ (Z.sub i σ))
  le_refl_sub : ∀ {Γ Δ} (i : C.Tm Γ (Z.type Γ)) (σ : C.Sub Δ Γ),
    HEq (C.tmSub (Z.le_refl i) σ) (Z.le_refl (Z.sub i σ))
  le_trans_sub : ∀ {Γ Δ} {i j k : C.Tm Γ (Z.type Γ)}
    (p : C.Tm Γ (U.el (Z.le i j))) (q : C.Tm Γ (U.el (Z.le j k))) (σ : C.Sub Δ Γ)
    (p' : C.Tm Δ (U.el (Z.le (Z.sub i σ) (Z.sub j σ))))
    (q' : C.Tm Δ (U.el (Z.le (Z.sub j σ) (Z.sub k σ)))),
    HEq (C.tmSub p σ) p' → HEq (C.tmSub q σ) q' →
    HEq (C.tmSub (Z.le_trans p q) σ) (Z.le_trans p' q')
  le_prop_sub : ∀ {Γ Δ} {i j : C.Tm Γ (Z.type Γ)}
    (p q : C.Tm Γ (U.el (Z.le i j))) (σ : C.Sub Δ Γ)
    (p' q' : C.Tm Δ (U.el (Z.le (Z.sub i σ) (Z.sub j σ)))),
    HEq (C.tmSub p σ) p' → HEq (C.tmSub q σ) q' →
    HEq (C.tmSub (Z.le_prop p q) σ) (Z.le_prop p' q')

/-- Substitution coherence of the primitive size fixpoint and its propositional
unfolding proof. Transported recursive-step terms are stated explicitly. -/
structure SizeRecursionSubstitution (U : Universe C) (I : IdentityTypes C)
    (Z : SizeRules C U I) (P : DependentProducts C) (F : FunctionTypes C)
    (R : SizeRecursion C U I Z P F) where
  fix_sub : ∀ {Γ Δ} (A : C.Ty (C.ext Γ (Z.type Γ)))
    (f : C.Tm Γ (P.pi (Z.type Γ) (F.arr (Z.bounded P F A) A))) (σ : C.Sub Δ Γ)
    (f' : C.Tm Δ (P.pi (Z.type Δ)
      (F.arr (Z.bounded P F (C.tySub A (Z.lift σ))) (C.tySub A (Z.lift σ))))),
    HEq (C.tmSub f σ) f' → HEq (C.tmSub (R.fix A f) σ) (R.fix (C.tySub A (Z.lift σ)) f')
  beta_sub : ∀ {Γ Δ} (A : C.Ty (C.ext Γ (Z.type Γ)))
    (f : C.Tm Γ (P.pi (Z.type Γ) (F.arr (Z.bounded P F A) A))) (σ : C.Sub Δ Γ)
    (f' : C.Tm Δ (P.pi (Z.type Δ)
      (F.arr (Z.bounded P F (C.tySub A (Z.lift σ))) (C.tySub A (Z.lift σ))))),
    HEq (C.tmSub f σ) f' → HEq (C.tmSub (R.beta A f) σ) (R.beta (C.tySub A (Z.lift σ)) f')

/-- Substitution coherence of the small universal size quantifier. -/
structure UniversalSizeSubstitution (U : Universe C) (I : IdentityTypes C)
    (Z : SizeRules C U I) (Q : UniversalSizeQuantifier C U I Z) where
  code_sub : ∀ {Γ Δ} (A : U.Code (C.ext Γ (Z.type Γ))) (σ : C.Sub Δ Γ),
    U.sub (Q.code A) σ = Q.code (U.sub A (Z.lift σ))
  lam_sub : ∀ {Γ Δ} {A : U.Code (C.ext Γ (Z.type Γ))}
    (a : C.Tm (C.ext Γ (Z.type Γ)) (U.el A)) (σ : C.Sub Δ Γ),
    HEq (C.tmSub (Q.lam a) σ)
      (Q.lam (C.castTm (U.el_sub A (Z.lift σ)) (C.tmSub a (Z.lift σ))))
  unlam_sub : ∀ {Γ Δ} {A : U.Code (C.ext Γ (Z.type Γ))}
    (f : C.Tm Γ (U.el (Q.code A))) (σ : C.Sub Δ Γ)
    (f' : C.Tm Δ (U.el (Q.code (U.sub A (Z.lift σ))))),
    HEq (C.tmSub f σ) f' → HEq (C.tmSub (Q.unlam f) (Z.lift σ)) (Q.unlam f')

/-- Substitution coherence for existential type formation. Its elimination
rule is already contextual in `ExistentialSizeQuantifier`. -/
structure ExistentialSizeSubstitution (U : Universe C) (I : IdentityTypes C)
    (Z : SizeRules C U I) (Q : ExistentialSizeQuantifier C U I Z) where
  code_sub : ∀ {Γ Δ} (A : U.Code (C.ext Γ (Z.type Γ))) (σ : C.Sub Δ Γ),
    U.sub (Q.code A) σ = Q.code (U.sub A (Z.lift σ))

namespace Universe

variable (U : Universe C)

/-- Lift a substitution under a variable of a decoded small type. -/
def liftEl {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : U.Code Γ) :
    C.Sub (C.ext Δ (U.el (U.sub A σ))) (C.ext Γ (U.el A)) :=
  C.pair (C.comp σ C.fst)
    (C.castTm ((congrArg (fun B => C.tySub B C.fst) (U.el_sub A σ).symm).trans
      (C.tySub_comp (U.el A) σ C.fst)) C.snd)

/-- The same context lift with a definitionally equal target code. -/
def liftElAs {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : U.Code Γ) (B : U.Code Δ)
    (h : U.sub A σ = B) : C.Sub (C.ext Δ (U.el B)) (C.ext Γ (U.el A)) :=
  h ▸ U.liftEl σ A

end Universe

/-- Substitution coherence of the base-type eliminators. The code equalities
select the exact lifted context; branch terms are transported explicitly. -/
structure BaseTypeSubstitution (U : Universe C) (B : BaseTypes U) where
  emptyElim_sub : ∀ {Γ Δ} (M : C.Ty (C.ext Γ (U.el B.empty))) (σ : C.Sub Δ Γ),
    C.tmSub (B.emptyElim M) (U.liftElAs σ B.empty B.empty (B.empty_sub σ)) =
      B.emptyElim (C.tySub M (U.liftElAs σ B.empty B.empty (B.empty_sub σ)))
  unitElim_sub : ∀ {Γ Δ} (M : C.Ty (C.ext Γ (U.el B.unit)))
    (d : C.Tm Γ (C.tySub M (C.termSub B.star))) (σ : C.Sub Δ Γ)
    (d' : C.Tm Δ (C.tySub
      (C.tySub M (U.liftElAs σ B.unit B.unit (B.unit_sub σ))) (C.termSub B.star))),
    HEq (C.tmSub d σ) d' →
    C.tmSub (B.unitElim M d) (U.liftElAs σ B.unit B.unit (B.unit_sub σ)) =
      B.unitElim (C.tySub M (U.liftElAs σ B.unit B.unit (B.unit_sub σ))) d'
  boolElim_sub : ∀ {Γ Δ} (M : C.Ty (C.ext Γ (U.el B.bool)))
    (f : C.Tm Γ (C.tySub M (C.termSub B.false)))
    (t : C.Tm Γ (C.tySub M (C.termSub B.true))) (σ : C.Sub Δ Γ)
    (f' : C.Tm Δ (C.tySub
      (C.tySub M (U.liftElAs σ B.bool B.bool (B.bool_sub σ))) (C.termSub B.false)))
    (t' : C.Tm Δ (C.tySub
      (C.tySub M (U.liftElAs σ B.bool B.bool (B.bool_sub σ))) (C.termSub B.true))),
    HEq (C.tmSub f σ) f' → HEq (C.tmSub t σ) t' →
    C.tmSub (B.boolElim M f t) (U.liftElAs σ B.bool B.bool (B.bool_sub σ)) =
      B.boolElim (C.tySub M (U.liftElAs σ B.bool B.bool (B.bool_sub σ))) f' t'

/-- Substitution coherence for existential pairing and dependent elimination. -/
structure ExistentialTermSubstitution (U : Universe C) (I : IdentityTypes C)
    (Z : SizeRules C U I) (E : ExistentialSizeQuantifier C U I Z)
    (ES : ExistentialSizeSubstitution U I Z E) where
  pair_sub : ∀ {Γ Δ} (A : U.Code (C.ext Γ (Z.type Γ))) (σ : C.Sub Δ Γ),
    HEq (C.tmSub (E.pair A) (U.liftEl (Z.lift σ) A)) (E.pair (U.sub A (Z.lift σ)))
  elim_sub : ∀ {Γ Δ} (A : U.Code (C.ext Γ (Z.type Γ)))
    (M : U.Code (C.ext Γ (U.el (E.code A))))
    (b : C.Tm (C.ext (C.ext Γ (Z.type Γ)) (U.el A))
      (C.tySub (U.el M) (C.pair (C.comp C.fst C.fst) (E.pair A))))
    (σ : C.Sub Δ Γ)
    (b' : C.Tm (C.ext (C.ext Δ (Z.type Δ)) (U.el (U.sub A (Z.lift σ))))
      (C.tySub
        (U.el (U.sub M
          (U.liftElAs σ (E.code A) (E.code (U.sub A (Z.lift σ))) (ES.code_sub A σ))))
        (C.pair (C.comp C.fst C.fst) (E.pair (U.sub A (Z.lift σ)))))),
    HEq (C.tmSub b (U.liftEl (Z.lift σ) A)) b' →
    HEq (C.tmSub (E.elim A M b)
      (U.liftElAs σ (E.code A) (E.code (U.sub A (Z.lift σ))) (ES.code_sub A σ)))
      (E.elim (U.sub A (Z.lift σ))
        (U.sub M (U.liftElAs σ (E.code A) (E.code (U.sub A (Z.lift σ))) (ES.code_sub A σ))) b')

/-- Substitution coherence of the universe's dependent product, dependent sum,
and identity codes. -/
structure SmallTypeSubstitution (U : Universe C) (P : DependentProducts C)
    (S : DependentSums C) (I : IdentityTypes C) (K : SmallTypeConstructors C U P S I) where
  pi_sub : ∀ {Γ Δ} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A))) (σ : C.Sub Δ Γ),
    U.sub (K.pi A B) σ = K.pi (U.sub A σ) (U.sub B (U.liftEl σ A))
  sigma_sub : ∀ {Γ Δ} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A))) (σ : C.Sub Δ Γ),
    U.sub (K.sigma A B) σ = K.sigma (U.sub A σ) (U.sub B (U.liftEl σ A))
  id_sub : ∀ {Γ Δ} (A : U.Code Γ) (a b : C.Tm Γ (U.el A)) (σ : C.Sub Δ Γ),
    U.sub (K.id A a b) σ = K.id (U.sub A σ)
      (C.castTm (U.el_sub A σ) (C.tmSub a σ))
      (C.castTm (U.el_sub A σ) (C.tmSub b σ))

namespace SizeRules

variable {U : Universe C} {I : IdentityTypes C} (Z : SizeRules C U I)

/-- The universe code for the source abbreviation `j < i`. -/
def boundCode {Γ : C.Ctx} :
    U.Code (C.ext (C.ext Γ (Z.type Γ)) (Z.type (C.ext Γ (Z.type Γ)))) :=
  Z.le (Z.succ (Z.generic (C.ext Γ (Z.type Γ)))) (Z.sub (Z.generic Γ) C.fst)

/-- The code of the bounded existential `∃ j < i, A(j)`. -/
def diamond {P : DependentProducts C} {S : DependentSums C}
    (K : SmallTypeConstructors C U P S I) (E : ExistentialSizeQuantifier C U I Z)
    {Γ : C.Ctx} (A : U.Code (C.ext Γ (Z.type Γ))) : U.Code (C.ext Γ (Z.type Γ)) :=
  E.code (K.sigma Z.boundCode (U.sub (U.sub A Z.inner) C.fst))

/-- The code of the bounded universal `∀ j < i, A(j)`. -/
def box {P : DependentProducts C} {S : DependentSums C}
    (K : SmallTypeConstructors C U P S I) (Q : UniversalSizeQuantifier C U I Z)
    {Γ : C.Ctx} (A : U.Code (C.ext Γ (Z.type Γ))) : U.Code (C.ext Γ (Z.type Γ)) :=
  Q.code (K.pi Z.boundCode (U.sub (U.sub A Z.inner) C.fst))

/-- The canonical forward operation for universal quantification over `<`:
`f ↦ λ i, λ j < i, f j`. Its body uses only the source introduction rules. -/
def forallBound {P : DependentProducts C} {S : DependentSums C}
    (K : SmallTypeConstructors C U P S I) (Q : UniversalSizeQuantifier C U I Z)
    {Γ : C.Ctx} {A : U.Code (C.ext Γ (Z.type Γ))}
    (f : C.Tm Γ (U.el (Q.code A))) : C.Tm Γ (U.el (Q.code (Z.box K Q A))) :=
  Q.lam (Q.lam (C.castTm (K.el_pi Z.boundCode (U.sub (U.sub A Z.inner) C.fst)).symm
    (P.lam (C.castTm (U.el_sub (U.sub A Z.inner) C.fst)
      (C.tmSub (C.castTm (U.el_sub A Z.inner) (C.tmSub (Q.unlam f) Z.inner)) C.fst)))))

end SizeRules

namespace ExistentialSizeQuantifier

variable {U : Universe C} {I : IdentityTypes C} {Z : SizeRules C U I}
    (E : ExistentialSizeQuantifier C U I Z)

/-- The context map presenting the generic existential pair. -/
def pairSub {Γ : C.Ctx} (A : U.Code (C.ext Γ (Z.type Γ))) :
    C.Sub (C.ext (C.ext Γ (Z.type Γ)) (U.el A)) (C.ext Γ (U.el (E.code A))) :=
  C.pair (C.comp C.fst C.fst) (E.pair A)

/-- Nondependent elimination to a small code, derived from the source's
dependent elimination rule. The branch is still an internal contextual term. -/
def recursor (F : FunctionTypes C) {Γ : C.Ctx} (A : U.Code (C.ext Γ (Z.type Γ)))
    (B : U.Code Γ)
    (b : C.Tm (C.ext (C.ext Γ (Z.type Γ)) (U.el A))
      (C.tySub (U.el B) (C.comp C.fst C.fst))) :
    C.Tm Γ (F.arr (U.el (E.code A)) (U.el B)) := by
  have h : C.tySub (U.el (U.sub B C.fst)) (E.pairSub A) =
      C.tySub (U.el B) (C.comp C.fst C.fst) := by
    calc
      _ = C.tySub (C.tySub (U.el B) C.fst) (E.pairSub A) :=
        congrArg (fun X => C.tySub X (E.pairSub A)) (U.el_sub B C.fst).symm
      _ = _ := by rw [C.tySub_comp, pairSub, C.pair_fst]
  exact F.lam (C.castTm (U.el_sub B C.fst).symm
    (E.elim A (U.sub B C.fst) (C.castTm h.symm b)))

end ExistentialSizeQuantifier

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_TheoryEquivalenceV2 -/

/-!
# Internal paths and half-adjoint equivalences

These are contextual constructions in the theory of Section 2, not Lean equality
or metatheoretic equivalences. Function action on paths is derived from the source's
identity eliminator. No identity reflection or uniqueness of identity proofs is used.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

namespace FunctionTypes

variable {C : CwF.{u, v, w, t}} (F : FunctionTypes C)

/-- Function substitution represents ordinary term substitution with its type transported. -/
theorem sub_heq {Γ Δ : C.Ctx} {A B : C.Ty Γ}
    (f : C.Tm Γ (F.arr A B)) (σ : C.Sub Δ Γ) :
    HEq (F.sub f σ) (C.tmSub f σ) := C.castTm_heq _ _

/-- Function substitution composes, with the explicit type transports retained. -/
theorem sub_comp_heq {Γ Δ Θ : C.Ctx} {A B : C.Ty Γ}
    (f : C.Tm Γ (F.arr A B)) (σ : C.Sub Δ Γ) (τ : C.Sub Θ Δ) :
    HEq (F.sub (F.sub f σ) τ) (F.sub f (C.comp σ τ)) :=
  (F.sub_heq _ _).trans
    ((C.tmSub_heq (F.arr_sub A B σ).symm (F.sub_heq f σ) τ).trans
      ((C.tmSub_comp f σ τ).trans (F.sub_heq _ _).symm))

/-- Application respects external type transport. This says nothing about internal paths. -/
theorem app_congr {Γ : C.Ctx} {A A' B B' : C.Ty Γ}
    (hA : A = A') (hB : B = B')
    {f : C.Tm Γ (F.arr A B)} {f' : C.Tm Γ (F.arr A' B')}
    {a : C.Tm Γ A} {a' : C.Tm Γ A'} (hf : HEq f f') (ha : HEq a a') :
    HEq (F.app f a) (F.app f' a') := by
  cases hA
  cases hB
  cases hf
  cases ha
  rfl

end FunctionTypes

namespace IdentityTypes

variable {C : CwF.{u, v, w, t}} (I : IdentityTypes C)

/-- Forgetting a path argument recovers its endpoint substitution. -/
theorem pathSub_fst {Γ : C.Ctx} {A : C.Ty Γ} (a b : C.Tm Γ A)
    (p : C.Tm Γ (I.id A a b)) : C.comp C.fst (I.pathSub a b p) = C.termSub b :=
  C.pair_fst _ _

end IdentityTypes

namespace InternalPath

variable {C : CwF.{u, v, w, t}}
    (F : FunctionTypes C) (I : IdentityTypes C) (J : IdentityElimination C I)

/-- The endpoint-indexed family `f(a) = f(y)` before adjoining the source path. -/
def apEndpoint {Γ : C.Ctx} {A B : C.Ty Γ}
    (f : C.Tm Γ (F.arr A B)) (a : C.Tm Γ A) : C.Ty (C.ext Γ A) :=
  I.id (C.tySub B C.fst) (C.tmSub (F.app f a) C.fst)
    (F.app (F.sub f C.fst) C.snd)

theorem apEndpoint_sub {Γ : C.Ctx} {A B : C.Ty Γ}
    (f : C.Tm Γ (F.arr A B)) (a b : C.Tm Γ A) :
    C.tySub (apEndpoint F I f a) (C.termSub b) = I.id B (F.app f a) (F.app f b) := by
  rw [apEndpoint, I.id_sub]
  apply I.id_congr (C.tySub_fst_termSub B b) (C.tmSub_fst_termSub (F.app f a) b)
  rw [F.app_sub]
  apply F.app_congr (C.tySub_fst_termSub A b) (C.tySub_fst_termSub B b)
  · have h := F.sub_comp_heq f C.fst (C.termSub b)
    rw [C.termSub_fst] at h
    exact h.trans ((F.sub_heq f C.id).trans (C.tmSub_id f))
  · exact C.termSub_snd b

/-- The motive for identity elimination defining action on paths. -/
def apMotive {Γ : C.Ctx} {A B : C.Ty Γ}
    (f : C.Tm Γ (F.arr A B)) (a : C.Tm Γ A) : C.Ty (I.pathContext a) :=
  C.tySub (apEndpoint F I f a) C.fst

theorem apMotive_sub {Γ : C.Ctx} {A B : C.Ty Γ}
    (f : C.Tm Γ (F.arr A B)) (a b : C.Tm Γ A) (p : C.Tm Γ (I.id A a b)) :
    C.tySub (apMotive F I f a) (I.pathSub a b p) = I.id B (F.app f a) (F.app f b) := by
  calc
    _ = C.tySub (apEndpoint F I f a) (C.comp C.fst (I.pathSub a b p)) :=
      C.tySub_comp _ _ _
    _ = _ := by rw [I.pathSub_fst, apEndpoint_sub]

/-- Function action on identity terms, obtained by the actual `J` rule. -/
def ap {Γ : C.Ctx} {A B : C.Ty Γ} (f : C.Tm Γ (F.arr A B))
    {a b : C.Tm Γ A} (p : C.Tm Γ (I.id A a b)) :
    C.Tm Γ (I.id B (F.app f a) (F.app f b)) :=
  C.castTm (apMotive_sub F I f a b p)
    (J.elim a (apMotive F I f a)
      (C.castTm (apMotive_sub F I f a a (I.refl a)).symm (I.refl (F.app f a))) b p)

/-- The action of a function on reflexivity is reflexivity, by the beta rule for `J`. -/
theorem ap_refl {Γ : C.Ctx} {A B : C.Ty Γ}
    (f : C.Tm Γ (F.arr A B)) (a : C.Tm Γ A) :
    ap F I J f (I.refl a) = I.refl (F.app f a) := by
  unfold ap
  rw [J.beta]
  apply eq_of_heq
  exact (C.castTm_heq _ _).trans (C.castTm_heq _ _)

end InternalPath

namespace InternalEquivalence

variable {C : CwF.{u, v, w, t}}
    (F : FunctionTypes C) (P : DependentProducts C) (I : IdentityTypes C)

/-- The family `g (f x) = x` over the generic source element. -/
def homotopyBody {Γ : C.Ctx} {A B : C.Ty Γ}
    (f : C.Tm Γ (F.arr A B)) (g : C.Tm Γ (F.arr B A)) : C.Ty (C.ext Γ A) :=
  I.id (C.tySub A C.fst) (F.app (F.sub g C.fst) (F.app (F.sub f C.fst) C.snd)) C.snd

/-- A homotopy from `g ∘ f` to the identity, expressed as an internal dependent product. -/
def homotopyType {Γ : C.Ctx} {A B : C.Ty Γ}
    (f : C.Tm Γ (F.arr A B)) (g : C.Tm Γ (F.arr B A)) : C.Ty Γ :=
  P.pi A (homotopyBody F I f g)

theorem homotopyBody_sub {Γ Δ : C.Ctx} {A B : C.Ty Γ}
    (f : C.Tm Γ (F.arr A B)) (g : C.Tm Γ (F.arr B A))
    (σ : C.Sub Δ Γ) (a : C.Tm Δ (C.tySub A σ)) :
    C.tySub (homotopyBody F I f g) (C.pair σ a) =
      I.id (C.tySub A σ) (F.app (F.sub g σ) (F.app (F.sub f σ) a)) a := by
  have hTy (T : C.Ty Γ) : C.tySub (C.tySub T C.fst) (C.pair σ a) = C.tySub T σ := by
    rw [C.tySub_comp, C.pair_fst]
  have hf : HEq (F.sub (F.sub f C.fst) (C.pair σ a)) (F.sub f σ) := by
    have h := F.sub_comp_heq f C.fst (C.pair σ a)
    rwa [C.pair_fst] at h
  have hg : HEq (F.sub (F.sub g C.fst) (C.pair σ a)) (F.sub g σ) := by
    have h := F.sub_comp_heq g C.fst (C.pair σ a)
    rwa [C.pair_fst] at h
  rw [homotopyBody, I.id_sub]
  apply I.id_congr (hTy A) ?_ (C.pair_snd σ a)
  rw [F.app_sub, F.app_sub]
  exact F.app_congr (hTy B) (hTy A) hg
    (F.app_congr (hTy A) (hTy B) hf (C.pair_snd σ a))

/-- Evaluate an internal homotopy after any substitution and at any source term. -/
def homotopyAt {Γ Δ : C.Ctx} {A B : C.Ty Γ}
    (f : C.Tm Γ (F.arr A B)) (g : C.Tm Γ (F.arr B A))
    (η : C.Tm Γ (homotopyType F P I f g))
    (σ : C.Sub Δ Γ) (a : C.Tm Δ (C.tySub A σ)) :
    C.Tm Δ (I.id (C.tySub A σ) (F.app (F.sub g σ) (F.app (F.sub f σ) a)) a) :=
  C.castTm (homotopyBody_sub F I f g σ a) (C.tmSub (P.unlam η) (C.pair σ a))

/-- Homotopy formation is stable under contextual substitution. -/
theorem homotopyType_sub {Γ Δ : C.Ctx} {A B : C.Ty Γ}
    (f : C.Tm Γ (F.arr A B)) (g : C.Tm Γ (F.arr B A)) (σ : C.Sub Δ Γ) :
    C.tySub (homotopyType F P I f g) σ =
      homotopyType F P I (F.sub f σ) (F.sub g σ) := by
  rw [homotopyType, P.pi_sub]
  congr 1
  change C.tySub (homotopyBody F I f g)
    (C.pair (C.comp σ C.fst) (C.castTm (C.tySub_comp A σ C.fst) C.snd)) = _
  rw [homotopyBody_sub]
  apply I.id_congr (C.tySub_comp A σ C.fst).symm ?_ (C.castTm_heq _ _)
  exact F.app_congr (C.tySub_comp B σ C.fst).symm (C.tySub_comp A σ C.fst).symm
    (F.sub_comp_heq g σ C.fst).symm
    (F.app_congr (C.tySub_comp A σ C.fst).symm (C.tySub_comp B σ C.fst).symm
      (F.sub_comp_heq f σ C.fst).symm (C.castTm_heq _ _))

/-- Substitute a homotopy, transporting its explicitly formed dependent product. -/
def homotopySub {Γ Δ : C.Ctx} {A B : C.Ty Γ}
    {f : C.Tm Γ (F.arr A B)} {g : C.Tm Γ (F.arr B A)}
    (η : C.Tm Γ (homotopyType F P I f g)) (σ : C.Sub Δ Γ) :
    C.Tm Δ (homotopyType F P I (F.sub f σ) (F.sub g σ)) :=
  C.castTm (homotopyType_sub F P I f g σ) (C.tmSub η σ)

/-- Half-adjoint coherence: `ap f (η x) = ε (f x)` for each source element. -/
def coherenceType (J : IdentityElimination C I) {Γ : C.Ctx} {A B : C.Ty Γ}
    (f : C.Tm Γ (F.arr A B)) (g : C.Tm Γ (F.arr B A))
    (η : C.Tm Γ (homotopyType F P I f g))
    (ε : C.Tm Γ (homotopyType F P I g f)) : C.Ty Γ :=
  P.pi A (I.id
    (I.id (C.tySub B C.fst)
      (F.app (F.sub f C.fst) (F.app (F.sub g C.fst) (F.app (F.sub f C.fst) C.snd)))
      (F.app (F.sub f C.fst) C.snd))
    (InternalPath.ap F I J (F.sub f C.fst) (P.unlam η))
    (homotopyAt F P I g f ε C.fst (F.app (F.sub f C.fst) C.snd)))

/-- The source's `isEquiv f`, literally a dependent sum of an inverse, the two
homotopies, and the half-adjoint coherence, with `ap` derived from identity elimination. -/
def isEquiv (S : DependentSums C) (J : IdentityElimination C I)
    {Γ : C.Ctx} {A B : C.Ty Γ} (f : C.Tm Γ (F.arr A B)) : C.Ty Γ :=
  let G := F.arr B A
  let f₁ := F.sub f C.fst (A := A) (B := B)
  let g₁ : C.Tm (C.ext Γ G) (F.arr (C.tySub B C.fst) (C.tySub A C.fst)) :=
    C.castTm (F.arr_sub B A C.fst) C.snd
  let H := homotopyType F P I f₁ g₁
  let f₂ := F.sub f₁ (C.fst (A := H))
  let g₂ := F.sub g₁ (C.fst (A := H))
  let η₂ := C.castTm (homotopyType_sub F P I f₁ g₁ C.fst) C.snd
  let E := homotopyType F P I g₂ f₂
  let f₃ := F.sub f₂ (C.fst (A := E))
  let g₃ := F.sub g₂ (C.fst (A := E))
  let η₃ := homotopySub F P I η₂ (C.fst (A := E))
  let ε₃ := C.castTm (homotopyType_sub F P I g₂ f₂ C.fst) C.snd
  S.sigma G (S.sigma H (S.sigma E (coherenceType F P I J f₃ g₃ η₃ ε₃)))

/-- The internal type of half-adjoint equivalences, including the forward function. -/
def equivalence (S : DependentSums C) (J : IdentityElimination C I)
    {Γ : C.Ctx} (A B : C.Ty Γ) : C.Ty Γ :=
  S.sigma (F.arr A B)
    (isEquiv F P I S J (C.castTm (F.arr_sub A B C.fst) C.snd))

end InternalEquivalence

namespace CwF

variable (C : CwF.{u, v, w, t})

theorem tySub_fst_pair {Γ Δ : C.Ctx} (A B : C.Ty Γ)
    (σ : C.Sub Δ Γ) (a : C.Tm Δ (C.tySub A σ)) :
    C.tySub (C.tySub B C.fst) (C.pair σ a) = C.tySub B σ := by
  rw [C.tySub_comp, C.pair_fst]

theorem pair_fst_snd {Γ : C.Ctx} (A : C.Ty Γ) :
    C.pair (C.fst (A := A)) C.snd = C.id :=
  (C.pair_unique _ _ _ (C.comp_id _) (C.tmSub_id _)).symm

theorem pair_comp {Γ Δ Θ : C.Ctx} {A : C.Ty Γ}
    (σ : C.Sub Δ Γ) (a : C.Tm Δ (C.tySub A σ)) (τ : C.Sub Θ Δ) :
    C.comp (C.pair σ a) τ =
      C.pair (C.comp σ τ) (C.castTm (C.tySub_comp A σ τ) (C.tmSub a τ)) := by
  apply C.pair_unique
  · rw [← C.assoc, C.pair_fst]
  · exact (C.tmSub_comp C.snd (C.pair σ a) τ).symm.trans
      ((C.tmSub_heq (C.tySub_fst_pair A A σ a) (C.pair_snd σ a) τ).trans
        (C.castTm_heq _ _).symm)

theorem lift_fst {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : C.Ty Γ) :
    C.comp C.fst (C.lift σ A) = C.comp σ C.fst := C.pair_fst _ _

theorem lift_snd {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : C.Ty Γ) :
    HEq (C.tmSub C.snd (C.lift σ A)) (C.snd (A := C.tySub A σ)) :=
  (C.pair_snd _ _).trans (C.castTm_heq _ _)

/-- Context transport along an external equality of types. -/
def castExt {Γ : C.Ctx} {A B : C.Ty Γ} (h : A = B) : C.Sub (C.ext Γ A) (C.ext Γ B) :=
  h ▸ C.id

theorem castExt_fst {Γ : C.Ctx} {A B : C.Ty Γ} (h : A = B) :
    C.comp C.fst (C.castExt h) = C.fst := by
  cases h
  exact C.comp_id _

theorem castExt_snd {Γ : C.Ctx} {A B : C.Ty Γ} (h : A = B) :
    HEq (C.tmSub C.snd (C.castExt h)) (C.snd (A := A)) := by
  cases h
  exact C.tmSub_id _

/-- A lift composed with a section is the corresponding extended substitution. -/
theorem lift_termSub {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : C.Ty Γ)
    (a : C.Tm Δ (C.tySub A σ)) :
    C.comp (C.lift σ A) (C.termSub a) = C.pair σ a := by
  apply C.pair_unique
  · rw [← C.assoc, C.lift_fst, C.assoc, C.termSub_fst, C.comp_id]
  · have hTy : C.tySub (C.tySub A C.fst) (C.lift σ A) =
        C.tySub (C.tySub A σ) C.fst := by
      rw [C.tySub_comp, C.lift_fst, C.tySub_comp]
    exact (C.tmSub_comp C.snd (C.lift σ A) (C.termSub a)).symm.trans
      ((C.tmSub_heq hTy (C.lift_snd σ A) (C.termSub a)).trans (C.termSub_snd a))

end CwF

namespace DependentProducts

variable {C : CwF.{u, v, w, t}} (P : DependentProducts C)

def sub {Γ Δ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (f : C.Tm Γ (P.pi A B)) (σ : C.Sub Δ Γ) :
    C.Tm Δ (P.pi (C.tySub A σ) (C.tySub B (C.lift σ A))) :=
  C.castTm (P.pi_sub A B σ) (C.tmSub f σ)

theorem sub_heq {Γ Δ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (f : C.Tm Γ (P.pi A B)) (σ : C.Sub Δ Γ) :
    HEq (P.sub f σ) (C.tmSub f σ) := C.castTm_heq _ _

theorem unlam_sub {Γ Δ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (f : C.Tm Γ (P.pi A B)) (σ : C.Sub Δ Γ) :
    P.unlam (P.sub f σ) = C.tmSub (P.unlam f) (C.lift σ A) := by
  have h := congrArg P.unlam (P.lam_sub (P.unlam f) σ)
  rw [P.eta, P.beta] at h
  exact h

end DependentProducts

namespace CwF

variable (C : CwF.{u, v, w, t})

theorem tySub_lift {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : C.Ty Γ) :
    C.tySub (C.tySub A C.fst) (C.lift σ A) = C.tySub (C.tySub A σ) C.fst := by
  rw [C.tySub_comp, C.lift_fst, C.tySub_comp]

/-- Lifting a retraction of contexts and transporting its domain yields the identity. -/
theorem lift_section {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (τ : C.Sub Γ Δ)
    (hστ : C.comp σ τ = C.id) (A : C.Ty Γ)
    (hA : C.tySub (C.tySub A σ) τ = A) :
    C.comp (C.comp (C.lift σ A) (C.lift τ (C.tySub A σ))) (C.castExt hA.symm) = C.id := by
  apply Eq.trans (C.pair_unique C.fst C.snd _ ?_ ?_) (C.pair_fst_snd A)
  · calc
      _ = C.comp (C.comp (C.comp C.fst (C.lift σ A)) (C.lift τ (C.tySub A σ)))
          (C.castExt hA.symm) := by simp only [C.assoc]
      _ = C.comp (C.comp (C.comp σ C.fst) (C.lift τ (C.tySub A σ)))
          (C.castExt hA.symm) := by rw [C.lift_fst]
      _ = C.comp (C.comp σ (C.comp τ C.fst)) (C.castExt hA.symm) := by
        rw [C.assoc σ C.fst, C.lift_fst]
      _ = C.comp (C.comp (C.comp σ τ) C.fst) (C.castExt hA.symm) := by
        rw [C.assoc σ τ]
      _ = C.fst := by rw [hστ, C.id_comp, C.castExt_fst]
  · have hTy : C.tySub (C.tySub A C.fst)
          (C.comp (C.lift σ A) (C.lift τ (C.tySub A σ))) =
        C.tySub (C.tySub (C.tySub A σ) τ) C.fst := by
      rw [← C.tySub_comp, C.tySub_lift, C.tySub_lift]
    have hs : HEq (C.tmSub C.snd (C.comp (C.lift σ A) (C.lift τ (C.tySub A σ))))
        (C.snd (A := C.tySub (C.tySub A σ) τ)) :=
      (C.tmSub_comp C.snd (C.lift σ A) (C.lift τ (C.tySub A σ))).symm.trans
        ((C.tmSub_heq (C.tySub_lift σ A) (C.lift_snd σ A)
          (C.lift τ (C.tySub A σ))).trans (C.lift_snd τ (C.tySub A σ)))
    exact (C.tmSub_comp C.snd
      (C.comp (C.lift σ A) (C.lift τ (C.tySub A σ))) (C.castExt hA.symm)).symm.trans
      ((C.tmSub_heq hTy hs (C.castExt hA.symm)).trans (C.castExt_snd hA.symm))

end CwF

namespace DependentProducts

variable {C : CwF.{u, v, w, t}} (P : DependentProducts C) (I : IdentityTypes C)

/-- Pointwise paths between dependent functions, as an internal dependent product. -/
def homotopyType {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (f g : C.Tm Γ (P.pi A B)) : C.Ty Γ :=
  P.pi A (I.id B (P.unlam f) (P.unlam g))

theorem homotopyType_sub {Γ Δ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (f g : C.Tm Γ (P.pi A B)) (σ : C.Sub Δ Γ) :
    C.tySub (P.homotopyType I f g) σ = P.homotopyType I (P.sub f σ) (P.sub g σ) := by
  simp only [homotopyType, P.pi_sub, I.id_sub, P.unlam_sub]

/-- Pointwise-path formation respects transport of a dependent function's domain and family. -/
theorem homotopyType_congr {Γ : C.Ctx} {A A' : C.Ty Γ}
    {B : C.Ty (C.ext Γ A)} {B' : C.Ty (C.ext Γ A')}
    (hA : A = A') (hB : C.tySub B (C.castExt hA.symm) = B')
    {f g : C.Tm Γ (P.pi A B)} {f' g' : C.Tm Γ (P.pi A' B')}
    (hf : HEq f f') (hg : HEq g g') : P.homotopyType I f g = P.homotopyType I f' g' := by
  cases hA
  simp only [CwF.castExt, C.tySub_id] at hB
  cases hB
  cases hf
  cases hg
  rfl

end DependentProducts

namespace InternalPath

variable {C : CwF.{u, v, w, t}}
    (P : DependentProducts C) (I : IdentityTypes C) (J : IdentityElimination C I)

/-- The pointwise-path motive over a variable function endpoint. -/
def happlyEndpoint {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (f : C.Tm Γ (P.pi A B)) : C.Ty (C.ext Γ (P.pi A B)) :=
  P.homotopyType I (P.sub f C.fst) (C.castTm (P.pi_sub A B C.fst) C.snd)

theorem happlyEndpoint_sub {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (f g : C.Tm Γ (P.pi A B)) :
    C.tySub (happlyEndpoint P I f) (C.termSub g) = P.homotopyType I f g := by
  rw [happlyEndpoint, P.homotopyType_sub]
  apply P.homotopyType_congr I (C.tySub_fst_termSub A g)
  · rw [C.tySub_comp, C.tySub_comp, ← C.assoc,
      C.lift_section C.fst (C.termSub g) (C.termSub_fst g) A
        (C.tySub_fst_termSub A g), C.tySub_id]
  · exact (P.sub_heq _ _).trans
      ((C.tmSub_heq (P.pi_sub A B C.fst).symm (P.sub_heq f C.fst) (C.termSub g)).trans
        (C.tmSub_fst_termSub f g))
  · exact (P.sub_heq _ _).trans
      ((C.tmSub_heq (P.pi_sub A B C.fst).symm (C.castTm_heq _ _) (C.termSub g)).trans
        (C.termSub_snd g))

/-- The based identity-elimination motive defining canonical dependent happly. -/
def happlyMotive {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (f : C.Tm Γ (P.pi A B)) : C.Ty (I.pathContext f) :=
  C.tySub (happlyEndpoint P I f) C.fst

theorem happlyMotive_sub {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (f g : C.Tm Γ (P.pi A B)) (p : C.Tm Γ (I.id (P.pi A B) f g)) :
    C.tySub (happlyMotive P I f) (I.pathSub f g p) = P.homotopyType I f g := by
  calc
    _ = C.tySub (happlyEndpoint P I f) (C.comp C.fst (I.pathSub f g p)) :=
      C.tySub_comp _ _ _
    _ = _ := by rw [I.pathSub_fst, happlyEndpoint_sub]

/-- Canonical dependent happly, derived by path induction into pointwise identity types. -/
def happlyTerm {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    {f g : C.Tm Γ (P.pi A B)} (p : C.Tm Γ (I.id (P.pi A B) f g)) :
    C.Tm Γ (P.homotopyType I f g) :=
  C.castTm (happlyMotive_sub P I f g p)
    (J.elim f (happlyMotive P I f)
      (C.castTm (happlyMotive_sub P I f f (I.refl f)).symm
        (P.lam (I.refl (P.unlam f)))) g p)

theorem happlyTerm_refl {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (f : C.Tm Γ (P.pi A B)) :
    happlyTerm P I J (I.refl f) = P.lam (I.refl (P.unlam f)) := by
  unfold happlyTerm
  rw [J.beta]
  apply eq_of_heq
  exact (C.castTm_heq _ _).trans (C.castTm_heq _ _)

/-- The canonical happly as an internal function, obtained by contextual abstraction. -/
def happly (F : FunctionTypes C) {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (f g : C.Tm Γ (P.pi A B)) :
    C.Tm Γ (F.arr (I.id (P.pi A B) f g) (P.homotopyType I f g)) :=
  let pathSub : C.tySub (I.id (P.pi A B) f g) C.fst =
      I.id (P.pi (C.tySub A C.fst) (C.tySub B (C.lift C.fst A)))
        (P.sub f C.fst) (P.sub g C.fst) :=
    (I.id_sub f g C.fst).trans
      (I.id_congr (P.pi_sub A B C.fst) (P.sub_heq f C.fst).symm
        (P.sub_heq g C.fst).symm)
  F.lam (C.castTm (P.homotopyType_sub I f g C.fst).symm
    (happlyTerm P I J (C.castTm pathSub C.snd)))

end InternalPath

/-- Function extensionality as stated in Section 2: the J-defined canonical
happly map is internally a half-adjoint equivalence. -/
structure FunctionExtensionality (C : CwF.{u, v, w, t}) (F : FunctionTypes C)
    (P : DependentProducts C) (S : DependentSums C) (I : IdentityTypes C)
    (J : IdentityElimination C I) where
  isEquiv_happly : ∀ {Γ} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (f g : C.Tm Γ (P.pi A B)),
    C.Tm Γ (InternalEquivalence.isEquiv F P I S J (InternalPath.happly P I J F f g))

namespace FunctionExtensionality

variable {C : CwF.{u, v, w, t}} {F : FunctionTypes C} {P : DependentProducts C}
    {S : DependentSums C} {I : IdentityTypes C} {J : IdentityElimination C I}
    (E : FunctionExtensionality C F P S I J)

/-- The inverse to canonical happly selected by the internal equivalence witness. -/
def funext {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (f g : C.Tm Γ (P.pi A B)) :
    C.Tm Γ (F.arr (P.homotopyType I f g) (I.id (P.pi A B) f g)) :=
  S.fst (E.isEquiv_happly f g)

/-- Function extensionality applied to an internal pointwise homotopy. -/
def funextApply {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    {f g : C.Tm Γ (P.pi A B)} (h : C.Tm Γ (P.homotopyType I f g)) :
    C.Tm Γ (I.id (P.pi A B) f g) := F.app (E.funext f g) h

end FunctionExtensionality

namespace IdentityTypes

variable {C : CwF.{u, v, w, t}} (I : IdentityTypes C)

/-- Based path families are stable under the lift of a context substitution. -/
theorem basedPath_lift {Γ Δ : C.Ctx} {A : C.Ty Γ}
    (a : C.Tm Γ A) (σ : C.Sub Δ Γ) :
    C.tySub (I.basedPath a) (C.lift σ A) = I.basedPath (C.tmSub a σ) := by
  rw [basedPath, I.id_sub]
  apply I.id_congr (C.tySub_lift σ A) ?_ (C.lift_snd σ A)
  have h := C.tmSub_comp a C.fst (C.lift σ A)
  rw [C.lift_fst] at h
  exact h.trans (C.tmSub_comp a σ C.fst).symm

/-- Lift a context substitution through both an endpoint and its based path. -/
def pathLift {Γ Δ : C.Ctx} {A : C.Ty Γ} (a : C.Tm Γ A) (σ : C.Sub Δ Γ) :
    C.Sub (I.pathContext (C.tmSub a σ)) (I.pathContext a) :=
  C.pair (C.comp (C.lift σ A) C.fst)
    (C.castTm ((congrArg (fun T ↦ C.tySub T C.fst) (I.basedPath_lift a σ)).symm.trans
      (C.tySub_comp (I.basedPath a) (C.lift σ A) C.fst)) C.snd)

theorem pathLift_fst {Γ Δ : C.Ctx} {A : C.Ty Γ} (a : C.Tm Γ A) (σ : C.Sub Δ Γ) :
    C.comp C.fst (I.pathLift a σ) = C.comp (C.lift σ A) C.fst := C.pair_fst _ _

end IdentityTypes

namespace InternalPath

variable {C : CwF.{u, v, w, t}} (I : IdentityTypes C) (J : IdentityElimination C I)

/-- The transport motive pulls a contextual family back along the endpoint projection. -/
def transportMotive {Γ : C.Ctx} {A : C.Ty Γ} (B : C.Ty (C.ext Γ A))
    (a : C.Tm Γ A) : C.Ty (I.pathContext a) := C.tySub B C.fst

theorem transportMotive_sub {Γ : C.Ctx} {A : C.Ty Γ} (B : C.Ty (C.ext Γ A))
    (a b : C.Tm Γ A) (p : C.Tm Γ (I.id A a b)) :
    C.tySub (transportMotive I B a) (I.pathSub a b p) = C.tySub B (C.termSub b) := by
  calc
    _ = C.tySub B (C.comp C.fst (I.pathSub a b p)) := C.tySub_comp _ _ _
    _ = _ := by rw [I.pathSub_fst]

/-- Internal dependent transport, constructed by the based identity eliminator. -/
def transport {Γ : C.Ctx} {A : C.Ty Γ} (B : C.Ty (C.ext Γ A))
    {a b : C.Tm Γ A} (p : C.Tm Γ (I.id A a b))
    (x : C.Tm Γ (C.tySub B (C.termSub a))) : C.Tm Γ (C.tySub B (C.termSub b)) :=
  C.castTm (transportMotive_sub I B a b p)
    (J.elim a (transportMotive I B a)
      (C.castTm (transportMotive_sub I B a a (I.refl a)).symm x) b p)

theorem transport_refl {Γ : C.Ctx} {A : C.Ty Γ} (B : C.Ty (C.ext Γ A))
    (a : C.Tm Γ A) (x : C.Tm Γ (C.tySub B (C.termSub a))) :
    transport I J B (I.refl a) x = x := by
  unfold transport
  rw [J.beta]
  apply eq_of_heq
  exact (C.castTm_heq _ _).trans (C.castTm_heq _ _)

end InternalPath

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_ParametricityV2 -/

/-!
# The source type expressions for the four parametricity axioms

All domains and codomains are literal contextual translations of Section 2.2.
The small family `B` is a term in `Γ, x : A, i : Size`; the interchange map below
puts it in `Γ, i : Size, x : A`. No arbitrary Lean family over decoded sizes or
elements is introduced.

This module forms the exact type expressions. The canonical arrows are defined
in the `Canonical*V2` modules and their half-adjoint equivalence axioms in
`ParametricityAxiomsV2`.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

variable {C : CwF.{u, v, w, t}} {U : Universe C} {I : IdentityTypes C}
    (Z : SizeRules C U I)

namespace Parametricity

variable {P : DependentProducts C} {S : DependentSums C}
    (K : SmallTypeConstructors C U P S I)
    (Q : UniversalSizeQuantifier C U I Z) (E : ExistentialSizeQuantifier C U I Z)

/-- Interchange an independent small variable and a size variable. -/
def interchange {Γ : C.Ctx} (A : U.Code Γ) :
    C.Sub (C.ext (C.ext Γ (Z.type Γ)) (U.el (U.sub A C.fst)))
      (C.ext (C.ext Γ (U.el A)) (Z.type (C.ext Γ (U.el A)))) :=
  Z.extend (U.liftEl C.fst A) (Z.sub (Z.generic Γ) C.fst)

/-- Existential quantification bounded by an arbitrary contextual size term. -/
def boundedExAt {Γ : C.Ctx} (i : C.Tm Γ (Z.type Γ))
    (B : U.Code (C.ext Γ (Z.type Γ))) : U.Code Γ :=
  E.code (K.sigma (Z.le (Z.succ (Z.generic Γ)) (Z.sub i C.fst)) (U.sub B C.fst))

/-- Left-hand side of `∃` parametric over `Π`. -/
def existsPiSource {Γ : C.Ctx} (A : U.Code Γ)
    (B : U.Code (C.ext (C.ext Γ (U.el A)) (Z.type (C.ext Γ (U.el A))))) : U.Code Γ :=
  K.pi A (E.code B)

/-- Right-hand side of `∃` parametric over `Π`, with the source's essential
inner bounded existential. No monotonicity hypothesis is added. -/
def existsPiTarget {Γ : C.Ctx} (A : U.Code Γ)
    (B : U.Code (C.ext (C.ext Γ (U.el A)) (Z.type (C.ext Γ (U.el A))))) : U.Code Γ :=
  E.code (K.pi (U.sub A C.fst)
    (boundedExAt Z K E (Z.sub (Z.generic Γ) C.fst) (U.sub B (Z.lift (U.liftEl C.fst A)))))

/-- Left-hand side of `∀` parametric over `Σ`. -/
def allSigmaSource {Γ : C.Ctx} (A : U.Code Γ)
    (B : U.Code (C.ext (C.ext Γ (U.el A)) (Z.type (C.ext Γ (U.el A))))) : U.Code Γ :=
  K.sigma A (Q.code B)

/-- Right-hand side of `∀` parametric over `Σ`. -/
def allSigmaTarget {Γ : C.Ctx} (A : U.Code Γ)
    (B : U.Code (C.ext (C.ext Γ (U.el A)) (Z.type (C.ext Γ (U.el A))))) : U.Code Γ :=
  Q.code (K.sigma (U.sub A C.fst) (U.sub B (interchange Z A)))

/-- Domain of the right-to-left canonical map for `∃` parametric over `<`. -/
def existsLtSource {Γ : C.Ctx} (A : U.Code (C.ext Γ (Z.type Γ))) : U.Code Γ :=
  E.code (Z.diamond K E A)

/-- Codomain of that canonical map. -/
def existsLtTarget {Γ : C.Ctx} (A : U.Code (C.ext Γ (Z.type Γ))) : U.Code Γ :=
  E.code A

/-- Domain of the left-to-right canonical map for `∀` parametric over `<`. -/
def allLtSource {Γ : C.Ctx} (A : U.Code (C.ext Γ (Z.type Γ))) : U.Code Γ :=
  Q.code A

/-- Codomain of that canonical map. -/
def allLtTarget {Γ : C.Ctx} (A : U.Code (C.ext Γ (Z.type Γ))) : U.Code Γ :=
  Q.code (Z.box K Q A)

end Parametricity

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_QuantifierNaturalityV2 -/

/-!
# Substitution of bounded size quantifiers

The source abbreviations `∀ j < i, A(j)` and `∃ j < i, A(j)` are stable under
substitution. Their stability is derived from the primitive constructor rules;
it is not an additional field imposed on the interpretation.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

namespace SizeRules

variable {C : CwF.{u, v, w, t}} {U : Universe C} {I : IdentityTypes C}
    (Z : SizeRules C U I)

theorem sub_comp {Γ Δ Θ : C.Ctx} (i : C.Tm Γ (Z.type Γ))
    (σ : C.Sub Δ Γ) (τ : C.Sub Θ Δ) :
    Z.sub (Z.sub i σ) τ = Z.sub i (C.comp σ τ) := by
  apply eq_of_heq
  exact (C.castTm_heq _ _).trans
    ((C.tmSub_heq (Z.type_sub σ).symm (C.castTm_heq _ _) τ).trans
      ((C.tmSub_comp i σ τ).trans (C.castTm_heq _ _).symm))

theorem generic_sub_extend {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (i : C.Tm Δ (Z.type Δ)) : Z.sub (Z.generic Γ) (Z.extend σ i) = i := by
  apply eq_of_heq
  exact (C.castTm_heq _ _).trans
    ((C.tmSub_heq (Z.type_sub C.fst).symm (C.castTm_heq _ _) (Z.extend σ i)).trans
      ((C.pair_snd _ _).trans (C.castTm_heq _ _)))

theorem extend_fst {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (i : C.Tm Δ (Z.type Δ)) :
    C.comp C.fst (Z.extend σ i) = σ := C.pair_fst _ _

theorem sub_generic_heq {Γ Δ : C.Ctx} (σ : C.Sub Δ (C.ext Γ (Z.type Γ))) :
    HEq (Z.sub (Z.generic Γ) σ) (C.tmSub C.snd σ) :=
  (C.castTm_heq _ _).trans
    (C.tmSub_heq (Z.type_sub C.fst).symm (C.castTm_heq _ _) σ)

/-- A substitution into a size extension is determined by its base and size component. -/
theorem hom_ext {Γ Δ : C.Ctx} {f g : C.Sub Δ (C.ext Γ (Z.type Γ))}
    (hfst : C.comp C.fst f = C.comp C.fst g)
    (hsnd : Z.sub (Z.generic Γ) f = Z.sub (Z.generic Γ) g) : f = g := by
  let a := C.castTm (C.tySub_comp (Z.type Γ) C.fst g) (C.tmSub C.snd g)
  have hf : f = C.pair (C.comp C.fst g) a :=
    C.pair_unique _ _ _ hfst
      ((Z.sub_generic_heq f).symm.trans ((heq_of_eq hsnd).trans
        ((Z.sub_generic_heq g).trans (C.castTm_heq _ _).symm)))
  have hg : g = C.pair (C.comp C.fst g) a :=
    C.pair_unique _ _ _ rfl (C.castTm_heq _ _).symm
  exact hf.trans hg.symm

theorem lift_fst {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) :
    C.comp C.fst (Z.lift σ) = C.comp σ C.fst := C.pair_fst _ _

theorem generic_sub_lift {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) :
    Z.sub (Z.generic Γ) (Z.lift σ) = Z.generic Δ := Z.generic_sub_extend _ _

theorem inner_fst {Γ : C.Ctx} : C.comp C.fst (Z.inner (Γ := Γ)) = C.comp C.fst C.fst :=
  C.pair_fst _ _

theorem generic_sub_inner {Γ : C.Ctx} :
    Z.sub (Z.generic Γ) Z.inner = Z.generic (C.ext Γ (Z.type Γ)) :=
  Z.generic_sub_extend _ _

/-- Selecting the inner size commutes with lifting a substitution through both size binders. -/
theorem inner_lift {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) :
    C.comp (Z.inner (Γ := Γ)) (Z.lift (Z.lift σ)) =
      C.comp (Z.lift σ) (Z.inner (Γ := Δ)) := by
  apply Z.hom_ext
  · calc
      C.comp C.fst (C.comp Z.inner (Z.lift (Z.lift σ))) =
          C.comp (C.comp C.fst C.fst) (Z.lift (Z.lift σ)) := by
        rw [← C.assoc, Z.inner_fst]
      _ = C.comp C.fst (C.comp (Z.lift σ) C.fst) := by
        rw [C.assoc, Z.lift_fst]
      _ = C.comp (C.comp σ C.fst) C.fst := by rw [← C.assoc, Z.lift_fst]
      _ = C.comp (C.comp C.fst (Z.lift σ)) Z.inner := by
        simp only [Z.lift_fst, C.assoc, Z.inner_fst]
      _ = C.comp C.fst (C.comp (Z.lift σ) Z.inner) := C.assoc _ _ _
  · rw [← Z.sub_comp, Z.generic_sub_inner, Z.generic_sub_lift,
      ← Z.sub_comp, Z.generic_sub_lift, Z.generic_sub_inner]

theorem outer_sub_lift {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) :
    Z.sub (Z.sub (Z.generic Γ) C.fst) (Z.lift (Z.lift σ)) =
      Z.sub (Z.generic Δ) C.fst := by
  rw [Z.sub_comp, Z.lift_fst, ← Z.sub_comp, Z.generic_sub_lift]

/-- The source predicate `j < i` commutes with substitution under both size binders. -/
theorem boundCode_sub (ZS : SizeSubstitution U I Z) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) :
    U.sub (Z.boundCode (Γ := Γ)) (Z.lift (Z.lift σ)) = Z.boundCode (Γ := Δ) := by
  simp only [boundCode, ZS.le_sub, ZS.succ_sub, Z.generic_sub_lift, Z.outer_sub_lift]

end SizeRules

namespace Universe

variable {C : CwF.{u, v, w, t}} (U : Universe C)

theorem liftElAs_fst {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : U.Code Γ) (B : U.Code Δ)
    (h : U.sub A σ = B) :
    C.comp C.fst (U.liftElAs σ A B h) = C.comp σ C.fst := by
  subst B
  exact C.pair_fst _ _

end Universe

namespace SmallTypeConstructors

variable {C : CwF.{u, v, w, t}} {U : Universe C} {P : DependentProducts C}
    {S : DependentSums C} {I : IdentityTypes C} (K : SmallTypeConstructors C U P S I)

theorem pi_sub_as (KS : SmallTypeSubstitution U P S I K) {Γ Δ : C.Ctx}
    (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A))) (σ : C.Sub Δ Γ)
    (A' : U.Code Δ) (h : U.sub A σ = A') :
    U.sub (K.pi A B) σ = K.pi A' (U.sub B (U.liftElAs σ A A' h)) := by
  subst A'
  exact KS.pi_sub A B σ

theorem sigma_sub_as (KS : SmallTypeSubstitution U P S I K) {Γ Δ : C.Ctx}
    (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A))) (σ : C.Sub Δ Γ)
    (A' : U.Code Δ) (h : U.sub A σ = A') :
    U.sub (K.sigma A B) σ = K.sigma A' (U.sub B (U.liftElAs σ A A' h)) := by
  subst A'
  exact KS.sigma_sub A B σ

end SmallTypeConstructors

namespace SizeRules

variable {C : CwF.{u, v, w, t}} {U : Universe C} {I : IdentityTypes C}
    (Z : SizeRules C U I)

/-- The family under the bound-proof binder has the expected substitution. -/
theorem boundedFamily_sub (ZS : SizeSubstitution U I Z) {Γ Δ : C.Ctx}
    (A : U.Code (C.ext Γ (Z.type Γ))) (σ : C.Sub Δ Γ) :
    U.sub (U.sub (U.sub A Z.inner) C.fst)
      (U.liftElAs (Z.lift (Z.lift σ)) Z.boundCode Z.boundCode (Z.boundCode_sub ZS σ)) =
      U.sub (U.sub (U.sub A (Z.lift σ)) Z.inner) C.fst := by
  rw [U.sub_comp, U.liftElAs_fst]
  rw [← U.sub_comp]
  rw [U.sub_comp A, Z.inner_lift, ← U.sub_comp]

/-- Bounded universal quantification commutes with substitution of its free context. -/
theorem box_sub {P : DependentProducts C} {S : DependentSums C}
    (K : SmallTypeConstructors C U P S I) (Q : UniversalSizeQuantifier C U I Z)
    (ZS : SizeSubstitution U I Z) (KS : SmallTypeSubstitution U P S I K)
    (QS : UniversalSizeSubstitution U I Z Q) {Γ Δ : C.Ctx}
    (A : U.Code (C.ext Γ (Z.type Γ))) (σ : C.Sub Δ Γ) :
    U.sub (Z.box K Q A) (Z.lift σ) = Z.box K Q (U.sub A (Z.lift σ)) := by
  unfold box
  rw [QS.code_sub]
  rw [K.pi_sub_as KS _ _ _ _ (Z.boundCode_sub ZS σ), Z.boundedFamily_sub ZS]

/-- Bounded existential quantification commutes with substitution of its free context. -/
theorem diamond_sub {P : DependentProducts C} {S : DependentSums C}
    (K : SmallTypeConstructors C U P S I) (E : ExistentialSizeQuantifier C U I Z)
    (ZS : SizeSubstitution U I Z) (KS : SmallTypeSubstitution U P S I K)
    (ES : ExistentialSizeSubstitution U I Z E) {Γ Δ : C.Ctx}
    (A : U.Code (C.ext Γ (Z.type Γ))) (σ : C.Sub Δ Γ) :
    U.sub (Z.diamond K E A) (Z.lift σ) = Z.diamond K E (U.sub A (Z.lift σ)) := by
  unfold diamond
  rw [ES.code_sub]
  rw [K.sigma_sub_as KS _ _ _ _ (Z.boundCode_sub ZS σ), Z.boundedFamily_sub ZS]

end SizeRules

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_ContextInterchangeV2 -/

/-! Interchange of an independent small variable and a size variable. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

namespace CwF

variable (C : CwF.{u, v, w, t})

/-- A map into a context extension is determined by its two components. -/
theorem sub_ext {Γ Δ : C.Ctx} {A : C.Ty Γ} {f g : C.Sub Δ (C.ext Γ A)}
    (hfst : C.comp C.fst f = C.comp C.fst g)
    (hsnd : HEq (C.tmSub C.snd f) (C.tmSub C.snd g)) : f = g := by
  let a := C.castTm (C.tySub_comp A C.fst g) (C.tmSub C.snd g)
  have hf : f = C.pair (C.comp C.fst g) a :=
    C.pair_unique _ _ _ hfst (hsnd.trans (C.castTm_heq _ _).symm)
  have hg : g = C.pair (C.comp C.fst g) a :=
    C.pair_unique _ _ _ rfl (C.castTm_heq _ _).symm
  exact hf.trans hg.symm

end CwF

namespace Universe

variable {C : CwF.{u, v, w, t}} (U : Universe C)

theorem liftEl_fst {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : U.Code Γ) :
    C.comp C.fst (U.liftEl σ A) = C.comp σ C.fst := C.pair_fst _ _

theorem liftEl_snd {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : U.Code Γ) :
    HEq (C.tmSub C.snd (U.liftEl σ A)) (C.snd (Γ := Δ) (A := U.el (U.sub A σ))) :=
  (C.pair_snd _ _).trans (C.castTm_heq _ _)

/-- Lifting through an equal presentation of a decoded code preserves the variable. -/
theorem liftElAs_snd {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : U.Code Γ)
    (B : U.Code Δ) (h : U.sub A σ = B) :
    HEq (C.tmSub C.snd (U.liftElAs σ A B h)) (C.snd (Γ := Δ) (A := U.el B)) := by
  subst B
  exact U.liftEl_snd σ A

theorem liftEl_snd_type {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : U.Code Γ) :
    C.tySub (C.tySub (U.el A) C.fst) (U.liftEl σ A) =
      C.tySub (U.el (U.sub A σ)) C.fst := by
  rw [C.tySub_comp, U.liftEl_fst, ← C.tySub_comp, U.el_sub]
  rfl

end Universe

namespace SizeRules

variable {C : CwF.{u, v, w, t}} {U : Universe C} {I : IdentityTypes C}
    (Z : SizeRules C U I)

theorem sub_id {Γ : C.Ctx} (i : C.Tm Γ (Z.type Γ)) : Z.sub i C.id = i := by
  apply eq_of_heq
  exact (C.castTm_heq _ _).trans (C.tmSub_id i)

end SizeRules

namespace Parametricity

variable {C : CwF.{u, v, w, t}} {U : Universe C} {I : IdentityTypes C}
    (Z : SizeRules C U I)

/-- Forget the small variable while retaining the last size. -/
def interchangeSizeMap {Γ : C.Ctx} (A : U.Code Γ) :
    C.Sub (C.ext (C.ext Γ (U.el A)) (Z.type (C.ext Γ (U.el A))))
      (C.ext Γ (Z.type Γ)) :=
  Z.extend (C.comp C.fst C.fst) (Z.generic (C.ext Γ (U.el A)))

theorem interchangeInverseType {Γ : C.Ctx} (A : U.Code Γ) :
    C.tySub (U.el (U.sub A C.fst)) (interchangeSizeMap Z A) =
      C.tySub (C.tySub (U.el A) C.fst) C.fst := by
  calc
    _ = C.tySub (C.tySub (U.el A) C.fst) (interchangeSizeMap Z A) :=
      congrArg (fun T => C.tySub T (interchangeSizeMap Z A)) (U.el_sub A C.fst).symm
    _ = C.tySub (U.el A) (C.comp C.fst (interchangeSizeMap Z A)) := C.tySub_comp _ _ _
    _ = C.tySub (U.el A) (C.comp C.fst C.fst) := by rw [interchangeSizeMap, Z.extend_fst]
    _ = _ := (C.tySub_comp _ _ _).symm

/-- The inverse swap from `Γ, x : A, i : Size` to `Γ, i : Size, x : A`. -/
def interchangeInverse {Γ : C.Ctx} (A : U.Code Γ) :
    C.Sub (C.ext (C.ext Γ (U.el A)) (Z.type (C.ext Γ (U.el A))))
      (C.ext (C.ext Γ (Z.type Γ)) (U.el (U.sub A C.fst))) :=
  C.pair (interchangeSizeMap Z A)
    (C.castTm (interchangeInverseType Z A).symm (C.tmSub C.snd C.fst))

theorem interchangeInverse_fst {Γ : C.Ctx} (A : U.Code Γ) :
    C.comp C.fst (interchangeInverse Z A) = interchangeSizeMap Z A := C.pair_fst _ _

theorem interchangeInverse_snd {Γ : C.Ctx} (A : U.Code Γ) :
    HEq (C.tmSub C.snd (interchangeInverse Z A))
      (C.tmSub (C.snd (A := U.el A)) (C.fst (A := Z.type (C.ext Γ (U.el A))))) :=
  (C.pair_snd _ _).trans (C.castTm_heq _ _)

theorem interchangeInverse_snd_type {Γ : C.Ctx} (A : U.Code Γ) :
    C.tySub (C.tySub (U.el (U.sub A C.fst)) C.fst) (interchangeInverse Z A) =
      C.tySub (C.tySub (U.el A) C.fst) C.fst := by
  rw [C.tySub_comp, interchangeInverse_fst]
  exact interchangeInverseType Z A

theorem interchange_fst {Γ : C.Ctx} (A : U.Code Γ) :
    C.comp C.fst (interchange Z A) = U.liftEl C.fst A := Z.extend_fst _ _

theorem generic_sub_interchange {Γ : C.Ctx} (A : U.Code Γ) :
    Z.sub (Z.generic (C.ext Γ (U.el A))) (interchange Z A) =
      Z.sub (Z.generic Γ) C.fst := Z.generic_sub_extend _ _

/-- Recover the original small variable after swapping it past the size. -/
theorem interchange_liftEl_inverse {Γ : C.Ctx} (A : U.Code Γ) :
    C.comp (U.liftEl C.fst A) (interchangeInverse Z A) = C.fst := by
  apply C.sub_ext
  · rw [← C.assoc, U.liftEl_fst, C.assoc, interchangeInverse_fst,
      interchangeSizeMap, Z.extend_fst]
  · exact (C.tmSub_comp C.snd (U.liftEl C.fst A) (interchangeInverse Z A)).symm.trans
      ((C.tmSub_heq (U.liftEl_snd_type C.fst A) (U.liftEl_snd C.fst A)
        (interchangeInverse Z A)).trans (interchangeInverse_snd Z A))

/-- Recover the original size after swapping it past the small variable. -/
theorem interchangeSizeMap_interchange {Γ : C.Ctx} (A : U.Code Γ) :
    C.comp (interchangeSizeMap Z A) (interchange Z A) = C.fst := by
  apply Z.hom_ext
  · rw [← C.assoc, interchangeSizeMap, Z.extend_fst, C.assoc,
      interchange_fst, U.liftEl_fst]
  · rw [← Z.sub_comp, interchangeSizeMap, Z.generic_sub_extend, generic_sub_interchange]

/-- Swapping to size-first order and back is the identity substitution. -/
theorem interchange_inverse {Γ : C.Ctx} (A : U.Code Γ) :
    C.comp (interchange Z A) (interchangeInverse Z A) = C.id := by
  apply Z.hom_ext
  · rw [← C.assoc, interchange_fst, interchange_liftEl_inverse, C.comp_id]
  · rw [← Z.sub_comp, generic_sub_interchange, Z.sub_comp, interchangeInverse_fst,
      interchangeSizeMap, Z.generic_sub_extend, Z.sub_id]

/-- Swapping to small-variable-first order and back is the identity substitution. -/
theorem inverse_interchange {Γ : C.Ctx} (A : U.Code Γ) :
    C.comp (interchangeInverse Z A) (interchange Z A) = C.id := by
  apply C.sub_ext
  · rw [← C.assoc, interchangeInverse_fst, interchangeSizeMap_interchange, C.comp_id]
  · have hmid := C.tmSub_comp (C.snd (A := U.el A)) C.fst (interchange Z A)
    rw [interchange_fst] at hmid
    exact (C.tmSub_comp C.snd (interchangeInverse Z A) (interchange Z A)).symm.trans
      ((C.tmSub_heq (interchangeInverse_snd_type Z A) (interchangeInverse_snd Z A)
        (interchange Z A)).trans
          (hmid.trans ((U.liftEl_snd C.fst A).trans (C.tmSub_id C.snd).symm)))

end Parametricity

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_ContextualSumsV2 -/

/-!
# Context substitutions extracting dependent pairs

These substitutions are derived from the source's dependent-sum projections.
They expose the two components in a context and preserve the original context.
They are useful when constructing the canonical parametricity maps.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

namespace DependentSums

variable {C : CwF.{u, v, w, t}} (S : DependentSums C)

/-- The generic dependent pair, transported through sigma-type substitution. -/
def generic {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Tm (C.ext Γ (S.sigma A B))
      (S.sigma (C.tySub A C.fst) (C.tySub B (C.lift C.fst A))) :=
  C.castTm (S.sigma_sub A B C.fst) C.snd

/-- Replace one dependent-pair variable by its first and second projections. -/
def split {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Sub (C.ext Γ (S.sigma A B)) (C.ext (C.ext Γ A) B) :=
  C.pair (C.pair C.fst (S.fst (S.generic A B)))
    (C.castTm ((C.tySub_comp B (C.lift C.fst A) (C.termSub (S.fst (S.generic A B)))).trans
      (congrArg (C.tySub B) (C.lift_termSub C.fst A (S.fst (S.generic A B)))))
      (S.snd (S.generic A B)))

/-- Extracting the components of a pair preserves the preceding context. -/
theorem split_base {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.comp (C.comp C.fst C.fst) (S.split A B) = C.fst := by
  rw [C.assoc, split, C.pair_fst, C.pair_fst]

end DependentSums

namespace SmallTypeConstructors

variable {C : CwF.{u, v, w, t}} {U : Universe C} {P : DependentProducts C}
    {S : DependentSums C} {I : IdentityTypes C} (K : SmallTypeConstructors C U P S I)

/-- Extract the components of a decoded small dependent pair. -/
def sigmaSplit {Γ : C.Ctx} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A))) :
    C.Sub (C.ext Γ (U.el (K.sigma A B))) (C.ext (C.ext Γ (U.el A)) (U.el B)) :=
  C.comp (S.split (U.el A) (U.el B)) (C.castExt (K.el_sigma A B))

/-- Extracting a small dependent pair preserves the original context. -/
theorem sigmaSplit_base {Γ : C.Ctx} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A))) :
    C.comp (C.comp C.fst C.fst) (K.sigmaSplit A B) = C.fst := by
  rw [sigmaSplit, ← C.assoc, S.split_base, C.castExt_fst]

/-- Discard the first component of a small nondependent pair. This is a
contextual term derived from the small sigma decoding and projections. -/
def forgetFirst (F : FunctionTypes C) {Γ : C.Ctx} (A B : U.Code Γ) :
    C.Tm Γ (F.arr (U.el (K.sigma A (U.sub B C.fst))) (U.el B)) := by
  let σ := K.sigmaSplit A (U.sub B C.fst)
  have h : C.tySub (C.tySub (U.el (U.sub B C.fst)) C.fst) σ =
      C.tySub (U.el B) C.fst := by
    calc
      _ = C.tySub (C.tySub (C.tySub (U.el B) C.fst) C.fst) σ :=
        congrArg (fun X => C.tySub (C.tySub X C.fst) σ) (U.el_sub B C.fst).symm
      _ = C.tySub (U.el B) (C.comp (C.comp C.fst C.fst) σ) := by
        rw [C.tySub_comp, C.tySub_comp, C.assoc]
      _ = _ := congrArg (C.tySub (U.el B)) (K.sigmaSplit_base A (U.sub B C.fst))
  exact F.lam (C.castTm h (C.tmSub C.snd σ))

/-- Introduce a small dependent pair after any substitution of its parameter
context. This is the ordinary sigma constructor with explicit type transports. -/
def sigmaPairAt {Γ Δ : C.Ctx} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A)))
    (σ : C.Sub Δ Γ) (a : C.Tm Δ (C.tySub (U.el A) σ))
    (b : C.Tm Δ (C.tySub (U.el B) (C.pair σ a))) :
    C.Tm Δ (C.tySub (U.el (K.sigma A B)) σ) :=
  C.castTm (congrArg (fun X => C.tySub X σ) (K.el_sigma A B).symm)
    (C.castTm (S.sigma_sub (U.el A) (U.el B) σ).symm
      (S.pair a (C.castTm
        ((C.tySub_comp (U.el B) (C.lift σ (U.el A)) (C.termSub a)).trans
          (congrArg (C.tySub (U.el B)) (C.lift_termSub σ (U.el A) a))).symm b)))

/-- Apply an internal arrow to the second component of a small product. -/
def productMap (F : FunctionTypes C) {Γ : C.Ctx} (R A B : U.Code Γ)
    (f : C.Tm Γ (F.arr (U.el A) (U.el B))) :
    C.Tm Γ (F.arr (U.el (K.sigma R (U.sub A C.fst)))
      (U.el (K.sigma R (U.sub B C.fst)))) := by
  let p₀ := @C.fst Γ (U.el R)
  let p₁ := @C.fst (C.ext Γ (U.el R)) (U.el (U.sub A p₀))
  let τ := C.comp p₀ p₁
  let r := C.castTm (C.tySub_comp (U.el R) p₀ p₁) (C.tmSub C.snd p₁)
  have pair_eq : C.pair τ r = p₁ :=
    (C.pair_unique τ r p₁ rfl (C.castTm_heq _ _).symm).symm
  have hA : C.tySub (U.el (U.sub A p₀)) p₁ = C.tySub (U.el A) τ :=
    (congrArg (fun X => C.tySub X p₁) (U.el_sub A p₀).symm).trans (C.tySub_comp _ _ _)
  let a := C.castTm hA C.snd
  let b := F.app (F.sub f τ) a
  have hB : C.tySub (U.el (U.sub B p₀)) (C.pair τ r) = C.tySub (U.el B) τ :=
    (congrArg (C.tySub (U.el (U.sub B p₀))) pair_eq).trans
      ((congrArg (fun X => C.tySub X p₁) (U.el_sub B p₀).symm).trans (C.tySub_comp _ _ _))
  let output := K.sigmaPairAt R (U.sub B p₀) τ r (C.castTm hB.symm b)
  let ρ := K.sigmaSplit R (U.sub A p₀)
  have hout : C.tySub (C.tySub (U.el (K.sigma R (U.sub B p₀))) τ) ρ =
      C.tySub (U.el (K.sigma R (U.sub B p₀))) C.fst :=
    (C.tySub_comp _ τ ρ).trans
      (congrArg (C.tySub (U.el (K.sigma R (U.sub B p₀)))) (K.sigmaSplit_base R (U.sub A p₀)))
  exact F.lam (C.castTm hout (C.tmSub output ρ))

end SmallTypeConstructors

namespace ExistentialSizeQuantifier

variable {C : CwF.{u, v, w, t}} {U : Universe C} {I : IdentityTypes C}
    {Z : SizeRules C U I} (E : ExistentialSizeQuantifier C U I Z)

/-- Introduce an existential after a contextual substitution supplying its size.
The second component is a contextual term, with no added tracking premise. -/
def pairAt {Γ Δ : C.Ctx} (A : U.Code (C.ext Γ (Z.type Γ)))
    (σ : C.Sub Δ (C.ext Γ (Z.type Γ))) (a : C.Tm Δ (C.tySub (U.el A) σ)) :
    C.Tm Δ (C.tySub (U.el (E.code A)) (C.comp C.fst σ)) :=
  C.castTm ((C.tySub_comp (U.el (E.code A)) (C.comp C.fst C.fst) (C.pair σ a)).trans
    (congrArg (C.tySub (U.el (E.code A))) (by rw [C.assoc, C.pair_fst])))
    (C.tmSub (E.pair A) (C.pair σ a))

end ExistentialSizeQuantifier

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_CanonicalAllSigmaV2 -/

/-!
# The canonical map for universal size quantification over dependent sums

The source map sends `(a, f)` to `λ i, (a, f i)`. It is constructed from
dependent-sum projections and universal introduction; invertibility is a
separate parametricity principle.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

namespace Parametricity

variable {C : CwF.{u, v, w, t}} {U : Universe C} {I : IdentityTypes C}
    {P : DependentProducts C} {S : DependentSums C}
    (Z : SizeRules C U I) (F : FunctionTypes C)
    (K : SmallTypeConstructors C U P S I) (Q : UniversalSizeQuantifier C U I Z)
    (QS : UniversalSizeSubstitution U I Z Q)

/-- The exact canonical left-to-right map in `∀` parametric over `Σ`:
`(a, f) ↦ λ i, (a, f i)`. -/
def allSigmaMap {Γ : C.Ctx} (A : U.Code Γ)
    (B : U.Code (C.ext (C.ext Γ (U.el A)) (Z.type (C.ext Γ (U.el A))))) :
    C.Tm Γ (F.arr (U.el (allSigmaSource Z K Q A B))
      (U.el (allSigmaTarget Z K Q A B))) := by
  let pA := @C.fst Γ (U.el A)
  let ph := @C.fst (C.ext Γ (U.el A)) (U.el (Q.code B))
  let σ := C.comp pA ph
  let σsize := Z.lift σ
  let ρ := C.comp (interchangeInverse Z A) (Z.lift ph)
  have hρ : C.comp C.fst ρ = σsize := by
    dsimp [ρ, σsize]
    rw [← C.assoc, interchangeInverse_fst]
    apply Z.hom_ext
    · rw [← C.assoc, interchangeSizeMap, Z.extend_fst, C.assoc,
        Z.lift_fst, Z.lift_fst, ← C.assoc]
    · rw [← Z.sub_comp, interchangeSizeMap, Z.generic_sub_extend,
        Z.generic_sub_lift, Z.generic_sub_lift]
  let a := C.castTm ((C.tySub_comp (U.el (U.sub A C.fst)) C.fst ρ).trans
    (congrArg (C.tySub (U.el (U.sub A C.fst))) hρ)) (C.tmSub C.snd ρ)
  have hpair : C.pair σsize a = ρ :=
    (C.pair_unique σsize a ρ hρ (C.castTm_heq _ _).symm).symm
  have hswap : C.comp (interchange Z A) (C.pair σsize a) = Z.lift ph := by
    rw [hpair]
    dsimp [ρ]
    rw [← C.assoc, interchange_inverse, C.id_comp]
  have hin : C.tySub (U.el (Q.code B)) ph = U.el (Q.code (U.sub B (Z.lift ph))) :=
    (U.el_sub (Q.code B) ph).trans (congrArg U.el (QS.code_sub B ph))
  let value := Q.unlam (C.castTm hin C.snd)
  have hvalue : U.el (U.sub B (Z.lift ph)) =
      C.tySub (U.el (U.sub B (interchange Z A))) (C.pair σsize a) := by
    exact (U.el_sub B (Z.lift ph)).symm.trans
      ((congrArg (C.tySub (U.el B)) hswap.symm).trans
        ((C.tySub_comp (U.el B) (interchange Z A) (C.pair σsize a)).symm.trans
          (congrArg (fun X => C.tySub X (C.pair σsize a))
            (U.el_sub B (interchange Z A)))))
  let D := K.sigma (U.sub A C.fst) (U.sub B (interchange Z A))
  let body := K.sigmaPairAt (U.sub A C.fst) (U.sub B (interchange Z A))
    σsize a (C.castTm hvalue value)
  let quantified := Q.lam (C.castTm (U.el_sub D σsize) body)
  have hout : C.tySub (U.el (Q.code D)) σ = U.el (Q.code (U.sub D σsize)) :=
    (U.el_sub (Q.code D) σ).trans (congrArg U.el (QS.code_sub D σ))
  let branch := C.castTm hout.symm quantified
  let split := K.sigmaSplit A (Q.code B)
  have hbase : C.tySub (C.tySub (U.el (Q.code D)) σ) split =
      C.tySub (U.el (Q.code D)) C.fst := by
    rw [C.tySub_comp]
    exact congrArg (C.tySub (U.el (Q.code D))) (K.sigmaSplit_base A (Q.code B))
  exact F.lam (C.castTm hbase (C.tmSub branch split))

end Parametricity

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_CanonicalParametricityV2 -/

/-!
# Canonical maps appearing in the parametricity axioms

The arrows in this file are constructed from the source type formers. They are
not supplied as extra hypotheses and their invertibility is not assumed here.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

variable {C : CwF.{u, v, w, t}} {U : Universe C} {I : IdentityTypes C}
    {P : DependentProducts C} {S : DependentSums C}

namespace Parametricity

variable (Z : SizeRules C U I) (F : FunctionTypes C)
    (K : SmallTypeConstructors C U P S I) (E : ExistentialSizeQuantifier C U I Z)

/-- The source map `∃ j < i, A(j) → ∃ j, A(j)`, in the context of a size `i`.
It eliminates the existential and forgets the order-proof component of its pair. -/
def boundedToExists {Γ : C.Ctx} (A : U.Code (C.ext Γ (Z.type Γ))) :
    C.Tm (C.ext Γ (Z.type Γ))
      (F.arr (U.el (Z.diamond K E A)) (U.el (U.sub (E.code A) C.fst))) := by
  let D := K.sigma Z.boundCode (U.sub (U.sub A Z.inner) C.fst)
  let p₀ := @C.fst Γ (Z.type Γ)
  let p₁ := @C.fst (C.ext Γ (Z.type Γ)) (Z.type (C.ext Γ (Z.type Γ)))
  let p₂ := @C.fst _ (U.el D)
  let payload := F.app (F.sub (K.forgetFirst F Z.boundCode (U.sub A Z.inner)) p₂) C.snd
  have hp : C.tySub (U.el (U.sub A Z.inner)) p₂ =
      C.tySub (U.el A) (C.comp Z.inner p₂) :=
    (congrArg (fun X => C.tySub X p₂) (U.el_sub A Z.inner).symm).trans
      (C.tySub_comp (U.el A) Z.inner p₂)
  let output := E.pairAt A (C.comp Z.inner p₂) (C.castTm hp payload)
  have hbase : C.comp p₀ (C.comp Z.inner p₂) = C.comp p₀ (C.comp p₁ p₂) := by
    dsimp [p₀, p₁]
    rw [← C.assoc, SizeRules.inner, SizeRules.extend, C.pair_fst, C.assoc]
  have hout : C.tySub (U.el (E.code A)) (C.comp p₀ (C.comp Z.inner p₂)) =
      C.tySub (U.el (U.sub (E.code A) p₀)) (C.comp p₁ p₂) := by
    calc
      _ = C.tySub (U.el (E.code A)) (C.comp p₀ (C.comp p₁ p₂)) :=
        congrArg (C.tySub (U.el (E.code A))) hbase
      _ = C.tySub (C.tySub (U.el (E.code A)) p₀) (C.comp p₁ p₂) :=
        (C.tySub_comp _ _ _).symm
      _ = _ := congrArg (fun X => C.tySub X (C.comp p₁ p₂)) (U.el_sub (E.code A) p₀)
  exact E.recursor F D (U.sub (E.code A) p₀) (C.castTm hout output)

/-- The same bounded-existential elimination with an arbitrary contextual bound. -/
def boundedAtToExists {Γ : C.Ctx} (i : C.Tm Γ (Z.type Γ))
    (A : U.Code (C.ext Γ (Z.type Γ))) :
    C.Tm Γ (F.arr (U.el (boundedExAt Z K E i A)) (U.el (E.code A))) := by
  let R := Z.le (Z.succ (Z.generic Γ)) (Z.sub i C.fst)
  let D := K.sigma R (U.sub A C.fst)
  let π := @C.fst (C.ext Γ (Z.type Γ)) (U.el D)
  let payload := F.app (F.sub (K.forgetFirst F R A) π) C.snd
  exact E.recursor F D (E.code A) (E.pairAt A π payload)

/-- The exact canonical right-to-left map in `∃` parametric over `<`:
`⟨i, ⟨j, p, a⟩⟩ ↦ ⟨j, a⟩`. -/
def existsLtMap {Γ : C.Ctx} (A : U.Code (C.ext Γ (Z.type Γ))) :
    C.Tm Γ (F.arr (U.el (existsLtSource Z K E A)) (U.el (existsLtTarget Z E A))) := by
  let p₀ := @C.fst Γ (Z.type Γ)
  let p₁ := @C.fst (C.ext Γ (Z.type Γ)) (U.el (Z.diamond K E A))
  let branch := F.app (F.sub (boundedToExists Z F K E A) p₁) C.snd
  have h : C.tySub (U.el (U.sub (E.code A) p₀)) p₁ =
      C.tySub (U.el (E.code A)) (C.comp p₀ p₁) :=
    (congrArg (fun X => C.tySub X p₁) (U.el_sub (E.code A) p₀).symm).trans
      (C.tySub_comp _ p₀ p₁)
  exact E.recursor F (Z.diamond K E A) (E.code A) (C.castTm h branch)

/-- The exact canonical left-to-right map in `∀` parametric over `<`:
`f ↦ λ i, λ j < i, f j`. Substitution stability used to abstract its argument
is proved from the source's primitive substitution rules. -/
def allLtMap (Q : UniversalSizeQuantifier C U I Z)
    (ZS : SizeSubstitution U I Z) (KS : SmallTypeSubstitution U P S I K)
    (QS : UniversalSizeSubstitution U I Z Q)
    {Γ : C.Ctx} (A : U.Code (C.ext Γ (Z.type Γ))) :
    C.Tm Γ (F.arr (U.el (allLtSource Z Q A)) (U.el (allLtTarget Z K Q A))) := by
  let σ := @C.fst Γ (U.el (Q.code A))
  have hin : C.tySub (U.el (Q.code A)) σ = U.el (Q.code (U.sub A (Z.lift σ))) :=
    (U.el_sub (Q.code A) σ).trans (congrArg U.el (QS.code_sub A σ))
  have hout : C.tySub (U.el (Q.code (Z.box K Q A))) σ =
      U.el (Q.code (Z.box K Q (U.sub A (Z.lift σ)))) :=
    (U.el_sub (Q.code (Z.box K Q A)) σ).trans
      ((congrArg U.el (QS.code_sub (Z.box K Q A) σ)).trans
        (congrArg (fun B => U.el (Q.code B)) (Z.box_sub K Q ZS KS QS A σ)))
  exact F.lam (C.castTm hout.symm (Z.forallBound K Q (C.castTm hin C.snd)))

end Parametricity

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_ContextualProductsV2 -/

/-!
# Small dependent-function rules after contextual substitution

The two operations here are source lambda abstraction and application, with the
universe decoding and context-lifting transports written explicitly.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

namespace SmallTypeConstructors

variable {C : CwF.{u, v, w, t}} {U : Universe C} {P : DependentProducts C}
    {S : DependentSums C} {I : IdentityTypes C} (K : SmallTypeConstructors C U P S I)

/-- The small code for a nondependent function type. -/
def arrow {Γ : C.Ctx} (A B : U.Code Γ) : U.Code Γ :=
  K.pi A (U.sub B C.fst)

/-- Decoding the small arrow gives the source's nondependent function type. -/
theorem el_arrow {F : FunctionTypes C} (FP : FunctionProductCompatibility F P)
    {Γ : C.Ctx} (A B : U.Code Γ) : U.el (K.arrow A B) = F.arr (U.el A) (U.el B) :=
  (K.el_pi A (U.sub B C.fst)).trans
    ((congrArg (P.pi (U.el A)) (U.el_sub B C.fst).symm).trans (FP.arr_eq _ _).symm)

/-- Small arrow codes commute with contextual substitution. -/
theorem arrow_sub (KS : SmallTypeSubstitution U P S I K)
    {Γ Δ : C.Ctx} (A B : U.Code Γ) (σ : C.Sub Δ Γ) :
    U.sub (K.arrow A B) σ = K.arrow (U.sub A σ) (U.sub B σ) := by
  have h : U.sub (U.sub B C.fst) (U.liftEl σ A) = U.sub (U.sub B σ) C.fst := by
    rw [U.sub_comp, U.sub_comp]
    exact congrArg (U.sub B) (C.pair_fst _ _)
  exact (KS.pi_sub A (U.sub B C.fst) σ).trans (congrArg (K.pi (U.sub A σ)) h)

/-- The ordinary postcomposition operation on decoded small arrows. -/
def postcompose (F : FunctionTypes C) (FP : FunctionProductCompatibility F P)
    {Γ : C.Ctx} (R A B : U.Code Γ) (f : C.Tm Γ (F.arr (U.el A) (U.el B))) :
    C.Tm Γ (F.arr (U.el (K.arrow R A)) (U.el (K.arrow R B))) := by
  let σ := @C.fst Γ (U.el (K.arrow R A))
  let h := C.castTm ((congrArg (fun X => C.tySub X σ) (K.el_arrow FP R A)).trans
    (F.arr_sub (U.el R) (U.el A) σ)) C.snd
  let output := F.compose (F.sub f σ) h
  exact F.lam (C.castTm
    ((congrArg (fun X => C.tySub X σ) (K.el_arrow FP R B)).trans
      (F.arr_sub (U.el R) (U.el B) σ)).symm output)

/-- Introduce a decoded small dependent function after a substitution. -/
def piAbsAt {Γ Δ : C.Ctx} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A)))
    (σ : C.Sub Δ Γ)
    (b : C.Tm (C.ext Δ (C.tySub (U.el A) σ)) (C.tySub (U.el B) (C.lift σ (U.el A)))) :
    C.Tm Δ (C.tySub (U.el (K.pi A B)) σ) :=
  C.castTm (congrArg (fun X => C.tySub X σ) (K.el_pi A B).symm)
    (C.castTm (P.pi_sub (U.el A) (U.el B) σ).symm (P.lam b))

/-- Apply a decoded small dependent function after a substitution. -/
def piAppAt {Γ Δ : C.Ctx} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A)))
    (σ : C.Sub Δ Γ) (f : C.Tm Δ (C.tySub (U.el (K.pi A B)) σ))
    (a : C.Tm Δ (C.tySub (U.el A) σ)) :
    C.Tm Δ (C.tySub (U.el B) (C.pair σ a)) :=
  C.castTm ((C.tySub_comp (U.el B) (C.lift σ (U.el A)) (C.termSub a)).trans
      (congrArg (C.tySub (U.el B)) (C.lift_termSub σ (U.el A) a)))
    (C.tmSub (P.unlam (C.castTm (P.pi_sub (U.el A) (U.el B) σ)
      (C.castTm (congrArg (fun X => C.tySub X σ) (K.el_pi A B)) f))) (C.termSub a))

end SmallTypeConstructors

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_CanonicalExistsPiV2 -/

/-!
# The canonical map for existential quantification and dependent products

The map sends `⟨i, f⟩` to `λ x, let ⟨j, p, b⟩ := f x; ⟨j, b⟩`.
Its construction uses the small existential eliminator and the ordinary small
dependent-function rules. Its invertibility remains a source axiom, not a fact
assumed in this definition.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

namespace Parametricity

variable {C : CwF.{u, v, w, t}} {U : Universe C} {I : IdentityTypes C}
    {P : DependentProducts C} {S : DependentSums C}
    (Z : SizeRules C U I) (F : FunctionTypes C)
    (K : SmallTypeConstructors C U P S I) (E : ExistentialSizeQuantifier C U I Z)
    (ES : ExistentialSizeSubstitution U I Z E)

/-- The size-indexed family under the outer existential in the source's
`∃`-over-`Π` axiom. -/
def existsPiFiber {Γ : C.Ctx} (A : U.Code Γ)
    (B : U.Code (C.ext (C.ext Γ (U.el A)) (Z.type (C.ext Γ (U.el A))))) :
    U.Code (C.ext Γ (Z.type Γ)) :=
  K.pi (U.sub A C.fst)
    (boundedExAt Z K E (Z.sub (Z.generic Γ) C.fst) (U.sub B (Z.lift (U.liftEl C.fst A))))

/-- The branch of the outer existential eliminator in the canonical map. -/
def existsPiBranch {Γ : C.Ctx} (A : U.Code Γ)
    (B : U.Code (C.ext (C.ext Γ (U.el A)) (Z.type (C.ext Γ (U.el A))))) :
    C.Tm (C.ext (C.ext Γ (Z.type Γ)) (U.el (existsPiFiber Z K E A B)))
      (C.tySub (U.el (existsPiSource Z K E A B)) (C.comp C.fst C.fst)) := by
  let p₀ := @C.fst Γ (Z.type Γ)
  let Ai := U.sub A p₀
  let xMap := U.liftEl p₀ A
  let B' := U.sub B (Z.lift xMap)
  let i := Z.sub (Z.generic Γ) (@C.fst (C.ext Γ (Z.type Γ)) (U.el Ai))
  let Bi := boundedExAt Z K E i B'
  let T := K.pi Ai Bi
  let pf := @C.fst (C.ext Γ (Z.type Γ)) (U.el T)
  let σ := C.comp p₀ pf
  let px := @C.fst (C.ext (C.ext Γ (Z.type Γ)) (U.el T)) (C.tySub (U.el A) σ)
  let inputSub := C.comp pf px
  have hx : C.tySub (U.el Ai) inputSub = C.tySub (C.tySub (U.el A) σ) px := by
    calc
      _ = C.tySub (C.tySub (U.el A) p₀) inputSub :=
        congrArg (fun X => C.tySub X inputSub) (U.el_sub A p₀).symm
      _ = C.tySub (U.el A) (C.comp p₀ inputSub) := C.tySub_comp _ _ _
      _ = C.tySub (U.el A) (C.comp σ px) := congrArg (C.tySub (U.el A)) (C.assoc p₀ pf px).symm
      _ = _ := (C.tySub_comp _ _ _).symm
  let x := C.castTm hx.symm C.snd
  let f := C.castTm (C.tySub_comp (U.el T) pf px) (C.tmSub C.snd px)
  let b := K.piAppAt Ai Bi inputSub f x
  let ρ := C.pair inputSub x
  let output := F.app (F.sub (boundedAtToExists Z F K E i B') ρ) b
  have hρ : C.comp xMap ρ = C.lift σ (U.el A) := by
    apply C.sub_ext
    · change C.comp C.fst (C.comp (U.liftEl p₀ A) (C.pair inputSub x)) =
        C.comp C.fst (C.lift σ (U.el A))
      rw [← C.assoc, U.liftEl_fst, C.assoc, C.pair_fst, C.lift_fst]
      exact (C.assoc p₀ pf px).symm
    · exact (C.tmSub_comp C.snd xMap ρ).symm.trans
        ((C.tmSub_heq (U.liftEl_snd_type p₀ A) (U.liftEl_snd p₀ A) ρ).trans
          ((C.pair_snd inputSub x).trans
            ((C.castTm_heq hx.symm C.snd).trans (C.lift_snd σ (U.el A)).symm)))
  have he : C.tySub (U.el (E.code B)) xMap = U.el (E.code B') :=
    (U.el_sub (E.code B) xMap).trans (congrArg U.el (ES.code_sub B xMap))
  have hout : C.tySub (U.el (E.code B')) ρ = C.tySub (U.el (E.code B)) (C.lift σ (U.el A)) :=
    (congrArg (fun X => C.tySub X ρ) he.symm).trans
      ((C.tySub_comp (U.el (E.code B)) xMap ρ).trans
        (congrArg (C.tySub (U.el (E.code B))) hρ))
  exact K.piAbsAt A (E.code B) σ (C.castTm hout output)

/-- The exact canonical right-to-left arrow in `∃` parametric over `Π`. -/
def existsPiMap {Γ : C.Ctx} (A : U.Code Γ)
    (B : U.Code (C.ext (C.ext Γ (U.el A)) (Z.type (C.ext Γ (U.el A))))) :
    C.Tm Γ (F.arr (U.el (existsPiTarget Z K E A B)) (U.el (existsPiSource Z K E A B))) :=
  E.recursor F (existsPiFiber Z K E A B) (existsPiSource Z K E A B)
    (existsPiBranch Z F K E ES A B)

end Parametricity

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_TheorySubstitutionV2 -/

/-!
# Substitution of identity elimination

The source explicitly assumes substitution admissible for every judgment.
This interface states its instance for `J`, using the actual based path-context
lift constructed from the CwF rules. The motive is reindexed along that lift;
there is no independent semantic operation hidden in this condition.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

variable {C : CwF.{u, v, w, t}}

/-- Identity elimination commutes with contextual substitution. The transported
reflexivity branch is explicit so that no equality of internal paths is imposed. -/
structure IdentityEliminationSubstitution (I : IdentityTypes C) (J : IdentityElimination C I) where
  elim_sub : ∀ {Γ Δ} {A : C.Ty Γ} (a : C.Tm Γ A) (M : C.Ty (I.pathContext a))
    (d : C.Tm Γ (C.tySub M (I.pathSub a a (I.refl a))))
    (b : C.Tm Γ A) (p : C.Tm Γ (I.id A a b)) (σ : C.Sub Δ Γ)
    (d' : C.Tm Δ (C.tySub (C.tySub M (I.pathLift a σ))
      (I.pathSub (C.tmSub a σ) (C.tmSub a σ) (I.refl (C.tmSub a σ))))),
    HEq (C.tmSub d σ) d' →
    HEq (C.tmSub (J.elim a M d b p) σ)
      (J.elim (C.tmSub a σ) (C.tySub M (I.pathLift a σ)) d' (C.tmSub b σ)
        (C.castTm (I.id_sub a b σ) (C.tmSub p σ)))

/-- The function-extensionality axiom schema is stable under substitution.
The canonical map remains the one constructed by identity elimination. -/
structure FunctionExtensionalitySubstitution (F : FunctionTypes C)
    (P : DependentProducts C) (S : DependentSums C) (I : IdentityTypes C)
    (J : IdentityElimination C I) (E : FunctionExtensionality C F P S I J) where
  isEquiv_sub : ∀ {Γ Δ} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (f g : C.Tm Γ (P.pi A B)) (σ : C.Sub Δ Γ),
    HEq (C.tmSub (E.isEquiv_happly f g) σ)
      (E.isEquiv_happly (P.sub f σ) (P.sub g σ))

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_RecursionNaturalityV2 -/

/-! Substitution of the large size-recursion types and its internal solution type. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

namespace CwF

variable (C : CwF.{u,v,w,t})

/-- Lift under a type binder, using an explicitly equal presentation of its substitution. -/
def liftAs {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : C.Ty Γ) (A' : C.Ty Δ)
    (h : C.tySub A σ = A') : C.Sub (C.ext Δ A') (C.ext Γ A) :=
  h ▸ C.lift σ A

theorem liftAs_fst {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : C.Ty Γ) (A' : C.Ty Δ)
    (h : C.tySub A σ = A') : C.comp C.fst (C.liftAs σ A A' h) = C.comp σ C.fst := by
  subst A'
  exact C.pair_fst _ _

theorem liftAs_snd {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : C.Ty Γ) (A' : C.Ty Δ)
    (h : C.tySub A σ = A') : HEq (C.tmSub C.snd (C.liftAs σ A A' h))
      (@C.snd Δ A') := by
  subst A'
  exact (C.pair_snd _ _).trans (C.castTm_heq _ _)

end CwF

namespace DependentProducts

variable {C : CwF.{u,v,w,t}} (P : DependentProducts C)

theorem pi_sub_as {Γ Δ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (σ : C.Sub Δ Γ) (A' : C.Ty Δ) (h : C.tySub A σ = A') :
    C.tySub (P.pi A B) σ = P.pi A' (C.tySub B (C.liftAs σ A A' h)) := by
  subst A'
  exact P.pi_sub A B σ

end DependentProducts

namespace SizeRules

variable {C : CwF.{u,v,w,t}} {U : Universe C} {I : IdentityTypes C}
    (Z : SizeRules C U I)

theorem liftAs_eq_lift {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) :
    C.liftAs σ (Z.type Γ) (Z.type Δ) (Z.type_sub σ) = Z.lift σ := by
  apply Z.hom_ext
  · exact (C.liftAs_fst _ _ _ _).trans (Z.lift_fst σ).symm
  · rw [Z.generic_sub_lift]
    apply eq_of_heq
    exact (Z.sub_generic_heq _).trans ((C.liftAs_snd _ _ _ _).trans (C.castTm_heq _ _).symm)

theorem pi_sub (P : DependentProducts C) {Γ Δ : C.Ctx}
    (A : C.Ty (C.ext Γ (Z.type Γ))) (σ : C.Sub Δ Γ) :
    C.tySub (P.pi (Z.type Γ) A) σ = P.pi (Z.type Δ) (C.tySub A (Z.lift σ)) := by
  rw [P.pi_sub_as _ _ _ _ (Z.type_sub σ), Z.liftAs_eq_lift]

theorem bounded_sub (P : DependentProducts C) (F : FunctionTypes C)
    (ZS : SizeSubstitution U I Z) {Γ Δ : C.Ctx}
    (A : C.Ty (C.ext Γ (Z.type Γ))) (σ : C.Sub Δ Γ) :
    C.tySub (Z.bounded P F A) (Z.lift σ) = Z.bounded P F (C.tySub A (Z.lift σ)) := by
  unfold bounded
  rw [Z.pi_sub, F.arr_sub]
  apply congrArg (P.pi _)
  apply congrArg₂ F.arr
  · change C.tySub (U.el Z.boundCode) (Z.lift (Z.lift σ)) = U.el Z.boundCode
    exact (U.el_sub _ _).trans (congrArg U.el (Z.boundCode_sub ZS σ))
  · rw [C.tySub_comp, Z.inner_lift, ← C.tySub_comp]

theorem step_sub (P : DependentProducts C) (F : FunctionTypes C)
    (ZS : SizeSubstitution U I Z) {Γ Δ : C.Ctx}
    (A : C.Ty (C.ext Γ (Z.type Γ))) (σ : C.Sub Δ Γ) :
    C.tySub (P.pi (Z.type Γ) (F.arr (Z.bounded P F A) A)) σ =
      P.pi (Z.type Δ) (F.arr (Z.bounded P F (C.tySub A (Z.lift σ)))
        (C.tySub A (Z.lift σ))) := by
  rw [Z.pi_sub, F.arr_sub, Z.bounded_sub P F ZS]

/-- The internal pointwise unfolding equation for a candidate size-recursive function. -/
def fixedPointEquation (P : DependentProducts C) (F : FunctionTypes C)
    {Γ : C.Ctx} (A : C.Ty (C.ext Γ (Z.type Γ)))
    (f : C.Tm Γ (P.pi (Z.type Γ) (F.arr (Z.bounded P F A) A)))
    (h : C.Tm Γ (P.pi (Z.type Γ) A)) : C.Ty Γ :=
  P.pi (Z.type Γ) (I.id A (P.unlam h) (F.app (P.unlam f) (Z.restrict P F h)))

/-- The precise internal solution type of Lemma 1, including its equality witness.
Contractibility of this type is a theorem, not an assumption of size recursion. -/
def fixedPointSolutions (P : DependentProducts C) (F : FunctionTypes C)
    (S : DependentSums C) (ZS : SizeSubstitution U I Z)
    {Γ : C.Ctx} (A : C.Ty (C.ext Γ (Z.type Γ)))
    (f : C.Tm Γ (P.pi (Z.type Γ) (F.arr (Z.bounded P F A) A))) : C.Ty Γ :=
  let σ := @C.fst Γ (P.pi (Z.type Γ) A)
  S.sigma (P.pi (Z.type Γ) A)
    (Z.fixedPointEquation P F (C.tySub A (Z.lift σ))
      (C.castTm (Z.step_sub P F ZS A σ) (C.tmSub f σ))
      (C.castTm (Z.pi_sub P A σ) C.snd))

end SizeRules

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_TheoryPackageV2 -/

/-! The complete source rule package, before adding the four parametricity axioms. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

/-- A contextual interpretation of Section 2 before the parametricity axioms.
Every field is a primitive source rule or its substitution stability. In
particular, neither uniqueness of fixpoints nor algebra initiality is assumed. -/
structure CoreTheory (C : CwF.{u,v,w,t}) where
  functions : FunctionTypes C
  products : DependentProducts C
  functionProducts : FunctionProductCompatibility functions products
  sums : DependentSums C
  sumSubstitution : DependentSumSubstitution sums
  identities : IdentityTypes C
  identityElimination : IdentityElimination C identities
  identitySubstitution : IdentityEliminationSubstitution identities identityElimination
  univ : Universe C
  small : SmallTypeConstructors C univ products sums identities
  smallSubstitution : SmallTypeSubstitution univ products sums identities small
  base : BaseTypes univ
  baseSubstitution : BaseTypeSubstitution univ base
  size : SizeRules C univ identities
  sizeSubstitution : SizeSubstitution univ identities size
  recursion : SizeRecursion C univ identities size products functions
  recursionSubstitution : SizeRecursionSubstitution univ identities size products functions recursion
  all : UniversalSizeQuantifier C univ identities size
  allSubstitution : UniversalSizeSubstitution univ identities size all
  ex : ExistentialSizeQuantifier C univ identities size
  exSubstitution : ExistentialSizeSubstitution univ identities size ex
  exTermSubstitution : ExistentialTermSubstitution univ identities size ex exSubstitution
  funext : FunctionExtensionality C functions products sums identities identityElimination
  funextSubstitution : FunctionExtensionalitySubstitution functions products sums identities
    identityElimination funext

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_TheoryPathOperationsV2 -/

/-! Internal path operations derived from the identity eliminator. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory.InternalPath

universe u v w t

variable {C : CwF.{u, v, w, t}} (I : IdentityTypes C) (J : IdentityElimination C I)

def reverseFamily {Γ : C.Ctx} {A : C.Ty Γ} (a : C.Tm Γ A) : C.Ty (C.ext Γ A) :=
  I.id (C.tySub A C.fst) C.snd (C.tmSub a C.fst)

theorem reverseFamily_sub {Γ : C.Ctx} {A : C.Ty Γ} (a b : C.Tm Γ A) :
    C.tySub (reverseFamily I a) (C.termSub b) = I.id A b a := by
  rw [reverseFamily, I.id_sub]
  exact I.id_congr (C.tySub_fst_termSub A b)
    (C.termSub_snd b) (C.tmSub_fst_termSub a b)

/-- Reverse an internal path using dependent transport, hence the source J rule. -/
def symm {Γ : C.Ctx} {A : C.Ty Γ} {a b : C.Tm Γ A}
    (p : C.Tm Γ (I.id A a b)) : C.Tm Γ (I.id A b a) :=
  C.castTm (reverseFamily_sub I a b)
    (transport I J (reverseFamily I a) p
      (C.castTm (reverseFamily_sub I a a).symm (I.refl a)))

end LaarakkerOttenVanDenBerg2026.V2.Theory.InternalPath

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_ParametricityAxiomsV2 -/

/-!
# The four source parametricity axioms

Each axiom asserts that the source's exact canonical map is a half-adjoint
equivalence. All four maps are constructed in preceding modules. Their inverses,
homotopies, and coherence are encoded internally by `isEquiv`; no metatheoretic
equivalence or merely existential map is substituted for the source statement.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

variable {C : CwF.{u, v, w, t}}

/-- The four equivalence axioms of Section 2.2, on their canonical arrows. -/
structure ParametricityAxioms (F : FunctionTypes C) (P : DependentProducts C)
    (S : DependentSums C) (I : IdentityTypes C) (J : IdentityElimination C I)
    (U : Universe C) (K : SmallTypeConstructors C U P S I) (Z : SizeRules C U I)
    (E : ExistentialSizeQuantifier C U I Z) (Q : UniversalSizeQuantifier C U I Z)
    (ZS : SizeSubstitution U I Z) (KS : SmallTypeSubstitution U P S I K)
    (QS : UniversalSizeSubstitution U I Z Q) (ES : ExistentialSizeSubstitution U I Z E) where
  existsPi : ∀ {Γ} (A : U.Code Γ)
    (B : U.Code (C.ext (C.ext Γ (U.el A)) (Z.type (C.ext Γ (U.el A))))),
    C.Tm Γ (InternalEquivalence.isEquiv F P I S J (Parametricity.existsPiMap Z F K E ES A B))
  allSigma : ∀ {Γ} (A : U.Code Γ)
    (B : U.Code (C.ext (C.ext Γ (U.el A)) (Z.type (C.ext Γ (U.el A))))),
    C.Tm Γ (InternalEquivalence.isEquiv F P I S J (Parametricity.allSigmaMap Z F K Q QS A B))
  existsLt : ∀ {Γ} (A : U.Code (C.ext Γ (Z.type Γ))),
    C.Tm Γ (InternalEquivalence.isEquiv F P I S J (Parametricity.existsLtMap Z F K E A))
  allLt : ∀ {Γ} (A : U.Code (C.ext Γ (Z.type Γ))),
    C.Tm Γ (InternalEquivalence.isEquiv F P I S J (Parametricity.allLtMap Z F K Q ZS KS QS A))

/-- Structural substitution for the four source axiom schemas. These equations
only express substitution of their proof terms; they do not add any equivalence
or encoding conclusion beyond the source's four axioms. -/
structure ParametricitySubstitution (F : FunctionTypes C) (P : DependentProducts C)
    (S : DependentSums C) (I : IdentityTypes C) (J : IdentityElimination C I)
    (U : Universe C) (K : SmallTypeConstructors C U P S I) (Z : SizeRules C U I)
    (E : ExistentialSizeQuantifier C U I Z) (Q : UniversalSizeQuantifier C U I Z)
    (ZS : SizeSubstitution U I Z) (KS : SmallTypeSubstitution U P S I K)
    (QS : UniversalSizeSubstitution U I Z Q) (ES : ExistentialSizeSubstitution U I Z E)
    (Axioms : ParametricityAxioms F P S I J U K Z E Q ZS KS QS ES) where
  existsPi_sub : ∀ {Γ Δ} (A : U.Code Γ)
    (B : U.Code (C.ext (C.ext Γ (U.el A)) (Z.type (C.ext Γ (U.el A))))) (σ : C.Sub Δ Γ),
    HEq (C.tmSub (Axioms.existsPi A B) σ)
      (Axioms.existsPi (U.sub A σ) (U.sub B (Z.lift (U.liftEl σ A))))
  allSigma_sub : ∀ {Γ Δ} (A : U.Code Γ)
    (B : U.Code (C.ext (C.ext Γ (U.el A)) (Z.type (C.ext Γ (U.el A))))) (σ : C.Sub Δ Γ),
    HEq (C.tmSub (Axioms.allSigma A B) σ)
      (Axioms.allSigma (U.sub A σ) (U.sub B (Z.lift (U.liftEl σ A))))
  existsLt_sub : ∀ {Γ Δ} (A : U.Code (C.ext Γ (Z.type Γ))) (σ : C.Sub Δ Γ),
    HEq (C.tmSub (Axioms.existsLt A) σ) (Axioms.existsLt (U.sub A (Z.lift σ)))
  allLt_sub : ∀ {Γ Δ} (A : U.Code (C.ext Γ (Z.type Γ))) (σ : C.Sub Δ Γ),
    HEq (C.tmSub (Axioms.allLt A) σ) (Axioms.allLt (U.sub A (Z.lift σ)))

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_ParametricTheoryV2 -/

/-! The full source theory: the contextual core plus exactly four parametricity axioms. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

/-- Section 2 and Appendix A, with all operations acting on contextual terms.
Realizers, trackers, external function introduction, identity reflection, and
uniqueness of fixpoints are not fields of this theory. -/
structure ParametricTheory (C : CwF.{u,v,w,t}) extends CoreTheory C where
  parametricity : ParametricityAxioms functions products sums identities identityElimination
    univ small size ex all sizeSubstitution smallSubstitution allSubstitution exSubstitution
  parametricitySubstitution : ParametricitySubstitution functions products sums identities
    identityElimination univ small size ex all sizeSubstitution smallSubstitution
    allSubstitution exSubstitution parametricity

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_TheoryConsequencesV2 -/

/-! Source conclusions used as open mission targets. These are predicates,
not fields of the primitive type theory and not assumed proof results. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

namespace CoreTheory

variable {C : CwF.{u,v,w,t}} (T : CoreTheory C)

/-- An internal half-adjoint equivalence between two contextual types. -/
abbrev HasTypeEquivalence {Γ : C.Ctx} (A B : C.Ty Γ) : Prop :=
  Nonempty (C.Tm Γ (InternalEquivalence.equivalence T.functions T.products
    T.identities T.sums T.identityElimination A B))

/-- Proposition 2: dependent products commute with universal size quantification,
and dependent sums commute with existential size quantification. -/
def DefinableQuantifierEquivalences : Prop :=
  ∀ (Γ : C.Ctx) (A : T.univ.Code Γ)
    (B : T.univ.Code (C.ext (C.ext Γ (T.univ.el A))
      (T.size.type (C.ext Γ (T.univ.el A))))),
    T.HasTypeEquivalence
      (T.univ.el (T.small.pi A (T.all.code B)))
      (T.univ.el (T.all.code
        (T.small.pi (T.univ.sub A C.fst)
          (T.univ.sub B (Parametricity.interchange T.size A))))) ∧
    T.HasTypeEquivalence
      (T.univ.el (T.small.sigma A (T.ex.code B)))
      (T.univ.el (T.ex.code
        (T.small.sigma (T.univ.sub A C.fst)
          (T.univ.sub B (Parametricity.interchange T.size A)))))

/-- Proposition 3: quantifying a size-independent small type returns an
internally equivalent type. Dependence on the ambient context remains allowed. -/
def ConstantQuantifierEquivalences : Prop :=
  ∀ (Γ : C.Ctx) (A : T.univ.Code Γ),
    T.HasTypeEquivalence (T.univ.el (T.ex.code (T.univ.sub A
      (@C.fst Γ (T.size.type Γ))))) (T.univ.el A) ∧
    T.HasTypeEquivalence (T.univ.el (T.all.code (T.univ.sub A
      (@C.fst Γ (T.size.type Γ))))) (T.univ.el A)

/-- Semantic consistency means there is no closed term of the chosen empty type. -/
def IsConsistent : Prop :=
  ¬ Nonempty (C.Tm C.empty (T.univ.el T.base.empty))

end CoreTheory

end LaarakkerOttenVanDenBerg2026.V2.Theory


