-- Prove2me | Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingRevision2
-- name    : LaarakkerOttenVanDenBerg2026_EncodingRevision2
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-17T07:41:55.532659+00:00
-- url     : https://prove2.me/theorems/2a696c9c-9e87-4e86-b546-c3ea7588c3dd
-- title:
--   Internal polynomial, sized, inductive and coinductive constructions
-- statement:
--   Wild endofunctors have internal object and morphism operations with substitution and internal identity/composition laws. The file constructs literal polynomial functor data, size-indexed arrows and modal actions, full algebra/coalgebra hom types, internally quantified initiality and terminality, the prescribed weak-commutation maps, recursive sized carriers, and their J-transported structure maps. Unsized mu and nu structures use the source quantifier action and the inverse of the specified weak-commutation map. Polynomial laws, initiality/terminality and functorial lifting remain theorem conclusions, not added fields. Homwise equivalence types are distinguished from natural adjunctions; the lifting targets retain full morphism witnesses while stating identity/composition laws for the prescribed underlying arrows.
-- source:
--   Laarakker, Otten and van den Berg, Constructing (Co)inductive Types via Large Sizes, arXiv:2602.18921v2, Section 3 and Appendix B, https://arxiv.org/abs/2602.18921v2

import Definitions.Def_LaarakkerOttenVanDenBerg2026_TheoryRevision2

/-! Generated from reviewed V2 modules by bundle_v2.py.
See the accompanying manifest for exact input hashes and source order. -/

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingV2 -/

/-!
# Internal functor data in a contextual type theory

Section 3 describes internal terms, rather than arbitrary functions on a Lean
type of decoded elements. Here the object and morphism operations are given in
their substitution-natural contextual form. The generic-specialization theorems
below prove that these operations are determined by their generic terms.

No realizer, tracker transformer, recursive solution, initiality, or terminality
is part of the functor data. The categorical laws, when supplied, are terms of
internal identity types. This file does not claim the encoding theorems.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

variable {C : CwF.{u, v, w, t}}

/-- An internal arrow between two small types, in a fixed context. -/
abbrev SmallHom (U : Universe C) (P : FunctionTypes C) {Γ : C.Ctx}
    (A B : U.Code Γ) := C.Tm Γ (P.arr (U.el A) (U.el B))

namespace SmallHom

variable (U : Universe C) (P : FunctionTypes C)

/-- The substituted type of a small arrow. -/
theorem type_sub {Γ Δ : C.Ctx} (A B : U.Code Γ) (σ : C.Sub Δ Γ) :
    C.tySub (P.arr (U.el A) (U.el B)) σ =
      P.arr (U.el (U.sub A σ)) (U.el (U.sub B σ)) := by
  rw [P.arr_sub, U.el_sub, U.el_sub]
  rfl

/-- Substitution of an internal small arrow. -/
def sub {Γ Δ : C.Ctx} {A B : U.Code Γ} (f : SmallHom U P A B) (σ : C.Sub Δ Γ) :
    SmallHom U P (U.sub A σ) (U.sub B σ) :=
  C.castTm (type_sub U P A B σ) (C.tmSub f σ)

end SmallHom

/-- The contextual form of an internal endofunctor's object and morphism
operations. Naturality is substitution coherence of a term, not an additional
mathematical hypothesis about a source functor. -/
structure InternalFunctorData (U : Universe C) (P : FunctionTypes C) (Γ : C.Ctx) where
  obj : {Δ : C.Ctx} → C.Sub Δ Γ → U.Code Δ → U.Code Δ
  obj_sub : ∀ {Δ Θ} (σ : C.Sub Δ Γ) (A : U.Code Δ) (τ : C.Sub Θ Δ),
    U.sub (obj σ A) τ = obj (C.comp σ τ) (U.sub A τ)
  map : {Δ : C.Ctx} → (σ : C.Sub Δ Γ) → (A B : U.Code Δ) →
    SmallHom U P A B → SmallHom U P (obj σ A) (obj σ B)
  map_sub : ∀ {Δ Θ} (σ : C.Sub Δ Γ) (A B : U.Code Δ)
    (f : SmallHom U P A B) (τ : C.Sub Θ Δ),
    HEq (SmallHom.sub U P (map σ A B f) τ)
      (map (C.comp σ τ) (U.sub A τ) (U.sub B τ) (SmallHom.sub U P f τ))

namespace InternalFunctorData

variable {U : Universe C} {P : FunctionTypes C} {Γ : C.Ctx}
    (F : InternalFunctorData U P Γ)

/-- The generic object term in `Γ, A : U`. -/
def genericObject : U.Code (C.ext Γ (U.type Γ)) :=
  F.obj C.fst (U.generic Γ)

/-- Every object-operation instance is substitution of its one generic term. -/
theorem object_from_generic {Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : U.Code Δ) :
    U.sub F.genericObject (U.extend σ A) = F.obj σ A := by
  rw [genericObject, F.obj_sub, U.extend_fst, U.generic_sub_extend]

/-- The closed internal function `F : U → U` determined by the object operation. -/
def objectTerm : C.Tm Γ (P.arr (U.type Γ) (U.type Γ)) :=
  P.lam (C.castTm (U.type_sub C.fst).symm F.genericObject)

/-- Congruence of the morphism operation, including external type transports. -/
theorem map_congr {Δ : C.Ctx} {σ τ : C.Sub Δ Γ} (hσ : σ = τ)
    {A B A' B' : U.Code Δ} (hA : A = A') (hB : B = B')
    {f : SmallHom U P A B} {g : SmallHom U P A' B'} (hf : HEq f g) :
    HEq (F.map σ A B f) (F.map τ A' B' g) := by
  cases hσ
  cases hA
  cases hB
  cases hf
  rfl

end InternalFunctorData

namespace GenericArrow

variable (U : Universe C) (P : FunctionTypes C) (Γ : C.Ctx)

/-- The context of two small-type codes. -/
abbrev codes : C.Ctx := C.ext (C.ext Γ (U.type Γ)) (U.type (C.ext Γ (U.type Γ)))

/-- The first generic code in `Γ, A : U, B : U`. -/
def domain : U.Code (codes U Γ) := U.sub (U.generic Γ) C.fst

/-- The second generic code in `Γ, A : U, B : U`. -/
def codomain : U.Code (codes U Γ) := U.generic (C.ext Γ (U.type Γ))

/-- Forget both generic codes. -/
def base : C.Sub (codes U Γ) Γ := C.comp C.fst C.fst

/-- The context `Γ, A : U, B : U, f : A → B`. -/
abbrev context : C.Ctx :=
  C.ext (codes U Γ) (P.arr (U.el (domain U Γ)) (U.el (codomain U Γ)))

/-- The first code weakened into the generic arrow context. -/
def source : U.Code (context U P Γ) := U.sub (domain U Γ) C.fst

/-- The second code weakened into the generic arrow context. -/
def target : U.Code (context U P Γ) := U.sub (codomain U Γ) C.fst

/-- Forget the codes and the arrow. -/
def projection : C.Sub (context U P Γ) Γ := C.comp (base U Γ) C.fst

/-- The generic internal arrow. -/
def term : SmallHom U P (source U P Γ) (target U P Γ) :=
  C.castTm (SmallHom.type_sub U P (domain U Γ) (codomain U Γ) C.fst) C.snd

/-- Substitute two small-type codes into their generic context. -/
def codesSub {Δ : C.Ctx} (σ : C.Sub Δ Γ) (A B : U.Code Δ) : C.Sub Δ (codes U Γ) :=
  U.extend (U.extend σ A) B

theorem domain_sub {Δ : C.Ctx} (σ : C.Sub Δ Γ) (A B : U.Code Δ) :
    U.sub (domain U Γ) (codesSub U Γ σ A B) = A := by
  rw [domain, U.sub_comp, codesSub, U.extend_fst, U.generic_sub_extend]

theorem codomain_sub {Δ : C.Ctx} (σ : C.Sub Δ Γ) (A B : U.Code Δ) :
    U.sub (codomain U Γ) (codesSub U Γ σ A B) = B :=
  U.generic_sub_extend _ _

theorem base_sub {Δ : C.Ctx} (σ : C.Sub Δ Γ) (A B : U.Code Δ) :
    C.comp (base U Γ) (codesSub U Γ σ A B) = σ := by
  rw [base, C.assoc, codesSub, U.extend_fst, U.extend_fst]

/-- The generic arrow type specializes to the specified domain and codomain. -/
theorem arrowType_sub {Δ : C.Ctx} (σ : C.Sub Δ Γ) (A B : U.Code Δ) :
    C.tySub (P.arr (U.el (domain U Γ)) (U.el (codomain U Γ)))
      (codesSub U Γ σ A B) = P.arr (U.el A) (U.el B) := by
  rw [SmallHom.type_sub, domain_sub, codomain_sub]

/-- Substitute codes and an arrow into the generic arrow context. -/
def specialize {Δ : C.Ctx} (σ : C.Sub Δ Γ) (A B : U.Code Δ) (f : SmallHom U P A B) :
    C.Sub Δ (context U P Γ) :=
  C.pair (codesSub U Γ σ A B) (C.castTm (arrowType_sub U P Γ σ A B).symm f)

theorem source_sub {Δ : C.Ctx} (σ : C.Sub Δ Γ) (A B : U.Code Δ)
    (f : SmallHom U P A B) : U.sub (source U P Γ) (specialize U P Γ σ A B f) = A := by
  rw [source, U.sub_comp, specialize, C.pair_fst, domain_sub]

theorem target_sub {Δ : C.Ctx} (σ : C.Sub Δ Γ) (A B : U.Code Δ)
    (f : SmallHom U P A B) : U.sub (target U P Γ) (specialize U P Γ σ A B f) = B := by
  rw [target, U.sub_comp, specialize, C.pair_fst, codomain_sub]

theorem projection_sub {Δ : C.Ctx} (σ : C.Sub Δ Γ) (A B : U.Code Δ)
    (f : SmallHom U P A B) :
    C.comp (projection U P Γ) (specialize U P Γ σ A B f) = σ := by
  rw [projection, C.assoc, specialize, C.pair_fst, base_sub]

/-- Substitution of the generic arrow recovers the supplied arrow. -/
theorem term_sub {Δ : C.Ctx} (σ : C.Sub Δ Γ) (A B : U.Code Δ) (f : SmallHom U P A B) :
    HEq (SmallHom.sub U P (term U P Γ) (specialize U P Γ σ A B f)) f := by
  exact (C.castTm_heq _ _).trans
    ((C.tmSub_heq (SmallHom.type_sub U P (domain U Γ) (codomain U Γ) C.fst).symm
      (C.castTm_heq _ _) (specialize U P Γ σ A B f)).trans
      ((C.pair_snd _ _).trans (C.castTm_heq _ _)))

end GenericArrow

namespace InternalFunctorData

variable {U : Universe C} {P : FunctionTypes C} {Γ : C.Ctx}
    (F : InternalFunctorData U P Γ)

/-- The one generic morphism-action term in `Γ, A : U, B : U, f : A → B`. -/
def genericMap : SmallHom U P
    (F.obj (GenericArrow.projection U P Γ) (GenericArrow.source U P Γ))
    (F.obj (GenericArrow.projection U P Γ) (GenericArrow.target U P Γ)) :=
  F.map (GenericArrow.projection U P Γ) (GenericArrow.source U P Γ)
    (GenericArrow.target U P Γ) (GenericArrow.term U P Γ)

/-- Every morphism-operation instance is substitution of its one generic term.
This is the contextual representability condition missing from an arbitrary
external functor on the set of universe codes. -/
theorem map_from_generic {Δ : C.Ctx} (σ : C.Sub Δ Γ) (A B : U.Code Δ)
    (f : SmallHom U P A B) :
    HEq (SmallHom.sub U P F.genericMap (GenericArrow.specialize U P Γ σ A B f))
      (F.map σ A B f) := by
  exact (F.map_sub _ _ _ _ _).trans
    (F.map_congr (GenericArrow.projection_sub U P Γ σ A B f)
      (GenericArrow.source_sub U P Γ σ A B f)
      (GenericArrow.target_sub U P Γ σ A B f)
      (GenericArrow.term_sub U P Γ σ A B f))

end InternalFunctorData

/-! The context of three small types and two composable arrows, used to state
the functor composition law as one internal term. -/
namespace GenericComposition

variable (U : Universe C) (P : FunctionTypes C) (Γ : C.Ctx)

abbrev codes : C.Ctx := C.ext (GenericArrow.codes U Γ) (U.type (GenericArrow.codes U Γ))

def firstCode : U.Code (codes U Γ) := U.sub (GenericArrow.domain U Γ) C.fst
def middleCode : U.Code (codes U Γ) := U.sub (GenericArrow.codomain U Γ) C.fst
def lastCode : U.Code (codes U Γ) := U.generic (GenericArrow.codes U Γ)

abbrev firstContext : C.Ctx :=
  C.ext (codes U Γ) (P.arr (U.el (firstCode U Γ)) (U.el (middleCode U Γ)))

def firstDomain : U.Code (firstContext U P Γ) := U.sub (firstCode U Γ) C.fst
def firstCodomain : U.Code (firstContext U P Γ) := U.sub (middleCode U Γ) C.fst
def lastCodomain : U.Code (firstContext U P Γ) := U.sub (lastCode U Γ) C.fst

def firstTerm : SmallHom U P (firstDomain U P Γ) (firstCodomain U P Γ) :=
  C.castTm (SmallHom.type_sub U P (firstCode U Γ) (middleCode U Γ) C.fst) C.snd

abbrev context : C.Ctx := C.ext (firstContext U P Γ)
  (P.arr (U.el (firstCodomain U P Γ)) (U.el (lastCodomain U P Γ)))

def source : U.Code (context U P Γ) := U.sub (firstDomain U P Γ) C.fst
def middle : U.Code (context U P Γ) := U.sub (firstCodomain U P Γ) C.fst
def target : U.Code (context U P Γ) := U.sub (lastCodomain U P Γ) C.fst

def first : SmallHom U P (source U P Γ) (middle U P Γ) :=
  SmallHom.sub U P (firstTerm U P Γ) C.fst

def second : SmallHom U P (middle U P Γ) (target U P Γ) :=
  C.castTm (SmallHom.type_sub U P (firstCodomain U P Γ) (lastCodomain U P Γ) C.fst) C.snd

def projection : C.Sub (context U P Γ) Γ :=
  C.comp (C.comp (C.comp (GenericArrow.base U Γ) C.fst) C.fst) C.fst

end GenericComposition

/-- Internal identity and composition laws for contextual functor data.
The witnesses live in the type theory, rather than in Lean's proof-irrelevant
equality. Each law is one term in its generic context; instances in other
contexts are obtained by substitution, not by an arbitrary family of choices.
The source does not require higher categorical coherence. -/
structure WildEndofunctor (U : Universe C) (P : FunctionTypes C)
    (I : IdentityTypes C) (Γ : C.Ctx) extends InternalFunctorData U P Γ where
  map_id : C.Tm (C.ext Γ (U.type Γ))
    (I.id (P.arr (U.el (obj C.fst (U.generic Γ))) (U.el (obj C.fst (U.generic Γ))))
      (map C.fst (U.generic Γ) (U.generic Γ) (P.identity (U.el (U.generic Γ))))
      (P.identity (U.el (obj C.fst (U.generic Γ)))))
  map_comp : C.Tm (GenericComposition.context U P Γ)
    (I.id (P.arr
      (U.el (obj (GenericComposition.projection U P Γ) (GenericComposition.source U P Γ)))
      (U.el (obj (GenericComposition.projection U P Γ) (GenericComposition.target U P Γ))))
      (map (GenericComposition.projection U P Γ)
        (GenericComposition.source U P Γ) (GenericComposition.target U P Γ)
        (P.compose (GenericComposition.second U P Γ) (GenericComposition.first U P Γ)))
      (P.compose
        (map (GenericComposition.projection U P Γ)
          (GenericComposition.middle U P Γ) (GenericComposition.target U P Γ)
          (GenericComposition.second U P Γ))
        (map (GenericComposition.projection U P Γ)
          (GenericComposition.source U P Γ) (GenericComposition.middle U P Γ)
          (GenericComposition.first U P Γ))))

/-- A source algebra in a fixed context. Its carrier and structure map are
internal terms; there is no initiality or recursive solver in this definition. -/
structure Algebra {U : Universe C} {P : FunctionTypes C} {I : IdentityTypes C}
    {Γ : C.Ctx} (F : WildEndofunctor U P I Γ) where
  carrier : U.Code Γ
  structureMap : SmallHom U P (F.obj C.id carrier) carrier

/-- A source coalgebra in a fixed context. -/
structure Coalgebra {U : Universe C} {P : FunctionTypes C} {I : IdentityTypes C}
    {Γ : C.Ctx} (F : WildEndofunctor U P I Γ) where
  carrier : U.Code Γ
  structureMap : SmallHom U P carrier (F.obj C.id carrier)

/-- A morphism of algebras carries an internal identity witness. -/
structure AlgebraHom {U : Universe C} {P : FunctionTypes C} {I : IdentityTypes C}
    {Γ : C.Ctx} {F : WildEndofunctor U P I Γ} (A B : Algebra F) where
  map : SmallHom U P A.carrier B.carrier
  commutes : C.Tm Γ (I.id (P.arr (U.el (F.obj C.id A.carrier)) (U.el B.carrier))
    (P.compose map A.structureMap)
    (P.compose B.structureMap (F.map C.id A.carrier B.carrier map)))

/-- A morphism of coalgebras carries the source's internal commuting-square witness. -/
structure CoalgebraHom {U : Universe C} {P : FunctionTypes C} {I : IdentityTypes C}
    {Γ : C.Ctx} {F : WildEndofunctor U P I Γ} (A B : Coalgebra F) where
  map : SmallHom U P A.carrier B.carrier
  commutes : C.Tm Γ (I.id (P.arr (U.el A.carrier) (U.el (F.obj C.id B.carrier)))
    (P.compose B.structureMap map)
    (P.compose (F.map C.id A.carrier B.carrier map) A.structureMap))

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_QuantifierMapsV2 -/

/-! # The source actions of size quantifiers on internal families of arrows -/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

variable {C : CwF.{u, v, w, t}} {U : Universe C} {I : IdentityTypes C}
    {Z : SizeRules C U I}

namespace ExistentialSizeQuantifier

variable (E : ExistentialSizeQuantifier C U I Z) (F : FunctionTypes C)

/-- The source operation `∃ f`, obtained by existential elimination and pairing. -/
def map {Γ : C.Ctx} (A B : U.Code (C.ext Γ (Z.type Γ)))
    (f : C.Tm (C.ext Γ (Z.type Γ)) (F.arr (U.el A) (U.el B))) :
    C.Tm Γ (F.arr (U.el (E.code A)) (U.el (E.code B))) := by
  let σ := @C.fst (C.ext Γ (Z.type Γ)) (U.el A)
  exact E.recursor F A (E.code B) (E.pairAt B σ (F.app (F.sub f σ) C.snd))

end ExistentialSizeQuantifier

namespace UniversalSizeQuantifier

variable (Q : UniversalSizeQuantifier C U I Z) (F : FunctionTypes C)
    (QS : UniversalSizeSubstitution U I Z Q)

/-- The source operation `∀ f`, formed by universal abstraction and application. -/
def map {Γ : C.Ctx} (A B : U.Code (C.ext Γ (Z.type Γ)))
    (f : C.Tm (C.ext Γ (Z.type Γ)) (F.arr (U.el A) (U.el B))) :
    C.Tm Γ (F.arr (U.el (Q.code A)) (U.el (Q.code B))) := by
  let σ := @C.fst Γ (U.el (Q.code A))
  have hin : C.tySub (U.el (Q.code A)) σ = U.el (Q.code (U.sub A (Z.lift σ))) :=
    (U.el_sub (Q.code A) σ).trans (congrArg U.el (QS.code_sub A σ))
  have hout : C.tySub (U.el (Q.code B)) σ = U.el (Q.code (U.sub B (Z.lift σ))) :=
    (U.el_sub (Q.code B) σ).trans (congrArg U.el (QS.code_sub B σ))
  let f' := SmallHom.sub U F f (Z.lift σ)
  exact F.lam (C.castTm hout.symm (Q.lam (F.app f' (Q.unlam (C.castTm hin C.snd)))))

end UniversalSizeQuantifier

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingSizedV2 -/

/-!
# Size-indexed internal morphisms and modal actions

Objects are contextual terms `Γ, i : Size ⊢ A(i) : U`. Morphisms are terms
of the small universal type `∀ i, A(i) → B(i)`. The modal actions below are the
literal existential-pair and universal-function operations of Section 3.2.
They never replace a size-indexed morphism by an arbitrary external family.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory.Sized

universe u v w t

variable {C : CwF.{u, v, w, t}} {U : Universe C} {I : IdentityTypes C}
    {P : DependentProducts C} {S : DependentSums C}
    (Z : SizeRules C U I) (F : FunctionTypes C) (K : SmallTypeConstructors C U P S I)
    (Q : UniversalSizeQuantifier C U I Z)

/-- The universe code for a size-indexed internal arrow. -/
def homCode {Γ : C.Ctx} (A B : U.Code (C.ext Γ (Z.type Γ))) : U.Code Γ :=
  Q.code (K.arrow A B)

/-- The source type of a size-indexed morphism. -/
abbrev Hom {Γ : C.Ctx} (A B : U.Code (C.ext Γ (Z.type Γ))) :=
  C.Tm Γ (U.el (homCode Z K Q A B))

/-- Evaluate a size-indexed morphism at the generic size. -/
def eval (FP : FunctionProductCompatibility F P) {Γ : C.Ctx}
    {A B : U.Code (C.ext Γ (Z.type Γ))} (f : Hom Z K Q A B) :
    C.Tm (C.ext Γ (Z.type Γ)) (F.arr (U.el A) (U.el B)) :=
  C.castTm (K.el_arrow FP A B) (Q.unlam f)

/-- Abstract a contextual arrow over sizes. -/
def ofAt (FP : FunctionProductCompatibility F P) {Γ : C.Ctx}
    {A B : U.Code (C.ext Γ (Z.type Γ))}
    (f : C.Tm (C.ext Γ (Z.type Γ)) (F.arr (U.el A) (U.el B))) : Hom Z K Q A B :=
  Q.lam (C.castTm (K.el_arrow FP A B).symm f)

theorem eval_ofAt (FP : FunctionProductCompatibility F P) {Γ : C.Ctx}
    {A B : U.Code (C.ext Γ (Z.type Γ))}
    (f : C.Tm (C.ext Γ (Z.type Γ)) (F.arr (U.el A) (U.el B))) :
    eval Z F K Q FP (ofAt Z F K Q FP f) = f := by
  unfold eval ofAt
  rw [Q.beta]
  exact eq_of_heq ((C.castTm_heq _ _).trans (C.castTm_heq _ _))

theorem ofAt_eval (FP : FunctionProductCompatibility F P) {Γ : C.Ctx}
    {A B : U.Code (C.ext Γ (Z.type Γ))} (f : Hom Z K Q A B) :
    ofAt Z F K Q FP (eval Z F K Q FP f) = f := by
  have h : C.castTm (K.el_arrow FP A B).symm
      (C.castTm (K.el_arrow FP A B) (Q.unlam f)) = Q.unlam f :=
    eq_of_heq ((C.castTm_heq _ _).trans (C.castTm_heq _ _))
  exact (congrArg Q.lam h).trans (Q.eta f)

/-- Identity in the source's category of size-indexed small types. -/
def identity (FP : FunctionProductCompatibility F P) {Γ : C.Ctx}
    (A : U.Code (C.ext Γ (Z.type Γ))) : Hom Z K Q A A :=
  ofAt Z F K Q FP (F.identity (U.el A))

/-- Composition of size-indexed internal arrows. -/
def compose (FP : FunctionProductCompatibility F P) {Γ : C.Ctx}
    {A B D : U.Code (C.ext Γ (Z.type Γ))} (g : Hom Z K Q B D) (f : Hom Z K Q A B) :
    Hom Z K Q A D :=
  ofAt Z F K Q FP (F.compose (eval Z F K Q FP g) (eval Z F K Q FP f))

/-- Substitution of size-indexed morphism types. -/
theorem homType_sub (KS : SmallTypeSubstitution U P S I K)
    (QS : UniversalSizeSubstitution U I Z Q)
    {Γ Δ : C.Ctx} (A B : U.Code (C.ext Γ (Z.type Γ))) (σ : C.Sub Δ Γ) :
    C.tySub (U.el (homCode Z K Q A B)) σ =
      U.el (homCode Z K Q (U.sub A (Z.lift σ)) (U.sub B (Z.lift σ))) :=
  (U.el_sub (Q.code (K.arrow A B)) σ).trans
    ((congrArg U.el (QS.code_sub (K.arrow A B) σ)).trans
      (congrArg (fun X => U.el (Q.code X)) (K.arrow_sub KS A B (Z.lift σ))))

/-- Substitution of a size-indexed arrow. -/
def sub (KS : SmallTypeSubstitution U P S I K) (QS : UniversalSizeSubstitution U I Z Q)
    {Γ Δ : C.Ctx} {A B : U.Code (C.ext Γ (Z.type Γ))} (f : Hom Z K Q A B)
    (σ : C.Sub Δ Γ) : Hom Z K Q (U.sub A (Z.lift σ)) (U.sub B (Z.lift σ)) :=
  C.castTm (homType_sub Z K Q KS QS A B σ) (C.tmSub f σ)

/-- The pointwise lift of a source functor on small types. -/
def liftObject {Γ : C.Ctx} (T : WildEndofunctor U F I Γ)
    (A : U.Code (C.ext Γ (Z.type Γ))) : U.Code (C.ext Γ (Z.type Γ)) :=
  T.obj C.fst A

/-- The pointwise lift of its internal morphism action. -/
def liftMap (FP : FunctionProductCompatibility F P) {Γ : C.Ctx}
    (T : WildEndofunctor U F I Γ) {A B : U.Code (C.ext Γ (Z.type Γ))}
    (f : Hom Z K Q A B) : Hom Z K Q (liftObject Z F T A) (liftObject Z F T B) :=
  ofAt Z F K Q FP (T.map C.fst A B (eval Z F K Q FP f))

/-- The source's bounded existential action on size-indexed morphisms. -/
def diamondMap (FP : FunctionProductCompatibility F P)
    (E : ExistentialSizeQuantifier C U I Z) {Γ : C.Ctx}
    {A B : U.Code (C.ext Γ (Z.type Γ))} (f : Hom Z K Q A B) :
    Hom Z K Q (Z.diamond K E A) (Z.diamond K E B) :=
  ofAt Z F K Q FP (E.map F
    (K.sigma Z.boundCode (U.sub (U.sub A Z.inner) C.fst))
    (K.sigma Z.boundCode (U.sub (U.sub B Z.inner) C.fst))
    (K.productMap F Z.boundCode (U.sub A Z.inner) (U.sub B Z.inner)
      (SmallHom.sub U F (eval Z F K Q FP f) Z.inner)))

/-- The source's bounded universal action on size-indexed morphisms. -/
def boxMap (FP : FunctionProductCompatibility F P)
    (QS : UniversalSizeSubstitution U I Z Q) {Γ : C.Ctx}
    {A B : U.Code (C.ext Γ (Z.type Γ))} (f : Hom Z K Q A B) :
    Hom Z K Q (Z.box K Q A) (Z.box K Q B) :=
  ofAt Z F K Q FP (Q.map F QS
    (K.arrow Z.boundCode (U.sub A Z.inner))
    (K.arrow Z.boundCode (U.sub B Z.inner))
    (K.postcompose F FP Z.boundCode (U.sub A Z.inner) (U.sub B Z.inner)
      (SmallHom.sub U F (eval Z F K Q FP f) Z.inner)))

/-- A source size-indexed algebra for `T[◇ -]`. -/
structure Algebra (E : ExistentialSizeQuantifier C U I Z)
    {Γ : C.Ctx} (T : WildEndofunctor U F I Γ) where
  carrier : U.Code (C.ext Γ (Z.type Γ))
  structureMap : Hom Z K Q (liftObject Z F T (Z.diamond K E carrier)) carrier

/-- A source size-indexed coalgebra for `T[□ -]`. -/
structure Coalgebra {Γ : C.Ctx} (T : WildEndofunctor U F I Γ) where
  carrier : U.Code (C.ext Γ (Z.type Γ))
  structureMap : Hom Z K Q carrier (liftObject Z F T (Z.box K Q carrier))

/-- A size-indexed algebra morphism with the source's internal path witness. -/
structure AlgebraHom (FP : FunctionProductCompatibility F P)
    (E : ExistentialSizeQuantifier C U I Z) {Γ : C.Ctx} {T : WildEndofunctor U F I Γ}
    (A B : Algebra Z F K Q E T) where
  map : Hom Z K Q A.carrier B.carrier
  commutes : C.Tm Γ (I.id
    (U.el (homCode Z K Q (liftObject Z F T (Z.diamond K E A.carrier)) B.carrier))
    (compose Z F K Q FP map A.structureMap)
    (compose Z F K Q FP B.structureMap
      (liftMap Z F K Q FP T (diamondMap Z F K Q FP E map))))

/-- A size-indexed coalgebra morphism with the source's internal path witness. -/
structure CoalgebraHom (FP : FunctionProductCompatibility F P)
    (QS : UniversalSizeSubstitution U I Z Q) {Γ : C.Ctx} {T : WildEndofunctor U F I Γ}
    (A B : Coalgebra Z F K Q T) where
  map : Hom Z K Q A.carrier B.carrier
  commutes : C.Tm Γ (I.id
    (U.el (homCode Z K Q A.carrier (liftObject Z F T (Z.box K Q B.carrier))))
    (compose Z F K Q FP B.structureMap map)
    (compose Z F K Q FP (liftMap Z F K Q FP T (boxMap Z F K Q FP QS map)) A.structureMap))

end LaarakkerOttenVanDenBerg2026.V2.Theory.Sized

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingFamiliesV2 -/

/-! Internal quantification over small families indexed by the large size type. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

variable {C : CwF.{u, v, w, t}} {U : Universe C}

namespace InternalFunctorData

variable {F : FunctionTypes C} {Γ : C.Ctx} (T : InternalFunctorData U F Γ)

/-- Reindex the one internal functor term into a different context. -/
def reindex {Δ : C.Ctx} (σ : C.Sub Δ Γ) : InternalFunctorData U F Δ where
  obj τ A := T.obj (C.comp σ τ) A
  obj_sub τ A υ := by simpa only [C.assoc] using T.obj_sub (C.comp σ τ) A υ
  map τ A B f := T.map (C.comp σ τ) A B f
  map_sub τ A B f υ := (T.map_sub (C.comp σ τ) A B f υ).trans
    (T.map_congr (C.assoc σ τ υ) rfl rfl HEq.rfl)

end InternalFunctorData

namespace DependentProducts

variable (P : DependentProducts C)

/-- Product application after substitution, with an equal presentation of the domain. -/
theorem unlam_sub_as {Γ Δ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (f : C.Tm Γ (P.pi A B)) (σ : C.Sub Δ Γ) (A' : C.Ty Δ)
    (h : C.tySub A σ = A') :
    P.unlam (C.castTm (P.pi_sub_as A B σ A' h) (C.tmSub f σ)) =
      C.tmSub (P.unlam f) (C.liftAs σ A A' h) := by
  subst A'
  exact P.unlam_sub f σ

theorem unlam_congr {Γ : C.Ctx} {A : C.Ty Γ} {B B' : C.Ty (C.ext Γ A)}
    (hB : B = B') {f : C.Tm Γ (P.pi A B)} {g : C.Tm Γ (P.pi A B')}
    (h : HEq f g) : HEq (P.unlam f) (P.unlam g) := by
  subst B'
  cases h
  rfl

end DependentProducts

namespace SizeRules

variable {I : IdentityTypes C} (Z : SizeRules C U I) (P : DependentProducts C)

/-- Product application commutes with substitution under the source's size binder. -/
theorem unlam_sub {Γ Δ : C.Ctx} {A : C.Ty (C.ext Γ (Z.type Γ))}
    (f : C.Tm Γ (P.pi (Z.type Γ) A)) (σ : C.Sub Δ Γ) :
    P.unlam (C.castTm (Z.pi_sub P A σ) (C.tmSub f σ)) =
      C.tmSub (P.unlam f) (Z.lift σ) := by
  have h := P.unlam_sub_as f σ (Z.type Δ) (Z.type_sub σ)
  have hL := Z.liftAs_eq_lift σ
  have ht (τ υ : C.Sub (C.ext Δ (Z.type Δ)) (C.ext Γ (Z.type Γ))) (e : τ = υ) :
      HEq (C.tmSub (P.unlam f) τ) (C.tmSub (P.unlam f) υ) := by
    cases e
    rfl
  apply eq_of_heq
  exact (P.unlam_congr (congrArg (C.tySub A) hL.symm)
    ((C.castTm_heq _ _).trans (C.castTm_heq _ _).symm)).trans
      ((heq_of_eq h).trans (ht _ _ hL))

end SizeRules

namespace SizedFamily

variable {I : IdentityTypes C} (Z : SizeRules C U I) (P : DependentProducts C)

/-- The large internal type `Π i : Size, U` of small size-indexed families. -/
def type (Γ : C.Ctx) : C.Ty Γ := P.pi (Z.type Γ) (U.type (C.ext Γ (Z.type Γ)))

theorem type_sub {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) :
    C.tySub (type Z P Γ) σ = type Z P Δ := by
  rw [type, Z.pi_sub, U.type_sub]
  rfl

/-- The context containing a generic size-indexed small family. -/
abbrev context (Γ : C.Ctx) : C.Ctx := C.ext Γ (type Z P Γ)

/-- Evaluate the generic family at the generic size. -/
def generic {Γ : C.Ctx} : U.Code (C.ext (context Z P Γ) (Z.type (context Z P Γ))) :=
  P.unlam (C.castTm (type_sub Z P C.fst) C.snd)

/-- Bind an actual contextual family in the generic-family context. -/
def extend {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : U.Code (C.ext Δ (Z.type Δ))) : C.Sub Δ (context Z P Γ) :=
  C.pair σ (C.castTm (type_sub Z P σ).symm (P.lam A))

theorem extend_fst {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : U.Code (C.ext Δ (Z.type Δ))) :
    C.comp C.fst (extend Z P σ A) = σ := C.pair_fst _ _

/-- Specializing the generic family recovers the supplied family pointwise. -/
theorem generic_sub_extend {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : U.Code (C.ext Δ (Z.type Δ))) :
    U.sub (generic Z P) (Z.lift (extend Z P σ A)) = A := by
  let τ := extend Z P σ A
  let f : C.Tm (context Z P Γ) (type Z P (context Z P Γ)) :=
    C.castTm (type_sub Z P C.fst) C.snd
  have hf : HEq (C.tmSub f τ) (P.lam A) :=
    (C.tmSub_heq (type_sub Z P C.fst).symm (C.castTm_heq _ _) τ).trans
      ((C.pair_snd _ _).trans (C.castTm_heq _ _))
  apply eq_of_heq
  exact (C.castTm_heq _ _).trans
    ((heq_of_eq (Z.unlam_sub P f τ)).symm.trans
      ((P.unlam_congr (U.type_sub (Z.lift τ))
        ((C.castTm_heq _ _).trans hf)).trans (heq_of_eq (P.beta A))))

end SizedFamily

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingSizedInitialityV2 -/

/-!
# Internal hom types for size-indexed algebras

Algebras and coalgebras can be substituted into any context over the parameters
of their functor. Their hom types are actual internal dependent sums of a
size-indexed arrow and its commuting-square path.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory.Sized

universe u v w t

variable {C : CwF.{u, v, w, t}} (T : CoreTheory C) {Γ : C.Ctx}
    (F : WildEndofunctor T.univ T.functions T.identities Γ)

/-- The pointwise object action over a substitution into the functor's parameters. -/
def liftObjectOver {Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : T.univ.Code (C.ext Δ (T.size.type Δ))) : T.univ.Code (C.ext Δ (T.size.type Δ)) :=
  F.obj (C.comp σ C.fst) A

/-- The corresponding action on internal size-indexed arrows. -/
def liftMapOver {Δ : C.Ctx} (σ : C.Sub Δ Γ)
    {A B : T.univ.Code (C.ext Δ (T.size.type Δ))}
    (f : Hom T.size T.small T.all A B) :
    Hom T.size T.small T.all (liftObjectOver T F σ A) (liftObjectOver T F σ B) :=
  ofAt T.size T.functions T.small T.all T.functionProducts
    (F.map (C.comp σ C.fst) A B (eval T.size T.functions T.small T.all T.functionProducts f))

theorem liftObjectOver_sub {Δ Θ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : T.univ.Code (C.ext Δ (T.size.type Δ))) (τ : C.Sub Θ Δ) :
    T.univ.sub (liftObjectOver T F σ A) (T.size.lift τ) =
      liftObjectOver T F (C.comp σ τ) (T.univ.sub A (T.size.lift τ)) := by
  rw [liftObjectOver, F.obj_sub]
  have h : C.comp (C.comp σ C.fst) (T.size.lift τ) = C.comp (C.comp σ τ) C.fst := by
    rw [C.assoc, T.size.lift_fst, ← C.assoc]
  exact congrArg (fun ρ => F.obj ρ (T.univ.sub A (T.size.lift τ))) h

theorem liftDiamond_sub {Δ Θ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : T.univ.Code (C.ext Δ (T.size.type Δ))) (τ : C.Sub Θ Δ) :
    T.univ.sub (liftObjectOver T F σ (T.size.diamond T.small T.ex A)) (T.size.lift τ) =
      liftObjectOver T F (C.comp σ τ) (T.size.diamond T.small T.ex (T.univ.sub A (T.size.lift τ))) :=
  (liftObjectOver_sub T F σ _ τ).trans
    (congrArg (liftObjectOver T F (C.comp σ τ))
      (T.size.diamond_sub T.small T.ex T.sizeSubstitution T.smallSubstitution T.exSubstitution A τ))

theorem liftBox_sub {Δ Θ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : T.univ.Code (C.ext Δ (T.size.type Δ))) (τ : C.Sub Θ Δ) :
    T.univ.sub (liftObjectOver T F σ (T.size.box T.small T.all A)) (T.size.lift τ) =
      liftObjectOver T F (C.comp σ τ) (T.size.box T.small T.all (T.univ.sub A (T.size.lift τ))) :=
  (liftObjectOver_sub T F σ _ τ).trans
    (congrArg (liftObjectOver T F (C.comp σ τ))
      (T.size.box_sub T.small T.all T.sizeSubstitution T.smallSubstitution T.allSubstitution A τ))

/-- A size-indexed algebra in a context over the parameters of the functor. -/
structure AlgebraOver {Δ : C.Ctx} (σ : C.Sub Δ Γ) where
  carrier : T.univ.Code (C.ext Δ (T.size.type Δ))
  structureMap : Hom T.size T.small T.all
    (liftObjectOver T F σ (T.size.diamond T.small T.ex carrier)) carrier

/-- A size-indexed coalgebra in a context over the functor's parameters. -/
structure CoalgebraOver {Δ : C.Ctx} (σ : C.Sub Δ Γ) where
  carrier : T.univ.Code (C.ext Δ (T.size.type Δ))
  structureMap : Hom T.size T.small T.all carrier
    (liftObjectOver T F σ (T.size.box T.small T.all carrier))

namespace AlgebraOver

variable {T F}

/-- Substitute a size-indexed algebra. -/
def sub {Δ Θ : C.Ctx} {σ : C.Sub Δ Γ} (A : AlgebraOver T F σ) (τ : C.Sub Θ Δ) :
    AlgebraOver T F (C.comp σ τ) where
  carrier := T.univ.sub A.carrier (T.size.lift τ)
  structureMap := C.castTm
    (congrArg (fun X => T.univ.el (homCode T.size T.small T.all X
      (T.univ.sub A.carrier (T.size.lift τ)))) (liftDiamond_sub T F σ A.carrier τ))
    (Sized.sub T.size T.small T.all T.smallSubstitution T.allSubstitution A.structureMap τ)

/-- The full internal type of size-indexed algebra morphisms. -/
def homType {Δ : C.Ctx} {σ : C.Sub Δ Γ} (A B : AlgebraOver T F σ) : C.Ty Δ :=
  let H := T.univ.el (homCode T.size T.small T.all A.carrier B.carrier)
  let π := @C.fst Δ H
  let A' := A.sub π
  let B' := B.sub π
  let h := C.castTm (homType_sub T.size T.small T.all T.smallSubstitution T.allSubstitution
    A.carrier B.carrier π) C.snd
  T.sums.sigma H
    (T.identities.id
      (T.univ.el (homCode T.size T.small T.all
        (liftObjectOver T F (C.comp σ π) (T.size.diamond T.small T.ex A'.carrier)) B'.carrier))
      (compose T.size T.functions T.small T.all T.functionProducts h A'.structureMap)
      (compose T.size T.functions T.small T.all T.functionProducts B'.structureMap
        (liftMapOver T F (C.comp σ π)
          (diamondMap T.size T.functions T.small T.all T.functionProducts T.ex h))))

end AlgebraOver

namespace CoalgebraOver

variable {T F}

/-- Substitute a size-indexed coalgebra. -/
def sub {Δ Θ : C.Ctx} {σ : C.Sub Δ Γ} (A : CoalgebraOver T F σ) (τ : C.Sub Θ Δ) :
    CoalgebraOver T F (C.comp σ τ) where
  carrier := T.univ.sub A.carrier (T.size.lift τ)
  structureMap := C.castTm
    (congrArg (fun X => T.univ.el (homCode T.size T.small T.all
      (T.univ.sub A.carrier (T.size.lift τ)) X)) (liftBox_sub T F σ A.carrier τ))
    (Sized.sub T.size T.small T.all T.smallSubstitution T.allSubstitution A.structureMap τ)

/-- The full internal type of size-indexed coalgebra morphisms. -/
def homType {Δ : C.Ctx} {σ : C.Sub Δ Γ} (A B : CoalgebraOver T F σ) : C.Ty Δ :=
  let H := T.univ.el (homCode T.size T.small T.all A.carrier B.carrier)
  let π := @C.fst Δ H
  let A' := A.sub π
  let B' := B.sub π
  let h := C.castTm (homType_sub T.size T.small T.all T.smallSubstitution T.allSubstitution
    A.carrier B.carrier π) C.snd
  T.sums.sigma H
    (T.identities.id
      (T.univ.el (homCode T.size T.small T.all A'.carrier
        (liftObjectOver T F (C.comp σ π) (T.size.box T.small T.all B'.carrier))))
      (compose T.size T.functions T.small T.all T.functionProducts B'.structureMap h)
      (compose T.size T.functions T.small T.all T.functionProducts
        (liftMapOver T F (C.comp σ π)
          (boxMap T.size T.functions T.small T.all T.functionProducts T.allSubstitution h))
        A'.structureMap))

end CoalgebraOver

/-- The structure-map type over the generic size-indexed family. -/
def algebraStructureType : C.Ty (SizedFamily.context T.size T.products Γ) :=
  T.univ.el (homCode T.size T.small T.all
    (liftObjectOver T F C.fst (T.size.diamond T.small T.ex (SizedFamily.generic T.size T.products)))
    (SizedFamily.generic T.size T.products))

/-- The source's generic sized algebra in a context containing its family and
its structure map. -/
def genericAlgebra : AlgebraOver T F
    (C.comp (@C.fst Γ (SizedFamily.type T.size T.products Γ))
      (@C.fst (SizedFamily.context T.size T.products Γ) (algebraStructureType T F))) where
  carrier := T.univ.sub (SizedFamily.generic T.size T.products) (T.size.lift C.fst)
  structureMap := C.castTm
    (congrArg (fun X => T.univ.el (homCode T.size T.small T.all X
      (T.univ.sub (SizedFamily.generic T.size T.products) (T.size.lift C.fst))))
      (liftDiamond_sub T F C.fst (SizedFamily.generic T.size T.products) C.fst))
    (C.castTm (homType_sub T.size T.small T.all T.smallSubstitution T.allSubstitution
      (liftObjectOver T F C.fst (T.size.diamond T.small T.ex (SizedFamily.generic T.size T.products)))
      (SizedFamily.generic T.size T.products) C.fst) C.snd)

/-- The structure-map type over the generic size-indexed coalgebra family. -/
def coalgebraStructureType : C.Ty (SizedFamily.context T.size T.products Γ) :=
  T.univ.el (homCode T.size T.small T.all (SizedFamily.generic T.size T.products)
    (liftObjectOver T F C.fst (T.size.box T.small T.all (SizedFamily.generic T.size T.products))))

/-- The generic sized coalgebra, including its internal structure map. -/
def genericCoalgebra : CoalgebraOver T F
    (C.comp (@C.fst Γ (SizedFamily.type T.size T.products Γ))
      (@C.fst (SizedFamily.context T.size T.products Γ) (coalgebraStructureType T F))) where
  carrier := T.univ.sub (SizedFamily.generic T.size T.products) (T.size.lift C.fst)
  structureMap := C.castTm
    (congrArg (fun X => T.univ.el (homCode T.size T.small T.all
      (T.univ.sub (SizedFamily.generic T.size T.products) (T.size.lift C.fst)) X))
      (liftBox_sub T F C.fst (SizedFamily.generic T.size T.products) C.fst))
    (C.castTm (homType_sub T.size T.small T.all T.smallSubstitution T.allSubstitution
      (SizedFamily.generic T.size T.products)
      (liftObjectOver T F C.fst (T.size.box T.small T.all (SizedFamily.generic T.size T.products)))
      C.fst) C.snd)

namespace AlgebraOver

variable {T F}

/-- The full source initiality type for a sized algebra. It quantifies internally
over `B : Size → U` and `k : F[◇ B] →ⁱ B`, then takes internal contractibility
of the complete algebra-morphism type. -/
def initialityType (A : AlgebraOver T F C.id) : C.Ty Γ :=
  T.products.pi (SizedFamily.type T.size T.products Γ)
    (T.products.pi (algebraStructureType T F)
      (contractible T.products T.sums T.identities
        (homType (C.id_comp (C.comp C.fst C.fst) ▸ A.sub (C.comp C.fst C.fst))
          (genericAlgebra T F))))

/-- An initiality witness is an internal term. -/
abbrev IsInitial (A : AlgebraOver T F C.id) := C.Tm Γ A.initialityType

end AlgebraOver

namespace CoalgebraOver

variable {T F}

/-- The full source terminality type for a sized coalgebra. -/
def terminalityType (A : CoalgebraOver T F C.id) : C.Ty Γ :=
  T.products.pi (SizedFamily.type T.size T.products Γ)
    (T.products.pi (coalgebraStructureType T F)
      (contractible T.products T.sums T.identities
        (homType (genericCoalgebra T F)
          (C.id_comp (C.comp C.fst C.fst) ▸ A.sub (C.comp C.fst C.fst)))))

/-- A terminality witness is an internal term. -/
abbrev IsTerminal (A : CoalgebraOver T F C.id) := C.Tm Γ A.terminalityType

end CoalgebraOver

end LaarakkerOttenVanDenBerg2026.V2.Theory.Sized

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingInitialityV2 -/

/-!
# Internal algebra morphisms and universal-property types

The initiality and terminality conditions of Section 3 and Appendix B quantify
internally over a small carrier and its structure map. Their morphism types are
dependent sums of an arrow and an internal identity witness, and contractibility
is the internal `Σ center, Π point, center = point` type. In particular these
definitions do not replace source contractibility by external unique existence.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

variable {C : CwF.{u, v, w, t}} {U : Universe C} {P : FunctionTypes C}
    {I : IdentityTypes C} {Γ : C.Ctx} (F : WildEndofunctor U P I Γ)

/-- An algebra in a context over the parameter context of the functor. -/
structure AlgebraOver {Δ : C.Ctx} (σ : C.Sub Δ Γ) where
  carrier : U.Code Δ
  structureMap : SmallHom U P (F.obj σ carrier) carrier

/-- A coalgebra in a context over the parameter context of the functor. -/
structure CoalgebraOver {Δ : C.Ctx} (σ : C.Sub Δ Γ) where
  carrier : U.Code Δ
  structureMap : SmallHom U P carrier (F.obj σ carrier)

namespace AlgebraOver

variable {F}

/-- Substitute an algebra, using the functor's proved object-operation coherence. -/
def sub {Δ Θ : C.Ctx} {σ : C.Sub Δ Γ} (A : AlgebraOver F σ) (τ : C.Sub Θ Δ) :
    AlgebraOver F (C.comp σ τ) where
  carrier := U.sub A.carrier τ
  structureMap := C.castTm
    (congrArg (fun X => P.arr (U.el X) (U.el (U.sub A.carrier τ))) (F.obj_sub σ A.carrier τ))
    (SmallHom.sub U P A.structureMap τ)

/-- The type of source algebra morphisms: an internal arrow together with
the internal identity expressing its commuting square. -/
def homType (S : DependentSums C) {Δ : C.Ctx} {σ : C.Sub Δ Γ}
    (A B : AlgebraOver F σ) : C.Ty Δ :=
  S.sigma (P.arr (U.el A.carrier) (U.el B.carrier))
    (I.id (P.arr (U.el (F.obj (C.comp σ C.fst) (U.sub A.carrier C.fst)))
        (U.el (U.sub B.carrier C.fst)))
      (P.compose
        (C.castTm (SmallHom.type_sub U P A.carrier B.carrier C.fst) C.snd)
        (A.sub C.fst).structureMap)
      (P.compose (B.sub C.fst).structureMap
        (F.map (C.comp σ C.fst) (U.sub A.carrier C.fst) (U.sub B.carrier C.fst)
          (C.castTm (SmallHom.type_sub U P A.carrier B.carrier C.fst) C.snd))))

end AlgebraOver

namespace CoalgebraOver

variable {F}

/-- Substitution of a coalgebra. -/
def sub {Δ Θ : C.Ctx} {σ : C.Sub Δ Γ} (A : CoalgebraOver F σ) (τ : C.Sub Θ Δ) :
    CoalgebraOver F (C.comp σ τ) where
  carrier := U.sub A.carrier τ
  structureMap := C.castTm
    (congrArg (fun X => P.arr (U.el (U.sub A.carrier τ)) (U.el X)) (F.obj_sub σ A.carrier τ))
    (SmallHom.sub U P A.structureMap τ)

/-- The source coalgebra-morphism type with its internal commuting-square witness. -/
def homType (S : DependentSums C) {Δ : C.Ctx} {σ : C.Sub Δ Γ}
    (A B : CoalgebraOver F σ) : C.Ty Δ :=
  S.sigma (P.arr (U.el A.carrier) (U.el B.carrier))
    (I.id (P.arr (U.el (U.sub A.carrier C.fst))
        (U.el (F.obj (C.comp σ C.fst) (U.sub B.carrier C.fst))))
      (P.compose (B.sub C.fst).structureMap
        (C.castTm (SmallHom.type_sub U P A.carrier B.carrier C.fst) C.snd))
      (P.compose
        (F.map (C.comp σ C.fst) (U.sub A.carrier C.fst) (U.sub B.carrier C.fst)
          (C.castTm (SmallHom.type_sub U P A.carrier B.carrier C.fst) C.snd))
        (A.sub C.fst).structureMap))

end CoalgebraOver

namespace WildEndofunctor

/-- The structure-map type for the generic small algebra carrier. -/
def algebraStructureType : C.Ty (C.ext Γ (U.type Γ)) :=
  P.arr (U.el (F.obj C.fst (U.generic Γ))) (U.el (U.generic Γ))

/-- The generic small algebra in `Γ, B : U, k : F B → B`. -/
def genericAlgebra : AlgebraOver F
    (C.comp (@C.fst Γ (U.type Γ)) (@C.fst (C.ext Γ (U.type Γ)) F.algebraStructureType)) where
  carrier := U.sub (U.generic Γ) C.fst
  structureMap := C.castTm
    (congrArg (fun X => P.arr (U.el X) (U.el (U.sub (U.generic Γ) C.fst)))
      (F.obj_sub C.fst (U.generic Γ) C.fst))
    (C.castTm (SmallHom.type_sub U P (F.obj C.fst (U.generic Γ)) (U.generic Γ) C.fst) C.snd)

/-- The structure-map type for the generic small coalgebra carrier. -/
def coalgebraStructureType : C.Ty (C.ext Γ (U.type Γ)) :=
  P.arr (U.el (U.generic Γ)) (U.el (F.obj C.fst (U.generic Γ)))

/-- The generic small coalgebra in `Γ, B : U, k : B → F B`. -/
def genericCoalgebra : CoalgebraOver F
    (C.comp (@C.fst Γ (U.type Γ)) (@C.fst (C.ext Γ (U.type Γ)) F.coalgebraStructureType)) where
  carrier := U.sub (U.generic Γ) C.fst
  structureMap := C.castTm
    (congrArg (fun X => P.arr (U.el (U.sub (U.generic Γ) C.fst)) (U.el X))
      (F.obj_sub C.fst (U.generic Γ) C.fst))
    (C.castTm (SmallHom.type_sub U P (U.generic Γ) (F.obj C.fst (U.generic Γ)) C.fst) C.snd)

end WildEndofunctor

namespace Algebra

variable {F}

/-- View a fixed-context algebra as an algebra over the identity substitution. -/
def over (A : Algebra F) : AlgebraOver F C.id := ⟨A.carrier, A.structureMap⟩

/-- The full source initiality type, with internal quantification over carriers,
structure maps, and the complete algebra-morphism type. -/
def initialityType (Q : DependentProducts C) (S : DependentSums C) (A : Algebra F) : C.Ty Γ :=
  Q.pi (U.type Γ) (Q.pi F.algebraStructureType
    (contractible Q S I
      (AlgebraOver.homType S
        (C.id_comp (C.comp C.fst C.fst) ▸ A.over.sub (C.comp C.fst C.fst))
        F.genericAlgebra)))

/-- A witness of initiality is a term of the source initiality type. -/
abbrev IsInitial (Q : DependentProducts C) (S : DependentSums C) (A : Algebra F) :=
  C.Tm Γ (A.initialityType Q S)

end Algebra

namespace Coalgebra

variable {F}

/-- View a fixed-context coalgebra over the identity substitution. -/
def over (A : Coalgebra F) : CoalgebraOver F C.id := ⟨A.carrier, A.structureMap⟩

/-- The full source terminality type, with internal quantification and internal
contractibility of the coalgebra-morphism type. -/
def terminalityType (Q : DependentProducts C) (S : DependentSums C) (A : Coalgebra F) : C.Ty Γ :=
  Q.pi (U.type Γ) (Q.pi F.coalgebraStructureType
    (contractible Q S I
      (CoalgebraOver.homType S F.genericCoalgebra
        (C.id_comp (C.comp C.fst C.fst) ▸ A.over.sub (C.comp C.fst C.fst)))))

/-- A witness of terminality is a term of the source terminality type. -/
abbrev IsTerminal (Q : DependentProducts C) (S : DependentSums C) (A : Coalgebra F) :=
  C.Tm Γ (A.terminalityType Q S)

end Coalgebra

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_WeakCommutationV2 -/

/-!
# The canonical maps for weak commutation with size quantifiers

The maps are constructed from the functor action and the source quantifier
rules. Their equivalence types therefore refer to these precise arrows.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

variable {C : CwF.{u, v, w, t}} {U : Universe C} {I : IdentityTypes C}
    {P : DependentProducts C} {S : DependentSums C}

namespace UniversalSizeQuantifier

variable {Z : SizeRules C U I} (Q : UniversalSizeQuantifier C U I Z)
    (QS : UniversalSizeSubstitution U I Z Q) (F : FunctionTypes C)

/-- Evaluate an arrow into a universal size type at the generic size. -/
def arrowAtSize {Γ : C.Ctx} {D : U.Code Γ}
    {B : U.Code (C.ext Γ (Z.type Γ))} (f : SmallHom U F D (Q.code B)) :
    SmallHom U F (U.sub D C.fst) B := by
  let π := @C.fst Γ (U.el D)
  have hin : C.tySub (U.el (Q.code B)) π = U.el (Q.code (U.sub B (Z.lift π))) :=
    (U.el_sub _ _).trans (congrArg U.el (QS.code_sub B π))
  let body := Q.unlam (C.castTm hin (F.app (F.sub f π) C.snd))
  have hout : C.tySub (U.el (U.sub B (Z.lift π))) (Parametricity.interchange Z D) =
      C.tySub (U.el B) C.fst := by
    calc
      _ = C.tySub (C.tySub (U.el B) (Z.lift π))
          (Parametricity.interchange Z D) :=
        congrArg (fun X => C.tySub X (Parametricity.interchange Z D))
          (U.el_sub B (Z.lift π)).symm
      _ = C.tySub (U.el B)
          (C.comp (Z.lift π) (Parametricity.interchange Z D)) := C.tySub_comp _ _ _
      _ = _ := by
        change C.tySub (U.el B)
          (C.comp (Parametricity.interchangeSizeMap Z D)
            (Parametricity.interchange Z D)) = _
        rw [Parametricity.interchangeSizeMap_interchange]
  exact F.lam (C.castTm hout (C.tmSub body (Parametricity.interchange Z D)))

/-- Abstract a uniform family of arrows with a size-independent domain. -/
def arrowFromSize {Γ : C.Ctx} {D : U.Code Γ}
    {B : U.Code (C.ext Γ (Z.type Γ))}
    (f : SmallHom U F (U.sub D C.fst) B) : SmallHom U F D (Q.code B) := by
  let π := @C.fst Γ (U.el D)
  let swap := Parametricity.interchangeInverse Z D
  let body := F.app (F.sub f C.fst) C.snd
  have hout : C.tySub (C.tySub (U.el B) C.fst) swap =
      U.el (U.sub B (Z.lift π)) := by
    rw [C.tySub_comp, Parametricity.interchangeInverse_fst]
    exact U.el_sub _ _
  have hcode : C.tySub (U.el (Q.code B)) π =
      U.el (Q.code (U.sub B (Z.lift π))) :=
    (U.el_sub _ _).trans (congrArg U.el (QS.code_sub B π))
  exact F.lam (C.castTm hcode.symm (Q.lam (C.castTm hout (C.tmSub body swap))))

end UniversalSizeQuantifier

namespace WeakCommutation

variable (Z : SizeRules C U I) (F : FunctionTypes C)
    (K : SmallTypeConstructors C U P S I)

/-- The exact canonical existential map `⟨i,x⟩ ↦ T (φ i) x`. -/
def existsCan (E : ExistentialSizeQuantifier C U I Z)
    {Γ : C.Ctx} (T : InternalFunctorData U F Γ)
    (A : U.Code (C.ext Γ (Z.type Γ))) :
    SmallHom U F (E.code (T.obj C.fst (Z.diamond K E A)))
      (T.obj C.id (E.code A)) := by
  let D := T.obj C.fst (Z.diamond K E A)
  let B := T.obj C.id (E.code A)
  let π := @C.fst Γ (Z.type Γ)
  let ρ := @C.fst (C.ext Γ (Z.type Γ)) (U.el D)
  let f := T.map π (Z.diamond K E A) (U.sub (E.code A) π)
    (Parametricity.boundedToExists Z F K E A)
  have hB : U.sub B π = T.obj π (U.sub (E.code A) π) := by
    dsimp [B]
    rw [T.obj_sub, C.id_comp]
  have hout : C.tySub (U.el (T.obj π (U.sub (E.code A) π))) ρ =
      C.tySub (U.el B) (C.comp π ρ) := by
    rw [← hB]
    exact (congrArg (fun X => C.tySub X ρ) (U.el_sub B π).symm).trans
      (C.tySub_comp _ _ _)
  exact E.recursor F D B (C.castTm hout (F.app (F.sub f ρ) C.snd))

/-- Restriction `ψ i : (∀ j, A j) → (∀ j < i, A j)` at the generic size. -/
def allRestriction (Q : UniversalSizeQuantifier C U I Z)
    (ZS : SizeSubstitution U I Z) (KS : SmallTypeSubstitution U P S I K)
    (QS : UniversalSizeSubstitution U I Z Q)
    {Γ : C.Ctx} (A : U.Code (C.ext Γ (Z.type Γ))) :
    SmallHom U F (U.sub (Q.code A) C.fst) (Z.box K Q A) :=
  Q.arrowAtSize QS F (Parametricity.allLtMap Z F K Q ZS KS QS A)

/-- The exact canonical universal map `x ↦ λ i, T (ψ i) x`. -/
def allCan (Q : UniversalSizeQuantifier C U I Z)
    (ZS : SizeSubstitution U I Z) (KS : SmallTypeSubstitution U P S I K)
    (QS : UniversalSizeSubstitution U I Z Q)
    {Γ : C.Ctx} (T : InternalFunctorData U F Γ)
    (A : U.Code (C.ext Γ (Z.type Γ))) :
    SmallHom U F (T.obj C.id (Q.code A)) (Q.code (T.obj C.fst (Z.box K Q A))) := by
  let f := T.map C.fst (U.sub (Q.code A) C.fst) (Z.box K Q A)
    (allRestriction Z F K Q ZS KS QS A)
  have h : U.sub (T.obj C.id (Q.code A)) (@C.fst Γ (Z.type Γ)) =
      T.obj C.fst (U.sub (Q.code A) C.fst) := by
    rw [T.obj_sub, C.id_comp]
  exact Q.arrowFromSize QS F (C.castTm (congrArg (fun D => F.arr (U.el D) _) h).symm f)

/-- The source hypothesis `Π A : Size → U, isEquiv (can_A)` for existentials. -/
def existsType (J : IdentityElimination C I) (E : ExistentialSizeQuantifier C U I Z)
    {Γ : C.Ctx} (T : InternalFunctorData U F Γ) : C.Ty Γ :=
  P.pi (SizedFamily.type Z P Γ)
    (InternalEquivalence.isEquiv F P I S J
      (existsCan Z F K E (T.reindex C.fst) (SizedFamily.generic Z P)))

/-- The source hypothesis `Π A : Size → U, isEquiv (can_A)` for universals. -/
def allType (J : IdentityElimination C I) (Q : UniversalSizeQuantifier C U I Z)
    (ZS : SizeSubstitution U I Z) (KS : SmallTypeSubstitution U P S I K)
    (QS : UniversalSizeSubstitution U I Z Q)
    {Γ : C.Ctx} (T : InternalFunctorData U F Γ) : C.Ty Γ :=
  P.pi (SizedFamily.type Z P Γ)
    (InternalEquivalence.isEquiv F P I S J
      (allCan Z F K Q ZS KS QS (T.reindex C.fst) (SizedFamily.generic Z P)))

end WeakCommutation

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingAdjunctionV2 -/

/-!
# The object operations in the quantifier adjunctions

Constant carriers use the source extraction and insertion maps. Quantified
carriers use the inverse of the precise weak-commutation map. The hom-equivalence
types retain complete internal morphism sums, including commuting paths. They
do not, by themselves, assert naturality or an adjunction.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

variable {C : CwF.{u, v, w, t}}

namespace QuantifierAdjunction

variable (T : CoreTheory C)

/-- Erase the irrelevant size from an existential of a constant small type. -/
def forgetSize {Γ : C.Ctx} (A : T.univ.Code Γ) :
    SmallHom T.univ T.functions (T.ex.code (T.univ.sub A C.fst)) A := by
  let π := @C.fst (C.ext Γ (T.size.type Γ)) (T.univ.el (T.univ.sub A C.fst))
  have h : C.tySub (T.univ.el (T.univ.sub A C.fst)) π =
      C.tySub (T.univ.el A) (C.comp C.fst π) :=
    (congrArg (fun V => C.tySub V π) (T.univ.el_sub A C.fst).symm).trans
      (C.tySub_comp _ _ _)
  exact T.ex.recursor T.functions (T.univ.sub A C.fst) A (C.castTm h C.snd)

/-- The source `extract_A i ⟨j, a⟩ = a` for a bounded constant family. -/
def extract {Γ : C.Ctx} (A : T.univ.Code Γ) :
    SmallHom T.univ T.functions
      (T.size.diamond T.small T.ex (T.univ.sub A C.fst)) (T.univ.sub A C.fst) :=
  T.functions.compose (SmallHom.sub T.univ T.functions (forgetSize T A) C.fst)
    (Parametricity.boundedToExists T.size T.functions T.small T.ex (T.univ.sub A C.fst))

/-- Constant introduction into the universal size type. -/
def repeatAll {Γ : C.Ctx} (A : T.univ.Code Γ) :
    SmallHom T.univ T.functions A (T.all.code (T.univ.sub A C.fst)) :=
  T.all.arrowFromSize T.allSubstitution T.functions
    (T.functions.identity (T.univ.el (T.univ.sub A C.fst)))

/-- The source `insert_A i a = λ j < i, a`. -/
def insert {Γ : C.Ctx} (A : T.univ.Code Γ) :
    SmallHom T.univ T.functions (T.univ.sub A C.fst)
      (T.size.box T.small T.all (T.univ.sub A C.fst)) :=
  T.functions.compose
    (WeakCommutation.allRestriction T.size T.functions T.small T.all
      T.sizeSubstitution T.smallSubstitution T.allSubstitution (T.univ.sub A C.fst))
    (SmallHom.sub T.univ T.functions (repeatAll T A) C.fst)

/-- Extract the inverse of the source existential canonical map from its
single internally quantified half-adjoint-equivalence witness. -/
def existsInverse {Γ : C.Ctx} (D : InternalFunctorData T.univ T.functions Γ)
    (h : C.Tm Γ (WeakCommutation.existsType T.size T.functions T.small
      T.identityElimination T.ex D))
    (A : T.univ.Code (C.ext Γ (T.size.type Γ))) :
    SmallHom T.univ T.functions (D.obj C.id (T.ex.code A))
      (T.ex.code (D.obj C.fst (T.size.diamond T.small T.ex A))) := by
  let G := SizedFamily.generic T.size T.products (Γ := Γ)
  let τ := SizedFamily.extend T.size T.products C.id A
  have hin : T.univ.sub ((D.reindex C.fst).obj C.id (T.ex.code G)) τ =
      D.obj C.id (T.ex.code A) := by
    dsimp [InternalFunctorData.reindex]
    rw [D.obj_sub, T.exSubstitution.code_sub, SizedFamily.generic_sub_extend,
      C.comp_id, SizedFamily.extend_fst]
  have hbase : C.comp (C.comp C.fst C.fst) (T.size.lift τ) =
      (@C.fst Γ (T.size.type Γ)) := by
    rw [C.assoc, T.size.lift_fst, ← C.assoc, SizedFamily.extend_fst, C.id_comp]
  have hout : T.univ.sub (T.ex.code ((D.reindex C.fst).obj C.fst
      (T.size.diamond T.small T.ex G))) τ =
      T.ex.code (D.obj C.fst (T.size.diamond T.small T.ex A)) := by
    dsimp [InternalFunctorData.reindex]
    rw [T.exSubstitution.code_sub, D.obj_sub, hbase,
      T.size.diamond_sub T.small T.ex T.sizeSubstitution T.smallSubstitution T.exSubstitution,
      SizedFamily.generic_sub_extend]
  let inverse := T.sums.fst (T.products.unlam h)
  exact C.castTm (by
    rw [SmallHom.type_sub, hin, hout]) (C.tmSub inverse τ)

/-- Extract the inverse of the source universal canonical map, retaining its
internally quantified provenance. -/
def allInverse {Γ : C.Ctx} (D : InternalFunctorData T.univ T.functions Γ)
    (h : C.Tm Γ (WeakCommutation.allType T.size T.functions T.small
      T.identityElimination T.all T.sizeSubstitution T.smallSubstitution T.allSubstitution D))
    (A : T.univ.Code (C.ext Γ (T.size.type Γ))) :
    SmallHom T.univ T.functions (T.all.code (D.obj C.fst (T.size.box T.small T.all A)))
      (D.obj C.id (T.all.code A)) := by
  let G := SizedFamily.generic T.size T.products (Γ := Γ)
  let τ := SizedFamily.extend T.size T.products C.id A
  have hout : T.univ.sub ((D.reindex C.fst).obj C.id (T.all.code G)) τ =
      D.obj C.id (T.all.code A) := by
    dsimp [InternalFunctorData.reindex]
    rw [D.obj_sub, T.allSubstitution.code_sub, SizedFamily.generic_sub_extend,
      C.comp_id, SizedFamily.extend_fst]
  have hbase : C.comp (C.comp C.fst C.fst) (T.size.lift τ) =
      (@C.fst Γ (T.size.type Γ)) := by
    rw [C.assoc, T.size.lift_fst, ← C.assoc, SizedFamily.extend_fst, C.id_comp]
  have hin : T.univ.sub (T.all.code ((D.reindex C.fst).obj C.fst
      (T.size.box T.small T.all G))) τ =
      T.all.code (D.obj C.fst (T.size.box T.small T.all A)) := by
    dsimp [InternalFunctorData.reindex]
    rw [T.allSubstitution.code_sub, D.obj_sub, hbase,
      T.size.box_sub T.small T.all T.sizeSubstitution T.smallSubstitution T.allSubstitution,
      SizedFamily.generic_sub_extend]
  let inverse := T.sums.fst (T.products.unlam h)
  exact C.castTm (by
    rw [SmallHom.type_sub, hin, hout]) (C.tmSub inverse τ)

variable {Γ : C.Ctx} (F : WildEndofunctor T.univ T.functions T.identities Γ)

/-- The constant size-indexed algebra, with structure `k ∘ F(extract)`. -/
def constantAlgebra {Δ : C.Ctx} {σ : C.Sub Δ Γ} (A : AlgebraOver F σ) :
    Sized.AlgebraOver T F σ where
  carrier := T.univ.sub A.carrier C.fst
  structureMap := Sized.ofAt T.size T.functions T.small T.all T.functionProducts
    (T.functions.compose
      (C.castTm (congrArg (fun X => T.functions.arr (T.univ.el X)
        (T.univ.el (T.univ.sub A.carrier C.fst))) (F.obj_sub σ A.carrier C.fst))
        (SmallHom.sub T.univ T.functions A.structureMap C.fst))
      (F.map (C.comp σ C.fst) (T.size.diamond T.small T.ex (T.univ.sub A.carrier C.fst))
        (T.univ.sub A.carrier C.fst) (extract T A.carrier)))

/-- The constant size-indexed coalgebra, with structure `F(insert) ∘ k`. -/
def constantCoalgebra {Δ : C.Ctx} {σ : C.Sub Δ Γ} (A : CoalgebraOver F σ) :
    Sized.CoalgebraOver T F σ where
  carrier := T.univ.sub A.carrier C.fst
  structureMap := Sized.ofAt T.size T.functions T.small T.all T.functionProducts
    (T.functions.compose
      (F.map (C.comp σ C.fst) (T.univ.sub A.carrier C.fst)
        (T.size.box T.small T.all (T.univ.sub A.carrier C.fst)) (insert T A.carrier))
      (C.castTm (congrArg (fun X => T.functions.arr
        (T.univ.el (T.univ.sub A.carrier C.fst)) (T.univ.el X)) (F.obj_sub σ A.carrier C.fst))
        (SmallHom.sub T.univ T.functions A.structureMap C.fst)))

/-- Existentially quantify a size-indexed algebra. Its structure is exactly
`(∃ k) ∘ can⁻¹`, using the inverse supplied by the source weak-commutation term. -/
def existsAlgebra {Δ : C.Ctx} {σ : C.Sub Δ Γ}
    (h : C.Tm Δ (WeakCommutation.existsType T.size T.functions T.small
      T.identityElimination T.ex (F.toInternalFunctorData.reindex σ)))
    (A : Sized.AlgebraOver T F σ) : AlgebraOver F σ where
  carrier := T.ex.code A.carrier
  structureMap := by
    let inverse := existsInverse T (F.toInternalFunctorData.reindex σ) h A.carrier
    have hi : (F.toInternalFunctorData.reindex σ).obj C.id (T.ex.code A.carrier) =
        F.obj σ (T.ex.code A.carrier) :=
      congrArg (fun ρ => F.obj ρ (T.ex.code A.carrier)) (C.comp_id σ)
    let inverse' := C.castTm (congrArg (fun X => T.functions.arr (T.univ.el X)
      (T.univ.el (T.ex.code (Sized.liftObjectOver T F σ
        (T.size.diamond T.small T.ex A.carrier))))) hi) inverse
    exact T.functions.compose
      (T.ex.map T.functions _ A.carrier
        (Sized.eval T.size T.functions T.small T.all T.functionProducts A.structureMap)) inverse'

/-- Universally quantify a size-indexed coalgebra. Its structure is exactly
`can⁻¹ ∘ (∀ k)`. -/
def allCoalgebra {Δ : C.Ctx} {σ : C.Sub Δ Γ}
    (h : C.Tm Δ (WeakCommutation.allType T.size T.functions T.small T.identityElimination
      T.all T.sizeSubstitution T.smallSubstitution T.allSubstitution
      (F.toInternalFunctorData.reindex σ)))
    (A : Sized.CoalgebraOver T F σ) : CoalgebraOver F σ where
  carrier := T.all.code A.carrier
  structureMap := by
    let inverse := allInverse T (F.toInternalFunctorData.reindex σ) h A.carrier
    have hi : (F.toInternalFunctorData.reindex σ).obj C.id (T.all.code A.carrier) =
        F.obj σ (T.all.code A.carrier) :=
      congrArg (fun ρ => F.obj ρ (T.all.code A.carrier)) (C.comp_id σ)
    let inverse' := C.castTm (congrArg (fun X => T.functions.arr
      (T.univ.el (T.all.code (Sized.liftObjectOver T F σ
        (T.size.box T.small T.all A.carrier)))) (T.univ.el X)) hi) inverse
    exact T.functions.compose inverse'
      (T.all.map T.functions T.allSubstitution A.carrier _
        (Sized.eval T.size T.functions T.small T.all T.functionProducts A.structureMap))

/-- The internal hom-equivalence type used in the proposed existential
adjunction argument. Both sides retain commuting paths; naturality is separate. -/
def existsHomEquivalenceType {Δ : C.Ctx} {σ : C.Sub Δ Γ}
    (h : C.Tm Δ (WeakCommutation.existsType T.size T.functions T.small
      T.identityElimination T.ex (F.toInternalFunctorData.reindex σ)))
    (A : Sized.AlgebraOver T F σ) (B : AlgebraOver F σ) : C.Ty Δ :=
  InternalEquivalence.equivalence T.functions T.products T.identities T.sums T.identityElimination
    (AlgebraOver.homType T.sums (existsAlgebra T F h A) B)
    (Sized.AlgebraOver.homType A (constantAlgebra T F B))

/-- The internal hom-equivalence type used in the universal adjunction argument.
It compares complete coalgebra morphisms, but does not assert naturality. -/
def allHomEquivalenceType {Δ : C.Ctx} {σ : C.Sub Δ Γ}
    (h : C.Tm Δ (WeakCommutation.allType T.size T.functions T.small T.identityElimination
      T.all T.sizeSubstitution T.smallSubstitution T.allSubstitution
      (F.toInternalFunctorData.reindex σ)))
    (B : CoalgebraOver F σ) (A : Sized.CoalgebraOver T F σ) : C.Ty Δ :=
  InternalEquivalence.equivalence T.functions T.products T.identities T.sums T.identityElimination
    (Sized.CoalgebraOver.homType (constantCoalgebra T F B) A)
    (CoalgebraOver.homType T.sums B (allCoalgebra T F h A))

end QuantifierAdjunction

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingFixpointsV2 -/

/-!
# The source's recursive codes for inductive and coinductive carriers

Section 3.3 and Appendix B define the sized carriers by recursion into the large
universe type. The recursive input is only defined below the current size. It is
therefore evaluated after introducing both a smaller size and its bound proof;
no arbitrary extension to a total family of universe codes is used.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory.EncodingFixpoints

universe u v w t

variable {C : CwF.{u, v, w, t}} {U : Universe C} {I : IdentityTypes C}
    (Z : SizeRules C U I) (P : DependentProducts C) (F : FunctionTypes C)

abbrev sizeContext (Γ : C.Ctx) : C.Ctx := C.ext Γ (Z.type Γ)

/-- At the current size, the recursive input has type `Π j, j < i → U`. -/
abbrev recursiveType (Γ : C.Ctx) : C.Ty (sizeContext Z Γ) :=
  Z.bounded P F (U.type (sizeContext Z Γ))

abbrev recursiveContext (Γ : C.Ctx) : C.Ctx :=
  C.ext (sizeContext Z Γ) (recursiveType Z P F Γ)

abbrev bodyContext (Γ : C.Ctx) : C.Ctx :=
  C.ext (recursiveContext Z P F Γ) (Z.type (recursiveContext Z P F Γ))

abbrev recursiveProjection (Γ : C.Ctx) :
    C.Sub (recursiveContext Z P F Γ) (sizeContext Z Γ) := C.fst

abbrev bodyProjection (Γ : C.Ctx) :
    C.Sub (bodyContext Z P F Γ) (recursiveContext Z P F Γ) := C.fst

/-- The body of the recursive input before its dependent product is formed. -/
abbrev recursiveBody (Γ : C.Ctx) :
    C.Ty (C.ext (sizeContext Z Γ) (Z.type (sizeContext Z Γ))) :=
  F.arr Z.bound (C.tySub (U.type (sizeContext Z Γ)) Z.inner)

/-- The generic recursive family, reindexed into the context containing it. -/
def genericRecursive (Γ : C.Ctx) :
    C.Tm (recursiveContext Z P F Γ)
      (P.pi (Z.type (recursiveContext Z P F Γ))
        (C.tySub (recursiveBody Z F Γ)
          (Z.lift (recursiveProjection Z P F Γ)))) :=
  C.castTm (Z.pi_sub P (recursiveBody Z F Γ)
    (recursiveProjection Z P F Γ)) C.snd

theorem innerSize_type (Γ : C.Ctx) :
    C.tySub (C.tySub (Z.type (sizeContext Z Γ)) (recursiveProjection Z P F Γ))
        (bodyProjection Z P F Γ) = Z.type (bodyContext Z P F Γ) :=
  (C.tySub_comp _ _ _).trans (Z.type_sub _)

/-- Supply the newly bound size to the reindexed recursive family. -/
def innerSizeSub (Γ : C.Ctx) : C.Sub (bodyContext Z P F Γ)
    (C.ext (recursiveContext Z P F Γ)
      (C.tySub (Z.type (sizeContext Z Γ)) (recursiveProjection Z P F Γ))) :=
  C.pair (bodyProjection Z P F Γ)
    (C.castTm (innerSize_type Z P F Γ).symm (Z.generic (recursiveContext Z P F Γ)))

/-- Forget the recursive family while retaining the current and smaller sizes. -/
def boundsSub (Γ : C.Ctx) : C.Sub (bodyContext Z P F Γ)
    (C.ext (sizeContext Z Γ) (Z.type (sizeContext Z Γ))) :=
  Z.lift (recursiveProjection Z P F Γ)

/-- The actual source bound code `j < i` in the recursive body context. -/
def guardCode (Γ : C.Ctx) : U.Code (bodyContext Z P F Γ) :=
  U.sub Z.boundCode (boundsSub Z P F Γ)

theorem recursiveArrow_type (Γ : C.Ctx) :
    C.tySub (recursiveBody Z F Γ) (boundsSub Z P F Γ) =
      F.arr (U.el (guardCode Z P F Γ)) (U.type (bodyContext Z P F Γ)) := by
  rw [recursiveBody, F.arr_sub]
  apply congrArg₂ F.arr
  · exact U.el_sub Z.boundCode (boundsSub Z P F Γ)
  · exact (C.tySub_comp _ _ _).trans (U.type_sub _)

/-- The internal function `X j : (j < i) → U`. -/
def recursiveArrow (Γ : C.Ctx) : C.Tm (bodyContext Z P F Γ)
    (F.arr (U.el (guardCode Z P F Γ)) (U.type (bodyContext Z P F Γ))) :=
  C.castTm (recursiveArrow_type Z P F Γ) (P.unlam (genericRecursive Z P F Γ))

/-- The universe code `X j p` after the bound proof has been introduced. -/
def recursiveValue (Γ : C.Ctx) :
    U.Code (C.ext (bodyContext Z P F Γ) (U.el (guardCode Z P F Γ))) :=
  C.castTm (U.type_sub C.fst) (F.app (F.sub (recursiveArrow Z P F Γ) C.fst) C.snd)

/-- Bounded existential packaging of the partial recursive family: `∃ j. Σ p : j < i, X j p`. -/
def existentialPack {S : DependentSums C} (K : SmallTypeConstructors C U P S I)
    (E : ExistentialSizeQuantifier C U I Z) (Γ : C.Ctx) :
    U.Code (recursiveContext Z P F Γ) :=
  E.code (K.sigma (guardCode Z P F Γ) (recursiveValue Z P F Γ))

/-- Bounded universal packaging of the partial recursive family: `∀ j. Π p : j < i, X j p`. -/
def universalPack {S : DependentSums C} (K : SmallTypeConstructors C U P S I)
    (Q : UniversalSizeQuantifier C U I Z) (Γ : C.Ctx) :
    U.Code (recursiveContext Z P F Γ) :=
  Q.code (K.pi (guardCode Z P F Γ) (recursiveValue Z P F Γ))

/-- The step `λ i X, T (∃ j < i, X j)` used in the source's sized μ definition. -/
def muStep {S : DependentSums C} (K : SmallTypeConstructors C U P S I)
    (E : ExistentialSizeQuantifier C U I Z) {Γ : C.Ctx} (T : WildEndofunctor U F I Γ) :
    C.Tm Γ (P.pi (Z.type Γ)
      (F.arr (recursiveType Z P F Γ) (U.type (sizeContext Z Γ)))) :=
  P.lam (F.lam (C.castTm (U.type_sub C.fst).symm
    (T.obj (C.comp C.fst (recursiveProjection Z P F Γ)) (existentialPack Z P F K E Γ))))

/-- The step `λ i X, T (∀ j < i, X j)` used in the source's sized ν definition. -/
def nuStep {S : DependentSums C} (K : SmallTypeConstructors C U P S I)
    (Q : UniversalSizeQuantifier C U I Z) {Γ : C.Ctx} (T : WildEndofunctor U F I Γ) :
    C.Tm Γ (P.pi (Z.type Γ)
      (F.arr (recursiveType Z P F Γ) (U.type (sizeContext Z Γ)))) :=
  P.lam (F.lam (C.castTm (U.type_sub C.fst).symm
    (T.obj (C.comp C.fst (recursiveProjection Z P F Γ)) (universalPack Z P F K Q Γ))))

/-- The source's sized inductive carrier `μ◇ T`, defined by the primitive size recursor. -/
def sizedMu {S : DependentSums C} (K : SmallTypeConstructors C U P S I)
    (E : ExistentialSizeQuantifier C U I Z) (R : SizeRecursion C U I Z P F)
    {Γ : C.Ctx} (T : WildEndofunctor U F I Γ) : U.Code (sizeContext Z Γ) :=
  P.unlam (R.fix (U.type (sizeContext Z Γ)) (muStep Z P F K E T))

/-- The source's sized coinductive carrier `ν□ T`, defined by the primitive size recursor. -/
def sizedNu {S : DependentSums C} (K : SmallTypeConstructors C U P S I)
    (Q : UniversalSizeQuantifier C U I Z) (R : SizeRecursion C U I Z P F)
    {Γ : C.Ctx} (T : WildEndofunctor U F I Γ) : U.Code (sizeContext Z Γ) :=
  P.unlam (R.fix (U.type (sizeContext Z Γ)) (nuStep Z P F K Q T))

/-- The actual propositional recursor beta witness for the sized μ code. -/
def sizedMu_fix_beta {S : DependentSums C} (K : SmallTypeConstructors C U P S I)
    (E : ExistentialSizeQuantifier C U I Z) (R : SizeRecursion C U I Z P F)
    {Γ : C.Ctx} (T : WildEndofunctor U F I Γ) :
    C.Tm Γ (P.pi (Z.type Γ)
      (I.id (U.type (sizeContext Z Γ)) (sizedMu Z P F K E R T)
        (F.app (P.unlam (muStep Z P F K E T))
          (Z.restrict P F (R.fix (U.type (sizeContext Z Γ)) (muStep Z P F K E T)))))) :=
  R.beta (U.type (sizeContext Z Γ)) (muStep Z P F K E T)

/-- The actual propositional recursor beta witness for the sized ν code. -/
def sizedNu_fix_beta {S : DependentSums C} (K : SmallTypeConstructors C U P S I)
    (Q : UniversalSizeQuantifier C U I Z) (R : SizeRecursion C U I Z P F)
    {Γ : C.Ctx} (T : WildEndofunctor U F I Γ) :
    C.Tm Γ (P.pi (Z.type Γ)
      (I.id (U.type (sizeContext Z Γ)) (sizedNu Z P F K Q R T)
        (F.app (P.unlam (nuStep Z P F K Q T))
          (Z.restrict P F (R.fix (U.type (sizeContext Z Γ)) (nuStep Z P F K Q T)))))) :=
  R.beta (U.type (sizeContext Z Γ)) (nuStep Z P F K Q T)

/-- The source's unsized inductive carrier `μ T := ∃ i, μ◇ T i`. -/
def mu {S : DependentSums C} (K : SmallTypeConstructors C U P S I)
    (E : ExistentialSizeQuantifier C U I Z) (R : SizeRecursion C U I Z P F)
    {Γ : C.Ctx} (T : WildEndofunctor U F I Γ) : U.Code Γ :=
  E.code (sizedMu Z P F K E R T)

/-- The source's unsized coinductive carrier `ν T := ∀ i, ν□ T i`. -/
def nu {S : DependentSums C} (K : SmallTypeConstructors C U P S I)
    (Q : UniversalSizeQuantifier C U I Z) (R : SizeRecursion C U I Z P F)
    {Γ : C.Ctx} (T : WildEndofunctor U F I Γ) : U.Code Γ :=
  Q.code (sizedNu Z P F K Q R T)

end LaarakkerOttenVanDenBerg2026.V2.Theory.EncodingFixpoints

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingFixpointBetaV2 -/

/-! Unfolding the recursive carrier codes by the source's substitution and beta rules. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

variable {C : CwF.{u, v, w, t}} {U : Universe C} {I : IdentityTypes C}

namespace FunctionTypes

variable (F : FunctionTypes C)

theorem sub_congr {Γ Δ : C.Ctx} {A A' B B' : C.Ty Γ}
    (hA : A = A') (hB : B = B')
    {f : C.Tm Γ (F.arr A B)} {g : C.Tm Γ (F.arr A' B')}
    (h : HEq f g) (σ : C.Sub Δ Γ) : HEq (F.sub f σ) (F.sub g σ) := by
  cases hA
  cases hB
  cases h
  rfl

/-- Evaluation of a lambda at the generic variable is its contextual body. -/
theorem genericApp_lam {P : DependentProducts C} (FP : FunctionProductCompatibility F P)
    {Γ : C.Ctx} {A B : C.Ty Γ} (b : C.Tm (C.ext Γ A) (C.tySub B C.fst)) :
    F.app (F.sub (F.lam b) C.fst) C.snd = b := by
  have h := (FP.lam_eq (F.app (F.sub (F.lam b) C.fst) C.snd)).symm.trans
    ((heq_of_eq (F.eta (F.lam b))).trans (FP.lam_eq b))
  have h' := congrArg P.unlam (eq_of_heq h)
  simpa only [P.beta] using h'

theorem genericApp_sub {Γ Δ : C.Ctx} {A B : C.Ty Γ}
    (f : C.Tm Γ (F.arr A B)) (σ : C.Sub Δ Γ) :
    HEq (C.tmSub (F.app (F.sub f C.fst) C.snd) (C.lift σ A))
      (F.app (F.sub (F.sub f σ) C.fst) C.snd) := by
  have hs (τ υ : C.Sub (C.ext Δ (C.tySub A σ)) Γ) (e : τ = υ) :
      HEq (F.sub f τ) (F.sub f υ) := by cases e; rfl
  have hB : C.tySub (C.tySub B C.fst) (C.lift σ A) =
      C.tySub (C.tySub B σ) C.fst := by
    rw [C.tySub_comp, C.lift_fst, C.tySub_comp]
  exact (heq_of_eq (F.app_sub (F.sub f C.fst) C.snd (C.lift σ A))).trans
    (F.app_congr (C.tySub_lift σ A) hB
      ((F.sub_comp_heq f C.fst (C.lift σ A)).trans
        ((hs _ _ (C.lift_fst σ A)).trans (F.sub_comp_heq f σ C.fst).symm))
      (C.lift_snd σ A))

theorem genericApp_sub_as {Γ Δ : C.Ctx} {A B : C.Ty Γ}
    (f : C.Tm Γ (F.arr A B)) (σ : C.Sub Δ Γ) (A' B' : C.Ty Δ)
    (hA : C.tySub A σ = A') (hB : C.tySub B σ = B')
    (g : C.Tm Δ (F.arr A' B')) (hg : HEq (F.sub f σ) g) :
    HEq (C.tmSub (F.app (F.sub f C.fst) C.snd) (C.liftAs σ A A' hA))
      (F.app (F.sub g C.fst) C.snd) := by
  subst A'
  subst B'
  have e := eq_of_heq hg
  subst g
  exact F.genericApp_sub f σ

end FunctionTypes

namespace Universe

variable (U : Universe C)

theorem liftElAs_eq_liftAs {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : U.Code Γ)
    (A' : U.Code Δ) (h : U.sub A σ = A') :
    U.liftElAs σ A A' h =
      C.liftAs σ (U.el A) (U.el A') ((U.el_sub A σ).trans (congrArg U.el h)) := by
  apply C.sub_ext
  · exact (U.liftElAs_fst _ _ _ _).trans (C.liftAs_fst _ _ _ _).symm
  · exact (U.liftElAs_snd _ _ _ _).trans (C.liftAs_snd _ _ _ _).symm

end Universe

namespace SizeRules

variable (Z : SizeRules C U I)

theorem lift_section {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (τ : C.Sub Γ Δ)
    (h : C.comp σ τ = C.id) : C.comp (Z.lift σ) (Z.lift τ) = C.id := by
  apply Z.hom_ext
  · rw [← C.assoc, Z.lift_fst, C.assoc, Z.lift_fst,
      ← C.assoc, h, C.id_comp, C.comp_id]
  · rw [← Z.sub_comp, Z.generic_sub_lift, Z.generic_sub_lift, Z.sub_id]

end SizeRules

namespace EncodingFixpoints

variable (Z : SizeRules C U I) (P : DependentProducts C) (F : FunctionTypes C)

/-- Substitute the restricted family for the generic recursive argument. -/
abbrev restrictionSub {Γ : C.Ctx}
    (h : C.Tm Γ (P.pi (Z.type Γ) (U.type (sizeContext Z Γ)))) :
    C.Sub (sizeContext Z Γ) (recursiveContext Z P F Γ) :=
  C.termSub (Z.restrict P F h)

theorem boundsSub_restriction {Γ : C.Ctx}
    (h : C.Tm Γ (P.pi (Z.type Γ) (U.type (sizeContext Z Γ)))) :
    C.comp (boundsSub Z P F Γ) (Z.lift (restrictionSub Z P F h)) = C.id :=
  Z.lift_section C.fst (C.termSub (Z.restrict P F h)) (C.termSub_fst _)

theorem guardCode_restriction {Γ : C.Ctx}
    (h : C.Tm Γ (P.pi (Z.type Γ) (U.type (sizeContext Z Γ)))) :
    U.sub (guardCode Z P F Γ) (Z.lift (restrictionSub Z P F h)) = Z.boundCode := by
  rw [guardCode, U.sub_comp, boundsSub_restriction]
  exact eq_of_heq ((C.castTm_heq _ _).trans (C.tmSub_id _))

theorem recursiveBody_restriction {Γ : C.Ctx}
    (h : C.Tm Γ (P.pi (Z.type Γ) (U.type (sizeContext Z Γ)))) :
    C.tySub (C.tySub (recursiveBody Z F Γ) (boundsSub Z P F Γ))
      (Z.lift (restrictionSub Z P F h)) = recursiveBody Z F Γ := by
  rw [C.tySub_comp, boundsSub_restriction, C.tySub_id]

/-- Evaluating the generic recursive argument after substitution gives the restriction. -/
theorem recursiveArrow_restriction {Γ : C.Ctx}
    (h : C.Tm Γ (P.pi (Z.type Γ) (U.type (sizeContext Z Γ)))) :
    HEq (F.sub (recursiveArrow Z P F Γ) (Z.lift (restrictionSub Z P F h)))
      (P.unlam (Z.restrict P F h)) := by
  let τ := restrictionSub Z P F h
  have hf : HEq (C.tmSub (genericRecursive Z P F Γ) τ) (Z.restrict P F h) :=
    (C.tmSub_heq (Z.pi_sub P (recursiveBody Z F Γ) C.fst).symm
      (C.castTm_heq _ _) τ).trans (C.termSub_snd _)
  exact (F.sub_heq _ _).trans
    ((C.tmSub_heq (recursiveArrow_type Z P F Γ).symm
      (C.castTm_heq _ _) (Z.lift τ)).trans
      ((heq_of_eq (Z.unlam_sub P (genericRecursive Z P F Γ) τ)).symm.trans
        (P.unlam_congr (recursiveBody_restriction Z P F h)
          ((C.castTm_heq _ _).trans hf))))

/-- The bound proof is passed to the recursive family; after restriction the result is `h j`. -/
theorem recursiveValue_restriction (FP : FunctionProductCompatibility F P) {Γ : C.Ctx}
    (h : C.Tm Γ (P.pi (Z.type Γ) (U.type (sizeContext Z Γ)))) :
    U.sub (recursiveValue Z P F Γ)
      (U.liftElAs (Z.lift (restrictionSub Z P F h)) (guardCode Z P F Γ) Z.boundCode
        (guardCode_restriction Z P F h)) =
      U.sub (U.sub (P.unlam h) Z.inner) C.fst := by
  let s := Z.lift (restrictionSub Z P F h)
  let l := U.liftElAs s (guardCode Z P F Γ) Z.boundCode
    (guardCode_restriction Z P F h)
  have hA : C.tySub (U.el (guardCode Z P F Γ)) s = Z.bound :=
    (U.el_sub _ _).trans (congrArg U.el (guardCode_restriction Z P F h))
  have hB : C.tySub (U.type (bodyContext Z P F Γ)) s =
      C.tySub (U.type (sizeContext Z Γ)) Z.inner :=
    (U.type_sub s).trans (U.type_sub Z.inner).symm
  have ha := F.genericApp_sub_as (recursiveArrow Z P F Γ) s Z.bound
    (C.tySub (U.type (sizeContext Z Γ)) Z.inner) hA hB
    (P.unlam (Z.restrict P F h)) (recursiveArrow_restriction Z P F h)
  have hl : l = C.liftAs s (U.el (guardCode Z P F Γ)) Z.bound hA :=
    U.liftElAs_eq_liftAs _ _ _ _
  have hbody : F.app (F.sub (P.unlam (Z.restrict P F h)) C.fst) C.snd =
      C.tmSub (C.tmSub (P.unlam h) Z.inner) C.fst := by
    rw [SizeRules.restrict, P.beta]
    exact F.genericApp_lam FP _
  apply eq_of_heq
  refine (C.castTm_heq _ _).trans ?_
  refine (C.tmSub_heq (U.type_sub C.fst).symm (C.castTm_heq _ _) l).trans ?_
  have ha' : HEq
      (C.tmSub (F.app (F.sub (recursiveArrow Z P F Γ) C.fst) C.snd) l)
      (C.tmSub (C.tmSub (P.unlam h) Z.inner) (C.fst (A := Z.bound))) := by
    rw [hl]
    exact ha.trans (heq_of_eq hbody)
  refine ha'.trans ?_
  exact ((C.tmSub_heq (U.type_sub Z.inner).symm (C.castTm_heq _ _) C.fst).symm.trans
    (C.castTm_heq _ _).symm)

theorem existentialPack_restriction {S : DependentSums C}
    (K : SmallTypeConstructors C U P S I) (E : ExistentialSizeQuantifier C U I Z)
    (FP : FunctionProductCompatibility F P) (KS : SmallTypeSubstitution U P S I K)
    (ES : ExistentialSizeSubstitution U I Z E) {Γ : C.Ctx}
    (h : C.Tm Γ (P.pi (Z.type Γ) (U.type (sizeContext Z Γ)))) :
    U.sub (existentialPack Z P F K E Γ) (restrictionSub Z P F h) =
      Z.diamond K E (P.unlam h) := by
  rw [existentialPack, ES.code_sub,
    K.sigma_sub_as KS _ _ _ _ (guardCode_restriction Z P F h),
    recursiveValue_restriction Z P F FP]
  rfl

theorem universalPack_restriction {S : DependentSums C}
    (K : SmallTypeConstructors C U P S I) (Q : UniversalSizeQuantifier C U I Z)
    (FP : FunctionProductCompatibility F P) (KS : SmallTypeSubstitution U P S I K)
    (QS : UniversalSizeSubstitution U I Z Q) {Γ : C.Ctx}
    (h : C.Tm Γ (P.pi (Z.type Γ) (U.type (sizeContext Z Γ)))) :
    U.sub (universalPack Z P F K Q Γ) (restrictionSub Z P F h) =
      Z.box K Q (P.unlam h) := by
  rw [universalPack, QS.code_sub,
    K.pi_sub_as KS _ _ _ _ (guardCode_restriction Z P F h),
    recursiveValue_restriction Z P F FP]
  rfl

/-- The μ step computes to the functor applied to the exact bounded existential. -/
theorem muStep_restriction {S : DependentSums C}
    (K : SmallTypeConstructors C U P S I) (E : ExistentialSizeQuantifier C U I Z)
    (FP : FunctionProductCompatibility F P) (KS : SmallTypeSubstitution U P S I K)
    (ES : ExistentialSizeSubstitution U I Z E) {Γ : C.Ctx}
    (T : WildEndofunctor U F I Γ)
    (h : C.Tm Γ (P.pi (Z.type Γ) (U.type (sizeContext Z Γ)))) :
    F.app (P.unlam (muStep Z P F K E T)) (Z.restrict P F h) =
      T.obj C.fst (Z.diamond K E (P.unlam h)) := by
  let b := T.obj (C.comp C.fst (recursiveProjection Z P F Γ))
    (existentialPack Z P F K E Γ)
  have hb : U.sub b (restrictionSub Z P F h) =
      T.obj C.fst (Z.diamond K E (P.unlam h)) := by
    dsimp [b]
    rw [T.obj_sub, existentialPack_restriction Z P F K E FP KS ES]
    congr 1
    exact (C.assoc _ _ _).trans
      ((congrArg (C.comp C.fst) (C.termSub_fst _)).trans (C.comp_id _))
  rw [muStep, P.beta]
  apply eq_of_heq
  exact (F.beta _ (Z.restrict P F h)).trans
    ((C.tmSub_heq (U.type_sub C.fst) (C.castTm_heq _ _) (restrictionSub Z P F h)).trans
      ((C.castTm_heq _ _).symm.trans (heq_of_eq hb)))

/-- The ν step computes to the functor applied to the exact bounded universal. -/
theorem nuStep_restriction {S : DependentSums C}
    (K : SmallTypeConstructors C U P S I) (Q : UniversalSizeQuantifier C U I Z)
    (FP : FunctionProductCompatibility F P) (KS : SmallTypeSubstitution U P S I K)
    (QS : UniversalSizeSubstitution U I Z Q) {Γ : C.Ctx}
    (T : WildEndofunctor U F I Γ)
    (h : C.Tm Γ (P.pi (Z.type Γ) (U.type (sizeContext Z Γ)))) :
    F.app (P.unlam (nuStep Z P F K Q T)) (Z.restrict P F h) =
      T.obj C.fst (Z.box K Q (P.unlam h)) := by
  let b := T.obj (C.comp C.fst (recursiveProjection Z P F Γ))
    (universalPack Z P F K Q Γ)
  have hb : U.sub b (restrictionSub Z P F h) =
      T.obj C.fst (Z.box K Q (P.unlam h)) := by
    dsimp [b]
    rw [T.obj_sub, universalPack_restriction Z P F K Q FP KS QS]
    congr 1
    exact (C.assoc _ _ _).trans
      ((congrArg (C.comp C.fst) (C.termSub_fst _)).trans (C.comp_id _))
  rw [nuStep, P.beta]
  apply eq_of_heq
  exact (F.beta _ (Z.restrict P F h)).trans
    ((C.tmSub_heq (U.type_sub C.fst) (C.castTm_heq _ _) (restrictionSub Z P F h)).trans
      ((C.castTm_heq _ _).symm.trans (heq_of_eq hb)))

end EncodingFixpoints

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingStructuresV2 -/

/-!
# The source algebra and coalgebra structures on the recursive carriers

The size-recursion equation is normalized to the literal bounded code. Its
identity witness is decoded using J-derived transport. Quantification then
uses the inverse of the canonical weak-commutation map.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

variable {C : CwF.{u, v, w, t}}

namespace Universe

variable (U : Universe C) (I : IdentityTypes C) (J : IdentityElimination C I)

theorem generic_decode_sub {Γ : C.Ctx} (A : U.Code Γ) :
    C.tySub (U.el (U.generic Γ)) (C.termSub A) = U.el A :=
  (U.el_sub _ _).trans (congrArg U.el (U.generic_sub_extend C.id A))

/-- Decode an internal equality of universe codes by J-derived transport. -/
def transport {Γ : C.Ctx} {A B : U.Code Γ}
    (p : C.Tm Γ (I.id (U.type Γ) A B)) (a : C.Tm Γ (U.el A)) : C.Tm Γ (U.el B) :=
  C.castTm (U.generic_decode_sub B)
    (InternalPath.transport I J (U.el (U.generic Γ)) p
      (C.castTm (U.generic_decode_sub A).symm a))

def pathSub {Γ Δ : C.Ctx} {A B : U.Code Γ}
    (p : C.Tm Γ (I.id (U.type Γ) A B)) (σ : C.Sub Δ Γ) :
    C.Tm Δ (I.id (U.type Δ) (U.sub A σ) (U.sub B σ)) :=
  C.castTm ((I.id_sub A B σ).trans
    (I.id_congr (U.type_sub σ) (C.castTm_heq _ _).symm (C.castTm_heq _ _).symm))
    (C.tmSub p σ)

/-- The internal arrow induced by a universe path, with no equality reflection. -/
def pathArrow (F : FunctionTypes C) {Γ : C.Ctx} {A B : U.Code Γ}
    (p : C.Tm Γ (I.id (U.type Γ) A B)) : SmallHom U F A B :=
  F.lam (C.castTm (U.el_sub B C.fst).symm
    (U.transport I J (U.pathSub I p C.fst) (C.castTm (U.el_sub A C.fst) C.snd)))

end Universe

namespace EncodingFixpoints

variable (T : CoreTheory C) {Γ : C.Ctx}
    (D : WildEndofunctor T.univ T.functions T.identities Γ)

/-- The normalized source equation `μ◇ D i = D (◇ (μ◇ D) i)` in the universe. -/
def sizedMu_path : C.Tm (C.ext Γ (T.size.type Γ))
    (T.identities.id (T.univ.type (C.ext Γ (T.size.type Γ)))
      (sizedMu T.size T.products T.functions T.small T.ex T.recursion D)
      (D.obj C.fst (T.size.diamond T.small T.ex
        (sizedMu T.size T.products T.functions T.small T.ex T.recursion D)))) :=
  C.castTm (congrArg (T.identities.id _ _)
    (muStep_restriction T.size T.products T.functions T.small T.ex
      T.functionProducts T.smallSubstitution T.exSubstitution D
      (T.recursion.fix _ (muStep T.size T.products T.functions T.small T.ex D))))
    (T.products.unlam (sizedMu_fix_beta T.size T.products T.functions
      T.small T.ex T.recursion D))

/-- The normalized source equation `ν□ D i = D (□ (ν□ D) i)` in the universe. -/
def sizedNu_path : C.Tm (C.ext Γ (T.size.type Γ))
    (T.identities.id (T.univ.type (C.ext Γ (T.size.type Γ)))
      (sizedNu T.size T.products T.functions T.small T.all T.recursion D)
      (D.obj C.fst (T.size.box T.small T.all
        (sizedNu T.size T.products T.functions T.small T.all T.recursion D)))) :=
  C.castTm (congrArg (T.identities.id _ _)
    (nuStep_restriction T.size T.products T.functions T.small T.all
      T.functionProducts T.smallSubstitution T.allSubstitution D
      (T.recursion.fix _ (nuStep T.size T.products T.functions T.small T.all D))))
    (T.products.unlam (sizedNu_fix_beta T.size T.products T.functions
      T.small T.all T.recursion D))

/-- The sized inductive structure, obtained by reversing and decoding its universe equation. -/
def sizedMuAlgebra : Sized.AlgebraOver T D C.id where
  carrier := sizedMu T.size T.products T.functions T.small T.ex T.recursion D
  structureMap := by
    apply Sized.ofAt T.size T.functions T.small T.all T.functionProducts
    have hd : D.obj (C.comp C.id C.fst)
        (T.size.diamond T.small T.ex
          (sizedMu T.size T.products T.functions T.small T.ex T.recursion D)) =
        D.obj C.fst (T.size.diamond T.small T.ex
          (sizedMu T.size T.products T.functions T.small T.ex T.recursion D)) := by
      rw [C.id_comp]
    exact C.castTm (congrArg (fun A => T.functions.arr (T.univ.el A) _) hd).symm
      (T.univ.pathArrow T.identities T.identityElimination T.functions
        (InternalPath.symm T.identities T.identityElimination (sizedMu_path T D)))

/-- The sized coinductive structure, obtained by decoding its universe equation. -/
def sizedNuCoalgebra : Sized.CoalgebraOver T D C.id where
  carrier := sizedNu T.size T.products T.functions T.small T.all T.recursion D
  structureMap := by
    apply Sized.ofAt T.size T.functions T.small T.all T.functionProducts
    have hd : D.obj (C.comp C.id C.fst)
        (T.size.box T.small T.all
          (sizedNu T.size T.products T.functions T.small T.all T.recursion D)) =
        D.obj C.fst (T.size.box T.small T.all
          (sizedNu T.size T.products T.functions T.small T.all T.recursion D)) := by
      rw [C.id_comp]
    exact C.castTm (congrArg (fun B => T.functions.arr _ (T.univ.el B)) hd).symm
      (T.univ.pathArrow T.identities T.identityElimination T.functions (sizedNu_path T D))

/-- The source algebra on `μ D`, with `In = (∃ In◇) ∘ can⁻¹`. -/
def muAlgebra
    (h : C.Tm Γ (WeakCommutation.existsType T.size T.functions T.small
      T.identityElimination T.ex D.toInternalFunctorData)) : Algebra D where
  carrier := mu T.size T.products T.functions T.small T.ex T.recursion D
  structureMap := T.functions.compose
    (T.ex.map T.functions _ _
      (T.univ.pathArrow T.identities T.identityElimination T.functions
        (InternalPath.symm T.identities T.identityElimination (sizedMu_path T D))))
    (QuantifierAdjunction.existsInverse T D.toInternalFunctorData h
      (sizedMu T.size T.products T.functions T.small T.ex T.recursion D))

/-- The source coalgebra on `ν D`, with `Out = can⁻¹ ∘ (∀ Out□)`. -/
def nuCoalgebra
    (h : C.Tm Γ (WeakCommutation.allType T.size T.functions T.small T.identityElimination
      T.all T.sizeSubstitution T.smallSubstitution T.allSubstitution
      D.toInternalFunctorData)) : Coalgebra D where
  carrier := nu T.size T.products T.functions T.small T.all T.recursion D
  structureMap := T.functions.compose
    (QuantifierAdjunction.allInverse T D.toInternalFunctorData h
      (sizedNu T.size T.products T.functions T.small T.all T.recursion D))
    (T.all.map T.functions T.allSubstitution _ _
      (T.univ.pathArrow T.identities T.identityElimination T.functions (sizedNu_path T D)))

theorem muAlgebra_carrier
    (h : C.Tm Γ (WeakCommutation.existsType T.size T.functions T.small
      T.identityElimination T.ex D.toInternalFunctorData)) :
    (muAlgebra T D h).carrier = mu T.size T.products T.functions T.small T.ex T.recursion D :=
  rfl

theorem nuCoalgebra_carrier
    (h : C.Tm Γ (WeakCommutation.allType T.size T.functions T.small T.identityElimination
      T.all T.sizeSubstitution T.smallSubstitution T.allSubstitution
      D.toInternalFunctorData)) :
    (nuCoalgebra T D h).carrier =
      nu T.size T.products T.functions T.small T.all T.recursion D := rfl

end EncodingFixpoints

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_PolynomialV2 -/

/-!
# Internal polynomial operations

The object operation is the source code `Σ a : A, (B(a) → X)`. The morphism
operation is constructed by dependent pairing and postcomposition.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

variable {C : CwF.{u, v, w, t}}

namespace Universe

variable (U : Universe C)

theorem sub_id {Γ : C.Ctx} (A : U.Code Γ) : U.sub A C.id = A := by
  apply eq_of_heq
  exact (C.castTm_heq _ _).trans (C.tmSub_id A)

theorem sub_generic_heq {Γ Δ : C.Ctx} (σ : C.Sub Δ (C.ext Γ (U.type Γ))) :
    HEq (U.sub (U.generic Γ) σ) (C.tmSub C.snd σ) :=
  (C.castTm_heq _ _).trans
    (C.tmSub_heq (U.type_sub C.fst).symm (C.castTm_heq _ _) σ)

/-- The base substitution and its last universe code determine a context map. -/
theorem hom_ext {Γ Δ : C.Ctx} {f g : C.Sub Δ (C.ext Γ (U.type Γ))}
    (hfst : C.comp C.fst f = C.comp C.fst g)
    (hsnd : U.sub (U.generic Γ) f = U.sub (U.generic Γ) g) : f = g :=
  C.sub_ext hfst ((U.sub_generic_heq f).symm.trans
    ((heq_of_eq hsnd).trans (U.sub_generic_heq g)))

theorem extend_comp {Γ Δ Θ : C.Ctx} (σ : C.Sub Δ Γ) (A : U.Code Δ)
    (τ : C.Sub Θ Δ) :
    C.comp (U.extend σ A) τ = U.extend (C.comp σ τ) (U.sub A τ) := by
  apply U.hom_ext
  · rw [← C.assoc, U.extend_fst, U.extend_fst]
  · rw [← U.sub_comp, U.generic_sub_extend, U.generic_sub_extend]

theorem extend_generic {Γ : C.Ctx} : U.extend C.fst (U.generic Γ) = C.id := by
  apply U.hom_ext
  · rw [U.extend_fst, C.comp_id]
  · rw [U.generic_sub_extend, U.sub_id]

/-- Composition of lifts through a decoded type, with its code substitution
equality made explicit in the intermediate context. -/
theorem liftEl_comp_as {Γ Δ Θ : C.Ctx} (A : U.Code Γ)
    (σ : C.Sub Δ Γ) (τ : C.Sub Θ Δ) :
    C.comp (U.liftEl σ A)
      (U.liftElAs τ (U.sub A σ) (U.sub A (C.comp σ τ)) (U.sub_comp A σ τ)) =
      U.liftEl (C.comp σ τ) A := by
  apply C.sub_ext
  · rw [← C.assoc, U.liftEl_fst, C.assoc, U.liftElAs_fst,
      ← C.assoc, U.liftEl_fst]
  · exact (C.tmSub_comp C.snd (U.liftEl σ A) _).symm.trans
      ((C.tmSub_heq (U.liftEl_snd_type σ A) (U.liftEl_snd σ A) _).trans
        ((U.liftElAs_snd τ (U.sub A σ) _ _).trans (U.liftEl_snd _ A).symm))

end Universe

namespace GenericArrow

variable (U : Universe C) (F : FunctionTypes C) (Γ : C.Ctx)

/-- Specializing a generic arrow commutes with another substitution. -/
theorem specialize_comp {Δ Θ : C.Ctx} (σ : C.Sub Δ Γ) (X Y : U.Code Δ)
    (f : SmallHom U F X Y) (τ : C.Sub Θ Δ) :
    C.comp (specialize U F Γ σ X Y f) τ =
      specialize U F Γ (C.comp σ τ) (U.sub X τ) (U.sub Y τ) (SmallHom.sub U F f τ) := by
  apply C.sub_ext
  · rw [← C.assoc, specialize, C.pair_fst, specialize, C.pair_fst, codesSub,
      U.extend_comp, U.extend_comp]
    rfl
  · have ht : C.tySub
        (C.tySub (F.arr (U.el (domain U Γ)) (U.el (codomain U Γ))) C.fst)
          (specialize U F Γ σ X Y f) = F.arr (U.el X) (U.el Y) := by
      rw [C.tySub_comp, specialize, C.pair_fst]
      exact arrowType_sub U F Γ σ X Y
    have hh : HEq (C.tmSub C.snd (specialize U F Γ σ X Y f)) f :=
      (C.pair_snd _ _).trans (C.castTm_heq _ _)
    exact (C.tmSub_comp C.snd (specialize U F Γ σ X Y f) τ).symm.trans
      ((C.tmSub_heq ht hh τ).trans
        ((C.castTm_heq _ _).symm.trans
          ((C.castTm_heq _ _).symm.trans (C.pair_snd _ _).symm)))

/-- The generic arrow specializes to itself by the identity context map. -/
theorem specialize_generic :
    specialize U F Γ (projection U F Γ) (source U F Γ) (target U F Γ) (term U F Γ) = C.id := by
  have hbase : U.extend (base U Γ) (domain U Γ) = C.fst := by
    apply U.hom_ext
    · rw [U.extend_fst]
      rfl
    · rw [U.generic_sub_extend]
      rfl
  have hcodes : codesSub U Γ (base U Γ) (domain U Γ) (codomain U Γ) = C.id := by
    dsimp [codesSub]
    rw [hbase]
    exact U.extend_generic
  have hfst : codesSub U Γ (projection U F Γ) (source U F Γ) (target U F Γ) = C.fst := by
    dsimp [codesSub, projection, source, target]
    rw [← U.extend_comp, ← U.extend_comp]
    change C.comp (codesSub U Γ (base U Γ) (domain U Γ) (codomain U Γ)) C.fst = C.fst
    rw [hcodes, C.id_comp]
  apply C.sub_ext
  · rw [specialize, C.pair_fst, hfst, C.comp_id]
  · exact (C.pair_snd _ _).trans ((C.castTm_heq _ _).trans
      ((C.castTm_heq _ _).trans (C.tmSub_id C.snd).symm))

end GenericArrow

namespace Polynomial

variable {U : Universe C} {P : DependentProducts C} {S : DependentSums C}
    {I : IdentityTypes C} (K : SmallTypeConstructors C U P S I)

/-- The literal source polynomial `Σ a : A, (B(a) → X)`. -/
def code {Γ : C.Ctx} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A)))
    (X : U.Code Γ) : U.Code Γ :=
  K.sigma A (K.arrow B (U.sub X C.fst))

/-- Polynomial object action in any context over the parameter context. -/
def obj {Γ Δ : C.Ctx} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A)))
    (σ : C.Sub Δ Γ) (X : U.Code Δ) : U.Code Δ :=
  code K (U.sub A σ) (U.sub B (U.liftEl σ A)) X

/-- The polynomial object code is stable under contextual substitution. -/
theorem obj_sub (KS : SmallTypeSubstitution U P S I K) {Γ Δ Θ : C.Ctx}
    (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A)))
    (σ : C.Sub Δ Γ) (X : U.Code Δ) (τ : C.Sub Θ Δ) :
    U.sub (obj K A B σ X) τ = obj K A B (C.comp σ τ) (U.sub X τ) := by
  dsimp [obj, code]
  rw [K.sigma_sub_as KS _ _ τ _ (U.sub_comp A σ τ), K.arrow_sub KS,
    U.sub_comp B, U.liftEl_comp_as, U.sub_comp X, U.liftElAs_fst, ← U.sub_comp X]

/-- The source morphism action `(a, h) ↦ (a, f ∘ h)` at given parameters. -/
def action (F : FunctionTypes C) (FP : FunctionProductCompatibility F P)
    {Γ : C.Ctx} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A)))
    (X Y : U.Code Γ) (f : SmallHom U F X Y) :
    SmallHom U F (code K A B X) (code K A B Y) := by
  let BX := K.arrow B (U.sub X C.fst)
  let BY := K.arrow B (U.sub Y C.fst)
  let ph := @C.fst (C.ext Γ (U.el A)) (U.el BX)
  let σ := C.comp C.fst ph
  let a := C.castTm (C.tySub_comp (U.el A) C.fst ph) (C.tmSub C.snd ph)
  have hpair : C.pair σ a = ph :=
    (C.pair_unique σ a ph rfl (C.castTm_heq _ _).symm).symm
  have htype (T : U.Code Γ) :
      C.tySub (U.el (K.arrow B (U.sub T C.fst))) ph =
      F.arr (C.tySub (U.el B) ph) (C.tySub (U.el T) σ) := by
    exact (congrArg (fun V => C.tySub V ph) (K.el_arrow FP B (U.sub T C.fst))).trans
      ((F.arr_sub _ _ ph).trans
        (congrArg (F.arr (C.tySub (U.el B) ph))
          ((congrArg (fun V => C.tySub V ph) (U.el_sub T C.fst).symm).trans
            (C.tySub_comp _ _ _))))
  let h := C.castTm (htype X) C.snd
  let value := F.compose (F.sub f σ) h
  let b := C.castTm (congrArg (C.tySub (U.el BY)) hpair.symm)
    (C.castTm (htype Y).symm value)
  let paired := K.sigmaPairAt A BY σ a b
  let split := K.sigmaSplit A BX
  have hbase : C.tySub (C.tySub (U.el (code K A B Y)) σ) split =
      C.tySub (U.el (code K A B Y)) C.fst :=
    (C.tySub_comp _ σ split).trans
      (congrArg (C.tySub (U.el (code K A B Y))) (K.sigmaSplit_base A BX))
  exact F.lam (C.castTm hbase (C.tmSub paired split))

/-- The one generic polynomial action term, with parameters, both codes, and
the input function as contextual variables. -/
def genericMap (F : FunctionTypes C) (FP : FunctionProductCompatibility F P)
    {Γ : C.Ctx} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A))) :
    SmallHom U F
      (obj K A B (GenericArrow.projection U F Γ) (GenericArrow.source U F Γ))
      (obj K A B (GenericArrow.projection U F Γ) (GenericArrow.target U F Γ)) :=
  action K F FP (U.sub A (GenericArrow.projection U F Γ))
    (U.sub B (U.liftEl (GenericArrow.projection U F Γ) A))
    (GenericArrow.source U F Γ) (GenericArrow.target U F Γ) (GenericArrow.term U F Γ)

/-- The generic action has the required polynomial function type after
specializing its two codes and input arrow. -/
theorem genericMap_type_sub (F : FunctionTypes C)
    (KS : SmallTypeSubstitution U P S I K)
    {Γ Δ : C.Ctx} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A)))
    (σ : C.Sub Δ Γ) (X Y : U.Code Δ) (f : SmallHom U F X Y) :
    C.tySub (F.arr
      (U.el (obj K A B (GenericArrow.projection U F Γ) (GenericArrow.source U F Γ)))
      (U.el (obj K A B (GenericArrow.projection U F Γ) (GenericArrow.target U F Γ))))
      (GenericArrow.specialize U F Γ σ X Y f) =
      F.arr (U.el (obj K A B σ X)) (U.el (obj K A B σ Y)) := by
  rw [SmallHom.type_sub, obj_sub K KS, obj_sub K KS,
    GenericArrow.projection_sub, GenericArrow.source_sub, GenericArrow.target_sub]

/-- The internal polynomial map is substitution of the one literal generic
term `(a, h) ↦ (a, f ∘ h)`. -/
def map (F : FunctionTypes C) (FP : FunctionProductCompatibility F P)
    (KS : SmallTypeSubstitution U P S I K)
    {Γ Δ : C.Ctx} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A)))
    (σ : C.Sub Δ Γ) (X Y : U.Code Δ) (f : SmallHom U F X Y) :
    SmallHom U F (obj K A B σ X) (obj K A B σ Y) :=
  C.castTm (genericMap_type_sub K F KS A B σ X Y f)
    (C.tmSub (genericMap K F FP A B) (GenericArrow.specialize U F Γ σ X Y f))

/-- Substitution naturality follows from generic specialization, rather than
being supplied as an extra law about the polynomial action. -/
theorem map_sub (F : FunctionTypes C) (FP : FunctionProductCompatibility F P)
    (KS : SmallTypeSubstitution U P S I K)
    {Γ Δ Θ : C.Ctx} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A)))
    (σ : C.Sub Δ Γ) (X Y : U.Code Δ) (f : SmallHom U F X Y) (τ : C.Sub Θ Δ) :
    HEq (SmallHom.sub U F (map K F FP KS A B σ X Y f) τ)
      (map K F FP KS A B (C.comp σ τ) (U.sub X τ) (U.sub Y τ) (SmallHom.sub U F f τ)) := by
  exact (C.castTm_heq _ _).trans
    ((C.tmSub_heq (genericMap_type_sub K F KS A B σ X Y f).symm
      (C.castTm_heq _ _) τ).trans
      ((C.tmSub_comp (genericMap K F FP A B) (GenericArrow.specialize U F Γ σ X Y f) τ).trans
        ((congr_arg_heq (fun ρ => C.tmSub (genericMap K F FP A B) ρ)
          (GenericArrow.specialize_comp U F Γ σ X Y f τ)).trans
            (C.castTm_heq _ _).symm)))

/-- The polynomial's genuine internal object and morphism data. The two
functor laws are not assumed by this construction. -/
def data (F : FunctionTypes C) (FP : FunctionProductCompatibility F P)
    (KS : SmallTypeSubstitution U P S I K)
    {Γ : C.Ctx} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A))) :
    InternalFunctorData U F Γ where
  obj := obj K A B
  obj_sub := obj_sub K KS A B
  map := map K F FP KS A B
  map_sub := map_sub K F FP KS A B

/-- The generic map of the assembled data is exactly the literal polynomial
action, up to the explicitly recorded code transports. -/
theorem data_genericMap (F : FunctionTypes C) (FP : FunctionProductCompatibility F P)
    (KS : SmallTypeSubstitution U P S I K)
    {Γ : C.Ctx} (A : U.Code Γ) (B : U.Code (C.ext Γ (U.el A))) :
    HEq (data K F FP KS A B).genericMap (genericMap K F FP A B) := by
  change HEq (map K F FP KS A B _ _ _ _) _
  apply (C.castTm_heq _ _).trans
  rw [GenericArrow.specialize_generic]
  exact C.tmSub_id _

end Polynomial

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingLawsV2 -/

/-! Exact functor-law conclusions for the modal operations of Propositions 4 and 5.
They are predicates to prove about the constructed operations, not assumed fields. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory.Sized

universe u v w t

variable {C : CwF.{u,v,w,t}} (T : CoreTheory C) {Γ : C.Ctx}

/-- Equality of size-indexed morphisms is an internal identity term. -/
def HasPath {A B : T.univ.Code (C.ext Γ (T.size.type Γ))}
    (f g : Hom T.size T.small T.all A B) : Prop :=
  Nonempty (C.Tm Γ (T.identities.id (T.univ.el (homCode T.size T.small T.all A B)) f g))

/-- The source's two functor laws for a specified size-indexed action. -/
def PreservesIdComp
    (obj : T.univ.Code (C.ext Γ (T.size.type Γ)) →
      T.univ.Code (C.ext Γ (T.size.type Γ)))
    (map : ∀ {A B}, Hom T.size T.small T.all A B → Hom T.size T.small T.all (obj A) (obj B)) :
    Prop :=
  (∀ A, HasPath T (map (identity T.size T.functions T.small T.all T.functionProducts A))
    (identity T.size T.functions T.small T.all T.functionProducts (obj A))) ∧
  (∀ A B D (g : Hom T.size T.small T.all B D) (f : Hom T.size T.small T.all A B),
    HasPath T (map (compose T.size T.functions T.small T.all T.functionProducts g f))
      (compose T.size T.functions T.small T.all T.functionProducts (map g) (map f)))

/-- The constructed bounded-existential action satisfies the source functor laws. -/
def DiamondFunctorLaws (Γ : C.Ctx) : Prop :=
  PreservesIdComp T (T.size.diamond T.small T.ex (Γ := Γ))
    (diamondMap T.size T.functions T.small T.all T.functionProducts T.ex)

/-- The constructed bounded-universal action satisfies the source functor laws. -/
def BoxFunctorLaws (Γ : C.Ctx) : Prop :=
  PreservesIdComp T (T.size.box T.small T.all (Γ := Γ))
    (boxMap T.size T.functions T.small T.all T.functionProducts T.allSubstitution)

/-- The literal composite action `F[◇ -]` on morphisms. -/
def liftDiamondMap (F : WildEndofunctor T.univ T.functions T.identities Γ)
    {A B : T.univ.Code (C.ext Γ (T.size.type Γ))}
    (f : Hom T.size T.small T.all A B) :
    Hom T.size T.small T.all
      (liftObject T.size T.functions F (T.size.diamond T.small T.ex A))
      (liftObject T.size T.functions F (T.size.diamond T.small T.ex B)) :=
  liftMap T.size T.functions T.small T.all T.functionProducts F
    (diamondMap T.size T.functions T.small T.all T.functionProducts T.ex f)

/-- The literal composite action `F[□ -]` on morphisms. -/
def liftBoxMap (F : WildEndofunctor T.univ T.functions T.identities Γ)
    {A B : T.univ.Code (C.ext Γ (T.size.type Γ))}
    (f : Hom T.size T.small T.all A B) :
    Hom T.size T.small T.all
      (liftObject T.size T.functions F (T.size.box T.small T.all A))
      (liftObject T.size T.functions F (T.size.box T.small T.all B)) :=
  liftMap T.size T.functions T.small T.all T.functionProducts F
    (boxMap T.size T.functions T.small T.all T.functionProducts T.allSubstitution f)

/-- Functor laws for the prescribed composite `F[◇ -]`. -/
def LiftDiamondFunctorLaws (F : WildEndofunctor T.univ T.functions T.identities Γ) : Prop :=
  PreservesIdComp T (fun A ↦ liftObject T.size T.functions F (T.size.diamond T.small T.ex A))
    (liftDiamondMap T F)

/-- Functor laws for the prescribed composite `F[□ -]`. -/
def LiftBoxFunctorLaws (F : WildEndofunctor T.univ T.functions T.identities Γ) : Prop :=
  PreservesIdComp T (fun A ↦ liftObject T.size T.functions F (T.size.box T.small T.all A))
    (liftBoxMap T F)

end LaarakkerOttenVanDenBerg2026.V2.Theory.Sized

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingConclusionsV2 -/

/-! The source encoding conclusions. These predicates are targets to prove;
none is a field of the theory, a functor, or a size recursor. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

namespace CoreTheory

variable {C : CwF.{u,v,w,t}} (T : CoreTheory C) {Γ : C.Ctx}
    (D : WildEndofunctor T.univ T.functions T.identities Γ)

/-- The source existential weak-commutation hypothesis is one internal term
quantifying over every size family and inverting the prescribed canonical map. -/
abbrev WeaklyCommutesExists :=
  C.Tm Γ (WeakCommutation.existsType T.size T.functions T.small
    T.identityElimination T.ex D.toInternalFunctorData)

/-- The dual internally quantified weak-commutation hypothesis. -/
abbrev WeaklyCommutesAll :=
  C.Tm Γ (WeakCommutation.allType T.size T.functions T.small
    T.identityElimination T.all T.sizeSubstitution T.smallSubstitution
    T.allSubstitution D.toInternalFunctorData)

/-- Theorem 11's specified algebra is initial, and its specified structure map
is an internal half-adjoint equivalence. -/
def InductiveEncoding (h : T.WeaklyCommutesExists D) : Prop :=
  let A := EncodingFixpoints.muAlgebra T D h
  Nonempty (A.IsInitial T.products T.sums) ∧
  Nonempty (C.Tm Γ (InternalEquivalence.isEquiv T.functions T.products T.identities
    T.sums T.identityElimination A.structureMap))

/-- The dual conclusion for the specified coinductive coalgebra. -/
def CoinductiveEncoding (h : T.WeaklyCommutesAll D) : Prop :=
  let A := EncodingFixpoints.nuCoalgebra T D h
  Nonempty (A.IsTerminal T.products T.sums) ∧
  Nonempty (C.Tm Γ (InternalEquivalence.isEquiv T.functions T.products T.identities
    T.sums T.identityElimination A.structureMap))

/-- The polynomial corollary constructs the functor-law witnesses for the
literal polynomial object and morphism data, then proves weak commutation and
the canonical inductive encoding. No polynomial functor laws are assumed. -/
def PolynomialInductiveEncodings : Prop :=
  ∀ (Γ : C.Ctx) (A : T.univ.Code Γ) (B : T.univ.Code (C.ext Γ (T.univ.el A))),
    ∃ D : WildEndofunctor T.univ T.functions T.identities Γ,
      D.toInternalFunctorData = Polynomial.data T.small T.functions
        T.functionProducts T.smallSubstitution A B ∧
      ∃ h : T.WeaklyCommutesExists D, T.InductiveEncoding D h

/-- The corresponding polynomial coinductive corollary, for every small
branching family, including empty and infinitely branching signatures. -/
def PolynomialCoinductiveEncodings : Prop :=
  ∀ (Γ : C.Ctx) (A : T.univ.Code Γ) (B : T.univ.Code (C.ext Γ (T.univ.el A))),
    ∃ D : WildEndofunctor T.univ T.functions T.identities Γ,
      D.toInternalFunctorData = Polynomial.data T.small T.functions
        T.functionProducts T.smallSubstitution A B ∧
      ∃ h : T.WeaklyCommutesAll D, T.CoinductiveEncoding D h

end CoreTheory

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingFunctorialityV2 -/

/-!
# Prescribed morphism lifting and underlying-arrow functor laws

The lift types retain the full internal sigma type of algebra morphisms,
including its commuting-square path. They prescribe the underlying arrow by
an internal pointwise identity. Identity and composition laws below concern
the prescribed underlying arrows. They do not identify arbitrary choices of
commuting-square witnesses, or assert higher coherence absent from the paper's
wild-functor interface.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory

universe u v w t

variable {C : CwF.{u, v, w, t}}

namespace ArrowLifting

variable (T : CoreTheory C)

/-- The first-projection function of an internal dependent sum. -/
def firstProjection {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Tm Γ (T.functions.arr (T.sums.sigma A B) A) :=
  T.functions.lam (T.sums.fst (C.castTm (T.sums.sigma_sub A B C.fst) C.snd))

/-- A full morphism map with its prescribed underlying action. The pointwise
identity is itself an internal dependent product, rather than external equality. -/
def liftType {Γ : C.Ctx} (H₁ H₂ A₁ A₂ : C.Ty Γ)
    (forget₁ : C.Tm Γ (T.functions.arr H₁ A₁))
    (forget₂ : C.Tm Γ (T.functions.arr H₂ A₂))
    (action : C.Tm Γ (T.functions.arr A₁ A₂)) : C.Ty Γ :=
  let L := T.functions.arr H₁ H₂
  let p := @C.fst Γ L
  let l := C.castTm (T.functions.arr_sub H₁ H₂ p) C.snd
  let q := @C.fst (C.ext Γ L) (C.tySub H₁ p)
  T.sums.sigma L (T.products.pi (C.tySub H₁ p)
    (T.identities.id (C.tySub (C.tySub A₂ p) q)
      (T.functions.app (T.functions.sub (T.functions.sub forget₂ p) q)
        (T.functions.app (T.functions.sub l q) C.snd))
      (T.functions.app (T.functions.sub (T.functions.sub action p) q)
        (T.functions.app (T.functions.sub (T.functions.sub forget₁ p) q) C.snd))))

/-- The internal identity law for a fixed underlying-arrow action. -/
def identityType {Γ : C.Ctx} {A B : C.Ty Γ}
    (action : C.Tm Γ (T.functions.arr A B)) (sourceId : C.Tm Γ A) (targetId : C.Tm Γ B) :
    C.Ty Γ := T.identities.id B (T.functions.app action sourceId) targetId

/-- Substitute a curried binary operation, normalizing both arrow constructors. -/
def subBinary {Γ Δ : C.Ctx} {A B D : C.Ty Γ}
    (f : C.Tm Γ (T.functions.arr A (T.functions.arr B D))) (σ : C.Sub Δ Γ) :
    C.Tm Δ (T.functions.arr (C.tySub A σ) (T.functions.arr (C.tySub B σ) (C.tySub D σ))) :=
  C.castTm (congrArg (T.functions.arr (C.tySub A σ)) (T.functions.arr_sub B D σ))
    (T.functions.sub f σ)

/-- The internal composition law for a fixed action, on two generic arrows.
Both composition operations are supplied by named source constructions below. -/
def compositionType {Γ : C.Ctx} (A₁ B₁ D₁ A₂ B₂ D₂ : C.Ty Γ)
    (actionAB : C.Tm Γ (T.functions.arr A₁ A₂))
    (actionBD : C.Tm Γ (T.functions.arr B₁ B₂))
    (actionAD : C.Tm Γ (T.functions.arr D₁ D₂))
    (compose₁ : C.Tm Γ (T.functions.arr B₁ (T.functions.arr A₁ D₁)))
    (compose₂ : C.Tm Γ (T.functions.arr B₂ (T.functions.arr A₂ D₂))) : C.Ty Γ :=
  let p := @C.fst Γ B₁
  let q := @C.fst (C.ext Γ B₁) (C.tySub A₁ p)
  let g := C.tmSub (@C.snd Γ B₁) q
  let f := @C.snd (C.ext Γ B₁) (C.tySub A₁ p)
  let comp₁ := subBinary T (subBinary T compose₁ p) q
  let comp₂ := subBinary T (subBinary T compose₂ p) q
  T.products.pi B₁ (T.products.pi (C.tySub A₁ p)
    (T.identities.id (C.tySub (C.tySub D₂ p) q)
      (T.functions.app (T.functions.sub (T.functions.sub actionAD p) q)
        (T.functions.app (T.functions.app comp₁ g) f))
      (T.functions.app (T.functions.app comp₂
        (T.functions.app (T.functions.sub (T.functions.sub actionBD p) q) g))
        (T.functions.app (T.functions.sub (T.functions.sub actionAB p) q) f))))

/-- Actual curried composition of ordinary internal functions. -/
def functionComposition {Γ : C.Ctx} (A B D : C.Ty Γ) :
    C.Tm Γ (T.functions.arr (T.functions.arr B D)
      (T.functions.arr (T.functions.arr A B) (T.functions.arr A D))) := by
  let p := @C.fst Γ (T.functions.arr B D)
  let q := @C.fst (C.ext Γ (T.functions.arr B D)) (C.tySub (T.functions.arr A B) p)
  let g := T.functions.sub (C.castTm (T.functions.arr_sub B D p) C.snd) q
  have hf : C.tySub (C.tySub (T.functions.arr A B) p) q =
      T.functions.arr (C.tySub (C.tySub A p) q) (C.tySub (C.tySub B p) q) :=
    (congrArg (fun X => C.tySub X q) (T.functions.arr_sub A B p)).trans (T.functions.arr_sub _ _ q)
  have ho : C.tySub (C.tySub (T.functions.arr A D) p) q =
      T.functions.arr (C.tySub (C.tySub A p) q) (C.tySub (C.tySub D p) q) :=
    (congrArg (fun X => C.tySub X q) (T.functions.arr_sub A D p)).trans (T.functions.arr_sub _ _ q)
  let body := T.functions.compose g (C.castTm hf C.snd)
  exact T.functions.lam (C.castTm
    (T.functions.arr_sub (T.functions.arr A B) (T.functions.arr A D) p).symm
    (T.functions.lam (C.castTm ho.symm body)))

/-- Actual curried composition of size-indexed arrows. -/
def sizedComposition {Γ : C.Ctx}
    (A B D : T.univ.Code (C.ext Γ (T.size.type Γ))) :
    C.Tm Γ (T.functions.arr (T.univ.el (Sized.homCode T.size T.small T.all B D))
      (T.functions.arr (T.univ.el (Sized.homCode T.size T.small T.all A B))
        (T.univ.el (Sized.homCode T.size T.small T.all A D)))) := by
  let AB := T.univ.el (Sized.homCode T.size T.small T.all A B)
  let BD := T.univ.el (Sized.homCode T.size T.small T.all B D)
  let AD := T.univ.el (Sized.homCode T.size T.small T.all A D)
  let p := @C.fst Γ BD
  let q := @C.fst (C.ext Γ BD) (C.tySub AB p)
  let σ := C.comp p q
  let g := C.castTm (Sized.homType_sub T.size T.small T.all T.smallSubstitution T.allSubstitution B D σ)
    (C.castTm (C.tySub_comp BD p q) (C.tmSub C.snd q))
  let f := C.castTm (Sized.homType_sub T.size T.small T.all T.smallSubstitution T.allSubstitution A B σ)
    (C.castTm (C.tySub_comp AB p q) C.snd)
  let result := Sized.compose T.size T.functions T.small T.all T.functionProducts g f
  let body := C.castTm (C.tySub_comp AD p q).symm
    (C.castTm (Sized.homType_sub T.size T.small T.all T.smallSubstitution T.allSubstitution A D σ).symm result)
  exact T.functions.lam (C.castTm (T.functions.arr_sub AB AD p).symm (T.functions.lam body))

end ArrowLifting

namespace QuantifierAdjunction

variable (T : CoreTheory C)

/-- The prescribed existential action as one internal higher-order term. -/
def existsArrowAction {Γ : C.Ctx} (A B : T.univ.Code (C.ext Γ (T.size.type Γ))) :
    C.Tm Γ (T.functions.arr (T.univ.el (Sized.homCode T.size T.small T.all A B))
      (T.functions.arr (T.univ.el (T.ex.code A)) (T.univ.el (T.ex.code B)))) := by
  let σ := @C.fst Γ (T.univ.el (Sized.homCode T.size T.small T.all A B))
  let f := C.castTm (Sized.homType_sub T.size T.small T.all
    T.smallSubstitution T.allSubstitution A B σ) C.snd
  let result := T.ex.map T.functions (T.univ.sub A (T.size.lift σ)) (T.univ.sub B (T.size.lift σ))
    (Sized.eval T.size T.functions T.small T.all T.functionProducts f)
  have hout : C.tySub (T.functions.arr (T.univ.el (T.ex.code A)) (T.univ.el (T.ex.code B))) σ =
      T.functions.arr (T.univ.el (T.ex.code (T.univ.sub A (T.size.lift σ))))
        (T.univ.el (T.ex.code (T.univ.sub B (T.size.lift σ)))) := by
    rw [SmallHom.type_sub, T.exSubstitution.code_sub, T.exSubstitution.code_sub]
  exact T.functions.lam (C.castTm hout.symm result)

/-- The prescribed universal action as one internal higher-order term. -/
def allArrowAction {Γ : C.Ctx} (A B : T.univ.Code (C.ext Γ (T.size.type Γ))) :
    C.Tm Γ (T.functions.arr (T.univ.el (Sized.homCode T.size T.small T.all A B))
      (T.functions.arr (T.univ.el (T.all.code A)) (T.univ.el (T.all.code B)))) := by
  let σ := @C.fst Γ (T.univ.el (Sized.homCode T.size T.small T.all A B))
  let f := C.castTm (Sized.homType_sub T.size T.small T.all
    T.smallSubstitution T.allSubstitution A B σ) C.snd
  let result := T.all.map T.functions T.allSubstitution
    (T.univ.sub A (T.size.lift σ)) (T.univ.sub B (T.size.lift σ))
    (Sized.eval T.size T.functions T.small T.all T.functionProducts f)
  have hout : C.tySub (T.functions.arr (T.univ.el (T.all.code A)) (T.univ.el (T.all.code B))) σ =
      T.functions.arr (T.univ.el (T.all.code (T.univ.sub A (T.size.lift σ))))
        (T.univ.el (T.all.code (T.univ.sub B (T.size.lift σ)))) := by
    rw [SmallHom.type_sub, T.allSubstitution.code_sub, T.allSubstitution.code_sub]
  exact T.functions.lam (C.castTm hout.symm result)

/-- Reindexing a constant size family is again the constant reindexed family. -/
theorem constantFamily_sub {Γ Δ : C.Ctx} (A : T.univ.Code Γ) (σ : C.Sub Δ Γ) :
    T.univ.sub (T.univ.sub A (@C.fst Γ (T.size.type Γ))) (T.size.lift σ) =
      T.univ.sub (T.univ.sub A σ) (@C.fst Δ (T.size.type Δ)) := by
  rw [T.univ.sub_comp, T.univ.sub_comp, T.size.lift_fst]

/-- The prescribed constant-family action `f ↦ λ i, f`. -/
def constantArrowAction {Γ : C.Ctx} (A B : T.univ.Code Γ) :
    C.Tm Γ (T.functions.arr (T.functions.arr (T.univ.el A) (T.univ.el B))
      (T.univ.el (Sized.homCode T.size T.small T.all
        (T.univ.sub A C.fst) (T.univ.sub B C.fst)))) := by
  let σ := @C.fst Γ (T.functions.arr (T.univ.el A) (T.univ.el B))
  let f := C.castTm (SmallHom.type_sub T.univ T.functions A B σ) C.snd
  let result := Sized.ofAt T.size T.functions T.small T.all T.functionProducts
    (SmallHom.sub T.univ T.functions f C.fst)
  have hout : C.tySub (T.univ.el (Sized.homCode T.size T.small T.all
      (T.univ.sub A C.fst) (T.univ.sub B C.fst))) σ =
      T.univ.el (Sized.homCode T.size T.small T.all
        (T.univ.sub (T.univ.sub A σ) C.fst) (T.univ.sub (T.univ.sub B σ) C.fst)) := by
    rw [Sized.homType_sub T.size T.small T.all T.smallSubstitution T.allSubstitution,
      constantFamily_sub, constantFamily_sub]
  exact T.functions.lam (C.castTm hout.symm result)

/-- The existential action preserves the underlying identity arrow. -/
def existsIdentityType {Γ : C.Ctx} (A : T.univ.Code (C.ext Γ (T.size.type Γ))) : C.Ty Γ :=
  ArrowLifting.identityType T (existsArrowAction T A A)
    (Sized.identity T.size T.functions T.small T.all T.functionProducts A)
    (T.functions.identity (T.univ.el (T.ex.code A)))

/-- The universal action preserves the underlying identity arrow. -/
def allIdentityType {Γ : C.Ctx} (A : T.univ.Code (C.ext Γ (T.size.type Γ))) : C.Ty Γ :=
  ArrowLifting.identityType T (allArrowAction T A A)
    (Sized.identity T.size T.functions T.small T.all T.functionProducts A)
    (T.functions.identity (T.univ.el (T.all.code A)))

/-- The constant-family action preserves the underlying identity arrow. -/
def constantIdentityType {Γ : C.Ctx} (A : T.univ.Code Γ) : C.Ty Γ :=
  ArrowLifting.identityType T (constantArrowAction T A A)
    (T.functions.identity (T.univ.el A))
    (Sized.identity T.size T.functions T.small T.all T.functionProducts (T.univ.sub A C.fst))

/-- The existential action preserves pointwise composition of underlying arrows. -/
def existsCompositionType {Γ : C.Ctx}
    (A B D : T.univ.Code (C.ext Γ (T.size.type Γ))) : C.Ty Γ :=
  ArrowLifting.compositionType T _ _ _ _ _ _
    (existsArrowAction T A B) (existsArrowAction T B D) (existsArrowAction T A D)
    (ArrowLifting.sizedComposition T A B D)
    (ArrowLifting.functionComposition T (T.univ.el (T.ex.code A))
      (T.univ.el (T.ex.code B)) (T.univ.el (T.ex.code D)))

/-- The universal action preserves pointwise composition of underlying arrows. -/
def allCompositionType {Γ : C.Ctx}
    (A B D : T.univ.Code (C.ext Γ (T.size.type Γ))) : C.Ty Γ :=
  ArrowLifting.compositionType T _ _ _ _ _ _
    (allArrowAction T A B) (allArrowAction T B D) (allArrowAction T A D)
    (ArrowLifting.sizedComposition T A B D)
    (ArrowLifting.functionComposition T (T.univ.el (T.all.code A))
      (T.univ.el (T.all.code B)) (T.univ.el (T.all.code D)))

/-- The constant-family action preserves composition of underlying arrows. -/
def constantCompositionType {Γ : C.Ctx} (A B D : T.univ.Code Γ) : C.Ty Γ :=
  ArrowLifting.compositionType T _ _ _ _ _ _
    (constantArrowAction T A B) (constantArrowAction T B D) (constantArrowAction T A D)
    (ArrowLifting.functionComposition T (T.univ.el A) (T.univ.el B) (T.univ.el D))
    (ArrowLifting.sizedComposition T (T.univ.sub A C.fst)
      (T.univ.sub B C.fst) (T.univ.sub D C.fst))

variable {Γ : C.Ctx} (F : WildEndofunctor T.univ T.functions T.identities Γ)

/-- The existential action lifts to full algebra morphisms. Both source and
target retain their commuting-square witnesses. -/
def existsMorphismLiftType {Δ : C.Ctx} {σ : C.Sub Δ Γ}
    (h : C.Tm Δ (WeakCommutation.existsType T.size T.functions T.small
      T.identityElimination T.ex (F.toInternalFunctorData.reindex σ)))
    (A B : Sized.AlgebraOver T F σ) : C.Ty Δ :=
  ArrowLifting.liftType T (Sized.AlgebraOver.homType A B)
    (AlgebraOver.homType T.sums (existsAlgebra T F h A) (existsAlgebra T F h B))
    _ _ (ArrowLifting.firstProjection T _ _) (ArrowLifting.firstProjection T _ _)
    (existsArrowAction T A.carrier B.carrier)

/-- The universal action lifts to full coalgebra morphisms, including the
commuting-square witnesses. -/
def allMorphismLiftType {Δ : C.Ctx} {σ : C.Sub Δ Γ}
    (h : C.Tm Δ (WeakCommutation.allType T.size T.functions T.small T.identityElimination
      T.all T.sizeSubstitution T.smallSubstitution T.allSubstitution
      (F.toInternalFunctorData.reindex σ)))
    (A B : Sized.CoalgebraOver T F σ) : C.Ty Δ :=
  ArrowLifting.liftType T (Sized.CoalgebraOver.homType A B)
    (CoalgebraOver.homType T.sums (allCoalgebra T F h A) (allCoalgebra T F h B))
    _ _ (ArrowLifting.firstProjection T _ _) (ArrowLifting.firstProjection T _ _)
    (allArrowAction T A.carrier B.carrier)

/-- Constant-family formation lifts full algebra morphisms with prescribed
underlying action `f ↦ λ i, f`. -/
def constantAlgebraMorphismLiftType {Δ : C.Ctx} {σ : C.Sub Δ Γ}
    (A B : AlgebraOver F σ) : C.Ty Δ :=
  ArrowLifting.liftType T (AlgebraOver.homType T.sums A B)
    (Sized.AlgebraOver.homType (constantAlgebra T F A) (constantAlgebra T F B))
    _ _ (ArrowLifting.firstProjection T _ _) (ArrowLifting.firstProjection T _ _)
    (constantArrowAction T A.carrier B.carrier)

/-- Constant-family formation lifts full coalgebra morphisms with prescribed
underlying action `f ↦ λ i, f`. -/
def constantCoalgebraMorphismLiftType {Δ : C.Ctx} {σ : C.Sub Δ Γ}
    (A B : CoalgebraOver F σ) : C.Ty Δ :=
  ArrowLifting.liftType T (CoalgebraOver.homType T.sums A B)
    (Sized.CoalgebraOver.homType (constantCoalgebra T F A) (constantCoalgebra T F B))
    _ _ (ArrowLifting.firstProjection T _ _) (ArrowLifting.firstProjection T _ _)
    (constantArrowAction T A.carrier B.carrier)

end QuantifierAdjunction

end LaarakkerOttenVanDenBerg2026.V2.Theory

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingInfrastructureV2 -/

/-! The source's modal laws, sized universal properties and prescribed
morphism-lifting conclusions. Full morphisms retain their square witnesses;
identity/composition laws here concern their prescribed underlying arrows. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Theory.CoreTheory

universe u v w t
variable {C : CwF.{u,v,w,t}} (T : CoreTheory C)
open QuantifierAdjunction

/-- Identity and composition equations for the actual constant-family action. -/
def ConstantArrowLaws : Prop :=
  (∀ (Γ : C.Ctx) (A : T.univ.Code Γ), Nonempty (C.Tm Γ (constantIdentityType T A))) ∧
  (∀ (Γ : C.Ctx) (A B D : T.univ.Code Γ),
    Nonempty (C.Tm Γ (constantCompositionType T A B D)))

/-- Identity and composition equations for the actual existential action. -/
def ExistsArrowLaws : Prop :=
  (∀ (Γ : C.Ctx) (A : T.univ.Code (C.ext Γ (T.size.type Γ))),
    Nonempty (C.Tm Γ (existsIdentityType T A))) ∧
  (∀ (Γ : C.Ctx) (A B D : T.univ.Code (C.ext Γ (T.size.type Γ))),
    Nonempty (C.Tm Γ (existsCompositionType T A B D)))

/-- Identity and composition equations for the actual universal action. -/
def AllArrowLaws : Prop :=
  (∀ (Γ : C.Ctx) (A : T.univ.Code (C.ext Γ (T.size.type Γ))),
    Nonempty (C.Tm Γ (allIdentityType T A))) ∧
  (∀ (Γ : C.Ctx) (A B D : T.univ.Code (C.ext Γ (T.size.type Γ))),
    Nonempty (C.Tm Γ (allCompositionType T A B D)))

/-- Proposition 4, Lemmas 7–8 and the concrete lifting assertion of Proposition 10.
No natural adjunction or higher coherence of chosen square proofs is silently
identified with these specified morphism-lifting and underlying-arrow laws. -/
def InductiveInfrastructure : Prop :=
  (∀ Γ : C.Ctx, Sized.DiamondFunctorLaws T Γ) ∧
  (∀ (Γ : C.Ctx) (D : WildEndofunctor T.univ T.functions T.identities Γ),
    Sized.LiftDiamondFunctorLaws T D ∧
    Nonempty (EncodingFixpoints.sizedMuAlgebra T D).IsInitial) ∧
  T.ConstantArrowLaws ∧
  (∀ (Γ Δ : C.Ctx) (D : WildEndofunctor T.univ T.functions T.identities Γ)
    (σ : C.Sub Δ Γ) (A B : AlgebraOver D σ),
    Nonempty (C.Tm Δ (constantAlgebraMorphismLiftType T D A B))) ∧
  T.ExistsArrowLaws ∧
  (∀ (Γ Δ : C.Ctx) (D : WildEndofunctor T.univ T.functions T.identities Γ)
    (σ : C.Sub Δ Γ)
    (h : C.Tm Δ (WeakCommutation.existsType T.size T.functions T.small
      T.identityElimination T.ex (D.toInternalFunctorData.reindex σ)))
    (A B : Sized.AlgebraOver T D σ),
    Nonempty (C.Tm Δ (existsMorphismLiftType T D h A B)))

/-- The corresponding bounded-universal laws, sized terminality and concrete
constant/universal morphism lifts in Proposition 5, Lemmas 19–20 and Proposition 22. -/
def CoinductiveInfrastructure : Prop :=
  (∀ Γ : C.Ctx, Sized.BoxFunctorLaws T Γ) ∧
  (∀ (Γ : C.Ctx) (D : WildEndofunctor T.univ T.functions T.identities Γ),
    Sized.LiftBoxFunctorLaws T D ∧
    Nonempty (EncodingFixpoints.sizedNuCoalgebra T D).IsTerminal) ∧
  T.ConstantArrowLaws ∧
  (∀ (Γ Δ : C.Ctx) (D : WildEndofunctor T.univ T.functions T.identities Γ)
    (σ : C.Sub Δ Γ) (A B : CoalgebraOver D σ),
    Nonempty (C.Tm Δ (constantCoalgebraMorphismLiftType T D A B))) ∧
  T.AllArrowLaws ∧
  (∀ (Γ Δ : C.Ctx) (D : WildEndofunctor T.univ T.functions T.identities Γ)
    (σ : C.Sub Δ Γ)
    (h : C.Tm Δ (WeakCommutation.allType T.size T.functions T.small
      T.identityElimination T.all T.sizeSubstitution T.smallSubstitution T.allSubstitution
      (D.toInternalFunctorData.reindex σ)))
    (A B : Sized.CoalgebraOver T D σ),
    Nonempty (C.Tm Δ (allMorphismLiftType T D h A B)))

end LaarakkerOttenVanDenBerg2026.V2.Theory.CoreTheory


