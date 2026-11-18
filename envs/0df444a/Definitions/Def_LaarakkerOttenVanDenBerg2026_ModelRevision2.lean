-- Prove2me | Definitions.Def_LaarakkerOttenVanDenBerg2026_ModelRevision2
-- name    : LaarakkerOttenVanDenBerg2026_ModelRevision2
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-17T07:42:30.092102+00:00
-- url     : https://prove2.me/theorems/b5c79d19-d4f7-4a4c-84ab-81e60d24622d
-- title:
--   Kleene assemblies, PERs and the prescribed large-size model
-- statement:
--   The concrete realizability construction over Kleene's first algebra uses arbitrary partial recursive application. Assemblies have existential tracker evidence for morphisms and contextual terms. Small types are PERs over natural numbers; large types are assemblies, with realizer-preserving comparison maps and distinct small/large presentations where decoder equations require them. The code constructs PER/modest equivalence, modest reflection, products and sums, the universe, identity/J, base types, countable-ordinal sizes, both size quantifiers, and uniformly tracked well-founded recursion. FullModelSoundness is the remaining proposition that these pinned operations extend to a consistent interpretation of every source rule and all four parametricity axioms; it is not assumed or proved merely by defining it.
-- source:
--   Laarakker, Otten and van den Berg, Constructing (Co)inductive Types via Large Sizes, arXiv:2602.18921v2, Section 4 and Appendix C (explicit K1 restriction in Section 4.1), https://arxiv.org/abs/2602.18921v2

import Definitions.Def_LaarakkerOttenVanDenBerg2026_TheoryRevision2
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Part
import Mathlib.Data.Set.Basic
import Mathlib.SetTheory.Cardinal.Ordinal

/-! Generated from reviewed V2 modules by bundle_v2.py.
See the accompanying manifest for exact input hashes and source order. -/

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_KleeneV2 -/

/-!
# Kleene's first algebra for the assembly model

This file supplies the computation model used in Section 4.1 and Appendix C of
Laarakker, Otten, and van den Berg, *Constructing (Co)inductive Types via Large Sizes*
(2026). Application is evaluation in Mathlib's enumeration of **all** partial recursive
functions. It is a `Part ℕ`, so divergence is retained in the semantics.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Kleene

open Nat.Partrec (Code)

/-- The natural-number index of a partial recursive program. -/
def index (c : Code) : ℕ := Encodable.encode c

/-- Kleene application `e · n = φₑ(n)`. -/
def app (e n : ℕ) : Part ℕ := Code.eval (Denumerable.ofNat Code e) n

@[simp]
theorem app_index (c : Code) (n : ℕ) : app (index c) n = Code.eval c n := by
  simp [app, index]

/-- Every partial recursive partial function occurs in the chosen enumeration. -/
theorem exists_index {f : ℕ → Part ℕ} (hf : Nat.Partrec f) : ∃ e, app e = f := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  exact ⟨index c, by funext n; simpa using congrFun hc n⟩

/-- Universal evaluation is itself partial recursive. -/
theorem app_partrec : Partrec₂ app :=
  (Code.eval_part.comp ((Computable.ofNat Code).comp Computable.fst)
    Computable.snd).to₂

/-- An index for the identity function. -/
def idCode : ℕ := index Code.id

/-- An index for the constant function with value `a`. -/
def constCode (a : ℕ) : ℕ := index (Code.const a)

/-- Composition, with `e` evaluated first and `d` second. -/
def compCode (d e : ℕ) : ℕ :=
  index (Code.comp (Denumerable.ofNat Code d) (Denumerable.ofNat Code e))

/-- An index pairing the results of two programs. -/
def pairCode (d e : ℕ) : ℕ :=
  index (Code.pair (Denumerable.ofNat Code d) (Denumerable.ofNat Code e))

/-- An index for the first projection of the standard natural-number pairing. -/
def fstCode : ℕ := index Code.left

/-- An index for the second projection of the standard natural-number pairing. -/
def sndCode : ℕ := index Code.right

@[simp]
theorem app_idCode (n : ℕ) : app idCode n = Part.some n := by
  simp [idCode]

@[simp]
theorem app_constCode (a n : ℕ) : app (constCode a) n = Part.some a := by
  simp [constCode]

@[simp]
theorem app_compCode (d e n : ℕ) :
    app (compCode d e) n = (app e n).bind (app d) := by
  simp only [compCode, app_index]
  rfl

@[simp]
theorem app_pairCode (d e n : ℕ) :
    app (pairCode d e) n =
      (app d n).bind (fun a ↦ (app e n).map (Nat.pair a)) := by
  simp [pairCode, Code.eval, app, index, Seq.seq]

@[simp]
theorem app_fstCode (n : ℕ) : app fstCode n = Part.some n.unpair.1 := by
  simp [fstCode, Code.eval]

@[simp]
theorem app_sndCode (n : ℕ) : app sndCode n = Part.some n.unpair.2 := by
  simp [sndCode, Code.eval]

/-- Specialize the first input of a program on paired inputs. -/
def curryCode (e a : ℕ) : ℕ := index (Code.curry (Denumerable.ofNat Code e) a)

@[simp]
theorem app_curryCode (e a n : ℕ) : app (curryCode e a) n = app e (Nat.pair a n) := by
  simp [curryCode, app, index]

/-- The specializing operation is a total computable function (s-m-n). -/
theorem curryCode_computable : Computable₂ curryCode :=
  Computable.encode.comp
    (Code.primrec₂_curry.to_comp.comp ((Computable.ofNat Code).comp Computable.fst)
      Computable.snd)

/-- Every total computable function has an index for its total partial-function lift. -/
theorem exists_index_of_computable {f : ℕ → ℕ} (hf : Computable f) :
    ∃ e, ∀ n, app e n = Part.some (f n) := by
  obtain ⟨e, he⟩ := exists_index (Partrec.nat_iff.mp hf.partrec)
  exact ⟨e, fun n ↦ congrFun he n⟩

/-- A program for universal evaluation on paired inputs. -/
noncomputable def universalCode : ℕ :=
  (exists_index (Partrec₂.unpaired'.mpr app_partrec)).choose

@[simp]
theorem app_universalCode (e n : ℕ) :
    app universalCode (Nat.pair e n) = app e n := by
  have h := congrFun (exists_index (Partrec₂.unpaired'.mpr app_partrec)).choose_spec
    (Nat.pair e n)
  simpa [universalCode, Nat.unpaired] using h

/-- Apply the function computed by `d` to the value computed by `e`. -/
noncomputable def applyCode (d e : ℕ) : ℕ := compCode universalCode (pairCode d e)

@[simp]
theorem app_applyCode (d e n : ℕ) :
    app (applyCode d e) n =
      (app d n).bind (fun f ↦ (app e n).bind (app f)) := by
  simp [applyCode, Part.bind_assoc, Part.bind_map]

private theorem specialize_computable :
    Computable (fun n : ℕ ↦ curryCode n.unpair.1 n.unpair.2) :=
  curryCode_computable.comp (Computable.fst.comp Computable.unpair)
    (Computable.snd.comp Computable.unpair)

/-- A program computing s-m-n on paired numeric inputs. -/
noncomputable def specializeCode : ℕ :=
  (exists_index_of_computable specialize_computable).choose

@[simp]
theorem app_specializeCode (e n : ℕ) :
    app specializeCode (Nat.pair e n) = Part.some (curryCode e n) := by
  simpa [specializeCode] using
    (exists_index_of_computable specialize_computable).choose_spec (Nat.pair e n)

/-- A program producing the specialization of `d` at its input. -/
noncomputable def abstractCode (d : ℕ) : ℕ := curryCode specializeCode d

@[simp]
theorem app_abstractCode (d n : ℕ) :
    app (abstractCode d) n = Part.some (curryCode d n) := by
  simp [abstractCode]

/-- Rogers's fixed-point theorem, stated for numeric program indices. -/
theorem fixed_point {f : ℕ → ℕ} (hf : Computable f) : ∃ e, app (f e) = app e := by
  obtain ⟨c, hc⟩ := Code.fixed_point
    ((Computable.ofNat Code).comp (hf.comp Computable.encode))
  refine ⟨index c, ?_⟩
  funext n
  simpa [app, index] using congrFun hc n

/-- Kleene's second recursion theorem for the same numeric enumeration. -/
theorem fixed_point₂ {f : ℕ → ℕ → Part ℕ} (hf : Partrec₂ f) :
    ∃ e, app e = f e := by
  obtain ⟨c, hc⟩ := Code.fixed_point₂
    ((hf.comp (Computable.encode.comp Computable.fst) Computable.snd).to₂)
  refine ⟨index c, ?_⟩
  funext n
  rw [app_index]
  exact congrFun hc n

/-- Taking a constant-function index is computable. -/
theorem constCode_computable : Computable constCode :=
  Computable.encode.comp Code.primrec_const.to_comp

/-- Composition of indices is computable. -/
theorem compCode_computable : Computable₂ compCode :=
  Computable.encode.comp
    (Code.primrec₂_comp.to_comp.comp ((Computable.ofNat Code).comp Computable.fst)
      ((Computable.ofNat Code).comp Computable.snd))

/-- Pairing program results is a computable operation on indices. -/
theorem pairCode_computable : Computable₂ pairCode :=
  Computable.encode.comp
    (Code.primrec₂_pair.to_comp.comp ((Computable.ofNat Code).comp Computable.fst)
      ((Computable.ofNat Code).comp Computable.snd))

/-- The program construction used for application is computable. -/
theorem applyCode_computable : Computable₂ applyCode :=
  compCode_computable.comp (Computable.const universalCode) pairCode_computable

/-- A concrete K combinator in the enumeration. -/
noncomputable def kCode : ℕ := (exists_index_of_computable constCode_computable).choose

@[simp]
theorem app_kCode (a : ℕ) : app kCode a = Part.some (constCode a) :=
  (exists_index_of_computable constCode_computable).choose_spec a

/-- K is defined after one argument and discards its second argument. -/
theorem kCode_spec (a b : ℕ) :
    (app kCode a).bind (fun k ↦ app k b) = Part.some a := by
  simp

private theorem applyIndex_computable :
    Computable (fun n : ℕ ↦ applyCode n.unpair.1 n.unpair.2) :=
  applyCode_computable.comp (Computable.fst.comp Computable.unpair)
    (Computable.snd.comp Computable.unpair)

/-- A program producing the application of two indexed programs to their common input. -/
noncomputable def applyIndexCode : ℕ :=
  (exists_index_of_computable applyIndex_computable).choose

@[simp]
theorem app_applyIndexCode (a b : ℕ) :
    app applyIndexCode (Nat.pair a b) = Part.some (applyCode a b) := by
  simpa [applyIndexCode] using
    (exists_index_of_computable applyIndex_computable).choose_spec (Nat.pair a b)

/-- A concrete S combinator in the enumeration. -/
noncomputable def sCode : ℕ := abstractCode applyIndexCode

@[simp]
theorem app_sCode (a : ℕ) : app sCode a = Part.some (curryCode applyIndexCode a) := by
  simp [sCode]

/-- S is defined after its first two arguments. -/
theorem sCode_defined (a b : ℕ) :
    (app sCode a).bind (fun sa ↦ app sa b) = Part.some (applyCode a b) := by
  simp

/-- The S law, including equality of undefined computations on both sides. -/
theorem sCode_spec (a b c : ℕ) :
    ((app sCode a).bind (fun sa ↦ app sa b)).bind (fun sab ↦ app sab c) =
      (app a c).bind (fun ac ↦ (app b c).bind (app ac)) := by
  simp

/-- The uniform fixpoint combinator required in Proposition 16 / Appendix C. -/
theorem exists_fixCode : ∃ z : ℕ, ∀ f : ℕ, ∃ ff : ℕ,
    app z f = Part.some ff ∧
      ∀ a : ℕ, app ff a = (app f ff).bind (fun g ↦ app g a) := by
  let F (c p : ℕ) : Part ℕ :=
    (app p.unpair.1 (curryCode c p.unpair.1)).bind (fun g ↦ app g p.unpair.2)
  have hF : Partrec₂ F := by
    have first : Computable (fun p : ℕ × ℕ ↦ p.2.unpair.1) :=
      Computable.fst.comp (Computable.unpair.comp Computable.snd)
    have second : Computable (fun p : (ℕ × ℕ) × ℕ ↦ p.1.2.unpair.2) :=
      Computable.snd.comp
        (Computable.unpair.comp (Computable.snd.comp Computable.fst))
    exact ((app_partrec.comp first (curryCode_computable.comp Computable.fst first)).bind
      (app_partrec.comp Computable.snd second).to₂).to₂
  obtain ⟨c, hc⟩ := fixed_point₂ hF
  obtain ⟨z, hz⟩ := exists_index_of_computable
    (curryCode_computable.comp (Computable.const c) Computable.id)
  refine ⟨z, fun f ↦ ⟨curryCode c f, hz f, ?_⟩⟩
  intro a
  rw [app_curryCode, hc]
  simp [F]

/-- One fixed choice of the uniform fixpoint combinator. -/
noncomputable def fixCode : ℕ := exists_fixCode.choose

theorem fixCode_spec (f : ℕ) : ∃ ff : ℕ,
    app fixCode f = Part.some ff ∧
      ∀ a : ℕ, app ff a = (app f ff).bind (fun g ↦ app g a) :=
  exists_fixCode.choose_spec f

end LaarakkerOttenVanDenBerg2026.V2.Kleene

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_AssembliesV2 -/

/-!
Assemblies and their contextual operations over Kleene's first algebra.
Source: Laarakker, Otten and van den Berg (2026), Section 4.1 and Appendix C.1.
Trackers certify morphisms but are not part of their data. Application is partial.
This module concerns the semantic model; it adds no rules to the abstract type theory.
-/

namespace LaarakkerOttenVanDenBerg2026.V2

universe u v

/-- An assembly as in Definition 12. -/
structure Assembly where
  Carrier : Type u
  realises : ℕ → Carrier → Prop
  realised : ∀ x, ∃ n, realises n x

namespace Assembly

/-- Defined application with a realizing output, including the definedness obligation. -/
def Tracks {X Y : Assembly.{u}} (e : ℕ) (f : X.Carrier → Y.Carrier) : Prop :=
  ∀ x n, X.realises n x → ∃ m, m ∈ Kleene.app e n ∧ Y.realises m (f x)

/-- A morphism is a function with the mere existence of a tracker. -/
structure Hom (X Y : Assembly.{u}) where
  toFun : X.Carrier → Y.Carrier
  tracked : ∃ e, Tracks e toFun

@[ext] theorem Hom.ext {X Y : Assembly.{u}} {f g : Hom X Y}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f
  cases g
  congr
  exact funext h

/-- Identity is tracked by the identity partial recursive function. -/
def Hom.id (X : Assembly.{u}) : Hom X X where
  toFun := fun x ↦ x
  tracked := ⟨Kleene.idCode, fun x n hn ↦ ⟨n, by simp, hn⟩⟩

/-- Composition uses composition of partial recursive functions. -/
def Hom.comp {X Y Z : Assembly.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toFun := g.toFun ∘ f.toFun
  tracked := by
    obtain ⟨d, hd⟩ := f.tracked
    obtain ⟨e, he⟩ := g.tracked
    refine ⟨Kleene.compCode e d, ?_⟩
    intro x n hn
    obtain ⟨m, hm, hmx⟩ := hd x n hn
    obtain ⟨k, hk, hkx⟩ := he (f.toFun x) m hmx
    exact ⟨k, by rw [Kleene.app_compCode]; exact Part.mem_bind hm hk, hkx⟩

instance : CategoryTheory.Category Assembly.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext fun _ ↦ rfl
  comp_id _ := Hom.ext fun _ ↦ rfl
  assoc _ _ _ := Hom.ext fun _ ↦ rfl

/-- The full realizability relation, denoted ∇ in the paper. -/
def nabla (X : Type u) : Assembly.{u} where
  Carrier := X
  realises := fun _ _ ↦ True
  realised := fun _ ↦ ⟨0, trivial⟩

/-- The empty context, Appendix C.1. -/
def terminal : Assembly.{u} := nabla PUnit

/-- The unique map to the empty context. -/
def terminate (X : Assembly.{u}) : Hom X terminal where
  toFun := fun _ ↦ PUnit.unit
  tracked := ⟨Kleene.constCode 0, fun _ _ _ ↦ ⟨0, by simp, trivial⟩⟩

theorem terminate_unique {X : Assembly.{u}} (f : Hom X terminal) : f = terminate X :=
  Hom.ext fun _ ↦ @Subsingleton.elim PUnit _ _ _

/-- Semantic types are families of assemblies. -/
abbrev Ty (Γ : Assembly.{u}) := Γ.Carrier → Assembly.{u}

/-- The tracking condition for a dependent section. -/
def TracksSection {Γ : Assembly.{u}} (A : Ty Γ)
    (e : ℕ) (a : (γ : Γ.Carrier) → (A γ).Carrier) : Prop :=
  ∀ γ n, Γ.realises n γ → ∃ m, m ∈ Kleene.app e n ∧ (A γ).realises m (a γ)

/-- Semantic terms are dependent sections with a uniformly existing tracker. -/
structure Tm (Γ : Assembly.{u}) (A : Ty Γ) where
  toFun : (γ : Γ.Carrier) → (A γ).Carrier
  tracked : ∃ e, TracksSection A e toFun

@[ext] theorem Tm.ext {Γ : Assembly.{u}} {A : Ty Γ} {a b : Tm Γ A}
    (h : ∀ γ, a.toFun γ = b.toFun γ) : a = b := by
  cases a
  cases b
  congr
  exact funext h

/-- Substitution on semantic types is precomposition. -/
def substTy {Δ Γ : Assembly.{u}} (A : Ty Γ) (f : Hom Δ Γ) : Ty Δ := A ∘ f.toFun

/-- Substitution preserves tracked terms. -/
def substTm {Δ Γ : Assembly.{u}} {A : Ty Γ} (a : Tm Γ A) (f : Hom Δ Γ) :
    Tm Δ (substTy A f) where
  toFun := fun δ ↦ a.toFun (f.toFun δ)
  tracked := by
    obtain ⟨d, hd⟩ := f.tracked
    obtain ⟨e, he⟩ := a.tracked
    refine ⟨Kleene.compCode e d, ?_⟩
    intro δ n hn
    obtain ⟨m, hm, hmx⟩ := hd δ n hn
    obtain ⟨k, hk, hkx⟩ := he (f.toFun δ) m hmx
    exact ⟨k, by rw [Kleene.app_compCode]; exact Part.mem_bind hm hk, hkx⟩

theorem substTy_id {Γ : Assembly.{u}} (A : Ty Γ) : substTy A (Hom.id Γ) = A := rfl

theorem substTy_comp {Θ Δ Γ : Assembly.{u}} (A : Ty Γ) (f : Hom Θ Δ) (g : Hom Δ Γ) :
    substTy A (Hom.comp f g) = substTy (substTy A g) f := rfl

theorem substTm_id {Γ : Assembly.{u}} {A : Ty Γ} (a : Tm Γ A) :
    substTm a (Hom.id Γ) = a := Tm.ext fun _ ↦ rfl

theorem substTm_comp {Θ Δ Γ : Assembly.{u}} {A : Ty Γ} (a : Tm Γ A)
    (f : Hom Θ Δ) (g : Hom Δ Γ) :
    substTm a (Hom.comp f g) = substTm (substTm a g) f := Tm.ext fun _ ↦ rfl

/-- Context extension with the paired realizability relation of Definition 24. -/
def extend (Γ : Assembly.{u}) (A : Ty Γ) : Assembly.{u} where
  Carrier := (γ : Γ.Carrier) × (A γ).Carrier
  realises := fun n p ↦ Γ.realises (Nat.unpair n).1 p.1 ∧ (A p.1).realises (Nat.unpair n).2 p.2
  realised := by
    intro ⟨γ, a⟩
    obtain ⟨n, hn⟩ := Γ.realised γ
    obtain ⟨m, hm⟩ := (A γ).realised a
    exact ⟨Nat.pair n m, by simpa only [Nat.unpair_pair] using And.intro hn hm⟩

/-- The context projection is tracked by first projection on codes. -/
def projection (Γ : Assembly.{u}) (A : Ty Γ) : Hom (extend Γ A) Γ where
  toFun := Sigma.fst
  tracked := ⟨Kleene.fstCode, fun _ n hn ↦ ⟨(Nat.unpair n).1, by simp, hn.1⟩⟩

/-- The last variable is tracked by second projection on codes. -/
def lastVar (Γ : Assembly.{u}) (A : Ty Γ) :
    Tm (extend Γ A) (substTy A (projection Γ A)) where
  toFun := Sigma.snd
  tracked := ⟨Kleene.sndCode, fun _ n hn ↦ ⟨(Nat.unpair n).2, by simp, hn.2⟩⟩

/-- Extend a substitution by a term, as required by the CwF comprehension property. -/
def pairSubst {Δ Γ : Assembly.{u}} {A : Ty Γ} (f : Hom Δ Γ)
    (a : Tm Δ (substTy A f)) : Hom Δ (extend Γ A) where
  toFun := fun δ ↦ ⟨f.toFun δ, a.toFun δ⟩
  tracked := by
    obtain ⟨d, hd⟩ := f.tracked
    obtain ⟨e, he⟩ := a.tracked
    refine ⟨Kleene.pairCode d e, ?_⟩
    intro δ n hn
    obtain ⟨m, hm, hmx⟩ := hd δ n hn
    obtain ⟨k, hk, hkx⟩ := he δ n hn
    refine ⟨Nat.pair m k, ?_, ?_⟩
    · rw [Kleene.app_pairCode]
      exact Part.mem_bind hm (Part.mem_map _ hk)
    · simpa only [extend, Nat.unpair_pair, substTy, Function.comp_apply] using And.intro hmx hkx

theorem pairSubst_projection {Δ Γ : Assembly.{u}} {A : Ty Γ} (f : Hom Δ Γ)
    (a : Tm Δ (substTy A f)) : Hom.comp (pairSubst f a) (projection Γ A) = f :=
  Hom.ext fun _ ↦ rfl

theorem pairSubst_variable {Δ Γ : Assembly.{u}} {A : Ty Γ} (f : Hom Δ Γ)
    (a : Tm Δ (substTy A f)) : substTm (lastVar Γ A) (pairSubst f a) = a :=
  Tm.ext fun _ ↦ rfl

theorem pairSubst_eta {Δ Γ : Assembly.{u}} {A : Ty Γ} (f : Hom Δ (extend Γ A)) :
    pairSubst (Hom.comp f (projection Γ A)) (substTm (lastVar Γ A) f) = f :=
  Hom.ext fun _ ↦ rfl

theorem pairSubst_comp {Θ Δ Γ : Assembly.{u}} {A : Ty Γ} (f : Hom Δ Γ)
    (a : Tm Δ (substTy A f)) (g : Hom Θ Δ) :
    Hom.comp g (pairSubst f a) = pairSubst (Hom.comp g f) (substTm a g) :=
  Hom.ext fun _ ↦ rfl

/-- Large dependent product, Appendix C.5, Definition 30. -/
def pi (A : Assembly.{u}) (B : A.Carrier → Assembly.{u}) : Assembly.{u} where
  Carrier := { f : (a : A.Carrier) → (B a).Carrier //
    ∃ e, ∀ a n, A.realises n a → ∃ m, m ∈ Kleene.app e n ∧ (B a).realises m (f a) }
  realises := fun e f ↦ ∀ a n, A.realises n a →
    ∃ m, m ∈ Kleene.app e n ∧ (B a).realises m (f.val a)
  realised := fun f ↦ f.property

/-- The dependent product of contextual types. -/
def piTy {Γ : Assembly.{u}} (A : Ty Γ) (B : Ty (extend Γ A)) : Ty Γ :=
  fun γ ↦ pi (A γ) (fun a ↦ B ⟨γ, a⟩)

/-- Lambda abstraction of a tracked term; s-m-n supplies the contextual tracker. -/
def lambda {Γ : Assembly.{u}} {A : Ty Γ} {B : Ty (extend Γ A)}
    (b : Tm (extend Γ A) B) : Tm Γ (piTy A B) where
  toFun := fun γ ↦ ⟨fun a ↦ b.toFun ⟨γ, a⟩, by
    obtain ⟨e, he⟩ := b.tracked
    obtain ⟨n, hn⟩ := Γ.realised γ
    refine ⟨Kleene.curryCode e n, ?_⟩
    intro a m hm
    obtain ⟨k, hk, hkx⟩ := he ⟨γ, a⟩ (Nat.pair n m)
      (by simpa only [extend, Nat.unpair_pair] using And.intro hn hm)
    exact ⟨k, by simpa only [Kleene.app_curryCode] using hk, hkx⟩⟩
  tracked := by
    obtain ⟨e, he⟩ := b.tracked
    refine ⟨Kleene.abstractCode e, ?_⟩
    intro γ n hn
    refine ⟨Kleene.curryCode e n, by simp, ?_⟩
    intro a m hm
    obtain ⟨k, hk, hkx⟩ := he ⟨γ, a⟩ (Nat.pair n m)
      (by simpa only [extend, Nat.unpair_pair] using And.intro hn hm)
    exact ⟨k, by simpa only [Kleene.app_curryCode] using hk, hkx⟩

/-- Application of semantic terms, with definedness justified by both trackers. -/
def apply {Γ : Assembly.{u}} {A : Ty Γ} {B : Ty (extend Γ A)}
    (f : Tm Γ (piTy A B)) (a : Tm Γ A) :
    Tm Γ (substTy B (pairSubst (Hom.id Γ) a)) where
  toFun := fun γ ↦ (f.toFun γ).val (a.toFun γ)
  tracked := by
    obtain ⟨d, hd⟩ := f.tracked
    obtain ⟨e, he⟩ := a.tracked
    refine ⟨Kleene.applyCode d e, ?_⟩
    intro γ n hn
    obtain ⟨q, hq, hqf⟩ := hd γ n hn
    obtain ⟨m, hm, hma⟩ := he γ n hn
    obtain ⟨k, hk, hkb⟩ := hqf (a.toFun γ) m hma
    exact ⟨k, by rw [Kleene.app_applyCode]; exact Part.mem_bind hq (Part.mem_bind hm hk), hkb⟩

theorem apply_lambda {Γ : Assembly.{u}} {A : Ty Γ} {B : Ty (extend Γ A)}
    (b : Tm (extend Γ A) B) (a : Tm Γ A) :
    apply (lambda b) a = substTm b (pairSubst (Hom.id Γ) a) :=
  Tm.ext fun _ ↦ rfl

/-- Modesty is uniqueness of the element realized by a code. -/
def IsModest (A : Assembly.{u}) : Prop :=
  ∀ n x y, A.realises n x → A.realises n y → x = y

/-- Proposition 31: a dependent product with modest fibers is modest. -/
theorem pi_isModest (A : Assembly.{u}) (B : A.Carrier → Assembly.{u})
    (hB : ∀ a, IsModest (B a)) : IsModest (pi A B) := by
  intro e f g hf hg
  apply Subtype.ext
  funext a
  obtain ⟨n, hn⟩ := A.realised a
  obtain ⟨m, hm, hmf⟩ := hf a n hn
  obtain ⟨k, hk, hkg⟩ := hg a n hn
  have : m = k := Part.mem_unique hm hk
  subst k
  exact hB a m (f.val a) (g.val a) hmf hkg

end Assembly
end LaarakkerOttenVanDenBerg2026.V2

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_PERv2 -/

/-!
# Partial equivalence relations for the Laarakker–Otten–van den Berg model

This successor module follows Section 4.1 and Appendix C of the source. In
particular, the dependent product below uses partial Kleene application: output
values must exist before the codomain PER can relate them. No total operation is
substituted for the partial application of the model.
-/

namespace LaarakkerOttenVanDenBerg2026.V2

universe u

/-- A symmetric, transitive relation on the natural-number realizers (Definition 14). -/
structure PER where
  rel : ℕ → ℕ → Prop
  symm : ∀ {m n}, rel m n → rel n m
  trans : ∀ {l m n}, rel l m → rel m n → rel l n

namespace PER

variable (R : PER)

@[ext]
theorem ext {S : PER} (h : ∀ m n, R.rel m n ↔ S.rel m n) : R = S := by
  cases R with
  | mk rel symm trans =>
    cases S with
    | mk rel' symm' trans' =>
      have hr : rel = rel' := funext fun m => funext fun n => propext (h m n)
      cases hr
      rfl

theorem refl_left {m n : ℕ} (h : R.rel m n) : R.rel m m :=
  R.trans h (R.symm h)

theorem refl_right {m n : ℕ} (h : R.rel m n) : R.rel n n :=
  R.trans (R.symm h) h

/-- The support `dom(R)` of a PER. -/
def Domain := {n : ℕ // R.rel n n}

/-- Restricting a PER to its support gives an equivalence relation. -/
def domainSetoid : Setoid R.Domain where
  r m n := R.rel m.val n.val
  iseqv := ⟨fun m => m.property, fun h => R.symm h, fun h k => R.trans h k⟩

/-- The set of equivalence classes of supported realizers, `ℕ/R`. -/
def Quotient := _root_.Quotient R.domainSetoid

/-- The class represented by a supported realizer. -/
def classOf (n : ℕ) (hn : R.rel n n) : R.Quotient :=
  _root_.Quotient.mk R.domainSetoid ⟨n, hn⟩

theorem classOf_eq_iff {m n : ℕ} (hm : R.rel m m) (hn : R.rel n n) :
    R.classOf m hm = R.classOf n hn ↔ R.rel m n :=
  _root_.Quotient.eq

/-- A natural number realizes a class exactly when it belongs to that class. -/
def realises (n : ℕ) (x : R.Quotient) : Prop :=
  ∃ hn : R.rel n n, R.classOf n hn = x

theorem realised (x : R.Quotient) : ∃ n, R.realises n x := by
  induction x using _root_.Quotient.inductionOn with
  | h x => exact ⟨x.val, x.property, rfl⟩

theorem realises_classOf_iff {m n : ℕ} (hn : R.rel n n) :
    R.realises m (R.classOf n hn) ↔ R.rel m n := by
  constructor
  · rintro ⟨hm, h⟩
    exact (R.classOf_eq_iff hm hn).mp h
  · intro h
    exact ⟨R.refl_left h, (R.classOf_eq_iff _ _).mpr h⟩

theorem realises_self (n : ℕ) (hn : R.rel n n) :
    R.realises n (R.classOf n hn) := ⟨hn, rfl⟩

theorem modest {n : ℕ} {x y : R.Quotient}
    (hx : R.realises n x) (hy : R.realises n y) : x = y := by
  obtain ⟨hn, rfl⟩ := hx
  obtain ⟨_, hy⟩ := hy
  exact hy

theorem rel_of_realises {m n : ℕ} {x : R.Quotient}
    (hm : R.realises m x) (hn : R.realises n x) : R.rel m n := by
  obtain ⟨hnn, rfl⟩ := hn
  exact (R.realises_classOf_iff hnn).mp hm

theorem realises_of_rel {m n : ℕ} {x : R.Quotient}
    (h : R.rel m n) (hn : R.realises n x) : R.realises m x := by
  obtain ⟨hnn, rfl⟩ := hn
  exact (R.realises_classOf_iff hnn).mpr h

theorem rel_iff_common_class {m n : ℕ} :
    R.rel m n ↔ ∃ x : R.Quotient, R.realises m x ∧ R.realises n x := by
  constructor
  · intro h
    exact ⟨R.classOf n (R.refl_right h),
      (R.realises_classOf_iff _).mpr h, R.realises_self _ _⟩
  · rintro ⟨x, hm, hn⟩
    exact R.rel_of_realises hm hn

end PER

/-- The source's tracking condition for a map between PER quotients. -/
def PER.Tracks (R S : PER) (e : ℕ) (f : R.Quotient → S.Quotient) : Prop :=
  ∀ x n, R.realises n x → ∃ m ∈ Kleene.app e n, S.realises m (f x)

/-- A PER morphism consists of a function between quotient sets with the mere
existence of a tracker (Definition 14). -/
structure PERHom (R S : PER) where
  toFun : R.Quotient → S.Quotient
  tracked : ∃ e, R.Tracks S e toFun

namespace PERHom

@[ext]
theorem ext {R S : PER} {f g : PERHom R S} (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f
  cases g
  congr
  exact funext h

/-- The identity map has the identity program as tracker. -/
def id (R : PER) : PERHom R R where
  toFun := _root_.id
  tracked := ⟨Kleene.idCode, fun x n hn => ⟨n, by simp, hn⟩⟩

/-- Composition of PER morphisms is tracked by composition of programs. -/
def comp {R S T : PER} (f : PERHom R S) (g : PERHom S T) : PERHom R T where
  toFun := g.toFun ∘ f.toFun
  tracked := by
    obtain ⟨d, hd⟩ := f.tracked
    obtain ⟨e, he⟩ := g.tracked
    refine ⟨Kleene.compCode e d, ?_⟩
    intro x n hn
    obtain ⟨m, hm, hmx⟩ := hd x n hn
    obtain ⟨k, hk, hkx⟩ := he (f.toFun x) m hmx
    exact ⟨k, by rw [Kleene.app_compCode]; exact Part.mem_bind hm hk, hkx⟩

end PERHom

instance : CategoryTheory.Category PER where
  Hom := PERHom
  id := PERHom.id
  comp := PERHom.comp
  id_comp _ := PERHom.ext fun _ => rfl
  comp_id _ := PERHom.ext fun _ => rfl
  assoc _ _ _ := PERHom.ext fun _ => rfl

/-- The initial PER, interpreting the empty type (Definition 26). -/
def botPER : PER where
  rel _ _ := False
  symm h := h
  trans h _ := h

/-- The terminal PER, interpreting the unit type (Definition 27). -/
def unitPER : PER where
  rel _ _ := True
  symm _ := trivial
  trans _ _ := trivial

instance : IsEmpty botPER.Quotient where
  false x := by
    obtain ⟨n, hn, _⟩ := botPER.realised x
    exact hn

instance : Subsingleton unitPER.Quotient where
  allEq x y := by
    obtain ⟨n, hn, rfl⟩ := unitPER.realised x
    obtain ⟨m, hm, rfl⟩ := unitPER.realised y
    exact (unitPER.classOf_eq_iff hn hm).mpr trivial

instance : Inhabited unitPER.Quotient := ⟨unitPER.classOf 0 trivial⟩

/-- The Boolean PER has the two classes of pairs with first coordinate `0` or `1`
(Definition 28). The second coordinate is arbitrary. -/
def boolPER : PER where
  rel m n := m.unpair.1 = n.unpair.1 ∧ (m.unpair.1 = 0 ∨ m.unpair.1 = 1)
  symm := by
    rintro m n ⟨h, hm⟩
    exact ⟨h.symm, h ▸ hm⟩
  trans := by
    rintro l m n ⟨h, hl⟩ ⟨k, _⟩
    exact ⟨h.trans k, hl⟩

theorem boolPER_pair_iff (i j m n : ℕ) :
    boolPER.rel (Nat.pair i m) (Nat.pair j n) ↔ i = j ∧ (i = 0 ∨ i = 1) := by
  simp only [boolPER, Nat.unpair_pair]

/-- The false class of the Boolean PER. -/
def boolFalse : boolPER.Quotient :=
  boolPER.classOf (Nat.pair 0 0) ((boolPER_pair_iff 0 0 0 0).mpr ⟨rfl, Or.inl rfl⟩)

/-- The true class of the Boolean PER. -/
def boolTrue : boolPER.Quotient :=
  boolPER.classOf (Nat.pair 1 0) ((boolPER_pair_iff 1 1 0 0).mpr ⟨rfl, Or.inr rfl⟩)

theorem boolFalse_ne_boolTrue : boolFalse ≠ boolTrue := by
  intro h
  have hrel := (boolPER.classOf_eq_iff _ _).mp h
  have hzero := ((boolPER_pair_iff 0 1 0 0).mp hrel).1
  exact Nat.zero_ne_one hzero

theorem boolPER_realises_false (n : ℕ) :
    boolPER.realises n boolFalse ↔ n.unpair.1 = 0 := by
  rw [boolFalse, boolPER.realises_classOf_iff]
  simp only [boolPER, Nat.unpair_pair]
  exact ⟨And.left, fun h => ⟨h, Or.inl h⟩⟩

theorem boolPER_realises_true (n : ℕ) :
    boolPER.realises n boolTrue ↔ n.unpair.1 = 1 := by
  rw [boolTrue, boolPER.realises_classOf_iff]
  simp only [boolPER, Nat.unpair_pair]
  exact ⟨And.left, fun h => ⟨h, Or.inr h⟩⟩

theorem boolPER_cases (b : boolPER.Quotient) : b = boolFalse ∨ b = boolTrue := by
  obtain ⟨n, hn⟩ := boolPER.realised b
  have hnn : boolPER.rel n n := (boolPER.rel_of_realises hn hn)
  rcases hnn.2 with hzero | hone
  · exact Or.inl (boolPER.modest hn ((boolPER_realises_false n).mpr hzero))
  · exact Or.inr (boolPER.modest hn ((boolPER_realises_true n).mpr hone))

/-- Identity is the terminal PER when its two endpoints agree and the empty PER
otherwise (Definition 29). This definition does not require decidable equality. -/
def identityPER {α : Sort u} (a b : α) : PER where
  rel _ _ := a = b
  symm h := h
  trans h _ := h

theorem identityPER_rel_iff {α : Sort u} (a b : α) (m n : ℕ) :
    (identityPER a b).rel m n ↔ a = b := Iff.rfl

theorem identityPER_self {α : Sort u} (a : α) : identityPER a a = unitPER := by
  apply PER.ext
  intro m n
  exact ⟨fun _ => trivial, fun _ => rfl⟩

theorem identityPER_of_ne {α : Sort u} {a b : α} (h : a ≠ b) :
    identityPER a b = botPER := by
  apply PER.ext
  intro m n
  exact ⟨h, False.elim⟩

instance {α : Sort u} (a b : α) : Subsingleton (identityPER a b).Quotient where
  allEq x y := by
    obtain ⟨n, hn, rfl⟩ := (identityPER a b).realised x
    obtain ⟨m, hm, rfl⟩ := (identityPER a b).realised y
    exact ((identityPER a b).classOf_eq_iff hn hm).mpr hn

theorem identityPER_nonempty_iff {α : Sort u} (a b : α) :
    Nonempty (identityPER a b).Quotient ↔ a = b := by
  constructor
  · rintro ⟨x⟩
    obtain ⟨n, hn, _⟩ := (identityPER a b).realised x
    exact hn
  · intro h
    exact ⟨(identityPER a b).classOf 0 h⟩

/-- The small dependent sum of Definition 35. A related pair of first
coordinates determines a common class `a`, and the second coordinates must be
related in the fibre `B a`. -/
def smallSigmaPER (A : PER) (B : A.Quotient → PER) : PER where
  rel p q := ∃ a, A.realises p.unpair.1 a ∧ A.realises q.unpair.1 a ∧
    (B a).rel p.unpair.2 q.unpair.2
  symm := by
    rintro p q ⟨a, hp, hq, h⟩
    exact ⟨a, hq, hp, (B a).symm h⟩
  trans := by
    rintro p q r ⟨a, hp, hq, h⟩ ⟨b, hq', hr, k⟩
    have hab := A.modest hq hq'
    subst b
    exact ⟨a, hp, hr, (B a).trans h k⟩

/-- The literal paired-coordinate formula of Definition 35. -/
theorem smallSigmaPER_pair_iff (A : PER) (B : A.Quotient → PER)
    (m₁ n₁ m₂ n₂ : ℕ) :
    (smallSigmaPER A B).rel (Nat.pair m₁ n₁) (Nat.pair m₂ n₂) ↔
      ∃ h : A.rel m₁ m₂, (B (A.classOf m₁ (A.refl_left h))).rel n₁ n₂ := by
  change (∃ a, A.realises (Nat.unpair (Nat.pair m₁ n₁)).1 a ∧
    A.realises (Nat.unpair (Nat.pair m₂ n₂)).1 a ∧
    (B a).rel (Nat.unpair (Nat.pair m₁ n₁)).2 (Nat.unpair (Nat.pair m₂ n₂)).2) ↔ _
  simp only [Nat.unpair_pair]
  constructor
  · rintro ⟨a, hm₁, hm₂, h⟩
    obtain ⟨hm₁₁, rfl⟩ := hm₁
    exact ⟨A.rel_of_realises (A.realises_self m₁ hm₁₁) hm₂, h⟩
  · rintro ⟨h, hn⟩
    exact ⟨A.classOf m₁ (A.refl_left h), A.realises_self _ _,
      (A.realises_classOf_iff _).mpr (A.symm h), hn⟩

/-- The impredicative small product of Definition 32, over any realized carrier.
Both partial applications must converge; the outputs then lie in the same
codomain class. -/
def smallPiPER {α : Type u} (realises : ℕ → α → Prop) (B : α → PER) : PER where
  rel d e := ∀ a m n, realises m a → realises n a →
    ∃ u ∈ Kleene.app d m, ∃ v ∈ Kleene.app e n, (B a).rel u v
  symm := by
    intro d e h a m n hm hn
    obtain ⟨v, hv, u, hu, hrel⟩ := h a n m hn hm
    exact ⟨u, hu, v, hv, (B a).symm hrel⟩
  trans := by
    intro d e f h k a m n hm hn
    obtain ⟨u, hu, v, hv, huv⟩ := h a m m hm hm
    obtain ⟨v', hv', w, hw, hvw⟩ := k a m n hm hn
    have hvals := Part.mem_unique hv hv'
    subst v'
    exact ⟨u, hu, w, hw, (B a).trans huv hvw⟩

theorem smallPiPER_rel_iff {α : Type u} (realises : ℕ → α → Prop)
    (B : α → PER) (d e : ℕ) :
    (smallPiPER realises B).rel d e ↔
      ∀ a m n, realises m a → realises n a →
        ∃ u ∈ Kleene.app d m, ∃ v ∈ Kleene.app e n, (B a).rel u v := Iff.rfl

/-- A code tracks a dependent function into PER quotients exactly when all its
applications to input realizers converge to realizers of the required values. -/
def smallPiTracks {α : Type u} (realises : ℕ → α → Prop) (B : α → PER)
    (e : ℕ) (f : (a : α) → (B a).Quotient) : Prop :=
  ∀ a n, realises n a → ∃ m ∈ Kleene.app e n, (B a).realises m (f a)

/-- Two trackers of one dependent function are related in the small product. -/
theorem smallPiPER_rel_of_tracks {α : Type u} {realises : ℕ → α → Prop}
    {B : α → PER} {d e : ℕ} {f : (a : α) → (B a).Quotient}
    (hd : smallPiTracks realises B d f) (he : smallPiTracks realises B e f) :
    (smallPiPER realises B).rel d e := by
  intro a m n hm hn
  obtain ⟨u, hu, huf⟩ := hd a m hm
  obtain ⟨v, hv, hvf⟩ := he a n hn
  exact ⟨u, hu, v, hv, (B a).rel_of_realises huf hvf⟩

/-- Replacing a tracker by a related code preserves the dependent function. -/
theorem smallPiTracks_of_rel {α : Type u} {realises : ℕ → α → Prop}
    {B : α → PER} {d e : ℕ} {f : (a : α) → (B a).Quotient}
    (h : (smallPiPER realises B).rel d e) (he : smallPiTracks realises B e f) :
    smallPiTracks realises B d f := by
  intro a n hn
  obtain ⟨u, hu, v, hv, huv⟩ := h a n n hn hn
  obtain ⟨w, hw, hwf⟩ := he a n hn
  have hvw := Part.mem_unique hv hw
  subst w
  exact ⟨u, hu, (B a).realises_of_rel huv hwf⟩

/-- A single tracker determines at most one dependent function into PER quotients. -/
theorem smallPiTracks_unique {α : Type u} {realises : ℕ → α → Prop}
    (realised : ∀ a, ∃ n, realises n a) {B : α → PER} {e : ℕ}
    {f g : (a : α) → (B a).Quotient}
    (hf : smallPiTracks realises B e f) (hg : smallPiTracks realises B e g) : f = g := by
  funext a
  obtain ⟨n, hn⟩ := realised a
  obtain ⟨u, hu, huf⟩ := hf a n hn
  obtain ⟨v, hv, hvg⟩ := hg a n hn
  have huv := Part.mem_unique hu hv
  subst v
  exact (B a).modest huf hvg

/-- Every supported product code tracks a dependent function. -/
theorem smallPiPER_exists_tracked_function {α : Type u} {realises : ℕ → α → Prop}
    (realised : ∀ a, ∃ n, realises n a) {B : α → PER} {e : ℕ}
    (he : (smallPiPER realises B).rel e e) :
    ∃ f : (a : α) → (B a).Quotient, smallPiTracks realises B e f := by
  classical
  have hex : ∀ a, ∃ x : (B a).Quotient,
      ∀ n, realises n a → ∃ v ∈ Kleene.app e n, (B a).realises v x := by
    intro a
    obtain ⟨m, hm⟩ := realised a
    obtain ⟨u, hu, v, hv, huv⟩ := he a m m hm hm
    refine ⟨(B a).classOf u ((B a).refl_left huv), ?_⟩
    intro n hn
    obtain ⟨w, hw, z, hz, hwz⟩ := he a m n hm hn
    have huw := Part.mem_unique hu hw
    subst w
    exact ⟨z, hz, ((B a).realises_classOf_iff _).mpr ((B a).symm hwz)⟩
  choose f hf using hex
  exact ⟨f, hf⟩

/-- Definition 32's characterization: related codes track the same dependent
function, and conversely. The only domain assumption is the assembly axiom that
each element has some realizer. -/
theorem smallPiPER_rel_iff_common_function {α : Type u}
    {realises : ℕ → α → Prop} (realised : ∀ a, ∃ n, realises n a)
    {B : α → PER} (d e : ℕ) :
    (smallPiPER realises B).rel d e ↔
      ∃ f : (a : α) → (B a).Quotient,
        smallPiTracks realises B d f ∧ smallPiTracks realises B e f := by
  constructor
  · intro h
    obtain ⟨f, hf⟩ := smallPiPER_exists_tracked_function realised
      ((smallPiPER realises B).refl_left h)
    refine ⟨f, hf, ?_⟩
    intro a n hn
    obtain ⟨u, hu, huf⟩ := hf a n hn
    obtain ⟨u', hu', v, hv, huv⟩ := h a n n hn hn
    have huu := Part.mem_unique hu hu'
    subst u'
    exact ⟨v, hv, (B a).realises_of_rel ((B a).symm huv) huf⟩
  · rintro ⟨f, hd, he⟩
    exact smallPiPER_rel_of_tracks hd he

/-- The dependent morphisms represented by the small product. The existence of a
tracker is a proposition, rather than a chosen component of the function. -/
def SmallPiFunction {α : Type u} (realises : ℕ → α → Prop) (B : α → PER) :=
  {f : (a : α) → (B a).Quotient // ∃ e, smallPiTracks realises B e f}

theorem smallPiPER_exists_function_of_quotient {α : Type u}
    {realises : ℕ → α → Prop} (realised : ∀ a, ∃ n, realises n a)
    {B : α → PER} (q : (smallPiPER realises B).Quotient) :
    ∃ f : SmallPiFunction realises B,
      ∀ e, (smallPiPER realises B).realises e q → smallPiTracks realises B e f.val := by
  obtain ⟨e, he, rfl⟩ := (smallPiPER realises B).realised q
  obtain ⟨f, hf⟩ := smallPiPER_exists_tracked_function realised he
  refine ⟨⟨f, e, hf⟩, ?_⟩
  intro d hd
  exact smallPiTracks_of_rel ((smallPiPER realises B).realises_classOf_iff he |>.mp hd) hf

/-- Decode a product equivalence class as its uniquely determined dependent
function. Choice only selects a representative of this unique value. -/
noncomputable def smallPiDecode {α : Type u} {realises : ℕ → α → Prop}
    (realised : ∀ a, ∃ n, realises n a) {B : α → PER}
    (q : (smallPiPER realises B).Quotient) : SmallPiFunction realises B :=
  Classical.choose (smallPiPER_exists_function_of_quotient realised q)

theorem smallPiDecode_tracks {α : Type u} {realises : ℕ → α → Prop}
    (realised : ∀ a, ∃ n, realises n a) {B : α → PER}
    (q : (smallPiPER realises B).Quotient) (e : ℕ)
    (he : (smallPiPER realises B).realises e q) :
    smallPiTracks realises B e (smallPiDecode realised q).val :=
  Classical.choose_spec (smallPiPER_exists_function_of_quotient realised q) e he

/-- The product class of all codes tracking a given dependent morphism. -/
noncomputable def smallPiEncode {α : Type u} {realises : ℕ → α → Prop}
    {B : α → PER} (f : SmallPiFunction realises B) : (smallPiPER realises B).Quotient :=
  (smallPiPER realises B).classOf (Classical.choose f.property)
    (smallPiPER_rel_of_tracks (Classical.choose_spec f.property)
      (Classical.choose_spec f.property))

theorem smallPiEncode_realises_iff {α : Type u} {realises : ℕ → α → Prop}
    {B : α → PER} (f : SmallPiFunction realises B) (e : ℕ) :
    (smallPiPER realises B).realises e (smallPiEncode f) ↔
      smallPiTracks realises B e f.val := by
  rw [smallPiEncode, (smallPiPER realises B).realises_classOf_iff]
  exact ⟨fun h => smallPiTracks_of_rel h (Classical.choose_spec f.property),
    fun h => smallPiPER_rel_of_tracks h (Classical.choose_spec f.property)⟩

/-- The product PER quotient is equivalent to the set of dependent morphisms,
as asserted after Definition 32. -/
noncomputable def smallPiFunctionEquiv {α : Type u} {realises : ℕ → α → Prop}
    (realised : ∀ a, ∃ n, realises n a) (B : α → PER) :
    (smallPiPER realises B).Quotient ≃ SmallPiFunction realises B where
  toFun := smallPiDecode realised
  invFun := smallPiEncode
  left_inv q := by
    obtain ⟨e, he⟩ := (smallPiPER realises B).realised q
    exact (smallPiPER realises B).modest
      ((smallPiEncode_realises_iff _ e).mpr (smallPiDecode_tracks realised q e he)) he
  right_inv f := by
    apply Subtype.ext
    obtain ⟨e, he⟩ := f.property
    exact smallPiTracks_unique realised
      (smallPiDecode_tracks realised (smallPiEncode f) e
        ((smallPiEncode_realises_iff f e).mpr he)) he

/-- The source's universal quantifier is the small product over a codiscrete
domain such as the size assembly `∇ ω₁`. -/
def forallPER {ι : Type u} (B : ι → PER) : PER :=
  smallPiPER (fun _ _ => True) B

theorem forallPER_rel_iff {ι : Type u} (B : ι → PER) (d e : ℕ) :
    (forallPER B).rel d e ↔
      ∀ i m n, ∃ u ∈ Kleene.app d m, ∃ v ∈ Kleene.app e n, (B i).rel u v := by
  constructor
  · intro h i m n
    exact h i m n trivial trivial
  · intro h i m n _ _
    exact h i m n

end LaarakkerOttenVanDenBerg2026.V2

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_ModestV2 -/

/-!
Modest reflection of assemblies over Kleene's first algebra.
Source: Section 4.5 and Appendix C.9. The quotient is by the equivalence relation
generated by shared realizers. Its universal property is proved, not assumed.
-/

namespace LaarakkerOttenVanDenBerg2026.V2

universe u
open Assembly CategoryTheory

/-- A modest assembly. -/
structure Modest where
  toAssembly : Assembly.{u}
  modest : IsModest toAssembly

instance : Category Modest.{u} where
  Hom X Y := Assembly.Hom X.toAssembly Y.toAssembly
  id X := Assembly.Hom.id X.toAssembly
  comp := Assembly.Hom.comp
  id_comp _ := Assembly.Hom.ext fun _ ↦ rfl
  comp_id _ := Assembly.Hom.ext fun _ ↦ rfl
  assoc _ _ _ := Assembly.Hom.ext fun _ ↦ rfl

/-- The inclusion of modest sets into assemblies. -/
def modestInclusion : Modest.{u} ⥤ Assembly.{u} where
  obj := Modest.toAssembly
  map f := f

/-- Two elements sharing a realizer generate the modest-reflection equivalence. -/
def sharedRealiser (X : Assembly.{u}) (x y : X.Carrier) : Prop :=
  ∃ n, X.realises n x ∧ X.realises n y

/-- The source's quotient assembly M(X). -/
def reflectModest (X : Assembly.{u}) : Modest.{u} where
  toAssembly := {
    Carrier := Quot (sharedRealiser X)
    realises := fun n q ↦ ∃ x, Quot.mk (sharedRealiser X) x = q ∧ X.realises n x
    realised := by
      intro q
      induction q using Quot.inductionOn with
      | h x =>
        obtain ⟨n, hn⟩ := X.realised x
        exact ⟨n, x, rfl, hn⟩ }
  modest := by
    rintro n _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
    exact Quot.sound ⟨n, hx, hy⟩

/-- The quotient map is tracked by identity. -/
def reflectUnit (X : Assembly.{u}) : Assembly.Hom X (reflectModest X).toAssembly where
  toFun := Quot.mk (sharedRealiser X)
  tracked := ⟨Kleene.idCode, fun x n hn ↦ ⟨n, by simp, x, rfl, hn⟩⟩

private theorem sharedRealiser_map {X : Assembly.{u}} {Y : Modest.{u}}
    (f : Assembly.Hom X Y.toAssembly) {x y : X.Carrier} (h : sharedRealiser X x y) :
    f.toFun x = f.toFun y := by
  obtain ⟨n, hx, hy⟩ := h
  obtain ⟨e, he⟩ := f.tracked
  obtain ⟨m, hm, hmx⟩ := he x n hx
  obtain ⟨k, hk, hky⟩ := he y n hy
  have : m = k := Part.mem_unique hm hk
  subst k
  exact Y.modest m _ _ hmx hky

/-- Every map into a modest assembly factors through the reflection. -/
def reflectLift {X : Assembly.{u}} {Y : Modest.{u}}
    (f : Assembly.Hom X Y.toAssembly) :
    Assembly.Hom (reflectModest X).toAssembly Y.toAssembly where
  toFun := Quot.lift f.toFun (fun _ _ h ↦ sharedRealiser_map f h)
  tracked := by
    obtain ⟨e, he⟩ := f.tracked
    refine ⟨e, ?_⟩
    rintro q n ⟨x, rfl, hx⟩
    exact he x n hx

theorem reflectLift_unit {X : Assembly.{u}} {Y : Modest.{u}}
    (f : Assembly.Hom X Y.toAssembly) :
    Assembly.Hom.comp (reflectUnit X) (reflectLift f) = f :=
  Assembly.Hom.ext fun _ ↦ rfl

theorem reflectLift_unique {X : Assembly.{u}} {Y : Modest.{u}}
    (f : Assembly.Hom X Y.toAssembly)
    (g : Assembly.Hom (reflectModest X).toAssembly Y.toAssembly)
    (h : Assembly.Hom.comp (reflectUnit X) g = f) : g = reflectLift f := by
  apply Assembly.Hom.ext
  intro q
  induction q using Quot.inductionOn with
  | h x => exact congrArg (fun k : Assembly.Hom X Y.toAssembly ↦ k.toFun x) h

/-- M acts on maps by its universal property. -/
def modestReflection : Assembly.{u} ⥤ Modest.{u} where
  obj := reflectModest
  map {X Y} f := reflectLift (Assembly.Hom.comp f (reflectUnit Y))
  map_id X := by
    apply Assembly.Hom.ext
    intro q
    induction q using Quot.inductionOn with
    | h x => rfl
  map_comp f g := by
    apply Assembly.Hom.ext
    intro q
    induction q using Quot.inductionOn with
    | h x => rfl

/-- The hom-set equivalence underlying the reflection adjunction. -/
def reflectionHomEquiv (X : Assembly.{u}) (Y : Modest.{u}) :
    (modestReflection.obj X ⟶ Y) ≃ (X ⟶ modestInclusion.obj Y) where
  toFun g := Assembly.Hom.comp (reflectUnit X) g
  invFun := reflectLift
  left_inv g := (reflectLift_unique _ g rfl).symm
  right_inv := reflectLift_unit

/-- Lemma 17: modest reflection is left adjoint to inclusion. -/
def reflectionAdjunction : modestReflection.{u} ⊣ modestInclusion.{u} :=
  Adjunction.mkOfHomEquiv {
    homEquiv := reflectionHomEquiv
    homEquiv_naturality_left_symm := by
      intros
      apply Assembly.Hom.ext
      intro q
      induction q using Quot.inductionOn with
      | h x => rfl
    homEquiv_naturality_right := by
      intros
      apply Assembly.Hom.ext
      intro x
      rfl }

/-- A modest assembly determines the PER of its shared realizers. -/
def modestPER (X : Modest.{u}) : PER where
  rel m n := ∃ x, X.toAssembly.realises m x ∧ X.toAssembly.realises n x
  symm := by
    rintro m n ⟨x, hm, hn⟩
    exact ⟨x, hn, hm⟩
  trans := by
    rintro l m n ⟨x, hl, hm⟩ ⟨y, hm', hn⟩
    have : x = y := X.modest m x y hm hm'
    subst y
    exact ⟨x, hl, hn⟩

/-- U-truncation is reflection followed by the PER construction. -/
def truncatePER (X : Assembly.{u}) : PER := modestPER (reflectModest X)

/-- Dependent sums of modest assemblies are modest. -/
theorem extend_modest (X : Modest.{u}) (A : Ty X.toAssembly)
    (hA : ∀ x, IsModest (A x)) : IsModest (extend X.toAssembly A) := by
  rintro n ⟨x, a⟩ ⟨y, b⟩ ⟨hx, ha⟩ ⟨hy, hb⟩
  have hxy := X.modest (Nat.unpair n).1 x y hx hy
  subst y
  have hab := hA x (Nat.unpair n).2 a b ha hb
  subst b
  rfl

private theorem realises_cast {α : Type u} {A : α → Assembly.{u}}
    {x y : α} (h : x = y) (a : (A x).Carrier) (n : ℕ) :
    (A y).realises n (h ▸ a) ↔ (A x).realises n a := by
  cases h
  rfl

/-- Dependent elimination from the modest reflection into modest fibers.
The branch is an actual tracked term on the original assembly. -/
theorem exists_reflectElim (X : Assembly.{u}) (A : Ty (reflectModest X).toAssembly)
    (hA : ∀ q, IsModest (A q))
    (b : Tm X (substTy A (reflectUnit X))) :
    ∃ a : Tm (reflectModest X).toAssembly A, substTm a (reflectUnit X) = b := by
  let Y : Modest.{u} := ⟨extend (reflectModest X).toAssembly A,
    extend_modest (reflectModest X) A hA⟩
  let g : Assembly.Hom X Y.toAssembly := pairSubst (reflectUnit X) b
  let l : Assembly.Hom (reflectModest X).toAssembly Y.toAssembly := reflectLift g
  have hl : ∀ q, (l.toFun q).1 = q := by
    intro q
    induction q using Quot.inductionOn with
    | h x => rfl
  let a : Tm (reflectModest X).toAssembly A := {
    toFun := fun q ↦ (hl q) ▸ (l.toFun q).2
    tracked := by
      obtain ⟨e, he⟩ := l.tracked
      refine ⟨Kleene.compCode Kleene.sndCode e, ?_⟩
      intro q n hn
      obtain ⟨m, hm, hmy⟩ := he q n hn
      refine ⟨(Nat.unpair m).2, ?_, ?_⟩
      · rw [Kleene.app_compCode]
        exact Part.mem_bind hm (by simp)
      · exact (realises_cast (hl q) (l.toFun q).2 (Nat.unpair m).2).mpr hmy.2 }
  refine ⟨a, ?_⟩
  apply Tm.ext
  intro x
  rfl

/-- A dependent reflected section is determined by its values before quotienting. -/
theorem reflectElim_unique (X : Assembly.{u}) (A : Ty (reflectModest X).toAssembly)
    (a b : Tm (reflectModest X).toAssembly A)
    (h : substTm a (reflectUnit X) = substTm b (reflectUnit X)) : a = b := by
  apply Tm.ext
  intro q
  induction q using Quot.inductionOn with
  | h x => exact congrArg (fun t : Tm X (substTy A (reflectUnit X)) ↦ t.toFun x) h

end LaarakkerOttenVanDenBerg2026.V2

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_PEREquivalenceV2 -/

/-!
# The equivalence of PERs and modest assemblies

This is the categorical equivalence of Lemma 15. Its inclusion sends a PER to
the modest assembly of its quotient classes. Essential surjectivity is witnessed
by the source's shared-realizer PER `modestPER X`, and both comparison maps are
tracked by the identity program.
-/

namespace LaarakkerOttenVanDenBerg2026.V2

open CategoryTheory

universe u

/-- The assembly associated to a PER, lifted to the context universe. -/
def perAssembly (R : PER) : Assembly.{u} where
  Carrier := ULift.{u} R.Quotient
  realises n x := R.realises n x.down
  realised x := R.realised x.down

theorem perAssembly_modest (R : PER) : Assembly.IsModest (perAssembly.{u} R) := by
  intro n x y hx hy
  exact ULift.ext _ _ (R.modest hx hy)

/-- The full and faithful inclusion of PERs as modest assemblies. -/
def perToModest : PER ⥤ Modest.{0} where
  obj R := {
    toAssembly := {
      Carrier := R.Quotient
      realises := R.realises
      realised := R.realised }
    modest := fun _ _ _ hx hy => R.modest hx hy }
  map f := {
    toFun := f.toFun
    tracked := f.tracked }
  map_id _ := Assembly.Hom.ext fun _ => rfl
  map_comp _ _ := Assembly.Hom.ext fun _ => rfl

instance : perToModest.Full where
  map_surjective f := ⟨⟨f.toFun, f.tracked⟩, Assembly.Hom.ext fun _ => rfl⟩

instance : perToModest.Faithful where
  map_injective {R S} f g h := by
    apply PERHom.ext
    intro x
    exact congrArg (fun k : Assembly.Hom (perToModest.obj R).toAssembly
      (perToModest.obj S).toAssembly => k.toFun x) h

/-- Decode a class of realizers of a modest assembly. Modesty makes the result
independent of the chosen realizer and the chosen element it realizes. -/
noncomputable def modestPERDecode (X : Modest.{u}) :
    (modestPER X).Quotient → X.toAssembly.Carrier :=
  _root_.Quotient.lift (fun n : (modestPER X).Domain => Classical.choose n.property)
    (by
      intro m n h
      obtain ⟨x, hm, hn⟩ := h
      exact (X.modest m.val _ x (Classical.choose_spec m.property).1 hm).trans
        (X.modest n.val x _ hn (Classical.choose_spec n.property).1))

theorem modestPERDecode_realises (X : Modest.{u})
    {q : (modestPER X).Quotient} {n : ℕ} (hn : (modestPER X).realises n q) :
    X.toAssembly.realises n (modestPERDecode X q) := by
  obtain ⟨hnn, rfl⟩ := hn
  exact (Classical.choose_spec hnn).1

/-- An element of a modest assembly determines the equivalence class of all its
realizers in the source's PER. -/
noncomputable def modestPEREncode (X : Modest.{u}) (x : X.toAssembly.Carrier) :
    (modestPER X).Quotient :=
  (modestPER X).classOf (Classical.choose (X.toAssembly.realised x))
    ⟨x, Classical.choose_spec (X.toAssembly.realised x),
      Classical.choose_spec (X.toAssembly.realised x)⟩

theorem modestPEREncode_realises_iff (X : Modest.{u}) (x : X.toAssembly.Carrier) (n : ℕ) :
    (modestPER X).realises n (modestPEREncode X x) ↔ X.toAssembly.realises n x := by
  have hclass : (modestPER X).realises n (modestPEREncode X x) ↔
      (modestPER X).rel n (Classical.choose (X.toAssembly.realised x)) :=
    (modestPER X).realises_classOf_iff _
  apply hclass.trans
  constructor
  · rintro ⟨y, hny, hmy⟩
    have hxy := X.modest _ y x hmy (Classical.choose_spec (X.toAssembly.realised x))
    exact hxy ▸ hny
  · intro hnx
    exact ⟨x, hnx, Classical.choose_spec (X.toAssembly.realised x)⟩

theorem modestPERDecode_encode (X : Modest.{u}) (x : X.toAssembly.Carrier) :
    modestPERDecode X (modestPEREncode X x) = x := by
  obtain ⟨n, hn⟩ := X.toAssembly.realised x
  exact X.modest n _ x
    (modestPERDecode_realises X ((modestPEREncode_realises_iff X x n).mpr hn)) hn

theorem modestPEREncode_decode (X : Modest.{u}) (q : (modestPER X).Quotient) :
    modestPEREncode X (modestPERDecode X q) = q := by
  obtain ⟨n, hn⟩ := (modestPER X).realised q
  exact (modestPER X).modest
    ((modestPEREncode_realises_iff X _ n).mpr (modestPERDecode_realises X hn)) hn

/-- The canonical identity-tracked isomorphism from the modest assembly of the
source's PER back to the given modest assembly. -/
noncomputable def modestPERIso (X : Modest.{0}) :
    perToModest.obj (modestPER X) ≅ X where
  hom := {
    toFun := modestPERDecode X
    tracked := ⟨Kleene.idCode, fun q n hn =>
      ⟨n, by simp, modestPERDecode_realises X hn⟩⟩ }
  inv := {
    toFun := modestPEREncode X
    tracked := ⟨Kleene.idCode, fun x n hn =>
      ⟨n, by simp, (modestPEREncode_realises_iff X x n).mpr hn⟩⟩ }
  hom_inv_id := Assembly.Hom.ext (modestPEREncode_decode X)
  inv_hom_id := Assembly.Hom.ext (modestPERDecode_encode X)

instance : perToModest.EssSurj where
  mem_essImage X := ⟨modestPER X, ⟨modestPERIso X⟩⟩

instance : perToModest.IsEquivalence where

/-- Lemma 15: the categories of PERs and modest sets are equivalent. -/
noncomputable def perModestEquivalence : PER ≌ Modest.{0} :=
  perToModest.asEquivalence

/-- The PER inclusion in assemblies of any universe. The lift changes only the
carrier's universe, preserving its realizing natural numbers. -/
def liftedPerToModest : PER ⥤ Modest.{u} where
  obj R := ⟨perAssembly R, perAssembly_modest R⟩
  map f := {
    toFun x := ULift.up (f.toFun x.down)
    tracked := by
      obtain ⟨e, he⟩ := f.tracked
      exact ⟨e, fun x n hn => he x.down n hn⟩ }
  map_id _ := Assembly.Hom.ext fun _ => rfl
  map_comp _ _ := Assembly.Hom.ext fun _ => rfl

instance : liftedPerToModest.{u}.Full where
  map_surjective {R S} f := by
    refine ⟨{
      toFun := fun x => (f.toFun (ULift.up x)).down
      tracked := ?_ }, ?_⟩
    · obtain ⟨e, he⟩ := f.tracked
      exact ⟨e, fun x n hn => he (ULift.up x) n hn⟩
    · exact Assembly.Hom.ext fun _ => rfl

instance : liftedPerToModest.{u}.Faithful where
  map_injective {R S} f g h := by
    apply PERHom.ext
    intro x
    exact congrArg (fun k : Assembly.Hom (perAssembly.{u} R) (perAssembly.{u} S) =>
      (k.toFun (ULift.up x)).down) h

/-- Every modest assembly, including those with large carriers, is isomorphic
to the assembly of the source's PER. -/
noncomputable def liftedModestPERIso (X : Modest.{u}) :
    liftedPerToModest.obj (modestPER X) ≅ X where
  hom := {
    toFun q := modestPERDecode X q.down
    tracked := ⟨Kleene.idCode, fun q n hn =>
      ⟨n, by simp, modestPERDecode_realises X hn⟩⟩ }
  inv := {
    toFun x := ULift.up (modestPEREncode X x)
    tracked := ⟨Kleene.idCode, fun x n hn =>
      ⟨n, by simp, (modestPEREncode_realises_iff X x n).mpr hn⟩⟩ }
  hom_inv_id := Assembly.Hom.ext fun q =>
    ULift.ext _ _ (modestPEREncode_decode X q.down)
  inv_hom_id := Assembly.Hom.ext (modestPERDecode_encode X)

instance : liftedPerToModest.{u}.EssSurj where
  mem_essImage X := ⟨modestPER X, ⟨liftedModestPERIso X⟩⟩

instance : liftedPerToModest.{u}.IsEquivalence where

/-- The source's PER–modest-set equivalence, without a bound on the universe of
the modest assembly's carrier. -/
noncomputable def liftedPerModestEquivalence : PER ≌ Modest.{u} :=
  liftedPerToModest.asEquivalence

end LaarakkerOttenVanDenBerg2026.V2

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_SmallTypesV2 -/

/-!
# Small-product and small-sum comparison isomorphisms

Appendix C.5–C.6 compares the PER and assembly interpretations of dependent
products and sums. These comparisons are genuine assembly isomorphisms with
identity trackers. They are not equalities of the two carrier representations.
As the source explicitly notes, strict decoding equations require a further
case distinction in the interpretation of the type constructors.
-/

namespace LaarakkerOttenVanDenBerg2026.V2

open CategoryTheory

universe u

/-- The small product decodes to an assembly isomorphic to the assembly of
dependent morphisms. The maps preserve the realizing codes themselves. -/
noncomputable def smallPiAssemblyIso (A : Assembly.{0}) (B : A.Carrier → PER) :
    (perToModest.obj (smallPiPER A.realises B)).toAssembly ≅
      Assembly.pi A (fun a => (perToModest.obj (B a)).toAssembly) where
  hom := {
    toFun := smallPiDecode A.realised
    tracked := ⟨Kleene.idCode, fun q n hn =>
      ⟨n, by simp, smallPiDecode_tracks A.realised q n hn⟩⟩ }
  inv := {
    toFun := smallPiEncode
    tracked := ⟨Kleene.idCode, fun f n hn =>
      ⟨n, by simp, (smallPiEncode_realises_iff f n).mpr hn⟩⟩ }
  hom_inv_id := Assembly.Hom.ext (smallPiFunctionEquiv A.realised B).left_inv
  inv_hom_id := Assembly.Hom.ext (smallPiFunctionEquiv A.realised B).right_inv

/-- Pointwise lifting does not change the dependent function's tracker. -/
def smallPiLiftedFunctionEquiv (A : Assembly.{u}) (B : A.Carrier → PER) :
    SmallPiFunction A.realises B ≃
      (Assembly.pi A (fun a => perAssembly.{u} (B a))).Carrier where
  toFun f := ⟨fun a => ULift.up (f.val a), f.property⟩
  invFun f := ⟨fun a => (f.val a).down, f.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The comparison of product carriers is valid over large domains too. -/
noncomputable def smallPiLiftedCarrierEquiv (A : Assembly.{u}) (B : A.Carrier → PER) :
    (perAssembly.{u} (smallPiPER A.realises B)).Carrier ≃
      (Assembly.pi A (fun a => perAssembly.{u} (B a))).Carrier :=
  Equiv.ulift.trans ((smallPiFunctionEquiv A.realised B).trans
    (smallPiLiftedFunctionEquiv A B))

/-- The small-product comparison for arbitrary universe levels, in particular
for the large domain `∇ ω₁` used by universal size quantification. -/
noncomputable def smallPiLiftedAssemblyIso (A : Assembly.{u}) (B : A.Carrier → PER) :
    perAssembly.{u} (smallPiPER A.realises B) ≅
      Assembly.pi A (fun a => perAssembly.{u} (B a)) where
  hom := {
    toFun := smallPiLiftedCarrierEquiv A B
    tracked := ⟨Kleene.idCode, fun q n hn =>
      ⟨n, by simp, smallPiDecode_tracks A.realised q.down n hn⟩⟩ }
  inv := {
    toFun := (smallPiLiftedCarrierEquiv A B).symm
    tracked := ⟨Kleene.idCode, fun f n hn =>
      ⟨n, by simp,
        (smallPiEncode_realises_iff ((smallPiLiftedFunctionEquiv A B).symm f) n).mpr hn⟩⟩ }
  hom_inv_id := Assembly.Hom.ext (smallPiLiftedCarrierEquiv A B).left_inv
  inv_hom_id := Assembly.Hom.ext (smallPiLiftedCarrierEquiv A B).right_inv

/-- The dependent sum of modest PER assemblies is modest. -/
def smallSigmaModest (A : PER) (B : A.Quotient → PER) : Modest.{0} where
  toAssembly := Assembly.extend (perToModest.obj A).toAssembly
    (fun a => (perToModest.obj (B a)).toAssembly)
  modest := by
    intro n p q hp hq
    obtain ⟨a, b⟩ := p
    obtain ⟨a', b'⟩ := q
    have haa : a = a' := A.modest hp.1 hq.1
    subst a'
    have hbb : b = b' := (B a).modest hp.2 hq.2
    subst b'
    rfl

/-- The small-sum PER is exactly the PER obtained from the corresponding
modest dependent sum, as asserted in Definition 35. -/
theorem smallSigmaModestPER_eq (A : PER) (B : A.Quotient → PER) :
    modestPER (smallSigmaModest A B) = smallSigmaPER A B := by
  apply PER.ext
  intro p q
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hpa, hpb⟩, ⟨hqa, hqb⟩⟩
    exact ⟨a, hpa, hqa, (B a).rel_of_realises hpb hqb⟩
  · rintro ⟨a, hpa, hqa, hpq⟩
    obtain ⟨b, hpb, hqb⟩ := (B a).rel_iff_common_class.mp hpq
    exact ⟨⟨a, b⟩, ⟨hpa, hpb⟩, ⟨hqa, hqb⟩⟩

/-- The small sum decodes to the assembly of dependent pairs, up to an
identity-tracked isomorphism. -/
noncomputable def smallSigmaAssemblyIso (A : PER) (B : A.Quotient → PER) :
    (perToModest.obj (smallSigmaPER A B)).toAssembly ≅
      Assembly.extend (perToModest.obj A).toAssembly
        (fun a => (perToModest.obj (B a)).toAssembly) := by
  have e := modestPERIso (smallSigmaModest A B)
  have e' : perToModest.obj (smallSigmaPER A B) ≅ smallSigmaModest A B :=
    smallSigmaModestPER_eq A B ▸ e
  exact modestInclusion.mapIso e'

/-- The lifted dependent sum remains modest in every ambient universe. -/
def smallSigmaLiftedModest (A : PER) (B : A.Quotient → PER) : Modest.{u} where
  toAssembly := Assembly.extend (perAssembly.{u} A)
    (fun a => perAssembly.{u} (B a.down))
  modest := by
    intro n p q hp hq
    obtain ⟨a, b⟩ := p
    obtain ⟨a', b'⟩ := q
    have haa : a = a' := ULift.ext _ _ (A.modest hp.1 hq.1)
    subst a'
    have hbb : b = b' := ULift.ext _ _ ((B a.down).modest hp.2 hq.2)
    subst b'
    rfl

theorem smallSigmaLiftedModestPER_eq (A : PER) (B : A.Quotient → PER) :
    modestPER (smallSigmaLiftedModest.{u} A B) = smallSigmaPER A B := by
  apply PER.ext
  intro p q
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hpa, hpb⟩, ⟨hqa, hqb⟩⟩
    exact ⟨a.down, hpa, hqa, (B a.down).rel_of_realises hpb hqb⟩
  · rintro ⟨a, hpa, hqa, hpq⟩
    obtain ⟨b, hpb, hqb⟩ := (B a).rel_iff_common_class.mp hpq
    exact ⟨⟨ULift.up a, ULift.up b⟩, ⟨hpa, hpb⟩, ⟨hqa, hqb⟩⟩

/-- The small-sum comparison at any ambient universe. -/
noncomputable def smallSigmaLiftedAssemblyIso (A : PER) (B : A.Quotient → PER) :
    perAssembly.{u} (smallSigmaPER A B) ≅
      Assembly.extend (perAssembly.{u} A)
        (fun a => perAssembly.{u} (B a.down)) := by
  have e := liftedModestPERIso (smallSigmaLiftedModest.{u} A B)
  have e' : liftedPerToModest.obj (smallSigmaPER A B) ≅ smallSigmaLiftedModest.{u} A B :=
    smallSigmaLiftedModestPER_eq A B ▸ e
  exact modestInclusion.mapIso e'

end LaarakkerOttenVanDenBerg2026.V2

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_TypeObjectsV2 -/

/-!
# Small and large semantic type objects

Appendix C.5–C.6 explicitly requires a case distinction between small and large
type constructors in order to validate the decoder equations. A type object
therefore records whether it is a PER code or a large assembly. Products and
sums of small objects use the PER constructions; every other case uses the
ordinary assembly construction. Both branches have their intended semantics.
-/

namespace LaarakkerOttenVanDenBerg2026.V2

universe u

namespace Assembly

/-- An equivalence of assembly carriers which preserves the realizing numbers.
Both directions therefore have the same uniform identity tracker. -/
structure RealizerIso (A B : Assembly.{u}) where
  toEquiv : A.Carrier ≃ B.Carrier
  realises_iff : ∀ n x, A.realises n x ↔ B.realises n (toEquiv x)

namespace RealizerIso

def refl (A : Assembly.{u}) : RealizerIso A A where
  toEquiv := Equiv.refl _
  realises_iff _ _ := Iff.rfl

def ofEq {A B : Assembly.{u}} (h : A = B) : RealizerIso A B :=
  h ▸ refl A

def trans {A B C : Assembly.{u}} (f : RealizerIso A B) (g : RealizerIso B C) :
    RealizerIso A C where
  toEquiv := f.toEquiv.trans g.toEquiv
  realises_iff n x := (f.realises_iff n x).trans (g.realises_iff n (f.toEquiv x))

def ofEquiv {A B : Assembly.{u}} (e : A.Carrier ≃ B.Carrier)
    (hf : ∀ n x, A.realises n x → B.realises n (e x))
    (hg : ∀ n y, B.realises n y → A.realises n (e.symm y)) : RealizerIso A B where
  toEquiv := e
  realises_iff n x := ⟨hf n x, fun h => by
    have hx := hg n (e x) h
    simpa only [Equiv.symm_apply_apply] using hx⟩

def toIso {A B : Assembly.{u}} (e : RealizerIso A B) : CategoryTheory.Iso A B where
  hom := {
    toFun := e.toEquiv
    tracked := ⟨Kleene.idCode, fun x n hn =>
      ⟨n, by simp, (e.realises_iff n x).mp hn⟩⟩ }
  inv := {
    toFun := e.toEquiv.symm
    tracked := ⟨Kleene.idCode, fun y n hn => ⟨n, by simp,
      (e.realises_iff n (e.toEquiv.symm y)).mpr
        (by simpa only [Equiv.apply_symm_apply] using hn)⟩⟩ }
  hom_inv_id := Hom.ext e.toEquiv.left_inv
  inv_hom_id := Hom.ext e.toEquiv.right_inv

theorem inv_realises {A B : Assembly.{u}} (e : RealizerIso A B) (n : ℕ)
    (y : B.Carrier) (h : B.realises n y) : A.realises n (e.toEquiv.symm y) :=
  (e.realises_iff n (e.toEquiv.symm y)).mpr
    (by simpa only [Equiv.apply_symm_apply] using h)

end RealizerIso
end Assembly

/-- The lifted small product comparison preserves every realizer in both directions. -/
noncomputable def smallPiRealizerIso (A : Assembly.{u}) (B : A.Carrier → PER) :
    Assembly.RealizerIso (perAssembly.{u} (smallPiPER A.realises B))
      (Assembly.pi A (fun a => perAssembly.{u} (B a))) :=
  Assembly.RealizerIso.ofEquiv (smallPiLiftedCarrierEquiv A B)
    (fun n q hn => smallPiDecode_tracks A.realised q.down n hn)
    (fun n f hn =>
      (smallPiEncode_realises_iff ((smallPiLiftedFunctionEquiv A B).symm f) n).mpr hn)

/-- The PER presentation of any modest assembly preserves every realizer. -/
noncomputable def modestPERRealizerIso (X : Modest.{u}) :
    Assembly.RealizerIso (perAssembly.{u} (modestPER X)) X.toAssembly :=
  Assembly.RealizerIso.ofEquiv {
    toFun q := modestPERDecode X q.down
    invFun x := ULift.up (modestPEREncode X x)
    left_inv q := ULift.ext _ _ (modestPEREncode_decode X q.down)
    right_inv := modestPERDecode_encode X }
    (fun _ _ hn => modestPERDecode_realises X hn)
    (fun n x hn => (modestPEREncode_realises_iff X x n).mpr hn)

/-- The lifted small sum comparison preserves every realizer in both directions. -/
noncomputable def smallSigmaRealizerIso (A : PER) (B : A.Quotient → PER) :
    Assembly.RealizerIso (perAssembly.{u} (smallSigmaPER A B))
      (Assembly.extend (perAssembly.{u} A) (fun a => perAssembly.{u} (B a.down))) :=
  (Assembly.RealizerIso.ofEq
    (congrArg perAssembly.{u} (smallSigmaLiftedModestPER_eq.{u} A B).symm)).trans
      (modestPERRealizerIso (smallSigmaLiftedModest.{u} A B))

/-- Semantic type objects record smallness as part of their representation. -/
inductive TypeObj where
  | small (R : PER)
  | large (A : Assembly.{u})

namespace TypeObj

/-- Decode a semantic type object to its realizing assembly. -/
def asAssembly : TypeObj.{u} → Assembly.{u}
  | small R => perAssembly R
  | large A => A

/-- Whether the object is represented by a small PER code. -/
def IsSmall : TypeObj.{u} → Prop
  | small _ => True
  | large _ => False

/-- Extract a PER code only from an object proved to be small. There is no
default code for a large assembly. -/
def smallCode : (A : TypeObj.{u}) → A.IsSmall → PER
  | small R, _ => R
  | large _, h => False.elim h

theorem smallCode_asAssembly (A : TypeObj.{u}) (h : A.IsSmall) :
    perAssembly (A.smallCode h) = A.asAssembly := by
  cases A with
  | small R => rfl
  | large A => exact False.elim h

theorem small_smallCode (A : TypeObj.{u}) (h : A.IsSmall) :
    small (A.smallCode h) = A := by
  cases A with
  | small R => rfl
  | large A => exact False.elim h

/-- The source's small/large case distinction for dependent products. -/
noncomputable def pi :
    (A : TypeObj.{u}) → (A.asAssembly.Carrier → TypeObj.{u}) → TypeObj.{u}
  | small R, B => by
    classical
    exact if h : ∀ a, (B a).IsSmall then
      small (smallPiPER (perAssembly R).realises (fun a => (B a).smallCode (h a)))
    else large (Assembly.pi (perAssembly R) (fun a => (B a).asAssembly))
  | large A, B => large (Assembly.pi A (fun a => (B a).asAssembly))

/-- The source's small/large case distinction for dependent sums. -/
noncomputable def sigma :
    (A : TypeObj.{u}) → (A.asAssembly.Carrier → TypeObj.{u}) → TypeObj.{u}
  | small R, B => by
    classical
    exact if h : ∀ a, (B a).IsSmall then
      small (smallSigmaPER R (fun a => (B (ULift.up a)).smallCode (h (ULift.up a))))
    else large (Assembly.extend (perAssembly R) (fun a => (B a).asAssembly))
  | large A, B => large (Assembly.extend A (fun a => (B a).asAssembly))

/-- Exact decoding equation for small dependent products. -/
theorem pi_small (R : PER) (B : (perAssembly.{u} R).Carrier → PER) :
    pi (small R) (fun a => small (B a)) =
      small (smallPiPER (perAssembly.{u} R).realises B) := by
  exact dif_pos (fun _ => trivial)

/-- Exact decoding equation for small dependent sums. -/
theorem sigma_small (R : PER) (B : (perAssembly.{u} R).Carrier → PER) :
    sigma (small R) (fun a => small (B a)) =
      small (smallSigmaPER R (fun a => B (ULift.up a))) := by
  exact dif_pos (fun _ => trivial)

/-- Every product branch has the ordinary dependent-function semantics, with a
uniform identity tracker for the comparison. -/
noncomputable def piRealizerIso : (A : TypeObj.{u}) →
    (B : A.asAssembly.Carrier → TypeObj.{u}) →
    Assembly.RealizerIso (pi A B).asAssembly
      (Assembly.pi A.asAssembly (fun a => (B a).asAssembly))
  | small R, B => by
    classical
    by_cases h : ∀ a, (B a).IsSmall
    · rw [pi, dif_pos h]
      have hB : (fun a => perAssembly ((B a).smallCode (h a))) =
          (fun a => (B a).asAssembly) := funext fun a => smallCode_asAssembly (B a) (h a)
      exact (smallPiRealizerIso (perAssembly R) (fun a => (B a).smallCode (h a))).trans
        (Assembly.RealizerIso.ofEq (congrArg (Assembly.pi (perAssembly R)) hB))
    · rw [pi, dif_neg h]
      exact Assembly.RealizerIso.refl _
  | large A, B => Assembly.RealizerIso.refl _

/-- Every sum branch has the ordinary dependent-pair semantics, with a uniform
identity tracker for the comparison. -/
noncomputable def sigmaRealizerIso : (A : TypeObj.{u}) →
    (B : A.asAssembly.Carrier → TypeObj.{u}) →
    Assembly.RealizerIso (sigma A B).asAssembly
      (Assembly.extend A.asAssembly (fun a => (B a).asAssembly))
  | small R, B => by
    classical
    by_cases h : ∀ a, (B a).IsSmall
    · rw [sigma, dif_pos h]
      have hB : (fun a => perAssembly ((B a).smallCode (h a))) =
          (fun a => (B a).asAssembly) := funext fun a => smallCode_asAssembly (B a) (h a)
      exact (smallSigmaRealizerIso R
        (fun a => (B (ULift.up a)).smallCode (h (ULift.up a)))).trans
          (Assembly.RealizerIso.ofEq (congrArg (Assembly.extend (perAssembly R)) hB))
    · rw [sigma, dif_neg h]
      exact Assembly.RealizerIso.refl _
  | large A, B => Assembly.RealizerIso.refl _

/-- The assembly isomorphism underlying the product representation change. -/
noncomputable def piAssemblyIso (A : TypeObj.{u})
    (B : A.asAssembly.Carrier → TypeObj.{u}) :
    CategoryTheory.Iso (pi A B).asAssembly
      (Assembly.pi A.asAssembly (fun a => (B a).asAssembly)) :=
  (piRealizerIso A B).toIso

/-- The assembly isomorphism underlying the sum representation change. -/
noncomputable def sigmaAssemblyIso (A : TypeObj.{u})
    (B : A.asAssembly.Carrier → TypeObj.{u}) :
    CategoryTheory.Iso (sigma A B).asAssembly
      (Assembly.extend A.asAssembly (fun a => (B a).asAssembly)) :=
  (sigmaRealizerIso A B).toIso

end TypeObj

end LaarakkerOttenVanDenBerg2026.V2

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_AssemblyFamiliesV2 -/

/-! Tracked changes of presentation for families and iterated context extension. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Assembly

universe u

/-- A fiberwise realizer-preserving equivalence induces a context substitution. -/
def fiberForward {Γ : Assembly.{u}} {A B : Ty Γ}
    (e : ∀ γ, RealizerIso (A γ) (B γ)) : Hom (extend Γ A) (extend Γ B) where
  toFun p := ⟨p.1, (e p.1).toEquiv p.2⟩
  tracked := ⟨Kleene.idCode, fun p n hn ↦
    ⟨n, by simp, hn.1, ((e p.1).realises_iff (Nat.unpair n).2 p.2).mp hn.2⟩⟩

/-- The inverse fiberwise change of presentation preserves the same context code. -/
def fiberBackward {Γ : Assembly.{u}} {A B : Ty Γ}
    (e : ∀ γ, RealizerIso (A γ) (B γ)) : Hom (extend Γ B) (extend Γ A) where
  toFun p := ⟨p.1, (e p.1).toEquiv.symm p.2⟩
  tracked := ⟨Kleene.idCode, fun p n hn ↦
    ⟨n, by simp, hn.1, (e p.1).inv_realises (Nat.unpair n).2 p.2 hn.2⟩⟩

theorem fiberForward_backward {Γ : Assembly.{u}} {A B : Ty Γ}
    (e : ∀ γ, RealizerIso (A γ) (B γ)) :
    Hom.comp (fiberForward e) (fiberBackward e) = Hom.id (extend Γ A) := by
  apply Hom.ext
  intro p
  exact congrArg (Sigma.mk p.1) ((e p.1).toEquiv.symm_apply_apply p.2)

theorem fiberBackward_forward {Γ : Assembly.{u}} {A B : Ty Γ}
    (e : ∀ γ, RealizerIso (A γ) (B γ)) :
    Hom.comp (fiberBackward e) (fiberForward e) = Hom.id (extend Γ B) := by
  apply Hom.ext
  intro p
  exact congrArg (Sigma.mk p.1) ((e p.1).toEquiv.apply_symm_apply p.2)

/-- Reassociate two context binders into one dependent-sum binder. -/
def associate {Γ : Assembly.{u}} (A : Ty Γ) (B : Ty (extend Γ A)) :
    Hom (extend (extend Γ A) B)
      (extend Γ (fun γ ↦ extend (A γ) (fun a ↦ B ⟨γ, a⟩))) where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  tracked := by
    refine ⟨Kleene.pairCode (Kleene.compCode Kleene.fstCode Kleene.fstCode)
      (Kleene.pairCode (Kleene.compCode Kleene.sndCode Kleene.fstCode) Kleene.sndCode), ?_⟩
    intro p n hn
    rcases p with ⟨⟨γ, a⟩, b⟩
    refine ⟨Nat.pair n.unpair.1.unpair.1 (Nat.pair n.unpair.1.unpair.2 n.unpair.2), ?_, ?_⟩
    · simp
    · simpa only [extend, Nat.unpair_pair] using And.intro hn.1.1 (And.intro hn.1.2 hn.2)

/-- Undo reassociation; both directions are computational context morphisms. -/
def unassociate {Γ : Assembly.{u}} (A : Ty Γ) (B : Ty (extend Γ A)) :
    Hom (extend Γ (fun γ ↦ extend (A γ) (fun a ↦ B ⟨γ, a⟩)))
      (extend (extend Γ A) B) where
  toFun p := ⟨⟨p.1, p.2.1⟩, p.2.2⟩
  tracked := by
    refine ⟨Kleene.pairCode
      (Kleene.pairCode Kleene.fstCode (Kleene.compCode Kleene.fstCode Kleene.sndCode))
      (Kleene.compCode Kleene.sndCode Kleene.sndCode), ?_⟩
    intro p n hn
    refine ⟨Nat.pair (Nat.pair n.unpair.1 n.unpair.2.unpair.1) n.unpair.2.unpair.2, ?_, ?_⟩
    · simp
    · simpa only [extend, Nat.unpair_pair] using And.intro (And.intro hn.1 hn.2.1) hn.2.2

theorem associate_unassociate {Γ : Assembly.{u}} (A : Ty Γ) (B : Ty (extend Γ A)) :
    Hom.comp (associate A B) (unassociate A B) = Hom.id _ := Hom.ext fun _ ↦ rfl

theorem unassociate_associate {Γ : Assembly.{u}} (A : Ty Γ) (B : Ty (extend Γ A)) :
    Hom.comp (unassociate A B) (associate A B) = Hom.id _ := Hom.ext fun _ ↦ rfl

end LaarakkerOttenVanDenBerg2026.V2.Assembly

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_FixV2 -/

/-!
# Tracked well-founded recursion

This is the fixpoint construction of Appendix C of Laarakker, Otten, and van den Berg
(2026). The step is an actual semantic term between assemblies, including its uniform
tracker. The recursion simultaneously constructs values and proves their tracking.
The size carrier can be any well-founded relation with the full realizability relation;
in the paper it is the first uncountable ordinal.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Assembly

universe u

namespace SizedFix

variable {S : Type u} (r : S → S → Prop)

/-- The assembly of tracked sections below a size. -/
def bounded (A : S → Assembly.{u}) (s : S) : Assembly.{u} :=
  pi (nabla {t : S // r t s}) (fun t ↦ A t.val)

/-- Restriction of a tracked section preserves the same tracker. -/
def restrict {A : S → Assembly.{u}} (g : (pi (nabla S) A).Carrier) (s : S) :
    (bounded r A s).Carrier :=
  ⟨fun t ↦ g.val t.val, by
    obtain ⟨e, he⟩ := g.property
    exact ⟨e, fun t n hn ↦ he t.val n hn⟩⟩

/-- The actual assembly-valued type of a step for sized recursion. -/
def stepTy {Γ : Assembly.{u}} (A : Γ.Carrier → S → Assembly.{u}) : Ty Γ :=
  fun γ ↦ pi (nabla S) (fun s ↦ pi (bounded r (A γ) s) (fun _ ↦ A γ s))

/-- The type of the recursively defined tracked section. -/
def resultTy {Γ : Assembly.{u}} (A : Γ.Carrier → S → Assembly.{u}) : Ty Γ :=
  fun γ ↦ pi (nabla S) (A γ)

/-- A fixed point satisfies the paper's beta equation, using tracked restrictions. -/
def IsFixed {Γ : Assembly.{u}} {A : Γ.Carrier → S → Assembly.{u}}
    (f : Tm Γ (stepTy r A)) (g : Tm Γ (resultTy A)) : Prop :=
  ∀ (γ : Γ.Carrier) (s : S), (g.toFun γ).val s =
    ((f.toFun γ).val s).val (restrict r (g.toFun γ) s)

/-- Well-founded recursion on a tracked step produces a uniformly tracked fixed point. -/
theorem exists_fixedTerm (hw : WellFounded r) {Γ : Assembly.{u}}
    {A : Γ.Carrier → S → Assembly.{u}} (f : Tm Γ (stepTy r A)) :
    ∃ g : Tm Γ (resultTy A), IsFixed r f g := by
  obtain ⟨e, he⟩ := f.tracked
  let F (c p : ℕ) : Part ℕ :=
    (Kleene.app e p.unpair.1).bind fun d ↦
      (Kleene.app d p.unpair.2).bind fun q ↦
        Kleene.app q (Kleene.curryCode c p.unpair.1)
  have hF : Partrec₂ F := by
    have first : Computable (fun p : ℕ × ℕ ↦ p.2.unpair.1) :=
      Computable.fst.comp (Computable.unpair.comp Computable.snd)
    have second : Computable (fun p : (ℕ × ℕ) × ℕ ↦ p.1.2.unpair.2) :=
      Computable.snd.comp
        (Computable.unpair.comp (Computable.snd.comp Computable.fst))
    have hc : Computable (fun p : ((ℕ × ℕ) × ℕ) × ℕ ↦
        Kleene.curryCode p.1.1.1 p.1.1.2.unpair.1) :=
      Kleene.curryCode_computable.comp
        (Computable.fst.comp (Computable.fst.comp Computable.fst))
        (first.comp (Computable.fst.comp Computable.fst))
    exact ((Kleene.app_partrec.comp (Computable.const e) first).bind
      ((Kleene.app_partrec.comp Computable.snd second).bind
        (Kleene.app_partrec.comp Computable.snd hc).to₂).to₂).to₂
  obtain ⟨c, hc⟩ := Kleene.fixed_point₂ hF
  have hcurry (k n : ℕ) :
      Kleene.app (Kleene.curryCode c k) n =
        (Kleene.app e k).bind fun d ↦
          (Kleene.app d n).bind fun q ↦ Kleene.app q (Kleene.curryCode c k) := by
    rw [Kleene.app_curryCode, hc]
    simp [F]
  let P (γ : Γ.Carrier) (s : S) :=
    {a : (A γ s).Carrier // ∀ k, Γ.realises k γ → ∀ n,
      ∃ m, m ∈ Kleene.app (Kleene.curryCode c k) n ∧ (A γ s).realises m a}
  let step (γ : Γ.Carrier) (s : S) (ih : ∀ t, r t s → P γ t) : P γ s := by
    let previous : (bounded r (A γ) s).Carrier :=
      ⟨fun t ↦ (ih t.val t.property).val, by
        obtain ⟨k, hk⟩ := Γ.realised γ
        exact ⟨Kleene.curryCode c k,
          fun t n _ ↦ (ih t.val t.property).property k hk n⟩⟩
    refine ⟨((f.toFun γ).val s).val previous, ?_⟩
    intro k hk n
    obtain ⟨d, hd, hdf⟩ := he γ k hk
    obtain ⟨q, hq, hqf⟩ := hdf s n trivial
    have hprevious : (bounded r (A γ) s).realises (Kleene.curryCode c k) previous :=
      fun t m _ ↦ (ih t.val t.property).property k hk m
    obtain ⟨m, hm, hma⟩ := hqf previous (Kleene.curryCode c k) hprevious
    exact ⟨m, by rw [hcurry]; exact Part.mem_bind hd (Part.mem_bind hq hm), hma⟩
  let values (γ : Γ.Carrier) : ∀ s, P γ s := hw.fix (step γ)
  let g : Tm Γ (resultTy A) :=
    { toFun := fun γ ↦ ⟨fun s ↦ (values γ s).val, by
        obtain ⟨k, hk⟩ := Γ.realised γ
        exact ⟨Kleene.curryCode c k, fun s n _ ↦ (values γ s).property k hk n⟩⟩
      tracked := by
        refine ⟨Kleene.abstractCode c, ?_⟩
        intro γ k hk
        refine ⟨Kleene.curryCode c k, by simp, ?_⟩
        exact fun s n _ ↦ (values γ s).property k hk n }
  refine ⟨g, ?_⟩
  intro γ s
  change (hw.fix (step γ) s).val = _
  rw [WellFounded.fix_eq]
  rfl

/-- The semantic sized fixpoint operator, with all tracking obligations discharged. -/
noncomputable def fixedTerm (hw : WellFounded r) {Γ : Assembly.{u}}
    {A : Γ.Carrier → S → Assembly.{u}} (f : Tm Γ (stepTy r A)) :
    Tm Γ (resultTy A) := (exists_fixedTerm r hw f).choose

theorem fixedTerm_beta (hw : WellFounded r) {Γ : Assembly.{u}}
    {A : Γ.Carrier → S → Assembly.{u}} (f : Tm Γ (stepTy r A)) :
    IsFixed r f (fixedTerm r hw f) := (exists_fixedTerm r hw f).choose_spec

/-- The beta equation determines the fixed point uniquely. -/
theorem fixedTerm_unique (hw : WellFounded r) {Γ : Assembly.{u}}
    {A : Γ.Carrier → S → Assembly.{u}} (f : Tm Γ (stepTy r A))
    (g : Tm Γ (resultTy A)) (hg : IsFixed r f g) : g = fixedTerm r hw f := by
  apply Tm.ext
  intro γ
  apply Subtype.ext
  funext s
  induction s using hw.induction with
  | h s ih =>
    rw [hg γ s, fixedTerm_beta r hw f γ s]
    apply congrArg (((f.toFun γ).val s).val)
    apply Subtype.ext
    funext t
    exact ih t.val t.property

/-- The fixpoint operator commutes with contextual substitution. -/
theorem fixedTerm_subst (hw : WellFounded r) {Δ Γ : Assembly.{u}}
    {A : Γ.Carrier → S → Assembly.{u}} (f : Tm Γ (stepTy r A)) (σ : Hom Δ Γ) :
    substTm (fixedTerm r hw f) σ =
      fixedTerm r hw (A := fun δ ↦ A (σ.toFun δ)) (substTm f σ) := by
  apply fixedTerm_unique r hw
  intro δ s
  exact fixedTerm_beta r hw f (σ.toFun δ) s

/-- A proposition interpreted as the terminal PER when true and the empty PER otherwise. -/
def guardPER (p : Prop) : PER where
  rel _ _ := p
  symm h := h
  trans h _ := h

/-- The assembly interpreting a logical guard such as a strict size inequality. -/
def guard (p : Prop) : Assembly.{u} := perAssembly (guardPER p)

/-- Every element of a guard proves the guarding proposition. -/
theorem guardProof {p : Prop} (x : (guard.{u} p).Carrier) : p := by
  obtain ⟨n, hn, _⟩ := (guardPER p).realised x.down
  exact hn

/-- The unique element of a true guard. -/
def guardWitness {p : Prop} (h : p) : (guard.{u} p).Carrier :=
  ULift.up ((guardPER p).classOf 0 h)

theorem guard_realises {p : Prop} (h : p) (n : ℕ) (x : (guard.{u} p).Carrier) :
    (guard p).realises n x := by
  obtain ⟨k, hk, heq⟩ := (guardPER p).realised x.down
  change (guardPER p).realises n x.down
  rw [← heq]
  exact ((guardPER p).realises_classOf_iff hk).mpr h

instance (p : Prop) : Subsingleton (guard.{u} p).Carrier where
  allEq x y := perAssembly_modest (guardPER p) 0 x y
    (guard_realises (guardProof x) 0 x) (guard_realises (guardProof x) 0 y)

/-- The literal guarded-product interpretation of `∀ t. (t < s → A t)`. -/
def guarded (A : S → Assembly.{u}) (s : S) : Assembly.{u} :=
  pi (nabla S) (fun t ↦ pi (guard (r t s)) (fun _ ↦ A t))

/-- Extend a bounded section to guarded functions, returning an empty function
where the guard is false. K tracks this operation uniformly in the sizes. -/
def boundedToGuarded (A : S → Assembly.{u}) (s : S) :
    Hom (bounded r A s) (guarded r A s) where
  toFun g := ⟨fun t ↦ ⟨fun h ↦ g.val ⟨t, guardProof h⟩, by
    obtain ⟨e, he⟩ := g.property
    exact ⟨e, fun h n _ ↦ he ⟨t, guardProof h⟩ n trivial⟩⟩, by
    obtain ⟨e, he⟩ := g.property
    refine ⟨Kleene.constCode e, fun t n _ ↦ ⟨e, by simp, ?_⟩⟩
    exact fun h m _ ↦ he ⟨t, guardProof h⟩ m trivial⟩
  tracked := by
    refine ⟨Kleene.kCode, ?_⟩
    intro g e he
    refine ⟨Kleene.constCode e, by simp, ?_⟩
    intro t n _
    refine ⟨e, by simp, ?_⟩
    exact fun h m _ ↦ he ⟨t, guardProof h⟩ m trivial

/-- Evaluate each guarded function at its unique proof, on the bounded domain. -/
def guardedToBounded (A : S → Assembly.{u}) (s : S) :
    Hom (guarded r A s) (bounded r A s) where
  toFun g := ⟨fun t ↦ (g.val t.val).val (guardWitness t.property), by
    obtain ⟨e, he⟩ := g.property
    refine ⟨Kleene.applyCode e (Kleene.constCode 0), ?_⟩
    intro t n _
    obtain ⟨q, hq, hqg⟩ := he t.val n trivial
    obtain ⟨m, hm, hma⟩ := hqg (guardWitness t.property) 0
      (guard_realises t.property 0 _)
    refine ⟨m, ?_, hma⟩
    simp only [Kleene.app_applyCode, Kleene.app_constCode, Part.bind_some]
    exact Part.mem_bind hq hm⟩
  tracked := by
    obtain ⟨z, hz⟩ := Kleene.exists_index_of_computable
      (Kleene.applyCode_computable.comp Computable.id
        (Computable.const (Kleene.constCode 0)))
    refine ⟨z, ?_⟩
    intro g e he
    refine ⟨Kleene.applyCode e (Kleene.constCode 0), by rw [hz]; simp, ?_⟩
    intro t n _
    obtain ⟨q, hq, hqg⟩ := he t.val n trivial
    obtain ⟨m, hm, hma⟩ := hqg (guardWitness t.property) 0
      (guard_realises t.property 0 _)
    refine ⟨m, ?_, hma⟩
    simp only [Kleene.app_applyCode, Kleene.app_constCode, Part.bind_some]
    exact Part.mem_bind hq hm

/-- Appendix C.8's identification of bounded sections with guarded products is
an isomorphism of assemblies, not merely a bijection of their carriers. -/
def boundedGuardedIso (A : S → Assembly.{u}) (s : S) :
    bounded r A s ≅ guarded r A s where
  hom := boundedToGuarded r A s
  inv := guardedToBounded r A s
  hom_inv_id := Hom.ext fun g ↦ Subtype.ext (funext fun t ↦ rfl)
  inv_hom_id := by
    apply Hom.ext
    intro g
    apply Subtype.ext
    funext t
    apply Subtype.ext
    funext h
    exact congrArg (g.val t).val (Subsingleton.elim _ _)

theorem boundedToGuarded_realises (A : S → Assembly.{u}) (s : S)
    {g : (bounded r A s).Carrier} {e : ℕ} (he : (bounded r A s).realises e g) :
    (guarded r A s).realises (Kleene.constCode e) ((boundedToGuarded r A s).toFun g) := by
  intro t n _
  exact ⟨e, by simp, fun h m _ ↦ he ⟨t, guardProof h⟩ m trivial⟩

/-- Precompose a step with the tracked inclusion of bounded sections into guarded products. -/
def precomposeGuard (A : S → Assembly.{u}) (s : S)
    (f : (pi (guarded r A s) (fun _ ↦ A s)).Carrier) :
    (pi (bounded r A s) (fun _ ↦ A s)).Carrier :=
  ⟨fun g ↦ f.val ((boundedToGuarded r A s).toFun g), by
    obtain ⟨e, he⟩ := f.property
    refine ⟨Kleene.compCode e Kleene.kCode, ?_⟩
    intro g n hn
    obtain ⟨m, hm, hma⟩ := he ((boundedToGuarded r A s).toFun g)
      (Kleene.constCode n) (boundedToGuarded_realises r A s hn)
    exact ⟨m, by simpa using hm, hma⟩⟩

theorem precomposeGuard_realises (A : S → Assembly.{u}) (s : S)
    {f : (pi (guarded r A s) (fun _ ↦ A s)).Carrier} {e : ℕ}
    (he : (pi (guarded r A s) (fun _ ↦ A s)).realises e f) :
    (pi (bounded r A s) (fun _ ↦ A s)).realises
      (Kleene.compCode e Kleene.kCode) (precomposeGuard r A s f) := by
  intro g n hn
  obtain ⟨m, hm, hma⟩ := he ((boundedToGuarded r A s).toFun g)
    (Kleene.constCode n) (boundedToGuarded_realises r A s hn)
  exact ⟨m, by simpa using hm, hma⟩

private theorem precomposeIndex_computable :
    Computable (fun e ↦ Kleene.compCode e Kleene.kCode) :=
  Kleene.compCode_computable.comp Computable.id (Computable.const Kleene.kCode)

private noncomputable def precomposeIndex : ℕ :=
  (Kleene.exists_index_of_computable precomposeIndex_computable).choose

private theorem app_precomposeIndex (e : ℕ) :
    Kleene.app precomposeIndex e = Part.some (Kleene.compCode e Kleene.kCode) :=
  (Kleene.exists_index_of_computable precomposeIndex_computable).choose_spec e

/-- The step type using the paper's literal guarded quantifier. -/
def guardedStepTy {Γ : Assembly.{u}} (A : Γ.Carrier → S → Assembly.{u}) : Ty Γ :=
  fun γ ↦ pi (nabla S) (fun s ↦ pi (guarded r (A γ) s) (fun _ ↦ A γ s))

/-- Convert an actual guarded semantic step to the bounded-domain recursion interface. -/
noncomputable def guardedStepToStep {Γ : Assembly.{u}}
    {A : Γ.Carrier → S → Assembly.{u}} (f : Tm Γ (guardedStepTy r A)) :
    Tm Γ (stepTy r A) where
  toFun γ := ⟨fun s ↦ precomposeGuard r (A γ) s ((f.toFun γ).val s), by
    obtain ⟨e, he⟩ := (f.toFun γ).property
    refine ⟨Kleene.compCode precomposeIndex e, ?_⟩
    intro s n hn
    obtain ⟨q, hq, hqf⟩ := he s n hn
    refine ⟨Kleene.compCode q Kleene.kCode, ?_, precomposeGuard_realises r (A γ) s hqf⟩
    rw [Kleene.app_compCode]
    exact Part.mem_bind hq (by rw [app_precomposeIndex]; simp)⟩
  tracked := by
    obtain ⟨d, hd⟩ := f.tracked
    obtain ⟨z, hz⟩ := Kleene.exists_index_of_computable
      (Kleene.compCode_computable.comp (Computable.const precomposeIndex) Computable.id)
    refine ⟨Kleene.compCode z d, ?_⟩
    intro γ k hk
    obtain ⟨e, he, hef⟩ := hd γ k hk
    refine ⟨Kleene.compCode precomposeIndex e, ?_, ?_⟩
    · rw [Kleene.app_compCode]
      exact Part.mem_bind he (by rw [hz]; simp)
    · intro s n hn
      obtain ⟨q, hq, hqf⟩ := hef s n hn
      refine ⟨Kleene.compCode q Kleene.kCode, ?_, precomposeGuard_realises r (A γ) s hqf⟩
      rw [Kleene.app_compCode]
      exact Part.mem_bind hq (by rw [app_precomposeIndex]; simp)

/-- The guarded restriction used in the syntactic beta equation. -/
def guardedRestrict {A : S → Assembly.{u}} (g : (pi (nabla S) A).Carrier) (s : S) :
    (guarded r A s).Carrier :=
  (boundedToGuarded r A s).toFun (restrict r g s)

@[simp]
theorem guardedRestrict_apply {A : S → Assembly.{u}} (g : (pi (nabla S) A).Carrier)
    (s t : S) (h : (guard (r t s)).Carrier) :
    ((guardedRestrict r g s).val t).val h = g.val t := rfl

/-- The beta equation in the guarded-product presentation from the source. -/
def IsGuardedFixed {Γ : Assembly.{u}} {A : Γ.Carrier → S → Assembly.{u}}
    (f : Tm Γ (guardedStepTy r A)) (g : Tm Γ (resultTy A)) : Prop :=
  ∀ (γ : Γ.Carrier) (s : S), (g.toFun γ).val s =
    ((f.toFun γ).val s).val (guardedRestrict r (g.toFun γ) s)

/-- The semantic fixpoint operator with the paper's guarded step type. -/
noncomputable def guardedFixedTerm (hw : WellFounded r) {Γ : Assembly.{u}}
    {A : Γ.Carrier → S → Assembly.{u}} (f : Tm Γ (guardedStepTy r A)) :
    Tm Γ (resultTy A) := fixedTerm r hw (guardedStepToStep r f)

theorem guardedFixedTerm_beta (hw : WellFounded r) {Γ : Assembly.{u}}
    {A : Γ.Carrier → S → Assembly.{u}} (f : Tm Γ (guardedStepTy r A)) :
    IsGuardedFixed r f (guardedFixedTerm r hw f) :=
  fixedTerm_beta r hw (guardedStepToStep r f)

theorem guardedFixedTerm_unique (hw : WellFounded r) {Γ : Assembly.{u}}
    {A : Γ.Carrier → S → Assembly.{u}} (f : Tm Γ (guardedStepTy r A))
    (g : Tm Γ (resultTy A)) (hg : IsGuardedFixed r f g) :
    g = guardedFixedTerm r hw f := fixedTerm_unique r hw (guardedStepToStep r f) g hg

theorem guardedFixedTerm_subst (hw : WellFounded r) {Δ Γ : Assembly.{u}}
    {A : Γ.Carrier → S → Assembly.{u}} (f : Tm Γ (guardedStepTy r A)) (σ : Hom Δ Γ) :
    substTm (guardedFixedTerm r hw f) σ =
      guardedFixedTerm r hw (A := fun δ ↦ A (σ.toFun δ)) (substTm f σ) := by
  apply guardedFixedTerm_unique r hw
  intro δ s
  exact guardedFixedTerm_beta r hw f (σ.toFun δ) s

end SizedFix
end LaarakkerOttenVanDenBerg2026.V2.Assembly

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_ModelV2 -/

/-!
The assembly CwF and the literal universe and size interpretations of Section 4.
This file connects contextual syntax to the K1 assembly infrastructure. A full
interpretation of the additional rules requires separate instances and proofs;
the CwF alone is not a consistency theorem for the whole theory.
-/

namespace LaarakkerOttenVanDenBerg2026.V2

universe u
open Assembly

/-- The complete structural CwF of Appendix C.1. -/
def assemblyCwF : Theory.CwF where
  Ctx := Assembly.{u}
  Sub := Assembly.Hom
  id := Assembly.Hom.id _
  comp σ τ := Assembly.Hom.comp τ σ
  id_comp _ := Assembly.Hom.ext fun _ ↦ rfl
  comp_id _ := Assembly.Hom.ext fun _ ↦ rfl
  assoc _ _ _ := Assembly.Hom.ext fun _ ↦ rfl
  Ty := Assembly.Ty
  Tm := Assembly.Tm
  tySub := Assembly.substTy
  tmSub := Assembly.substTm
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  tmSub_id a := heq_of_eq (substTm_id a)
  tmSub_comp a σ τ := heq_of_eq (substTm_comp a τ σ).symm
  empty := Assembly.terminal
  emptySub := Assembly.terminate _
  empty_unique := Assembly.terminate_unique
  ext := Assembly.extend
  fst := Assembly.projection _ _
  snd := Assembly.lastVar _ _
  pair := Assembly.pairSubst
  pair_fst := Assembly.pairSubst_projection
  pair_snd σ a := heq_of_eq (Assembly.pairSubst_variable σ a)
  pair_unique := by
    intro Γ Δ A σ a τ hp hq
    apply Assembly.Hom.ext
    intro δ
    have hp' := congrArg (fun f : Assembly.Hom Δ Γ ↦ f.toFun δ) hp
    have hq' : HEq ((τ.toFun δ).2) (a.toFun δ) := by
      cases hp
      have hh := eq_of_heq hq
      exact heq_of_eq (congrArg (fun b ↦ b.toFun δ) hh)
    exact Sigma.ext hp' hq'

/-- The universe is the codiscrete assembly of PER codes. -/
def universeAssembly : Assembly.{u} := nabla (ULift.{u} PER)

/-- Every PER family is a term of the codiscrete universe, tracked by a constant. -/
def universeTerm (Γ : Assembly.{u}) (A : Γ.Carrier → PER) :
    Tm Γ (fun _ ↦ universeAssembly) where
  toFun γ := ULift.up (A γ)
  tracked := ⟨Kleene.constCode 0, fun _ _ _ ↦ ⟨0, by simp, trivial⟩⟩

/-- Interpretation of the Tarski universe and decoder from Appendix C.2. -/
def assemblyUniverse : Theory.Universe assemblyCwF.{u} where
  type _ := fun _ ↦ universeAssembly
  type_sub _ := rfl
  el A := fun γ ↦ perAssembly (A.toFun γ).down
  el_sub _ _ := rfl

/-- Small product codes use the actual input assembly and partial K1 application. -/
def smallProductTerm {Γ : Assembly.{u}} (A : Ty Γ)
    (B : Tm (extend Γ A) (fun _ ↦ universeAssembly)) :
    Tm Γ (fun _ ↦ universeAssembly) :=
  universeTerm Γ (fun γ ↦ smallPiPER (A γ).realises (fun a ↦ (B.toFun ⟨γ, a⟩).down))

/-- All countable ordinals, as required by Section 4.3. -/
abbrev Omega1 := {α : Ordinal.{0} // α.card ≤ Cardinal.aleph0}

/-- The semantic large size type is ∇ω₁. -/
def sizeAssembly : Assembly.{1} := nabla Omega1

/-- The zero countable ordinal. -/
def sizeZero : Omega1 := ⟨0, by simp⟩

/-- Successor preserves countability. -/
def sizeSucc (α : Omega1) : Omega1 :=
  ⟨α.val + 1, by
    rw [Ordinal.card_add_one]
    exact Cardinal.add_le_of_le (le_refl _) α.property Cardinal.one_le_aleph0⟩

/-- The strict size relation is well-founded. -/
theorem size_lt_wf : WellFounded (fun α β : Omega1 ↦ α.val < β.val) :=
  InvImage.wf (fun α : Omega1 ↦ α.val) Ordinal.lt_wf

/-- The small size ordering is the terminal PER when inhabited and empty otherwise. -/
def sizeLePER (α β : Omega1) : PER where
  rel _ _ := α.val ≤ β.val
  symm h := h
  trans h _ := h

/-- Literal universal size quantification: the small product of Appendix C.5. -/
def sizeForallPER (A : Omega1 → PER) : PER := forallPER A

/-- Literal existential size quantification: U-truncation of the dependent sum. -/
def sizeExistsPER (A : Omega1 → PER) : PER :=
  truncatePER (extend sizeAssembly (fun i ↦ perAssembly (A i)))

/-- The semantic size recursion operator, specialized to ω₁ and tracked steps.
Its bounded input has the source form `Π j, (j < i → A j)`. -/
noncomputable def sizeFix {Γ : Assembly.{1}}
    {A : Γ.Carrier → Omega1 → Assembly.{1}}
    (f : Tm Γ (SizedFix.guardedStepTy (fun α β ↦ α.val < β.val) A)) :
    Tm Γ (SizedFix.resultTy A) :=
  SizedFix.guardedFixedTerm (fun α β ↦ α.val < β.val) size_lt_wf f

theorem sizeFix_beta {Γ : Assembly.{1}}
    {A : Γ.Carrier → Omega1 → Assembly.{1}}
    (f : Tm Γ (SizedFix.guardedStepTy (fun α β ↦ α.val < β.val) A)) :
    SizedFix.IsGuardedFixed (fun α β ↦ α.val < β.val) f (sizeFix f) :=
  SizedFix.guardedFixedTerm_beta _ size_lt_wf f

end LaarakkerOttenVanDenBerg2026.V2

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_InterpretationV2 -/

/-!
Contextual interpretation with the small/large distinction from Appendix C.5.
Terms are still exactly tracked sections. The distinction affects the chosen
representation of a type, allowing the universe decoder equations to hold.
-/

namespace LaarakkerOttenVanDenBerg2026.V2

universe u
open Assembly

namespace Interpretation

/-- Families of small/large semantic type objects. -/
abbrev Ty (Γ : Assembly.{u}) := Γ.Carrier → TypeObj.{u}

/-- Underlying assembly family. -/
abbrev decode {Γ : Assembly.{u}} (A : Ty Γ) : Assembly.Ty Γ :=
  fun γ ↦ (A γ).asAssembly

/-- Terms have the same tracking condition as in the assembly CwF. -/
abbrev Tm (Γ : Assembly.{u}) (A : Ty Γ) := Assembly.Tm Γ (decode A)

/-- The representation-aware CwF, with all comprehension equations proved. -/
def cwf : Theory.CwF where
  Ctx := Assembly.{u}
  Sub := Assembly.Hom
  id := Assembly.Hom.id _
  comp σ τ := Assembly.Hom.comp τ σ
  id_comp _ := Assembly.Hom.ext fun _ ↦ rfl
  comp_id _ := Assembly.Hom.ext fun _ ↦ rfl
  assoc _ _ _ := Assembly.Hom.ext fun _ ↦ rfl
  Ty := Ty
  Tm := Tm
  tySub A σ := A ∘ σ.toFun
  tmSub := Assembly.substTm
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  tmSub_id a := heq_of_eq (Assembly.substTm_id a)
  tmSub_comp a σ τ := heq_of_eq (Assembly.substTm_comp a τ σ).symm
  empty := Assembly.terminal
  emptySub := Assembly.terminate _
  empty_unique := Assembly.terminate_unique
  ext Γ A := Assembly.extend Γ (decode A)
  fst := Assembly.projection _ _
  snd := Assembly.lastVar _ _
  pair {Γ Δ A} σ a := Assembly.pairSubst (A := decode A) σ a
  pair_fst {Γ Δ A} σ a := Assembly.pairSubst_projection (A := decode A) σ a
  pair_snd {Γ Δ A} σ a := heq_of_eq (Assembly.pairSubst_variable (A := decode A) σ a)
  pair_unique := by
    intro Γ Δ A σ a τ hp hq
    apply Assembly.Hom.ext
    intro δ
    have hp' := congrArg (fun f : Assembly.Hom Δ Γ ↦ f.toFun δ) hp
    have hq' : HEq ((τ.toFun δ).2) (a.toFun δ) := by
      cases hp
      have hh := eq_of_heq hq
      exact heq_of_eq (congrArg (fun b ↦ b.toFun δ) hh)
    exact Sigma.ext hp' hq'

/-- The universe is large; decoding a code records the small representation. -/
def universeRules : Theory.Universe cwf.{u} where
  type _ := fun _ ↦ TypeObj.large universeAssembly
  type_sub _ := rfl
  el A := fun γ ↦ TypeObj.small (A.toFun γ).down
  el_sub _ _ := rfl

/-- Transport a tracked term through pointwise realizer-preserving equivalences. -/
def mapTerm {Γ : Assembly.{u}} {A B : Assembly.Ty Γ}
    (e : ∀ γ, RealizerIso (A γ) (B γ)) (a : Assembly.Tm Γ A) : Assembly.Tm Γ B where
  toFun γ := (e γ).toEquiv (a.toFun γ)
  tracked := by
    obtain ⟨c, hc⟩ := a.tracked
    refine ⟨c, ?_⟩
    intro γ n hn
    obtain ⟨m, hm, hma⟩ := hc γ n hn
    exact ⟨m, hm, ((e γ).realises_iff m _).mp hma⟩

/-- The inverse representation change also preserves each realizing number. -/
def unmapTerm {Γ : Assembly.{u}} {A B : Assembly.Ty Γ}
    (e : ∀ γ, RealizerIso (A γ) (B γ)) (b : Assembly.Tm Γ B) : Assembly.Tm Γ A where
  toFun γ := (e γ).toEquiv.symm (b.toFun γ)
  tracked := by
    obtain ⟨c, hc⟩ := b.tracked
    refine ⟨c, ?_⟩
    intro γ n hn
    obtain ⟨m, hm, hmb⟩ := hc γ n hn
    exact ⟨m, hm, (e γ).inv_realises m _ hmb⟩

theorem map_unmapTerm {Γ : Assembly.{u}} {A B : Assembly.Ty Γ}
    (e : ∀ γ, RealizerIso (A γ) (B γ)) (b : Assembly.Tm Γ B) :
    mapTerm e (unmapTerm e b) = b :=
  Assembly.Tm.ext fun γ ↦ (e γ).toEquiv.apply_symm_apply _

theorem unmap_mapTerm {Γ : Assembly.{u}} {A B : Assembly.Ty Γ}
    (e : ∀ γ, RealizerIso (A γ) (B γ)) (a : Assembly.Tm Γ A) :
    unmapTerm e (mapTerm e a) = a :=
  Assembly.Tm.ext fun γ ↦ (e γ).toEquiv.symm_apply_apply _

/-- Contextual product formation with the source's small/large case split. -/
noncomputable def pi {Γ : Assembly.{u}} (A : Ty Γ)
    (B : Ty (Assembly.extend Γ (decode A))) : Ty Γ :=
  fun γ ↦ TypeObj.pi (A γ) (fun a ↦ B ⟨γ, a⟩)

/-- Contextual lambda abstraction uses the same tracker in either representation. -/
noncomputable def lam {Γ : Assembly.{u}} {A : Ty Γ}
    {B : Ty (Assembly.extend Γ (decode A))} (b : Tm _ B) : Tm Γ (pi A B) :=
  unmapTerm (fun γ ↦ TypeObj.piRealizerIso (A γ) (fun a ↦ B ⟨γ, a⟩))
    (Assembly.lambda b)

/-- The large-assembly presentation of a represented product term. -/
noncomputable def toPi {Γ : Assembly.{u}} {A : Ty Γ}
    {B : Ty (Assembly.extend Γ (decode A))} (f : Tm Γ (pi A B)) :
    Assembly.Tm Γ (Assembly.piTy (decode A) (decode B)) :=
  mapTerm (fun γ ↦ TypeObj.piRealizerIso (A γ) (fun a ↦ B ⟨γ, a⟩)) f

/-- Application in the generic extended context. -/
noncomputable def unlam {Γ : Assembly.{u}} {A : Ty Γ}
    {B : Ty (Assembly.extend Γ (decode A))} (f : Tm Γ (pi A B)) : Tm _ B where
  toFun p := ((toPi f).toFun p.1).val p.2
  tracked := by
    obtain ⟨e, he⟩ := (toPi f).tracked
    refine ⟨Kleene.applyCode (Kleene.compCode e Kleene.fstCode) Kleene.sndCode, ?_⟩
    intro p n hn
    obtain ⟨d, hd, hdf⟩ := he p.1 (Nat.unpair n).1 hn.1
    obtain ⟨m, hm, hmb⟩ := hdf p.2 (Nat.unpair n).2 hn.2
    refine ⟨m, ?_, hmb⟩
    rw [Kleene.app_applyCode, Kleene.app_compCode]
    exact Part.mem_bind (Part.mem_bind (by simp) hd) (Part.mem_bind (by simp) hm)

theorem unlam_lam {Γ : Assembly.{u}} {A : Ty Γ}
    {B : Ty (Assembly.extend Γ (decode A))} (b : Tm _ B) : unlam (lam b) = b := by
  apply Assembly.Tm.ext
  intro p
  change (((TypeObj.piRealizerIso (A p.1) (fun a ↦ B ⟨p.1, a⟩)).toEquiv
    ((TypeObj.piRealizerIso (A p.1) (fun a ↦ B ⟨p.1, a⟩)).toEquiv.symm
      ((Assembly.lambda b).toFun p.1))).val p.2) = b.toFun p
  exact congrArg (fun q ↦ q.val p.2)
    ((TypeObj.piRealizerIso (A p.1) (fun a ↦ B ⟨p.1, a⟩)).toEquiv.apply_symm_apply _)

theorem lam_unlam {Γ : Assembly.{u}} {A : Ty Γ}
    {B : Ty (Assembly.extend Γ (decode A))} (f : Tm Γ (pi A B)) : lam (unlam f) = f := by
  apply Assembly.Tm.ext
  intro γ
  apply (TypeObj.piRealizerIso (A γ) (fun a ↦ B ⟨γ, a⟩)).toEquiv.injective
  change (TypeObj.piRealizerIso (A γ) (fun a ↦ B ⟨γ, a⟩)).toEquiv
    ((TypeObj.piRealizerIso (A γ) (fun a ↦ B ⟨γ, a⟩)).toEquiv.symm
      ((Assembly.lambda (unlam f)).toFun γ)) = _
  exact ((TypeObj.piRealizerIso (A γ) (fun a ↦ B ⟨γ, a⟩)).toEquiv.apply_symm_apply _).trans
    (Subtype.ext rfl)

/-- The represented products satisfy the contextual Π rules, including substitution. -/
noncomputable def products : Theory.DependentProducts cwf.{u} where
  pi := pi
  pi_sub _ _ _ := rfl
  lam := lam
  unlam := unlam
  beta := unlam_lam
  eta := lam_unlam
  lam_sub _ _ := Assembly.Tm.ext fun _ ↦ rfl

/-- Nondependent arrows are the constant-fiber case of represented products. -/
noncomputable def arrow {Γ : Assembly.{u}} (A B : Ty Γ) : Ty Γ :=
  pi A (fun p ↦ B p.1)

/-- Application for the constant-fiber case. -/
noncomputable def app {Γ : Assembly.{u}} {A B : Ty Γ}
    (f : Tm Γ (arrow A B)) (a : Tm Γ A) : Tm Γ B :=
  Assembly.apply (toPi f) a

/-- The nondependent function fragment used by internal wild functors. -/
noncomputable def functions : Theory.FunctionTypes cwf.{u} where
  arr := arrow
  arr_sub _ _ _ := rfl
  lam := lam
  app := app
  beta {Γ A B} b a := by
    apply heq_of_eq
    apply Assembly.Tm.ext
    intro γ
    exact congrArg (fun t : Tm (Assembly.extend Γ (decode A)) (fun p ↦ B p.1) ↦
      t.toFun ⟨γ, a.toFun γ⟩) (unlam_lam b)
  eta f := lam_unlam f
  app_sub _ _ _ := Assembly.Tm.ext fun _ ↦ rfl
  lam_sub b σ b' h := by
    apply Assembly.Tm.ext
    intro δ
    have hb := eq_of_heq h
    subst b'
    rfl

end Interpretation
end LaarakkerOttenVanDenBerg2026.V2

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_InterpretationIdentityV2 -/

/-!
The extensional identity interpretation of Appendix C.4. Equality reflection
below is proved for this concrete model; it is not a rule of the abstract theory.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Interpretation

universe u
open Assembly

/-- Identity types are the small singleton/empty PER, pointwise in the context. -/
def identityRules : Theory.IdentityTypes cwf.{u} where
  id _ a b := fun γ ↦ TypeObj.small (identityPER (a.toFun γ) (b.toFun γ))
  refl a := {
    toFun := fun _ ↦ ULift.up ((identityPER _ _).classOf 0 rfl)
    tracked := ⟨Kleene.constCode 0, fun _ _ _ ↦ ⟨0, by simp,
      (identityPER _ _).realises_self 0 rfl⟩⟩ }
  id_sub _ _ _ := rfl
  refl_sub _ _ := HEq.rfl

/-- The concrete interpretation is extensional, as the paper states. -/
theorem identity_reflect {Γ : Assembly.{u}} {A : Ty Γ} {a b : Tm Γ A}
    (p : Tm Γ (identityRules.id A a b)) : a = b := by
  apply Assembly.Tm.ext
  intro γ
  obtain ⟨n, hn, _⟩ := (identityPER (a.toFun γ) (b.toFun γ)).realised (p.toFun γ).down
  exact hn

/-- Proofs of an interpreted identity are unique; this is a model theorem only. -/
theorem identity_proof_unique {Γ : Assembly.{u}} {A : Ty Γ} {a b : Tm Γ A}
    (p q : Tm Γ (identityRules.id A a b)) : p = q := by
  apply Assembly.Tm.ext
  intro γ
  apply ULift.ext
  obtain ⟨n, hn, hp⟩ := (identityPER (a.toFun γ) (b.toFun γ)).realised (p.toFun γ).down
  obtain ⟨m, hm, hq⟩ := (identityPER (a.toFun γ) (b.toFun γ)).realised (q.toFun γ).down
  exact hp.symm.trans ((((identityPER _ _).classOf_eq_iff hn hm).mpr hn).trans hq)

/-- Based J is validated by the singleton/empty identity interpretation. -/
def identityElimination : Theory.IdentityElimination cwf.{u} identityRules where
  elim := by
    intro Γ A a M d b p
    have hb : b = a := (identity_reflect p).symm
    subst b
    have hp : p = identityRules.refl a := identity_proof_unique _ _
    subst p
    exact d
  beta _ _ _ := rfl

end LaarakkerOttenVanDenBerg2026.V2.Interpretation

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_InterpretationBaseV2 -/

/-!
# The empty, unit and Boolean rules in the assembly interpretation

The basic types are decoded PER codes. Their eliminators remain tracked even
for large dependent motives. Boolean elimination inspects the tag of a realizing
pair and executes only the chosen branch's partial recursive tracker.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Interpretation

universe u
open Assembly

/-- The constant code for a basic PER. -/
def baseCode {Γ : Assembly.{u}} (R : PER) : universeRules.Code Γ :=
  universeTerm Γ (fun _ => R)

def unitValue : (perAssembly.{u} unitPER).Carrier :=
  ULift.up (unitPER.classOf 0 trivial)

def falseValue : (perAssembly.{u} boolPER).Carrier := ULift.up boolFalse

def trueValue : (perAssembly.{u} boolPER).Carrier := ULift.up boolTrue

theorem unitValue_unique (x : (perAssembly.{u} unitPER).Carrier) : x = unitValue :=
  ULift.ext _ _ (Subsingleton.elim x.down _)

theorem trueValue_ne_falseValue : trueValue.{u} ≠ falseValue.{u} := by
  intro h
  exact boolFalse_ne_boolTrue (congrArg ULift.down h).symm

theorem boolValue_cases (x : (perAssembly.{u} boolPER).Carrier) :
    x = falseValue ∨ x = trueValue := by
  rcases boolPER_cases x.down with h | h
  · exact Or.inl (ULift.ext _ _ h)
  · exact Or.inr (ULift.ext _ _ h)

theorem boolValue_eq_true {x : (perAssembly.{u} boolPER).Carrier}
    (h : x ≠ falseValue) : x = trueValue :=
  (boolValue_cases x).resolve_left h

/-- The constant unit term is tracked by the constant zero program. -/
def unitTerm {Γ : Assembly.{u}} : Tm Γ (universeRules.el (baseCode unitPER)) where
  toFun _ := unitValue
  tracked := ⟨Kleene.constCode 0, fun _ _ _ =>
    ⟨0, by simp, unitPER.realises_self 0 trivial⟩⟩

/-- The false constructor is tracked by a constant tagged pair. -/
def falseTerm {Γ : Assembly.{u}} : Tm Γ (universeRules.el (baseCode boolPER)) where
  toFun _ := falseValue
  tracked := ⟨Kleene.constCode (Nat.pair 0 0), fun _ _ _ =>
    ⟨Nat.pair 0 0, by simp,
      (boolPER_realises_false _).mpr (by simp only [Nat.unpair_pair])⟩⟩

/-- The true constructor is tracked by the other constant tagged pair. -/
def trueTerm {Γ : Assembly.{u}} : Tm Γ (universeRules.el (baseCode boolPER)) where
  toFun _ := trueValue
  tracked := ⟨Kleene.constCode (Nat.pair 1 0), fun _ _ _ =>
    ⟨Nat.pair 1 0, by simp,
      (boolPER_realises_true _).mpr (by simp only [Nat.unpair_pair])⟩⟩

/-- The empty context extension has no elements, so elimination is unique. -/
def emptyElim {Γ : Assembly.{u}}
    (M : Ty (Assembly.extend Γ (fun _ => perAssembly.{u} botPER))) : Tm _ M where
  toFun p := isEmptyElim p.2.down
  tracked := ⟨Kleene.idCode, fun p => isEmptyElim p.2.down⟩

/-- Dependent unit elimination transports along the unique unit value. -/
def unitElim {Γ : Assembly.{u}}
    (M : Ty (Assembly.extend Γ (fun _ => perAssembly.{u} unitPER)))
    (d : Tm Γ (fun γ => M ⟨γ, unitValue⟩)) : Tm _ M where
  toFun p := cast
    (congrArg (fun x => (M ⟨p.1, x⟩).asAssembly.Carrier) (unitValue_unique p.2).symm)
      (d.toFun p.1)
  tracked := by
    obtain ⟨e, he⟩ := d.tracked
    refine ⟨Kleene.compCode e Kleene.fstCode, ?_⟩
    intro ⟨γ, x⟩ n hn
    have hx : x = unitValue := unitValue_unique x
    subst x
    obtain ⟨m, hm, hmd⟩ := he γ n.unpair.1 hn.1
    refine ⟨m, ?_, hmd⟩
    rw [Kleene.app_compCode]
    exact Part.mem_bind (by simp) hm

/-- The dependent Boolean case distinction has no unsupported default value. -/
noncomputable def boolElimValue {Γ : Assembly.{u}}
    (M : Ty (Assembly.extend Γ (fun _ => perAssembly.{u} boolPER)))
    (f : Tm Γ (fun γ => M ⟨γ, falseValue⟩))
    (t : Tm Γ (fun γ => M ⟨γ, trueValue⟩))
    (p : (Assembly.extend Γ (fun _ => perAssembly.{u} boolPER)).Carrier) :
    (M p).asAssembly.Carrier := by
  classical
  exact if h : p.2 = falseValue then
    cast (congrArg (fun x => (M ⟨p.1, x⟩).asAssembly.Carrier) h.symm) (f.toFun p.1)
    else cast (congrArg (fun x => (M ⟨p.1, x⟩).asAssembly.Carrier)
      (boolValue_eq_true h).symm) (t.toFun p.1)

theorem boolElimValue_false {Γ : Assembly.{u}}
    (M : Ty (Assembly.extend Γ (fun _ => perAssembly.{u} boolPER)))
    (f : Tm Γ (fun γ => M ⟨γ, falseValue⟩))
    (t : Tm Γ (fun γ => M ⟨γ, trueValue⟩)) (γ : Γ.Carrier) :
    boolElimValue M f t ⟨γ, falseValue⟩ = f.toFun γ := by
  exact dif_pos rfl

theorem boolElimValue_true {Γ : Assembly.{u}}
    (M : Ty (Assembly.extend Γ (fun _ => perAssembly.{u} boolPER)))
    (f : Tm Γ (fun γ => M ⟨γ, falseValue⟩))
    (t : Tm Γ (fun γ => M ⟨γ, trueValue⟩)) (γ : Γ.Carrier) :
    boolElimValue M f t ⟨γ, trueValue⟩ = t.toFun γ := by
  exact dif_neg trueValue_ne_falseValue

private def boolBranch (d e n : ℕ) : ℕ :=
  Nat.casesOn n.unpair.2.unpair.1 d (fun _ => e)

private theorem boolBranch_computable (d e : ℕ) : Computable (boolBranch d e) :=
  Computable.nat_casesOn
    ((Computable.fst.comp Computable.unpair).comp
      (Computable.snd.comp Computable.unpair))
    (Computable.const d) (Computable.const e)

private noncomputable def boolSelectCode (d e : ℕ) : ℕ :=
  (Kleene.exists_index_of_computable (boolBranch_computable d e)).choose

private theorem app_boolSelectCode (d e n : ℕ) :
    Kleene.app (boolSelectCode d e) n = Part.some (boolBranch d e n) :=
  (Kleene.exists_index_of_computable (boolBranch_computable d e)).choose_spec n

/-- A Boolean case program selects a branch index before evaluating that branch.
In particular, divergence of the unselected branch is irrelevant. -/
noncomputable def boolCaseCode (d e : ℕ) : ℕ :=
  Kleene.applyCode (boolSelectCode d e) Kleene.fstCode

private theorem app_boolCaseCode (d e n : ℕ) :
    Kleene.app (boolCaseCode d e) n = Kleene.app (boolBranch d e n) n.unpair.1 := by
  simp only [boolCaseCode, Kleene.app_applyCode, app_boolSelectCode,
    Kleene.app_fstCode, Part.bind_some]

theorem app_boolCaseCode_zero (d e n : ℕ) (h : n.unpair.2.unpair.1 = 0) :
    Kleene.app (boolCaseCode d e) n = Kleene.app d n.unpair.1 := by
  rw [app_boolCaseCode]
  simp only [boolBranch, h]
  rfl

theorem app_boolCaseCode_one (d e n : ℕ) (h : n.unpair.2.unpair.1 = 1) :
    Kleene.app (boolCaseCode d e) n = Kleene.app e n.unpair.1 := by
  rw [app_boolCaseCode]
  simp only [boolBranch, h]
  rfl

/-- Dependent Boolean elimination, with a lazy partial recursive branch tracker. -/
noncomputable def boolElim {Γ : Assembly.{u}}
    (M : Ty (Assembly.extend Γ (fun _ => perAssembly.{u} boolPER)))
    (f : Tm Γ (fun γ => M ⟨γ, falseValue⟩))
    (t : Tm Γ (fun γ => M ⟨γ, trueValue⟩)) : Tm _ M where
  toFun := boolElimValue M f t
  tracked := by
    obtain ⟨d, hd⟩ := f.tracked
    obtain ⟨e, he⟩ := t.tracked
    refine ⟨boolCaseCode d e, ?_⟩
    intro ⟨γ, x⟩ n hn
    rcases boolValue_cases x with hx | hx
    · subst x
      obtain ⟨m, hm, hmf⟩ := hd γ n.unpair.1 hn.1
      refine ⟨m, ?_, ?_⟩
      · rw [app_boolCaseCode_zero d e n ((boolPER_realises_false _).mp hn.2)]
        exact hm
      · exact (boolElimValue_false M f t γ).symm ▸ hmf
    · subst x
      obtain ⟨m, hm, hmt⟩ := he γ n.unpair.1 hn.1
      refine ⟨m, ?_, ?_⟩
      · rw [app_boolCaseCode_one d e n ((boolPER_realises_true _).mp hn.2)]
        exact hm
      · exact (boolElimValue_true M f t γ).symm ▸ hmt

/-- The source's basic codes, constructors, dependent eliminators, and equations. -/
noncomputable def baseTypes : Theory.BaseTypes universeRules.{u} where
  empty := baseCode botPER
  unit := baseCode unitPER
  bool := baseCode boolPER
  star := unitTerm
  false := falseTerm
  true := trueTerm
  empty_sub _ := Assembly.Tm.ext fun _ => rfl
  unit_sub _ := Assembly.Tm.ext fun _ => rfl
  bool_sub _ := Assembly.Tm.ext fun _ => rfl
  star_sub _ := HEq.rfl
  false_sub _ := HEq.rfl
  true_sub _ := HEq.rfl
  emptyElim := emptyElim
  unitElim := unitElim
  unit_beta _ _ := Assembly.Tm.ext fun _ => rfl
  boolElim := boolElim
  bool_beta_false M f t := Assembly.Tm.ext (boolElimValue_false M f t)
  bool_beta_true M f t := Assembly.Tm.ext (boolElimValue_true M f t)

end LaarakkerOttenVanDenBerg2026.V2.Interpretation

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_InterpretationSizesV2 -/

/-! The large size type and its small preorder, Section 4.3 and Appendix C.7. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Interpretation

open Assembly
universe u

/-- A section whose values all have realizer zero is tracked by a constant. -/
def zeroRealizedTerm {Γ : Assembly.{u}} (R : Γ.Carrier → PER)
    (h : ∀ γ, (R γ).rel 0 0) :
    Tm Γ (fun γ ↦ TypeObj.small (R γ)) where
  toFun γ := ULift.up ((R γ).classOf 0 (h γ))
  tracked := ⟨Kleene.constCode 0, fun γ _ _ ↦ ⟨0, by simp, (R γ).realises_self _ _⟩⟩

/-- The size and order rules interpreted by countable ordinals. -/
def sizes : Theory.SizeRules cwf.{1} universeRules identityRules where
  type _ := fun _ ↦ TypeObj.large sizeAssembly
  type_sub _ := rfl
  zero := {
    toFun _ := sizeZero
    tracked := ⟨Kleene.constCode 0, fun _ _ _ ↦ ⟨0, by simp, trivial⟩⟩ }
  succ i := {
    toFun γ := sizeSucc (i.toFun γ)
    tracked := ⟨Kleene.constCode 0, fun _ _ _ ↦ ⟨0, by simp, trivial⟩⟩ }
  le i j := universeTerm _ (fun γ ↦ sizeLePER (i.toFun γ) (j.toFun γ))
  le_zero i := zeroRealizedTerm _ (fun _ ↦ zero_le)
  le_succ i := zeroRealizedTerm _ (fun _ ↦ (Order.lt_add_one_iff.mpr (le_refl _)).le)
  le_refl i := zeroRealizedTerm _ (fun γ ↦ le_refl _)
  le_trans p q := by
    apply zeroRealizedTerm
    intro γ
    obtain ⟨n, hn, _⟩ := (sizeLePER _ _).realised (p.toFun γ).down
    obtain ⟨m, hm, _⟩ := (sizeLePER _ _).realised (q.toFun γ).down
    exact le_trans hn hm
  le_prop p q := by
    have hpq : p = q := by
      apply Assembly.Tm.ext
      intro γ
      apply ULift.ext
      obtain ⟨n, hn, hp⟩ := (sizeLePER _ _).realised (p.toFun γ).down
      obtain ⟨m, hm, hq⟩ := (sizeLePER _ _).realised (q.toFun γ).down
      exact hp.symm.trans ((((sizeLePER _ _).classOf_eq_iff hn hm).mpr hn).trans hq)
    subst q
    exact identityRules.refl p

end LaarakkerOttenVanDenBerg2026.V2.Interpretation

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_ReflectionFamiliesV2 -/

/-! Fiberwise modest reflection and its contextual dependent elimination. -/

namespace LaarakkerOttenVanDenBerg2026.V2

universe u
open Assembly

/-- Reflect each fiber, leaving the ambient context unchanged. -/
def reflectFamily {Γ : Assembly.{u}} (A : Ty Γ) : Ty Γ :=
  fun γ ↦ (reflectModest (A γ)).toAssembly

/-- The fiberwise quotient substitution preserves the paired realizing code. -/
def reflectFamilyUnit {Γ : Assembly.{u}} (A : Ty Γ) :
    Assembly.Hom (extend Γ A) (extend Γ (reflectFamily A)) where
  toFun p := ⟨p.1, Quot.mk (sharedRealiser (A p.1)) p.2⟩
  tracked := ⟨Kleene.idCode, fun p n hn ↦
    ⟨n, by simp, hn.1, p.2, rfl, hn.2⟩⟩

/-- Dependent elimination into modest fibers is valid uniformly in every context. -/
theorem exists_reflectFamilyElim {Γ : Assembly.{u}} (A : Ty Γ)
    (B : Ty (extend Γ (reflectFamily A))) (hB : ∀ p, IsModest (B p))
    (b : Tm (extend Γ A) (substTy B (reflectFamilyUnit A))) :
    ∃ a : Tm (extend Γ (reflectFamily A)) B,
      substTm a (reflectFamilyUnit A) = b := by
  let branch (γ : Γ.Carrier) :
      Tm (A γ) (fun x ↦ B ⟨γ, Quot.mk (sharedRealiser (A γ)) x⟩) := {
    toFun x := b.toFun ⟨γ, x⟩
    tracked := by
      obtain ⟨e, he⟩ := b.tracked
      obtain ⟨k, hk⟩ := Γ.realised γ
      refine ⟨Kleene.curryCode e k, ?_⟩
      intro x n hn
      obtain ⟨m, hm, hmb⟩ := he ⟨γ, x⟩ (Nat.pair k n)
        (by simpa only [extend, Nat.unpair_pair] using And.intro hk hn)
      exact ⟨m, by simpa only [Kleene.app_curryCode] using hm, hmb⟩ }
  have hex (γ : Γ.Carrier) :
      ∃ a : Tm (reflectModest (A γ)).toAssembly (fun q ↦ B ⟨γ, q⟩),
        substTm a (reflectUnit (A γ)) = branch γ :=
    exists_reflectElim (A γ) (fun q ↦ B ⟨γ, q⟩) (fun q ↦ hB ⟨γ, q⟩) (branch γ)
  let fiber (γ : Γ.Carrier) := (hex γ).choose
  have hfiber (γ : Γ.Carrier) (x : (A γ).Carrier) :
      (fiber γ).toFun (Quot.mk (sharedRealiser (A γ)) x) = b.toFun ⟨γ, x⟩ :=
    congrArg (fun t : Tm (A γ) _ ↦ t.toFun x) (hex γ).choose_spec
  let a : Tm (extend Γ (reflectFamily A)) B := {
    toFun p := (fiber p.1).toFun p.2
    tracked := by
      obtain ⟨e, he⟩ := b.tracked
      refine ⟨e, ?_⟩
      rintro ⟨γ, q⟩ n ⟨hγ, x, hx, hnx⟩
      dsimp only at hx hγ hnx
      obtain ⟨m, hm, hmb⟩ := he ⟨γ, x⟩ n ⟨hγ, hnx⟩
      refine ⟨m, hm, ?_⟩
      have hh : (B ⟨γ, Quot.mk (sharedRealiser (A γ)) x⟩).realises m
          ((fiber γ).toFun (Quot.mk (sharedRealiser (A γ)) x)) :=
        (hfiber γ x) ▸ hmb
      exact hx ▸ hh }
  exact ⟨a, Assembly.Tm.ext fun p ↦ hfiber p.1 p.2⟩

/-- Fiberwise quotienting loses no information about a descended section. -/
theorem reflectFamilyElim_unique {Γ : Assembly.{u}} (A : Ty Γ)
    (B : Ty (extend Γ (reflectFamily A)))
    (a b : Tm (extend Γ (reflectFamily A)) B)
    (h : substTm a (reflectFamilyUnit A) = substTm b (reflectFamilyUnit A)) : a = b := by
  apply Assembly.Tm.ext
  rintro ⟨γ, q⟩
  induction q using Quot.inductionOn with
  | h x => exact congrArg (fun t : Tm (extend Γ A) _ ↦ t.toFun ⟨γ, x⟩) h

end LaarakkerOttenVanDenBerg2026.V2

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_InterpretationExistsV2 -/

/-! Existential size quantification is the modest reflection of the large sum. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Interpretation

open Assembly

private theorem castTerm_apply_heq {Γ : Assembly.{1}} {A B : Assembly.Ty Γ}
    (h : A = B) (a : Assembly.Tm Γ A) (γ : Γ.Carrier) :
    HEq ((cast (congrArg (Assembly.Tm Γ) h) a).toFun γ) (a.toFun γ) := by
  cases h
  rfl

/-- The large sum whose modest reflection interprets existential quantification. -/
def exSum {Γ : Assembly.{1}}
    (A : universeRules.Code (cwf.ext Γ (sizes.type Γ))) : Assembly.Ty Γ :=
  fun γ ↦ Assembly.extend sizeAssembly (fun i ↦ perAssembly (A.toFun ⟨γ, i⟩).down)

/-- Existential formation uses the literal reflection PER. -/
def exCode {Γ : Assembly.{1}}
    (A : universeRules.Code (cwf.ext Γ (sizes.type Γ))) : universeRules.Code Γ :=
  universeTerm Γ (fun γ ↦ truncatePER (exSum A γ))

/-- The PER presentation and the reflected sum preserve every realizer. -/
noncomputable def exIso {Γ : Assembly.{1}}
    (A : universeRules.Code (cwf.ext Γ (sizes.type Γ))) (γ : Γ.Carrier) :
    RealizerIso (decode (universeRules.el (exCode A)) γ) (reflectFamily (exSum A) γ) :=
  modestPERRealizerIso (reflectModest (exSum A γ))

/-- The existential constructor as a context substitution. -/
noncomputable def exPairSub {Γ : Assembly.{1}}
    (A : universeRules.Code (cwf.ext Γ (sizes.type Γ))) :
    Hom (cwf.ext (cwf.ext Γ (sizes.type Γ)) (universeRules.el A))
      (cwf.ext Γ (universeRules.el (exCode A))) :=
  Hom.comp (Hom.comp (associate (fun _ ↦ sizeAssembly) (decode (universeRules.el A)))
    (reflectFamilyUnit (exSum A))) (fiberBackward (exIso A))

/-- The generic existential pair. -/
noncomputable def exPair {Γ : Assembly.{1}}
    (A : universeRules.Code (cwf.ext Γ (sizes.type Γ))) :
    cwf.Tm (cwf.ext (cwf.ext Γ (sizes.type Γ)) (universeRules.el A))
      (cwf.tySub (universeRules.el (exCode A)) (cwf.comp cwf.fst cwf.fst)) :=
  Assembly.substTm (Assembly.lastVar Γ _) (exPairSub A)

/-- Dependent existential elimination into a small family, with its computation rule. -/
theorem exists_exElim {Γ : Assembly.{1}}
    (A : universeRules.Code (cwf.ext Γ (sizes.type Γ)))
    (M : universeRules.Code (cwf.ext Γ (universeRules.el (exCode A))))
    (b : cwf.Tm (cwf.ext (cwf.ext Γ (sizes.type Γ)) (universeRules.el A))
      (cwf.tySub (universeRules.el M) (cwf.pair (cwf.comp cwf.fst cwf.fst) (exPair A)))) :
    ∃ a : cwf.Tm (cwf.ext Γ (universeRules.el (exCode A))) (universeRules.el M),
      cwf.tmSub a (cwf.pair (cwf.comp cwf.fst cwf.fst) (exPair A)) = b := by
  let e := exIso A
  let B := Assembly.substTy (decode (universeRules.el M)) (fiberBackward e)
  let branch : Assembly.Tm (Assembly.extend Γ (exSum A))
      (Assembly.substTy B (reflectFamilyUnit (exSum A))) :=
    Assembly.substTm b (unassociate (fun _ ↦ sizeAssembly) (decode (universeRules.el A)))
  obtain ⟨d, hd⟩ := exists_reflectFamilyElim (exSum A) B
    (fun p ↦ perAssembly_modest _) branch
  have htype : Assembly.substTy B (fiberForward e) = decode (universeRules.el M) := by
    funext p
    exact congrArg (decode (universeRules.el M))
      (congrArg (Sigma.mk p.1) ((e p.1).toEquiv.symm_apply_apply p.2))
  let a : cwf.Tm (cwf.ext Γ (universeRules.el (exCode A))) (universeRules.el M) :=
    cast (congrArg (Assembly.Tm (cwf.ext Γ (universeRules.el (exCode A)))) htype)
      (Assembly.substTm d (fiberForward e))
  refine ⟨a, ?_⟩
  apply Assembly.Tm.ext
  intro p
  have hd' := congrArg (fun t ↦ t.toFun ⟨p.1.1, p.1.2, p.2⟩) hd
  dsimp only [Assembly.substTm, reflectFamilyUnit, branch, unassociate] at hd'
  have hq := (e p.1.1).toEquiv.apply_symm_apply
    (Quot.mk (sharedRealiser (exSum A p.1.1)) ⟨p.1.2, p.2⟩)
  have ha : HEq (a.toFun ((exPairSub A).toFun p))
      (d.toFun ((fiberForward e).toFun ((exPairSub A).toFun p))) := by
    exact castTerm_apply_heq htype _ _
  apply eq_of_heq
  apply ha.trans
  have hctx : (fiberForward e).toFun ((exPairSub A).toFun p) =
      ⟨p.1.1, Quot.mk (sharedRealiser (exSum A p.1.1)) ⟨p.1.2, p.2⟩⟩ :=
    congrArg (Sigma.mk p.1.1) hq
  exact (congr_arg_heq d.toFun hctx).trans (heq_of_eq hd')

/-- The source existential rules with no chosen trackers in the interface. -/
noncomputable def existential : Theory.ExistentialSizeQuantifier cwf.{1}
    universeRules identityRules sizes where
  code := exCode
  pair := exPair
  elim A M b := (exists_exElim A M b).choose
  beta A M b := (exists_exElim A M b).choose_spec

/-- Every existential value has a representative in the untruncated sum. -/
theorem exPairSub_surjective {Γ : Assembly.{1}}
    (A : universeRules.Code (cwf.ext Γ (sizes.type Γ))) :
    Function.Surjective (exPairSub A).toFun := by
  rintro ⟨γ, q⟩
  obtain ⟨x, hx⟩ := Quot.exists_rep ((exIso A γ).toEquiv q)
  refine ⟨⟨⟨γ, x.1⟩, x.2⟩, ?_⟩
  exact congrArg (Sigma.mk γ)
    ((congrArg (exIso A γ).toEquiv.symm hx).trans
      ((exIso A γ).toEquiv.symm_apply_apply q))

/-- A dependent section of an existential type is determined by its values on pairs. -/
theorem exElim_unique {Γ : Assembly.{1}}
    (A : universeRules.Code (cwf.ext Γ (sizes.type Γ)))
    (M : Ty (cwf.ext Γ (universeRules.el (exCode A))))
    (a b : Tm _ M)
    (h : Assembly.substTm a (exPairSub A) = Assembly.substTm b (exPairSub A)) : a = b := by
  apply Assembly.Tm.ext
  intro q
  obtain ⟨p, rfl⟩ := exPairSub_surjective A q
  exact congrArg (fun t => t.toFun p) h

/-- Existential PER codes commute with contextual substitution. -/
theorem existentialSubstitution : Theory.ExistentialSizeSubstitution
    universeRules identityRules sizes existential where
  code_sub _ _ := Assembly.Tm.ext fun _ => rfl

/-- The existential constructor commutes with substitution. -/
theorem exPair_sub {Γ Δ : Assembly.{1}}
    (A : universeRules.Code (cwf.ext Γ (sizes.type Γ))) (σ : cwf.Sub Δ Γ) :
    HEq (cwf.tmSub (existential.pair A) (universeRules.liftEl (sizes.lift σ) A))
      (existential.pair (universeRules.sub A (sizes.lift σ))) := by
  apply heq_of_eq
  exact Assembly.Tm.ext fun _ => rfl

/-- Pairing and dependent existential elimination both commute with substitution.
The elimination equation follows from the computation rule and uniqueness on pairs. -/
theorem existentialTermSubstitution : Theory.ExistentialTermSubstitution
    universeRules identityRules sizes existential existentialSubstitution where
  pair_sub := exPair_sub
  elim_sub := by
    intro Γ Δ A M b σ b' h
    let A' := universeRules.sub A (sizes.lift σ)
    let τ := universeRules.liftElAs σ (existential.code A) (existential.code A')
      (existentialSubstitution.code_sub A σ)
    let M' := universeRules.sub M τ
    apply heq_of_eq
    apply exElim_unique A'
    apply Assembly.Tm.ext
    intro p
    have hleft := congrArg
      (fun t => t.toFun ((universeRules.liftEl (sizes.lift σ) A).toFun p))
      (existential.beta A M b)
    have hright := congrArg (fun t => t.toFun p) (existential.beta A' M' b')
    have hbranch := congrArg (fun t => t.toFun p) (eq_of_heq h)
    exact hleft.trans (hbranch.trans hright.symm)

end LaarakkerOttenVanDenBerg2026.V2.Interpretation

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_InterpretationForallV2 -/

/-! Universal size quantification interpreted as the literal small product. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Interpretation

open Assembly

/-- The source small-product code over the large size assembly. -/
def allCode {Γ : Assembly.{1}}
    (A : universeRules.Code (cwf.ext Γ (sizes.type Γ))) : universeRules.Code Γ :=
  universeTerm Γ (fun γ ↦ forallPER (fun i ↦ (A.toFun ⟨γ, i⟩).down))

/-- The literal small product and the large dependent product preserve realizers. -/
noncomputable def allIso {Γ : Assembly.{1}}
    (A : universeRules.Code (cwf.ext Γ (sizes.type Γ))) (γ : Γ.Carrier) :
    RealizerIso (decode (universeRules.el (allCode A)) γ)
      (Assembly.piTy (fun _ ↦ sizeAssembly) (decode (universeRules.el A)) γ) :=
  smallPiRealizerIso sizeAssembly (fun i ↦ (A.toFun ⟨γ, i⟩).down)

/-- Universal introduction accepts exactly a contextual term over Size. -/
noncomputable def allLam {Γ : Assembly.{1}}
    {A : universeRules.Code (cwf.ext Γ (sizes.type Γ))}
    (a : Tm (cwf.ext Γ (sizes.type Γ)) (universeRules.el A)) :
    Tm Γ (universeRules.el (allCode A)) :=
  unmapTerm (allIso A) (Assembly.lambda a)

/-- Generic universal application, using partial application of the PER realizer. -/
noncomputable def allUnlam {Γ : Assembly.{1}}
    {A : universeRules.Code (cwf.ext Γ (sizes.type Γ))}
    (f : Tm Γ (universeRules.el (allCode A))) :
    Tm (cwf.ext Γ (sizes.type Γ)) (universeRules.el A) :=
  unlam (A := sizes.type Γ) (B := universeRules.el A) (mapTerm (allIso A) f)

theorem allUnlam_lam {Γ : Assembly.{1}}
    {A : universeRules.Code (cwf.ext Γ (sizes.type Γ))}
    (a : Tm (cwf.ext Γ (sizes.type Γ)) (universeRules.el A)) :
    allUnlam (allLam a) = a := by
  apply Assembly.Tm.ext
  intro p
  exact congrArg (fun f ↦ f.val p.2) ((allIso A p.1).toEquiv.apply_symm_apply _)

theorem allLam_unlam {Γ : Assembly.{1}}
    {A : universeRules.Code (cwf.ext Γ (sizes.type Γ))}
    (f : Tm Γ (universeRules.el (allCode A))) : allLam (allUnlam f) = f := by
  apply Assembly.Tm.ext
  intro γ
  apply (allIso A γ).toEquiv.injective
  exact ((allIso A γ).toEquiv.apply_symm_apply _).trans (Subtype.ext rfl)

/-- The source universal size-quantifier rules, now interpreted in K1 assemblies. -/
noncomputable def universal : Theory.UniversalSizeQuantifier cwf.{1}
    universeRules identityRules sizes where
  code := allCode
  lam := allLam
  unlam := allUnlam
  beta := allUnlam_lam
  eta := allLam_unlam

end LaarakkerOttenVanDenBerg2026.V2.Interpretation

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_InterpretationNaturalityV2 -/

/-! Substitution stability of the concrete size and universal quantifier rules. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Interpretation

open Assembly

theorem sizeSubstitution : Theory.SizeSubstitution universeRules identityRules sizes where
  zero_sub _ := Assembly.Tm.ext fun _ ↦ rfl
  succ_sub _ _ := Assembly.Tm.ext fun _ ↦ rfl
  le_sub _ _ _ := Assembly.Tm.ext fun _ ↦ rfl
  le_zero_sub _ _ := heq_of_eq (Assembly.Tm.ext fun _ ↦ rfl)
  le_succ_sub _ _ := heq_of_eq (Assembly.Tm.ext fun _ ↦ rfl)
  le_refl_sub _ _ := heq_of_eq (Assembly.Tm.ext fun _ ↦ rfl)
  le_trans_sub p q σ p' q' hp hq := by
    cases eq_of_heq hp
    cases eq_of_heq hq
    exact heq_of_eq (Assembly.Tm.ext fun _ ↦ rfl)
  le_prop_sub {Γ Δ i j} p q σ p' q' hp hq := by
    cases eq_of_heq hp
    cases eq_of_heq hq
    apply heq_of_eq
    exact identity_proof_unique
      (A := cwf.tySub (universeRules.el (sizes.le i j)) σ)
      (a := cwf.tmSub p σ) (b := cwf.tmSub q σ) _ _

theorem universalSubstitution : Theory.UniversalSizeSubstitution
    universeRules identityRules sizes universal where
  code_sub _ _ := Assembly.Tm.ext fun _ ↦ rfl
  lam_sub _ _ := heq_of_eq (Assembly.Tm.ext fun _ ↦ rfl)
  unlam_sub f σ f' h := by
    cases eq_of_heq h
    exact heq_of_eq (Assembly.Tm.ext fun _ ↦ rfl)

end LaarakkerOttenVanDenBerg2026.V2.Interpretation

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_InterpretationSumsV2 -/

/-!
# Contextual dependent sums in the represented assembly model

The small/large sum representation is converted to ordinary dependent pairs by
a realizer-preserving equivalence. Pairing and projections use actual partial
recursive trackers, and their dependent beta and eta equations are proved.
-/

namespace LaarakkerOttenVanDenBerg2026.V2.Interpretation

universe u

open Assembly

/-- Contextual sum formation uses the source's small/large case distinction. -/
noncomputable def sigma {Γ : Assembly.{u}} (A : Ty Γ)
    (B : Ty (Assembly.extend Γ (decode A))) : Ty Γ :=
  fun γ => TypeObj.sigma (A γ) (fun a => B ⟨γ, a⟩)

/-- The ordinary dependent-pair presentation of a represented sum term. -/
noncomputable def toSigma {Γ : Assembly.{u}} {A : Ty Γ}
    {B : Ty (Assembly.extend Γ (decode A))} (p : Tm Γ (sigma A B)) :
    Assembly.Tm Γ (fun γ => Assembly.extend (decode A γ)
      (fun a => decode B ⟨γ, a⟩)) :=
  mapTerm (fun γ => TypeObj.sigmaRealizerIso (A γ) (fun a => B ⟨γ, a⟩)) p

/-- Form a represented pair from two tracked terms. -/
noncomputable def sigmaPair {Γ : Assembly.{u}} {A : Ty Γ}
    {B : Ty (Assembly.extend Γ (decode A))} (a : Tm Γ A)
    (b : Tm Γ (fun γ => B ⟨γ, a.toFun γ⟩)) : Tm Γ (sigma A B) :=
  unmapTerm (fun γ => TypeObj.sigmaRealizerIso (A γ) (fun a => B ⟨γ, a⟩)) {
    toFun γ := ⟨a.toFun γ, b.toFun γ⟩
    tracked := by
      obtain ⟨d, hd⟩ := a.tracked
      obtain ⟨e, he⟩ := b.tracked
      refine ⟨Kleene.pairCode d e, ?_⟩
      intro γ n hn
      obtain ⟨m, hm, hma⟩ := hd γ n hn
      obtain ⟨k, hk, hkb⟩ := he γ n hn
      refine ⟨Nat.pair m k, ?_, ?_⟩
      · rw [Kleene.app_pairCode]
        exact Part.mem_bind hm (Part.mem_map _ hk)
      · simpa only [Assembly.extend, decode, Nat.unpair_pair] using And.intro hma hkb }

/-- The first projection has a composed first-projection tracker. -/
noncomputable def sigmaFst {Γ : Assembly.{u}} {A : Ty Γ}
    {B : Ty (Assembly.extend Γ (decode A))} (p : Tm Γ (sigma A B)) : Tm Γ A where
  toFun γ := ((toSigma p).toFun γ).1
  tracked := by
    obtain ⟨e, he⟩ := (toSigma p).tracked
    refine ⟨Kleene.compCode Kleene.fstCode e, ?_⟩
    intro γ n hn
    obtain ⟨m, hm, hmp⟩ := he γ n hn
    refine ⟨m.unpair.1, ?_, hmp.1⟩
    rw [Kleene.app_compCode]
    exact Part.mem_bind hm (by simp)

/-- The second projection retains its dependency on the first. -/
noncomputable def sigmaSnd {Γ : Assembly.{u}} {A : Ty Γ}
    {B : Ty (Assembly.extend Γ (decode A))} (p : Tm Γ (sigma A B)) :
    Tm Γ (fun γ => B ⟨γ, (sigmaFst p).toFun γ⟩) where
  toFun γ := ((toSigma p).toFun γ).2
  tracked := by
    obtain ⟨e, he⟩ := (toSigma p).tracked
    refine ⟨Kleene.compCode Kleene.sndCode e, ?_⟩
    intro γ n hn
    obtain ⟨m, hm, hmp⟩ := he γ n hn
    refine ⟨m.unpair.2, ?_, hmp.2⟩
    rw [Kleene.app_compCode]
    exact Part.mem_bind hm (by simp)

theorem sigmaFst_pair {Γ : Assembly.{u}} {A : Ty Γ}
    {B : Ty (Assembly.extend Γ (decode A))} (a : Tm Γ A)
    (b : Tm Γ (fun γ => B ⟨γ, a.toFun γ⟩)) : sigmaFst (sigmaPair a b) = a := by
  apply Assembly.Tm.ext
  intro γ
  exact congrArg Sigma.fst
    ((TypeObj.sigmaRealizerIso (A γ) (fun a => B ⟨γ, a⟩)).toEquiv.apply_symm_apply
      ⟨a.toFun γ, b.toFun γ⟩)

private theorem term_hext {Γ : Assembly.{u}} {A B : Ty Γ} (hAB : A = B)
    {a : Tm Γ A} {b : Tm Γ B} (h : ∀ γ, HEq (a.toFun γ) (b.toFun γ)) : HEq a b := by
  cases hAB
  apply heq_of_eq
  exact Assembly.Tm.ext fun γ => eq_of_heq (h γ)

theorem sigmaSnd_pair {Γ : Assembly.{u}} {A : Ty Γ}
    {B : Ty (Assembly.extend Γ (decode A))} (a : Tm Γ A)
    (b : Tm Γ (fun γ => B ⟨γ, a.toFun γ⟩)) : HEq (sigmaSnd (sigmaPair a b)) b := by
  apply term_hext
    (congrArg (fun a' : Tm Γ A => fun γ => B ⟨γ, a'.toFun γ⟩) (sigmaFst_pair a b))
  intro γ
  exact congr_arg_heq Sigma.snd
    ((TypeObj.sigmaRealizerIso (A γ) (fun a => B ⟨γ, a⟩)).toEquiv.apply_symm_apply
      ⟨a.toFun γ, b.toFun γ⟩)

theorem sigmaPair_eta {Γ : Assembly.{u}} {A : Ty Γ}
    {B : Ty (Assembly.extend Γ (decode A))} (p : Tm Γ (sigma A B)) :
    sigmaPair (sigmaFst p) (sigmaSnd p) = p := by
  apply Assembly.Tm.ext
  intro γ
  exact (TypeObj.sigmaRealizerIso (A γ) (fun a => B ⟨γ, a⟩)).toEquiv.symm_apply_apply
    (p.toFun γ)

theorem sigmaPair_sub {Γ Δ : Assembly.{u}} {A : Ty Γ}
    {B : Ty (Assembly.extend Γ (decode A))} (a : Tm Γ A)
    (b : Tm Γ (fun γ => B ⟨γ, a.toFun γ⟩)) (σ : Assembly.Hom Δ Γ) :
    Assembly.substTm (sigmaPair a b) σ =
      sigmaPair (A := fun δ => A (σ.toFun δ))
        (B := fun p => B ⟨σ.toFun p.1, p.2⟩)
        (Assembly.substTm a σ) (Assembly.substTm b σ) :=
  Assembly.Tm.ext fun _ => rfl

theorem sigmaFst_sub {Γ Δ : Assembly.{u}} {A : Ty Γ}
    {B : Ty (Assembly.extend Γ (decode A))} (p : Tm Γ (sigma A B))
    (σ : Assembly.Hom Δ Γ) :
    Assembly.substTm (sigmaFst p) σ =
      sigmaFst (A := fun δ => A (σ.toFun δ))
        (B := fun q => B ⟨σ.toFun q.1, q.2⟩) (Assembly.substTm p σ) :=
  Assembly.Tm.ext fun _ => rfl

theorem sigmaSnd_sub {Γ Δ : Assembly.{u}} {A : Ty Γ}
    {B : Ty (Assembly.extend Γ (decode A))} (p : Tm Γ (sigma A B))
    (σ : Assembly.Hom Δ Γ) :
    Assembly.substTm (sigmaSnd p) σ =
      sigmaSnd (A := fun δ => A (σ.toFun δ))
        (B := fun q => B ⟨σ.toFun q.1, q.2⟩) (Assembly.substTm p σ) :=
  Assembly.Tm.ext fun _ => rfl

/-- The represented model satisfies the contextual dependent-sum rules. -/
noncomputable def sums : Theory.DependentSums cwf.{u} where
  sigma := sigma
  sigma_sub _ _ _ := rfl
  pair := sigmaPair
  fst := sigmaFst
  snd := sigmaSnd
  fst_pair := sigmaFst_pair
  snd_pair := sigmaSnd_pair
  eta := sigmaPair_eta

/-- Pairing and both dependent projections satisfy the source substitution rules. -/
theorem sumSubstitution : Theory.DependentSumSubstitution sums.{u} where
  pair_sub a b σ b' h := by
    have hb := eq_of_heq h
    subst b'
    exact heq_of_eq (sigmaPair_sub a b σ)
  fst_sub p σ := sigmaFst_sub p σ
  snd_sub p σ := heq_of_eq (sigmaSnd_sub p σ)

end LaarakkerOttenVanDenBerg2026.V2.Interpretation

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_InterpretationSmallV2 -/

/-! The small constructors and their exact decoder equations from Appendix C. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Interpretation

universe u

/-- Arrows are precisely the constant-family special case of dependent products. -/
theorem functionProductCompatibility : Theory.FunctionProductCompatibility
    functions.{u} products.{u} := {
  arr_eq _ _ := rfl
  lam_eq _ := HEq.rfl }

/-- All three small constructors satisfy equality of decoded type objects. -/
def smallConstructors : Theory.SmallTypeConstructors cwf.{u} universeRules
    products sums identityRules where
  pi A B := universeTerm _ (fun γ ↦ smallPiPER
    (perAssembly (A.toFun γ).down).realises (fun a ↦ (B.toFun ⟨γ, a⟩).down))
  sigma A B := universeTerm _ (fun γ ↦ smallSigmaPER
    (A.toFun γ).down (fun a ↦ (B.toFun ⟨γ, ULift.up a⟩).down))
  id _ a b := universeTerm _ (fun γ ↦ identityPER (a.toFun γ) (b.toFun γ))
  el_pi A B := funext fun γ ↦ (TypeObj.pi_small (A.toFun γ).down
    (fun a ↦ (B.toFun ⟨γ, a⟩).down)).symm
  el_sigma A B := funext fun γ ↦ (TypeObj.sigma_small (A.toFun γ).down
    (fun a ↦ (B.toFun ⟨γ, a⟩).down)).symm
  el_id _ _ _ := rfl

/-- The small codes commute with contextual substitution. -/
theorem smallSubstitution : Theory.SmallTypeSubstitution universeRules.{u}
    products sums identityRules smallConstructors := {
  pi_sub _ _ _ := Assembly.Tm.ext fun _ ↦ rfl
  sigma_sub _ _ _ := Assembly.Tm.ext fun _ ↦ rfl
  id_sub _ _ _ _ := Assembly.Tm.ext fun _ ↦ rfl }

end LaarakkerOttenVanDenBerg2026.V2.Interpretation

/- Module: Definitions.Def_LaarakkerOttenVanDenBerg2026_ModelPresentationV2 -/

/-! The exact concrete data that a full model-soundness theorem must extend.
The carrier CwF is fixed, as are the interpreted primitive type constructors.
Existence of all remaining rules and parametricity is a separate open target. -/

namespace LaarakkerOttenVanDenBerg2026.V2.Interpretation

/-- A full source theory on the specified K1 assembly CwF must use these literal
constructions. Heterogeneous equalities account only for preceding structure
parameters; they do not identify internal identity terms with Lean equality. -/
structure PresentsAssemblyModel (T : Theory.CoreTheory cwf.{1}) : Prop where
  functions_eq : T.functions = functions
  products_eq : T.products = products
  sums_eq : T.sums = sums
  identities_eq : T.identities = identityRules
  identityElimination_eq : HEq T.identityElimination identityElimination
  universe_eq : T.univ = universeRules
  small_eq : HEq T.small smallConstructors
  base_eq : HEq T.base baseTypes
  sizes_eq : HEq T.size sizes
  universal_eq : HEq T.all universal
  existential_eq : HEq T.ex existential

/-- The concrete empty type has no closed section. This does not by itself
assert soundness of the full source theory. -/
theorem no_closed_empty :
    ¬ Nonempty (cwf.{1}.Tm cwf.empty (universeRules.el baseTypes.empty)) := by
  rintro ⟨a⟩
  obtain ⟨n, hn, _⟩ := botPER.realised (a.toFun PUnit.unit).down
  exact hn

/-- The full model-soundness conclusion: these specified assemblies, products,
PERs, sizes, and quantifiers extend to a consistent interpretation of every
source rule and all four parametricity axioms. This is a proposition to prove,
not an assumption in the semantic definitions. -/
def FullModelSoundness : Prop :=
  ∃ T : Theory.ParametricTheory cwf.{1},
    PresentsAssemblyModel T.toCoreTheory ∧ T.toCoreTheory.IsConsistent

end LaarakkerOttenVanDenBerg2026.V2.Interpretation


