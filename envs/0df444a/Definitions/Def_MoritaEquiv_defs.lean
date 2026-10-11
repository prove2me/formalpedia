-- Prove2me | Definitions.Def_MoritaEquiv_defs
-- name    : MoritaEquiv_defs
-- status  : Definition
-- author  : @Alien60
-- created : 2026-10-10T12:56:53.091643+00:00
-- url     : https://prove2.me/theorems/f6a74d27-5b0f-482e-a1c3-6a84157e541e
-- title:
--   Many-sorted first-order logic, Morita extensions and Morita equivalence
-- statement:
--   Self-contained many-sorted first-order logic: signatures `Sig` with dependent arities, de Bruijn terms and formulas in typed contexts, structures `Str` with nonempty carriers, satisfaction, theories as sets of formulas-in-context (universal closures), elementary embeddings and the category `Model T`; `CategoricallyEquivalent`; signature maps `Sig.Hom` with reducts and bijective renamings; `MoritaData L T` (product, coproduct, subsort, quotient sorts and explicitly defined function/predicate symbols with semantic admissibility), the generated signature `D.sig`, defining axioms, the extension `D.ext` and the reduct functor `D.proj`; chains `MoritaReach` and `MoritaEquivalent`; the concrete theories `Ex1.T1`, `Ex1.T2` (Example 4) and `Thm52.T1`, `Thm52.T2` (Theorem 5.2).
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675 (numbering as in arXiv v1), §2–§5 (definitions of explicit definitions, Morita extensions, Morita and categorical equivalence; Examples 1, 4; Theorem 5.2)

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Many-sorted first-order logic and Morita equivalence of theories

Setting of T. W. Barrett and H. Halvorson, "Morita equivalence",
Rev. Symb. Logic 9 (2016) 556–582 (arXiv:1506.04675), §§2–5.

* `Sig` — a many-sorted signature; arities are tuples `Fin m → Srt` (constants are 0-ary).
* `Term`, `Formula` — de Bruijn syntax; contexts are tuples `Γ : Fin n → Srt`, and
  `Formula.all` binds variable `0` (so `all : Formula (Γ' : Fin (n+1) → _) → Formula (Fin.tail Γ')`).
* `Str` — a structure; **every sort is nonempty** (the classical convention, needed e.g. for
  the paper's Example 4).
* `Axiom`, `Theory` — a theory is a set of formulas-in-context, read as their universal closures
  (a sentence is an axiom with empty context).
* `ElemEmb`, `Model`, the category `Model T` (= the paper's `Mod(T)`, arrows = elementary embeddings).
* `MoritaData L T` — the explicit definitions of a Morita extension of `T`: new product, coproduct,
  sub- and quotient sorts, new function (incl. constant) symbols and new predicate symbols, each
  with an explicit definition by a `L`-formula, plus the admissibility conditions `T ⊨ α_s`.
  `D.sig` is the extended signature `Σ⁺`, `D.incl : Σ ⟶ Σ⁺` the inclusion and `D.ext` the theory
  `T⁺ = T ∪ {δ_s}`; `D.proj : Model D.ext ⥤ Model T` is the paper's reduct functor `Π`.
* `MoritaReach` — finite chains of Morita extensions; `MoritaEquivalent` (paper §4.3);
  `CategoricallyEquivalent` (paper §5).
* `Ex1` and `Thm52` — the concrete theories of the paper's Example 1/4 and Theorem 5.2.
-/

open CategoryTheory

namespace MoritaEquiv

/-- A many-sorted signature. `Func m dom s` are the function symbols of arity
`dom 0 × … × dom (m-1) → s` (constants: `m = 0`); `Rel m dom` the predicate symbols. -/
structure Sig where
  Srt : Type
  Func : (m : ℕ) → (Fin m → Srt) → Srt → Type
  Rel : (m : ℕ) → (Fin m → Srt) → Type

/-- Terms in context `Γ` (variable `i` has sort `Γ i`), indexed by their sort. -/
inductive Term (L : Sig) {n : ℕ} (Γ : Fin n → L.Srt) : L.Srt → Type
  | var (i : Fin n) : Term L Γ (Γ i)
  | func {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : L.Func m dom s)
      (args : (j : Fin m) → Term L Γ (dom j)) : Term L Γ s

/-- Formulas in context. `all φ` universally quantifies variable `0` of `φ` (of sort `Γ' 0`). -/
inductive Formula (L : Sig) : {n : ℕ} → (Fin n → L.Srt) → Type
  | falsum {n : ℕ} {Γ : Fin n → L.Srt} : Formula L Γ
  | equal {n : ℕ} {Γ : Fin n → L.Srt} {s : L.Srt} (t₁ t₂ : Term L Γ s) : Formula L Γ
  | rel {n : ℕ} {Γ : Fin n → L.Srt} {m : ℕ} {dom : Fin m → L.Srt} (r : L.Rel m dom)
      (args : (j : Fin m) → Term L Γ (dom j)) : Formula L Γ
  | imp {n : ℕ} {Γ : Fin n → L.Srt} (φ ψ : Formula L Γ) : Formula L Γ
  | all {n : ℕ} {Γ' : Fin (n + 1) → L.Srt} (φ : Formula L Γ') : Formula L (Fin.tail Γ')

namespace Formula
variable {L : Sig} {n : ℕ} {Γ : Fin n → L.Srt}
def not (φ : Formula L Γ) : Formula L Γ := imp φ falsum
def and (φ ψ : Formula L Γ) : Formula L Γ := not (imp φ (not ψ))
def or (φ ψ : Formula L Γ) : Formula L Γ := imp (not φ) ψ
def iff (φ ψ : Formula L Γ) : Formula L Γ := and (imp φ ψ) (imp ψ φ)
/-- `∃` on variable `0`. -/
def ex {Γ' : Fin (n + 1) → L.Srt} (φ : Formula L Γ') : Formula L (Fin.tail Γ') := not (all (not φ))
end Formula

/-- Context extension: the new variable `0` has sort `s`, old variable `i` becomes `i+1`. -/
def Ctx.cons {S : Type} {n : ℕ} (s : S) (Γ : Fin n → S) : Fin (n + 1) → S := Fin.cons s Γ

/-- `∀ x : s, φ` (binds variable `0` of sort `s`). -/
def Formula.allS {L : Sig} {n : ℕ} {Γ : Fin n → L.Srt} (s : L.Srt) (φ : Formula L (Ctx.cons s Γ)) :
    Formula L Γ := Formula.all φ

/-- `∃ x : s, φ` (binds variable `0` of sort `s`). -/
def Formula.exS {L : Sig} {n : ℕ} {Γ : Fin n → L.Srt} (s : L.Srt) (φ : Formula L (Ctx.cons s Γ)) :
    Formula L Γ := Formula.ex φ

/-- Apply a unary function symbol. -/
def Term.app1 {L : Sig} {n : ℕ} {Γ : Fin n → L.Srt} {a b : L.Srt} (f : L.Func 1 ![a] b)
    (t : Term L Γ a) : Term L Γ b :=
  .func f (Fin.cons (α := fun j => Term L Γ (![a] j)) t finZeroElim)

/-- A `L`-structure. All sorts are interpreted by nonempty types. -/
structure Str (L : Sig) where
  carrier : L.Srt → Type
  funMap : ∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt},
    L.Func m dom s → ((j : Fin m) → carrier (dom j)) → carrier s
  relMap : ∀ {m : ℕ} {dom : Fin m → L.Srt}, L.Rel m dom → ((j : Fin m) → carrier (dom j)) → Prop
  nonempty : ∀ s, Nonempty (carrier s)

/-- Value of a term under an assignment `v` of the context variables. -/
def Term.realize {L : Sig} (M : Str L) {n : ℕ} {Γ : Fin n → L.Srt}
    (v : (i : Fin n) → M.carrier (Γ i)) : {s : L.Srt} → Term L Γ s → M.carrier s
  | _, .var i => v i
  | _, .func f args => M.funMap f (fun j => (args j).realize M v)

/-- Satisfaction `M ⊨ φ[v]`. -/
def Formula.Realize {L : Sig} (M : Str L) :
    {n : ℕ} → {Γ : Fin n → L.Srt} → Formula L Γ → ((i : Fin n) → M.carrier (Γ i)) → Prop
  | _, _, .falsum, _ => False
  | _, _, .equal t₁ t₂, v => t₁.realize M v = t₂.realize M v
  | _, _, .rel r args, v => M.relMap r (fun j => (args j).realize M v)
  | _, _, .imp φ ψ, v => φ.Realize M v → ψ.Realize M v
  | _, _, .all (Γ' := Γ') φ, v => ∀ a : M.carrier (Γ' 0),
      φ.Realize M (Fin.cons (α := fun i => M.carrier (Γ' i)) a v)

/-- An axiom: a formula in context, read as its universal closure. -/
structure Axiom (L : Sig) where
  {n : ℕ}
  ctx : Fin n → L.Srt
  φ : Formula L ctx

/-- A theory: a set of axioms (sentences are axioms with `n = 0`). -/
abbrev Theory (L : Sig) := Set (Axiom L)

/-- `M ⊨ A` (universal closure). -/
def Str.Satisfies {L : Sig} (M : Str L) (A : Axiom L) : Prop := ∀ v, A.φ.Realize M v

def Str.IsModel {L : Sig} (M : Str L) (T : Theory L) : Prop := ∀ A ∈ T, M.Satisfies A

/-- Elementary embeddings: sortwise maps preserving and reflecting every formula. -/
structure ElemEmb {L : Sig} (M N : Str L) where
  toFun : ∀ s, M.carrier s → N.carrier s
  map_formula : ∀ {n : ℕ} {Γ : Fin n → L.Srt} (φ : Formula L Γ) (v : (i : Fin n) → M.carrier (Γ i)),
    φ.Realize N (fun i => toFun (Γ i) (v i)) ↔ φ.Realize M v

def ElemEmb.id {L : Sig} (M : Str L) : ElemEmb M M where
  toFun _ x := x
  map_formula _ _ := Iff.rfl

def ElemEmb.comp {L : Sig} {M N P : Str L} (g : ElemEmb N P) (f : ElemEmb M N) : ElemEmb M P where
  toFun s x := g.toFun s (f.toFun s x)
  map_formula φ v := (g.map_formula φ _).trans (f.map_formula φ v)

/-- A model of `T`; `Model T` is the category `Mod(T)` (arrows: elementary embeddings). -/
structure Model {L : Sig} (T : Theory L) where
  str : Str L
  isModel : str.IsModel T

instance {L : Sig} (T : Theory L) : Category (Model T) where
  Hom M N := ElemEmb M.str N.str
  id M := ElemEmb.id M.str
  comp f g := ElemEmb.comp g f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Theories `T₁, T₂` are categorically equivalent if `Mod(T₁) ≌ Mod(T₂)`. -/
def CategoricallyEquivalent {L₁ L₂ : Sig} (T₁ : Theory L₁) (T₂ : Theory L₂) : Prop :=
  Nonempty (Model T₁ ≌ Model T₂)

/-! ### Signature morphisms, translation and reducts -/

structure Sig.Hom (L L' : Sig) where
  onSrt : L.Srt → L'.Srt
  onFunc : ∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt}, L.Func m dom s → L'.Func m (onSrt ∘ dom) (onSrt s)
  onRel : ∀ {m : ℕ} {dom : Fin m → L.Srt}, L.Rel m dom → L'.Rel m (onSrt ∘ dom)

/-- A renaming: bijective on sorts and on the symbols of each arity. -/
structure Sig.Hom.IsRenaming {L L' : Sig} (F : L.Hom L') : Prop where
  srt : Function.Bijective F.onSrt
  func : ∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt}, Function.Bijective (@Sig.Hom.onFunc L L' F m dom s)
  rel : ∀ {m : ℕ} {dom : Fin m → L.Srt}, Function.Bijective (@Sig.Hom.onRel L L' F m dom)

def Term.onTerm {L L' : Sig} (F : L.Hom L') {n : ℕ} {Γ : Fin n → L.Srt} :
    {s : L.Srt} → Term L Γ s → Term L' (F.onSrt ∘ Γ) (F.onSrt s)
  | _, .var i => .var i
  | _, .func f args => .func (F.onFunc f) (fun j => (args j).onTerm F)

def Formula.onFormula {L L' : Sig} (F : L.Hom L') :
    {n : ℕ} → {Γ : Fin n → L.Srt} → Formula L Γ → Formula L' (F.onSrt ∘ Γ)
  | _, _, .falsum => .falsum
  | _, _, .equal t₁ t₂ => .equal (t₁.onTerm F) (t₂.onTerm F)
  | _, _, .rel r args => .rel (F.onRel r) (fun j => (args j).onTerm F)
  | _, _, .imp φ ψ => .imp (φ.onFormula F) (ψ.onFormula F)
  | _, _, .all φ => .all (φ.onFormula F)

def Axiom.map {L L' : Sig} (F : L.Hom L') (A : Axiom L) : Axiom L' := ⟨F.onSrt ∘ A.ctx, A.φ.onFormula F⟩

def Theory.map {L L' : Sig} (F : L.Hom L') (T : Theory L) : Theory L' := Axiom.map F '' T

/-- The reduct `M|Σ` of an `L'`-structure along `F : L ⟶ L'`. -/
def Str.reduct {L L' : Sig} (M : Str L') (F : L.Hom L') : Str L where
  carrier s := M.carrier (F.onSrt s)
  funMap f xs := M.funMap (F.onFunc f) xs
  relMap r xs := M.relMap (F.onRel r) xs
  nonempty _ := M.nonempty _

theorem Term.realize_onTerm {L L' : Sig} (F : L.Hom L') (M : Str L') {n : ℕ} {Γ : Fin n → L.Srt}
    (v : (i : Fin n) → M.carrier (F.onSrt (Γ i))) {s : L.Srt} (t : Term L Γ s) :
    (t.onTerm F).realize M v = t.realize (M.reduct F) v := by
  induction t with
  | var i => rfl
  | func f args ih =>
    show M.funMap (F.onFunc f) _ = M.funMap (F.onFunc f) _
    exact congrArg _ (funext ih)

theorem Formula.realize_onFormula {L L' : Sig} (F : L.Hom L') (M : Str L') {n : ℕ}
    {Γ : Fin n → L.Srt} (φ : Formula L Γ) (v : (i : Fin n) → M.carrier (F.onSrt (Γ i))) :
    (φ.onFormula F).Realize M v ↔ φ.Realize (M.reduct F) v := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ =>
    exact iff_of_eq (congrArg₂ (· = ·) (Term.realize_onTerm F M v t₁) (Term.realize_onTerm F M v t₂))
  | rel r args =>
    show M.relMap (F.onRel r) _ ↔ M.relMap (F.onRel r) _
    exact iff_of_eq (congrArg _ (funext fun j => Term.realize_onTerm F M v (args j)))
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ v) (ihψ v)
  | all φ ih => exact forall_congr' fun a => ih _

/-! ### Morita extensions (paper §4.1) -/

/-- The explicit definitions making up a Morita extension of the `L`-theory `T`, together with
the admissibility conditions `T ⊨ α_s` (stated semantically: they hold in every model of `T`).
* product sorts `σ` with projections `π₁ : σ → prodFst σ`, `π₂ : σ → prodSnd σ`;
* coproduct sorts with injections `ρ₁ : coprodFst σ → σ`, `ρ₂ : coprodSnd σ → σ`;
* subsorts `σ ⊆ subBase σ` cut out by `subDef σ` (variable `0`), inclusion `i : σ → subBase σ`;
* quotient sorts `σ = quotBase σ / quotDef σ` (variables `0, 1`), projection `ε`;
* new function symbols `f : dom → s` with `f(x) = y ↔ funcDef f (y, x)` (`y` is variable `0`,
  `xⱼ` is variable `j+1`; context `Ctx.cons s dom`); constants are the case `m = 0`;
* new predicate symbols `p : dom` with `p(x) ↔ relDef p (x)`. -/
structure MoritaData (L : Sig) (T : Theory L) where
  Prod : Type
  prodFst : Prod → L.Srt
  prodSnd : Prod → L.Srt
  Coprod : Type
  coprodFst : Coprod → L.Srt
  coprodSnd : Coprod → L.Srt
  Sub : Type
  subBase : Sub → L.Srt
  subDef : (σ : Sub) → Formula L ![subBase σ]
  Quot : Type
  quotBase : Quot → L.Srt
  quotDef : (σ : Quot) → Formula L ![quotBase σ, quotBase σ]
  NewFunc : (m : ℕ) → (Fin m → L.Srt) → L.Srt → Type
  funcDef : ∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt}, NewFunc m dom s → Formula L (Ctx.cons s dom)
  NewRel : (m : ℕ) → (Fin m → L.Srt) → Type
  relDef : ∀ {m : ℕ} {dom : Fin m → L.Srt}, NewRel m dom → Formula L dom
  /-- admissibility of subsorts: `T ⊨ ∃x φ(x)` -/
  sub_adm : ∀ M : Str L, M.IsModel T → ∀ σ, ∃ a : M.carrier (subBase σ),
    (subDef σ).Realize M (Fin.cons (α := fun j => M.carrier (![subBase σ] j)) a finZeroElim)
  /-- admissibility of quotient sorts: `T ⊨ "φ is an equivalence relation"` -/
  quot_adm : ∀ M : Str L, M.IsModel T → ∀ σ, Equivalence fun a b : M.carrier (quotBase σ) =>
    (quotDef σ).Realize M (Fin.cons (α := fun j => M.carrier (![quotBase σ, quotBase σ] j)) a
      (Fin.cons (α := fun j => M.carrier (![quotBase σ, quotBase σ] j.succ)) b finZeroElim))
  /-- admissibility of function symbols: `T ⊨ ∀x ∃!y φ(x, y)` -/
  func_adm : ∀ M : Str L, M.IsModel T → ∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt}
    (f : NewFunc m dom s) (x : (j : Fin m) → M.carrier (dom j)),
    ∃! y : M.carrier s, (funcDef f).Realize M (Fin.cons (α := fun j => M.carrier (Ctx.cons s dom j)) y x)

namespace MoritaData
variable {L : Sig} {T : Theory L} (D : MoritaData L T)

/-- Sorts of `Σ⁺`. -/
inductive ExtSrt
  | old (s : L.Srt)
  | prod (σ : D.Prod)
  | coprod (σ : D.Coprod)
  | sub (σ : D.Sub)
  | quot (σ : D.Quot)

/-- Function symbols of `Σ⁺`. -/
inductive ExtFunc : (m : ℕ) → (Fin m → D.ExtSrt) → D.ExtSrt → Type
  | old {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : L.Func m dom s) :
      ExtFunc m (ExtSrt.old ∘ dom) (.old s)
  | new {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : D.NewFunc m dom s) :
      ExtFunc m (ExtSrt.old ∘ dom) (.old s)
  | fst (σ : D.Prod) : ExtFunc 1 ![.prod σ] (.old (D.prodFst σ))
  | snd (σ : D.Prod) : ExtFunc 1 ![.prod σ] (.old (D.prodSnd σ))
  | inl (σ : D.Coprod) : ExtFunc 1 ![.old (D.coprodFst σ)] (.coprod σ)
  | inr (σ : D.Coprod) : ExtFunc 1 ![.old (D.coprodSnd σ)] (.coprod σ)
  | incl (σ : D.Sub) : ExtFunc 1 ![.sub σ] (.old (D.subBase σ))
  | proj (σ : D.Quot) : ExtFunc 1 ![.old (D.quotBase σ)] (.quot σ)

/-- Predicate symbols of `Σ⁺`. -/
inductive ExtRel : (m : ℕ) → (Fin m → D.ExtSrt) → Type
  | old {m : ℕ} {dom : Fin m → L.Srt} (r : L.Rel m dom) : ExtRel m (ExtSrt.old ∘ dom)
  | new {m : ℕ} {dom : Fin m → L.Srt} (r : D.NewRel m dom) : ExtRel m (ExtSrt.old ∘ dom)

/-- The extended signature `Σ⁺`. -/
def sig : Sig := ⟨D.ExtSrt, D.ExtFunc, D.ExtRel⟩

/-- The inclusion `Σ ⊂ Σ⁺`. -/
def incl : L.Hom D.sig := ⟨ExtSrt.old, ExtFunc.old, ExtRel.old⟩

open Formula Term

/-- `δ_σ` for a product sort: `∀x ∀y ∃z (π₁ z = x ∧ π₂ z = y ∧ ∀z' (π₁ z' = x ∧ π₂ z' = y → z' = z))`.
Context `(x, y)`. -/
def prodAx (σ : D.Prod) : Axiom D.sig :=
  ⟨(![ExtSrt.old (D.prodFst σ), ExtSrt.old (D.prodSnd σ)] : Fin 2 → D.sig.Srt),
    exS (ExtSrt.prod σ)
      (Formula.and
        (Formula.and (equal (app1 (L := D.sig) (ExtFunc.fst σ) (var 0)) (var 1))
          (equal (app1 (L := D.sig) (ExtFunc.snd σ) (var 0)) (var 2)))
        (allS (ExtSrt.prod σ)
          (imp
            (Formula.and (equal (app1 (L := D.sig) (ExtFunc.fst σ) (var 0)) (var 2))
              (equal (app1 (L := D.sig) (ExtFunc.snd σ) (var 0)) (var 3)))
            (equal (var 0) (var 1)))))⟩

/-- `δ_σ` for a coproduct sort:
`∀z ((∃!x ρ₁ x = z) ∨ (∃!y ρ₂ y = z)) ∧ ∀x ∀y ¬(ρ₁ x = ρ₂ y)`. Context `(z)`. -/
def coprodAx (σ : D.Coprod) : Axiom D.sig :=
  ⟨(![ExtSrt.coprod σ] : Fin 1 → D.sig.Srt),
    Formula.and
      (Formula.or
        (exS (ExtSrt.old (D.coprodFst σ))
          (Formula.and (equal (app1 (L := D.sig) (ExtFunc.inl σ) (var 0)) (var 1))
            (allS (ExtSrt.old (D.coprodFst σ))
              (imp (equal (app1 (L := D.sig) (ExtFunc.inl σ) (var 0)) (var 2))
                (equal (var 0) (var 1))))))
        (exS (ExtSrt.old (D.coprodSnd σ))
          (Formula.and (equal (app1 (L := D.sig) (ExtFunc.inr σ) (var 0)) (var 1))
            (allS (ExtSrt.old (D.coprodSnd σ))
              (imp (equal (app1 (L := D.sig) (ExtFunc.inr σ) (var 0)) (var 2))
                (equal (var 0) (var 1)))))))
      (allS (ExtSrt.old (D.coprodFst σ))
        (allS (ExtSrt.old (D.coprodSnd σ))
          (Formula.not (equal (app1 (L := D.sig) (ExtFunc.inl σ) (var 1))
            (app1 (L := D.sig) (ExtFunc.inr σ) (var 0))))))⟩

/-- `δ_σ` for a subsort: `∀x (φ(x) ↔ ∃z i(z) = x) ∧ ∀z₁ ∀z₂ (i z₁ = i z₂ → z₁ = z₂)`.
Context `(x)`. -/
def subAx (σ : D.Sub) : Axiom D.sig :=
  ⟨(D.incl.onSrt ∘ ![D.subBase σ] : Fin 1 → D.sig.Srt),
    Formula.and
      (Formula.iff ((D.subDef σ).onFormula D.incl)
        (exS (ExtSrt.sub σ) (equal (app1 (L := D.sig) (ExtFunc.incl σ) (var 0)) (var 1))))
      (allS (ExtSrt.sub σ) (allS (ExtSrt.sub σ)
        (imp (equal (app1 (L := D.sig) (ExtFunc.incl σ) (var 0))
              (app1 (L := D.sig) (ExtFunc.incl σ) (var 1)))
          (equal (var 0) (var 1)))))⟩

/-- `δ_σ` for a quotient sort: `∀x₁ ∀x₂ (ε x₁ = ε x₂ ↔ φ(x₁, x₂)) ∧ ∀z ∃x ε(x) = z`.
Context `(x₁, x₂)`. -/
def quotAx (σ : D.Quot) : Axiom D.sig :=
  ⟨(D.incl.onSrt ∘ ![D.quotBase σ, D.quotBase σ] : Fin 2 → D.sig.Srt),
    Formula.and
      (Formula.iff (equal (app1 (L := D.sig) (ExtFunc.proj σ) (var 0))
          (app1 (L := D.sig) (ExtFunc.proj σ) (var 1)))
        ((D.quotDef σ).onFormula D.incl))
      (allS (ExtSrt.quot σ) (exS (ExtSrt.old (D.quotBase σ))
        (equal (app1 (L := D.sig) (ExtFunc.proj σ) (var 0)) (var 1))))⟩

/-- `δ_f`: `∀x ∀y (f(x) = y ↔ φ(y, x))`. Context `(y, x₀, …, x_{m-1})`. -/
def funcAx {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : D.NewFunc m dom s) : Axiom D.sig :=
  ⟨(D.incl.onSrt ∘ Ctx.cons s dom : Fin (m + 1) → D.sig.Srt),
    Formula.iff (equal (Term.func (L := D.sig) (ExtFunc.new f) (fun j => var j.succ)) (var 0))
        ((D.funcDef f).onFormula D.incl)⟩

/-- `δ_p`: `∀x (p(x) ↔ φ(x))`. Context `(x₀, …, x_{m-1})`. -/
def relAx {m : ℕ} {dom : Fin m → L.Srt} (r : D.NewRel m dom) : Axiom D.sig :=
  ⟨(D.incl.onSrt ∘ dom : Fin m → D.sig.Srt),
    Formula.iff (Formula.rel (L := D.sig) (ExtRel.new r) (fun j => var j)) ((D.relDef r).onFormula D.incl)⟩

/-- The explicit definitions `{δ_s : s ∈ Σ⁺ − Σ}`. -/
def defs : Theory D.sig :=
  Set.range D.prodAx ∪ Set.range D.coprodAx ∪ Set.range D.subAx ∪ Set.range D.quotAx ∪
    {A | ∃ (m : ℕ) (dom : Fin m → L.Srt) (s : L.Srt) (f : D.NewFunc m dom s), A = D.funcAx f} ∪
    {A | ∃ (m : ℕ) (dom : Fin m → L.Srt) (r : D.NewRel m dom), A = D.relAx r}

/-- The Morita extension `T⁺ = T ∪ {δ_s : s ∈ Σ⁺ − Σ}`. -/
def ext : Theory D.sig := T.map D.incl ∪ D.defs

theorem reduct_isModel (M : Model D.ext) : (M.str.reduct D.incl).IsModel T := by
  intro A hA v
  exact (Formula.realize_onFormula D.incl M.str A.φ v).1 (M.isModel _ (Or.inl ⟨A, hA, rfl⟩) v)

/-- The reduct functor `Π : Mod(T⁺) ⥤ Mod(T)`, `M ↦ M|Σ`, `h ↦ h|Σ`. -/
def proj : Model D.ext ⥤ Model T where
  obj M := ⟨M.str.reduct D.incl, D.reduct_isModel M⟩
  map {M N} h :=
    { toFun := fun s => h.toFun (D.incl.onSrt s)
      map_formula := fun φ v =>
        (Formula.realize_onFormula D.incl N.str φ _).symm.trans
          ((h.map_formula (φ.onFormula D.incl) v).trans (Formula.realize_onFormula D.incl M.str φ v)) }
  map_id _ := rfl
  map_comp _ _ := rfl

end MoritaData

/-! ### Morita equivalence (paper §4.3) -/

/-- `MoritaReach T T'`: `T'` is reached from `T` by a finite chain of Morita extensions. -/
inductive MoritaReach : {L₁ : Sig} → Theory L₁ → {L₂ : Sig} → Theory L₂ → Prop
  | refl {L : Sig} (T : Theory L) : MoritaReach T T
  | step {L : Sig} {T : Theory L} (D : MoritaData L T) {L' : Sig} {T' : Theory L'} :
      MoritaReach D.ext T' → MoritaReach T T'

/-- `T₁` and `T₂` are Morita equivalent: chains of Morita extensions `T₁ ⇝ T₁'`, `T₂ ⇝ T₂'`
ending in logically equivalent theories over a common signature (here: over signatures
identified by a renaming `F`, i.e. an `L₂'`-structure is a model of `T₂'` iff its `F`-reduct is a
model of `T₁'`). -/
def MoritaEquivalent {L₁ L₂ : Sig} (T₁ : Theory L₁) (T₂ : Theory L₂) : Prop :=
  ∃ (L₁' L₂' : Sig) (T₁' : Theory L₁') (T₂' : Theory L₂') (F : L₁'.Hom L₂'),
    MoritaReach T₁ T₁' ∧ MoritaReach T₂ T₂' ∧ F.IsRenaming ∧
      ∀ M : Str L₂', M.IsModel T₂' ↔ (M.reduct F).IsModel T₁'

/-! ### Concrete theories from the paper -/

/-- Single-sorted contexts. -/
abbrev uctx (n : ℕ) : Fin n → Unit := fun _ => ()

namespace Ex1
/-- `Σ₁ = {σ₁, p, q}`: one sort, two unary predicates. -/
inductive Rel1 : (m : ℕ) → (Fin m → Unit) → Type
  | p : Rel1 1 (uctx 1)
  | q : Rel1 1 (uctx 1)

def sig1 : Sig := ⟨Unit, fun _ _ _ => Empty, Rel1⟩
/-- `Σ₂ = {σ₂, σ₃}`: two sorts, no symbols. -/
def sig2 : Sig := ⟨Bool, fun _ _ _ => Empty, fun _ _ => Empty⟩

/-- `p(x)` in the one-variable context. -/
def pAt : Formula sig1 (uctx 1) := Formula.rel (L := sig1) Rel1.p fun _ => Term.var 0
/-- `q(x)` in the one-variable context. -/
def qAt : Formula sig1 (uctx 1) := Formula.rel (L := sig1) Rel1.q fun _ => Term.var 0

/-- `T₁ = {∃x p(x), ∃x q(x), ∀x (p(x) ∨ q(x)), ∀x ¬(p(x) ∧ q(x))}`. -/
def T1 : Theory sig1 :=
  {⟨uctx 0, Formula.exS (L := sig1) (Γ := uctx 0) () pAt⟩,
   ⟨uctx 0, Formula.exS (L := sig1) (Γ := uctx 0) () qAt⟩,
   ⟨uctx 1, Formula.or pAt qAt⟩,
   ⟨uctx 1, Formula.not (Formula.and pAt qAt)⟩}

/-- `T₂ = ∅`. -/
def T2 : Theory sig2 := ∅
end Ex1

namespace Thm52
/-- One sort and countably many unary predicates `p₀, p₁, …`. -/
inductive PRel : (m : ℕ) → (Fin m → Unit) → Type
  | p (i : ℕ) : PRel 1 (uctx 1)

def sig : Sig := ⟨Unit, fun _ _ _ => Empty, PRel⟩

/-- `∃=1 x (x = x)`, i.e. `∃x ∀y (y = x)`. -/
def exactlyOne : Axiom sig :=
  ⟨uctx 0, Formula.exS (L := sig) (Γ := uctx 0) ()
    (Formula.allS (L := sig) (Γ := uctx 1) () (Formula.equal (Term.var 0) (Term.var 1)))⟩

/-- `pᵢ(y)` in the one-variable context. -/
def pAt (i : ℕ) : Formula sig (uctx 1) := Formula.rel (L := sig) (PRel.p i) fun _ => Term.var 0

/-- `T₁ = {∃=1 x (x = x)}` over `Σ₁ = {σ₁, p₀, p₁, …}`. -/
def T1 : Theory sig := {exactlyOne}

/-- `T₂ = {∃=1 y (y = y)} ∪ {∀y (q₀(y) → qᵢ(y)) : i ∈ ℕ}` over `Σ₂ = {σ₂, q₀, q₁, …}`. -/
def T2 : Theory sig :=
  {exactlyOne} ∪ Set.range fun i : ℕ => (⟨uctx 1, Formula.imp (pAt 0) (pAt i)⟩ : Axiom sig)
end Thm52


end MoritaEquiv


