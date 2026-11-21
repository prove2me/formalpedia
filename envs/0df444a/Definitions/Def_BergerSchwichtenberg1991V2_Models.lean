-- Prove2me | Definitions.Def_BergerSchwichtenberg1991V2_Models
-- name    : BergerSchwichtenberg1991V2_Models
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-20T20:13:45.638174+00:00
-- url     : https://prove2.me/theorems/ec03d098-6412-4920-a459-4234a0b7b1ba
-- title:
--   Extensional lambda-models and the inversion functionals
-- statement:
--   An extensional lambda-model supplies carriers, application, a default environment and evaluation of well-typed terms respecting the lambda equations. Admissible models also carry operations on codes of syntax and indices. The quotation and reflection functionals are interpreted lambda expressions defined recursively on types. A pr-model represents primitive-recursive functions via its ground-type numeral embedding.
-- source:
--   Ulrich Berger and Helmut Schwichtenberg (1991), An inverse of the evaluation functional for typed lambda-calculus, LICS, pp. 203–211, Sections 1, 3 and 4, pp. 204–208. https://epub.ub.uni-muenchen.de/4261/1/4261.pdf

import Definitions.Def_BergerSchwichtenberg1991V2_Syntax

/-!
# Models and inversion for the simply typed λ-calculus

The model, coding laws, and interpretation of the inversion functionals follow
Berger and Schwichtenberg, *An inverse of the evaluation functional for typed λ-calculus*,
LICS 1991, pp. 204–208. Evaluations take typed terms, and each model supplies a total
environment. The combinators are expressed with object-language variables assigned
their values by that environment. Their interpretation uses the model's λ-evaluation.
-/

namespace BergerSchwichtenberg1991V2

universe u

/-- An extensional model of the simply typed λ-calculus of Section 1.
A chosen total environment supplies values for variables of every type. -/
structure LambdaModel where
  Dom : Ty → Type u
  appM : {ρ σ : Ty} → Dom (.arr ρ σ) → Dom ρ → Dom σ
  eqM : (ρ : Ty) → Dom ρ → Dom ρ → Prop
  eqM_refl : ∀ (ρ : Ty) (a : Dom ρ), eqM ρ a a
  eqM_symm : ∀ (ρ : Ty) {a b : Dom ρ}, eqM ρ a b → eqM ρ b a
  eqM_trans : ∀ (ρ : Ty) {a b c : Dom ρ}, eqM ρ a b → eqM ρ b c → eqM ρ a c
  appM_congr : ∀ {ρ σ : Ty} {f f' : Dom (.arr ρ σ)} {a a' : Dom ρ},
    eqM (.arr ρ σ) f f' → eqM ρ a a' → eqM σ (appM f a) (appM f' a')
  extensional : ∀ {ρ σ : Ty} {f f' : Dom (.arr ρ σ)},
    (∀ b : Dom ρ, eqM σ (appM f b) (appM f' b)) → eqM (.arr ρ σ) f f'
  defaultEnv : ∀ x : Var, Dom x.ty
  eval : {r : Term} → {ρ : Ty} → HasType r ρ → (∀ x : Var, Dom x.ty) → Dom ρ
  eval_var : ∀ (x : Var) (η : ∀ y : Var, Dom y.ty),
    eqM x.ty (eval (.var x) η) (η x)
  eval_app : ∀ {t r : Term} {ρ σ : Ty} (ht : HasType t (.arr ρ σ)) (hr : HasType r ρ)
    (η : ∀ y : Var, Dom y.ty),
    eqM σ (eval (.app ht hr) η) (appM (eval ht η) (eval hr η))
  eval_lam : ∀ (x : Var) {s : Term} {σ : Ty} (hs : HasType s σ) (η : ∀ y : Var, Dom y.ty)
    (a : Dom x.ty),
    eqM σ (appM (eval (.lam x hs) η) a)
      (eval hs (fun y => if h : y = x then h ▸ a else η y))

namespace LambdaModel

/-- A type-respecting assignment to all variables. -/
abbrev Env (M : LambdaModel.{u}) := ∀ x : Var, M.Dom x.ty

/-- Replace the value assigned to one variable. -/
def updateEnv (M : LambdaModel.{u}) (η : M.Env) (x : Var) (a : M.Dom x.ty) : M.Env :=
  fun y => if h : y = x then h ▸ a else η y

@[simp]
theorem updateEnv_self (M : LambdaModel.{u}) (η : M.Env) (x : Var) (a : M.Dom x.ty) :
    M.updateEnv η x a x = a := by
  simp [updateEnv]

theorem updateEnv_of_ne (M : LambdaModel.{u}) (η : M.Env) {x y : Var} (a : M.Dom x.ty)
    (h : y ≠ x) : M.updateEnv η x a y = η y := by
  simp [updateEnv, h]

/-- Evaluation depends only on the values of variables occurring free. -/
theorem eval_congr_env (M : LambdaModel.{u}) {r : Term} {ρ : Ty} (ht : HasType r ρ)
    (η₁ η₂ : M.Env) (h : ∀ x ∈ freeVarOccurrences r, M.eqM x.ty (η₁ x) (η₂ x)) :
    M.eqM ρ (M.eval ht η₁) (M.eval ht η₂) := by
  induction ht generalizing η₁ η₂ with
  | var x =>
      exact M.eqM_trans _ (M.eval_var x η₁)
        (M.eqM_trans _ (h x (by simp [freeVarOccurrences])) (M.eqM_symm _ (M.eval_var x η₂)))
  | @app t r ρ σ ht hr iht ihr =>
      have ht' := iht η₁ η₂ (fun x hx => h x (List.mem_append_left _ hx))
      have hr' := ihr η₁ η₂ (fun x hx => h x (List.mem_append_right _ hx))
      exact M.eqM_trans _ (M.eval_app ht hr η₁)
        (M.eqM_trans _ (M.appM_congr ht' hr') (M.eqM_symm _ (M.eval_app ht hr η₂)))
  | @lam x s σ hs ih =>
      apply M.extensional
      intro a
      refine M.eqM_trans _ (M.eval_lam x hs η₁ a)
        (M.eqM_trans _ (ih (M.updateEnv η₁ x a) (M.updateEnv η₂ x a) ?_)
          (M.eqM_symm _ (M.eval_lam x hs η₂ a)))
      intro y hy
      by_cases hxy : y = x
      · subst y
        simpa using M.eqM_refl x.ty a
      · rw [M.updateEnv_of_ne η₁ a hxy, M.updateEnv_of_ne η₂ a hxy]
        apply h y
        rw [freeVarOccurrences, List.mem_filter]
        exact ⟨hy, by simpa using hxy⟩

/-- Semantic equality of two terms of the same type in one environment. -/
def ModelsEqAt (M : LambdaModel.{u}) {r s : Term} {ρ : Ty} (hr : HasType r ρ) (hs : HasType s ρ)
    (η : M.Env) : Prop :=
  M.eqM ρ (M.eval hr η) (M.eval hs η)

/-- Semantic equality in every environment. -/
def ModelsEq (M : LambdaModel.{u}) {r s : Term} {ρ : Ty} (hr : HasType r ρ) (hs : HasType s ρ) :
    Prop :=
  ∀ η : M.Env, M.ModelsEqAt hr hs η

/-- A definable element is the denotation of a closed term. The choice of environment for a
closed term is the one supplied with the model. -/
def IsLambdaDefinable (M : LambdaModel.{u}) (ρ : Ty) (a : M.Dom ρ) : Prop :=
  ∃ (r : Term) (hr : HasType r ρ), IsClosed r ∧ M.eqM ρ (M.eval hr M.defaultEnv) a

/-- The denotation of a closed term is independent of the environment. -/
theorem eval_closed (M : LambdaModel.{u}) {r : Term} {ρ : Ty} (ht : HasType r ρ)
    (hc : IsClosed r) (η₁ η₂ : M.Env) :
    M.eqM ρ (M.eval ht η₁) (M.eval ht η₂) := by
  apply M.eval_congr_env ht
  intro v hv
  have h : v ∈ freeVars r := List.mem_eraseDups.2 hv
  rw [hc] at h
  contradiction

end LambdaModel

/-- Section 3 (p. 205): An admissible λ-model `M` is a λ-model equipped with types `f` (term
families) and `ι` (indices), coding functions `⌈·⌉^o : Λ → M^o` and `⌈·⌉^ι : {0,1}* → M^ι`,
and objects `append`, `mvar_ρ`, `app`, `abst_ρ`, `emb`, `fun`, `extract` satisfying the
admissibility axioms `(append)`, `(mvar)`, `(app)`, `(abst)`, `(⌈·⌉)`, `(emb)`, `(fun)`,
and `(extract)`. -/
structure AdmissibleModel extends LambdaModel.{u} where
  tyF : Ty
  tyIdx : Ty
  codeTerm : Term → Dom .base
  codeIdx : Index → Dom tyIdx
  append : Dom (.arr tyIdx (.arr tyIdx tyIdx))
  mvar : (ρ : Ty) → Dom (.arr tyIdx .base)
  appCode : Dom (.arr .base (.arr .base .base))
  abst : (ρ : Ty) → Dom (.arr tyIdx (.arr .base .base))
  emb : Dom (.arr .base tyF)
  funOp : Dom (.arr tyF (.arr tyIdx .base))
  extract : Dom (.arr (.arr tyIdx .base) .base)
  /-- `(append)`: `append ⌈k⌉ ⌈l⌉ =_ι ⌈k * l⌉` -/
  law_append : ∀ k l : Index,
      eqM tyIdx (appM (appM append (codeIdx k)) (codeIdx l)) (codeIdx (appendIdx k l))
  /-- `(mvar)`: `mvar_ρ ⌈k⌉ =_o ⌈x_k^ρ⌉` -/
  law_mvar : ∀ (ρ : Ty) (k : Index),
      eqM .base (appM (mvar ρ) (codeIdx k)) (codeTerm (.var (indexedVar ρ k)))
  /-- `(app)`: `app ⌈r⌉ ⌈s⌉ =_o ⌈r s⌉` -/
  law_app : ∀ r s : Term,
      eqM .base (appM (appM appCode (codeTerm r)) (codeTerm s)) (codeTerm (.app r s))
  /-- `(abst)`: `abst_ρ ⌈k⌉ ⌈r⌉ =_o ⌈λx_k^ρ. r⌉` -/
  law_abst : ∀ (ρ : Ty) (k : Index) (r : Term),
      eqM .base (appM (appM (abst ρ) (codeIdx k)) (codeTerm r))
        (codeTerm (.lam (indexedVar ρ k) r))
  /-- `(⌈·⌉)`: `⌈r⌉ =_o ⌈s⌉ ⇒ EMB r = EMB s` -/
  law_code_inj : ∀ r s : Term,
      eqM .base (codeTerm r) (codeTerm s) → EMB r = EMB s
  /-- `(emb)`: `EMB r = EMB s ⇒ emb ⌈r⌉ =_f emb ⌈s⌉` -/
  law_emb_congr : ∀ r s : Term,
      EMB r = EMB s → eqM tyF (appM emb (codeTerm r)) (appM emb (codeTerm s))
  /-- `(fun)`: `fun (emb ⌈r⌉) ⌈k⌉ =_o ⌈EMB r k⌉` -/
  law_fun : ∀ (r : Term) (k : Index),
      eqM .base (appM (appM funOp (appM emb (codeTerm r))) (codeIdx k))
        (codeTerm (EMB r k))
  /-- `(extract)`: `(∀ k, a ⌈k⌉ =_o ⌈EMB r k⌉) ⇒ extract(a) =_o ⌈EXTRACT(EMB r)⌉` -/
  law_extract : ∀ (a : Dom (.arr tyIdx .base)) (r : Term),
      (∀ k : Index, eqM .base (appM a (codeIdx k)) (codeTerm (EMB r k))) →
      eqM .base (appM extract a) (codeTerm (EXTRACT (EMB r)))

private def modelVar (n : Nat) (ρ : Ty) : Var :=
  ⟨.named n, ρ⟩

/-- A typed expression assembled from object-language variables, applications, and binders. -/
private structure Expr (ρ : Ty) where
  term : Term
  typed : HasType term ρ

private def Expr.ref (n : Nat) (ρ : Ty) : Expr ρ :=
  ⟨.var (modelVar n ρ), .var (modelVar n ρ)⟩

private def Expr.app {ρ σ : Ty} (f : Expr (.arr ρ σ)) (a : Expr ρ) : Expr σ :=
  ⟨.app f.term a.term, .app f.typed a.typed⟩

private def Expr.lam (n : Nat) (ρ : Ty) {σ : Ty} (r : Expr σ) : Expr (.arr ρ σ) :=
  ⟨.lam (modelVar n ρ) r.term, .lam (modelVar n ρ) r.typed⟩

private def Expr.denote {ρ : Ty} (r : Expr ρ) (M : LambdaModel.{u}) (η : M.Env) : M.Dom ρ :=
  M.eval r.typed η

private def LambdaModel.withValue (M : LambdaModel.{u}) (η : M.Env) (n : Nat)
    {ρ : Ty} (a : M.Dom ρ) : M.Env :=
  M.updateEnv η (modelVar n ρ) a

@[simp]
private theorem LambdaModel.withValue_same (M : LambdaModel.{u}) (η : M.Env) (n : Nat)
    {ρ : Ty} (a : M.Dom ρ) : M.withValue η n a (modelVar n ρ) = a :=
  M.updateEnv_self η (modelVar n ρ) a

@[simp]
private theorem LambdaModel.withValue_other (M : LambdaModel.{u}) (η : M.Env) {i j : Nat}
    {ρ σ : Ty} (a : M.Dom ρ) (h : j ≠ i) :
    M.withValue η i a (modelVar j σ) = η (modelVar j σ) :=
  M.updateEnv_of_ne η (x := modelVar i ρ) (y := modelVar j σ) a
    (fun e => h (VarName.named.inj (congrArg Var.name e)))

private theorem Expr.denote_ref (M : LambdaModel.{u}) (η : M.Env) {n : Nat} {ρ : Ty}
    {a : M.Dom ρ} (h : η (modelVar n ρ) = a) :
    M.eqM ρ ((Expr.ref n ρ).denote M η) a :=
  h ▸ M.eval_var (modelVar n ρ) η

private theorem Expr.denote_app (M : LambdaModel.{u}) (η : M.Env)
    {ρ σ : Ty} {f : Expr (.arr ρ σ)} {x : Expr ρ}
    {g : M.Dom (.arr ρ σ)} {a : M.Dom ρ}
    (hf : M.eqM (.arr ρ σ) (f.denote M η) g) (hx : M.eqM ρ (x.denote M η) a) :
    M.eqM σ ((f.app x).denote M η) (M.appM g a) :=
  M.eqM_trans _ (M.eval_app f.typed x.typed η) (M.appM_congr hf hx)

private theorem Expr.apply_denote_lam (M : LambdaModel.{u}) (η : M.Env)
    {n : Nat} {ρ σ : Ty} {r : Expr σ} (a : M.Dom ρ) {b : M.Dom σ}
    (h : M.eqM σ (r.denote M (M.withValue η n a)) b) :
    M.eqM σ (M.appM ((Expr.lam n ρ r).denote M η) a) b :=
  M.eqM_trans _ (M.eval_lam (modelVar n ρ) r.typed η a) h

private theorem Expr.apply₂_denote_lam (M : LambdaModel.{u}) (η : M.Env)
    {n m : Nat} {ρ σ τ : Ty} {r : Expr τ} (a : M.Dom ρ) (b : M.Dom σ) {c : M.Dom τ}
    (h : M.eqM τ (r.denote M (M.withValue (M.withValue η n a) m b)) c) :
    M.eqM τ (M.appM (M.appM ((Expr.lam n ρ (Expr.lam m σ r)).denote M η) a) b) c :=
  M.eqM_trans _
    (M.appM_congr (M.eval_lam (modelVar n ρ) (Expr.lam m σ r).typed η a) (M.eqM_refl _ b))
    (Expr.apply_denote_lam M _ b h)

/-- Interpret the λ-term λ x. f (g x) with model elements assigned to its free variables. -/
def LambdaModel.compose (M : LambdaModel.{u}) {ρ σ τ : Ty}
    (f : M.Dom (.arr σ τ)) (g : M.Dom (.arr ρ σ)) : M.Dom (.arr ρ τ) :=
  let η := M.withValue (M.withValue M.defaultEnv 0 f) 1 g
  let body := (Expr.ref 0 (.arr σ τ)).app ((Expr.ref 1 (.arr ρ σ)).app (Expr.ref 2 ρ))
  (Expr.lam 2 ρ body).denote M η

theorem LambdaModel.compose_spec (M : LambdaModel.{u}) {ρ σ τ : Ty}
    (f : M.Dom (.arr σ τ)) (g : M.Dom (.arr ρ σ)) (x : M.Dom ρ) :
    M.eqM τ (M.appM (M.compose f g) x) (M.appM f (M.appM g x)) := by
  unfold compose
  apply Expr.apply_denote_lam
  apply Expr.denote_app
  · exact Expr.denote_ref M _ (by simp <;> rfl)
  · apply Expr.denote_app
    · exact Expr.denote_ref M _ (by simp <;> rfl)
    · exact Expr.denote_ref M _ (by simp <;> rfl)

/-- Interpret the λ-term λ x. f x y with its last argument fixed. -/
def LambdaModel.bindSecond (M : LambdaModel.{u}) {ρ σ τ : Ty}
    (f : M.Dom (.arr ρ (.arr σ τ))) (y : M.Dom σ) : M.Dom (.arr ρ τ) :=
  let η := M.withValue (M.withValue M.defaultEnv 0 f) 1 y
  let body := (Expr.ref 0 (.arr ρ (.arr σ τ))).app (Expr.ref 2 ρ) |>.app (Expr.ref 1 σ)
  (Expr.lam 2 ρ body).denote M η

theorem LambdaModel.bindSecond_spec (M : LambdaModel.{u}) {ρ σ τ : Ty}
    (f : M.Dom (.arr ρ (.arr σ τ))) (y : M.Dom σ) (x : M.Dom ρ) :
    M.eqM τ (M.appM (M.bindSecond f y) x) (M.appM (M.appM f x) y) := by
  unfold bindSecond
  apply Expr.apply_denote_lam
  repeat' first | exact Expr.denote_ref M _ (by simp <;> rfl) | apply Expr.denote_app

/-- Interpret λ a. a (index (a e) (a z)) in a model. For Lemma 3, e and z are the codes
of the empty index and the single zero bit. -/
def LambdaModel.extractFromIndex (M : LambdaModel.{u})
    (index : M.Dom (.arr .base (.arr .base .base))) (e z : M.Dom .base) :
    M.Dom (.arr (.arr .base .base) .base) :=
  let η := M.defaultEnv
  let η := M.withValue η 0 index
  let η := M.withValue η 1 e
  let η := M.withValue η 2 z
  let a := Expr.ref 3 (.arr .base .base)
  let ie := (Expr.ref 0 (.arr .base (.arr .base .base))).app (a.app (Expr.ref 1 .base))
  let iez := ie.app (a.app (Expr.ref 2 .base))
  (Expr.lam 3 (.arr .base .base) (a.app iez)).denote M η

theorem LambdaModel.extractFromIndex_spec (M : LambdaModel.{u})
    (index : M.Dom (.arr .base (.arr .base .base))) (e z : M.Dom .base)
    (a : M.Dom (.arr .base .base)) :
    M.eqM .base (M.appM (M.extractFromIndex index e z) a)
      (M.appM a (M.appM (M.appM index (M.appM a e)) (M.appM a z))) := by
  unfold extractFromIndex
  apply Expr.apply_denote_lam
  repeat' first | exact Expr.denote_ref M _ (by simp <;> rfl) | apply Expr.denote_app

namespace AdmissibleModel

variable (M : AdmissibleModel.{u})

/-- Extract a term code from a represented family. -/
def f_extract (f : M.Dom M.tyF) : M.Dom .base :=
  M.appM M.extract (M.appM M.funOp f)

/-- Apply one represented term family to another. -/
def f_app (f g : M.Dom M.tyF) : M.Dom M.tyF :=
  M.appM M.emb (M.appM (M.appM M.appCode (M.f_extract f)) (M.f_extract g))

/-- Represent a family given as a function from indices to term codes. -/
def fam (a : M.Dom (.arr M.tyIdx .base)) : M.Dom M.tyF :=
  M.appM M.emb (M.appM M.extract a)

private def extractFamilyFn : M.Dom (.arr M.tyF .base) :=
  M.toLambdaModel.compose M.extract M.funOp

private def famFn : M.Dom (.arr (.arr M.tyIdx .base) M.tyF) :=
  M.toLambdaModel.compose M.emb M.extract

private theorem extractFamilyFn_spec (f : M.Dom M.tyF) :
    M.eqM .base (M.appM M.extractFamilyFn f) (M.f_extract f) :=
  M.toLambdaModel.compose_spec M.extract M.funOp f

private theorem famFn_spec (a : M.Dom (.arr M.tyIdx .base)) :
    M.eqM M.tyF (M.appM M.famFn a) (M.fam a) :=
  M.toLambdaModel.compose_spec M.emb M.extract a

private def applyFamilyFn : M.Dom (.arr M.tyF (.arr M.tyF M.tyF)) :=
  let L := M.toLambdaModel
  let f := M.tyF
  let η := L.defaultEnv
  let η := L.withValue η 0 M.emb
  let η := L.withValue η 1 M.appCode
  let η := L.withValue η 2 M.extractFamilyFn
  let extract := Expr.ref 2 (.arr f .base)
  let codeApp := (Expr.ref 1 (.arr .base (.arr .base .base))).app
    (extract.app (Expr.ref 3 f)) |>.app (extract.app (Expr.ref 4 f))
  let body := (Expr.ref 0 (.arr .base f)).app codeApp
  (Expr.lam 3 f (Expr.lam 4 f body)).denote L η

private theorem applyFamilyFn_spec (x y : M.Dom M.tyF) :
    M.eqM M.tyF (M.appM (M.appM M.applyFamilyFn x) y) (M.f_app x y) := by
  unfold applyFamilyFn f_app
  apply Expr.apply₂_denote_lam
  apply Expr.denote_app
  · exact Expr.denote_ref M.toLambdaModel _ (by simp <;> rfl)
  · apply Expr.denote_app
    · apply Expr.denote_app
      · exact Expr.denote_ref M.toLambdaModel _ (by simp <;> rfl)
      · refine M.eqM_trans _ ?_ (M.extractFamilyFn_spec x)
        apply Expr.denote_app
        · exact Expr.denote_ref M.toLambdaModel _ (by simp <;> rfl)
        · exact Expr.denote_ref M.toLambdaModel _ (by simp <;> rfl)
    · refine M.eqM_trans _ ?_ (M.extractFamilyFn_spec y)
      apply Expr.denote_app
      · exact Expr.denote_ref M.toLambdaModel _ (by simp <;> rfl)
      · exact Expr.denote_ref M.toLambdaModel _ (by simp <;> rfl)

private def phiEnv (ρ σ : Ty) (psi : M.Dom (.arr M.tyF ρ))
    (phi : M.Dom (.arr σ M.tyF)) : M.Env :=
  let L := M.toLambdaModel
  let η := L.defaultEnv
  let η := L.withValue η 0 M.famFn
  let η := L.withValue η 1 (M.abst ρ)
  let η := L.withValue η 2 M.funOp
  let η := L.withValue η 3 phi
  let η := L.withValue η 4 psi
  let η := L.withValue η 5 M.emb
  let η := L.withValue η 6 (M.mvar ρ)
  let η := L.withValue η 7 M.append
  L.withValue η 8 (M.codeIdx zeroIdx)

private def phiIndexedExpr (f ι ρ σ : Ty) : Expr (.arr ι .base) :=
  let a := Expr.ref 9 (.arr ρ σ)
  let p := Expr.ref 10 ι
  let varCode := (Expr.ref 6 (.arr ι .base)).app p
  let varFamily := (Expr.ref 5 (.arr .base f)).app varCode
  let argument := (Expr.ref 4 (.arr f ρ)).app varFamily
  let bodyFamily := (Expr.ref 3 (.arr σ f)).app (a.app argument)
  let belowBinder := (Expr.ref 7 (.arr ι (.arr ι ι))).app p |>.app (Expr.ref 8 ι)
  let bodyCode := (Expr.ref 2 (.arr f (.arr ι .base))).app bodyFamily |>.app belowBinder
  let abstractionCode := (Expr.ref 1 (.arr ι (.arr .base .base))).app p |>.app bodyCode
  Expr.lam 10 ι abstractionCode

private def phiArrow (ρ σ : Ty) (psi : M.Dom (.arr M.tyF ρ))
    (phi : M.Dom (.arr σ M.tyF)) : M.Dom (.arr (.arr ρ σ) M.tyF) :=
  let family := (Expr.ref 0 (.arr (.arr M.tyIdx .base) M.tyF)).app
    (phiIndexedExpr M.tyF M.tyIdx ρ σ)
  (Expr.lam 9 (.arr ρ σ) family).denote M.toLambdaModel (M.phiEnv ρ σ psi phi)

private def psiArrow (ρ σ : Ty) (phi : M.Dom (.arr ρ M.tyF))
    (psi : M.Dom (.arr M.tyF σ)) : M.Dom (.arr M.tyF (.arr ρ σ)) :=
  let L := M.toLambdaModel
  let f := M.tyF
  let η := L.withValue L.defaultEnv 0 phi
  let η := L.withValue η 1 psi
  let η := L.withValue η 2 M.applyFamilyFn
  let argument := (Expr.ref 0 (.arr ρ f)).app (Expr.ref 4 ρ)
  let application := (Expr.ref 2 (.arr f (.arr f f))).app (Expr.ref 3 f) |>.app argument
  let reflected := (Expr.ref 1 (.arr f σ)).app application
  (Expr.lam 3 f (Expr.lam 4 ρ reflected)).denote L η

/-- Simultaneously interpret the quotation and reflection terms by recursion on the type,
as in Section 4. Each arrow clause evaluates a typed λ-term in the given model. -/
def inversionPair : (ρ : Ty) → M.Dom (.arr ρ M.tyF) × M.Dom (.arr M.tyF ρ)
  | .base => (M.emb, M.extractFamilyFn)
  | .arr ρ σ =>
      let domain := inversionPair ρ
      let codomain := inversionPair σ
      (M.phiArrow ρ σ domain.2 codomain.1, M.psiArrow ρ σ domain.1 codomain.2)

/-- The interpretation of the quotation term Φρ. -/
def phi (ρ : Ty) : M.Dom (.arr ρ M.tyF) :=
  (M.inversionPair ρ).1

/-- The interpretation of the reflection term Ψρ. -/
def psi (ρ : Ty) : M.Dom (.arr M.tyF ρ) :=
  (M.inversionPair ρ).2

@[simp]
theorem phi_base : M.phi .base = M.emb := rfl

theorem psi_base (x : M.Dom M.tyF) :
    M.eqM .base (M.appM (M.psi .base) x) (M.f_extract x) :=
  M.extractFamilyFn_spec x

/-- At an arrow type the quotation term abstracts a coded variable through
the represented family of its body. -/
theorem phi_arr (ρ σ : Ty) (a : M.Dom (.arr ρ σ)) :
    ∃ step : M.Dom (.arr M.tyIdx .base),
      (∀ p : M.Dom M.tyIdx,
        M.eqM .base (M.appM step p)
          (M.appM (M.appM (M.abst ρ) p)
            (M.appM
              (M.appM M.funOp
                (M.appM (M.phi σ)
                  (M.appM a (M.appM (M.psi ρ) (M.appM M.emb (M.appM (M.mvar ρ) p))))))
              (M.appM (M.appM M.append p) (M.codeIdx zeroIdx))))) ∧
      M.eqM M.tyF (M.appM (M.phi (.arr ρ σ)) a) (M.fam step) := by
  let L := M.toLambdaModel
  let η := M.phiEnv ρ σ (M.psi ρ) (M.phi σ)
  let body := phiIndexedExpr M.tyF M.tyIdx ρ σ
  let step := body.denote L (L.withValue η 9 a)
  refine ⟨step, ?_, ?_⟩
  · intro p
    dsimp only [step, body, phiIndexedExpr]
    apply Expr.apply_denote_lam
    repeat' first | exact Expr.denote_ref L _ (by simp [η, phiEnv] <;> rfl) | apply Expr.denote_app
  · change M.eqM M.tyF (M.appM (M.phiArrow ρ σ (M.psi ρ) (M.phi σ)) a) (M.fam step)
    unfold phiArrow
    apply Expr.apply_denote_lam
    refine M.eqM_trans _ ?_ (M.famFn_spec step)
    apply Expr.denote_app
    · exact Expr.denote_ref L _ (by simp [phiEnv] <;> rfl)
    · exact M.eqM_refl _ step

/-- At an arrow type the reflection term applies a represented function to the
family obtained by quoting its argument. -/
theorem psi_arr (ρ σ : Ty) (f : M.Dom M.tyF) (a : M.Dom ρ) :
    M.eqM σ (M.appM (M.appM (M.psi (.arr ρ σ)) f) a)
      (M.appM (M.psi σ) (M.f_app f (M.appM (M.phi ρ) a))) := by
  change M.eqM σ (M.appM (M.appM (M.psiArrow ρ σ (M.phi ρ) (M.psi σ)) f) a) _
  unfold psiArrow
  apply Expr.apply₂_denote_lam
  apply Expr.denote_app
  · exact Expr.denote_ref M.toLambdaModel _ (by simp <;> rfl)
  · refine M.eqM_trans _ ?_ (M.applyFamilyFn_spec f (M.appM (M.phi ρ) a))
    repeat' first
    | exact Expr.denote_ref M.toLambdaModel _ (by simp <;> rfl)
    | apply Expr.denote_app

/-- Reflect all substituted variables to form an evaluation environment. -/
def etaSubst (θ : Substitution) : M.Env :=
  fun y => M.appM (M.psi y.ty) (M.appM M.emb (M.codeTerm (θ y)))

/-- The procedure-to-expression function as an element of the model. -/
def inverse (ρ : Ty) : M.Dom (.arr ρ .base) :=
  M.toLambdaModel.compose M.extractFamilyFn (M.phi ρ)

theorem inverse_spec (ρ : Ty) (a : M.Dom ρ) :
    M.eqM .base (M.appM (M.inverse ρ) a) (M.f_extract (M.appM (M.phi ρ) a)) :=
  M.eqM_trans _ (M.toLambdaModel.compose_spec M.extractFamilyFn (M.phi ρ) a)
    (M.extractFamilyFn_spec (M.appM (M.phi ρ) a))

/-- The procedure-to-expression relation. At type ρ the result is a typed term whose code
represents the output of the interpreted inversion term. -/
def IsPeResult (ρ : Ty) (a : M.Dom ρ) (t : Term) : Prop :=
  HasType t ρ ∧ M.eqM .base (M.codeTerm t) (M.appM (M.inverse ρ) a)

end AdmissibleModel

/-- Inductive characterization of primitive recursive functions `ℕ^k → ℕ` (Section 3, p. 206). -/
inductive IsPrimRec : {k : Nat} → ((Fin k → Nat) → Nat) → Prop where
  | zero {k : Nat} : IsPrimRec (k := k) (fun _ => 0)
  | succ : IsPrimRec (k := 1) (fun v => v ⟨0, by decide⟩ + 1)
  | proj {k : Nat} (i : Fin k) : IsPrimRec (k := k) (fun v => v i)
  | comp {k m : Nat} {g : (Fin m → Nat) → Nat} {hs : Fin m → (Fin k → Nat) → Nat} :
      IsPrimRec g →
      (∀ j : Fin m, IsPrimRec (hs j)) →
      IsPrimRec (k := k) (fun v => g (fun j => hs j v))
  | prec {k : Nat} {g : (Fin k → Nat) → Nat} {h : (Fin (k + 2) → Nat) → Nat} :
      IsPrimRec g →
      IsPrimRec h →
      IsPrimRec (k := k + 1) (fun v =>
        Nat.rec
          (g (fun i => v ⟨i.val + 1, by omega⟩))
          (fun y ih =>
            h (fun j =>
              if _hj0 : j.val = 0 then y
              else if _hj1 : j.val = 1 then ih
              else v ⟨j.val - 1, by omega⟩))
          (v ⟨0, by omega⟩))

/-- Binary function `h : Nat → Nat → Nat` is primitive recursive (Section 3, p. 206). -/
def IsBinaryPrimRec (h : Nat → Nat → Nat) : Prop :=
  IsPrimRec (k := 2) (fun v => h (v ⟨0, by decide⟩) (v ⟨1, by decide⟩))

/-- Unary function `f : Nat → Nat` is primitive recursive (Section 3, p. 206). -/
def IsUnaryPrimRec (f : Nat → Nat) : Prop :=
  IsPrimRec (k := 1) (fun v => f (v ⟨0, by decide⟩))

/-- Section 3 (p. 206): A pr-model represents all binary primitive recursive functions
through an injection into its ground type. -/
structure PRModel extends LambdaModel.{u} where
  nu : Nat → Dom .base
  nu_inj : ∀ n m : Nat, eqM .base (nu n) (nu m) → n = m
  reprBinary : ∀ h : Nat → Nat → Nat, IsBinaryPrimRec h →
      ∃ hBar : Dom (.arr .base (.arr .base .base)),
        ∀ n m : Nat, eqM .base (appM (appM hBar (nu n)) (nu m)) (nu (h n m))

/-- Representation of unary primitive recursive functions follows from the binary case
by adjoining an unused argument. -/
theorem PRModel.reprUnary (M : PRModel.{u}) (f : Nat → Nat) (hf : IsUnaryPrimRec f) :
    ∃ fBar : M.Dom (.arr .base .base),
      ∀ n : Nat, M.eqM .base (M.appM fBar (M.nu n)) (M.nu (f n)) := by
  let h : Nat → Nat → Nat := fun n _ => f n
  have hh : IsBinaryPrimRec h := by
    exact IsPrimRec.comp (hs := fun _ v => v ⟨0, by decide⟩) hf
      (fun _ => IsPrimRec.proj ⟨0, by decide⟩)
  obtain ⟨g, hg⟩ := M.reprBinary h hh
  refine ⟨M.toLambdaModel.bindSecond g (M.nu 0), fun n => ?_⟩
  exact M.eqM_trans _ (M.toLambdaModel.bindSecond_spec g (M.nu 0) (M.nu n)) (hg n 0)

/-- Effective repetition-free numbering of terms `Λ` and indices `{0,1}*` (Section 3, p. 206). -/
structure EffectiveNumbering where
  termOfNat : Nat → Term
  natOfTerm : Term → Nat
  idxOfNat : Nat → Index
  natOfIdx : Index → Nat
  term_left_inv : ∀ r : Term, termOfNat (natOfTerm r) = r
  term_right_inv : ∀ n : Nat, natOfTerm (termOfNat n) = n
  idx_left_inv : ∀ k : Index, idxOfNat (natOfIdx k) = k
  idx_right_inv : ∀ n : Nat, natOfIdx (idxOfNat n) = n
  append_prim : IsBinaryPrimRec (fun n m => natOfIdx (appendIdx (idxOfNat n) (idxOfNat m)))
  mvar_prim : ∀ ρ : Ty, IsUnaryPrimRec (fun n => natOfTerm (.var (indexedVar ρ (idxOfNat n))))
  app_prim : IsBinaryPrimRec (fun n m => natOfTerm (.app (termOfNat n) (termOfNat m)))
  abst_prim : ∀ ρ : Ty, IsBinaryPrimRec (fun n m =>
      natOfTerm (.lam (indexedVar ρ (idxOfNat n)) (termOfNat m)))
  exemb_prim : IsUnaryPrimRec (fun n => natOfTerm (EXTRACT (EMB (termOfNat n))))
  alpha_prim : IsBinaryPrimRec (fun n m => natOfTerm (EMB (termOfNat n) (idxOfNat m)))
  indext_prim : ∃ indext : Nat → Nat → Nat,
      IsBinaryPrimRec indext ∧
      ∀ r : Term,
        let n := natOfTerm (EMB r epsIdx)
        let m := natOfTerm (EMB r zeroIdx)
        EXTRACT (EMB r) = EMB r (idxOfNat (indext n m))

end BergerSchwichtenberg1991V2


