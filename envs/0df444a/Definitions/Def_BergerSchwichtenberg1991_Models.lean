-- Prove2me | Definitions.Def_BergerSchwichtenberg1991_Models
-- name    : BergerSchwichtenberg1991_Models
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-30T01:55:16.236944+00:00
-- url     : https://prove2.me/theorems/0bb5bc30-2efd-41d1-b583-d0780cee8bca
-- title:
--   Sections 1, 3-5: Extensional λ-Models, Admissible Models, pr-Models, and Reification/Reflection (`Φ_ρ`/`Ψ_ρ`)
-- statement:
--   Formalizes Sections 1, 3, 4, and 5 of Berger and Schwichtenberg (LICS 1991): extensional λ-models (`LambdaModel`), admissible λ-models (`AdmissibleModel`, Section 3, p. 205), auxiliary operations `f_extract`, `f_app`, `fam` (Lemma 4), the mutually recursive reification/reflection functionals `Φ_ρ` and `Ψ_ρ` (`InversionFunctionals`, Section 4, p. 207), the substitution environment `η_θ`, the inversion functional `p-e_ρ` (`IsPeResult`, `invCode`), and primitive recursive models (`PRModel`, `EffectiveNumbering`, p. 206).
-- source:
--   Ulrich Berger and Helmut Schwichtenberg, 'An inverse of the evaluation functional for typed λ-calculus', Proceedings of the Sixth Annual IEEE Symposium on Logic in Computer Science (LICS 1991), pp. 203-211 (doi:10.1109/LICS.1991.151645). Sections 1, 3-5, pp. 204-208.

import Definitions.Def_BergerSchwichtenberg1991_Syntax

/-!
# Admissible λ-Models, pr-Models, and the Inversion Functional (Berger–Schwichtenberg 1991, Sections 1, 3–5)

Source: Ulrich Berger and Helmut Schwichtenberg,
"An inverse of the evaluation functional for typed λ-calculus",
*LICS 1991*, pp. 203–211, Sections 1, 3, 4, 5 (pp. 204–208).

This module formalizes:
- Section 1: Extensional pre-structures and λ-models (`LambdaModel`, p. 204), environments (`Env`),
  evaluation `|r|η`, and semantic validity `ModelsEq` (`M ⊨ r = s`).
- Section 3: Admissible λ-models (`AdmissibleModel`, p. 205), primitive recursive functions
  and pr-models (`PRModel`, p. 206), and auxiliary operations `f_extract`, `f_app`, `fam`
  (Lemma 4, p. 206).
- Section 4: The mutually recursive reification/reflection functionals `Φ_ρ` (`Phi`) and `Ψ_ρ`
  (`Psi`, p. 207), the substitution environment `η_θ` (`etaSubst`), the procedure-to-expression
  inversion relation `pe_ρ` (`IsPeResult`, p. 207), and `inv_ρ` (`invCode`) for pr-models (p. 208).
-/

namespace BergerSchwichtenberg1991

universe u

/-- Section 1 (p. 204): An extensional λ-model `M = (M^ρ, A_{ρ,σ}, =_ρ, |·|·)` consists of:
- a carrier `Dom ρ` (`M^ρ`) for each type `ρ`,
- application mappings `appM ρ σ : M^{ρ→σ} → M^ρ → M^σ`,
- equivalence relations `eqM ρ` (`=_ρ`) that are congruences for `appM` and satisfy
  extensionality (`∀ b ∈ M^ρ, a b =_σ a' b ⇒ a =_{ρ→σ} a'`),
- an evaluation mapping `eval r η ∈ M^ρ` satisfying the variable, application, and abstraction
  laws of a λ-model, and respecting α-equivalence. -/
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
  eval : Term → (∀ x : Var, Dom x.ty) → (ρ : Ty) → Dom ρ
  eval_var : ∀ (x : Var) (η : ∀ v : Var, Dom v.ty),
      eqM x.ty (eval (.var x) η x.ty) (η x)
  eval_app : ∀ (t r : Term) (ρ σ : Ty) (η : ∀ v : Var, Dom v.ty),
      HasType t (.arr ρ σ) → HasType r ρ →
      eqM σ (eval (.app t r) η σ) (appM (eval t η (.arr ρ σ)) (eval r η ρ))
  eval_lam : ∀ (x : Var) (s : Term) (σ : Ty) (η : ∀ v : Var, Dom v.ty) (a : Dom x.ty),
      HasType s σ →
      eqM σ (appM (eval (.lam x s) η (.arr x.ty σ)) a)
            (eval s (fun y => if h : y = x then h ▸ a else η y) σ)
  eval_congr_env : ∀ (r : Term) (ρ : Ty) (η₁ η₂ : ∀ v : Var, Dom v.ty),
      HasType r ρ →
      (∀ v ∈ freeVars r, eqM v.ty (η₁ v) (η₂ v)) →
      eqM ρ (eval r η₁ ρ) (eval r η₂ ρ)
  eval_alpha : ∀ {r s : Term} (ρ : Ty) (η : ∀ v : Var, Dom v.ty),
      HasType r ρ → AlphaEq r s →
      eqM ρ (eval r η ρ) (eval s η ρ)

namespace LambdaModel

/-- Environment `ENV` mapping each typed variable `x^ρ` to `M^ρ` (p. 204). -/
abbrev Env (M : LambdaModel.{u}) := ∀ x : Var, M.Dom x.ty

/-- Environment update `η[x ↦ a]` (p. 204). -/
def updateEnv (M : LambdaModel.{u}) (η : M.Env) (x : Var) (a : M.Dom x.ty) : M.Env :=
  fun y => if h : y = x then h ▸ a else η y

/-- Default evaluation `|r|` of a closed term `r ∈ Λ^ρ` (independent of the environment `η`
by `eval_congr_env`). -/
def evalIn (M : LambdaModel.{u}) (r : Term) (ρ : Ty) (η : M.Env) : M.Dom ρ :=
  M.eval r η ρ

/-- `M ⊨_η r = s` holds if `|r|η =_ρ |s|η` in `M` (Section 1, p. 204). -/
def ModelsEqAt (M : LambdaModel.{u}) (ρ : Ty) (η : M.Env) (r s : Term) : Prop :=
  M.eqM ρ (M.eval r η ρ) (M.eval s η ρ)

/-- `M ⊨ r = s` holds if `∀ η : ENV, M ⊨_η r = s` (Section 1, p. 204). -/
def ModelsEq (M : LambdaModel.{u}) (ρ : Ty) (r s : Term) : Prop :=
  ∀ η : M.Env, M.ModelsEqAt ρ η r s

/-- An element `a ∈ M^ρ` is λ-definable (with respect to environment `η` on closed terms)
if there is a closed term `r ∈ Λ^ρ` such that `|r| =_ρ a` (Section 4, p. 207). -/
def IsLambdaDefinable (M : LambdaModel.{u}) (ρ : Ty) (a : M.Dom ρ) : Prop :=
  ∃ r : Term, HasType r ρ ∧ IsClosed r ∧ ∀ η : M.Env, M.eqM ρ (M.eval r η ρ) a

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
  /-- Closure of `M` under the λ-definable step combinator used in `Φ_{ρ→σ}` (Section 4, p. 207):
      for every transformation `body : M^ι → M^f`, the functional
      `p ↦ abst_ρ p (fun (body p) (append p ⌈0⌉))` is represented by an element of `M^{ι→o}`
      whenever `body` comes from `a : M^{ρ→σ}`, `Ψ_ρ : M^f → M^ρ`, and `Φ_σ : M^σ → M^f`. -/
  mkStepFun : (ρ : Ty) → (Dom tyIdx → Dom tyF) → Dom (.arr tyIdx .base)
  mkStepFun_spec : ∀ (ρ : Ty) (body : Dom tyIdx → Dom tyF) (p : Dom tyIdx),
      (∀ p₁ p₂ : Dom tyIdx, eqM tyIdx p₁ p₂ → eqM tyF (body p₁) (body p₂)) →
      eqM .base (appM (mkStepFun ρ body) p)
        (appM (appM (abst ρ) p)
          (appM (appM funOp (body p)) (appM (appM append p) (codeIdx zeroIdx))))

namespace AdmissibleModel

variable (M : AdmissibleModel.{u})

/-- Section 3 (p. 206): `f-extract f = extract (fun f)`. -/
def f_extract (f : M.Dom M.tyF) : M.Dom .base :=
  M.appM M.extract (M.appM M.funOp f)

/-- Section 3 (p. 206): `f-app f g = emb (app (f-extract f) (f-extract g))`. -/
def f_app (f g : M.Dom M.tyF) : M.Dom M.tyF :=
  M.appM M.emb (M.appM (M.appM M.appCode (M.f_extract f)) (M.f_extract g))

/-- Section 3 (p. 206): `fam(a) = emb (extract(a))`. -/
def fam (a : M.Dom (.arr M.tyIdx .base)) : M.Dom M.tyF :=
  M.appM M.emb (M.appM M.extract a)

end AdmissibleModel

/-- Structure packaging the interpreted λ-terms `Φ_ρ ∈ M^{ρ→f}` and `Ψ_ρ ∈ M^{f→ρ}` defined by
the recursion equations of Section 4 (p. 207) in an admissible model `M`:
- `Φ_o = emb`
- `Ψ_o = f-extract`
- `Φ_{ρ→σ}(a) = fam(λp^ι. abst_ρ p (fun (Φ_σ (a (Ψ_ρ (emb (mvar_ρ p))))) (append p ⌈0⌉)))`
- `Ψ_{ρ→σ}(f)(a) = Ψ_σ (f-app f (Φ_ρ a))`. -/
structure InversionFunctionals (M : AdmissibleModel.{u}) where
  Phi : (ρ : Ty) → M.Dom (.arr ρ M.tyF)
  Psi : (ρ : Ty) → M.Dom (.arr M.tyF ρ)
  phi_base : ∀ a : M.Dom .base,
      M.eqM M.tyF (M.appM (Phi .base) a) (M.appM M.emb a)
  psi_base : ∀ f : M.Dom M.tyF,
      M.eqM .base (M.appM (Psi .base) f) (M.f_extract f)
  phi_arr : ∀ (ρ σ : Ty) (a : M.Dom (.arr ρ σ)),
      ∃ step : M.Dom (.arr M.tyIdx .base),
        (∀ p : M.Dom M.tyIdx,
          M.eqM .base (M.appM step p)
            (M.appM (M.appM (M.abst ρ) p)
              (M.appM
                (M.appM M.funOp
                  (M.appM (Phi σ)
                    (M.appM a (M.appM (Psi ρ) (M.appM M.emb (M.appM (M.mvar ρ) p))))))
                (M.appM (M.appM M.append p) (M.codeIdx zeroIdx))))) ∧
        M.eqM M.tyF (M.appM (Phi (.arr ρ σ)) a) (M.fam step)
  psi_arr : ∀ (ρ σ : Ty) (f : M.Dom M.tyF) (a : M.Dom ρ),
      M.eqM σ (M.appM (M.appM (Psi (.arr ρ σ)) f) a)
        (M.appM (Psi σ) (M.f_app f (M.appM (Phi ρ) a)))

namespace InversionFunctionals

variable {M : AdmissibleModel.{u}} (IF : InversionFunctionals M)

/-- Section 4 (p. 207): For any substitution `θ`, the environment `η_θ ∈ ENV` is defined by
`η_θ(y^ρ) = Ψ_ρ(emb(⌈θ y^ρ⌉))`. -/
def etaSubst (θ : Substitution) : M.Env :=
  fun y => M.appM (IF.Psi y.ty) (M.appM M.emb (M.codeTerm (θ y)))

/-- Environment `η_id` corresponding to the identity substitution `θ_id(y) = y` (p. 207). -/
def etaId : M.Env :=
  IF.etaSubst idSubst

/-- Section 4 (p. 207): Partial inversion functional `p-e_ρ(a) ≃ (f-extract(Φ_ρ(a)))^~`:
`IsPeResult ρ a t` holds if `t ∈ Λ^ρ` and `⌈t⌉ =_o f-extract(Φ_ρ(a))`. -/
def IsPeResult (ρ : Ty) (a : M.Dom ρ) (t : Term) : Prop :=
  HasType t ρ ∧ M.eqM .base (M.codeTerm t) (M.f_extract (M.appM (IF.Phi ρ) a))

/-- Code-level inversion functional `inv_ρ(a) := f-extract(Φ_ρ(a)) ∈ M^o` (p. 208). -/
def invCode (ρ : Ty) (a : M.Dom ρ) : M.Dom .base :=
  M.f_extract (M.appM (IF.Phi ρ) a)

end InversionFunctionals

/-- Inductive characterization of primitive recursive functions `ℕ^k → ℕ` (Section 3, p. 206). -/
inductive IsPrimRec : {k : Nat} → ((Fin k → Nat) → Nat) → Prop where
  | zero : IsPrimRec (k := 1) (fun _ => 0)
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

/-- Section 3 (p. 206): A λ-model `M` is a `pr-model` if all unary and binary primitive
recursive functions are represented in `M` via an injection `ν : ω → M^o` (with respect to `=_o`). -/
structure PRModel extends LambdaModel.{u} where
  nu : Nat → Dom .base
  nu_inj : ∀ n m : Nat, eqM .base (nu n) (nu m) → n = m
  reprUnary : ∀ f : Nat → Nat, IsUnaryPrimRec f →
      ∃ fBar : Dom (.arr .base .base),
        ∀ n : Nat, eqM .base (appM fBar (nu n)) (nu (f n))
  reprBinary : ∀ h : Nat → Nat → Nat, IsBinaryPrimRec h →
      ∃ hBar : Dom (.arr .base (.arr .base .base)),
        ∀ n m : Nat, eqM .base (appM (appM hBar (nu n)) (nu m)) (nu (h n m))

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

end BergerSchwichtenberg1991


