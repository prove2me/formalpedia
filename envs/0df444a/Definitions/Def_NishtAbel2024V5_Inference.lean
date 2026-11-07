-- Prove2me | Definitions.Def_NishtAbel2024V5_Inference
-- name    : NishtAbel2024V5_Inference
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T04:15:53.013415+00:00
-- url     : https://prove2.me/theorems/4d9cec10-3734-41e4-83dd-49fbb649a45b
-- title:
--   Chapter 6 (V5): Signature Encoding, Copattern Elaboration, Constraint Solving (Algorithm 1), and Termination Checking (Algorithm 2)
-- statement:
--   Formalization of the size inference and termination checking pipeline from Chapter 6 of Nisht and Abel (2024). Given an unsized System $F_\omega^c$ program, signature encoding $\pi; \Delta \vdash_{\mathsf{SCT}} A \Rightarrow \Psi; A^\prime$ (`Encode`, Section 6.1) assigns fresh size variables to $\mu$-positions at polarity $\pi^*$ and $\nu$-positions at polarity $-\pi^*$, and $\infty$ elsewhere.\n\nPattern and copattern spine elaboration (`InferPat`, `InferSpine`, Section 6.2) introduce rigid size variables with even names, while call-site inference and subtype comparison (`InferTm`, `CheckTm`, `Compare`, `CheckClause`, Section 6.3) introduce flexible size variables with odd names and emit scoped size constraints and recursive call records. Algorithm 1 (`solve`, Section 6.4) computes a closed-form size substitution by propagating rigid predecessors and ceiling bounds through the constraint graph, and Algorithm 2 (`Algorithm2Accepts`, Section 6.5) extracts the invocation graph family $\mathcal{G}$ and verifies $\mathsf{SCTValid}(\mathcal{G})$.
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Chapter 6, pp. 41-61, Figures 6.1-6.9, Algorithms 1-2

import Definitions.Def_NishtAbel2024V5_Syntax

/-!
# Nisht & Abel (2024), V5: inference of sizes and the termination checker (Chapter 6)

The source language is System `F_ω^c`: size-free types (`Unsized`, every fixpoint carries the
placeholder size `∞`) and the run-time terms of V5 (types and sizes are erased, so a source
clause and its size-annotated version coincide). The inference judgments are relational versions of
the thesis's algorithmic rules:

* **Encoding of signatures** `π; Δ ⊢_SCT A ⇒ Ψ; A'` (Section 6.1, `Encode`): fresh size variables
  for `μ` at polarity `π*` and `ν` at polarity `−π*`, `∞` elsewhere.
* **Rigid variables of (co)patterns** (Section 6.2, `InferPat`, `InferSpine`).
* **Call-site inference** (Section 6.3, `InferTm`, `CheckTm`, `CheckClause`): fresh *flexible*
  size variables at constructors (`+`), projections (`−`), calls (`+` for parameters indexing
  inductive types, `−` for coinductive ones, `◦` otherwise) and encoded type arguments (`◦`); size
  side conditions become constraints, recorded with the rigid context they were generated in;
  calls into the block are recorded. Type comparison (`Compare`, Section 6.3.3) generates the
  constraints of subtyping.
* **Constraint solving** (Section 6.4, `solve`, Algorithm 1) and the **termination checker**
  (Section 6.5, `Algorithm2Accepts`, Algorithm 2).

Rigid size variables have even names and flexible ones odd names, so a flexible substitution
never touches a rigid variable. Kinding side conditions of the algorithm are stated on size-erased
types (`Ty.eraseSz`), independently of the size variables in scope.

Repairs with respect to the printed algorithm (documented in `Solutions/V5/DESIGN.md`): calls
generate the bound constraints `a_k < b_k[a⃗/Ψ]` of their size arguments; fixpoints whose functor
is not positive are compared in both directions; and the solver's result is post-checked for
coherence and scoping before invocation graphs are built.
-/

namespace NishtAbel2024V5

open NishtAbel2024V2 (InvGraph InvGraphFamily SCTValid ConformsToGraph FunName EdgeRel)

/-! ## Source types of System `F_ω^c` -/

/-- Simple kinds as kinds of mixed variance. -/
def Kind.ofSKind : SKind → Kind
  | .star => .star
  | .arr ι₁ ι₂ => .arr .mix (Kind.ofSKind ι₁) (Kind.ofSKind ι₂)

mutual

/-- Size-free types of System `F_ω^c`: every fixpoint carries the placeholder size `∞`, and there
are no size quantifiers. -/
inductive Unsized : Ty → Prop where
  | unit : Unsized .unit
  | prod {A B : Ty} : Unsized A → Unsized B → Unsized (.prod A B)
  | arr {A B : Ty} : Unsized A → Unsized B → Unsized (.arr A B)
  | var (k : Nat) : Unsized (.var k)
  | fvar (X : Nat) : Unsized (.fvar X)
  | lam {ι : SKind} {F : Ty} : Unsized F → Unsized (.lam ι F)
  | app {F G : Ty} {ι : SKind} : Unsized F → Unsized G → Unsized (.app F G ι)
  | mu {S : List Ty} : UnsizedList S → Unsized (.mu (.inf 0) S)
  | nu {R : List Ty} : UnsizedList R → Unsized (.nu (.inf 0) R)
  | allT {κ : Kind} {B : Ty} : Unsized B → Unsized (.allT κ B)
  | exT {κ : Kind} {B : Ty} : Unsized B → Unsized (.exT κ B)

inductive UnsizedList : List Ty → Prop where
  | nil : UnsizedList []
  | cons {T : Ty} {S : List Ty} : Unsized T → UnsizedList S → UnsizedList (T :: S)

end

mutual

/-- Size erasure: every size becomes `∞`. Kinding of an annotated type depends only on its size
erasure and on the well-formedness of its sizes. -/
def Ty.eraseSz : Ty → Ty
  | .unit => .unit
  | .prod A B => .prod A.eraseSz B.eraseSz
  | .arr A B => .arr A.eraseSz B.eraseSz
  | .var k => .var k
  | .fvar X => .fvar X
  | .lam ι F => .lam ι F.eraseSz
  | .app F G ι => .app F.eraseSz G.eraseSz ι
  | .mu _ S => .mu (.inf 0) (Ty.eraseSzList S)
  | .nu _ R => .nu (.inf 0) (Ty.eraseSzList R)
  | .allT κ B => .allT κ B.eraseSz
  | .exT κ B => .exT κ B.eraseSz
  | .allS _ B => .allS (.inf 0) B.eraseSz
  | .exS _ B => .exS (.inf 0) B.eraseSz

def Ty.eraseSzList : List Ty → List Ty
  | [] => []
  | A :: S => A.eraseSz :: Ty.eraseSzList S

end

/-- Size-erased kinding: the kinding side conditions of the algorithm. -/
def EKinding (Δ : KCtx) (Δb : BCtx) (A : Ty) (κ : Kind) : Prop :=
  Kinding [] Δ Δb 0 A.eraseSz κ

/-! ## Names -/

/-- Two lists of names are disjoint. -/
def NamesDisjoint (l₁ l₂ : List Nat) : Prop := ∀ x ∈ l₁, x ∉ l₂

/-- Flexible size variables have odd names. -/
def FlexName (k : Nat) : Prop := k % 2 = 1

/-- Rigid size variables have even names. -/
def RigidName (k : Nat) : Prop := k % 2 = 0

/-! ## Section 6.1: encoding of function signatures -/

mutual

/-- `π; Δ ⊢_SCT A ⇒ Ψ; A'` with target polarity `πs` (`π*`): fresh size variables (whose names
satisfy `ok`) for `μ` occurring at polarity `πs` and for `ν` occurring at polarity `−πs`, and `∞`
for all other fixpoints. The operator of an application determines the polarity of its argument
through its kind. -/
inductive Encode (πs : Pol) (ok : Nat → Prop) :
    Pol → KCtx → BCtx → Ty → SizeCtx → Ty → Prop where
  | unit {π : Pol} {Δ : KCtx} {Δb : BCtx} : Encode πs ok π Δ Δb .unit [] .unit
  | prod {π : Pol} {Δ : KCtx} {Δb : BCtx} {A B A' B' : Ty} {Ψ₁ Ψ₂ : SizeCtx} :
      Encode πs ok π Δ Δb A Ψ₁ A' → Encode πs ok π Δ Δb B Ψ₂ B' →
      NamesDisjoint Ψ₁.dom Ψ₂.dom →
      Encode πs ok π Δ Δb (.prod A B) (Ψ₁ ++ Ψ₂) (.prod A' B')
  | arr {π : Pol} {Δ : KCtx} {Δb : BCtx} {A B A' B' : Ty} {Ψ₁ Ψ₂ : SizeCtx} :
      Encode πs ok π.negate Δ Δb A Ψ₁ A' → Encode πs ok π Δ Δb B Ψ₂ B' →
      NamesDisjoint Ψ₁.dom Ψ₂.dom →
      Encode πs ok π Δ Δb (.arr A B) (Ψ₁ ++ Ψ₂) (.arr A' B')
  | var {π : Pol} {Δ : KCtx} {Δb : BCtx} (k : Nat) : Encode πs ok π Δ Δb (.var k) [] (.var k)
  | fvar {π : Pol} {Δ : KCtx} {Δb : BCtx} (X : Nat) : Encode πs ok π Δ Δb (.fvar X) [] (.fvar X)
  | lam {π : Pol} {Δ : KCtx} {Δb : BCtx} {ι : SKind} {F F' : Ty} {Ψ : SizeCtx} :
      Encode πs ok π Δ ((.mix, Kind.ofSKind ι) :: Δb) F Ψ F' →
      Encode πs ok π Δ Δb (.lam ι F) Ψ (.lam ι F')
  | app {π π' : Pol} {Δ : KCtx} {Δb : BCtx} {F G F' G' : Ty} {ι : SKind} {κ₁ κ₂ : Kind}
      {Ψ₁ Ψ₂ : SizeCtx} :
      Kinding [] Δ Δb 0 F (.arr π' κ₁ κ₂) →
      Encode πs ok π Δ Δb F Ψ₁ F' → Encode πs ok (Pol.comp π' π) Δ Δb G Ψ₂ G' →
      NamesDisjoint Ψ₁.dom Ψ₂.dom →
      Encode πs ok π Δ Δb (.app F G ι) (Ψ₁ ++ Ψ₂) (.app F' G' ι)
  | mu_fresh {π : Pol} {Δ : KCtx} {Δb : BCtx} {S S' : List Ty} {Ψ : SizeCtx} {i : Nat} :
      π = πs → ok i → i ∉ Ψ.dom →
      EncodeList πs ok π Δ ((.mix, .star) :: Δb) S Ψ S' →
      Encode πs ok π Δ Δb (.mu (.inf 0) S) ((i, .inf 0) :: Ψ) (.mu (.var i 0) S')
  | mu_inf {π : Pol} {Δ : KCtx} {Δb : BCtx} {S S' : List Ty} {Ψ : SizeCtx} :
      π ≠ πs → EncodeList πs ok π Δ ((.mix, .star) :: Δb) S Ψ S' →
      Encode πs ok π Δ Δb (.mu (.inf 0) S) Ψ (.mu (.inf 0) S')
  | nu_fresh {π : Pol} {Δ : KCtx} {Δb : BCtx} {R R' : List Ty} {Ψ : SizeCtx} {i : Nat} :
      π = πs.negate → ok i → i ∉ Ψ.dom →
      EncodeList πs ok π Δ ((.mix, .star) :: Δb) R Ψ R' →
      Encode πs ok π Δ Δb (.nu (.inf 0) R) ((i, .inf 0) :: Ψ) (.nu (.var i 0) R')
  | nu_inf {π : Pol} {Δ : KCtx} {Δb : BCtx} {R R' : List Ty} {Ψ : SizeCtx} :
      π ≠ πs.negate → EncodeList πs ok π Δ ((.mix, .star) :: Δb) R Ψ R' →
      Encode πs ok π Δ Δb (.nu (.inf 0) R) Ψ (.nu (.inf 0) R')
  | allT {π : Pol} {Δ : KCtx} {Δb : BCtx} {κ : Kind} {B B' : Ty} {Ψ : SizeCtx} :
      Encode πs ok π Δ ((.mix, κ) :: Δb) B Ψ B' →
      Encode πs ok π Δ Δb (.allT κ B) Ψ (.allT κ B')
  | exT {π : Pol} {Δ : KCtx} {Δb : BCtx} {κ : Kind} {B B' : Ty} {Ψ : SizeCtx} :
      Encode πs ok π Δ ((.mix, κ) :: Δb) B Ψ B' →
      Encode πs ok π Δ Δb (.exT κ B) Ψ (.exT κ B')

/-- Encoding of the functors of a datatype or record. -/
inductive EncodeList (πs : Pol) (ok : Nat → Prop) :
    Pol → KCtx → BCtx → List Ty → SizeCtx → List Ty → Prop where
  | nil {π : Pol} {Δ : KCtx} {Δb : BCtx} : EncodeList πs ok π Δ Δb [] [] []
  | cons {π : Pol} {Δ : KCtx} {Δb : BCtx} {T T' : Ty} {S S' : List Ty} {Ψ₁ Ψ₂ : SizeCtx} :
      Encode πs ok π Δ Δb T Ψ₁ T' → EncodeList πs ok π Δ Δb S Ψ₂ S' →
      NamesDisjoint Ψ₁.dom Ψ₂.dom →
      EncodeList πs ok π Δ Δb (T :: S) (Ψ₁ ++ Ψ₂) (T' :: S')

end

/-! ## Occurrences of size variables as fixpoint indices -/

/-- The kind of fixpoint indexed by a size. -/
inductive FixKind where
  | mu : FixKind
  | nu : FixKind
  deriving DecidableEq, Repr

/-- Free size variables of a size expression. -/
def Size.fvars : Size → List Nat
  | .inf _ => []
  | .var i _ => [i]
  | .bvar _ _ => []
  | .meet a b => a.fvars ++ b.fvars

/-- `Δ ⊢ i ∈^π_fk A` (Section 6.1): the size variable `i` occurs in the size index of a fixpoint
of kind `fk` at polarity `π` in `A`. The polarity flips in the domain of arrows and follows the
variance of operators (read off their size-erased kinds). -/
inductive SizeOcc (fk : FixKind) (i : Nat) : KCtx → BCtx → Pol → Ty → Prop where
  | prodL {Δ : KCtx} {Δb : BCtx} {π : Pol} {A B : Ty} :
      SizeOcc fk i Δ Δb π A → SizeOcc fk i Δ Δb π (.prod A B)
  | prodR {Δ : KCtx} {Δb : BCtx} {π : Pol} {A B : Ty} :
      SizeOcc fk i Δ Δb π B → SizeOcc fk i Δ Δb π (.prod A B)
  | arrL {Δ : KCtx} {Δb : BCtx} {π : Pol} {A B : Ty} :
      SizeOcc fk i Δ Δb π.negate A → SizeOcc fk i Δ Δb π (.arr A B)
  | arrR {Δ : KCtx} {Δb : BCtx} {π : Pol} {A B : Ty} :
      SizeOcc fk i Δ Δb π B → SizeOcc fk i Δ Δb π (.arr A B)
  | lam {Δ : KCtx} {Δb : BCtx} {π : Pol} {ι : SKind} {F : Ty} :
      SizeOcc fk i Δ ((.mix, Kind.ofSKind ι) :: Δb) π F → SizeOcc fk i Δ Δb π (.lam ι F)
  | appF {Δ : KCtx} {Δb : BCtx} {π : Pol} {F G : Ty} {ι : SKind} :
      SizeOcc fk i Δ Δb π F → SizeOcc fk i Δ Δb π (.app F G ι)
  | appG {Δ : KCtx} {Δb : BCtx} {π π' : Pol} {F G : Ty} {ι : SKind} {κ₁ κ₂ : Kind} :
      EKinding Δ Δb F (.arr π' κ₁ κ₂) → SizeOcc fk i Δ Δb (Pol.comp π' π) G →
      SizeOcc fk i Δ Δb π (.app F G ι)
  | mu_here {Δ : KCtx} {Δb : BCtx} {a : Size} {S : List Ty} :
      fk = .mu → i ∈ a.fvars → SizeOcc fk i Δ Δb .pos (.mu a S)
  | nu_here {Δ : KCtx} {Δb : BCtx} {a : Size} {R : List Ty} :
      fk = .nu → i ∈ a.fvars → SizeOcc fk i Δ Δb .pos (.nu a R)
  | mu_body {Δ : KCtx} {Δb : BCtx} {π : Pol} {a : Size} {S : List Ty} {T : Ty} :
      T ∈ S → SizeOcc fk i Δ ((.mix, .star) :: Δb) π T → SizeOcc fk i Δ Δb π (.mu a S)
  | nu_body {Δ : KCtx} {Δb : BCtx} {π : Pol} {a : Size} {R : List Ty} {T : Ty} :
      T ∈ R → SizeOcc fk i Δ ((.mix, .star) :: Δb) π T → SizeOcc fk i Δ Δb π (.nu a R)
  | allT {Δ : KCtx} {Δb : BCtx} {π : Pol} {κ : Kind} {B : Ty} :
      SizeOcc fk i Δ ((.mix, κ) :: Δb) π B → SizeOcc fk i Δ Δb π (.allT κ B)
  | exT {Δ : KCtx} {Δb : BCtx} {π : Pol} {κ : Kind} {B : Ty} :
      SizeOcc fk i Δ ((.mix, κ) :: Δb) π B → SizeOcc fk i Δ Δb π (.exT κ B)
  | allS {Δ : KCtx} {Δb : BCtx} {π : Pol} {a : Size} {B : Ty} :
      SizeOcc fk i Δ Δb π B → SizeOcc fk i Δ Δb π (.allS a B)
  | exS {Δ : KCtx} {Δb : BCtx} {π : Pol} {a : Size} {B : Ty} :
      SizeOcc fk i Δ Δb π B → SizeOcc fk i Δ Δb π (.exS a B)

mutual
/-- Free size variables of a type. -/
def Ty.sizeVars : Ty → List Nat
  | .unit => []
  | .prod A B => A.sizeVars ++ B.sizeVars
  | .arr A B => A.sizeVars ++ B.sizeVars
  | .var _ => []
  | .fvar _ => []
  | .lam _ F => F.sizeVars
  | .app F G _ => F.sizeVars ++ G.sizeVars
  | .mu a S => a.fvars ++ Ty.sizeVarsList S
  | .nu a R => a.fvars ++ Ty.sizeVarsList R
  | .allT _ B => B.sizeVars
  | .exT _ B => B.sizeVars
  | .allS a B => a.fvars ++ B.sizeVars
  | .exS a B => a.fvars ++ B.sizeVars

def Ty.sizeVarsList : List Ty → List Nat
  | [] => []
  | A :: S => A.sizeVars ++ Ty.sizeVarsList S
end

/-! ## Section 6.2: rigid size variables of patterns and copattern spines -/

/-- `Ψ; Θ ⊢_SCT p : A ⇒ Γ; Ψ'; Θ'`: constructor patterns introduce fresh rigid size variables
`j < a` (even names), pack patterns on `∃X:κ` fresh type variables. -/
inductive InferPat : SizeCtx → TyCtx → Pat → Ty → TermCtx → SizeCtx → TyCtx → Prop where
  | var (Ψ : SizeCtx) (Θ : TyCtx) (x : Nat) (A : Ty) : InferPat Ψ Θ (.var x) A [(x, A)] [] []
  | unit (Ψ : SizeCtx) (Θ : TyCtx) : InferPat Ψ Θ .unit .unit [] [] []
  | pair {Ψ Ψ₁ Ψ₂ : SizeCtx} {Θ Θ₁ Θ₂ : TyCtx} {p q : Pat} {A B : Ty} {Γ₁ Γ₂ : TermCtx} :
      InferPat Ψ Θ p A Γ₁ Ψ₁ Θ₁ → InferPat (Ψ ++ Ψ₁) (Θ ++ Θ₁) q B Γ₂ Ψ₂ Θ₂ →
      InferPat Ψ Θ (.pair p q) (.prod A B) (Γ₁ ++ Γ₂) (Ψ₁ ++ Ψ₂) (Θ₁ ++ Θ₂)
  | cons {Ψ Ψ' : SizeCtx} {Θ Θ' : TyCtx} {c j : Nat} {p : Pat} {a : Size} {S : List Ty}
      {Sc : Ty} {Γ : TermCtx} :
      S[c]? = some Sc → RigidName j → j ∉ Ψ.dom →
      InferPat (Ψ ++ [(j, a)]) Θ p (Sc.substTy 0 (.mu (.var j 0) S)) Γ Ψ' Θ' →
      InferPat Ψ Θ (.cons c p) (.mu a S) Γ ((j, a) :: Ψ') Θ'
  | pack {Ψ Ψ' : SizeCtx} {Θ Θ' : TyCtx} {X : Nat} {κ : Kind} {p : Pat} {B : Ty}
      {Γ : TermCtx} :
      X ∉ Θ.map Prod.fst → InferPat Ψ (Θ ++ [(X, κ)]) p (B.substTy 0 (.fvar X)) Γ Ψ' Θ' →
      InferPat Ψ Θ (.pack p) (.exT κ B) Γ Ψ' ((X, κ) :: Θ')

/-- `Ψ; Θ ⊢_SCT q⃗ : A ⇒ C; Γ; Ψ'; Θ'`: projections introduce fresh rigid size variables, type
copatterns on `∀X:κ` fresh type variables. -/
inductive InferSpine :
    SizeCtx → TyCtx → List Copat → Ty → TermCtx → SizeCtx → TyCtx → Ty → Prop where
  | nil (Ψ : SizeCtx) (Θ : TyCtx) (A : Ty) : InferSpine Ψ Θ [] A [] [] [] A
  | pat {Ψ Ψ₁ Ψ₂ : SizeCtx} {Θ Θ₁ Θ₂ : TyCtx} {p : Pat} {qs : List Copat} {A B C : Ty}
      {Γ₁ Γ₂ : TermCtx} :
      InferPat Ψ Θ p A Γ₁ Ψ₁ Θ₁ → InferSpine (Ψ ++ Ψ₁) (Θ ++ Θ₁) qs B Γ₂ Ψ₂ Θ₂ C →
      InferSpine Ψ Θ (.pat p :: qs) (.arr A B) (Γ₁ ++ Γ₂) (Ψ₁ ++ Ψ₂) (Θ₁ ++ Θ₂) C
  | proj {Ψ Ψ' : SizeCtx} {Θ Θ' : TyCtx} {d j : Nat} {qs : List Copat} {a : Size}
      {R : List Ty} {Rd C : Ty} {Γ : TermCtx} :
      R[d]? = some Rd → RigidName j → j ∉ Ψ.dom →
      InferSpine (Ψ ++ [(j, a)]) Θ qs (Rd.substTy 0 (.nu (.var j 0) R)) Γ Ψ' Θ' C →
      InferSpine Ψ Θ (.proj d :: qs) (.nu a R) Γ ((j, a) :: Ψ') Θ' C
  | inst {Ψ Ψ' : SizeCtx} {Θ Θ' : TyCtx} {X : Nat} {κ : Kind} {qs : List Copat} {B C : Ty}
      {Γ : TermCtx} :
      X ∉ Θ.map Prod.fst → InferSpine Ψ (Θ ++ [(X, κ)]) qs (B.substTy 0 (.fvar X)) Γ Ψ' Θ' C →
      InferSpine Ψ Θ (.inst :: qs) (.allT κ B) Γ Ψ' ((X, κ) :: Θ') C

/-! ## Section 6.3: flexible variables, constraints, and call records -/

/-- A flexible size variable with its polarity and scope (the rigid size context it was
generated in). -/
structure FlexVar where
  name : Nat
  pol : Pol
  scope : SizeCtx

/-- A size constraint generated in the rigid context `ctx`: `lhs < rhs'` if `strict`, else
`lhs ≤ rhs'`, where `rhs'` is `rhs^↑` if `up` and `rhs` otherwise. -/
structure SConstr where
  ctx : SizeCtx
  lhs : Size
  rhs : Size
  strict : Bool
  up : Bool

/-- A call `g a⃗` into the current block, with the rigid context of the call site. -/
structure CallRec where
  ctx : SizeCtx
  callee : FunName
  args : List Size

mutual
/-- Whether the bound type variable `k` occurs in a type. -/
def Ty.hasBVar : Ty → Nat → Bool
  | .unit, _ => false
  | .prod A B, k => A.hasBVar k || B.hasBVar k
  | .arr A B, k => A.hasBVar k || B.hasBVar k
  | .var X, k => X == k
  | .fvar _, _ => false
  | .lam _ F, k => F.hasBVar (k + 1)
  | .app F G _, k => F.hasBVar k || G.hasBVar k
  | .mu _ S, k => Ty.hasBVarList S (k + 1)
  | .nu _ R, k => Ty.hasBVarList R (k + 1)
  | .allT _ B, k => B.hasBVar (k + 1)
  | .exT _ B, k => B.hasBVar (k + 1)
  | .allS _ B, k => B.hasBVar k
  | .exS _ B, k => B.hasBVar k

def Ty.hasBVarList : List Ty → Nat → Bool
  | [], _ => false
  | A :: S, k => A.hasBVar k || Ty.hasBVarList S k
end

mutual
/-- Whether `i` indexes an inductive (`fk = mu`) or coinductive (`fk = nu`) fixpoint in a type. -/
def Ty.indexes (fk : FixKind) (i : Nat) : Ty → Bool
  | .unit => false
  | .prod A B => A.indexes fk i || B.indexes fk i
  | .arr A B => A.indexes fk i || B.indexes fk i
  | .var _ => false
  | .fvar _ => false
  | .lam _ F => F.indexes fk i
  | .app F G _ => F.indexes fk i || G.indexes fk i
  | .mu a S => (fk == .mu && a.fvars.contains i) || Ty.indexesList fk i S
  | .nu a R => (fk == .nu && a.fvars.contains i) || Ty.indexesList fk i R
  | .allT _ B => B.indexes fk i
  | .exT _ B => B.indexes fk i
  | .allS _ B => B.indexes fk i
  | .exS _ B => B.indexes fk i

def Ty.indexesList (fk : FixKind) (i : Nat) : List Ty → Bool
  | [] => false
  | A :: S => A.indexes fk i || Ty.indexesList fk i S
end

/-- Polarity of the flexible variable instantiating the size parameter `i` of a callee of type
`A`: `+` for parameters indexing inductive types, `−` for coinductive ones, `◦` otherwise. -/
def paramPol (A : Ty) (i : Nat) : Pol :=
  if A.indexes .mu i then .pos else if A.indexes .nu i then .neg else .mix

/-- Flexible variables for the encoded size variables of a type argument (polarity `◦`). -/
def encFlex (Ψ : SizeCtx) (ΨG : SizeCtx) : List FlexVar :=
  ΨG.map fun p => ⟨p.1, .mix, Ψ⟩

/-- Flexible variables for the size arguments of a call. -/
def callFlex (Ψ : SizeCtx) (g : FunDecl) (as : List Nat) : List FlexVar :=
  (g.sizeParams.zip as).map fun p => ⟨p.2, paramPol g.ty p.1.1, Ψ⟩

/-- Bound constraints `a_k < b_k[a⃗/Ψ_g]` for the size arguments of a call. -/
def callBounds (Ψ : SizeCtx) (g : FunDecl) (as : List Size) : List SConstr :=
  (g.sizeParams.zip as).map fun p =>
    ⟨Ψ, p.2, p.1.2.subst (g.sizeParams.dom.zip as), true, false⟩

/-! ## Section 6.3.3: comparison of types -/

mutual

/-- `Ψ; Δ ⊢_SCT A ≤ B : κ ⇒ C`: comparison of size-annotated types along their common shape,
generating the size constraints of subtyping. Kinding side conditions are size-erased. The
functors of fixpoints are compared in one direction when the larger one is positive, and in both
directions otherwise. -/
inductive Compare : SizeCtx → KCtx → Ty → Ty → Kind → List SConstr → Prop where
  | refl {Ψ : SizeCtx} {Δ : KCtx} {A : Ty} {κ : Kind} :
      EKinding Δ [] A κ → Compare Ψ Δ A A κ []
  | beta_l {Ψ : SizeCtx} {Δ : KCtx} {F G B : Ty} {ι : SKind} {κ : Kind} {C : List SConstr} :
      EKinding Δ [] (.app (.lam ι F) G ι) κ → Compare Ψ Δ (F.substTy 0 G) B κ C →
      Compare Ψ Δ (.app (.lam ι F) G ι) B κ C
  | beta_r {Ψ : SizeCtx} {Δ : KCtx} {F G A : Ty} {ι : SKind} {κ : Kind} {C : List SConstr} :
      EKinding Δ [] (.app (.lam ι F) G ι) κ → Compare Ψ Δ A (F.substTy 0 G) κ C →
      Compare Ψ Δ A (.app (.lam ι F) G ι) κ C
  | prod {Ψ : SizeCtx} {Δ : KCtx} {A A' B B' : Ty} {C₁ C₂ : List SConstr} :
      Compare Ψ Δ A A' .star C₁ → Compare Ψ Δ B B' .star C₂ →
      Compare Ψ Δ (.prod A B) (.prod A' B') .star (C₁ ++ C₂)
  | arr {Ψ : SizeCtx} {Δ : KCtx} {A A' B B' : Ty} {C₁ C₂ : List SConstr} :
      Compare Ψ Δ A' A .star C₁ → Compare Ψ Δ B B' .star C₂ →
      Compare Ψ Δ (.arr A B) (.arr A' B') .star (C₁ ++ C₂)
  | app_pos {Ψ : SizeCtx} {Δ : KCtx} {F F' G G' : Ty} {ι : SKind} {κ₁ κ₂ : Kind}
      {C₁ C₂ : List SConstr} :
      Compare Ψ Δ F F' (.arr .pos κ₁ κ₂) C₁ → Compare Ψ Δ G G' κ₁ C₂ →
      EKinding (Δ.inv .pos) [] G κ₁ → EKinding (Δ.inv .pos) [] G' κ₁ → κ₁.erase = ι →
      Compare Ψ Δ (.app F G ι) (.app F' G' ι) κ₂ (C₁ ++ C₂)
  | app_neg {Ψ : SizeCtx} {Δ : KCtx} {F F' G G' : Ty} {ι : SKind} {κ₁ κ₂ : Kind}
      {C₁ C₂ : List SConstr} :
      Compare Ψ Δ F F' (.arr .neg κ₁ κ₂) C₁ → Compare Ψ Δ G' G κ₁ C₂ →
      EKinding (Δ.inv .neg) [] G κ₁ → EKinding (Δ.inv .neg) [] G' κ₁ → κ₁.erase = ι →
      Compare Ψ Δ (.app F G ι) (.app F' G' ι) κ₂ (C₁ ++ C₂)
  | app_mix {Ψ : SizeCtx} {Δ : KCtx} {F F' G G' : Ty} {ι : SKind} {κ₁ κ₂ : Kind}
      {C₁ C₂ C₃ : List SConstr} :
      Compare Ψ Δ F F' (.arr .mix κ₁ κ₂) C₁ → Compare Ψ Δ G G' κ₁ C₂ → Compare Ψ Δ G' G κ₁ C₃ →
      EKinding (Δ.inv .mix) [] G κ₁ → EKinding (Δ.inv .mix) [] G' κ₁ → κ₁.erase = ι →
      Compare Ψ Δ (.app F G ι) (.app F' G' ι) κ₂ (C₁ ++ C₂ ++ C₃)
  | app_top {Ψ : SizeCtx} {Δ : KCtx} {F F' G G' : Ty} {ι : SKind} {κ₁ κ₂ : Kind}
      {C₁ : List SConstr} :
      Compare Ψ Δ F F' (.arr .top κ₁ κ₂) C₁ →
      EKinding (Δ.inv .top) [] G κ₁ → EKinding (Δ.inv .top) [] G' κ₁ → κ₁.erase = ι →
      Compare Ψ Δ (.app F G ι) (.app F' G' ι) κ₂ C₁
  | lam {Ψ : SizeCtx} {Δ : KCtx} {F F' : Ty} {ι ι' : SKind} {π : Pol} {κ₁ κ₂ : Kind} {X : Nat}
      {C : List SConstr} :
      X ∉ Δ.dom →
      Compare Ψ (Δ ++ [(X, π, κ₁)]) (F.substTy 0 (.fvar X)) (F'.substTy 0 (.fvar X)) κ₂ C →
      EKinding Δ [] (.lam ι F) (.arr π κ₁ κ₂) → EKinding Δ [] (.lam ι' F') (.arr π κ₁ κ₂) →
      Compare Ψ Δ (.lam ι F) (.lam ι' F') (.arr π κ₁ κ₂) C
  | allT {Ψ : SizeCtx} {Δ : KCtx} {κ : Kind} {B B' : Ty} {X : Nat} {C : List SConstr} :
      X ∉ Δ.dom →
      Compare Ψ (Δ ++ [(X, .mix, κ)]) (B.substTy 0 (.fvar X)) (B'.substTy 0 (.fvar X)) .star C →
      EKinding Δ [] (.allT κ B) .star → EKinding Δ [] (.allT κ B') .star →
      Compare Ψ Δ (.allT κ B) (.allT κ B') .star C
  | exT {Ψ : SizeCtx} {Δ : KCtx} {κ : Kind} {B B' : Ty} {X : Nat} {C : List SConstr} :
      X ∉ Δ.dom →
      Compare Ψ (Δ ++ [(X, .mix, κ)]) (B.substTy 0 (.fvar X)) (B'.substTy 0 (.fvar X)) .star C →
      EKinding Δ [] (.exT κ B) .star → EKinding Δ [] (.exT κ B') .star →
      Compare Ψ Δ (.exT κ B) (.exT κ B') .star C
  | mu_pos {Ψ : SizeCtx} {Δ : KCtx} {a b : Size} {S S' : List Ty} {X : Nat}
      {C : List SConstr} :
      X ∉ Δ.dom → CompareList Ψ (Δ ++ [(X, .mix, .star)]) X S S' C →
      (∀ T' ∈ S', EKinding Δ [(.pos, .star)] T' .star) →
      EKinding Δ [] (.mu a S) .star → EKinding Δ [] (.mu b S') .star →
      Compare Ψ Δ (.mu a S) (.mu b S') .star (⟨Ψ, a, b, false, true⟩ :: C)
  | mu_eqv {Ψ : SizeCtx} {Δ : KCtx} {a b : Size} {S S' : List Ty} {X : Nat}
      {C₁ C₂ : List SConstr} :
      X ∉ Δ.dom → CompareList Ψ (Δ ++ [(X, .mix, .star)]) X S S' C₁ →
      CompareList Ψ (Δ ++ [(X, .mix, .star)]) X S' S C₂ →
      EKinding Δ [] (.mu a S) .star → EKinding Δ [] (.mu b S') .star →
      Compare Ψ Δ (.mu a S) (.mu b S') .star (⟨Ψ, a, b, false, true⟩ :: (C₁ ++ C₂))
  | nu_pos {Ψ : SizeCtx} {Δ : KCtx} {a b : Size} {R R' : List Ty} {X : Nat}
      {C : List SConstr} :
      X ∉ Δ.dom → CompareList Ψ (Δ ++ [(X, .mix, .star)]) X R R' C →
      (∀ T' ∈ R', EKinding Δ [(.pos, .star)] T' .star) →
      EKinding Δ [] (.nu a R) .star → EKinding Δ [] (.nu b R') .star →
      Compare Ψ Δ (.nu a R) (.nu b R') .star (⟨Ψ, b, a, false, true⟩ :: C)
  | nu_eqv {Ψ : SizeCtx} {Δ : KCtx} {a b : Size} {R R' : List Ty} {X : Nat}
      {C₁ C₂ : List SConstr} :
      X ∉ Δ.dom → CompareList Ψ (Δ ++ [(X, .mix, .star)]) X R R' C₁ →
      CompareList Ψ (Δ ++ [(X, .mix, .star)]) X R' R C₂ →
      EKinding Δ [] (.nu a R) .star → EKinding Δ [] (.nu b R') .star →
      Compare Ψ Δ (.nu a R) (.nu b R') .star (⟨Ψ, b, a, false, true⟩ :: (C₁ ++ C₂))

/-- Pointwise comparison of the functors of two fixpoints, opened at the variable `X`. -/
inductive CompareList : SizeCtx → KCtx → Nat → List Ty → List Ty → List SConstr → Prop where
  | nil {Ψ : SizeCtx} {Δ : KCtx} {X : Nat} : CompareList Ψ Δ X [] [] []
  | cons {Ψ : SizeCtx} {Δ : KCtx} {X : Nat} {T T' : Ty} {S S' : List Ty}
      {C₁ C₂ : List SConstr} :
      Compare Ψ Δ (T.substTy 0 (.fvar X)) (T'.substTy 0 (.fvar X)) .star C₁ →
      CompareList Ψ Δ X S S' C₂ → CompareList Ψ Δ X (T :: S) (T' :: S') (C₁ ++ C₂)

end

/-! ## Section 6.3: call-site inference -/

/-- The environment of the inference: the global signature and the current block, with encoded
signatures. -/
structure InfEnv where
  sig : List FunDecl
  block : List FunDecl

mutual

/-- Inference `Ψ; Θ; Γ ⊢_SCT t ⇒ A; Φ; C; T; K`: the inferred type `A` (with flexible size
variables), the new flexible variables `Φ`, the constraints `C`, the non-recursive variables `T`,
and the calls `K` into the block. -/
inductive InferTm (Ω : InfEnv) :
    SizeCtx → TyCtx → TermCtx → Tm → Ty → List FlexVar → List SConstr → List Nat →
      List CallRec → Prop where
  | var {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {x : Nat} {A : Ty} :
      Γ.lookup x = some A → InferTm Ω Ψ Θ Γ (.var x) A [] [] [] []
  | app {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {r s : Tm} {A B : Ty}
      {Φ₁ Φ₂ : List FlexVar} {C₁ C₂ : List SConstr} {T₁ T₂ : List Nat} {K₁ K₂ : List CallRec} :
      InferTm Ω Ψ Θ Γ r (.arr A B) Φ₁ C₁ T₁ K₁ → CheckTm Ω Ψ Θ Γ A s Φ₂ C₂ T₂ K₂ →
      InferTm Ω Ψ Θ Γ (.app r (.term s)) B (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂)
  | proj {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {r : Tm} {a : Size} {R : List Ty}
      {d j : Nat} {Rd : Ty} {Φ : List FlexVar} {C : List SConstr} {T : List Nat}
      {K : List CallRec} :
      InferTm Ω Ψ Θ Γ r (.nu a R) Φ C T K → R[d]? = some Rd → FlexName j →
      InferTm Ω Ψ Θ Γ (.app r (.proj d)) (Rd.substTy 0 (.nu (.var j 0) R))
        (⟨j, .neg, Ψ⟩ :: Φ) (⟨Ψ, .var j 0, a, true, true⟩ :: C)
        ((if Rd.hasBVar 0 then [] else [j]) ++ T) K
  | inst {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {r : Tm} {κ : Kind} {B G G' : Ty}
      {ΨG : SizeCtx} {Φ : List FlexVar} {C : List SConstr} {T : List Nat} {K : List CallRec} :
      InferTm Ω Ψ Θ Γ r (.allT κ B) Φ C T K → Unsized G → EKinding Θ.toK [] G κ →
      Encode .mix FlexName .mix Θ.toK [] G ΨG G' →
      InferTm Ω Ψ Θ Γ (.app r .inst) (B.substTy 0 G') (encFlex Ψ ΨG ++ Φ) C T K
  | global {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {g : FunDecl} {as : List Nat} :
      g ∈ Ω.sig → as.length = g.sizeParams.length → (∀ k ∈ as, FlexName k) →
      InferTm Ω Ψ Θ Γ (.fn g.name)
        (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0)))
        (callFlex Ψ g as) (callBounds Ψ g (as.map fun k => .var k 0)) [] []
  | local {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {g : FunDecl} {as : List Nat} :
      g ∈ Ω.block → as.length = g.sizeParams.length → (∀ k ∈ as, FlexName k) →
      InferTm Ω Ψ Θ Γ (.fn g.name)
        (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0)))
        (callFlex Ψ g as) (callBounds Ψ g (as.map fun k => .var k 0)) []
        [⟨Ψ, g.name, as.map fun k => .var k 0⟩]

/-- Checking `Ψ; Θ; Γ ⊢_SCT t ⇐ A ⇒ Φ; C; T; K`. -/
inductive CheckTm (Ω : InfEnv) :
    SizeCtx → TyCtx → TermCtx → Ty → Tm → List FlexVar → List SConstr → List Nat →
      List CallRec → Prop where
  | unit {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} : CheckTm Ω Ψ Θ Γ .unit .unit [] [] [] []
  | pair {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {t u : Tm} {A B : Ty}
      {Φ₁ Φ₂ : List FlexVar} {C₁ C₂ : List SConstr} {T₁ T₂ : List Nat} {K₁ K₂ : List CallRec} :
      CheckTm Ω Ψ Θ Γ A t Φ₁ C₁ T₁ K₁ → CheckTm Ω Ψ Θ Γ B u Φ₂ C₂ T₂ K₂ →
      CheckTm Ω Ψ Θ Γ (.prod A B) (.pair t u) (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂)
  | cons {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {c j : Nat} {t : Tm} {a : Size}
      {S : List Ty} {Sc : Ty} {Φ : List FlexVar} {C : List SConstr} {T : List Nat}
      {K : List CallRec} :
      S[c]? = some Sc → FlexName j →
      CheckTm Ω Ψ Θ Γ (Sc.substTy 0 (.mu (.var j 0) S)) t Φ C T K →
      CheckTm Ω Ψ Θ Γ (.mu a S) (.cons c t) (⟨j, .pos, Ψ⟩ :: Φ)
        (⟨Ψ, .var j 0, a, true, true⟩ :: C) ((if Sc.hasBVar 0 then [] else [j]) ++ T) K
  | pack {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {t : Tm} {κ : Kind} {B G G' : Ty}
      {ΨG : SizeCtx} {Φ : List FlexVar} {C : List SConstr} {T : List Nat} {K : List CallRec} :
      Unsized G → EKinding Θ.toK [] G κ → Encode .mix FlexName .mix Θ.toK [] G ΨG G' →
      CheckTm Ω Ψ Θ Γ (B.substTy 0 G') t Φ C T K →
      CheckTm Ω Ψ Θ Γ (.exT κ B) (.pack t) (encFlex Ψ ΨG ++ Φ) C T K
  | lam {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {A : Ty} {D : List Clause}
      {Φ : List FlexVar} {C : List SConstr} {T : List Nat} {K : List CallRec} :
      CheckClauses Ω Ψ Θ Γ A D Φ C T K → CheckTm Ω Ψ Θ Γ A (.lam D) Φ C T K
  | sub {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {r : Tm} {A B : Ty}
      {Φ : List FlexVar} {C₁ C₂ : List SConstr} {T : List Nat} {K : List CallRec} :
      InferTm Ω Ψ Θ Γ r A Φ C₁ T K → Compare Ψ Θ.toK A B .star C₂ →
      CheckTm Ω Ψ Θ Γ B r Φ (C₁ ++ C₂) T K

/-- Checking a list of clauses against a type. -/
inductive CheckClauses (Ω : InfEnv) :
    SizeCtx → TyCtx → TermCtx → Ty → List Clause → List FlexVar → List SConstr → List Nat →
      List CallRec → Prop where
  | nil {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {A : Ty} : CheckClauses Ω Ψ Θ Γ A [] [] [] [] []
  | cons {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {A : Ty} {cl : Clause} {D : List Clause}
      {Φ₁ Φ₂ : List FlexVar} {C₁ C₂ : List SConstr} {T₁ T₂ : List Nat} {K₁ K₂ : List CallRec} :
      CheckClause Ω Ψ Θ Γ A cl Φ₁ C₁ T₁ K₁ → CheckClauses Ω Ψ Θ Γ A D Φ₂ C₂ T₂ K₂ →
      CheckClauses Ω Ψ Θ Γ A (cl :: D) (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂)

/-- Checking a clause: the spine determines the rigid variables `Ψ'` and the body is checked in the
extended context. -/
inductive CheckClause (Ω : InfEnv) :
    SizeCtx → TyCtx → TermCtx → Ty → Clause → List FlexVar → List SConstr → List Nat →
      List CallRec → Prop where
  | mk {Ψ Ψ' : SizeCtx} {Θ Θ' : TyCtx} {Γ Γ' : TermCtx} {A C : Ty} {qs : List Copat} {t : Tm}
      {Φ : List FlexVar} {Cs : List SConstr} {T : List Nat} {K : List CallRec} :
      InferSpine Ψ Θ qs A Γ' Ψ' Θ' C → CheckTm Ω (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) C t Φ Cs T K →
      CheckClause Ω Ψ Θ Γ A (.mk qs t) Φ Cs T K

end

/-! ## Section 6.4: flexible substitutions and coherence -/

/-- A flexible substitution: sizes for flexible variables. -/
abbrev FlexSubst := List (Nat × Size)

/-- Substituting into the bounds of a rigid context. -/
def SizeCtx.substBounds (φ : FlexSubst) (Ψ : SizeCtx) : SizeCtx :=
  Ψ.map fun p => (p.1, p.2.subst φ)

/-- A constraint holds under `φ` in its rigid context. -/
def SConstr.Holds (φ : FlexSubst) (c : SConstr) : Prop :=
  if c.strict then
    SizeLt (c.ctx.substBounds φ) (c.lhs.subst φ) (if c.up then (c.rhs.subst φ).up else c.rhs.subst φ)
  else
    SizeLe (c.ctx.substBounds φ) (c.lhs.subst φ) (if c.up then (c.rhs.subst φ).up else c.rhs.subst φ)

/-- `Ψ; C ⊢ φ`: `φ` is coherent with the constraints. -/
def Coherent (φ : FlexSubst) (C : List SConstr) : Prop := ∀ c ∈ C, c.Holds φ

/-- Every flexible variable is assigned a size built from the rigid variables of its scope. -/
def ScopeOK (φ : FlexSubst) (Φ : List FlexVar) : Prop :=
  ∀ v ∈ Φ, ∃ b, φ.lookup v.name = some b ∧ SizeWf v.scope b

/-! ### Executable checks -/

/-- `Ψ ⊢ a` as a check. -/
def Size.wfB (Ψ : SizeCtx) : Size → Bool
  | .inf _ => true
  | .var i _ => Ψ.dom.contains i
  | .bvar _ _ => false
  | .meet a b => a.wfB Ψ && b.wfB Ψ

/-- A sound, fuel-bounded check of `Ψ ⊢ a < b` following the rules of `SizeLt`. -/
def sizeLtB : Nat → SizeCtx → Size → Size → Bool
  | 0, _, _, _ => false
  | fuel + 1, Ψ, a, b =>
    (match a, b with
      | .inf n, .inf m => decide (n < m)
      | .var i n, .var i' m => decide (i = i') && decide (n < m) && Ψ.dom.contains i
      | _, _ => false) ||
    (match a with
      | .var i n =>
        match Ψ.lookup i with
        | some bnd =>
          sizeLtB fuel Ψ (bnd.shift n) (b.shift 1) ||
            (match b with
              | .inf _ => sizeLtB fuel Ψ bnd (.inf 1)
              | _ => false)
        | none => false
      | .meet a₁ a₂ => (sizeLtB fuel Ψ a₁ b && a₂.wfB Ψ) || (sizeLtB fuel Ψ a₂ b && a₁.wfB Ψ)
      | _ => false) ||
    (match b with
      | .meet b₁ b₂ => sizeLtB fuel Ψ a b₁ && sizeLtB fuel Ψ a b₂
      | _ => false)

/-- A sound check of `Ψ ⊢ a ≤ b`. -/
def sizeLeB (fuel : Nat) (Ψ : SizeCtx) (a b : Size) : Bool := sizeLtB fuel Ψ a (b.shift 1)

/-- Checks a constraint under `φ`. -/
def SConstr.check (fuel : Nat) (φ : FlexSubst) (c : SConstr) : Bool :=
  let r := if c.up then (c.rhs.subst φ).up else c.rhs.subst φ
  if c.strict then sizeLtB fuel (c.ctx.substBounds φ) (c.lhs.subst φ) r
  else sizeLeB fuel (c.ctx.substBounds φ) (c.lhs.subst φ) r

/-- Post-check of coherence. -/
def checkCoherent (fuel : Nat) (φ : FlexSubst) (C : List SConstr) : Bool :=
  C.all (SConstr.check fuel φ)

/-- Post-check of scoping. -/
def checkScope (φ : FlexSubst) (Φ : List FlexVar) : Bool :=
  Φ.all fun v =>
    match φ.lookup v.name with
    | some b => b.wfB v.scope
    | none => false

/-! ### Algorithm 1: solving the constraint graph -/

/-- The flexible variable of a size `k + n` with `k` flexible. -/
def flexVarOf (names : List Nat) : Size → Option Nat
  | .var k _ => if names.contains k then some k else none
  | _ => none

/-- `x` reaches `y` in the constraint graph (edges from the variable of a lower bound to the
constrained variable), within `fuel` steps. -/
def reaches (names : List Nat) (C : List SConstr) : Nat → Nat → Nat → Bool
  | 0, x, y => x == y
  | fuel + 1, x, y =>
    x == y || C.any fun c =>
      flexVarOf names c.lhs == some x &&
        (match flexVarOf names c.rhs with
          | some z => reaches names C fuel z y
          | none => false)

/-- `Ψ ⊢ R a ⇒ b`: the closest size above `a` (its bound for `<`, itself for `≤`). -/
def closestAbove (Ψ : SizeCtx) (strict : Bool) : Size → Size
  | .var i n =>
    if strict then
      match Ψ.lookup i with
      | some b => b.shift n
      | none => .var i (n + 1)
    else .var i n
  | .inf n => if strict then .inf (n + 1) else .inf n
  | .meet a b => .meet (closestAbove Ψ strict a) (closestAbove Ψ strict b)
  | .bvar k n => .bvar k n

/-- `Ψ ⊢ LUB(b⃗) ⇒ c`: the largest of the sizes when they are comparable, `∞` otherwise. -/
def lubSizes (fuel : Nat) (Ψ : SizeCtx) : List Size → Size
  | [] => .inf 0
  | [b] => b
  | b :: bs =>
    let c := lubSizes fuel Ψ bs
    if sizeLeB fuel Ψ b c then c else if sizeLeB fuel Ψ c b then b else .inf 0

/-- `⋀_{i ∈ Ψ} i`. -/
def meetAll : List Nat → Size
  | [] => .inf 0
  | [i] => .var i 0
  | i :: is => .meet (.var i 0) (meetAll is)

/-- One round of Algorithm 1: every unassigned variable whose strongly connected component has all
its outside lower bounds assigned receives a value — `∞` if the component has an internal strict
edge, the meet of the rigid variables of its scope if it contains a non-recursive variable, and
otherwise the least upper bound of the closest bounds of its lower bounds. -/
def solveRound (fuel : Nat) (Φ : List FlexVar) (C : List SConstr) (T : List Nat)
    (φ : FlexSubst) : FlexSubst :=
  let names := Φ.map FlexVar.name
  Φ.foldl (fun φ v =>
    if (φ.lookup v.name).isSome then φ else
    let comp := names.filter fun m =>
      reaches names C names.length v.name m && reaches names C names.length m v.name
    let inComp (s : Size) : Bool :=
      match flexVarOf names s with
      | some m => comp.contains m
      | none => false
    let lower := C.filter fun c => inComp c.rhs && !inComp c.lhs
    let ready := lower.all fun c =>
      match flexVarOf names c.lhs with
      | some m => (φ.lookup m).isSome
      | none => true
    if !ready then φ else
    let strictInside := C.any fun c => c.strict && inComp c.lhs && inComp c.rhs
    let value : Size :=
      if strictInside then .inf 0
      else if comp.any (fun m => T.contains m) then meetAll v.scope.dom
      else lubSizes fuel v.scope (lower.map fun c =>
        closestAbove (c.ctx.substBounds φ) c.strict (c.lhs.subst φ))
    comp.map (fun m => (m, value)) ++ φ) φ

/-- Algorithm 1: the flexible substitution `φ*`. Variables left without a value are set to `∞`. -/
def solve (fuel : Nat) (Φ : List FlexVar) (C : List SConstr) (T : List Nat) : FlexSubst :=
  let φ := (List.range (Φ.length + 1)).foldl (fun φ _ => solveRound fuel Φ C T φ) []
  φ ++ (Φ.map fun v => (v.name, .inf 0))

/-! ## Section 6.5: invocation graphs and Algorithm 2 -/

/-- The invocation graph of a call `g a⃗` from a function with size parameters `Ψf`: an edge
`<` (`≤`) from `a_i` to the `j`-th parameter when `a_i < Ψf_j` (`a_i ≤ Ψf_j`) is established. -/
def callGraph (fuel : Nat) (Ψf : SizeCtx) (φ : FlexSubst) (k : CallRec) : InvGraph :=
  let as := k.args.map (Size.subst φ)
  let Ψ := k.ctx.substBounds φ
  ⟨as.length, Ψf.length, InvGraph.canonicalEdges as.length Ψf.length fun i j =>
    match as[i]?, Ψf[j]? with
    | some a, some p =>
      if sizeLtB fuel Ψ a (.var p.1 0) then some .lt
      else if sizeLeB fuel Ψ a (.var p.1 0) then some .le
      else none
    | _, _ => none⟩

/-- The result of running the inference on a clause. -/
structure ClauseRun where
  flex : List FlexVar
  constraints : List SConstr
  nonrecVars : List Nat
  calls : List CallRec

/-- The solution of a clause run. -/
def ClauseRun.solution (fuel : Nat) (r : ClauseRun) : FlexSubst :=
  solve fuel r.flex r.constraints r.nonrecVars

/-- Algorithm 2 on one clause of an annotated declaration: rigid variables from the copattern
spine, constraints from the body, the solution `φ*` of Algorithm 1, and its post-checks. -/
def ClauseAccepted (fuel : Nat) (Ω : InfEnv) (d : FunDecl) (cl : Clause) (r : ClauseRun) :
    Prop :=
  CheckClause Ω d.sizeParams [] [] d.ty cl r.flex r.constraints r.nonrecVars r.calls ∧
  checkScope (r.solution fuel) r.flex = true ∧
  checkCoherent fuel (r.solution fuel) r.constraints = true

/-- The invocation graphs computed from the runs of all clauses of a block. -/
def blockGraphs (fuel : Nat) (Ξ : List FunDecl) (runs : FunName → Clause → ClauseRun) :
    InvGraphFamily where
  arity := fun f => match Ξ.find? (fun d => d.name == f) with
    | some d => d.sizeParams.length
    | none => 0
  graphs := fun f g => Ξ.flatMap fun d =>
    if d.name = f then
      d.clauses.flatMap fun cl =>
        ((runs d.name cl).calls.filter fun k => k.callee == g).map
          (callGraph fuel d.sizeParams ((runs d.name cl).solution fuel))
    else []

/-- Pointwise relation of two lists. -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : ListRel R [] []
  | cons {a : α} {b : β} {l₁ : List α} {l₂ : List β} :
      R a b → ListRel R l₁ l₂ → ListRel R (a :: l₁) (b :: l₂)

/-- The size-annotated declaration of a source declaration: same name and clauses, encoded type. -/
def EncodedDecl (d d' : FunDecl) : Prop :=
  d'.name = d.name ∧ d'.clauses = d.clauses ∧ d.sizeParams = [] ∧ Unsized d.ty ∧
    EKinding [] [] d.ty .star ∧ Encode .neg RigidName .pos [] [] d.ty d'.sizeParams d'.ty

/-- **Algorithm 2** (Section 6.5) accepts the source block `Ξ` (size-free types, `F_ω^c`) with the
size-annotated block `Ξannot`: every signature is encoded, every clause passes the inference with
post-checked solution, and the invocation graphs computed from all calls satisfy SCT. -/
def Algorithm2Accepts (sig Ξ Ξannot : List FunDecl) : Prop :=
  ListRel EncodedDecl Ξ Ξannot ∧ (Ξannot.map FunDecl.name).Nodup ∧
  ∃ (fuel : Nat) (runs : FunName → Clause → ClauseRun),
    (∀ d ∈ Ξannot, ∀ cl ∈ d.clauses, ClauseAccepted fuel ⟨sig, Ξannot⟩ d cl (runs d.name cl)) ∧
    SCTValid (blockGraphs fuel Ξannot runs)

end NishtAbel2024V5


