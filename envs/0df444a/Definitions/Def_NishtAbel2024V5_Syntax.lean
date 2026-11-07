-- Prove2me | Definitions.Def_NishtAbel2024V5_Syntax
-- name    : NishtAbel2024V5_Syntax
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T04:15:37.877192+00:00
-- url     : https://prove2.me/theorems/98ac3e53-4d42-45ac-b677-604b6b56cc3b
-- title:
--   Chapter 4 (V5): Full System $F_\omega^{\mathsf{cop,SCT}}$ Syntax, Variance Kinding, Subtyping, and Copattern Typing
-- statement:
--   Complete syntax and static semantics of System $F_\omega^{\mathsf{cop,SCT}}$ from Chapter 4 of Nisht and Abel (2024). The calculus equips higher-order polymorphic copattern programs with size annotations $a, b ::= \infty + n \mid i + n \mid a \wedge b$, bound normalization $a^\uparrow$, and polarized kinding $\Delta \vdash F : \kappa$ over the variance lattice $\circ \le +, - \le \top$ with higher kinds $\kappa ::= * \mid \pi\kappa \to \kappa^\prime$ and inverse-polarity context scaling $\pi^{-1}\Delta$.
--
--   Types include type operators $\lambda X:\iota.\,F$ and applications $F\,G$, impredicative quantifiers $\forall X:\kappa.\,B$ and $\exists X:\kappa.\,B$, bounded size quantifiers $\forall(j < a).\,B$ and $\exists(j < a).\,B$, and sized inductive and coinductive fixpoints $\mu^a S$ and $\nu^a R$ whose underlying functors may have either positive ($+$) or mixed ($\circ$) variance. The module defines the size-order judgment $\Psi \vdash a \le b$, polarized higher-kinded subtyping $\Psi; \Delta \vdash^\pi F \le G : \kappa$ (including $\beta$-conversion), copattern spine and clause typing, mutual recursive block typing (`BlockTyped`), and lexicographic $F_\omega^{\mathsf{cop}}$ measure blocks (`MeasureBlockTyped`).
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Chapter 4, pp. 19-30, Figures 4.1-4.8

import Definitions.Def_NishtAbel2024V2_Syntax

/-!
# Nisht & Abel (2024), V5: syntax, kinding, subtyping and typing of System `F_ω^{cop,SCT}`

V5 is the full calculus of the thesis (Chapter 4), formalized so that every typing rule is
semantically justified:

* **Sizes** `∞ + n`, `i + n` and meets `a ∧ b` (Section 4.1.2), with bound normalization `a^↑`.
* **Kinds with variance** `κ ::= * | π κ → κ'` over the polarity lattice `◦ ≤ +, − ≤ ⊤`
  (Section 4.1.1), subkinding, and polarized kinding contexts with `π⁻¹ Δ`.
* **Type operators** `λX:ι. F` and applications `F G` (Section 4.2), impredicative quantifiers
  `∀X:κ. B` and `∃X:κ. B` over all kinds, bounded size quantifiers `∀(j < a). B` and
  `∃(j < a). B`, sized inductive and coinductive types `μ^a S` and `ν^a R` whose functors are
  positive (`+`) or of mixed variance (`◦`).
* **Polarized subtyping** (Section 4.2.2) including size subtyping of fixpoints (`μ` covariant,
  `ν` contravariant in the size), variance-directed comparison of operator arguments, and
  β-conversion of type-level redexes.
* **Copatterns** and **mutual blocks** with invocation graphs (Sections 4.3–4.6).

Binding is locally nameless: bound type and size variables are de Bruijn indices, free ones are
names, so no substitution can capture. Run-time terms are Curry-style: types and sizes are erased,
and typing derivations choose them. The invocation graphs and `SCTValid` are reused from
`NishtAbel2024V2`.
-/

namespace NishtAbel2024V5

open NishtAbel2024V2 (InvGraph InvGraphFamily SCTValid ConformsToGraph FunName)

/-! ## Sizes -/

/-- Size expressions: `∞ + n`, `i + n` for a free size variable `i`, `k + n` for a bound size
variable with de Bruijn index `k`, and meets `a ∧ b`. -/
inductive Size where
  | inf (n : Nat) : Size
  | var (i : Nat) (n : Nat) : Size
  | bvar (k : Nat) (n : Nat) : Size
  | meet (a b : Size) : Size
  deriving DecidableEq, Repr

namespace Size

/-- `∞`. -/
abbrev infty : Size := inf 0

/-- Increment `a + n`, distributing over meets. -/
def shift : Size → Nat → Size
  | inf m, n => inf (m + n)
  | var i m, n => var i (m + n)
  | bvar k m, n => bvar k (m + n)
  | meet a b, n => meet (a.shift n) (b.shift n)

/-- Bound normalization `a^↑`: `(∞ + n)^↑ = ∞ + 1`, and meets of variables are unchanged. -/
def up : Size → Size
  | inf _ => inf 1
  | var i n => var i n
  | bvar k n => bvar k n
  | meet a b => meet a.up b.up

/-- Simultaneous substitution of sizes for free size variables. -/
def subst (σ : List (Nat × Size)) : Size → Size
  | inf n => inf n
  | var i n =>
      match σ.lookup i with
      | some b => b.shift n
      | none => var i n
  | bvar k n => bvar k n
  | meet a b => meet (a.subst σ) (b.subst σ)

/-- `a.openAt k b`: replace the bound size variable `k` by the locally closed size `b`, lowering
the bound variables above `k`. -/
def openAt : Size → Nat → Size → Size
  | inf n, _, _ => inf n
  | var i n, _, _ => var i n
  | bvar k' n, k, b => if k' = k then b.shift n else if k < k' then bvar (k' - 1) n else bvar k' n
  | meet a₁ a₂, k, b => meet (a₁.openAt k b) (a₂.openAt k b)

end Size

/-- Size context `Ψ`: an entry `(i, a)` declares the free size variable `i` with `i < a`. -/
abbrev SizeCtx := List (Nat × Size)

def SizeCtx.dom (Ψ : SizeCtx) : List Nat := Ψ.map Prod.fst

/-- `Ψ; m ⊢ a`: free size variables declared in `Ψ`, bound size variables below `m`. -/
def SizeWfAt (Ψ : SizeCtx) (m : Nat) : Size → Prop
  | .inf _ => True
  | .var i _ => i ∈ Ψ.dom
  | .bvar k _ => k < m
  | .meet a b => SizeWfAt Ψ m a ∧ SizeWfAt Ψ m b

/-- `Ψ ⊢ a` for locally closed sizes. -/
abbrev SizeWf (Ψ : SizeCtx) : Size → Prop := SizeWfAt Ψ 0

/-- `⊢ Ψ`: distinct variables, each bounded by a size built from earlier variables. -/
inductive SizeCtxWf : SizeCtx → Prop where
  | nil : SizeCtxWf []
  | snoc {Ψ : SizeCtx} {i : Nat} {a : Size} :
      SizeCtxWf Ψ → i ∉ Ψ.dom → SizeWf Ψ a → SizeCtxWf (Ψ ++ [(i, a)])

/-- Strict size comparison `Ψ ⊢ a < b` on locally closed sizes (Section 4.1.2). A variable is
below `∞ + m` for every `m` only when its bound is at most `∞`. -/
inductive SizeLt (Ψ : SizeCtx) : Size → Size → Prop where
  | inf_inf {n m : Nat} : n < m → SizeLt Ψ (.inf n) (.inf m)
  | var_var {i n m : Nat} : i ∈ Ψ.dom → n < m → SizeLt Ψ (.var i n) (.var i m)
  | bound {i n : Nat} {a b : Size} :
      (i, a) ∈ Ψ → SizeLt Ψ (a.shift n) (b.shift 1) → SizeLt Ψ (.var i n) b
  | var_inf {i n m : Nat} {a : Size} :
      (i, a) ∈ Ψ → SizeLt Ψ a (.inf 1) → SizeLt Ψ (.var i n) (.inf m)
  | meet_l {a b c : Size} : SizeLt Ψ a c → SizeWf Ψ b → SizeLt Ψ (.meet a b) c
  | meet_r {a b c : Size} : SizeLt Ψ b c → SizeWf Ψ a → SizeLt Ψ (.meet a b) c
  | lt_meet {a b c : Size} : SizeLt Ψ a b → SizeLt Ψ a c → SizeLt Ψ a (.meet b c)
  | trans {a b c : Size} : SizeLt Ψ a b → SizeLt Ψ b c → SizeLt Ψ a c

/-- Non-strict size comparison `Ψ ⊢ a ≤ b`, defined as `Ψ ⊢ a < b + 1`. -/
def SizeLe (Ψ : SizeCtx) (a b : Size) : Prop := SizeLt Ψ a (b.shift 1)

/-- `Ψ ⊢ a⃗ ⇐ Ψ'`: well-formed instantiation of the size parameters `Ψ'` of a callee. -/
def SizeSubstWf (Ψ : SizeCtx) (as : List Size) (Ψ' : SizeCtx) : Prop :=
  as.length = Ψ'.length ∧
  ∀ (k : Nat) (hk : k < Ψ'.length) (ha : k < as.length),
    SizeLt Ψ (as[k]'ha) ((Ψ'[k]'hk).2.subst (Ψ'.dom.zip as))

/-! ## Polarities and kinds -/

/-- Polarities (variances) `◦` (mixed), `+`, `−`, `⊤` (unused). -/
inductive Pol where
  | mix : Pol
  | pos : Pol
  | neg : Pol
  | top : Pol
  deriving DecidableEq, Repr

namespace Pol

/-- The lattice `◦ ≤ + ≤ ⊤`, `◦ ≤ − ≤ ⊤`. -/
def le : Pol → Pol → Prop
  | .mix, _ => True
  | .pos, .pos => True
  | .pos, .top => True
  | .neg, .neg => True
  | .neg, .top => True
  | .top, .top => True
  | _, _ => False

/-- A variable of polarity `π` may be used directly iff `π ≤ +`. -/
def Usable (π : Pol) : Prop := le π .pos

/-- Negation `−π`. -/
def negate : Pol → Pol
  | .pos => .neg
  | .neg => .pos
  | π => π

/-- Composition `π π'` (commutative). -/
def comp : Pol → Pol → Pol
  | .top, _ => .top
  | _, .top => .top
  | .mix, _ => .mix
  | _, .mix => .mix
  | .pos, π => π
  | .neg, π => π.negate

/-- Inverse composition `π⁻¹ π'`. -/
def inv : Pol → Pol → Pol
  | .top, _ => .mix
  | .mix, .mix => .mix
  | .mix, _ => .top
  | .pos, π => π
  | .neg, π => π.negate

end Pol

/-- Kinds with variance `κ ::= * | π κ → κ'`. Sizes are not type-level arguments: bounded size
quantification has its own binders (the thesis forbids sizes as operator parameters). -/
inductive Kind where
  | star : Kind
  | arr (π : Pol) (κ₁ κ₂ : Kind) : Kind
  deriving DecidableEq, Repr

/-- Simple kinds `ι ::= * | ι → ι'`. -/
inductive SKind where
  | star : SKind
  | arr (ι₁ ι₂ : SKind) : SKind
  deriving DecidableEq, Repr

/-- The simple kind `|κ|` underlying a kind. -/
def Kind.erase : Kind → SKind
  | .star => .star
  | .arr _ κ₁ κ₂ => .arr κ₁.erase κ₂.erase

/-- Subkinding `κ ≤ κ'`: contravariant in the domain and in the variance annotation. -/
inductive SubKind : Kind → Kind → Prop where
  | star : SubKind .star .star
  | arr {π π' : Pol} {κ₁ κ₁' κ₂ κ₂' : Kind} :
      Pol.le π' π → SubKind κ₁' κ₁ → SubKind κ₂ κ₂' →
      SubKind (.arr π κ₁ κ₂) (.arr π' κ₁' κ₂')

/-! ## Types -/

/-- Type-level expressions. `var k` is a bound type variable (bound by `λ`, `μ`, `ν`, `∀X`,
`∃X`), `fvar X` a free one. `lam ι F` is `λX:ι. F`. `app F G ι` is the application `F G`
recording the simple kind `ι` of the argument. `allS a B` is `∀(j < a). B` and `exS a B` is
`∃(j < a). B`, binding the size index `0` in `B`. In `μ^a S` and `ν^a R`, each constructor or
destructor type binds the recursion variable as type index `0`. -/
inductive Ty where
  | unit : Ty
  | prod : Ty → Ty → Ty
  | arr : Ty → Ty → Ty
  | var : Nat → Ty
  | fvar : Nat → Ty
  | lam : SKind → Ty → Ty
  | app : Ty → Ty → SKind → Ty
  | mu : Size → List Ty → Ty
  | nu : Size → List Ty → Ty
  | allT : Kind → Ty → Ty
  | exT : Kind → Ty → Ty
  | allS : Size → Ty → Ty
  | exS : Size → Ty → Ty
  deriving Repr

mutual

/-- Substitute sizes for free size variables. -/
def Ty.substSize (σ : List (Nat × Size)) : Ty → Ty
  | .unit => .unit
  | .prod A B => .prod (A.substSize σ) (B.substSize σ)
  | .arr A B => .arr (A.substSize σ) (B.substSize σ)
  | .var X => .var X
  | .fvar X => .fvar X
  | .lam ι F => .lam ι (F.substSize σ)
  | .app F G ι => .app (F.substSize σ) (G.substSize σ) ι
  | .mu a S => .mu (a.subst σ) (Ty.substSizeList σ S)
  | .nu a R => .nu (a.subst σ) (Ty.substSizeList σ R)
  | .allT κ B => .allT κ (B.substSize σ)
  | .exT κ B => .exT κ (B.substSize σ)
  | .allS a B => .allS (a.subst σ) (B.substSize σ)
  | .exS a B => .exS (a.subst σ) (B.substSize σ)

def Ty.substSizeList (σ : List (Nat × Size)) : List Ty → List Ty
  | [] => []
  | A :: S => A.substSize σ :: Ty.substSizeList σ S

end

mutual

/-- `A.substTy k T`: replace the bound type variable `k` by the locally closed type `T`, lowering
the bound type variables above `k`. -/
def Ty.substTy : Ty → Nat → Ty → Ty
  | .unit, _, _ => .unit
  | .prod A B, k, T => .prod (A.substTy k T) (B.substTy k T)
  | .arr A B, k, T => .arr (A.substTy k T) (B.substTy k T)
  | .var X, k, T => if X = k then T else if k < X then .var (X - 1) else .var X
  | .fvar X, _, _ => .fvar X
  | .lam ι F, k, T => .lam ι (F.substTy (k + 1) T)
  | .app F G ι, k, T => .app (F.substTy k T) (G.substTy k T) ι
  | .mu a S, k, T => .mu a (Ty.substTyList S (k + 1) T)
  | .nu a R, k, T => .nu a (Ty.substTyList R (k + 1) T)
  | .allT κ B, k, T => .allT κ (B.substTy (k + 1) T)
  | .exT κ B, k, T => .exT κ (B.substTy (k + 1) T)
  | .allS a B, k, T => .allS a (B.substTy k T)
  | .exS a B, k, T => .exS a (B.substTy k T)

def Ty.substTyList : List Ty → Nat → Ty → List Ty
  | [], _, _ => []
  | A :: S, k, T => A.substTy k T :: Ty.substTyList S k T

end

mutual

/-- `A.openSz k b`: replace the bound size variable `k` by the locally closed size `b`. -/
def Ty.openSz : Ty → Nat → Size → Ty
  | .unit, _, _ => .unit
  | .prod A B, k, b => .prod (A.openSz k b) (B.openSz k b)
  | .arr A B, k, b => .arr (A.openSz k b) (B.openSz k b)
  | .var X, _, _ => .var X
  | .fvar X, _, _ => .fvar X
  | .lam ι F, k, b => .lam ι (F.openSz k b)
  | .app F G ι, k, b => .app (F.openSz k b) (G.openSz k b) ι
  | .mu a S, k, b => .mu (a.openAt k b) (Ty.openSzList S k b)
  | .nu a R, k, b => .nu (a.openAt k b) (Ty.openSzList R k b)
  | .allT κ B, k, b => .allT κ (B.openSz k b)
  | .exT κ B, k, b => .exT κ (B.openSz k b)
  | .allS a B, k, b => .allS (a.openAt k b) (B.openSz (k + 1) b)
  | .exS a B, k, b => .exS (a.openAt k b) (B.openSz (k + 1) b)

def Ty.openSzList : List Ty → Nat → Size → List Ty
  | [], _, _ => []
  | A :: S, k, b => A.openSz k b :: Ty.openSzList S k b

end

mutual

/-- Substitute locally closed types for free type variables. -/
def Ty.substFTy (τ : List (Nat × Ty)) : Ty → Ty
  | .unit => .unit
  | .prod A B => .prod (A.substFTy τ) (B.substFTy τ)
  | .arr A B => .arr (A.substFTy τ) (B.substFTy τ)
  | .var X => .var X
  | .fvar X => (τ.lookup X).getD (.fvar X)
  | .lam ι F => .lam ι (F.substFTy τ)
  | .app F G ι => .app (F.substFTy τ) (G.substFTy τ) ι
  | .mu a S => .mu a (Ty.substFTyList τ S)
  | .nu a R => .nu a (Ty.substFTyList τ R)
  | .allT κ B => .allT κ (B.substFTy τ)
  | .exT κ B => .exT κ (B.substFTy τ)
  | .allS a B => .allS a (B.substFTy τ)
  | .exS a B => .exS a (B.substFTy τ)

def Ty.substFTyList (τ : List (Nat × Ty)) : List Ty → List Ty
  | [] => []
  | A :: S => A.substFTy τ :: Ty.substFTyList τ S

end

/-! ## Kinding -/

/-- Kinding context for free type variables: `(X, π, κ)` declares `X : π κ`. -/
abbrev KCtx := List (Nat × Pol × Kind)

/-- `π⁻¹ Δ`. -/
def KCtx.inv (π : Pol) (Δ : KCtx) : KCtx := Δ.map fun e => (e.1, Pol.inv π e.2.1, e.2.2)

/-- Kinds and polarities of bound type variables, innermost first. -/
abbrev BCtx := List (Pol × Kind)

/-- `π⁻¹` on bound type variables. -/
def BCtx.inv (π : Pol) (Δb : BCtx) : BCtx := Δb.map fun e => (Pol.inv π e.1, e.2)

/-- Kinding `Ψ; Δ; Δb; m ⊢ F : κ` (Section 4.2.1): free size variables in `Ψ`, free type
variables in `Δ`, bound type variables in `Δb`, bound size variables below `m`.

* A variable is usable iff its polarity is at most `+`.
* `A → B` checks `A` under `−⁻¹Δ`; an application `F G` with `F : π κ₁ → κ₂` checks `G` under
  `π⁻¹Δ`.
* `∀X:κ` and `∃X:κ` bind `X` with mixed polarity (`∀κ, ∃κ : +(◦κ → *) → *`).
* The functors of `μ^a S` and `ν^a R` are positive (`+`, checked under `Δ`) or of mixed variance
  (`◦`, checked under `◦⁻¹Δ`, so that only mixed outer variables occur in them). -/
inductive Kinding (Ψ : SizeCtx) : KCtx → BCtx → Nat → Ty → Kind → Prop where
  | unit {Δ : KCtx} {Δb : BCtx} {m : Nat} : Kinding Ψ Δ Δb m .unit .star
  | prod {Δ : KCtx} {Δb : BCtx} {m : Nat} {A B : Ty} :
      Kinding Ψ Δ Δb m A .star → Kinding Ψ Δ Δb m B .star →
      Kinding Ψ Δ Δb m (.prod A B) .star
  | arr {Δ : KCtx} {Δb : BCtx} {m : Nat} {A B : Ty} :
      Kinding Ψ (Δ.inv .neg) (Δb.inv .neg) m A .star → Kinding Ψ Δ Δb m B .star →
      Kinding Ψ Δ Δb m (.arr A B) .star
  | var {Δ : KCtx} {Δb : BCtx} {m k : Nat} {π : Pol} {κ : Kind} :
      Δb[k]? = some (π, κ) → π.Usable → Kinding Ψ Δ Δb m (.var k) κ
  | fvar {Δ : KCtx} {Δb : BCtx} {m X : Nat} {π : Pol} {κ : Kind} :
      Δ.lookup X = some (π, κ) → π.Usable → Kinding Ψ Δ Δb m (.fvar X) κ
  | lam {Δ : KCtx} {Δb : BCtx} {m : Nat} {ι : SKind} {F : Ty} {π : Pol} {κ₁ κ₂ : Kind} :
      κ₁.erase = ι → Kinding Ψ Δ ((π, κ₁) :: Δb) m F κ₂ →
      Kinding Ψ Δ Δb m (.lam ι F) (.arr π κ₁ κ₂)
  | app {Δ : KCtx} {Δb : BCtx} {m : Nat} {F G : Ty} {ι : SKind} {π : Pol} {κ₁ κ₂ : Kind} :
      Kinding Ψ Δ Δb m F (.arr π κ₁ κ₂) → Kinding Ψ (Δ.inv π) (Δb.inv π) m G κ₁ →
      κ₁.erase = ι → Kinding Ψ Δ Δb m (.app F G ι) κ₂
  | mu {Δ : KCtx} {Δb : BCtx} {m : Nat} {a : Size} {S : List Ty} {π : Pol} :
      (π = .pos ∨ π = .mix) → SizeWfAt Ψ m a →
      (∀ T ∈ S, Kinding Ψ (Δ.inv π) ((π, .star) :: Δb.inv π) m T .star) →
      Kinding Ψ Δ Δb m (.mu a S) .star
  | nu {Δ : KCtx} {Δb : BCtx} {m : Nat} {a : Size} {R : List Ty} {π : Pol} :
      (π = .pos ∨ π = .mix) → SizeWfAt Ψ m a →
      (∀ T ∈ R, Kinding Ψ (Δ.inv π) ((π, .star) :: Δb.inv π) m T .star) →
      Kinding Ψ Δ Δb m (.nu a R) .star
  | allT {Δ : KCtx} {Δb : BCtx} {m : Nat} {κ : Kind} {B : Ty} :
      Kinding Ψ Δ ((.mix, κ) :: Δb) m B .star → Kinding Ψ Δ Δb m (.allT κ B) .star
  | exT {Δ : KCtx} {Δb : BCtx} {m : Nat} {κ : Kind} {B : Ty} :
      Kinding Ψ Δ ((.mix, κ) :: Δb) m B .star → Kinding Ψ Δ Δb m (.exT κ B) .star
  | allS {Δ : KCtx} {Δb : BCtx} {m : Nat} {a : Size} {B : Ty} :
      SizeWfAt Ψ m a → Kinding Ψ Δ Δb (m + 1) B .star → Kinding Ψ Δ Δb m (.allS a B) .star
  | exS {Δ : KCtx} {Δb : BCtx} {m : Nat} {a : Size} {B : Ty} :
      SizeWfAt Ψ m a → Kinding Ψ Δ Δb (m + 1) B .star → Kinding Ψ Δ Δb m (.exS a B) .star
  | sub {Δ : KCtx} {Δb : BCtx} {m : Nat} {F : Ty} {κ κ' : Kind} :
      Kinding Ψ Δ Δb m F κ → SubKind κ κ' → Kinding Ψ Δ Δb m F κ'

/-- Kinding of a locally closed type. -/
abbrev KindingC (Ψ : SizeCtx) (Δ : KCtx) (F : Ty) (κ : Kind) : Prop := Kinding Ψ Δ [] 0 F κ

/-- Free type variables of a term typing context, all of mixed polarity. -/
abbrev TyCtx := List (Nat × Kind)

def TyCtx.toK (Θ : TyCtx) : KCtx := Θ.map fun e => (e.1, Pol.mix, e.2)

def KCtx.dom (Δ : KCtx) : List Nat := Δ.map Prod.fst

/-! ## Subtyping -/

/-- Polarized subtyping `Ψ; Δ ⊢ A ≤ B : κ` between locally closed types (Section 4.2.2).
Binders are opened with fresh free variables. `μ` is covariant and `ν` contravariant in the
size, compared after bound normalization (`a^↑ ≤ b^↑`, or `a ≤ b^↑`). Fixpoints with different
functors are comparable
when the larger functor is positive, or when the functors are equivalent. Type-level
β-redexes convert. -/
inductive SubTy : SizeCtx → KCtx → Ty → Ty → Kind → Prop where
  | refl {Ψ : SizeCtx} {Δ : KCtx} {A : Ty} {κ : Kind} : KindingC Ψ Δ A κ → SubTy Ψ Δ A A κ
  | trans {Ψ : SizeCtx} {Δ : KCtx} {A B C : Ty} {κ : Kind} :
      SubTy Ψ Δ A B κ → SubTy Ψ Δ B C κ → SubTy Ψ Δ A C κ
  | beta_l {Ψ : SizeCtx} {Δ : KCtx} {F G B : Ty} {ι : SKind} {κ : Kind} :
      KindingC Ψ Δ (.app (.lam ι F) G ι) κ → SubTy Ψ Δ (F.substTy 0 G) B κ →
      SubTy Ψ Δ (.app (.lam ι F) G ι) B κ
  | beta_r {Ψ : SizeCtx} {Δ : KCtx} {F G A : Ty} {ι : SKind} {κ : Kind} :
      KindingC Ψ Δ (.app (.lam ι F) G ι) κ → SubTy Ψ Δ A (F.substTy 0 G) κ →
      SubTy Ψ Δ A (.app (.lam ι F) G ι) κ
  | prod {Ψ : SizeCtx} {Δ : KCtx} {A A' B B' : Ty} :
      SubTy Ψ Δ A A' .star → SubTy Ψ Δ B B' .star →
      SubTy Ψ Δ (.prod A B) (.prod A' B') .star
  | arr {Ψ : SizeCtx} {Δ : KCtx} {A A' B B' : Ty} :
      SubTy Ψ Δ A' A .star → SubTy Ψ Δ B B' .star →
      SubTy Ψ Δ (.arr A B) (.arr A' B') .star
  | app {Ψ : SizeCtx} {Δ : KCtx} {F F' G G' : Ty} {ι : SKind} {π : Pol} {κ₁ κ₂ : Kind} :
      SubTy Ψ Δ F F' (.arr π κ₁ κ₂) →
      (Pol.le π .pos → SubTy Ψ Δ G G' κ₁) → (Pol.le π .neg → SubTy Ψ Δ G' G κ₁) →
      KindingC Ψ (Δ.inv π) G κ₁ → KindingC Ψ (Δ.inv π) G' κ₁ → κ₁.erase = ι →
      SubTy Ψ Δ (.app F G ι) (.app F' G' ι) κ₂
  | lam {Ψ : SizeCtx} {Δ : KCtx} {F F' : Ty} {ι ι' : SKind} {π : Pol} {κ₁ κ₂ : Kind} {X : Nat} :
      X ∉ Δ.dom →
      SubTy Ψ (Δ ++ [(X, π, κ₁)]) (F.substTy 0 (.fvar X)) (F'.substTy 0 (.fvar X)) κ₂ →
      KindingC Ψ Δ (.lam ι F) (.arr π κ₁ κ₂) → KindingC Ψ Δ (.lam ι' F') (.arr π κ₁ κ₂) →
      SubTy Ψ Δ (.lam ι F) (.lam ι' F') (.arr π κ₁ κ₂)
  | allT {Ψ : SizeCtx} {Δ : KCtx} {κ κ' : Kind} {B B' : Ty} {X : Nat} :
      SubKind κ κ' → X ∉ Δ.dom →
      SubTy Ψ (Δ ++ [(X, .mix, κ)]) (B.substTy 0 (.fvar X)) (B'.substTy 0 (.fvar X)) .star →
      KindingC Ψ Δ (.allT κ' B) .star → KindingC Ψ Δ (.allT κ B') .star →
      SubTy Ψ Δ (.allT κ' B) (.allT κ B') .star
  | exT {Ψ : SizeCtx} {Δ : KCtx} {κ κ' : Kind} {B B' : Ty} {X : Nat} :
      SubKind κ κ' → X ∉ Δ.dom →
      SubTy Ψ (Δ ++ [(X, .mix, κ)]) (B.substTy 0 (.fvar X)) (B'.substTy 0 (.fvar X)) .star →
      KindingC Ψ Δ (.exT κ B) .star → KindingC Ψ Δ (.exT κ' B') .star →
      SubTy Ψ Δ (.exT κ B) (.exT κ' B') .star
  | allS {Ψ : SizeCtx} {Δ : KCtx} {a b : Size} {B B' : Ty} {j : Nat} :
      SizeLe Ψ b a → j ∉ Ψ.dom →
      SubTy (Ψ ++ [(j, b)]) Δ (B.openSz 0 (.var j 0)) (B'.openSz 0 (.var j 0)) .star →
      KindingC Ψ Δ (.allS a B) .star → KindingC Ψ Δ (.allS b B') .star →
      SubTy Ψ Δ (.allS a B) (.allS b B') .star
  | exS {Ψ : SizeCtx} {Δ : KCtx} {a b : Size} {B B' : Ty} {j : Nat} :
      SizeLe Ψ a b → j ∉ Ψ.dom →
      SubTy (Ψ ++ [(j, a)]) Δ (B.openSz 0 (.var j 0)) (B'.openSz 0 (.var j 0)) .star →
      KindingC Ψ Δ (.exS a B) .star → KindingC Ψ Δ (.exS b B') .star →
      SubTy Ψ Δ (.exS a B) (.exS b B') .star
  | mu_pos {Ψ : SizeCtx} {Δ : KCtx} {a b : Size} {S S' : List Ty} {X : Nat} :
      (SizeLe Ψ a.up b.up ∨ SizeLe Ψ a b.up) → S.length = S'.length → X ∉ Δ.dom →
      (∀ (c : Nat) (T T' : Ty), S[c]? = some T → S'[c]? = some T' →
        SubTy Ψ (Δ ++ [(X, .mix, .star)]) (T.substTy 0 (.fvar X)) (T'.substTy 0 (.fvar X))
          .star) →
      (∀ T' ∈ S', Kinding Ψ Δ [(.pos, .star)] 0 T' .star) →
      KindingC Ψ Δ (.mu a S) .star → KindingC Ψ Δ (.mu b S') .star →
      SubTy Ψ Δ (.mu a S) (.mu b S') .star
  | mu_eqv {Ψ : SizeCtx} {Δ : KCtx} {a b : Size} {S S' : List Ty} {X : Nat} :
      (SizeLe Ψ a.up b.up ∨ SizeLe Ψ a b.up) → S.length = S'.length → X ∉ Δ.dom →
      (∀ (c : Nat) (T T' : Ty), S[c]? = some T → S'[c]? = some T' →
        SubTy Ψ (Δ ++ [(X, .mix, .star)]) (T.substTy 0 (.fvar X)) (T'.substTy 0 (.fvar X))
          .star) →
      (∀ (c : Nat) (T T' : Ty), S[c]? = some T → S'[c]? = some T' →
        SubTy Ψ (Δ ++ [(X, .mix, .star)]) (T'.substTy 0 (.fvar X)) (T.substTy 0 (.fvar X))
          .star) →
      KindingC Ψ Δ (.mu a S) .star → KindingC Ψ Δ (.mu b S') .star →
      SubTy Ψ Δ (.mu a S) (.mu b S') .star
  | nu_pos {Ψ : SizeCtx} {Δ : KCtx} {a b : Size} {R R' : List Ty} {X : Nat} :
      (SizeLe Ψ b.up a.up ∨ SizeLe Ψ b a.up) → R.length = R'.length → X ∉ Δ.dom →
      (∀ (d : Nat) (T T' : Ty), R[d]? = some T → R'[d]? = some T' →
        SubTy Ψ (Δ ++ [(X, .mix, .star)]) (T.substTy 0 (.fvar X)) (T'.substTy 0 (.fvar X))
          .star) →
      (∀ T' ∈ R', Kinding Ψ Δ [(.pos, .star)] 0 T' .star) →
      KindingC Ψ Δ (.nu a R) .star → KindingC Ψ Δ (.nu b R') .star →
      SubTy Ψ Δ (.nu a R) (.nu b R') .star
  | nu_eqv {Ψ : SizeCtx} {Δ : KCtx} {a b : Size} {R R' : List Ty} {X : Nat} :
      (SizeLe Ψ b.up a.up ∨ SizeLe Ψ b a.up) → R.length = R'.length → X ∉ Δ.dom →
      (∀ (d : Nat) (T T' : Ty), R[d]? = some T → R'[d]? = some T' →
        SubTy Ψ (Δ ++ [(X, .mix, .star)]) (T.substTy 0 (.fvar X)) (T'.substTy 0 (.fvar X))
          .star) →
      (∀ (d : Nat) (T T' : Ty), R[d]? = some T → R'[d]? = some T' →
        SubTy Ψ (Δ ++ [(X, .mix, .star)]) (T'.substTy 0 (.fvar X)) (T.substTy 0 (.fvar X))
          .star) →
      KindingC Ψ Δ (.nu a R) .star → KindingC Ψ Δ (.nu b R') .star →
      SubTy Ψ Δ (.nu a R) (.nu b R') .star

/-! ## Terms -/

/-- Patterns `p ::= x | () | (p, p) | c p | pack p`. -/
inductive Pat where
  | var : Nat → Pat
  | unit : Pat
  | pair : Pat → Pat → Pat
  | cons : Nat → Pat → Pat
  | pack : Pat → Pat
  deriving DecidableEq, Repr

/-- Copatterns: a pattern for an argument, a projection `.d`, or `·` for a type or size
argument. -/
inductive Copat where
  | pat : Pat → Copat
  | proj : Nat → Copat
  | inst : Copat
  deriving DecidableEq, Repr

def Pat.vars : Pat → List Nat
  | .var x => [x]
  | .unit => []
  | .pair p q => p.vars ++ q.vars
  | .cons _ p => p.vars
  | .pack p => p.vars

def Copat.vars : Copat → List Nat
  | .pat p => p.vars
  | .proj _ => []
  | .inst => []

def spineVars (qs : List Copat) : List Nat := qs.flatMap Copat.vars

mutual

/-- Run-time terms (types and sizes erased). -/
inductive Tm where
  | var : Nat → Tm
  | fn : FunName → Tm
  | app : Tm → Elim → Tm
  | unit : Tm
  | pair : Tm → Tm → Tm
  | cons : Nat → Tm → Tm
  | pack : Tm → Tm
  | lam : List Clause → Tm

/-- Eliminations: an argument, a projection, or an erased type or size argument `·`. -/
inductive Elim where
  | term : Tm → Elim
  | proj : Nat → Elim
  | inst : Elim

/-- A clause `{q⃗ → t}`. -/
inductive Clause where
  | mk : List Copat → Tm → Clause

end

namespace Tm

/-- `r e⃗`. -/
def appSpine (r : Tm) (es : List Elim) : Tm := es.foldl .app r

end Tm

/-- Term substitution: an association list, looked up from the front. -/
abbrev TmSubst := List (Nat × Tm)

mutual

/-- Free term variables. -/
def Tm.fv : Tm → List Nat
  | .var x => [x]
  | .fn _ => []
  | .app r e => r.fv ++ e.fv
  | .unit => []
  | .pair t u => t.fv ++ u.fv
  | .cons _ t => t.fv
  | .pack t => t.fv
  | .lam D => Clause.fvList D

def Elim.fv : Elim → List Nat
  | .term t => t.fv
  | .proj _ => []
  | .inst => []

def Clause.fvList : List Clause → List Nat
  | [] => []
  | .mk qs t :: D => t.fv.filter (fun x => x ∉ spineVars qs) ++ Clause.fvList D

end

/-- A closed term has no free term variables. -/
def Tm.Closed (t : Tm) : Prop := t.fv = []

mutual

/-- Substitution. Binders filter the substitution but are never renamed; the semantics only
substitutes closed terms. -/
def Tm.subst (σ : TmSubst) : Tm → Tm
  | .var x => (σ.lookup x).getD (.var x)
  | .fn f => .fn f
  | .app r e => .app (r.subst σ) (e.subst σ)
  | .unit => .unit
  | .pair t u => .pair (t.subst σ) (u.subst σ)
  | .cons c t => .cons c (t.subst σ)
  | .pack t => .pack (t.subst σ)
  | .lam D => .lam (Clause.substList σ D)

def Elim.subst (σ : TmSubst) : Elim → Elim
  | .term t => .term (t.subst σ)
  | .proj d => .proj d
  | .inst => .inst

def Clause.substList (σ : TmSubst) : List Clause → List Clause
  | [] => []
  | .mk qs t :: D =>
      .mk qs (t.subst (σ.filter (fun p => p.1 ∉ spineVars qs))) :: Clause.substList σ D

end

/-! ## Typing -/

/-- Term context: looked up from the front. -/
abbrev TermCtx := List (Nat × Ty)

/-- Function declaration `f : ∀Ψ. A = D⃗`. -/
structure FunDecl where
  name : FunName
  sizeParams : SizeCtx
  ty : Ty
  clauses : List Clause

/-- Pattern typing `Ψ; Θ ⊢ p : A ⇒ Γ; Ψ'; Θ'` (Section 4.3). Constructor patterns on `μ^a S`
and pack patterns on `∃(j < a)` bind a fresh size variable `j < a`; pack patterns on `∃X:κ`
bind a fresh type variable `X : κ`. -/
inductive PatTy : SizeCtx → TyCtx → Pat → Ty → TermCtx → SizeCtx → TyCtx → Prop where
  | var (Ψ : SizeCtx) (Θ : TyCtx) (x : Nat) (A : Ty) : PatTy Ψ Θ (.var x) A [(x, A)] [] []
  | unit (Ψ : SizeCtx) (Θ : TyCtx) : PatTy Ψ Θ .unit .unit [] [] []
  | pair {Ψ Ψ₁ Ψ₂ : SizeCtx} {Θ Θ₁ Θ₂ : TyCtx} {p q : Pat} {A B : Ty} {Γ₁ Γ₂ : TermCtx} :
      PatTy Ψ Θ p A Γ₁ Ψ₁ Θ₁ → PatTy (Ψ ++ Ψ₁) (Θ ++ Θ₁) q B Γ₂ Ψ₂ Θ₂ →
      PatTy Ψ Θ (.pair p q) (.prod A B) (Γ₁ ++ Γ₂) (Ψ₁ ++ Ψ₂) (Θ₁ ++ Θ₂)
  | cons {Ψ Ψ' : SizeCtx} {Θ Θ' : TyCtx} {c j : Nat} {p : Pat} {a : Size} {S : List Ty}
      {Sc : Ty} {Γ : TermCtx} :
      S[c]? = some Sc → j ∉ Ψ.dom →
      PatTy (Ψ ++ [(j, a)]) Θ p (Sc.substTy 0 (.mu (.var j 0) S)) Γ Ψ' Θ' →
      PatTy Ψ Θ (.cons c p) (.mu a S) Γ ((j, a) :: Ψ') Θ'
  | packT {Ψ Ψ' : SizeCtx} {Θ Θ' : TyCtx} {X : Nat} {κ : Kind} {p : Pat} {B : Ty}
      {Γ : TermCtx} :
      X ∉ Θ.map Prod.fst → PatTy Ψ (Θ ++ [(X, κ)]) p (B.substTy 0 (.fvar X)) Γ Ψ' Θ' →
      PatTy Ψ Θ (.pack p) (.exT κ B) Γ Ψ' ((X, κ) :: Θ')
  | packS {Ψ Ψ' : SizeCtx} {Θ Θ' : TyCtx} {j : Nat} {p : Pat} {a : Size} {B : Ty}
      {Γ : TermCtx} :
      j ∉ Ψ.dom → PatTy (Ψ ++ [(j, a)]) Θ p (B.openSz 0 (.var j 0)) Γ Ψ' Θ' →
      PatTy Ψ Θ (.pack p) (.exS a B) Γ ((j, a) :: Ψ') Θ'

/-- Copattern spine typing `Ψ; Θ ⊢ q⃗ : A ⇒ Γ; Ψ'; Θ'; C` (Section 4.3). -/
inductive SpineTy :
    SizeCtx → TyCtx → List Copat → Ty → TermCtx → SizeCtx → TyCtx → Ty → Prop where
  | nil (Ψ : SizeCtx) (Θ : TyCtx) (A : Ty) : SpineTy Ψ Θ [] A [] [] [] A
  | pat {Ψ Ψ₁ Ψ₂ : SizeCtx} {Θ Θ₁ Θ₂ : TyCtx} {p : Pat} {qs : List Copat} {A B C : Ty}
      {Γ₁ Γ₂ : TermCtx} :
      PatTy Ψ Θ p A Γ₁ Ψ₁ Θ₁ → SpineTy (Ψ ++ Ψ₁) (Θ ++ Θ₁) qs B Γ₂ Ψ₂ Θ₂ C →
      SpineTy Ψ Θ (.pat p :: qs) (.arr A B) (Γ₁ ++ Γ₂) (Ψ₁ ++ Ψ₂) (Θ₁ ++ Θ₂) C
  | proj {Ψ Ψ' : SizeCtx} {Θ Θ' : TyCtx} {d j : Nat} {qs : List Copat} {a : Size}
      {R : List Ty} {Rd C : Ty} {Γ : TermCtx} :
      R[d]? = some Rd → j ∉ Ψ.dom →
      SpineTy (Ψ ++ [(j, a)]) Θ qs (Rd.substTy 0 (.nu (.var j 0) R)) Γ Ψ' Θ' C →
      SpineTy Ψ Θ (.proj d :: qs) (.nu a R) Γ ((j, a) :: Ψ') Θ' C
  | instT {Ψ Ψ' : SizeCtx} {Θ Θ' : TyCtx} {X : Nat} {κ : Kind} {qs : List Copat} {B C : Ty}
      {Γ : TermCtx} :
      X ∉ Θ.map Prod.fst → SpineTy Ψ (Θ ++ [(X, κ)]) qs (B.substTy 0 (.fvar X)) Γ Ψ' Θ' C →
      SpineTy Ψ Θ (.inst :: qs) (.allT κ B) Γ Ψ' ((X, κ) :: Θ') C
  | instS {Ψ Ψ' : SizeCtx} {Θ Θ' : TyCtx} {j : Nat} {qs : List Copat} {a : Size} {B C : Ty}
      {Γ : TermCtx} :
      j ∉ Ψ.dom → SpineTy (Ψ ++ [(j, a)]) Θ qs (B.openSz 0 (.var j 0)) Γ Ψ' Θ' C →
      SpineTy Ψ Θ (.inst :: qs) (.allS a B) Γ ((j, a) :: Ψ') Θ' C

/-- Typing environment: global signature `Σ`, current block `Ξ`, and the admissibility of
calls into the block: `localOK Ψ g a⃗` says that the call `g a⃗` in size context `Ψ` is allowed.
In System `F_ω^{cop,SCT}` this is conformance to an invocation graph (`sctCallOK`). -/
structure TypingEnv where
  sig : List FunDecl
  block : List FunDecl
  localOK : SizeCtx → FunName → List Size → Prop

/-- `a⃗ ≺_G Ψ_f` for some `G ∈ G(f, g)` (Section 4.5): the call rule of `F_ω^{cop,SCT}`. -/
def sctCallOK (𝒢 : InvGraphFamily) (f : FunName) (Ψf : SizeCtx) :
    SizeCtx → FunName → List Size → Prop :=
  fun Ψ g as => ∃ G ∈ 𝒢.graphs f g,
    ConformsToGraph (SizeLt Ψ) (SizeLe Ψ) G as (Ψf.map (fun p => Size.var p.1 0))

mutual

/-- Curry-style expression typing `Ω; Ψ; Θ; Γ ⊢ t : A` (Section 4.5). -/
inductive ExprTy (Ω : TypingEnv) : SizeCtx → TyCtx → TermCtx → Tm → Ty → Prop where
  | var {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {x : Nat} {A : Ty} :
      Γ.lookup x = some A → ExprTy Ω Ψ Θ Γ (.var x) A
  | unit (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) : ExprTy Ω Ψ Θ Γ .unit .unit
  | pair {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {t u : Tm} {A B : Ty} :
      ExprTy Ω Ψ Θ Γ t A → ExprTy Ω Ψ Θ Γ u B → ExprTy Ω Ψ Θ Γ (.pair t u) (.prod A B)
  | cons {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {c : Nat} {t : Tm} {a b : Size}
      {S : List Ty} {Sc : Ty} :
      S[c]? = some Sc → SizeLt Ψ b a.up → KindingC Ψ Θ.toK (.mu a S) .star →
      ExprTy Ω Ψ Θ Γ t (Sc.substTy 0 (.mu b S)) → ExprTy Ω Ψ Θ Γ (.cons c t) (.mu a S)
  | app {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {r s : Tm} {A B : Ty} :
      ExprTy Ω Ψ Θ Γ r (.arr A B) → ExprTy Ω Ψ Θ Γ s A → ExprTy Ω Ψ Θ Γ (.app r (.term s)) B
  | proj {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {r : Tm} {a b : Size} {R : List Ty}
      {d : Nat} {Rd : Ty} :
      ExprTy Ω Ψ Θ Γ r (.nu a R) → R[d]? = some Rd → SizeLt Ψ b a.up →
      ExprTy Ω Ψ Θ Γ (.app r (.proj d)) (Rd.substTy 0 (.nu b R))
  | instT {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {r : Tm} {κ : Kind} {B T : Ty} :
      ExprTy Ω Ψ Θ Γ r (.allT κ B) → KindingC Ψ Θ.toK T κ →
      ExprTy Ω Ψ Θ Γ (.app r .inst) (B.substTy 0 T)
  | instS {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {r : Tm} {a b : Size} {B : Ty} :
      ExprTy Ω Ψ Θ Γ r (.allS a B) → SizeLt Ψ b a →
      ExprTy Ω Ψ Θ Γ (.app r .inst) (B.openSz 0 b)
  | packT {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {t : Tm} {κ : Kind} {B T : Ty} :
      KindingC Ψ Θ.toK (.exT κ B) .star → KindingC Ψ Θ.toK T κ →
      ExprTy Ω Ψ Θ Γ t (B.substTy 0 T) → ExprTy Ω Ψ Θ Γ (.pack t) (.exT κ B)
  | packS {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {t : Tm} {a b : Size} {B : Ty} :
      KindingC Ψ Θ.toK (.exS a B) .star → SizeLt Ψ b a →
      ExprTy Ω Ψ Θ Γ t (B.openSz 0 b) → ExprTy Ω Ψ Θ Γ (.pack t) (.exS a B)
  | lam {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {D : List Clause} {A : Ty} :
      KindingC Ψ Θ.toK A .star → (∀ cl ∈ D, ClauseTy Ω Ψ Θ Γ cl A) →
      ExprTy Ω Ψ Θ Γ (.lam D) A
  | globalFun {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {g : FunDecl} {as : List Size} :
      g ∈ Ω.sig → SizeCtxWf g.sizeParams → KindingC g.sizeParams [] g.ty .star →
      SizeSubstWf Ψ as g.sizeParams →
      KindingC Ψ Θ.toK (g.ty.substSize (g.sizeParams.dom.zip as)) .star →
      ExprTy Ω Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip as))
  | localFun {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {g : FunDecl} {as : List Size} :
      g ∈ Ω.block → SizeCtxWf g.sizeParams → KindingC g.sizeParams [] g.ty .star →
      SizeSubstWf Ψ as g.sizeParams →
      KindingC Ψ Θ.toK (g.ty.substSize (g.sizeParams.dom.zip as)) .star →
      Ω.localOK Ψ g.name as →
      ExprTy Ω Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip as))
  | sub {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {t : Tm} {A B : Ty} :
      ExprTy Ω Ψ Θ Γ t A → SubTy Ψ Θ.toK A B .star → KindingC Ψ Θ.toK B .star →
      ExprTy Ω Ψ Θ Γ t B

/-- Clause typing `Ω; Ψ; Θ; Γ ⊢ {q⃗ → t} : A`. Pattern variables shadow `Γ`. -/
inductive ClauseTy (Ω : TypingEnv) : SizeCtx → TyCtx → TermCtx → Clause → Ty → Prop where
  | mk {Ψ Ψ' : SizeCtx} {Θ Θ' : TyCtx} {Γ Γ' : TermCtx} {qs : List Copat} {t : Tm}
      {A C : Ty} :
      SpineTy Ψ Θ qs A Γ' Ψ' Θ' C → ExprTy Ω (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) t C →
      ClauseTy Ω Ψ Θ Γ (.mk qs t) A

end

/-- `Σ; Ξ; G ⊢ f : ∀Ψ. A = D⃗` with calls into the block admitted by `callOK`. -/
def DeclTyWith (sig Ξ : List FunDecl) (callOK : SizeCtx → FunName → List Size → Prop)
    (d : FunDecl) : Prop :=
  SizeCtxWf d.sizeParams ∧ KindingC d.sizeParams [] d.ty .star ∧
  ∀ cl ∈ d.clauses, ClauseTy ⟨sig, Ξ, callOK⟩ d.sizeParams [] [] cl d.ty

/-- `Σ; Ξ; G ⊢ f : ∀Ψ. A = D⃗` (Section 4.6). -/
def DeclTy (sig Ξ : List FunDecl) (𝒢 : InvGraphFamily) (d : FunDecl) : Prop :=
  DeclTyWith sig Ξ (sctCallOK 𝒢 d.name d.sizeParams) d

/-- `Σ ⊢ Ξ`: the block is typed with an invocation graph family satisfying SCT. -/
def BlockTy (sig Ξ : List FunDecl) : Prop :=
  ∃ 𝒢 : InvGraphFamily, SCTValid 𝒢 ∧
    (∀ d ∈ Ξ, 𝒢.arity d.name = d.sizeParams.length) ∧
    ∀ d ∈ Ξ, DeclTy sig Ξ 𝒢 d

/-- `⊢ Σ`: each block is typed against the blocks before it. -/
inductive BlocksTy : List (List FunDecl) → Prop where
  | nil : BlocksTy []
  | snoc {blocks : List (List FunDecl)} {Ξ : List FunDecl} :
      BlocksTy blocks → BlockTy blocks.flatten Ξ → BlocksTy (blocks ++ [Ξ])

/-- `⊢ (Σ; u) : A`: typed blocks with distinct names and a main term typed against all of them. -/
def ProgramTy (blocks : List (List FunDecl)) (main : Tm) (A : Ty) : Prop :=
  BlocksTy blocks ∧ (blocks.flatten.map FunDecl.name).Nodup ∧
  ExprTy ⟨blocks.flatten, [], fun _ _ _ => False⟩ [] [] [] main A

/-! ## System `F_ω^{cop}`: lexicographic termination measures (Section 5.5) -/

/-- A call `g a⃗` from a function with size parameters `Ψf` decreases lexicographically along the
measure positions `m`: at the measure positions before some position `m[k]` the sizes do not
increase, and at `m[k]` the size decreases. -/
def lexCallOK (m : List Nat) (Ψf : SizeCtx) : SizeCtx → FunName → List Size → Prop :=
  fun Ψ _ as => as.length = Ψf.length ∧ ∃ k < m.length,
    (∀ k' < k, ∀ i, m[k']? = some i → ∃ (hi : i < as.length) (hj : i < Ψf.length),
      SizeLe Ψ as[i] (.var Ψf[i].1 0)) ∧
    ∃ i, m[k]? = some i ∧ ∃ (hi : i < as.length) (hj : i < Ψf.length),
      SizeLt Ψ as[i] (.var Ψf[i].1 0)

/-- `Σ ⊢ Ξ` in System `F_ω^{cop}`: the functions of the block share the arity `n` and a
duplicate-free measure `m` of size-parameter positions; every call into the block decreases
lexicographically along `m`. -/
def LexBlockTy (sig Ξ : List FunDecl) : Prop :=
  ∃ (n : Nat) (m : List Nat), m.Nodup ∧ (∀ i ∈ m, i < n) ∧ (∀ d ∈ Ξ, d.sizeParams.length = n) ∧
    ∀ d ∈ Ξ, DeclTyWith sig Ξ (lexCallOK m d.sizeParams) d

end NishtAbel2024V5


