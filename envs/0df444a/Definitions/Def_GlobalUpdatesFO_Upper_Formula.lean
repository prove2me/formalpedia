-- Prove2me | Definitions.Def_GlobalUpdatesFO_Upper_Formula
-- name    : GlobalUpdatesFO_Upper_Formula
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:20:30.96896+00:00
-- url     : https://prove2.me/theorems/f36e7ee1-cea5-4ee0-9a8a-64163d2acf4b
-- title:
--   First-order logic with named variables: syntax, length, codes, satisfaction, FO^k, full k-types, the type catalogue, k-bounded interpretations
-- statement:
--   **Formulas** of first-order logic are built from relation atoms $R(x_{i_1},\dots,x_{i_a})$ and equalities $x_i = x_j$ with $\neg$, $\wedge$, $\vee$, $\exists x_i$ and $\forall x_i$; variable symbols are natural numbers $x_0, x_1, \dots$. A formula is in $\mathrm{FO}[\Sigma]$ when every atom names a relation of $\Sigma$ with the right number of arguments. The **length** $|\varphi|$ counts every relation symbol, variable occurrence, equality sign, connective and quantifier as one symbol. Every formula has a **prefix code**, a list of numbers.
--
--   A formula $\varphi$ **with $r$ free variables** has its free variables among $x_0,\dots,x_{r-1}$; for an $r$-tuple $\bar a$, $A \models \varphi(\bar a)$ means $\varphi$ holds when $x_i$ is $a_i$. Quantifiers range over $U(A)$, which may be empty.
--
--   $\varphi \in \mathrm{FO}^k[\Sigma]$ with $r$ free variables means that $\varphi$ uses at most $k$ distinct variable symbols, the $r$ free variables counted whether or not they occur:
--   $$\bigl|\mathrm{vars}(\varphi) \cup \{x_0,\dots,x_{r-1}\}\bigr| \le k .$$
--   The **full $k$-type** of an $r$-tuple is
--   $$\mathrm{tp}^k(A,\bar a) = \{\varphi \in \mathrm{FO}^k[\Sigma] \text{ with } r \text{ free variables} : A \models \varphi(\bar a)\},$$
--   and $\mathrm{tp}^k(A)$, the full sentence $k$-type, is the type of the empty tuple; $(A,\bar a) \equiv_k (B,\bar b)$ means equal full $k$-types. The **type catalogue** $\mathrm{Types}_{\Sigma,k,D}$ is the set of all $\mathrm{tp}^k(A,\bar a)$ with $A$ a finite $\Sigma$-structure of treedepth at most $D$ and $|\bar a| \le k$. A formula $\varphi$ with $r$ free variables is **logically equivalent to the type $\tau$ in $\mathrm{TD}_D$** if $A \models \varphi(\bar a) \iff \mathrm{tp}^k(A,\bar a) = \tau$ for all such $A$ and all $\bar a \in U(A)^r$.
--
--   A **$(\Sigma,\Pi)$-interpretation** $I$ gives a formula $\varphi_R$ for each $R \in \Pi$; it is **$k$-bounded** when $\mathrm{maxarity}(\Sigma), \mathrm{maxarity}(\Pi) \le k$ and each $\varphi_R \in \mathrm{FO}^k[\Sigma]$ has $\mathrm{arity}(R)$ free variables. $I(A)$ is the $\Pi$-structure on $U(A)$ with $R(I(A)) = \{\bar a : A \models \varphi_R(\bar a)\}$. The code of $I$ is the concatenation of the codes of $\varphi_0, \varphi_1, \dots$.
--
--   **Formalization Note** Satisfaction is defined for partial assignments; an atom on an unassigned variable is false, which never matters for a formula whose free variables are assigned. Formulas are taken as syntax, so a type contains every bound-variable renaming of its members, as in the paper.
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), pp. 17–18, §3.4–3.5; p. 18, §3.5.1; p. 21, §3.6

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure

set_option autoImplicit false

namespace GlobalUpdatesFO.Upper

/-- **First-order formulas** with named variables (Korhonen, Sokołowski, *On efficient global
updates in first-order logic*, STOC 2027 submission, §3.4, p. 17): relation atoms `R(x_{i₁}, …,
x_{i_a})`, equality `x_i = x_j`, negation, conjunction, disjunction and the quantifiers `∃ x_i`,
`∀ x_i`. Variable symbols are natural numbers; relation symbols are the indices `0, …, |Σ| − 1` of
the signature. -/
inductive Formula where
  | rel (R : ℕ) (args : List ℕ)
  | eq (x y : ℕ)
  | neg (φ : Formula)
  | conj (φ ψ : Formula)
  | disj (φ ψ : Formula)
  | ex (x : ℕ) (φ : Formula)
  | all (x : ℕ) (φ : Formula)
  deriving DecidableEq

namespace Formula

/-- The **length** `|φ|` (§3.4, p. 17): the number of symbols, counting each relation symbol, each
variable occurrence, the equality sign, each connective `¬, ∧, ∨` and each quantifier as one. -/
def len : Formula → ℕ
  | rel _ args => 1 + args.length
  | eq _ _ => 3
  | neg φ => 1 + φ.len
  | conj φ ψ => 1 + φ.len + ψ.len
  | disj φ ψ => 1 + φ.len + ψ.len
  | ex _ φ => 2 + φ.len
  | all _ φ => 2 + φ.len

/-- The set of variable symbols occurring in `φ` (free or bound). -/
def vars : Formula → Finset ℕ
  | rel _ args => args.toFinset
  | eq x y => {x, y}
  | neg φ => φ.vars
  | conj φ ψ => φ.vars ∪ ψ.vars
  | disj φ ψ => φ.vars ∪ ψ.vars
  | ex x φ => insert x φ.vars
  | all x φ => insert x φ.vars

/-- The set of free variables of `φ`. -/
def freeVars : Formula → Finset ℕ
  | rel _ args => args.toFinset
  | eq x y => {x, y}
  | neg φ => φ.freeVars
  | conj φ ψ => φ.freeVars ∪ ψ.freeVars
  | disj φ ψ => φ.freeVars ∪ ψ.freeVars
  | ex x φ => φ.freeVars.erase x
  | all x φ => φ.freeVars.erase x

/-- `φ` is a formula of `FO[Σ]`: every relation atom names a relation of `Σ` and has exactly
`arity(R)` arguments. -/
def WF (σ : Signature) : Formula → Prop
  | rel R args => ∃ h : R < σ.length, args.length = σ.get ⟨R, h⟩
  | eq _ _ => True
  | neg φ => φ.WF σ
  | conj φ ψ => φ.WF σ ∧ ψ.WF σ
  | disj φ ψ => φ.WF σ ∧ ψ.WF σ
  | ex _ φ => φ.WF σ
  | all _ φ => φ.WF σ

/-- The prefix **code** of a formula as a list of numbers: `[0, R, a, i₁, …, i_a]` for
`R(x_{i₁}, …, x_{i_a})`, `[1, i, j]` for `x_i = x_j`, `2 :: φ` for `¬φ`, `3 :: φ ++ ψ` for `φ ∧ ψ`,
`4 :: φ ++ ψ` for `φ ∨ ψ`, `5 :: i :: φ` for `∃ x_i φ`, `6 :: i :: φ` for `∀ x_i φ`. -/
def code : Formula → List ℕ
  | rel R args => 0 :: R :: args.length :: args
  | eq x y => [1, x, y]
  | neg φ => 2 :: φ.code
  | conj φ ψ => 3 :: (φ.code ++ ψ.code)
  | disj φ ψ => 4 :: (φ.code ++ ψ.code)
  | ex x φ => 5 :: x :: φ.code
  | all x φ => 6 :: x :: φ.code

/-- **Satisfaction** of `φ` in `A` under a partial assignment `v` of the variable symbols
(§3.4, p. 17). An atom mentioning an unassigned variable is false; on formulas whose free variables
are all assigned this is the standard Tarskian semantics (quantifiers range over `U`, which may be
empty). -/
def Holds {σ : Signature} {U : Type*} (A : Structure σ U) : Formula → (ℕ → Option U) → Prop
  | rel R args, v => ∃ h : R < σ.length, ∃ t ∈ A.rel ⟨R, h⟩,
      List.ofFn (fun i => some (t i)) = args.map v
  | eq x y, v => ∃ u : U, v x = some u ∧ v y = some u
  | neg φ, v => ¬ Holds A φ v
  | conj φ ψ, v => Holds A φ v ∧ Holds A ψ v
  | disj φ ψ, v => Holds A φ v ∨ Holds A ψ v
  | ex x φ, v => ∃ u : U, Holds A φ (Function.update v x (some u))
  | all x φ, v => ∀ u : U, Holds A φ (Function.update v x (some u))

end Formula

/-- The assignment of an `r`-tuple `ā` to the free variables `x_0, …, x_{r−1}`. -/
def tupleAsg {U : Type*} {r : ℕ} (a : Fin r → U) : ℕ → Option U :=
  fun i => if h : i < r then some (a ⟨i, h⟩) else none

/-- `A ⊨ φ(ā)` (§3.4, p. 17): `φ` is read as a formula with the `r` free variables
`x_0, …, x_{r−1}` and `ā` is an `r`-tuple of elements. -/
def Sat {σ : Signature} {U : Type*} (A : Structure σ U) (φ : Formula) {r : ℕ} (a : Fin r → U) :
    Prop :=
  Formula.Holds A φ (tupleAsg a)

/-- `φ ∈ FO^k[Σ]` **with `r` free variables** (§3.5, p. 17): `φ` is a formula of `FO[Σ]` whose free
variables are among `x_0, …, x_{r−1}`, and it uses at most `k` distinct variable symbols, the `r`
free variables `x_0, …, x_{r−1}` counted (and distinct) whether or not they occur. -/
def IsFOk (σ : Signature) (k r : ℕ) (φ : Formula) : Prop :=
  φ.WF σ ∧ φ.freeVars ⊆ Finset.range r ∧ (φ.vars ∪ Finset.range r).card ≤ k

/-- The **full `k`-type** `tp^k(A, ā)` of an `r`-tuple (§3.5, p. 17): the set of all formulas of
`FO^k[Σ]` with `r` free variables that hold in `(A, ā)`. (It is empty when `r > k`.) -/
def tp {σ : Signature} {U : Type*} (k : ℕ) (A : Structure σ U) {r : ℕ} (a : Fin r → U) :
    Set Formula :=
  {φ | IsFOk σ k r φ ∧ Sat A φ a}

/-- The **full sentence `k`-type** `tp^k(A)` (§3.5, p. 18): the full `k`-type of the empty tuple. -/
def tp0 {σ : Signature} {U : Type*} (k : ℕ) (A : Structure σ U) : Set Formula :=
  tp k A (Fin.elim0 : Fin 0 → U)

/-- The **type catalogue** `Types_{Σ,k,D}` (§3.5.1, p. 18): the union over `0 ≤ r ≤ k` of
`Types^r_{Σ,k,D} = {tp^k(A, ā) | A a Σ-structure, td(A) ≤ D, ā ∈ U(A)^r}`, over all finite
`Σ`-structures. -/
def Types (σ : Signature) (k D : ℕ) : Set (Set Formula) :=
  {τ | ∃ (U : Type) (_ : Fintype U) (A : Structure σ U) (r : ℕ) (a : Fin r → U),
    r ≤ k ∧ A.td ≤ D ∧ τ = tp k A a}

/-- `φ` (with `r` free variables) is **logically equivalent to the type `τ` in `TD_D`**
(§3.5, p. 18): `A ⊨ φ(ā) ↔ tp^k(A, ā) = τ` for every finite `Σ`-structure `A` of treedepth at most
`D` and every `ā ∈ U(A)^r`. -/
def LogEquivTypeTD (σ : Signature) (k D : ℕ) (φ : Formula) (r : ℕ) (τ : Set Formula) : Prop :=
  ∀ (U : Type) [Fintype U] (A : Structure σ U), A.td ≤ D →
    ∀ a : Fin r → U, Sat A φ a ↔ tp k A a = τ

/-- A **`(Σ, Π)`-interpretation** (§3.6, p. 21): a defining formula `φ_R` for each relation
`R ∈ Π`. -/
structure Interp (σ π : Signature) where
  /-- the defining formula of each relation of `Π` -/
  defs : Fin π.length → Formula

namespace Interp

variable {σ π : Signature}

/-- `I` is **`k`-bounded** (§3.6, p. 21): `Σ` and `Π` have maximum arity at most `k`, and each
`φ_R` is a formula of `FO^k[Σ]` with `arity(R)` free variables. -/
def IsKBounded (k : ℕ) (I : Interp σ π) : Prop :=
  σ.maxarity ≤ k ∧ π.maxarity ≤ k ∧ ∀ R : Fin π.length, IsFOk σ k (π.get R) (I.defs R)

/-- The `Π`-structure `I(A)` (§3.6, p. 21): same universe, and `R(I(A)) = {ā | A ⊨ φ_R(ā)}`. -/
def apply {U : Type*} (I : Interp σ π) (A : Structure σ U) : Structure π U where
  rel R := {t | Sat A (I.defs R) t}

/-- The code of an interpretation: the codes of `φ_0, φ_1, …, φ_{|Π|−1}`, concatenated. -/
def code (I : Interp σ π) : List ℕ :=
  (List.ofFn fun R => (I.defs R).code).flatten

end Interp

end GlobalUpdatesFO.Upper


