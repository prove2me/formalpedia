-- Prove2me | Definitions.Def_BergerSchwichtenberg1991_Syntax
-- name    : BergerSchwichtenberg1991_Syntax
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-30T01:55:03.530059+00:00
-- url     : https://prove2.me/theorems/77bba890-32b5-4485-a94a-120c9b3361e3
-- title:
--   Sections 1-2: Simply Typed λ-Calculus, Long β-Normal Forms, and Bound-Variable Standardization (`EMB`/`EXTRACT`)
-- statement:
--   Formalizes Sections 1 and 2 of Berger and Schwichtenberg (LICS 1991): simple types over ground type `o`, typed variables (named and `{0,1}*`-indexed), capture-avoiding simultaneous substitution, α-equivalence, βη-equality, long β-normal and neutral forms (`IsLongBetaNormal`, `IsLongBetaNeutral`), the bound-variable standardization family `EMB r k = α_k(r)`, and the canonical extraction operator `EXTRACT`.
-- source:
--   Ulrich Berger and Helmut Schwichtenberg, 'An inverse of the evaluation functional for typed λ-calculus', Proceedings of the Sixth Annual IEEE Symposium on Logic in Computer Science (LICS 1991), pp. 203-211 (doi:10.1109/LICS.1991.151645). Sections 1-2, pp. 203-205.

import Std

/-!
# Syntax, Long β-Normal Forms, and α-Standardization (Berger–Schwichtenberg 1991, Sections 1–2)

Source: Ulrich Berger and Helmut Schwichtenberg,
"An inverse of the evaluation functional for typed λ-calculus",
*Proceedings of the Sixth Annual IEEE Symposium on Logic in Computer Science (LICS 1991)*,
pp. 203–211, Sections 1–2 (pp. 204–205).

This module formalizes:
- Simple types (`Ty`) built from ground type `o` (`Ty.base`) by `→` (`Ty.arr`).
- Binary indices `k, l ∈ {0,1}*` (`Index`), indexed variables `x_k^ρ`, and general typed
  variables (`Var`).
- Concrete typed λ-terms (`Term`), typing (`HasType`), capture-avoiding substitution (`substTerm`),
  α-conversion (`AlphaEq`), βη-equality (`BetaEtaEq`), and long β-normal forms (`IsLongBetaNormal`,
  `IsLongBetaNeutral`).
- The bound-variable standardization mapping `α_k(r)` (`alphaRename`, p. 204), the term-family
  embedding `EMB : Λ → Λ^{{0,1}*}` (`EMB`, p. 204), and the extraction functional
  `EXTRACT : Λ^{{0,1}*} → Λ` (`EXTRACT`, pp. 204–205).
-/

namespace BergerSchwichtenberg1991

/-- Simple types built from a single ground type `o` by `→` (Section 1, p. 204):
`ρ, σ ::= o | ρ → σ`. -/
inductive Ty where
  | base : Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq, Repr

namespace Ty

/-- Iterated function type `σ₁ → ⋯ → σₖ → τ` associated to the right (p. 204). -/
def arrMany : List Ty → Ty → Ty
  | [], τ => τ
  | σ :: σs, τ => .arr σ (arrMany σs τ)

/-- Argument types `[σ₁, ..., σₖ]` of a type `ρ = σ₁ → ⋯ → σₖ → o`. -/
def argTypes : Ty → List Ty
  | .base => []
  | .arr σ τ => σ :: argTypes τ

end Ty

/-- Finite 0–1 sequence `k ∈ {0, 1}*` used as a binding position index (Section 2, p. 204). -/
abbrev Index := List Bool

/-- The empty 0–1 sequence `ε` (p. 205). -/
def epsIdx : Index := []

/-- The singleton sequence `0` (p. 205). -/
def zeroIdx : Index := [false]

/-- The singleton sequence `1` (p. 204). -/
def oneIdx : Index := [true]

/-- Concatenation `k * l` of 0–1 sequences (p. 204). -/
def appendIdx (k l : Index) : Index := k ++ l

/-- `IsPrefixOf k m` holds if `m = k * l` for some `l ∈ {0, 1}*` ("`m` extends `k`", p. 204). -/
def IsPrefixOf (k m : Index) : Prop :=
  ∃ l : Index, m = k ++ l

/-- Variable identifier: either an indexed variable `x_k` (`k ∈ {0,1}*`, Section 2, p. 204)
or an ordinary named variable `y_n` (`n : Nat`). -/
inductive VarName where
  | indexed : Index → VarName
  | named : Nat → VarName
  deriving DecidableEq, Repr

/-- Typed variable `x^ρ` (Section 1, p. 204). -/
structure Var where
  name : VarName
  ty : Ty
  deriving DecidableEq, Repr

/-- Indexed variable `x_k^ρ` of type `ρ` with index `k ∈ {0, 1}*` (Section 2, p. 204). -/
def indexedVar (ρ : Ty) (k : Index) : Var :=
  ⟨.indexed k, ρ⟩

/-- Concrete typed λ-terms (Section 1, p. 204):
constructed from typed variables `x^ρ` by application `(t^{ρ→σ} r^ρ)^σ` and abstraction
`(λx^ρ. s^σ)^{ρ→σ}`. -/
inductive Term where
  | var : Var → Term
  | app : Term → Term → Term
  | lam : Var → Term → Term
  deriving DecidableEq, Repr

namespace Term

/-- Left-associated iterated application `r s₁ ... sₖ` (Section 1, p. 204). -/
def appMany : Term → List Term → Term
  | r, [] => r
  | r, s :: ss => appMany (.app r s) ss

/-- Iterated lambda abstraction `λx₁ ... xₙ. r`. -/
def lamMany : List Var → Term → Term
  | [], r => r
  | x :: xs, r => .lam x (lamMany xs r)

end Term

/-- Typing relation `r ∈ Λ^ρ` (`HasType r ρ`, Section 1, p. 204). -/
inductive HasType : Term → Ty → Prop where
  | var (x : Var) :
      HasType (.var x) x.ty
  | app {t r : Term} {ρ σ : Ty} :
      HasType t (.arr ρ σ) →
      HasType r ρ →
      HasType (.app t r) σ
  | lam (x : Var) {s : Term} {σ : Ty} :
      HasType s σ →
      HasType (.lam x s) (.arr x.ty σ)

/-- Free variable occurrences of a term `r`. -/
def freeVarOccurrences : Term → List Var
  | .var x => [x]
  | .app r s => freeVarOccurrences r ++ freeVarOccurrences s
  | .lam x r => (freeVarOccurrences r).filter (· != x)

/-- Set of free variables `FV(r)` (duplicate-free list). -/
def freeVars (r : Term) : List Var :=
  (freeVarOccurrences r).eraseDups

/-- A term `r` is closed if `FV(r) = ∅`. -/
def IsClosed (r : Term) : Prop :=
  freeVars r = []

/-- List of indices `l ∈ {0, 1}*` such that `x_l^σ` occurs free in `r` for some `σ`
(Section 2, p. 204: `{l ∈ {0,1}* | x_l free in r}`). -/
def freeIndices (r : Term) : List Index :=
  (freeVars r).filterMap (fun v =>
    match v.name with
    | .indexed l => some l
    | .named _ => none)

/-- All variables (both free and bound) occurring in `r`. -/
def allVars : Term → List Var
  | .var x => [x]
  | .app r s => allVars r ++ allVars s
  | .lam x r => x :: allVars r

/-- Maximum named-variable id occurring anywhere in `r`. -/
def maxNamedId : Term → Nat
  | .var ⟨.named n, _⟩ => n
  | .var ⟨.indexed _, _⟩ => 0
  | .app r s => Nat.max (maxNamedId r) (maxNamedId s)
  | .lam ⟨.named n, _⟩ r => Nat.max n (maxNamedId r)
  | .lam ⟨.indexed _, _⟩ r => maxNamedId r

/-- Maximum named-variable id across a list of terms. -/
def maxNamedIdList : List Term → Nat
  | [] => 0
  | t :: ts => Nat.max (maxNamedId t) (maxNamedIdList ts)

/-- Replace free occurrences of variable `x` with variable `y` in `r`. -/
def renameFreeVar (r : Term) (x y : Var) : Term :=
  match r with
  | .var v => if v == x then .var y else .var v
  | .app t s => .app (renameFreeVar t x y) (renameFreeVar s x y)
  | .lam v body =>
      if v == x then .lam v body else .lam v (renameFreeVar body x y)

/-- Structural size of a raw term `r`. -/
def rawSize : Term → Nat
  | .var _ => 1
  | .app r s => rawSize r + rawSize s + 1
  | .lam _ r => rawSize r + 1

theorem renameFreeVar_rawSize (r : Term) (x y : Var) :
    rawSize (renameFreeVar r x y) = rawSize r := by
  induction r with
  | var v => simp only [renameFreeVar]; split <;> rfl
  | app t s iht ihs => simp [renameFreeVar, rawSize, iht, ihs]
  | lam v body ih =>
      simp only [renameFreeVar]
      split
      · rfl
      · simp [rawSize, ih]

/-- Capture-avoiding substitution `r[s/x]` (Section 2, p. 204). -/
def substTerm (r : Term) (x : Var) (s : Term) : Term :=
  match r with
  | .var v => if v == x then s else .var v
  | .app t u => .app (substTerm t x s) (substTerm u x s)
  | .lam v body =>
      if v == x then
        .lam v body
      else if v ∈ freeVarOccurrences s then
        let freshId := Nat.max (maxNamedId body) (Nat.max (maxNamedId s) (maxNamedId (.var x))) + 1
        let v' : Var := ⟨.named freshId, v.ty⟩
        .lam v' (substTerm (renameFreeVar body v v') x s)
      else
        .lam v (substTerm body x s)
termination_by rawSize r
decreasing_by
  all_goals
    simp_wf
    simp [rawSize, renameFreeVar_rawSize]
    try omega

/-- Type-respecting simultaneous substitution `θ : Var → Term` (Section 3, p. 205 & Section 4, p. 207). -/
abbrev Substitution := Var → Term

/-- A substitution `θ` is well-typed (`IsWellTypedSubst θ`) if `θ(x^ρ) ∈ Λ^ρ` for every variable `x^ρ`. -/
def IsWellTypedSubst (θ : Substitution) : Prop :=
  ∀ x : Var, HasType (θ x) x.ty

/-- Identity substitution `θ_id(x) = x` (Section 4, p. 208). -/
def idSubst : Substitution := fun x => .var x

/-- Update a substitution `θ[x ↦ t]` (Section 4, p. 207). -/
def updateSubst (θ : Substitution) (x : Var) (t : Term) : Substitution :=
  fun y => if y == x then t else θ y

/-- Apply a simultaneous substitution `rθ` (with capture avoidance via fresh named variables). -/
def applySubst (θ : Substitution) (r : Term) : Term :=
  match r with
  | .var x => θ x
  | .app t u => .app (applySubst θ t) (applySubst θ u)
  | .lam v body =>
      let fvBody := (freeVars body).filter (· != v)
      let imgTerms := fvBody.map θ
      let imgFVs := imgTerms.foldr (fun t acc => freeVarOccurrences t ++ acc) []
      if v ∈ imgFVs then
        let freshId :=
          Nat.max (maxNamedId body)
            (Nat.max (maxNamedId (.var v)) (maxNamedIdList imgTerms)) + 1
        let v' : Var := ⟨.named freshId, v.ty⟩
        .lam v' (applySubst (updateSubst θ v (.var v')) body)
      else
        .lam v (applySubst (updateSubst θ v (.var v)) body)
termination_by rawSize r
decreasing_by
  all_goals
    simp_wf
    simp [rawSize]
    try omega

/-- α-equivalence `r =_α s` (Section 2, p. 204: terms interconvertible by bound variable renaming). -/
inductive AlphaEq : Term → Term → Prop where
  | refl (r : Term) : AlphaEq r r
  | symm {r s : Term} : AlphaEq r s → AlphaEq s r
  | trans {r s t : Term} : AlphaEq r s → AlphaEq s t → AlphaEq r t
  | app {r r' s s' : Term} :
      AlphaEq r r' → AlphaEq s s' → AlphaEq (.app r s) (.app r' s')
  | lam_rename (x y : Var) (r : Term) :
      x.ty = y.ty →
      (y = x ∨ y ∉ allVars r) →
      AlphaEq (.lam x r) (.lam y (renameFreeVar r x y))
  | lam_congr (x : Var) {r s : Term} :
      AlphaEq r s → AlphaEq (.lam x r) (.lam x s)

/-- Provable equality `r =_{βη} s` in the typed βη-calculus (Sections 1–2, pp. 203–204). -/
inductive BetaEtaEq : Term → Term → Prop where
  | of_alpha {r s : Term} : AlphaEq r s → BetaEtaEq r s
  | refl (r : Term) : BetaEtaEq r r
  | symm {r s : Term} : BetaEtaEq r s → BetaEtaEq s r
  | trans {r s t : Term} : BetaEtaEq r s → BetaEtaEq s t → BetaEtaEq r t
  | app {r r' s s' : Term} :
      BetaEtaEq r r' → BetaEtaEq s s' → BetaEtaEq (.app r s) (.app r' s')
  | lam (x : Var) {r s : Term} :
      BetaEtaEq r s → BetaEtaEq (.lam x r) (.lam x s)
  | beta (x : Var) (r s : Term) :
      BetaEtaEq (.app (.lam x r) s) (substTerm r x s)
  | eta (x : Var) (r : Term) :
      x ∉ freeVars r →
      BetaEtaEq (.lam x (.app r (.var x))) r

mutual
  /-- Long β-normal forms (Section 2, p. 204):
  `λx₁^{ρ₁} ... λxₙ^{ρₙ}. y^{σ₁ → ⋯ → σₖ → o} s₁^{σ₁} ... sₖ^{σₖ}` with `s₁, ..., sₖ` in
  long β-normal form and body `y s₁ ... sₖ` of ground type `o`. -/
  inductive IsLongBetaNormal : Ty → Term → Prop where
    | baseNeutral {t : Term} :
        IsLongBetaNeutral .base t →
        IsLongBetaNormal .base t
    | lam (x : Var) {σ : Ty} {r : Term} :
        IsLongBetaNormal σ r →
        IsLongBetaNormal (.arr x.ty σ) (.lam x r)

  /-- Neutral spine `y s₁ ... sₖ` whose arguments are in long β-normal form. -/
  inductive IsLongBetaNeutral : Ty → Term → Prop where
    | var (y : Var) :
        IsLongBetaNeutral y.ty (.var y)
    | app {t s : Term} {σ τ : Ty} :
        IsLongBetaNeutral (.arr σ τ) t →
        IsLongBetaNormal σ s →
        IsLongBetaNeutral τ (.app t s)
end

/-- Section 2 (p. 204): Bound-variable renaming functional `α_k(r)` for `k ∈ {0, 1}*`:
- `α_k(x) = x`
- `α_k(r s) = (α_{k * 0} r)(α_{k * 1} s)`
- `α_k(λy^ρ. r) = λx_k^ρ. (α_{k * 0} r)[x_k^ρ / y^ρ]` (standardizing inner bound variables
  to indices extending `k * 0` first so that renaming `y^ρ ↦ x_k^ρ` is capture-free). -/
def alphaRename (k : Index) (r : Term) : Term :=
  match r with
  | .var x => .var x
  | .app t s =>
      .app (alphaRename (appendIdx k zeroIdx) t) (alphaRename (appendIdx k oneIdx) s)
  | .lam y body =>
      let xk := indexedVar y.ty k
      let yFresh : Var := ⟨.named (maxNamedId body + 1), y.ty⟩
      let body' := alphaRename (appendIdx k zeroIdx) (renameFreeVar body y yFresh)
      .lam xk (renameFreeVar body' yFresh xk)
termination_by rawSize r
decreasing_by
  all_goals
    simp_wf
    simp [rawSize, renameFreeVar_rawSize]
    try omega

/-- Section 2 (p. 204): Term family representation `EMB : Λ → (Index → Λ)` defined by
`EMB r k := α_k(r)`. -/
def EMB (r : Term) (k : Index) : Term :=
  alphaRename k r

/-- Maximum length among a list of 0–1 sequences. -/
def maxIdxLength : List Index → Nat
  | [] => 0
  | l :: ls => Nat.max l.length (maxIdxLength ls)

/-- Canonical fresh index `k̂(F) ∈ {0, 1}*` computed from `F(ε)` and `F(0)` (pp. 204–205):
a sequence of `0`s strictly longer than every index occurring in `F(ε)` or `F(0)`, so that
no index in `{l ∈ {0,1}* | x_l free in r}` extends `k̂`. -/
def canonicalFreshIndex (F : Index → Term) : Index :=
  let len := Nat.max (maxIdxLength (freeIndices (F epsIdx)))
                     (maxIdxLength (freeIndices (F zeroIdx))) + 1
  List.replicate len false

/-- Section 2 (p. 205): Extraction functional `EXTRACT : Λ^{{0,1}*} → Λ` defined by
`EXTRACT(F) := F(k̂)`. -/
def EXTRACT (F : Index → Term) : Term :=
  F (canonicalFreshIndex F)

end BergerSchwichtenberg1991


