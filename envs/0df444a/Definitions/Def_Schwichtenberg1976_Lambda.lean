-- Prove2me | Definitions.Def_Schwichtenberg1976_Lambda
-- name    : Schwichtenberg1976_Lambda
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-30T01:50:57.350364+00:00
-- url     : https://prove2.me/theorems/1b8fdb07-70ed-450d-a3a9-1ff2a939563f
-- title:
--   Simply Typed λ-Calculus, Church Numerals, Combinators, and Extended Polynomials
-- statement:
--   Formalizes Schwichtenberg (1975/1976, pp. 113-114): simple types built from `0` (`Ty.zero`) with `ν = (0 → 0) → (0 → 0)` (`Ty.nu`), typed λ-terms, capture-avoiding substitution, α-equivalence, β-reduction (`ReducesTo`), β-normal forms, Church numerals `n̄ = λα. α^n`, explicit combinators for addition (`addComb`), multiplication (`mulComb`), constants (`constComb`), and zero-test conditional (`condComb`), multivariate polynomials (`IsPolynomial`), extended polynomials (`IsExtendedPolyInd`, `IsPiecewisePolynomial`), and the inductive grammar `IsType00Subterm` of normal subterms of type `0 → 0`.
-- source:
--   Helmut Schwichtenberg, 'Definierbare Funktionen im λ-Kalkül mit Typen', Archiv für mathematische Logik und Grundlagenforschung 17, 1975/1976, pp. 113-114 (doi:10.1007/BF02011242). pp. 113-114.

import Std

/-!
# Simply Typed λ-Calculus, Church Numerals, and Extended Polynomials (Schwichtenberg 1976)

Source: Helmut Schwichtenberg,
"Definierbare Funktionen im λ-Kalkül mit Typen",
*Archiv für mathematische Logik und Grundlagenforschung* 17, 1975/1976, pp. 113–114.

This module formalizes:
- Simple types (`Ty`) built from ground type `0` (`Ty.zero`) by `(σ → τ)` (`Ty.arr`),
  and the Church numeral type `ν := (0 → 0) → (0 → 0)` (`Ty.nu`, p. 113).
- Typed λ-terms (`Term`, `HasType`), capture-avoiding substitution (`substTerm`),
  α-equivalence (`AlphaEq`), β-reduction `t =| t'` (`ReducesTo`, clauses (i)–(v) on p. 113),
  β-normal forms (`IsBetaNormal`), and normal-form equality (`TermEq`, p. 113).
- Iterated function application `α^n := λx. α(...(α x)...)` (`iterApp`, `iterTerm`),
  Church numerals `n̄ := λα. α^n` (`churchNumeral`), and λ-definability of numerical
  functions `f : (Fin k → Nat) → Nat` (`DefinesFunction`, `IsLambdaDefinable`, p. 113).
- Explicit combinators for composition `t ∘ s`, addition `addComb`, multiplication `mulComb`,
  constant `constComb`, and zero-test conditional `condComb` (`d(n, m, i)`, p. 113).
- Polynomials (`IsPolynomial`), piecewise polynomials by vanishing/non-vanishing of arguments
  (`IsPiecewisePolynomial`, p. 114), and the inductive class of extended polynomials
  (`IsExtendedPolyInd`, pp. 113–114).
- Inductive grammar of normal subterms of type `0 → 0` (`IsType00Subterm`, clauses (1)–(3), p. 114).
-/

namespace Schwichtenberg1976

/-- Simple types over ground type `0` (p. 113):
`σ, τ ::= 0 | (σ → τ)`. -/
inductive Ty where
  | zero : Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq, Repr

namespace Ty

/-- Endomorphism type `0 → 0` (p. 113). -/
def endo : Ty := .arr .zero .zero

/-- Church numeral type `ν := (0 → 0) → (0 → 0)` (p. 113). -/
def nu : Ty := .arr endo endo

/-- Type `ν → (ν → ... (ν → ν)...)` with `k` arguments of type `ν` (p. 113). -/
def nuArity : Nat → Ty
  | 0 => nu
  | k + 1 => .arr nu (nuArity k)

end Ty

/-- Typed variable `x^τ` (p. 113). -/
structure Var where
  id : Nat
  ty : Ty
  deriving DecidableEq, Repr

/-- Typed λ-terms built from typed variables by application and λ-abstraction (p. 113). -/
inductive Term where
  | var : Var → Term
  | app : Term → Term → Term
  | lam : Var → Term → Term
  deriving DecidableEq, Repr

namespace Term

/-- Left-associated multi-argument application `t s₁ ... sₖ`. -/
def appMany : Term → List Term → Term
  | t, [] => t
  | t, s :: ss => appMany (.app t s) ss

/-- Multi-variable λ-abstraction `λx₁ ... xₖ. t`. -/
def lamMany : List Var → Term → Term
  | [], t => t
  | x :: xs, t => .lam x (lamMany xs t)

end Term

/-- Typing relation `HasType t τ` (`t^τ`, p. 113). -/
inductive HasType : Term → Ty → Prop where
  | var (x : Var) :
      HasType (.var x) x.ty
  | app {t s : Term} {σ τ : Ty} :
      HasType t (.arr σ τ) →
      HasType s σ →
      HasType (.app t s) τ
  | lam (x : Var) {t : Term} {τ : Ty} :
      HasType t τ →
      HasType (.lam x t) (.arr x.ty τ)

/-- Free variable occurrences of a term `t`. -/
def freeVarOccurrences : Term → List Var
  | .var x => [x]
  | .app t s => freeVarOccurrences t ++ freeVarOccurrences s
  | .lam x t => (freeVarOccurrences t).filter (· != x)

/-- Underlying set of free variables `FV(t)`. -/
def freeVars (t : Term) : List Var :=
  (freeVarOccurrences t).eraseDups

/-- All variables (both free and bound) occurring in `t`. -/
def allVars : Term → List Var
  | .var x => [x]
  | .app t s => allVars t ++ allVars s
  | .lam x t => x :: allVars t

/-- A term `t` is closed ("abgeschlossen", p. 113) if `FV(t) = ∅`. -/
def IsClosed (t : Term) : Prop :=
  freeVars t = []

/-- Maximum variable id occurring in `t`. -/
def maxVarId : Term → Nat
  | .var x => x.id
  | .app t s => Nat.max (maxVarId t) (maxVarId s)
  | .lam x t => Nat.max x.id (maxVarId t)

/-- Replace free occurrences of `x` with `y` in `t`. -/
def renameFreeVar (t : Term) (x y : Var) : Term :=
  match t with
  | .var v => if v == x then .var y else .var v
  | .app r s => .app (renameFreeVar r x y) (renameFreeVar s x y)
  | .lam v body =>
      if v == x then .lam v body else .lam v (renameFreeVar body x y)

/-- Structural size of `t` for termination of capture-avoiding substitution. -/
def rawSize : Term → Nat
  | .var _ => 1
  | .app t s => rawSize t + rawSize s + 1
  | .lam _ t => rawSize t + 1

theorem renameFreeVar_rawSize (t : Term) (x y : Var) :
    rawSize (renameFreeVar t x y) = rawSize t := by
  induction t with
  | var v => simp only [renameFreeVar]; split <;> rfl
  | app r s ihr ihs => simp [renameFreeVar, rawSize, ihr, ihs]
  | lam v body ih =>
      simp only [renameFreeVar]
      split
      · rfl
      · simp [rawSize, ih]

/-- Capture-avoiding substitution `t_x[s]` (p. 113). -/
def substTerm (t : Term) (x : Var) (s : Term) : Term :=
  match t with
  | .var v => if v == x then s else .var v
  | .app r u => .app (substTerm r x s) (substTerm u x s)
  | .lam v body =>
      if v == x then
        .lam v body
      else if v ∈ freeVarOccurrences s then
        let freshId := Nat.max (maxVarId body) (Nat.max (maxVarId s) x.id) + 1
        let v' : Var := ⟨freshId, v.ty⟩
        .lam v' (substTerm (renameFreeVar body v v') x s)
      else
        .lam v (substTerm body x s)
termination_by rawSize t
decreasing_by
  all_goals
    simp_wf
    simp [rawSize, renameFreeVar_rawSize]
    try omega

/-- Sequential substitution `t[s₁/x₁, ..., sₖ/xₖ]`. -/
def substMany : Term → List (Var × Term) → Term
  | t, [] => t
  | t, (x, s) :: rest => substMany (substTerm t x s) rest

/-- α-equivalence `AlphaEq t s` (p. 113: "Terme, die sich nur durch gebundene Umbenennung
unterscheiden, werden identifiziert."). -/
inductive AlphaEq : Term → Term → Prop where
  | refl (t : Term) : AlphaEq t t
  | symm {t s : Term} : AlphaEq t s → AlphaEq s t
  | trans {t s u : Term} : AlphaEq t s → AlphaEq s u → AlphaEq t u
  | app {t t' s s' : Term} :
      AlphaEq t t' → AlphaEq s s' → AlphaEq (.app t s) (.app t' s')
  | lam_rename (x y : Var) (t : Term) :
      x.ty = y.ty →
      (y = x ∨ y ∉ allVars t) →
      AlphaEq (.lam x t) (.lam y (renameFreeVar t x y))
  | lam_congr (x : Var) {t s : Term} :
      AlphaEq t s → AlphaEq (.lam x t) (.lam x s)

/-- Reduction relation `t =| t'` ("`t` ist reduzierbar auf `t'`", p. 113, clauses (i)–(v)):
- (i) `(λx t)s =| t_x[s]`
- (ii) `t =| t' ∧ s =| s' ⇒ t s =| t' s'`
- (iii) `t =| t' ⇒ λx t =| λx t'`
- (iv) `t =| t` (modulo bound variable renaming `AlphaEq`)
- (v) `t =| t' ∧ t' =| t'' ⇒ t =| t''`. -/
inductive ReducesTo : Term → Term → Prop where
  | beta (x : Var) (t s : Term) :
      ReducesTo (.app (.lam x t) s) (substTerm t x s)
  | app {t t' s s' : Term} :
      ReducesTo t t' → ReducesTo s s' → ReducesTo (.app t s) (.app t' s')
  | lam (x : Var) {t t' : Term} :
      ReducesTo t t' → ReducesTo (.lam x t) (.lam x t')
  | refl_alpha {t t' : Term} :
      AlphaEq t t' → ReducesTo t t'
  | trans {t t' t'' : Term} :
      ReducesTo t t' → ReducesTo t' t'' → ReducesTo t t''

/-- Predicate testing whether a term contains a β-redex `(λx t)s` as a subterm (p. 113). -/
def hasBetaRedex : Term → Bool
  | .var _ => false
  | .app (.lam _ _) _ => true
  | .app t s => hasBetaRedex t || hasBetaRedex s
  | .lam _ t => hasBetaRedex t

/-- Normal form predicate (p. 113: "Ein Term heißt in Normalform, wenn er keine Teilterme
der Gestalt `(λx t)s` besitzt."). -/
def IsBetaNormal (t : Term) : Prop :=
  hasBetaRedex t = false

/-- Subterm relation `IsSubterm s t` ("Teilterm", pp. 113–114). -/
inductive IsSubterm : Term → Term → Prop where
  | refl (t : Term) : IsSubterm t t
  | appLeft {s t u : Term} : IsSubterm s t → IsSubterm s (.app t u)
  | appRight {s t u : Term} : IsSubterm s u → IsSubterm s (.app t u)
  | lamBody {s t : Term} (x : Var) : IsSubterm s t → IsSubterm s (.lam x t)

/-- Term equality by common normal form (p. 113: "Zwei Terme heißen gleich, wenn sie dieselbe
Normalform besitzen."). -/
def TermEq (t s : Term) : Prop :=
  ∃ u v : Term,
    IsBetaNormal u ∧ IsBetaNormal v ∧
    ReducesTo t u ∧ ReducesTo s v ∧ AlphaEq u v

/-- `n`-fold application `α(α(...(α base)...))` (p. 113). -/
def iterApp (α base : Term) : Nat → Term
  | 0 => base
  | n + 1 => .app α (iterApp α base n)

/-- Iterated endomorphism `α^n := λx^0. α(...(α x)...)` (p. 113). -/
def iterTerm (α : Term) (xId : Nat := 0) (n : Nat) : Term :=
  let x : Var := ⟨xId, .zero⟩
  .lam x (iterApp α (.var x) n)

/-- Church numeral `n̄ := λα^{0→0}. α^n` of type `ν = (0 → 0) → (0 → 0)` (p. 113). -/
def churchNumeral (n : Nat) : Term :=
  let α : Var := ⟨1, Ty.endo⟩
  let x : Var := ⟨0, .zero⟩
  .lam α (.lam x (iterApp (.var α) (.var x) n))

/-- Endomorphism composition `t^{τ→τ} ∘ s^{τ→τ} := λx^τ. t(s x)` (p. 113). -/
def compTerm (τ : Ty) (t s : Term) (xId : Nat := 2) : Term :=
  let x : Var := ⟨xId, τ⟩
  .lam x (.app t (.app s (.var x)))

/-- Schwichtenberg's addition combinator `λF G α. (F α) ∘ (G α)` of type `ν → ν → ν` (p. 113). -/
def addComb : Term :=
  let F : Var := ⟨3, Ty.nu⟩
  let G : Var := ⟨4, Ty.nu⟩
  let α : Var := ⟨1, Ty.endo⟩
  .lam F (.lam G (.lam α (compTerm .zero (.app (.var F) (.var α)) (.app (.var G) (.var α)) 0)))

/-- Schwichtenberg's multiplication combinator `λF G. F ∘ G` of type `ν → ν → ν` (p. 113). -/
def mulComb : Term :=
  let F : Var := ⟨3, Ty.nu⟩
  let G : Var := ⟨4, Ty.nu⟩
  .lam F (.lam G (compTerm Ty.endo (.var F) (.var G) 1))

/-- Schwichtenberg's unary constant combinator `λF α. α^k` of type `ν → ν` (p. 113). -/
def constComb (k : Nat) : Term :=
  let F : Var := ⟨3, Ty.nu⟩
  let α : Var := ⟨1, Ty.endo⟩
  .lam F (.lam α (iterTerm (.var α) 0 k))

/-- Schwichtenberg's conditional combinator `λF G H α x. H (λy. G α x) (F α x)` of type
`ν → ν → ν → ν` defining `d(n, m, i) = n` if `i = 0` else `m` (p. 113). -/
def condComb : Term :=
  let F : Var := ⟨3, Ty.nu⟩
  let G : Var := ⟨4, Ty.nu⟩
  let H : Var := ⟨5, Ty.nu⟩
  let α : Var := ⟨1, Ty.endo⟩
  let x : Var := ⟨0, .zero⟩
  let y : Var := ⟨2, .zero⟩
  .lam F (.lam G (.lam H (.lam α (.lam x
    (.app
      (.app (.var H) (.lam y (.app (.app (.var G) (.var α)) (.var x))))
      (.app (.app (.var F) (.var α)) (.var x)))))))

/-- Numerical conditional `d(n, m, i) = n` if `i = 0`, and `m` if `i ≠ 0` (p. 113). -/
def condNat (n m i : Nat) : Nat :=
  if i == 0 then n else m

/-- Tuple of Church numerals `[n̄₁, ..., n̄ₖ]` for an input vector `v : Fin k → Nat`. -/
def numeralArgs : (k : Nat) → (Fin k → Nat) → List Term
  | 0, _ => []
  | k + 1, v =>
      churchNumeral (v ⟨0, Nat.zero_lt_succ k⟩) ::
        numeralArgs k (fun i => v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

/-- A closed term `t` of type `ν → ... → ν → ν` (`k` arguments) defines `f : (Fin k → Nat) → Nat`
if `t n̄₁ ... n̄ₖ` reduces to `f(n₁, ..., nₖ)̄` up to α-equivalence (p. 113). -/
def DefinesFunction (k : Nat) (t : Term) (f : (Fin k → Nat) → Nat) : Prop :=
  HasType t (Ty.nuArity k) ∧
  IsClosed t ∧
  ∀ v : Fin k → Nat,
    ReducesTo (Term.appMany t (numeralArgs k v)) (churchNumeral (f v))

/-- A function `f : (Fin k → Nat) → Nat` is λ-definable (`IsLambdaDefinable k f`, p. 113)
if there exists a closed term `t` of type `Ty.nuArity k` that defines `f`. -/
def IsLambdaDefinable (k : Nat) (f : (Fin k → Nat) → Nat) : Prop :=
  ∃ t : Term, DefinesFunction k t f

/-- Multivariate polynomials `P : (Fin k → Nat) → Nat` with natural number coefficients (p. 114). -/
inductive IsPolynomial : {k : Nat} → ((Fin k → Nat) → Nat) → Prop where
  | const {k : Nat} (c : Nat) :
      IsPolynomial (k := k) (fun _ => c)
  | proj {k : Nat} (i : Fin k) :
      IsPolynomial (k := k) (fun v => v i)
  | add {k : Nat} {P Q : (Fin k → Nat) → Nat} :
      IsPolynomial P → IsPolynomial Q →
      IsPolynomial (k := k) (fun v => P v + Q v)
  | mul {k : Nat} {P Q : (Fin k → Nat) → Nat} :
      IsPolynomial P → IsPolynomial Q →
      IsPolynomial (k := k) (fun v => P v * Q v)

/-- Inductive class of extended polynomials (`IsExtendedPolyInd`, pp. 113–114):
functions generated from constants, projections, addition, multiplication, zero-test
conditional `d(n, m, i)`, and composition. -/
inductive IsExtendedPolyInd : {k : Nat} → ((Fin k → Nat) → Nat) → Prop where
  | const {k : Nat} (c : Nat) :
      IsExtendedPolyInd (k := k) (fun _ => c)
  | proj {k : Nat} (i : Fin k) :
      IsExtendedPolyInd (k := k) (fun v => v i)
  | add {k : Nat} {f g : (Fin k → Nat) → Nat} :
      IsExtendedPolyInd f → IsExtendedPolyInd g →
      IsExtendedPolyInd (k := k) (fun v => f v + g v)
  | mul {k : Nat} {f g : (Fin k → Nat) → Nat} :
      IsExtendedPolyInd f → IsExtendedPolyInd g →
      IsExtendedPolyInd (k := k) (fun v => f v * g v)
  | cond {k : Nat} {f g h : (Fin k → Nat) → Nat} :
      IsExtendedPolyInd f → IsExtendedPolyInd g → IsExtendedPolyInd h →
      IsExtendedPolyInd (k := k) (fun v => condNat (f v) (g v) (h v))
  | comp {k m : Nat} {g : (Fin m → Nat) → Nat} {hs : Fin m → (Fin k → Nat) → Nat} :
      IsExtendedPolyInd g →
      (∀ j : Fin m, IsExtendedPolyInd (hs j)) →
      IsExtendedPolyInd (k := k) (fun v => g (fun j => hs j v))

/-- Pattern-wise polynomial characterization from the top of p. 114:
"alle Funktionen, die aus Polynomen durch Fallunterscheidung nach Verschwinden oder
Nicht-Verschwinden von Argumenten definierbar sind":
for every zero/nonzero pattern `σ : Fin k → Bool` of the arguments, there is a polynomial
`P_σ` such that `f(v) = P_σ(v)` whenever `(v i != 0) = σ i` for all `i`. -/
def IsPiecewisePolynomial (k : Nat) (f : (Fin k → Nat) → Nat) : Prop :=
  ∀ σ : Fin k → Bool,
    ∃ P : (Fin k → Nat) → Nat,
      IsPolynomial P ∧
      ∀ v : Fin k → Nat, (∀ i : Fin k, (v i != 0) = σ i) → f v = P v

mutual
  /-- Clause (1)–(2) basic subterms of type `0 → 0`: `α` or `Fᵢ s` (p. 114). -/
  inductive IsBasicType00 (Fs : List Var) (α : Var) : Term → Prop where
    | alpha :
        IsBasicType00 Fs α (.var α)
    | appF {F : Var} {s : Term} :
        F ∈ Fs →
        IsType00Subterm Fs α s →
        IsBasicType00 Fs α (.app (.var F) s)

  /-- Iterated application chain `s₁(...(s_q z)...)` of basic subterms `s₁, ..., s_q`
  to a variable `z` of type `0` (clause (3), p. 114). -/
  inductive IsBasicType00Chain (Fs : List Var) (α : Var) : Var → Term → Prop where
    | base (z : Var) :
        z.ty = .zero →
        IsBasicType00Chain Fs α z (.var z)
    | step {z : Var} {s₁ body : Term} :
        IsBasicType00 Fs α s₁ →
        IsBasicType00Chain Fs α z body →
        IsBasicType00Chain Fs α z (.app s₁ body)

  /-- Inductive characterization of the possible subterms of type `0 → 0` in the normal form
  of `t F₁ ... Fₖ α` (clauses (1)–(3) on p. 114):
  - (1) `α`
  - (2) With `s` also `Fᵢ s` (for `Fᵢ ∈ Fs`)
  - (3) With `s₁, ..., s_q` formed by (1), (2), also `λy^0. s₁(...(s_q z)...)`, where `z` has
    type `0` (and may be identical with `y`). -/
  inductive IsType00Subterm (Fs : List Var) (α : Var) : Term → Prop where
    | basic {s : Term} :
        IsBasicType00 Fs α s →
        IsType00Subterm Fs α s
    | chainLam (y z : Var) {body : Term} :
        y.ty = .zero →
        z.ty = .zero →
        IsBasicType00Chain Fs α z body →
        IsType00Subterm Fs α (.lam y body)
end

end Schwichtenberg1976


