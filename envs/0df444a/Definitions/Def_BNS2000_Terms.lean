-- Prove2me | Definitions.Def_BNS2000_Terms
-- name    : BNS2000_Terms
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-30T04:07:56.852376+00:00
-- url     : https://prove2.me/theorems/02e9f80a-7062-4b5e-ad64-3827cc010519
-- title:
--   Sections 4-5: Safe/Complete Variables, Affinability, the Term Systems RA and RS, and Register Evaluation NFEval
-- statement:
--   Formalizes Sections 4-5 of Bellantoni, Niggl, and Schwichtenberg (2000): safe and complete variable occurrences (`isSafeIn`, `isCompleteIn`), affinable occurrences (`IsAffinableIn`), the term systems `RA` (`IsRATerm`) and `RS` (`IsRSTerm`), ground `β_ι`-expansions (`BetaIotaExpandsTo`), and the stack-of-registers evaluation judgment `(t, n⃗) ↓^l_k v` (`NFEval`).
-- source:
--   Stephen Bellantoni, Karl-Heinz Niggl, and Helmut Schwichtenberg, 'Higher type recursion, ramification and polynomial time', Annals of Pure and Applied Logic 104, 2000, pp. 17-30 (doi:10.1016/S0168-0072(00)00006-3). Sections 4-5, pp. 21-26.

import Definitions.Def_BNS2000_Syntax

/-!
# RA-Terms, RS-Terms, Sharing, and Register-Machine Evaluation (Bellantoni–Niggl–Schwichtenberg 2000, Sections 3–5)

Source: Stephen Bellantoni, Karl-Heinz Niggl, and Helmut Schwichtenberg,
"Higher type recursion, ramification and polynomial time",
*Annals of Pure and Applied Logic* 104, 2000, pp. 17–30 (Sections 3–5, pp. 20–27 / preprint pp. 4–11).

This module formalizes:
- Section 3 (pp. 20–22):
  - Subterm paths (`SubtermPath`), `subtermAt`, and binder scope equivalence (`ScopeEquivalentIn`, p. 20).
  - Affinations of an incomplete variable `x` in `s` (`IsAffination`, p. 20) and affinable variables
    (`IsAffinable`, p. 20).
  - The property `(R)` (`SatisfiesR`: every complete subterm contains complete free variables only),
    the property `(A)` (`SatisfiesA`: for every subterm `λx. s` with `x` incomplete, `x` is affinable
    in a reduct of `s`), and the class of ramified affinable terms (`IsRATerm`, p. 20).
- Section 4 (pp. 22–26):
  - Ground-type `β_ι`-expansion (`BetaIotaExpandsTo`, Lemma 4.2, p. 22).
  - The sharing property `(S)` (`SatisfiesS`), safe-or-ground variable discipline (`AllVarsSafeOrGround`),
    `R`-free terms (`isRFree`), and the class of `RS`-terms (`IsRSTerm`, p. 23).
  - Numeral environments (`IsNumeralEnv`, p. 23) and the inductive register-machine normalization
    algorithm `nf(t; n⃗; x⃗)` (`NFEval`, Theorem 4.3, pp. 23–24).
- Section 5 (pp. 26–27):
  - Bellantoni–Cook safe recursion function algebra `B` (`BCFunc`, `evalBC`, p. 27) and
    representation of two-sorted numerical functions by closed `RA`-terms (`RADenotesTwoSorted`).
-/

namespace BNS2000

/-- Path to a subterm occurrence in a term `t`:
- `0` descends into the body of `λx. r`, `!r`, or `rκ`, or the function part `r` of `r s`.
- `1` descends into the argument part `s` of `r s`. -/
abbrev SubtermPath := List Nat

/-- Subterm at occurrence path `p` in `t`. -/
def subtermAt : Term → SubtermPath → Option Term
  | t, [] => some t
  | .lam _ r, 0 :: p => subtermAt r p
  | .app r _, 0 :: p => subtermAt r p
  | .app _ s, 1 :: p => subtermAt s p
  | .bang r, 0 :: p => subtermAt r p
  | .kappa r, 0 :: p => subtermAt r p
  | _, _ => none

/-- Reflexive subterm relation `IsSubterm u t`. -/
def IsSubterm (u t : Term) : Prop :=
  ∃ p : SubtermPath, subtermAt t p = some u

/-- Whether path `pref` is a prefix of path `p` (meaning `p` lies inside the subterm at `pref`). -/
def isPathPrefix : SubtermPath → SubtermPath → Bool
  | [], _ => true
  | _ :: _, [] => false
  | i :: pref, j :: p => (i == j) && isPathPrefix pref p

/-- Strict prefix of a path. -/
def isStrictPathPrefix (pref p : SubtermPath) : Bool :=
  isPathPrefix pref p && (pref != p)

/-- Whether variable `x` is free along path `p` from the root of `t` (no `λx` binder along `p`). -/
def isFreeAlongPath (x : Var) : Term → SubtermPath → Bool
  | _, [] => true
  | .lam y r, 0 :: p => (y != x) && isFreeAlongPath x r p
  | .app r _, 0 :: p => isFreeAlongPath x r p
  | .app _ s, 1 :: p => isFreeAlongPath x s p
  | .bang r, 0 :: p => isFreeAlongPath x r p
  | .kappa r, 0 :: p => isFreeAlongPath x r p
  | _, _ => false

/-- All occurrence paths of free occurrences of `x` in `t`. -/
def freeVarPaths (x : Var) : Term → List SubtermPath
  | .var y => if y == x then [[]] else []
  | .const _ => []
  | .lam y r =>
      if y == x then [] else (freeVarPaths x r).map (0 :: ·)
  | .app r s =>
      (freeVarPaths x r).map (0 :: ·) ++ (freeVarPaths x s).map (1 :: ·)
  | .bang r => (freeVarPaths x r).map (0 :: ·)
  | .kappa r => (freeVarPaths x r).map (0 :: ·)

/-- Section 3 (p. 20): Two subterm occurrences at paths `p₁, p₂` in `t` (with subterms `a₁, a₂`)
are *scope equivalent* in `t` if whenever `λy` (at a binder path `bpath` in `t`) binds a
variable `y` free in either `a₁` or `a₂`, and `bpath` encloses one of `p₁, p₂`, then both
`p₁` and `p₂` lie within the scope of that `λy`. -/
def ScopeEquivalentIn (t : Term) (p₁ p₂ : SubtermPath) : Prop :=
  ∃ a₁ a₂ : Term,
    subtermAt t p₁ = some a₁ ∧
    subtermAt t p₂ = some a₂ ∧
    ∀ (bpath : SubtermPath) (y : Var) (body : Term),
      subtermAt t bpath = some (.lam y body) →
      (y ∈ freeVars a₁ ∨ y ∈ freeVars a₂) →
      (isStrictPathPrefix bpath p₁ = true ↔ isStrictPathPrefix bpath p₂ = true)

/-- Section 3 (p. 20): An *affination* of an incomplete variable `x` in `s` is a ground-type
subterm `a^τ` with `FO(x, a) = 1` such that every free occurrence of `x` in `s` lies in an
occurrence of `a` in `s`, where the occurrences of `a` are scope equivalent in `s`. -/
def IsAffination (x : Var) (s a : Term) : Prop :=
  x.ty.isIncomplete = true ∧
  (∃ τ : Ty, HasType a τ ∧ τ.isGround = true) ∧
  freeOccCount x a = 1 ∧
  ∃ occPaths : List SubtermPath,
    occPaths ≠ [] ∧
    (∀ p ∈ occPaths, subtermAt s p = some a ∧ isFreeAlongPath x s p = true) ∧
    (∀ px ∈ freeVarPaths x s, ∃ p ∈ occPaths, isPathPrefix p px = true) ∧
    (∀ p₁ ∈ occPaths, ∀ p₂ ∈ occPaths, ScopeEquivalentIn s p₁ p₂)

/-- Section 3 (p. 20): An incomplete variable `x` is *affinable* in `s` if there is an
affination of `x` in `s` or `FO(x, s) ≤ 1`. -/
def IsAffinable (x : Var) (s : Term) : Prop :=
  freeOccCount x s ≤ 1 ∨ ∃ a : Term, IsAffination x s a

/-- Property `(R)` (Section 3, p. 20): every complete subterm of `r` contains complete
free variables only. -/
def SatisfiesR (r : Term) : Prop :=
  ∀ u : Term,
    IsSubterm u r →
    (inferTy u).isComplete = true →
    ∀ v ∈ freeVars u, v.ty.isComplete = true

/-- Property `(A)` (Section 3, p. 20): for every subterm `λx. s` of `r` with `x` incomplete,
the variable `x` is affinable in a reduct `s'` of `s` (`s →* s'`). -/
def SatisfiesA (r : Term) : Prop :=
  ∀ (x : Var) (s : Term),
    IsSubterm (.lam x s) r →
    x.ty.isIncomplete = true →
    ∃ s' : Term, ReducesTo s s' ∧ IsAffinable x s'

/-- Direct affinability (used in Lemma 4.2, p. 22): for every subterm `λx. s` of `t` with
`x` higher-type incomplete, `x` is affinable in `s` itself. -/
def SatisfiesDirectAffinability (t : Term) : Prop :=
  ∀ (x : Var) (s : Term),
    IsSubterm (.lam x s) t →
    x.ty.isHigherType = true →
    x.ty.isIncomplete = true →
    IsAffinable x s

/-- Section 3 (p. 20): A term `r` is an `RA`-term (`R` for ramified, `A` for affinable)
if it is well-typed and satisfies both `(R)` and `(A)`. -/
def IsRATerm (r : Term) : Prop :=
  (∃ τ : Ty, HasType r τ) ∧ SatisfiesR r ∧ SatisfiesA r

/-- Property that every higher-type incomplete bound variable `x` in `t` has at most one
free occurrence in its scope `s` (`FO(x, s) ≤ 1`, Lemma 4.2, p. 22). -/
def HasLinearHigherIncompleteBinders (t : Term) : Prop :=
  ∀ (x : Var) (s : Term),
    IsSubterm (.lam x s) t →
    x.ty.isHigherType = true →
    x.ty.isIncomplete = true →
    freeOccCount x s ≤ 1

/-- One-step ground-type `β_ι`-expansion `r[a/y^τ] ↦ (λy^τ. r) a` inside a context, where `τ`
is a ground type (Lemma 4.2, p. 22). -/
inductive BetaIotaExpandStep : Term → Term → Prop where
  | root (y : Var) (r a : Term) :
      y.ty.isGround = true →
      BetaIotaExpandStep (substTerm r y a) (.app (.lam y r) a)
  | lam (x : Var) {r r' : Term} :
      BetaIotaExpandStep r r' →
      BetaIotaExpandStep (.lam x r) (.lam x r')
  | appLeft {r r' s : Term} :
      BetaIotaExpandStep r r' →
      BetaIotaExpandStep (.app r s) (.app r' s)
  | appRight {r s s' : Term} :
      BetaIotaExpandStep s s' →
      BetaIotaExpandStep (.app r s) (.app r s')
  | bang {r r' : Term} :
      BetaIotaExpandStep r r' →
      BetaIotaExpandStep (.bang r) (.bang r')
  | kappa {r r' : Term} :
      BetaIotaExpandStep r r' →
      BetaIotaExpandStep (.kappa r) (.kappa r')

/-- Reflexive-transitive closure of ground-type `β_ι`-expansions (`t ↦^*_{β_ι} t'`, Lemma 4.2, p. 22). -/
inductive BetaIotaExpandsTo : Term → Term → Prop where
  | refl (t : Term) : BetaIotaExpandsTo t t
  | step {t u v : Term} :
      BetaIotaExpandStep t u →
      BetaIotaExpandsTo u v →
      BetaIotaExpandsTo t v

/-- Every variable occurring (free or bound) in `t` has safe or ground type (Lemma 4.1 & Section 4, p. 22). -/
def AllVarsSafeOrGround (t : Term) : Prop :=
  ∀ v ∈ allVars t, v.ty.isSafe = true ∨ v.ty.isGround = true

/-- Total number of occurrences (free or bound) of variable `x` in `t`. -/
def totalVarOccCount (x : Var) : Term → Nat
  | .var y => if y == x then 1 else 0
  | .const _ => 0
  | .lam y r => (if y == x then 1 else 0) + totalVarOccCount x r
  | .app r s => totalVarOccCount x r + totalVarOccCount x s
  | .bang r => totalVarOccCount x r
  | .kappa r => totalVarOccCount x r

/-- Property `(S)` (Section 4, p. 23): every higher-type variable occurs at most once in `t`
(each free higher-type variable has `FO(v, t) ≤ 1`, and for every subterm `λx. s` with `x`
higher-type, `FO(x, s) ≤ 1`). -/
def SatisfiesS (t : Term) : Prop :=
  (∀ v ∈ freeVars t, v.ty.isHigherType = true → freeOccCount v t ≤ 1) ∧
  (∀ (x : Var) (s : Term),
    IsSubterm (.lam x s) t →
    x.ty.isHigherType = true →
    freeOccCount x s ≤ 1)

/-- Section 4 (p. 23): An `RA`-term is an `RS`-term (`S` for sharing) if it has safe or
ground variables only, and `(S)` every higher-type variable occurs at most once. -/
def IsRSTerm (t : Term) : Prop :=
  IsRATerm t ∧ AllVarsSafeOrGround t ∧ SatisfiesS t

/-- Whether a term `t` is `R`-free (contains no recursor constant `R_σ`, Section 4, p. 24). -/
def isRFree : Term → Bool
  | .var _ => true
  | .const (.recursor _) => false
  | .const _ => true
  | .lam _ r => isRFree r
  | .app r s => isRFree r && isRFree s
  | .bang r => isRFree r
  | .kappa r => isRFree r

/-- An environment `n⃗; x⃗ := [(x₁, n₁), ..., (xₖ, nₖ)]` is a *numeral environment*
(Section 4, p. 23) if each `nᵢ` is a numeral of the same type as `xᵢ`. -/
def IsNumeralEnv (env : List (Var × Term)) : Prop :=
  (env.map Prod.fst).Nodup ∧
  ∀ p ∈ env, HasType p.2 p.1.ty ∧ isNumeral p.2 = true

/-- An environment `n⃗; x⃗` of closed ground-type `R`-free `RS`-terms (Theorem 4.5, p. 24). -/
def IsClosedGroundRFreeRSEnv (env : List (Var × Term)) : Prop :=
  (env.map Prod.fst).Nodup ∧
  ∀ p ∈ env,
    HasType p.2 p.1.ty ∧
    p.1.ty.isGround = true ∧
    IsClosed p.2 ∧
    isRFree p.2 = true ∧
    IsRSTerm p.2

/-- Maximum term length `max |nᵢ|` among terms in an environment `env`. -/
def maxEnvTermLength (env : List (Var × Term)) : Nat :=
  env.foldr (fun p acc => Nat.max (termLength p.2) acc) 0

/-- Sum of term lengths `∑ |nᵢ|` across an environment `env`. -/
def sumEnvTermLength (env : List (Var × Term)) : Nat :=
  env.foldr (fun p acc => termLength p.2 + acc) 0

/-- Apply `k` postfixed `κ` eliminations `t κ ... κ` (Section 4, p. 24). -/
def kappaRepeat : Nat → Term → Term
  | 0, t => t
  | k + 1, t => .kappa (kappaRepeat k t)

/-- Inductive operational specification of the register-machine algorithm `nf(t; n⃗; x⃗)`
for `R`-free `RS`-terms `t` of ground type (proof of Theorem 4.3, Section 4, p. 24),
recording `(steps, regs, maxLen)`:
- `zero`: `t = 0` outputs `0` in `2` steps, `1` register, max length `1`.
- `varKappa`: `t = xᵢ κ ... κ` (`k` times) with `(xᵢ, !^k m) ∈ env` outputs `m` in `k + 2` steps,
  using `min 2 (|t| + #n⃗)` registers, max length `max |t| |!^k m|`.
- `s1`: `t = s₁ r` computes `n := nf(r; n⃗; x⃗)` and forms `s₁ n` in `2 + s_r` steps.
- `bang`: `t = !r` computes `n := nf(r; n⃗; x⃗)` and forms `!n` in `2 + s_r` steps.
- `s0`: `t = s₀ r` computes `n := nf(r; n⃗; x⃗)` and outputs `0` if `n = 0` else `s₀ n` in `3 + s_r` steps.
- `pred`: `t = p r` computes `n := nf(r; n⃗; x⃗)` and outputs `n'` if `n = sᵢ n'` else `0` in `3 + s_r` steps.
- `bangKappa`: `t = ((!s)κ) r⃗` computes `nf(s r⃗; n⃗; x⃗)` in `4 + s` steps.
- `cases`: `t = c_σ t₁ t₂ t₃ t₄ r⃗` computes `n := nf(t₁; n⃗; x⃗)` and then `nf(tⱼ r⃗; n⃗; x⃗)` in `2 + s₁ + sⱼ` steps.
- `betaGround`: `t = (λx. s) r r⃗` with `FO(x, s) > 1` (and `x` ground) computes `n := nf(r; n⃗; x⃗)`
  and then `nf(s r⃗; n⃗, n; x⃗, x)` in `2 + s_r + s_{s r⃗}` steps.
- `betaLinear`: `t = (λx. s) r r⃗` with `FO(x, s) ≤ 1` computes `nf(s[r/x] r⃗; n⃗; x⃗)` in `1 + s'` steps. -/
inductive NFEval : Term → List (Var × Term) → Term → Nat → Nat → Nat → Prop where
  | zero (env : List (Var × Term)) :
      NFEval (.const .zero) env (.const .zero) 2 1 1
  | varKappa (x : Var) (k : Nat) (m : Term) (env : List (Var × Term)) :
      (x, bangRepeat k m) ∈ env →
      isNumeral m = true →
      NFEval
        (kappaRepeat k (.var x))
        env
        m
        (k + 2)
        (Nat.min 2 (termLength (kappaRepeat k (.var x)) + env.length))
        (Nat.max (termLength (kappaRepeat k (.var x))) (termLength (bangRepeat k m)))
  | s1 {r n : Term} {env : List (Var × Term)} {sr gr lr : Nat} :
      NFEval r env n sr gr lr →
      NFEval
        (.app (.const .s1) r)
        env
        (.app (.const .s1) n)
        (2 + sr)
        (1 + gr)
        (Nat.max lr (termLength (.app (.const .s1) n)))
  | bang {r n : Term} {env : List (Var × Term)} {sr gr lr : Nat} :
      NFEval r env n sr gr lr →
      NFEval
        (.bang r)
        env
        (.bang n)
        (2 + sr)
        (1 + gr)
        (Nat.max lr (termLength (.bang n)))
  | s0 {r n out : Term} {env : List (Var × Term)} {sr gr lr : Nat} :
      NFEval r env n sr gr lr →
      out = (if n == .const .zero then .const .zero else .app (.const .s0) n) →
      NFEval
        (.app (.const .s0) r)
        env
        out
        (3 + sr)
        (1 + gr)
        (Nat.max lr (termLength out))
  | pred {r n out : Term} {env : List (Var × Term)} {sr gr lr : Nat} :
      NFEval r env n sr gr lr →
      ((n = .const .zero ∧ out = .const .zero) ∨
       (n = .app (.const .s0) out) ∨
       (n = .app (.const .s1) out)) →
      NFEval
        (.app (.const .pred) r)
        env
        out
        (3 + sr)
        (1 + gr)
        (Nat.max lr (termLength out))
  | bangKappa {s out : Term} (rs : List Term) {env : List (Var × Term)} {st gt lt : Nat} :
      NFEval (Term.appMany s rs) env out st gt lt →
      NFEval
        (Term.appMany (.kappa (.bang s)) rs)
        env
        out
        (4 + st)
        gt
        (Nat.max (termLength (Term.appMany (.kappa (.bang s)) rs)) lt)
  | cases (σ : Ty) {t₁ t₂ t₃ t₄ n tj out : Term} (rs : List Term)
      {env : List (Var × Term)} {s₁ g₁ l₁ sj gj lj : Nat} :
      NFEval t₁ env n s₁ g₁ l₁ →
      ((n = .const .zero ∧ tj = t₂) ∨
       (∃ n', n = .app (.const .s0) n' ∧ tj = t₃) ∨
       (∃ n', n = .app (.const .s1) n' ∧ tj = t₄)) →
      NFEval (Term.appMany tj rs) env out sj gj lj →
      NFEval
        (Term.appMany (.app (.app (.app (.app (.const (.cases σ)) t₁) t₂) t₃) t₄) rs)
        env
        out
        (2 + s₁ + sj)
        (1 + Nat.max g₁ gj)
        (Nat.max l₁ lj)
  | betaGround (x : Var) {s r n out : Term} (rs : List Term)
      {env : List (Var × Term)} {sr gr lr ss gs ls : Nat} :
      freeOccCount x s > 1 →
      x.ty.isGround = true →
      NFEval r env n sr gr lr →
      NFEval (Term.appMany s rs) ((x, n) :: env) out ss gs ls →
      NFEval
        (Term.appMany (.app (.lam x s) r) rs)
        env
        out
        (2 + sr + ss)
        (1 + Nat.max gr gs)
        (Nat.max lr ls)
  | betaLinear (x : Var) {s r out : Term} (rs : List Term)
      {env : List (Var × Term)} {st gt lt : Nat} :
      freeOccCount x s ≤ 1 →
      NFEval (Term.appMany (substTerm s x r) rs) env out st gt lt →
      NFEval
        (Term.appMany (.app (.lam x s) r) rs)
        env
        out
        (1 + st)
        gt
        (Nat.max (termLength (Term.appMany (.app (.lam x s) r) rs)) lt)

/-- Univariate polynomial `p : Nat → Nat` with natural number coefficients. -/
inductive IsUnivariatePoly : (Nat → Nat) → Prop where
  | const (c : Nat) : IsUnivariatePoly (fun _ => c)
  | id : IsUnivariatePoly (fun m => m)
  | add {p q : Nat → Nat} : IsUnivariatePoly p → IsUnivariatePoly q → IsUnivariatePoly (fun m => p m + q m)
  | mul {p q : Nat → Nat} : IsUnivariatePoly p → IsUnivariatePoly q → IsUnivariatePoly (fun m => p m * q m)

/-- Bellantoni–Cook safe recursion function algebra `B` (Section 5, p. 27, citing [1]):
Every function `f(x⃗; y⃗)` has `m` normal inputs `x⃗` and `n` safe inputs `y⃗`. -/
inductive BCFunc : Nat → Nat → Type where
  | zero : BCFunc 0 0
  | s0 : BCFunc 0 1
  | s1 : BCFunc 0 1
  | pred : BCFunc 0 1
  | cases : BCFunc 0 4
  | projNormal {m n : Nat} (j : Fin m) : BCFunc m n
  | projSafe {m n : Nat} (j : Fin n) : BCFunc m n
  | safeComp {m n m' n' : Nat} :
      BCFunc m' n' →
      (Fin m' → BCFunc m 0) →
      (Fin n' → BCFunc m n) →
      BCFunc m n
  | safeRec {m n : Nat} :
      BCFunc m n →
      BCFunc (m + 1) (n + 1) →
      BCFunc (m + 1) (n + 1) →
      BCFunc (m + 1) n

/-- Standard numerical semantics `evalBC f x⃗ y⃗` of a Bellantoni–Cook function `f : BCFunc m n` (p. 27). -/
def evalBC : {m n : Nat} → BCFunc m n → (Fin m → Nat) → (Fin n → Nat) → Nat
  | 0, 0, .zero, _, _ => 0
  | 0, 1, .s0, _, ys => 2 * ys ⟨0, by decide⟩
  | 0, 1, .s1, _, ys => 2 * ys ⟨0, by decide⟩ + 1
  | 0, 1, .pred, _, ys => ys ⟨0, by decide⟩ / 2
  | 0, 4, .cases, _, ys =>
      let y0 := ys ⟨0, by decide⟩
      let y1 := ys ⟨1, by decide⟩
      let y2 := ys ⟨2, by decide⟩
      let y3 := ys ⟨3, by decide⟩
      if y0 == 0 then y1 else if y0 % 2 == 0 then y2 else y3
  | _, _, .projNormal j, xs, _ => xs j
  | _, _, .projSafe j, _, ys => ys j
  | _, _, .safeComp g gs hs, xs, ys =>
      evalBC g (fun i => evalBC (gs i) xs Fin.elim0) (fun j => evalBC (hs j) xs ys)
  | _, _, .safeRec g h0 h1, xs, ys =>
      let x0 := xs ⟨0, by omega⟩
      let xsTail : Fin _ → Nat := fun i => xs ⟨i.val + 1, by omega⟩
      recNat
        (evalBC g xsTail ys)
        (fun cur prev =>
          let half := cur / 2
          let xsRec : Fin _ → Nat := fun i =>
            if _h0 : i.val = 0 then half else xsTail ⟨i.val - 1, by omega⟩
          let ysRec : Fin _ → Nat := fun j =>
            if hj : j.val < _ then ys ⟨j.val, hj⟩ else prev
          if cur % 2 == 0 then evalBC h0 xsRec ysRec else evalBC h1 xsRec ysRec)
        x0

/-- A closed `RA`-term `t` of type `!ι → ... → !ι → ι → ... → ι → ι` (`m` normal inputs of type `!ι`
and `n` safe inputs of type `ι`) denotes a numerical function `f : (Fin m → Nat) → (Fin n → Nat) → Nat`
if for all `xs : Fin m → Nat` and `ys : Fin n → Nat`, applying `t` to `!(binaryNumeralOfNat (xs i))`
and `binaryNumeralOfNat (ys j)` reduces to `binaryNumeralOfNat (f xs ys)` (Section 5, pp. 26–27). -/
def RADenotesTwoSorted {m n : Nat} (t : Term) (f : (Fin m → Nat) → (Fin n → Nat) → Nat) : Prop :=
  let domTys := List.replicate m (.bang .iota) ++ List.replicate n .iota
  IsRATerm t ∧
  IsClosed t ∧
  HasType t (Ty.arrMany domTys .iota) ∧
  ∀ (xs : Fin m → Nat) (ys : Fin n → Nat),
    let normArgs := (List.finRange m).map (fun i => .bang (binaryNumeralOfNat (xs i)))
    let safeArgs := (List.finRange n).map (fun j => binaryNumeralOfNat (ys j))
    IsNormalFormOf
      (Term.appMany t (normArgs ++ safeArgs))
      (binaryNumeralOfNat (f xs ys))

end BNS2000


