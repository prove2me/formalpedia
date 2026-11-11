-- Prove2me | Definitions.Def_ApproxCountRwPHP_Unprovability_Translation
-- name    : ApproxCountRwPHP_Unprovability_Translation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:10.311011+00:00
-- url     : https://prove2.me/theorems/3f196ac6-61da-4346-a375-206cc4f05db9
-- title:
--   Parameterized finite principles and powers of two
-- statement:
--   Every original symbol acquires an initial size argument, including constants. Closure says that all constants and all function values on arguments below N remain below N. The finitary translation sends f(t̄) to its size-N slice and bounds every quantifier by N, preserving equality and Boolean connectives.
--
--   $$\Theta_\phi:=\forall N\ge1\ (\operatorname{Closed}(N)\to\exists\bar x<N\ \phi^{[N]}(\bar x)).$$
--
--   The powers-of-two variant substitutes N=2^{|u|} and quantifies over every string u. Neither closure nor the existence of a witness is built into the oracle language axioms. These are concrete first-order formulas, not arbitrary propositions supplied by a user.
--
--   Every numerical bound x<N includes canonical-numeral guards on x and N. Closure also requires canonical output numerals. Thus a slice has exactly N possible elements, with no additional elements arising from leading-zero strings. Theta restricts its size variable to positive canonical numerals; ThetaPow2 constructs a canonical size from an arbitrary string parameter.
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), §1.2.3, §3.2, §6.3, printed p. 6–7, 19, 40–41, PDF p. 8–9, 21, 42–43; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=8–9, 21, 42–43

import Definitions.Def_ApproxCountRwPHP_Unprovability_APX

namespace ApproxCountRwPHP.Unprovability

/-- Shift arithmetic terms past additional bound variables. -/
def liftArithmetic {S : Signature} {n : ℕ} (d : ℕ) (t : ArithTerm S n) : ArithTerm S (n + d) :=
  t.relabel (Sum.map id (Fin.castAdd d))

def allLast {S : Signature} {n : ℕ} : (d : ℕ) → ArithFormula S (n + d) → ArithFormula S n
  | 0, φ => φ
  | d + 1, φ => allLast d φ.all

def exLast {S : Signature} {n : ℕ} : (d : ℕ) → ArithFormula S (n + d) → ArithFormula S n
  | 0, φ => φ
  | d + 1, φ => exLast d φ.ex

def translateTerm {S : Signature} {n : ℕ} {α : Type}
    (size : ArithTerm (parameterizedSignature S) n)
    (assignment : α → ArithTerm (parameterizedSignature S) n) :
    S.language.Term α → ArithTerm (parameterizedSignature S) n
  | .var x => assignment x
  | .func ⟨s, hs⟩ ts =>
      native (@Native.query (parameterizedSignature S) s) (Fin.cons size (fun i => translateTerm size assignment (ts (Fin.cast hs i))))

/-- The finitary translation, including bounded quantifiers. -/
def translateFormula {S : Signature} : {k n : ℕ} →
    S.language.BoundedFormula Empty k → ArithTerm (parameterizedSignature S) n →
    (Fin k → ArithTerm (parameterizedSignature S) n) → ArithFormula (parameterizedSignature S) n
  | _, _, .falsum, _, _ => ⊥
  | _, _, .equal t u, size, xs =>
      (translateTerm size (Sum.elim Empty.elim xs) t).bdEqual
        (translateTerm size (Sum.elim Empty.elim xs) u)
  | _, _, .rel r _, _, _ => Empty.elim r
  | _, _, .imp φ ψ, size, xs => (translateFormula φ size xs).imp (translateFormula ψ size xs)
  | _, n, .all φ, size, xs =>
      let size' := liftArithmetic 1 size
      let xs' := Fin.snoc (fun i => liftArithmetic 1 (xs i)) (avar (Fin.last n))
      ((numericLess (avar (Fin.last n)) size').imp
        (translateFormula φ size' xs')).all

/-- Closure is a hypothesis on the slice, not an extra oracle axiom. -/
def closedSlice {S : Signature} {n : ℕ} (size : ArithTerm (parameterizedSignature S) n) :
    ArithFormula (parameterizedSignature S) n :=
  (List.ofFn (fun s : Fin S.count =>
    let d := S.arity s
    let size' := liftArithmetic d size
    let xs : Fin d → ArithTerm (parameterizedSignature S) (n+d) := fun i => avar (Fin.natAdd n i)
    let guard := (List.ofFn (fun i => numericLess (xs i) size')).foldr (· ⊓ ·) ⊤
    allLast d (guard.imp (numericLess (native (@Native.query (parameterizedSignature S) s) (Fin.cons size' xs)) size')))).foldr (· ⊓ ·) ⊤

def finiteWitness {S : Signature} {n k : ℕ} (φ : S.language.BoundedFormula Empty k)
    (size : ArithTerm (parameterizedSignature S) n) : ArithFormula (parameterizedSignature S) n :=
  let size' := liftArithmetic k size
  let xs : Fin k → ArithTerm (parameterizedSignature S) (n+k) := fun i => avar (Fin.natAdd n i)
  let guard := (List.ofFn (fun i => numericLess (xs i) size')).foldr (· ⊓ ·) ⊤
  exLast k (guard ⊓ translateFormula φ size' xs)

def Theta {S : Signature} {k : ℕ} (φ : S.language.BoundedFormula Empty k) : (LangLhat S).Sentence :=
  let size : ArithTerm (parameterizedSignature S) 1 := avar 0
  ((numeralTerm size ⊓ (holds (primitive .less ![size,aone])).not ⊓ closedSlice size).imp
    (finiteWitness φ size)).all

def ThetaPow2 {S : Signature} {k : ℕ} (φ : S.language.BoundedFormula Empty k) : (LangLhat S).Sentence :=
  let size : ArithTerm (parameterizedSignature S) 1 := primitive .pow2length ![avar 0]
  ((closedSlice size).imp (finiteWitness φ size)).all

end ApproxCountRwPHP.Unprovability


