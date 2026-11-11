-- Prove2me | Definitions.Def_ApproxCountRwPHP_Unprovability_Languages
-- name    : ApproxCountRwPHP_Unprovability_Languages
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:57:36.946255+00:00
-- url     : https://prove2.me/theorems/5c925b90-e284-46ff-ac6c-b8ecd7675394
-- title:
--   Relativized languages and universal base theories
-- statement:
--   The first-order language has a function symbol for every bounded program code and uses built-in equality. Primitive compression and decompression oracles satisfy
--
--   $$|f(u)|=|u|-1,\qquad |g(v)|=|v|+1,\qquad |P(C,\Delta)|\le |C|+2|\Delta|.$$
--
--   Subtraction is truncated at zero. A second language parameterizes every original symbol by a size argument and requires its output length to be at most that size argument's length. Parsing, input fixing, rational arithmetic, and evaluation of input-free circuits have fixed polynomial-time semantics.
--
--   The base theory consists of universal sentences true for every standard interpretation of arbitrary length-bounded oracles. This deliberately strengthens only the PV1 base. No counting-correctness restriction is imposed on P in defining this theory. The four counting axioms remain separate syntactic sentences.
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), §2.2, §3.2, printed p. 13–14, 18–19, PDF p. 15–16, 20–21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=15–16, 20–21

import Definitions.Def_ApproxCountRwPHP_Unprovability_Circuits
import Definitions.Def_ApproxCountRwPHP_Unprovability_Rationals

namespace ApproxCountRwPHP.Unprovability

/-! Oracle symbols and fixed polynomial-time circuit/rational operations.
The latter have their fixed standard semantics, rather than being additional
unconstrained oracles. They could instead be represented by Cobham codes.
Their parser scans an explicit circuit description, and circuit evaluation
uses only the primitive non-P oracles. No search over input assignments is
part of these operations. -/
inductive Native (S : Signature) : ℕ → Type
  | query (s : Fin S.count) : Native S (S.arity s)
  | count : Native S 2
  | isCircuit : Native S 1
  | noInputs : Native S 1
  | circuitVal : Native S 1
  | fix (b : Bool) : Native S 1
  | isRational : Native S 1
  | rationalAdd : Native S 2
  | rationalSub : Native S 2
  | rationalAbs : Native S 1
  | rationalHalf : Native S 1
  | rationalLE : Native S 2
  | inverseLength : Native S 1

def Native.eval {S : Signature}
    (oracle : ∀ s, (Fin (S.arity s) → BitString) → BitString)
    (P : BitString → BitString → BitString) :
    {n : ℕ} → Native S n → (Fin n → BitString) → BitString
  | _, .query s, xs => oracle s xs
  | _, .count, xs => P (xs 0) (xs 1)
  | _, .isCircuit, xs => truth (parseCircuit S (xs 0)).isSome
  | _, .noInputs, xs => truth (((parseCircuit S (xs 0)).map OracleCircuit.noInputs).getD false)
  | _, .circuitVal, xs => truth (((parseCircuit S (xs 0)).map (fun C => C.eval oracle [])).getD false)
  | _, .fix b, xs => ((parseCircuit S (xs 0)).map (fun C => (C.fix b).encode)).getD []
  | _, .isRational, xs => truth (decodeRational (xs 0)).isSome
  | _, .rationalAdd, xs => encodeRational (rationalValue (xs 0) + rationalValue (xs 1))
  | _, .rationalSub, xs => encodeRational (rationalValue (xs 0) - rationalValue (xs 1))
  | _, .rationalAbs, xs => encodeRational |rationalValue (xs 0)|
  | _, .rationalHalf, xs => encodeRational (rationalValue (xs 0) / 2)
  | _, .rationalLE, xs => truth (rationalValue (xs 0) ≤ rationalValue (xs 1))
  | _, .inverseLength, xs => encodeRational (1 / ((xs 0).length : ℚ))

def LanguageOver (S : Signature) : FirstOrder.Language where
  Functions n := CobhamCode (Native S) n
  Relations _ := Empty

@[instance_reducible]
def standardStructure {S : Signature}
    (oracle : ∀ s, (Fin (S.arity s) → BitString) → BitString)
    (P : BitString → BitString → BitString) : (LanguageOver S).Structure BitString where
  funMap := CobhamCode.eval (fun _ o xs => o.eval oracle P xs)
  RelMap := fun r => Empty.elim r

abbrev signatureFG : Signature := ⟨2, fun _ => 1⟩

abbrev LangFG := LanguageOver signatureFG

def interpretationFG (f g : BitString → BitString) :
    ∀ s : Fin signatureFG.count, (Fin (signatureFG.arity s) → BitString) → BitString :=
  fun s xs => if s.val = 0 then f (xs 0) else g (xs 0)

@[instance_reducible]
def Std (f g : BitString → BitString) (P : BitString → BitString → BitString) :
    LangFG.Structure BitString := standardStructure (interpretationFG f g) P

def lengthBoundsFG (f g : BitString → BitString) (P : BitString → BitString → BitString) : Prop :=
  (∀ u, (f u).length = u.length - 1) ∧
  (∀ v, (g v).length = v.length + 1) ∧
  (∀ C Δ, (P C Δ).length ≤ C.length + 2 * Δ.length)

/-- All universal base truths for arbitrary length-bounded P, without any
counting-correctness assumption on P. This is the base-theory generalization
allowed in the brief; the four counting axioms are added separately. -/
def baseFG : LangFG.Theory := {φ | φ.IsUniversal ∧
  ∀ f g P, lengthBoundsFG f g P → @FirstOrder.Language.Sentence.Realize _ _ (Std f g P) φ}

/-- Each primitive symbol acquires one size argument, including old constants. -/
abbrev parameterizedSignature (S : Signature) : Signature :=
  ⟨S.count, fun s => S.arity s + 1⟩

abbrev LangLhat (S : Signature) := LanguageOver (parameterizedSignature S)

def lengthBoundsLhat (S : Signature)
    (oracle : ∀ s, (Fin ((parameterizedSignature S).arity s) → BitString) → BitString)
    (P : BitString → BitString → BitString) : Prop :=
  (∀ s xs, (oracle s xs).length ≤ (xs 0).length) ∧
  (∀ C Δ, (P C Δ).length ≤ C.length + 2 * Δ.length)

def baseLhat (S : Signature) : (LangLhat S).Theory := {φ | φ.IsUniversal ∧
  ∀ oracle P, lengthBoundsLhat S oracle P →
    @FirstOrder.Language.Sentence.Realize _ _ (standardStructure oracle P) φ}

end ApproxCountRwPHP.Unprovability


