-- Prove2me | Definitions.Def_ApproxPolySatCH_Main_Supplement_ExistentialReals
-- name    : ApproxPolySatCH_Main_Supplement_ExistentialReals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:54:19.354386+00:00
-- url     : https://prove2.me/theorems/72b2b0fd-2f30-4654-9f56-30a407a3233a
-- title:
--   Finite existential real syntax, binary encodings and the ETR language
-- statement:
--   A real term is a finite expression built from $0$, $1$, indexed variables, addition and multiplication. A quantifier-free real formula uses equality and strict-order atoms and the Boolean connectives negation, conjunction and disjunction. An existential sentence binds all $n$ of its variables, including when $n=0$. Terms are evaluated by ordinary real arithmetic and formulas by ordinary Boolean semantics, so
--   $$\operatorname{True}(n,\varphi)\iff\exists x\in\mathbb R^n\;\varphi(x).$$
--   Each natural number is encoded by the published self-delimiting binary natural code. Each syntax constructor has a distinct natural-number tag; a variable writes its index, and recursive children are framed by their binary bit length. A sentence writes its variable count and framed formula body. The decision language is
--   $$\mathrm{ETR}=\{\operatorname{encode}(n,\varphi):\exists x\in\mathbb R^n\;\varphi(x)\}.$$
--   Only well-scoped syntax can be encoded; invalid binary words are no instances. The signature has no arbitrary real literals, exponentiation operation, circuit-evaluation oracle or truth oracle.
--
--   This is the existential theory of real closed fields interpreted in the reals, as in the source. Existential gate variables and local gate equations permit sharing of arithmetic computations without expanding polynomial expressions into trees. Binary integer and rational data must be represented through these equations rather than added as privileged literals.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), §6, ETR definition and Theorem 16, p.27–28 (PDF p.27–28), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=27

import Definitions.Def_ApproxPolySatCH_Main_Inputs

set_option autoImplicit false

namespace ApproxPolySatCH.Main.Supplement

/-- Finite terms in the source signature, with no arbitrary real literals. -/
inductive RealTerm (n : ℕ) where
  | zero
  | one
  | var (i : Fin n)
  | add (a b : RealTerm n)
  | mul (a b : RealTerm n)

def RealTerm.eval {n : ℕ} (x : Fin n → ℝ) : RealTerm n → ℝ
  | .zero => 0
  | .one => 1
  | .var i => x i
  | .add a b => a.eval x + b.eval x
  | .mul a b => a.eval x * b.eval x

/-- Equality and strict order, with a functionally complete set of Boolean connectives. -/
inductive RealFormula (n : ℕ) where
  | equal (a b : RealTerm n)
  | less (a b : RealTerm n)
  | neg (a : RealFormula n)
  | conj (a b : RealFormula n)
  | disj (a b : RealFormula n)

def RealFormula.Holds {n : ℕ} (x : Fin n → ℝ) : RealFormula n → Prop
  | .equal a b => a.eval x = b.eval x
  | .less a b => a.eval x < b.eval x
  | .neg a => ¬ a.Holds x
  | .conj a b => a.Holds x ∧ b.Holds x
  | .disj a b => a.Holds x ∨ b.Holds x

/-- All variables in the body are bound by this single existential block. -/
structure RealSentence where
  numVars : ℕ
  body : RealFormula numVars

def RealSentence.True (s : RealSentence) : Prop :=
  ∃ x : Fin s.numVars → ℝ, s.body.Holds x

/-- A self-delimiting binary length followed by exactly that many bits. -/
def frame (w : Word) : Word := encodeNat w.length ++ w

/-- Constructor tags and each recursive child's binary length are explicitly written. -/
def RealTerm.encode {n : ℕ} : RealTerm n → Word
  | .zero => encodeNat 0
  | .one => encodeNat 1
  | .var i => encodeNat 2 ++ encodeNat i.val
  | .add a b => encodeNat 3 ++ frame a.encode ++ frame b.encode
  | .mul a b => encodeNat 4 ++ frame a.encode ++ frame b.encode

def RealFormula.encode {n : ℕ} : RealFormula n → Word
  | .equal a b => encodeNat 0 ++ frame a.encode ++ frame b.encode
  | .less a b => encodeNat 1 ++ frame a.encode ++ frame b.encode
  | .neg a => encodeNat 2 ++ frame a.encode
  | .conj a b => encodeNat 3 ++ frame a.encode ++ frame b.encode
  | .disj a b => encodeNat 4 ++ frame a.encode ++ frame b.encode

def RealSentence.encode (s : RealSentence) : Word :=
  encodeNat s.numVars ++ frame s.body.encode

/-- Invalid binary words are outside the language; truth is ordinary real evaluation. -/
def ETRLanguage : Language :=
  {w | ∃ s : RealSentence, w = s.encode ∧ s.True}

end ApproxPolySatCH.Main.Supplement


