-- Prove2me | Definitions.Def_APSCounting893_Main_OracleProofPrimitives
-- name    : APSCounting893_Main_OracleProofPrimitives
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:11:35.780199+00:00
-- url     : https://prove2.me/theorems/90b41966-5fbe-428b-a208-d3b0ff5cdb12
-- title:
--   Finite register programs and canonical trailing-test payloads
-- statement:
--   This module supplies the finite data used in an explicit oracle-machine implementation of the trailing-coefficient test.
--
--   A register program has a finite control set and a fixed finite number of word registers. Its instructions inspect, remove or prepend one Boolean symbol, make a query using an entire register word, or halt with a Boolean answer. A query consumes that register. The input and auxiliary words occupy two designated registers; all remaining registers begin empty. Iterating the transition function defines execution:
--
--   $$\operatorname{run}(P,A,x,w,t)=\operatorname{step}_{P,A}^{\,t}(\operatorname{initial}_P(x,w)).$$
--
--   The module also gives a delimited binary pairing function and canonical natural-number and exponent-tuple encodings. The trailing-test verifier accepts a candidate coefficient with a one numerator bit, excludes earlier parameter exponents with one numerator bits, and tests every queried bit at the candidate parameter exponent with final exponent zero. Malformed candidate payloads reject; malformed universal payloads accept.
--
--   These are data structures, transition semantics and encoding predicates. Polynomial simulation, runtime bounds and Counting Hierarchy closure are separate proof targets.
--
--   **Formalization Note** The finite register implementation is an auxiliary construction for the proof of Lemma 6.5; it does not assume an APS oracle or a resultant identity.
-- source:
--   Auxiliary finite-machine implementation for Agarwal, Hari, Pandey, Shukla, STOC 2027 submission #893, Lemma 6.5, p. 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_CoefficientLanguages

set_option autoImplicit false
namespace APSCounting893.Main

inductive StackAction (Q : Type) (r : ℕ) where
  | jump (next : Q)
  | peek (reg : Fin (r + 2)) (zero one empty : Q)
  | pop (reg : Fin (r + 2)) (zero one empty : Q)
  | push (reg : Fin (r + 2)) (bit : Bool) (next : Q)
  | query (reg : Fin (r + 2)) (yes no : Q)
  | halt (bit : Bool)

structure StackProgram (Q : Type) (r : ℕ) where
  initial : Q
  transition : Q → StackAction Q r

structure StackConfig (Q : Type) (r : ℕ) where
  state : Q
  regs : Fin (r + 2) → Word
  answer : Option Bool

noncomputable def StackProgram.step {Q : Type} {r : ℕ} (P : StackProgram Q r)
    (A : Language) (cfg : StackConfig Q r) : StackConfig Q r := by
  classical
  exact if cfg.answer.isSome then cfg else
    match P.transition cfg.state with
    | .jump next => { cfg with state := next }
    | .peek j zero one empty =>
        { cfg with state := match cfg.regs j with
          | false :: _ => zero | true :: _ => one | [] => empty }
    | .pop j zero one empty =>
        { state := (match cfg.regs j with
            | false :: _ => zero
            | true :: _ => one
            | [] => empty)
          regs := Function.update cfg.regs j (cfg.regs j).tail
          answer := cfg.answer }
    | .push j bit next => { cfg with state := next, regs := Function.update cfg.regs j (bit :: cfg.regs j) }
    | .query j yes no =>
        { state := (if A (cfg.regs j) then yes else no)
          regs := Function.update cfg.regs j []
          answer := cfg.answer }
    | .halt bit => { cfg with answer := some bit }

def StackProgram.initialConfig {Q : Type} {r : ℕ} (P : StackProgram Q r) (x w : Word) : StackConfig Q r :=
  { state := P.initial, regs := fun j => if j = 0 then x else if j = 1 then w else [], answer := none }

noncomputable def StackProgram.run {Q : Type} {r : ℕ} (P : StackProgram Q r)
    (A : Language) (x w : Word) (time : ℕ) : StackConfig Q r :=
  (P.step A)^[time] (P.initialConfig x w)

noncomputable def StackProgram.exec {Q : Type} {r : ℕ} (P : StackProgram Q r)
    (A : Language) (cfg : StackConfig Q r) (t : ℕ) : StackConfig Q r := (P.step A)^[t] cfg

lemma StackProgram.exec_succ {Q : Type} {r : ℕ} (P : StackProgram Q r)
    (A : Language) (cfg : StackConfig Q r) (t : ℕ) :
    P.exec A cfg (t + 1) = P.step A (P.exec A cfg t) := Function.iterate_succ_apply' _ _ _

lemma StackProgram.exec_add {Q : Type} {r : ℕ} (P : StackProgram Q r)
    (A : Language) (cfg : StackConfig Q r) (t s : ℕ) :
    P.exec A cfg (t + s) = P.exec A (P.exec A cfg t) s := by
  unfold exec
  rw [Nat.add_comm, Function.iterate_add_apply]

lemma StackProgram.exec_one {Q : Type} {r : ℕ} (P : StackProgram Q r)
    (A : Language) (cfg : StackConfig Q r) : P.exec A cfg 1 = P.step A cfg := rfl


def pairWord (x y : Word) : Word := x.flatMap (fun b => [true, b]) ++ [false] ++ y

def canonicalBits : Word → Bool
  | [] => true
  | [b] => b
  | _ :: b :: w => canonicalBits (b :: w)

def bitsValue (w : Word) : ℕ := w.foldr Nat.bit 0

def readUnary : Word → Option (ℕ × Word)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (readUnary rest).map (fun p => (p.1 + 1, p.2))

def decodeNat (w : Word) : Option (ℕ × Word) := do
  let p ← readUnary w
  if p.1 ≤ p.2.length then
    let bits := p.2.take p.1
    if canonicalBits bits then some (bitsValue bits, p.2.drop p.1) else none
  else none

def decodePair : Word → Option (Word × Word)
  | false :: rest => some ([], rest)
  | true :: b :: rest => (decodePair rest).map (fun p => (b :: p.1, p.2))
  | _ => none

noncomputable def orderExponent {n : ℕ} (order : List (Fin n)) (a : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  (order.map (fun v => Finsupp.single v (a v))).sum

def decodeNats : ℕ → Word → Option (List ℕ × Word)
  | 0, w => some ([], w)
  | n + 1, w => do
      let a ← decodeNat w
      let rest ← decodeNats n a.2
      return (a.1 :: rest.1, rest.2)

noncomputable def exponentOfList (k : ℕ) (ns : List ℕ) : Fin (k + 1) →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i => ns[i.val]?.getD 0) (by simp)

def encodeExponent {k : ℕ} (a : Fin (k + 1) →₀ ℕ) : Word :=
  encodeList encodeNat (List.ofFn (fun i => a i))

noncomputable def decodeExponent (k : ℕ) (w : Word) : Option ((Fin (k + 1) →₀ ℕ) × Word) := do
  let n ← decodeNat w
  if n.1 = k + 1 then
    let ns ← decodeNats (k + 1) n.2
    return (exponentOfList k ns.1, ns.2)
  else none

def encodeExistential {k : ℕ} (a : Fin (k + 1) →₀ ℕ) (q : ℕ) : Word :=
  encodeExponent a ++ encodeNat q

def encodeUniversal {k : ℕ} (e : Fin (k + 1) →₀ ℕ) (qE qF : ℕ) : Word :=
  encodeExponent e ++ encodeNat qE ++ encodeNat qF

noncomputable def decodeExistential (k : ℕ) (w : Word) : Option ((Fin (k + 1) →₀ ℕ) × ℕ) := do
  let a ← decodeExponent k w
  let q ← decodeNat a.2
  return (a.1, q.1)

noncomputable def decodeUniversal (k : ℕ) (w : Word) : Option ((Fin (k + 1) →₀ ℕ) × ℕ × ℕ) := do
  let e ← decodeExponent k w
  let qE ← decodeNat e.2
  let qF ← decodeNat qE.2
  return (e.1, qE.1, qF.1)

noncomputable def BaseTrailingLanguage {k : ℕ} (rho : CoefficientRepresentation k) : Language :=
  fun w => match decodePair w with
  | none => False
  | some (v, u) => match decodePair v with
    | none => False
    | some (x, aWord) => match decodeExistential k aWord with
      | none => False
      | some (a, qA) => CoefficientBitLanguage rho (coefficientQuery x a .numerator qA) ∧
          match decodeUniversal k u with
          | none => True
          | some (e, qE, qF) =>
              (¬ List.Lex (· < ·)
                ((List.ofFn (fun i : Fin k => i.castSucc)).map (fun v => e v))
                ((List.ofFn (fun i : Fin k => i.castSucc)).map (fun v => a v)) ∨
                ¬ CoefficientBitLanguage rho (coefficientQuery x e .numerator qE)) ∧
              ¬ CoefficientBitLanguage rho (coefficientQuery x
                (orderExponent (List.ofFn (fun i : Fin k => i.castSucc)) a) .numerator qF)


end APSCounting893.Main


