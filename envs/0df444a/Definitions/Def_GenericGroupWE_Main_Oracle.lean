-- Prove2me | Definitions.Def_GenericGroupWE_Main_Oracle
-- name    : GenericGroupWE_Main_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:38.096633+00:00
-- url     : https://prove2.me/theorems/ab1c4f0d-5619-43b5-ae45-69de0c62f277
-- title:
--   Clocked probabilistic oracle programs and witness-encryption experiments
-- statement:
--   An oracle program has a bit-string transition function, a polynomial round clock, and a polynomial state-length cap. Actions halt, change local state, flip a fair coin, request one fresh prime-order group, or add/subtract two exposed strings. Nonprime group requests, malformed actions, exhausted clocks and oversized states abort. The transition's Turing time is asserted separately by each algorithmic theorem.
--
--   A ciphertext contains public output and access to its group context; neither decryption nor an adversary receives the encoding table. Decryption cannot create a replacement context. A depth-$Q$ adaptive decision tree counts every oracle call, including invalid guesses, and a randomized adversary assigns distributions to trees using only the entire public ciphertext. Correctness and advantage average over all coins and fresh encodings, with $n=\max(2,\lambda,|\varphi|)$.
--
--   $$\operatorname{Adv}_A=|\Pr[A(\operatorname{Enc}(0))=1]-\Pr[A(\operatorname{Enc}(1))=1]|.$$
--
--   The failure outcome is common. A singleton output string decodes to its bit; every other raw output decodes to failure, so the external decryption result is exactly a bit or failure.
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, Definition 2.1 and §2, PDF pp. 7–8 (printed pp. 6–7); Theorem 1.1, PDF p. 2 (printed p. 1); concrete bounded machine encoding of polynomial-time oracle algorithms.

import Definitions.Def_GenericGroupWE_Main_Group

namespace GenericGroupWE.Main

/-- Concrete next actions, decoded from a polynomial-time bit-string transition. -/
inductive OracleAction where
  | halt (output : Bits)
  | step (state : Bits)
  | coin (zero one : Bits)
  | group (p : ℕ) (state : Bits)
  | query (subtract : Bool) (x y state : Bits)

def decodeAction : Bits → Option OracleAction
  | false :: output => some (.halt output)
  | true :: false :: state => some (.step state)
  | true :: true :: false :: rest => do
      let (zero, one) ← unpacket rest
      pure (.coin zero one)
  | true :: true :: true :: false :: rest => do
      let (p, state) ← unpacket rest
      pure (.group (bitsNat p) state)
  | true :: true :: true :: true :: subtract :: rest => do
      let (x, rest) ← unpacket rest
      let (y, state) ← unpacket rest
      pure (.query subtract x y state)
  | _ => none

/-- Fixed clock and state cap, polynomial in the length of the entire input.
The transition's Turing-time property is imposed separately, never inferred from this clock. -/
structure OracleProgram where
  next : Bits → Bits
  clockCoefficient : ℕ
  clockDegree : ℕ
  stateCoefficient : ℕ
  stateDegree : ℕ

def OracleProgram.clock (P : OracleProgram) (n : ℕ) : ℕ :=
  P.clockCoefficient * (n + 1) ^ P.clockDegree

def OracleProgram.cap (P : OracleProgram) (n : ℕ) : ℕ :=
  P.stateCoefficient * (n + 1) ^ P.stateDegree

/-- The table is interpreter state. Programs see only strings; both consumers get this oracle. -/
structure Ciphertext where
  context : Option GroupContext
  output : Option Bits

def abortCiphertext : Ciphertext := ⟨none, none⟩

def Ciphertext.public (C : Ciphertext) : Bits :=
  pack [publicContext C.context, replyBits C.output]

noncomputable def runRounds (P : OracleProgram) (allowGroup : Bool) (cap : ℕ) :
    ℕ → Bits → Option GroupContext → PMF Ciphertext
  | 0, _, _ => pure abortCiphertext
  | fuel + 1, state, context =>
    if state.length > cap then pure abortCiphertext else
    match decodeAction (P.next state) with
    | none => pure abortCiphertext
    | some (.halt out) => pure ⟨context, some out⟩
    | some (.step state') => runRounds P allowGroup cap fuel state' context
    | some (.coin zero one) =>
        (PMF.uniformOfFintype Bool).bind fun b =>
          runRounds P allowGroup cap fuel (if b then one else zero) context
    | some (.group p state') =>
        if allowGroup ∧ context.isNone then
          if hp : p.Prime then
            (freshContext p hp).bind fun Γ =>
              runRounds P allowGroup cap fuel (pack [state', Γ.generator]) (some Γ)
          else pure abortCiphertext
        else pure abortCiphertext
    | some (.query subtract x y state') =>
        let reply := context.bind fun Γ => Γ.query subtract x y
        runRounds P allowGroup cap fuel (pack [state', replyBits reply]) context

noncomputable def OracleProgram.run (P : OracleProgram) (allowGroup : Bool)
    (input : Bits) (context : Option GroupContext) : PMF Ciphertext :=
  runRounds P allowGroup (P.cap input.length) (P.clock input.length) input context

/-- Every query, including invalid guesses and repeated operands, consumes one level. -/
inductive QueryTree : ℕ → Type where
  | halt {q : ℕ} (bit : Bool) : QueryTree q
  | query {q : ℕ} (subtract : Bool) (x y : Bits)
      (continuation : Option Bits → QueryTree q) : QueryTree (q + 1)

def QueryTree.run {q : ℕ} (context : Option GroupContext) : QueryTree q → Bool
  | .halt b => b
  | .query subtract x y continuation =>
      (continuation (context.bind fun Γ => Γ.query subtract x y)).run context

/-- Arbitrary local computation, advice and coins, fixed before the fresh experiment.
Only the entire public ciphertext is passed to this function. -/
abbrev Adversary (q : ℕ) := Bits → PMF (QueryTree q)

noncomputable def probability {α : Type*} (law : PMF α) (event : α → Prop) : ℝ :=
  (law.toOuterMeasure {a | event a}).toReal

def effectiveSize (security : ℕ) (statement : Bits) : ℕ :=
  max 2 (max security statement.length)

def encryptionInput (security : ℕ) (statement : Bits) (message : Bool) : Bits :=
  pack [List.replicate security true, statement, [message]]

def decryptionInput (security : ℕ) (statement witness : Bits) (C : Ciphertext) : Bits :=
  pack [List.replicate security true, statement, witness, C.public]

noncomputable def encrypt (P : OracleProgram) (security : ℕ) (statement : Bits)
    (message : Bool) : PMF Ciphertext :=
  P.run true (encryptionInput security statement message) none

/-- Decryption's external result is exactly a bit or failure. -/
def decodeBitOutput : Option Bits → Option Bool
  | some [bit] => some bit
  | _ => none

noncomputable def decrypt (P : OracleProgram) (security : ℕ) (statement witness : Bits)
    (C : Ciphertext) : PMF (Option Bool) :=
  (P.run false (decryptionInput security statement witness C) C.context).map
    (fun result => decodeBitOutput result.output)

noncomputable def correctnessProbability (enc dec : OracleProgram) (security : ℕ)
    (statement witness : Bits) (message : Bool) : ℝ :=
  probability ((encrypt enc security statement message).bind fun C =>
    decrypt dec security statement witness C) (fun out => out = some message)

noncomputable def adversaryOutput {q : ℕ} (A : Adversary q) (law : PMF Ciphertext) : PMF Bool :=
  law.bind fun C => (A C.public).map fun tree => tree.run C.context

noncomputable def advantage {q : ℕ} (enc : OracleProgram) (security : ℕ)
    (statement : Bits) (A : Adversary q) : ℝ :=
  |probability (adversaryOutput A (encrypt enc security statement false)) (· = true) -
    probability (adversaryOutput A (encrypt enc security statement true)) (· = true)|

end GenericGroupWE.Main


