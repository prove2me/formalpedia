-- Prove2me | Definitions.Def_TightPQRepetition_Main_Encryption
-- name    : TightPQRepetition_Main_Encryption
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T23:38:16.91519+00:00
-- url     : https://prove2.me/theorems/985eadad-f544-44fd-9d1a-6d9348fbfaee
-- title:
--   Encryption interface, Definitions 1 and 2, and the fresh-key transformation $\widehat V$
-- statement:
--   An **encryption interface** consists of classical key generation, encryption of classical messages, and deterministic decryption of classical ciphertexts, with keys of a length determined by $\lambda$, ciphertexts of a length determined by $\lambda$ and the message length, and explicit coins. It is **semantically secure** if for every polynomial-size quantum distinguisher with quantum advice and every pair of equal-length polynomial-length message families $m_0,m_1$,
--   $$\big|\Pr[A(\mathrm{pk},\mathrm{Enc}(\mathrm{pk},m_0))=1]-\Pr[A(\mathrm{pk},\mathrm{Enc}(\mathrm{pk},m_1))=1]\big|$$
--   is negligible.
--
--   **Definition 1** (`ClassicalFHE`) adds homomorphic evaluation with correctness and compactness. **Definition 2** (`QFHE`) adds quantum encryption, evaluation and decryption algorithms with correctness in diamond norm for all keys in the support of Gen, compactness, and classical friendliness: on classical data Enc and Dec are the classical algorithms, a classical-output circuit yields a classical ciphertext output (invariance under computational-basis dephasing), and measuring an output ciphertext gives a ciphertext of the measured plaintext. Both carry an encryption interface.
--
--   The **transformation** of §3.3.1: the coins of $\widehat V$ are $r_{\rm Query}$ and per-round blocks $(r_{{\rm Gen},\ell},r_{{\rm Enc},\ell},r'_{{\rm Enc},\ell})$. In round $\ell$, $\widehat V$ decrypts the previous answers under their own keys, computes $q_\ell$, generates the fresh $(\mathrm{pk}_\ell,\mathrm{sk}_\ell)$, and sends $\mathrm{pk}_\ell$, $\mathrm{Enc}(\mathrm{pk}_\ell,q_\ell)$ and, except in the first round, $\mathrm{Enc}(\mathrm{pk}_\ell,\mathrm{sk}_{\ell-1})$. At the end it decrypts all answers and outputs the verdict of $V$.
--
--   `chainSample` is the distribution $D_{0,\lambda},D_{1,\lambda}$ of the proof of Lemma 5.4: fresh keys, a chosen first plaintext, zero plaintexts of the right length in later rounds, and the encrypted key chain.
--
--   **Formalization Note** The diamond-norm bound is stated as a bound over all ancillas and input states, so no supremum is taken. Evaluation acts on a tuple of ciphertexts and returns one ciphertext per output register, since the homomorphic prover of Lemma 3.5 must combine several ciphertexts under one key and separate its answer from its state. An evaluated ciphertext has a size independent of the circuit by its type, which is compactness.
--
--   Tuple sizes count output wires and block headers, including empty blocks. Correctness covers polynomially many input and output blocks; this prevents a zero-wire tuple with exponentially many headers from being treated as a polynomial-size computation. The printed syntax `Eval(pk, C, ct)` is read with `ct` a tuple of ciphertexts under one key (for QFHE a multi-register ciphertext state), as the honest prover of Lemma 3.5 requires.
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Definitions 1, 2, §3.3.1, Remarks 3.3–3.4, printed pp. 8–11 / PDF pp. 10–13; proof of Lemma 5.4, printed p. 24 / PDF p. 26

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Protocol

namespace TightPQRepetition.Main

/-!
Brakerski, Huang, Kalai, Spooner, STOC 2027 submission #158, §3.3 (PDF pp. 10–13): the encryption
interface used by the verifier, Definitions 1 and 2, and the fresh-key transformation `(P̂, V̂)`.

`EncScheme` is the part of both definitions that the verifier and the soundness proof use: classical
key generation, encryption of classical messages and deterministic decryption of classical
ciphertexts. A scheme of Definition 1, and a classically friendly scheme of Definition 2, each
carries one (`ClassicalFHE.toEncScheme`, `QFHE.toEncScheme`).
-/

open QAlgorithms Matrix
open scoped Kronecker ComplexOrder

/-- Classical key generation, encryption and decryption. -/
structure EncScheme where
  /-- Length of public keys. -/
  pkLen : ℕ → ℕ
  /-- Length of secret keys. -/
  skLen : ℕ → ℕ
  /-- Number of coins of key generation. -/
  genCoins : ℕ → ℕ
  /-- Number of coins to encrypt a message of the given length. -/
  encCoins : ℕ → ℕ → ℕ
  /-- Length of the ciphertext of a message of the given length. -/
  ctLen : ℕ → ℕ → ℕ
  /-- `(pk, sk) ← Gen(1^λ; r)`. -/
  gen : ℕ → Bits → Bits × Bits
  /-- `ct ← Enc(pk, m; r)`, as `enc lam pk m r`. -/
  enc : ℕ → Bits → Bits → Bits → Bits
  /-- The deterministic `m ← Dec(sk, ct)`. -/
  dec : ℕ → Bits → Bits → Bits

/-- `Gen`, `Enc` and `Dec` are polynomial-size classical algorithms. Keys have lengths that depend on
`λ` only, and a ciphertext has a length that depends on `λ` and the length of the message. -/
def EncScheme.IsEfficient (E : EncScheme) : Prop :=
  PolyBound E.pkLen ∧ PolyBound E.skLen ∧ PolyBound E.genCoins ∧
    (∃ s : ℕ → ℕ, PolyBound s ∧
      ∀ lam L, E.encCoins lam L ≤ s (lam + L) ∧ E.ctLen lam L ≤ s (lam + L)) ∧
    (∀ lam r, (E.gen lam r).1.length = E.pkLen lam ∧ (E.gen lam r).2.length = E.skLen lam) ∧
    (∀ lam pk m r, (E.enc lam pk m r).length = E.ctLen lam m.length) ∧
    Efficient (fun lam x => pack [(E.gen lam x).1, (E.gen lam x).2]) ∧
    Efficient (fun lam x =>
      E.enc lam ((unpack x).getD 0 []) ((unpack x).getD 1 []) ((unpack x).getD 2 [])) ∧
    Efficient (fun lam x => E.dec lam ((unpack x).getD 0 []) ((unpack x).getD 1 []))

/-- `Pr[A(pk, Enc(pk, m)) = 1]` over `(pk, sk) ← Gen(1^λ)` and the encryption coins. -/
noncomputable def EncScheme.challengeAccept (E : EncScheme) (T : QTest) (lam : ℕ) (m : Bits) : ℝ :=
  avgCoins (E.genCoins lam) fun rg => avgCoins (E.encCoins lam m.length) fun re =>
    T.accept (pack [(E.gen lam rg).1, E.enc lam (E.gen lam rg).1 m re])

/-- (Non-uniform post-quantum) semantic security, Definitions 1.2 and 2.2 with footnotes 5–6: for
every polynomial-size quantum adversary with quantum advice and every pair of message families of
equal polynomial length, chosen independently of `pk`, the advantage is negligible. -/
def EncScheme.IsSemanticallySecure (E : EncScheme) : Prop :=
  ∀ T : ℕ → QTest, IsQTestFamily T → ∀ m0 m1 : ℕ → Bits,
    (∀ lam, (m0 lam).length = (m1 lam).length) → PolyBound (fun lam => (m0 lam).length) →
    Negligible fun lam => |E.challengeAccept (T lam) lam (m0 lam) - E.challengeAccept (T lam) lam (m1 lam)|

/-! ### Definition 1: classical FHE -/

/-- A classical multi-output circuit: one Boolean circuit per output bit. -/
abbrev BoolMap := List MIPRE.SAT.Circuit

/-- The output of a multi-output circuit. -/
def boolMapEval (C : BoolMap) (x : Bits) : Bits := C.map fun c => c.evalBits x

/-- The size of a multi-output circuit, counting every output wire, including a constant-false
output represented by an empty gate list. -/
def boolMapSize (C : BoolMap) : ℕ := (C.map fun c => 1 + c.size).sum

/-- The format and circuit size of a tuple of output blocks. Empty blocks still cost one unit:
otherwise exponentially many empty outputs would have size zero. -/
def boolBlockSize (C : List BoolMap) : ℕ := C.length + boolMapSize C.flatten

/-- Definition 1. Homomorphic evaluation takes a tuple of ciphertexts under one key and returns a
tuple of ciphertexts, one per output block of the circuit; the printed one-ciphertext syntax is the
tuple of length one. -/
structure ClassicalFHE extends EncScheme where
  /-- Number of coins of evaluation. -/
  evalCoins : ℕ → ℕ → ℕ
  /-- `ct' ← Eval(pk, C, ct; r)`: `C` is a list of output blocks. -/
  eval : ℕ → Bits → List BoolMap → List Bits → Bits → List Bits

/-- Correctness (Definition 1.1): for every polynomial-size circuit family and inputs, decrypting
the homomorphic evaluation on fresh encryptions gives `C(x)`, except with negligible probability. -/
def ClassicalFHE.IsCorrect (F : ClassicalFHE) : Prop :=
  ∀ (C : ℕ → List BoolMap) (x : ℕ → List Bits),
    PolyBound (fun lam => boolBlockSize (C lam)) →
    PolyBound (fun lam => (x lam).length + ((x lam).map List.length).sum) →
    Negligible fun lam =>
      avgCoins (F.genCoins lam) fun rg =>
        avgCoins (((x lam).map fun m => F.encCoins lam m.length).sum) fun re =>
          avgCoins (F.evalCoins lam (boolBlockSize (C lam))) fun rv =>
            let pk := (F.gen lam rg).1
            let sk := (F.gen lam rg).2
            -- the fresh ciphertexts, each with its own slice of `re`
            let cts := (x lam).zipIdx.map fun p =>
              F.enc lam pk p.1
                ((re.drop (((x lam).take p.2).map fun m => F.encCoins lam m.length).sum).take
                  (F.encCoins lam p.1.length))
            let outs := F.eval lam pk (C lam) cts rv
            open Classical in
            if outs.map (F.dec lam sk) =
                (C lam).map (fun Ci => boolMapEval Ci (x lam).flatten) then 0 else 1

/-- Compactness (Definition 1.3 and footnote 7): evaluated ciphertexts, hence decryption, have size
bounded in terms of the output length alone, whatever the evaluated circuit. -/
def ClassicalFHE.IsCompact (F : ClassicalFHE) : Prop :=
  ∃ s : ℕ → ℕ, PolyBound s ∧ ∀ lam pk C cts r, ∀ ct ∈ F.eval lam pk C cts r,
    ct.length ≤ s (lam + (C.map List.length).sum)

/-- `Eval` is polynomial-size in the security parameter, the evaluated circuit and its input. -/
def ClassicalFHE.EvalEfficient (F : ClassicalFHE) : Prop :=
  ∃ s : ℕ → ℕ, PolyBound s ∧ ∀ lam (C : List BoolMap) n,
    F.evalCoins lam (boolBlockSize C) ≤ s (lam + boolBlockSize C) ∧
    ComputedBySize (fun x => pack (F.eval lam ((unpack x).headD []) C
      (unpack ((unpack x).getD 1 [])) ((unpack x).getD 2 []))) n
      (s (lam + boolBlockSize C + n))

/-- A scheme of Definition 1: PPT algorithms, correct, compact, semantically secure. -/
def ClassicalFHE.IsValid (F : ClassicalFHE) : Prop :=
  F.toEncScheme.IsEfficient ∧ F.EvalEfficient ∧ F.IsCorrect ∧ F.IsCompact ∧
    F.toEncScheme.IsSemanticallySecure

/-! ### Quantum channels -/

/-- A completely positive map in Kraus form. -/
structure Kraus (α β : Type) where
  /-- Index of the Kraus operators. -/
  idx : Type
  /-- The index is finite. -/
  fin : Fintype idx
  /-- The Kraus operators. -/
  op : idx → Matrix β α ℂ

attribute [instance] Kraus.fin

/-- The action `ρ ↦ ∑ᵢ Kᵢ ρ Kᵢ†`. -/
noncomputable def Kraus.apply {α β : Type} [Fintype α] [Fintype β] (K : Kraus α β)
    (ρ : Matrix α α ℂ) : Matrix β β ℂ :=
  ∑ i, K.op i * ρ * (K.op i)ᴴ

/-- Sequential composition. -/
noncomputable def Kraus.comp {α β γ : Type} [Fintype β] (K₂ : Kraus β γ) (K₁ : Kraus α β) :
    Kraus α γ :=
  ⟨K₂.idx × K₁.idx, inferInstance, fun p => K₂.op p.1 * K₁.op p.2⟩

/-- The first `a` qubits of an `a + b`-qubit string. -/
def fstBits {a b : ℕ} (x : Qubits (a + b)) : Qubits a := fun i => x (Fin.castAdd b i)

/-- The last `b` qubits of an `a + b`-qubit string. -/
def sndBits {a b : ℕ} (x : Qubits (a + b)) : Qubits b := fun i => x (Fin.natAdd a i)

/-- Two channels on disjoint registers. -/
def Kraus.par {a b c d : ℕ} (K₁ : Kraus (Qubits a) (Qubits b)) (K₂ : Kraus (Qubits c) (Qubits d)) :
    Kraus (Qubits (a + c)) (Qubits (b + d)) :=
  ⟨K₁.idx × K₂.idx, inferInstance,
    fun p => Matrix.of fun y x =>
      K₁.op p.1 (fstBits y) (fstBits x) * K₂.op p.2 (sndBits y) (sndBits x)⟩

/-- The trivial channel on no qubits. -/
def Kraus.unit : Kraus (Qubits 0) (Qubits 0) := ⟨Unit, inferInstance, fun _ => 1⟩

/-- A channel applied to each register of a list, from `L` qubits to `g L` qubits. -/
def Kraus.parUp (g : ℕ → ℕ) (K : (L : ℕ) → Kraus (Qubits L) (Qubits (g L))) :
    (l : List ℕ) → Kraus (Qubits l.sum) (Qubits (l.map g).sum)
  | [] => Kraus.unit
  | L :: l => Kraus.par (K L) (Kraus.parUp g K l)

/-- A channel applied to each register of a list, from `g L` qubits to `L` qubits. -/
def Kraus.parDown (g : ℕ → ℕ) (K : (L : ℕ) → Kraus (Qubits (g L)) (Qubits L)) :
    (l : List ℕ) → Kraus (Qubits (l.map g).sum) (Qubits l.sum)
  | [] => Kraus.unit
  | L :: l => Kraus.par (K L) (Kraus.parDown g K l)

/-- The identity channel on `L` qubits. -/
def Kraus.idChannel (L : ℕ) : Kraus (Qubits L) (Qubits L) := ⟨Unit, inferInstance, fun _ => 1⟩

/-- The complete dephasing, i.e. computational-basis measurement, of `L` qubits. -/
def Kraus.measure (L : ℕ) : Kraus (Qubits L) (Qubits L) :=
  ⟨Qubits L, inferInstance, fun z => Matrix.of fun y x => if y = z ∧ x = z then 1 else 0⟩

/-- `‖Φ - Ψ‖⋄ ≤ ε`: for every ancilla and every input density matrix, the outputs of `Φ ⊗ id` and
`Ψ ⊗ id` are within `ε` in trace norm. -/
def DiamondClose {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (Φ Ψ : Kraus α β) (ε : ℝ) : Prop :=
  ∀ (d : ℕ) (ρ : Matrix (α × Qubits d) (α × Qubits d) ℂ), ρ.PosSemidef → ρ.trace = 1 →
    WildeQIT.traceNorm
      ((∑ i, ((Φ.op i) ⊗ₖ (1 : Matrix (Qubits d) (Qubits d) ℂ)) * ρ *
          ((Φ.op i) ⊗ₖ (1 : Matrix (Qubits d) (Qubits d) ℂ))ᴴ) -
        (∑ i, ((Ψ.op i) ⊗ₖ (1 : Matrix (Qubits d) (Qubits d) ℂ)) * ρ *
          ((Ψ.op i) ⊗ₖ (1 : Matrix (Qubits d) (Qubits d) ℂ))ᴴ)) ≤ ε

/-- A quantum algorithm with `cl` classical input bits, `a` input qubits and `b` output qubits:
all other wires start in `|0⟩` and are traced out at the end. -/
structure QAlg (cl a b : ℕ) where
  /-- Total number of wires. -/
  w : ℕ
  /-- The circuit. -/
  circ : QCircuit w
  /-- The wires of the input, classical part first. -/
  inW : Fin (cl + a) ↪ Fin w
  /-- The wires of the output. -/
  outW : Fin b ↪ Fin w

/-- The size of a quantum algorithm. -/
def QAlg.size {cl a b : ℕ} (A : QAlg cl a b) : ℕ := A.w + A.circ.size

open Classical in
/-- The channel of a quantum algorithm with its classical input fixed to `x`: a Kraus operator for
each value `e` of the traced-out wires. -/
noncomputable def QAlg.channel {cl a b : ℕ} (A : QAlg cl a b) (x : Qubits cl) :
    Kraus (Qubits a) (Qubits b) :=
  ⟨{i : Fin A.w // i ∉ Set.range A.outW} → Bool, inferInstance,
    fun e => Matrix.of fun y z =>
      ∑ v : Qubits A.w,
        if (∀ i, v (A.outW i) = y i) ∧ (∀ i : {i : Fin A.w // i ∉ Set.range A.outW}, v i = e i) then
          A.circ.unitary v
            (fun i => if h : ∃ j, A.inW j = i then Fin.append x z h.choose else false)
        else 0⟩

/-! ### Definition 2: classically friendly quantum FHE -/

/-- Definition 2, together with the classical algorithms that classical friendliness provides.
Encryption, evaluation and decryption of quantum data are quantum algorithms with the key as
classical input. As in Definition 1, evaluation acts on a tuple of ciphertexts under one key.
`evLen` is the size of an evaluated ciphertext: by its type it does not depend on the circuit. -/
structure QFHE extends EncScheme where
  /-- Size of an evaluated ciphertext of `L` qubits. -/
  evLen : ℕ → ℕ → ℕ
  /-- `ρ ← Enc(pk, σ)`. -/
  encQ : (lam L : ℕ) → QAlg (pkLen lam) L (ctLen lam L)
  /-- `σ ← Eval(pk, C, ρ)`, where `ins`, `outs` are the plaintext registers of `C`. -/
  evalQ : (lam : ℕ) → (ins outs : List ℕ) → QAlg 0 ins.sum outs.sum →
    QAlg (pkLen lam) (ins.map (ctLen lam)).sum (outs.map (evLen lam)).sum
  /-- `ρ ← Dec(sk, σ)`. -/
  decQ : (lam L : ℕ) → QAlg (skLen lam) (evLen lam L) L

/-- The encryption channel under `pk`. -/
noncomputable def QFHE.encCh (Q : QFHE) (lam : ℕ) (pk : Qubits (Q.pkLen lam)) (L : ℕ) :
    Kraus (Qubits L) (Qubits (Q.ctLen lam L)) :=
  (Q.encQ lam L).channel pk

/-- The decryption channel under `sk`. -/
noncomputable def QFHE.decCh (Q : QFHE) (lam : ℕ) (sk : Qubits (Q.skLen lam)) (L : ℕ) :
    Kraus (Qubits (Q.evLen lam L)) (Qubits L) :=
  (Q.decQ lam L).channel sk

/-- `Dec_sk ∘ Eval_{pk,C} ∘ Enc_pk`, register by register. -/
noncomputable def QFHE.roundTrip (Q : QFHE) (lam : ℕ) (pk : Qubits (Q.pkLen lam))
    (sk : Qubits (Q.skLen lam)) (ins outs : List ℕ) (C : QAlg 0 ins.sum outs.sum) :
    Kraus (Qubits ins.sum) (Qubits outs.sum) :=
  (Kraus.parDown (Q.evLen lam) (Q.decCh lam sk) outs).comp
    (((Q.evalQ lam ins outs C).channel pk).comp (Kraus.parUp (Q.ctLen lam) (Q.encCh lam pk) ins))

/-- The channel of a quantum circuit with no classical input. -/
noncomputable def QAlg.plainChannel {a b : ℕ} (C : QAlg 0 a b) : Kraus (Qubits a) (Qubits b) :=
  C.channel (fun i => i.elim0)

/-- Correctness (Definition 2.1): for every polynomial `p` there is a negligible `μ` such that for
all `λ`, all `p(λ)`-size circuits `C` and all keys in the support of `Gen`,
`‖Dec_sk ∘ Eval_{pk,C} ∘ Enc_pk - C‖⋄ ≤ μ(λ)`. -/
def QFHE.IsCorrect (Q : QFHE) : Prop :=
  ∀ p : ℕ → ℕ, PolyBound p → ∃ μ : ℕ → ℝ, Negligible μ ∧
    ∀ (lam : ℕ) (ins outs : List ℕ) (C : QAlg 0 ins.sum outs.sum), C.size + ins.length + outs.length ≤ p lam →
      ∀ r : Qubits (Q.genCoins lam),
        DiamondClose
          (Q.roundTrip lam (ofBits _ (Q.gen lam (toBits r)).1) (ofBits _ (Q.gen lam (toBits r)).2)
            ins outs C)
          C.plainChannel (μ lam)

/-- The density matrix of a computational-basis state. -/
def basisDensity {α : Type} [DecidableEq α] (x : α) : Matrix α α ℂ := Matrix.single x x 1

/-- The channel that measures the second of two registers and leaves the first alone. -/
def Kraus.measureSecond (a b : ℕ) : Kraus (Qubits (a + (b + 0))) (Qubits (a + (b + 0))) :=
  Kraus.par (Kraus.idChannel a) (Kraus.par (Kraus.measure b) Kraus.unit)

/-- The second output register is classical: its density matrix is invariant under
computational-basis dephasing, including correlations with the first output register. -/
def Kraus.HasClassicalSecondOutput {n : ℕ} (a b : ℕ)
    (K : Kraus (Qubits n) (Qubits (a + (b + 0)))) : Prop :=
  ∀ ρ : Matrix (Qubits n) (Qubits n) ℂ, ρ.PosSemidef → ρ.trace = 1 →
    (Kraus.measureSecond a b).apply (K.apply ρ) = K.apply ρ

/-- Classical friendliness (Definition 2.4). On classical messages, encryption is the classical
algorithm `enc`; on classical ciphertexts, decryption is the deterministic `dec`, which returns all
`L` bits of the plaintext of an `L`-qubit evaluated ciphertext; and measuring an output ciphertext in the computational basis yields a classical ciphertext of the measured
plaintext, stated here for the second of two output registers. A circuit with a classical second output
also has a classical second ciphertext output, before decryption. -/
def QFHE.IsClassicallyFriendly (Q : QFHE) : Prop :=
  (∀ (lam L : ℕ) (pk : Qubits (Q.pkLen lam)) (m : Qubits L),
    (Q.encCh lam pk L).apply (basisDensity m) =
      ((2 : ℂ) ^ (Q.encCoins lam L))⁻¹ • ∑ r : Qubits (Q.encCoins lam L),
        basisDensity (ofBits (Q.ctLen lam L) (Q.enc lam (toBits pk) (toBits m) (toBits r)))) ∧
  (∀ (lam L : ℕ) (sk : Qubits (Q.skLen lam)) (c : Qubits (Q.evLen lam L)),
    (Q.dec lam (toBits sk) (toBits c)).length = L ∧
    (Q.decCh lam sk L).apply (basisDensity c) =
      basisDensity (ofBits L (Q.dec lam (toBits sk) (toBits c)))) ∧
  (∀ (lam : ℕ) (ins : List ℕ) (a b : ℕ) (C : QAlg 0 ins.sum (a + (b + 0))),
    C.plainChannel.HasClassicalSecondOutput a b → ∀ r : Qubits (Q.genCoins lam),
      Kraus.HasClassicalSecondOutput (Q.evLen lam a) (Q.evLen lam b)
        (((Q.evalQ lam ins [a, b] C).channel (ofBits _ (Q.gen lam (toBits r)).1)).comp
          (Kraus.parUp (Q.ctLen lam) (Q.encCh lam (ofBits _ (Q.gen lam (toBits r)).1)) ins))) ∧
  (∀ p : ℕ → ℕ, PolyBound p → ∃ μ : ℕ → ℝ, Negligible μ ∧
    ∀ (lam : ℕ) (ins : List ℕ) (a b : ℕ) (C : QAlg 0 ins.sum (a + (b + 0))),
      C.size + ins.length + 2 ≤ p lam →
      ∀ r : Qubits (Q.genCoins lam),
        DiamondClose
          ((Kraus.parDown (Q.evLen lam)
              (Q.decCh lam (ofBits _ (Q.gen lam (toBits r)).2)) [a, b]).comp
            ((Kraus.measureSecond (Q.evLen lam a) (Q.evLen lam b)).comp
              (((Q.evalQ lam ins [a, b] C).channel (ofBits _ (Q.gen lam (toBits r)).1)).comp
                (Kraus.parUp (Q.ctLen lam) (Q.encCh lam (ofBits _ (Q.gen lam (toBits r)).1)) ins))))
          ((Kraus.measureSecond a b).comp C.plainChannel) (μ lam))

/-- A scheme of Definition 2 that is classically friendly: polynomial-size algorithms (for `Eval`,
in the size of the evaluated circuit; for `Dec`, independent of it, which is compactness, Definition
2.3), correct, semantically secure and classically friendly. -/
def QFHE.IsValid (Q : QFHE) : Prop :=
  Q.toEncScheme.IsEfficient ∧
    (∃ s : ℕ → ℕ, PolyBound s ∧
      (∀ lam L, (Q.encQ lam L).size ≤ s (lam + L) ∧ Q.evLen lam L ≤ s (lam + L) ∧
        (Q.decQ lam L).size ≤ s (lam + L)) ∧
      ∀ lam ins outs (C : QAlg 0 ins.sum outs.sum),
        (Q.evalQ lam ins outs C).size ≤ s (lam + ins.length + outs.length + ins.sum + outs.sum + C.size)) ∧
    Q.IsCorrect ∧ Q.IsClassicallyFriendly ∧ Q.toEncScheme.IsSemanticallySecure

/-! ### The transformation of §3.3.1 -/

/-- The coins of round `ℓ` of `V̂` (rounds are numbered from `0`): `r_Gen,ℓ`, `r_Enc,ℓ` and, except
in the first round, `r'_Enc,ℓ`. -/
def blockLen (E : EncScheme) (V : Verifier) (lam ℓ : ℕ) : ℕ :=
  E.genCoins lam + E.encCoins lam (V.qLen lam ℓ) +
    if ℓ = 0 then 0 else E.encCoins lam (E.skLen lam)

/-- The total length of the blocks of the rounds before `ℓ`. -/
def blocksBefore (E : EncScheme) (V : Verifier) (lam ℓ : ℕ) : ℕ :=
  ((List.range ℓ).map (blockLen E V lam)).sum

/-- The block of round `ℓ` in a string of consecutive blocks. -/
def blockAt (E : EncScheme) (V : Verifier) (lam ℓ : ℕ) (r : Bits) : Bits :=
  (r.drop (blocksBefore E V lam ℓ)).take (blockLen E V lam ℓ)

/-- `r_Gen` of a block. -/
def genPart (E : EncScheme) (lam : ℕ) (b : Bits) : Bits := b.take (E.genCoins lam)

/-- `r_Enc` of a block of round `ℓ`. -/
def encPart (E : EncScheme) (V : Verifier) (lam ℓ : ℕ) (b : Bits) : Bits :=
  (b.drop (E.genCoins lam)).take (E.encCoins lam (V.qLen lam ℓ))

/-- `r'_Enc` of a block of round `ℓ`. -/
def skEncPart (E : EncScheme) (V : Verifier) (lam ℓ : ℕ) (b : Bits) : Bits :=
  b.drop (E.genCoins lam + E.encCoins lam (V.qLen lam ℓ))

/-- The message of round `ℓ` of `V̂` (step 2(a), PDF p. 12): the fresh `pk_ℓ`, the encryption of the
plaintext `p` under it, and, when `ℓ` is not the first round, the encryption under `pk_ℓ` of the
previous round's secret key `skPrev`. All three come from the block `b`. -/
def hatMessage (E : EncScheme) (V : Verifier) (lam ℓ : ℕ) (b p skPrev : Bits) : Bits :=
  pack [(E.gen lam (genPart E lam b)).1,
    E.enc lam (E.gen lam (genPart E lam b)).1 p (encPart E V lam ℓ b),
    if ℓ = 0 then [] else
      E.enc lam (E.gen lam (genPart E lam b)).1 skPrev (skEncPart E V lam ℓ b)]

/-- The coins of `V̂` after `r_Query`. -/
def hatBlocks (V : Verifier) (lam : ℕ) (r : Bits) : Bits := r.drop (V.coins lam)

/-- `(pk_ℓ, sk_ℓ)` for the coins `r` of `V̂`. -/
def hatKeys (E : EncScheme) (V : Verifier) (lam : ℕ) (r : Bits) (ℓ : ℕ) : Bits × Bits :=
  E.gen lam (genPart E lam (blockAt E V lam ℓ (hatBlocks V lam r)))

/-- `r_Query` of the coins of `V̂`. -/
def hatQueryCoins (V : Verifier) (lam : ℕ) (r : Bits) : Bits := r.take (V.coins lam)

/-- The decrypted answers `a_ℓ = Dec(sk_ℓ, â_ℓ)`. -/
def plainAnswers (E : EncScheme) (V : Verifier) (lam : ℕ) (r : Bits) (as : List Bits) : List Bits :=
  as.zipIdx.map fun p => E.dec lam (hatKeys E V lam r p.2).2 p.1

/-- The fresh-key transformation `V̂` of §3.3.1 (PDF pp. 12–13). Its coins are `r_Query` followed
by the blocks of all rounds. In round `j` it decrypts the previous answers under their own keys,
computes `q_j = f_j(r_Query, a_0, …, a_{j-1})`, and sends `hatMessage`; at the end it decrypts all
answers and outputs `g`. -/
def hatV (E : EncScheme) (V : Verifier) : Verifier where
  rounds := V.rounds
  coins lam := V.coins lam + blocksBefore E V lam (V.rounds lam)
  qLen lam j := (pack [zeros (E.pkLen lam), zeros (E.ctLen lam (V.qLen lam j)),
    zeros (if j = 0 then 0 else E.ctLen lam (E.skLen lam))]).length
  query lam r j as :=
    hatMessage E V lam j (blockAt E V lam j (hatBlocks V lam r))
      (V.query lam (hatQueryCoins V lam r) j (plainAnswers E V lam r as))
      (hatKeys E V lam r (j - 1)).2
  verdict lam r τ :=
    V.verdict lam (hatQueryCoins V lam r)
      ((List.range τ.length).map fun i =>
        (V.query lam (hatQueryCoins V lam r) i
            ((plainAnswers E V lam r (τ.map Prod.snd)).take i),
          (plainAnswers E V lam r (τ.map Prod.snd)).getD i []))

/-- The number of bits of a key chain: the blocks of all rounds. -/
def chainCoins (E : EncScheme) (V : Verifier) (lam : ℕ) : ℕ := blocksBefore E V lam (V.rounds lam)

/-- The distributions `D_{0,λ}`, `D_{1,λ}` of the proof of Lemma 5.4 (PDF p. 26): fresh keys for
all rounds, the ciphertext of `head` in the first round, encryptions of the zero plaintext of the
right length in the later rounds, and each previous secret key encrypted under the next public
key. Its coins are the blocks of all rounds. -/
def chainSample (E : EncScheme) (V : Verifier) (lam : ℕ) (head r : Bits) : Bits :=
  pack ((List.range (V.rounds lam)).map fun ℓ =>
    hatMessage E V lam ℓ (blockAt E V lam ℓ r) (if ℓ = 0 then head else zeros (V.qLen lam ℓ))
      (E.gen lam (genPart E lam (blockAt E V lam (ℓ - 1) r))).2)

end TightPQRepetition.Main


