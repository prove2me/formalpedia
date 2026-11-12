-- Prove2me | Definitions.Def_QSampVerif_QFHEScheme
-- name    : QSampVerif_QFHEScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:29:47.378166+00:00
-- url     : https://prove2.me/theorems/04eb472a-0598-4802-a88c-12c71b4b766a
-- title:
--   Leveled QFHE schemes (Definition 3.20): algorithms, classical-output circuits, efficiency and compactness
-- statement:
--   A **leveled quantum fully homomorphic encryption scheme** consists of
--
--   1. classical key generation $(\mathsf{sk},\mathsf{ek})=\mathsf{Gen}(1^\kappa,1^L;g)$ with a polynomial number of coins $g$;
--   2. classical encryption $\mathsf{ct}=\mathsf{Enc}_{\mathsf{sk}}(x;e)$ with a polynomial number of coins $e$;
--   3. homomorphic evaluation: from $(\mathsf{ek},\langle C\rangle,\mathsf{ct})$ a classical polynomial-time map produces a quantum circuit that acts on the auxiliary input register of $C$ (its first wires) and fresh workspace and measures designated wires; the outcome is the output ciphertext $\mathsf{ct}'$;
--   4. classical decryption $y=\mathsf{Dec}_{\mathsf{sk}}(\mathsf{ct}')$.
--
--   The evaluated circuits are **classical-output circuits**: $N$ wires, of which the first $k$ hold an auxiliary quantum input; the classical input $x$ is written into designated input wires by $X$ flips; a layered Clifford+T circuit runs and output wires are measured.
--
--   The scheme is **efficient** when $\mathsf{Gen}$, $\mathsf{Enc}$, $\mathsf{Dec}$ and the evaluation-circuit description are polynomial-time computable, the coin counts are polynomial and polynomial-time computable, and (**compactness**) the output ciphertext has length at most a polynomial in $\kappa$ and the output length of $C$, independently of $C$.
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Definition 3.20, pp.23–24 (PDF 24–25); paper.md decision 12

import Definitions.Def_QSampVerif_tup

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms QAlgorithms.Complexity

/-- A quantum circuit with classical input and classical output, as evaluated by a QFHE scheme
(Definition 3.20, p.23: "a quantum circuit C of depth at most L on the encrypted input and an
auxiliary quantum input ρ"; "For circuits with classical outputs"). It has `N` wires: the first
`k` wires hold the auxiliary quantum input, the classical input `x` is written into the wires
`inW` by `X` flips, all other wires start in `|0⟩`; the layered Clifford+T circuit `circ` runs and
the wires `outW` are measured, giving the classical output. -/
structure COCircuit where
  /-- Number of wires. -/
  N : ℕ
  /-- Number of auxiliary-input wires (the first `k` wires). -/
  k : ℕ
  /-- Classical-input wires. -/
  inW : List (Fin N)
  /-- The circuit. -/
  circ : Layered N
  /-- Measured output wires. -/
  outW : List (Fin N)

namespace COCircuit

/-- Well formed: the auxiliary register fits, input wires are distinct and outside the auxiliary
register, output wires are distinct, gates of a layer are disjoint. -/
def Valid (C : COCircuit) : Prop :=
  C.k ≤ C.N ∧ C.inW.Nodup ∧ (∀ i ∈ C.inW, C.k ≤ i.val) ∧ C.outW.Nodup ∧
    ∀ l ∈ C.circ, LayerOk l

/-- The size of the circuit: wires, input wires, instructions and output wires. -/
def size (C : COCircuit) : ℕ := C.N + C.inW.length + numInstr C.circ + C.outW.length

/-- The classical description of the circuit, as given to `Eval`. -/
def code (C : COCircuit) : Str :=
  tup [unary C.N, unary C.k, wireList C.inW, encCirc C.circ, wireList C.outW]

end COCircuit

/-- The quantum part of a homomorphic evaluation: a circuit on `N` wires whose first `k` wires
receive the auxiliary input of the evaluated circuit (`k` is that circuit's `COCircuit.k`), the
rest starting in `|0⟩`; the wires `outW` are measured, and the outcome is the output ciphertext. -/
structure EvalCircuit where
  /-- Number of wires. -/
  N : ℕ
  /-- The circuit. -/
  circ : Layered N
  /-- The measured wires (the output ciphertext). -/
  outW : List (Fin N)

/-- The classical description of an evaluation circuit. -/
def EvalCircuit.encode (E : EvalCircuit) : Str :=
  tup [unary E.N, encCirc E.circ, wireList E.outW]

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Definition 3.20 (Quantum fully homomorphic encryption), pp.23–24 (PDF 24–25).

A leveled QFHE scheme with classical key generation and encryption:
* `gen κ L g = (sk, ek)` with `genCoins κ L` coins `g` ("Gen(1^κ, 1^L)");
* `enc κ sk x e` with `encCoins κ |x|` coins `e` ("Enc_sk(x)");
* `eval ek ⟨C⟩ ct`, the circuit run on the auxiliary input ("Eval_ek(C, ct, ρ)"); its measured
  outcome is the classical output ciphertext;
* `dec sk ct'` ("Dec_sk").

**Formalization Note.** The four algorithms are written out in the mission's circuit model
(paper.md decision 12); efficiency is the separate predicate `QFHEScheme.Efficient`. -/
structure QFHEScheme where
  /-- Number of key-generation coins for `(κ, L)`. -/
  genCoins : ℕ → ℕ → ℕ
  /-- Key generation: `(κ, L, coins) ↦ (sk, ek)`. -/
  gen : ℕ → ℕ → Str → Str × Str
  /-- Number of encryption coins for security parameter `κ` and message length `|x|`. -/
  encCoins : ℕ → ℕ → ℕ
  /-- Encryption: `(κ, sk, x, coins) ↦ ct`. -/
  enc : ℕ → Str → Str → Str → Str
  /-- Homomorphic evaluation: `(ek, ⟨C⟩, ct) ↦` the evaluation circuit. -/
  eval : Str → Str → Str → EvalCircuit
  /-- Decryption: `(sk, ct') ↦ y`. -/
  dec : Str → Str → Str

/-- Definition 3.20, "four efficient algorithms" and item 3 (Compactness): key generation,
encryption and decryption are classical polynomial-time maps; the evaluation circuit is produced
from `(ek, ⟨C⟩, ct)` by a classical polynomial-time map (so `Eval` is uniform quantum polynomial
time); the coin counts are polynomial and polynomial-time computable; and the output ciphertext
has length polynomial in `κ` and the output length of the evaluated circuit, independently of the
circuit, so that decryption takes time polynomial in `κ` and the output length. -/
def QFHEScheme.Efficient (S : QFHEScheme) : Prop :=
  (∃ p : Polynomial ℕ, ∀ κ L : ℕ, S.genCoins κ L ≤ p.eval (κ + L)) ∧
  (∃ p : Polynomial ℕ, ∀ κ ℓ : ℕ, S.encCoins κ ℓ ≤ p.eval (κ + ℓ)) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ κ L : ℕ, f (tup [unary κ, unary L]) = unary (S.genCoins κ L)) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ κ ℓ : ℕ, f (tup [unary κ, unary ℓ]) = unary (S.encCoins κ ℓ)) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ (κ L : ℕ) (g : Str), f (tup [unary κ, unary L, g]) = tup [(S.gen κ L g).1, (S.gen κ L g).2]) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ (κ : ℕ) (sk x e : Str), f (tup [unary κ, sk, x, e]) = S.enc κ sk x e) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ ek c ct : Str, f (tup [ek, c, ct]) = (S.eval ek c ct).encode) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ sk ct : Str, f (tup [sk, ct]) = S.dec sk ct) ∧
  (∃ p : Polynomial ℕ, ∀ (κ L : ℕ) (g : Qubits (S.genCoins κ L)) (C : COCircuit) (x : Str)
      (e : Qubits (S.encCoins κ x.length)),
    (S.eval (S.gen κ L (List.ofFn g)).2 C.code
      (S.enc κ (S.gen κ L (List.ofFn g)).1 x (List.ofFn e))).outW.length ≤
      p.eval (κ + C.outW.length))

end QSampVerif


