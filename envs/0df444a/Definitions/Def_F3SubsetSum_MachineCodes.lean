-- Prove2me | Definitions.Def_F3SubsetSum_MachineCodes
-- name    : F3SubsetSum_MachineCodes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:36.537508+00:00
-- url     : https://prove2.me/theorems/cb140c41-9269-4292-b1d6-a1a7e5cbcf0c
-- title:
--   Instance and secret codes for Binary-Error LWE machines, and "Dec runs in time $T$"
-- statement:
--   The paper's algorithms name no machine model. A **classical machine** is a deterministic multi-stack Turing machine with input and output alphabet $\{0,1\}$ (Mathlib's `TM2ComputableAux Bool Bool`), and "$M$ outputs $w$ on input $u$ within $T$ steps" is the published `HMBinPacking.OutputsWithin`.
--
--   Binary-Error LWE instances are written for the machine as follows: $1^n0\,1^m0$, then the columns $a_1,\dots,a_m$ of $A$ (each as its $n$ entries), then $b_1,\dots,b_m$, every entry $v\in\{0,\dots,q-1\}$ written $1^v0$. A secret $s\in\mathbb F_q^n$ is written as its entries $1^{s_1}0\cdots1^{s_n}0$. A machine **computes the decoder Dec on all $(n,m)$-inputs within $T$ steps** if on the code of every $(A,b)\in\mathbb F_q^{n\times m}\times\mathbb F_q^m$ it outputs the code of $\mathrm{Dec}(A,b)$ within $T$ steps.
--
--   This is the meaning given to "a deterministic classical algorithm that runs in time $T$" (Theorems 1.7 and 3.1); the unary codes $1^k$ and $1^k0$ also form the inputs of the circuit generators of Theorems 1.3 and 3.1.
--
--   **Formalization Note** Turing machines and RAMs differ by polynomial factors, which every time bound of the paper absorbs (p.22). The numbers $n$, $m$ are part of the input so that one machine handles every size.
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Theorem 1.7, p.6; Theorem 3.1, p.13; proof of Theorem 1.7, p.22

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_F3SubsetSum_BinaryErrorLWE

namespace F3SubsetSum

/-- The unary code `1ᵏ` of a natural number. -/
def unary (k : ℕ) : List Bool := List.replicate k true

/-- The self-delimiting unary code `1ᵏ 0`. -/
def unaryD (k : ℕ) : List Bool := unary k ++ [false]

/-- **Input code of a Binary-Error LWE instance** `(A, b) ∈ F_q^{n×m} × F_q^m` (Kothari, Metger,
O'Donnell, Shutty, Wu, arXiv:2609.40321v1, Problem 1.5, p.5): `1ⁿ 0 1ᵐ 0`, then the columns
`a_1, …, a_m` of `A` (each as its `n` entries in order), then `b_1, …, b_m`; every entry
`v ∈ F_q` is written `1^v 0` with `v ∈ {0, …, q − 1}`.

**Formalization Note** `n` and `m` are part of the input, so that a single machine can parse
instances of every size. -/
def encodeInstance {q n m : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) :
    List Bool :=
  unaryD n ++ unaryD m ++
    (List.finRange m).flatMap (fun i => (List.finRange n).flatMap (fun j => unaryD (A j i).val)) ++
    (List.finRange m).flatMap (fun i => unaryD (b i).val)

/-- **Output code of a secret** `s ∈ F_q^n`: the entries `s_1, …, s_n`, each written `1^v 0`. -/
def encodeSecret {q n : ℕ} (s : Fin n → ZMod q) : List Bool :=
  (List.finRange n).flatMap (fun j => unaryD (s j).val)

/-- **`M` computes the decoder `Dec` on all `(n, m)`-inputs within `T` steps** (Theorem 1.7,
p.6; Theorem 3.1, p.13: "Dec … runs in time T"). `M` is a deterministic multi-stack Turing
machine with Boolean input and output alphabets (Mathlib's `Turing.TM2ComputableAux Bool Bool`);
on the code of every `(A, b) ∈ F_q^{n×m} × F_q^m` it halts within `T` steps with the code of
`Dec(A, b)` on its output stack (the published `HMBinPacking.OutputsWithin`).

**Formalization Note** The paper names no machine model. A Turing machine and a RAM differ by
polynomial factors, which every time bound of the paper absorbs (p.22: "every polynomial factor in
n, m is g^{O_κ(h)}"). -/
def ComputesWithin {q : ℕ} (M : Turing.TM2ComputableAux Bool Bool) (Dec : DecoderFn q)
    (n m T : ℕ) : Prop :=
  ∀ (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q),
    HMBinPacking.OutputsWithin M (encodeInstance A b) (encodeSecret (Dec n m A b)) T

end F3SubsetSum


