-- Prove2me | Definitions.Def_CertRandQROM_Supplement_proofBits
-- name    : CertRandQROM_Supplement_proofBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:44:01.605819+00:00
-- url     : https://prove2.me/theorems/4a8c6473-e304-448f-86e3-5fb1178a9c09
-- title:
--   Binary codes of symbols, words, oracle inputs and proofs
-- statement:
--   Given a code $\mathrm{enc}:K\to\{0,1\}^e$ of field elements:
--
--   1. a symbol $s\in\Sigma=K^m$ is written as the $m\cdot e$ bits $\mathrm{enc}(s_0)\cdots\mathrm{enc}(s_{m-1})$;
--   2. a word $x\in\Sigma^n$ as the concatenation of its $n$ symbols;
--   3. an index $i\in[n]$ in binary, least significant bit first, on as many bits as $n$ has binary digits;
--   4. an oracle input $(i,x)\in[n]\times\Sigma$ as the index followed by the symbol;
--   5. a proof $\pi\in\Sigma^n\cup\{\bot\}$ as a flag bit followed by $n\cdot m\cdot e$ bits: $0$ and the word for $\pi=x$, $1$ and zeros for $\pi=\bot$.
--
--   A string is **parsed** as the word $x$ if it is $0$ followed by the code of $x$, and as $\bot$ otherwise (flag $1$, wrong length, or not a code).
--
--   These codes are how the classical proof and the oracle queries of the protocol appear on wires and tapes in the syntax property.
--
--   **Formalization Note** `symBits`, `wordBits`, `idxBits`, `domBits`, `proofBits` are the five codes and `proofOfBits` the parser, which picks the word by choice; it is unique when `enc` is injective.
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Definition 6.1, Syntax, p.27 (PDF p.29); Construction 6.2, Verify, step 1, p.29 (PDF p.31); §6.2, Biased Random Oracle, p.28 (PDF p.30)

import Mathlib

set_option autoImplicit false

namespace CertRandQROM.Supplement

variable {K : Type} {e n m : ℕ}

/-- The bit string of a symbol `s ∈ Σ = F_q^m`: the codes `enc (s_0), …, enc (s_{m−1})` of its
`m` field coordinates, concatenated (`m·e` bits). Coladangelo et al., arXiv:2608.31112
(sha256 b75095a2…), §5.2, p.23 (`Σ = F_q^m`); Definition 6.1, p.27 (classical proofs and oracle
queries are strings). -/
def symBits (enc : K → Fin e → Bool) (s : Fin m → K) : List Bool :=
  (List.ofFn fun j : Fin m => List.ofFn (enc (s j))).flatten

/-- The bit string of a word `x ∈ Σ^n`: the strings of `x_0, …, x_{n−1}`, concatenated
(`n·m·e` bits). -/
def wordBits (enc : K → Fin e → Bool) (x : Fin n → Fin m → K) : List Bool :=
  (List.ofFn fun i : Fin n => symBits enc (x i)).flatten

/-- The index `i ∈ [n]` (0-based) in binary, least significant bit first, on `Nat.size n` bits
(the number of binary digits of `n`, so that every `i < n` fits). -/
def idxBits (n : ℕ) (i : Fin n) : List Bool :=
  List.ofFn fun j : Fin (Nat.size n) => i.val.testBit j.val

/-- The bit string of an oracle input `(i, x) ∈ [n] × Σ` (§6.2, p.28: "functions mapping
`[n] × Σ → {0,1}`"): the index in binary followed by the symbol. -/
def domBits (enc : K → Fin e → Bool) (u : Fin n × (Fin m → K)) : List Bool :=
  idxBits n u.1 ++ symBits enc u.2

/-- **The bit string of a proof `π ∈ Σ^n ∪ {⊥}`** (Construction 6.2, pp.28–29): one flag bit
(`true` = `⊥`) followed by `n·m·e` bits, the word for `π = x` and zeros for `π = ⊥`. -/
def proofBits (enc : K → Fin e → Bool) : Option (Fin n → Fin m → K) → List Bool
  | none => true :: List.replicate (n * m * e) false
  | some x => false :: wordBits enc x

open Classical in
/-- **Parsing a proof** (Construction 6.2, Verify, step 1, p.29: "If `π = ⊥`, then output `⊥` and
halt. Otherwise, parse `π = x = (x_1, …, x_n)`"): a string `0 ++ wordBits x` is the word `x`;
every other string (flag `1`, wrong length, or not the string of a word) is `⊥` (`none`).

**Formalization Note** The word is chosen with `Classical.choose`; when `enc` is injective
(as for a `FieldPres` at `λ ≥ 2`) it is unique. -/
noncomputable def proofOfBits (enc : K → Fin e → Bool) (s : List Bool) :
    Option (Fin n → Fin m → K) :=
  if h : ∃ x : Fin n → Fin m → K, s = false :: wordBits enc x then some h.choose else none

end CertRandQROM.Supplement


