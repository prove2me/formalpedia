-- Prove2me | Definitions.Def_NearOptOWF_PPRF
-- name    : NearOptOWF_PPRF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:15.069031+00:00
-- url     : https://prove2.me/theorems/9edd1887-6a16-43ee-9197-911c8747c486
-- title:
--   Puncturable PRF (syntax)
-- statement:
--   A **puncturable pseudorandom function** is a keyed family $F_k$ together with a puncturing algorithm $k \mapsto k\{x^*\}$, which produces a punctured key for a point $x^*$, and an evaluation circuit for punctured keys. The paper uses the primitive without defining it; the syntax is the standard one of Sahai–Waters and Canetti–Chen–Reyzin.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemmas 3.5–3.6, p.9 (PDF p.11); Theorem 4.1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_NearOptOWF_KeyedFam

namespace NearOptOWF

open LaconicBarrier

/-- The syntax of a **puncturable PRF** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 3.5 and Lemma 3.6, p.9 (PDF p.11); Theorem
4.1, p.11 (PDF p.13); the paper names the primitive without defining it, so the standard
Sahai–Waters syntax is used): a keyed family `F_k` together with `Puncture(k, x*)`, returning a
punctured key `k{x*}`, and the punctured evaluation circuit `pcirc λ n m k{x*}`.

**Formalization Note** Keys are uniform bit strings (`KeyedFam.keyLen`); punctured keys are bit
strings. -/
structure PPRF extends KeyedFam where
  /-- `Puncture(k, x*)`: the punctured key `k{x*}` -/
  punc : (lam n m : ℕ) → (Fin (keyLen lam n m) → Bool) → List Bool → List Bool
  /-- the circuit evaluating a punctured key -/
  pcirc : (lam n m : ℕ) → List Bool → MCircuit n

end NearOptOWF


