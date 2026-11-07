-- Prove2me | Definitions.Def_QiOPoQ_IOPpoly
-- name    : QiOPoQ_IOPpoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:40.871794+00:00
-- url     : https://prove2.me/theorems/f7c06d5a-5a52-4f26-9b90-75f981f40541
-- title:
--   Definition 4.2: i.o.P/poly
-- statement:
--   A language $L$ is in **i.o.P/poly** if there is a non-uniform probabilistic polynomial-time algorithm $M$ such that, for infinitely many input lengths $\lambda$, every $x\in\{0,1\}^\lambda$ satisfies
--
--   $$
--   \Pr[M(x)=L(x)]\ge\frac23.
--   $$
--
--   The assumption $\mathsf{BQP}\not\subseteq$ i.o.P/poly is what Theorem 4.7 uses: it is slightly stronger than $\mathsf{BQP}\neq\mathsf{BPP}$, because an adversary breaks a cryptographic scheme as soon as it succeeds on infinitely many lengths, with advice.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Definition 4.2, p.18

import Mathlib
import Definitions.Def_QiOPoQ_NUPPT

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms.Complexity

open Classical in
/-- **Definition 4.2 (Infinitely-often P/poly).** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable
Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256
fe2f9210…), Definition 4.2, p.18: "A language L is in i.o.P/poly if there is a non-uniform
probabilistic polynomial-time algorithm M such that, for infinitely many input lengths λ, every
x ∈ {0, 1}^λ satisfies Pr[M(x) = L(x)] ≥ 2/3."

**Formalization Note.** `M` is a `NUPPT` (polynomially bounded advice) run on `(1^λ, x)` with
`λ = |x|`; it outputs the bit `L(x)` as the one-letter string `[decide (x ∈ L)]`. "For infinitely
many λ" is `∀ N, ∃ λ ≥ N`. -/
def IOPpoly (L : Set Str) : Prop :=
  ∃ M : NUPPT, ∀ N : ℕ, ∃ n ≥ N, ∀ x : Str, x.length = n →
    (2 / 3 : ℝ) ≤ M.expect n x fun o => if o = [decide (x ∈ L)] then 1 else 0

end QiOPoQ


