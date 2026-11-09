-- Prove2me | Definitions.Def_NKtLB_MnKtP
-- name    : NKtLB_MnKtP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:09:18.166448+00:00
-- url     : https://prove2.me/theorems/2ff4f302-ef80-4c8f-a073-02773e5a32d9
-- title:
--   The problem MnKtP
-- statement:
--   **MnKtP** is the problem: given $(x,1^s)$ with $x\in\{0,1\}^*$ and $s\in\mathbb N$, decide whether $\mathrm{nKt}(x)\le s$ ("yes" case) or $\mathrm{nKt}(x)>s$ ("no" case). As a language it is
--   $$
--   \mathrm{MnKtP}=\{\langle x,1^s\rangle : \mathrm{nKt}(x)\le s\},
--   $$
--   and strings that encode no pair are not in it.
--
--   **Formalization Note** $\mathrm{nKt}$ is taken with respect to the universal machine $U$, with no oracle and empty auxiliary and random strings. The pair encoding is `pairEnc`.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §1.2.4, p.12

import Mathlib
import Definitions.Def_NKtLB_nKt
import Definitions.Def_NKtLB_pairEnc

namespace NKtLB

/-- **MnKtP** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §1.2.4, p.12): "Given `(x, 1^s)`, where `x ∈ {0,1}^*` and `s ∈ ℕ`, decide
whether `nKt(x) ≤ s` ("yes" case) or `nKt(x) > s` ("no" case)." As a language: the encodings
`pairEnc x s` with `nKt(x) ≤ s`; strings that encode no pair are not in it.

**Formalization Note.** `nKt(x)` is unrelativized (`O = ∅`, no query bound), with empty auxiliary
and randomness strings, relative to the universal machine `U`. -/
def MnKtP (U : Machine) : Set (List Bool) :=
  {z | ∃ (x : List Bool) (s : ℕ), z = pairEnc x s ∧ nKt U ∅ ⊤ x [] [] ≤ s}

end NKtLB


