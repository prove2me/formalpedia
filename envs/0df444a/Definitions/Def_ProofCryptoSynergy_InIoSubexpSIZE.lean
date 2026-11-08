-- Prove2me | Definitions.Def_ProofCryptoSynergy_InIoSubexpSIZE
-- name    : ProofCryptoSynergy_InIoSubexpSIZE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:04:51.208124+00:00
-- url     : https://prove2.me/theorems/0a4c5d24-113d-41e7-a6d3-195008462ec1
-- title:
--   $\mathsf{io\text-SIZE}[2^{n^{o(1)}}]$
-- statement:
--   $L\in\mathsf{io\text-SIZE}[2^{n^{o(1)}}]$ if there is a subexponential $s$ such that for infinitely many $n$ some circuit with $n$ inputs and at most $s(n)$ gates decides $L$ on $\{0,1\}^n$. Hence $L\notin\mathsf{io\text-SIZE}[2^{n^{o(1)}}]$ means that for every subexponential $s$, for all but finitely many $n$, $L$ on $\{0,1\}^n$ has no circuit of size at most $s(n)$.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.5 (PDF 7)

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit_eval
import Definitions.Def_ProofCryptoSynergy_IsSubexp

open KarpLiptonOM

namespace ProofCryptoSynergy

/-- `L` has circuits of size `s` infinitely often (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.5 (PDF 7)): for infinitely many `n` there is a
circuit with `n` inputs and at most `s(n)` gates deciding `L` on `{0,1}ⁿ`. -/
def InIoSIZE (L : Set (List Bool)) (s : ℕ → ℝ) : Prop :=
  {n : ℕ | ∃ C : Circuit n, (C.gates.length : ℝ) ≤ s n ∧
    ∀ x : List Bool, x.length = n → (C.eval x = true ↔ x ∈ L)}.Infinite

/-- `L ∈ io-SIZE[2^{n^{o(1)}}]` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.5 (PDF 7): "the class of problems decidable by nonuniform boolean
circuits of size `2^{n^{o(1)}}` infinitely often").

**Formalization Note** So `L ∉ io-SIZE[2^{n^{o(1)}}]` says: for every subexponential `s`, for all but finitely
many `n`, `L` on `{0,1}ⁿ` has no circuit of size at most `s(n)`. -/
def InIoSubexpSIZE (L : Set (List Bool)) : Prop := ∃ s, IsSubexp s ∧ InIoSIZE L s

end ProofCryptoSynergy


