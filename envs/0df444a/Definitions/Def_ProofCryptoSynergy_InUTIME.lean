-- Prove2me | Definitions.Def_ProofCryptoSynergy_InUTIME
-- name    : ProofCryptoSynergy_InUTIME
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:04:02.334344+00:00
-- url     : https://prove2.me/theorems/59eabdd3-1d10-4778-9d98-3a1010f19a66
-- title:
--   $\mathsf{UTIME}[T]$, $\mathsf{UP}$, $\mathsf{UTIME}[n^{\mathrm{polylog}(n)}]$, $\mathsf{NP}$ and $\mathsf{coNP}\not\subseteq\mathsf{io\text-NP}$
-- statement:
--   $L\in\mathsf{UTIME}[T]$ if one deterministic checker, on $(w,y)$ with $|y|\le T(|w|)$, halts within $T(|w|)$ steps, accepts exactly one such $y$ if $w\in L$, and accepts none if $w\notin L$. $\mathsf{UP}$ takes $T(n)=n^k+k$ and $\mathsf{UTIME}[n^{\mathrm{polylog}(n)}]$ takes $T(n)=2^{(\log_2(n+2))^k}$, for some $k$.
--
--   $\mathsf{NP}$ is the same with "$w\in L$ iff some $y$ is accepted". $L\in\mathsf{io\text-NP}$ if some language in $\mathsf{NP}$ agrees with $L$ at infinitely many lengths, and $\mathsf{coNP}\not\subseteq\mathsf{io\text-NP}$ says some $L$ with $L^c\in\mathsf{NP}$ is not in $\mathsf{io\text-NP}$.
--
--   **Formalization Note** Unique accepting paths correspond to unique witnesses. io-NP is used by the paper without definition; this is the standard one.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.5 (PDF 7); Lemma 35, p.31 (PDF 33); Corollary 45, p.38 (PDF 40)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_OracleTM_Accepts
import Definitions.Def_KarpLiptonOM_tupleEnc

open KarpLiptonOM

namespace ProofCryptoSynergy

/-- `L ∈ UTIME[T]`, in witness form (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.5 (PDF 7): "solvable by a nondeterministic polynomial-time
Turing machine that never has more than one accepting computation path"; Corollary 45, p.38 (PDF 40)): one
deterministic checker, run on `(w, y)` with `|y| ≤ T(|w|)`, halts within `T(|w|)` steps; if `w ∈ L` it accepts
exactly one such `y`; if `w ∉ L` it accepts none.

**Formalization Note** Unique accepting paths correspond to unique witnesses (a witness is the path's
sequence of guesses). Time is measured in `|w|`, as for a nondeterministic machine on input `w`. Machines are
the published `KarpLiptonOM.OracleTM` with the empty oracle. -/
def InUTIME (T : ℕ → ℕ) (L : Set (List Bool)) : Prop :=
  ∃ M : OracleTM,
    (∀ w y : List Bool, y.length ≤ T w.length → M.HaltsWithin ∅ (T w.length) (tupleEnc [w, y])) ∧
    (∀ w ∈ L, ∃! y : List Bool, y.length ≤ T w.length ∧ M.Accepts ∅ (tupleEnc [w, y])) ∧
    (∀ w ∉ L, ∀ y : List Bool, y.length ≤ T w.length → ¬ M.Accepts ∅ (tupleEnc [w, y]))

/-- `L ∈ UP` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.5 (PDF 7)): `L ∈ UTIME[nᵏ + k]` for some `k`. -/
def InUP (L : Set (List Bool)) : Prop := ∃ k : ℕ, InUTIME (fun n => n ^ k + k) L

/-- `L ∈ UTIME[n^{polylog(n)}]` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Corollary 45, item 1, p.38 (PDF 40)): `L ∈ UTIME[2^{(log₂(n+2))^k}]`
for some `k`.

**Formalization Note** `n^{polylog(n)} = 2^{polylog(n)}`; `n + 2` and the floor of the logarithm only avoid the
degenerate small `n`. -/
def InQuasiU (L : Set (List Bool)) : Prop :=
  ∃ k : ℕ, InUTIME (fun n => 2 ^ (Nat.log 2 (n + 2)) ^ k) L

/-- `L ∈ NTIME[T]` in witness form: one deterministic checker on `(w, y)`, `|y| ≤ T(|w|)`, halting within
`T(|w|)` steps, with `w ∈ L` iff it accepts some such `y`. The class NP, used by Lemma 35 of
Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.31 (PDF 33). -/
def InNTIME (T : ℕ → ℕ) (L : Set (List Bool)) : Prop :=
  ∃ M : OracleTM,
    (∀ w y : List Bool, y.length ≤ T w.length → M.HaltsWithin ∅ (T w.length) (tupleEnc [w, y])) ∧
    (∀ w, w ∈ L ↔ ∃ y : List Bool, y.length ≤ T w.length ∧ M.Accepts ∅ (tupleEnc [w, y]))

/-- `L ∈ NP`. -/
def InNP (L : Set (List Bool)) : Prop := ∃ k : ℕ, InNTIME (fun n => n ^ k + k) L

/-- `L ∈ io-NP`: some language in NP agrees with `L` at infinitely many input lengths.

**Formalization Note** The paper uses io-NP without defining it (Lemma 35, p.31); this is the standard
definition. The agreeing language is in NP at all lengths. -/
def InIoNP (L : Set (List Bool)) : Prop :=
  ∃ A, InNP A ∧ {n : ℕ | ∀ x : List Bool, x.length = n → (x ∈ A ↔ x ∈ L)}.Infinite

/-- **`coNP ⊄ io-NP`** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 35, hypothesis 2, p.31 (PDF 33)): some language with its complement in
NP is not in io-NP. -/
def CoNPNotIoNP : Prop := ∃ L : Set (List Bool), InNP Lᶜ ∧ ¬ InIoNP L

end ProofCryptoSynergy


