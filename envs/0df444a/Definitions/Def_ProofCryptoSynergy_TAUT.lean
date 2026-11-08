-- Prove2me | Definitions.Def_ProofCryptoSynergy_TAUT
-- name    : ProofCryptoSynergy_TAUT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:04:51.108919+00:00
-- url     : https://prove2.me/theorems/9db4a63c-dd8a-4de9-a96d-d90001a63f35
-- title:
--   $\mathrm{TAUT}$, $\mathrm{SAT}$, $\varphi(w)=1$, $\varphi\vee\psi$ and P-uniform unsatisfiable sequences
-- statement:
--   $\mathrm{TAUT}$ is the set of strings reading as tautologies and $\mathrm{SAT}$ the set of strings reading as satisfiable formulas. For strings $\varphi,w$, $\varphi(w)=1$ means that $\varphi$ holds when $x_i$ takes the $i$-th bit of $w$ (false beyond its end). $\varphi\vee\psi$ is the shortest string reading as the disjunction.
--
--   A **P-uniform sequence of unsatisfiable formulas $\psi_n$ of size $n$** is one with $|\psi_n|=n$, $\psi_n\notin\mathrm{SAT}$, and a deterministic polynomial-time algorithm $G$ with $G(1^n)=\psi_n$.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), §2.2, pp.18–19 (PDF 20–21); Definition 14, p.20 (PDF 22); Definition 31, p.29 (PDF 31)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_Formula
import Definitions.Def_LaconicBarrier_PolyTimeOn

open LaconicBarrier

namespace ProofCryptoSynergy

/-- `TAUT`, the language of propositional tautologies (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), §2.2, p.18 (PDF 20)). -/
def TAUT : Set (List Bool) := {x | ∀ a, (decode x).eval a = true}

/-- `SAT`, the language of satisfiable formulas (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), §2.2, p.18 (PDF 20)). -/
def SAT : Set (List Bool) := {x | ∃ a, (decode x).eval a = true}

/-- `φ(w) = 1`: the string `w` is a satisfying assignment of the formula `φ`; `x_i` takes the `i`-th bit
of `w`, and `false` beyond its end (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 14, p.20 (PDF 22)). -/
def holds (φ w : List Bool) : Prop := (decode φ).eval (fun i => w.getD i false) = true

/-- The disjunction `φ ∨ ψ` of two formulas, as a string (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 31, p.29 (PDF 31)). -/
def orStr (φ ψ : List Bool) : List Bool := canon (.or (decode φ) (decode ψ))

/-- A **P-uniform sequence of unsatisfiable formulas `ψ_n`, of size `n`**: one deterministic
polynomial-time algorithm `G` with `G(1ⁿ) = ψ_n` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), §2.2, p.19 (PDF 21)).

**Formalization Note** `ψ_0` is the empty string, which is unsatisfiable; the source's `n ≥ 1` costs nothing. -/
def IsPUniformUnsat (ψ : ℕ → List Bool) : Prop :=
  (∀ n, (ψ n).length = n) ∧ (∀ n, ψ n ∉ SAT) ∧
    PolyTimeOn (ι := ℕ) (fun n => [unary n]) ψ

end ProofCryptoSynergy


