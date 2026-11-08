-- Prove2me | Definitions.Def_ProofCryptoSynergy_PiFamily
-- name    : ProofCryptoSynergy_PiFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:06:37.510786+00:00
-- url     : https://prove2.me/theorems/9ba03e72-cd92-4a7d-ad0d-c41ac7f1c8ca
-- title:
--   Families $R_c(\psi)=\forall w\,P_c(\psi,w)$
-- statement:
--   A family of formulas $R_c(\psi)=\forall w\,P_c(\psi,w)$, $c\ge1$, where $|w|\le 2^{|\psi|^{1/c}}$ and $P_c(\psi,w)$ is computable in time $2^{O(|\psi|^{1/c})}$.
--
--   **Formalization Note** One machine computes $P_c(\psi,w)$ from $(1^c,\psi,w)$, and the constant in the exponent may depend on $c$. The printed proof of Lemma 29 needs one machine, because its proof system $L_R$ checks transcripts of $P_c$ for $c$ given in the proof.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 29, p.25 (PDF 27)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_TAUT
import Definitions.Def_KarpLiptonOM_OracleTM_Accepts

open KarpLiptonOM LaconicBarrier

namespace ProofCryptoSynergy

/-- A family of formulas `R_c(ψ) = ∀w P_c(ψ, w)`, indexed by `c ≥ 1` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 29, p.25 (PDF 27)), computed by one machine
`M` on `(1^c, ψ, w)` with time constants `a c`.

**Formalization Note** The family is uniform: one machine for all `c`. The printed proof needs this, because `L_R` (p.26) is
one polynomial-time proof system checking transcripts of `P_c` for `c` given in the proof. -/
structure PiFamily where
  /-- the machine computing `P_c(ψ, w)` from `(1^c, ψ, w)` -/
  M : OracleTM
  /-- the constant in `2^{O(|ψ|^{1/c})}` -/
  a : ℕ → ℕ

/-- `P_c(ψ, w)`, for `|w| ≤ 2^{|ψ|^{1/c}}`, is computable in time `2^{O(|ψ|^{1/c})}`, for every `c ≥ 1` and `ψ` nonempty. -/
def PiFamily.TimeBounded (F : PiFamily) : Prop :=
  ∀ c : ℕ, 1 ≤ c → ∀ ψ w : List Bool, 1 ≤ ψ.length →
    (w.length : ℝ) ≤ (2 : ℝ) ^ ((ψ.length : ℝ) ^ (1 / (c : ℝ))) →
    ∃ t : ℕ, (t : ℝ) ≤ (2 : ℝ) ^ ((F.a c : ℝ) * (ψ.length : ℝ) ^ (1 / (c : ℝ))) ∧
      F.M.HaltsWithin ∅ t (tupleEnc [unary c, ψ, w])

/-- `R_c(ψ) = ∀w P_c(ψ, w)`, the quantifier over `|w| ≤ 2^{|ψ|^{1/c}}`. -/
def PiFamily.R (F : PiFamily) (c : ℕ) (ψ : List Bool) : Prop :=
  ∀ w : List Bool, (w.length : ℝ) ≤ (2 : ℝ) ^ ((ψ.length : ℝ) ^ (1 / (c : ℝ))) →
    F.M.Accepts ∅ (tupleEnc [unary c, ψ, w])

end ProofCryptoSynergy


