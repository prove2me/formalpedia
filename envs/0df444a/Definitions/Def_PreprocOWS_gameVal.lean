-- Prove2me | Definitions.Def_PreprocOWS_gameVal
-- name    : PreprocOWS_gameVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:29:39.359196+00:00
-- url     : https://prove2.me/theorems/30cc6853-83a8-4bb0-803c-9c3f2455373e
-- title:
--   Winning probability of the 1OWS game started from a database state
-- statement:
--   For a state $|\psi\rangle$ on (advice register)$\otimes$(database register) let
--   $$
--   \widehat C_k=\frac1{\sqrt N}\sum_x|x\rangle|0^w\rangle\otimes T_{k,x},
--   $$
--   the isometry that writes a fresh challenge with one compressed query, and
--   $$
--   \mathrm{val}_A(\psi)=\mathbb E_k\,\big\|(\Pi_k\otimes I)\,(\mathsf{cO}\,U)^T\,\widehat C_k\,|\psi\rangle\big\|^2 .
--   $$
--   This is the winning probability of the 1OWS game in which the algorithm starts from $|\psi\rangle$ in the compressed oracle database mode, receives one copy of $|\psi_{R,k}\rangle$ for uniform $k$, makes $T$ queries and guesses $k$.
--
--   Lemma 5.4 bounds it for states supported on small databases.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Reformulation of Lemma 5.3, p.19 (PDF p.22); §5.3, display (7), p.20 (PDF p.23)

import Mathlib
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_cO
open Matrix

namespace PreprocOWS

/-- The isometry `Ĉ_k = (1/√N) ∑_x |x⟩|0^w⟩ ⊗ T_{k,x}`, which writes a fresh challenge with one
compressed query (arXiv:2610.02101, §5.1, p.18, PDF p.21): `|z⟩|D⟩ ↦ N^{-1/2} ∑_x |z,x,0^w⟩|D ⊕ (k,x)⟩`. -/
noncomputable def chatMat {S K N : ℕ} (w : ℕ) (k : Fin K) :
    Matrix (Ω S N w × DB K N) (Fin (2 ^ S) × DB K N) ℂ :=
  Matrix.of fun s a =>
    if s.1.1 = a.1 ∧ s.1.2.2 = wsZero w ∧ s.2 = symmDiff a.2 {(k, s.1.2.1)} then
      ((Real.sqrt N : ℝ) : ℂ)⁻¹ else 0

/-- The **winning probability of the 1OWS game started from a database state** `|ψ⟩` on
(advice register) ⊗ (database register), Dong–Lombardi, arXiv:2610.02101 (version of 2026-11-02,
sha256 7a0bd8da…), Reformulation of Lemma 5.3, p.19 (PDF p.22) and display (7), p.20:
`E_k ‖Π_k (cO U)^T ((1/√N) ∑_x |x⟩ ⊗ T_{k,x}) |ψ⟩|0^w⟩‖²`.

**Formalization Note.** `Π_k` and the unitaries act as the identity on the database register. -/
noncomputable def gameVal {S T K N w : ℕ} (A : Alg S T K N w) (ψ : Fin (2 ^ S) × DB K N → ℂ) : ℝ :=
  (K : ℝ)⁻¹ * ∑ k, vnormSq (liftL (A.proj k) *ᵥ (cRun A *ᵥ (chatMat w k *ᵥ ψ)))

end PreprocOWS


