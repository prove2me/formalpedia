-- Prove2me | Definitions.Def_PreprocOWS_Ymat
-- name    : PreprocOWS_Ymat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:26:49.617632+00:00
-- url     : https://prove2.me/theorems/88744219-f547-4bc2-a59b-cf6e3d1ec34b
-- title:
--   The matrix $Y_R$ on the advice register
-- statement:
--   For an algorithm $A$ and an oracle $R$,
--   $$
--   Y_R:=\mathbb E_k\,\langle\psi_{R,k}|\langle0|_{\mathsf W}\,(U^\dagger O_R^\dagger)^T\,\Pi_k\,(O_RU)^T\,|\psi_{R,k}\rangle|0\rangle_{\mathsf W}
--   =\frac1K\sum_k J_{R,k}^\dagger\,\big((O_RU)^T\big)^\dagger\,\Pi_k\,(O_RU)^T\,J_{R,k},
--   $$
--   a $2^S\times2^S$ matrix on the advice register.
--
--   Its operator norm is the best winning probability for the oracle $R$ (display (4)); the proof of Theorem 5.2 bounds $\mathbb E_R\|Y_R\|$ by trace moments.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.1, display (4), p.17 (PDF p.20)

import Mathlib
import Definitions.Def_PreprocOWS_run
import Definitions.Def_PreprocOWS_chal
open Matrix

namespace PreprocOWS

/-- The matrix `Y_R := E_k ⟨ψ_{R,k}|⟨0|_W (U†O_R†)^T Π_k (O_R U)^T |ψ_{R,k}⟩|0⟩_W` on the advice
register, Dong–Lombardi, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), display (4), p.17 (PDF p.20), written
`Y_R = (1/K) ∑_k J_{R,k}† (O_R U)^{T†} Π_k (O_R U)^T J_{R,k}` with `J_{R,k}` = `embed w R k`. -/
noncomputable def Ymat {S T K N w : ℕ} (A : Alg S T K N w) (R : Oracle K N) :
    Matrix (Fin (2 ^ S)) (Fin (2 ^ S)) ℂ :=
  (K : ℂ)⁻¹ • ∑ k, (embed (S := S) w R k)ᴴ * (run A R)ᴴ * A.proj k * run A R * embed (S := S) w R k

end PreprocOWS


