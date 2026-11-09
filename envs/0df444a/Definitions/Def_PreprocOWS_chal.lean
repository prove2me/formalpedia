-- Prove2me | Definitions.Def_PreprocOWS_chal
-- name    : PreprocOWS_chal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:22:01.086203+00:00
-- url     : https://prove2.me/theorems/e10c7477-044d-4c96-8d89-cabfc77f985c
-- title:
--   Binary phase state $|\psi_{R,k}\rangle$ and the input embedding
-- statement:
--   The **challenge** is the binary phase state
--   $$
--   |\psi_{R,k}\rangle:=\frac1{\sqrt N}\sum_{x\in[N]}R(k,x)\,|x\rangle .
--   $$
--   The input of the game with advice $|\varphi\rangle\in\mathbb C^{2^S}$ is $|\varphi\rangle\otimes|\psi_{R,k}\rangle\otimes|0^w\rangle$; the linear map $J_{R,k}:|\varphi\rangle\mapsto|\varphi\rangle|\psi_{R,k}\rangle|0^w\rangle$ is an isometry from the advice register to $\mathbb C^{\Omega}$.
--
--   The key $k$ is hidden in the signs of the phase state; recovering it is the 1OWS inversion task.
--
--   **Formalization Note** `embed w R k` is the matrix of $J_{R,k}$, indexed by $\Omega$ and $[2^S]$.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Definition 5.1, p.16 (PDF p.19); §5.1, p.17 (PDF p.20)

import Mathlib
import Definitions.Def_PreprocOWS_Oracle
import Definitions.Def_PreprocOWS_Alg
open Matrix

namespace PreprocOWS

/-- The **binary phase state** `|ψ_{R,k}⟩ := N^{-1/2} ∑_x R(k,x) |x⟩` (the challenge), Dong–Lombardi,
*Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of
2026-11-02, sha256 7a0bd8da…), Definition 5.1, p.16 (PDF p.19).

**Formalization Note.** `Real.sqrt N` with `N ≥ 1` in every statement. -/
noncomputable def chal {K N : ℕ} (R : Oracle K N) (k : Fin K) : Fin N → ℂ :=
  fun x => ((Real.sqrt N : ℝ) : ℂ)⁻¹ * sgn (R (k, x))

/-- The isometry `J_{R,k} : |φ⟩ ↦ |φ⟩ ⊗ |ψ_{R,k}⟩ ⊗ |0^w⟩` placing the advice, the challenge and the
all-zero workspace (arXiv:2610.02101, §5.1, p.17, PDF p.20), as a matrix from the advice register
`[2^S]` to `Ω = [2^S] × [N] × [2^w]`. -/
noncomputable def embed {S K N : ℕ} (w : ℕ) (R : Oracle K N) (k : Fin K) :
    Matrix (Ω S N w) (Fin (2 ^ S)) ℂ :=
  Matrix.of fun s z => if s.1 = z ∧ s.2.2 = wsZero w then chal R k s.2.1 else 0

end PreprocOWS


