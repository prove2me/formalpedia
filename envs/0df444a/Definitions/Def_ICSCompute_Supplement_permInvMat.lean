-- Prove2me | Definitions.Def_ICSCompute_Supplement_permInvMat
-- name    : ICSCompute_Supplement_permInvMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T15:06:50.605504+00:00
-- url     : https://prove2.me/theorems/53ec912e-e79c-40f0-bfa5-265923faa191
-- title:
--   The inverse-permutation matrix $U_{\pi^{-1}}$
-- statement:
--   For a map $\pi:\{0,1\}^n\to\{0,1\}^n$, let
--
--   $$U_{\pi^{-1}}:=\sum_{x\in\{0,1\}^n}|x\rangle\langle\pi(x)|,$$
--
--   the $0/1$ matrix whose $(a,b)$ entry is $1$ exactly when $\pi(a)=b$. When $\pi$ is a permutation, $U_{\pi^{-1}}|y\rangle=|\pi^{-1}(y)\rangle$ for every $y$ and $U_{\pi^{-1}}$ is a permutation matrix, hence unitary. It is the generated unitary of the permutation-inversion construction (Theorem 5.3, eq. (5.6)).
--
--   **Formalization Note** The matrix is defined for every map $\pi$; Theorem 5.3 assumes $\pi$ bijective.
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Theorem 5.3, eq. (5.6), p.30 (PDF p.32)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace ICSCompute.Supplement

open QAlgorithms

/-- **The inverse-permutation unitary `U_{π⁻¹}`** (Shmueli, *What Can Be Computed with Indefinite
Causal Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606, Theorem 5.3,
eq. (5.6), p.30 (PDF p.32): `U_{π⁻¹}|y⟩ := |π⁻¹(y)⟩`).

For `π : {0,1}ⁿ → {0,1}ⁿ`, the `0/1` matrix with `(a, b)` entry `1` iff `π(a) = b`, i.e.
`∑_x |x⟩⟨π(x)|`. When `π` is a bijection it sends `|y⟩` to `|π⁻¹(y)⟩` and is a permutation
matrix, hence unitary.

**Formalization Note** Bits are `Bool`, `Qubits n = Fin n → Bool`; the matrix is defined for
every map `π`, and the theorems using it assume `π` bijective. -/
def permInvMat {n : ℕ} (π : Qubits n → Qubits n) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun a b => if π a = b then 1 else 0

end ICSCompute.Supplement


