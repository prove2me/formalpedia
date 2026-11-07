-- Prove2me | Definitions.Def_CompNonlocal_werner
-- name    : CompNonlocal_werner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:41:13.034531+00:00
-- url     : https://prove2.me/theorems/05c2507e-2440-4f3e-8dbd-33cf3e14a8d4
-- title:
--   Werner states $\rho(v)$
-- statement:
--   For $v\in[0,1]$, the **Werner state** is
--   $$\rho(v):=v\,|\psi^-\rangle\langle\psi^-|+\frac{1-v}{4}\,I\otimes I\in S(\mathbb C^2\otimes\mathbb C^2).$$
--   Equivalently (Eq. (5)) $\rho(v)=\frac14 I\otimes I-\frac v4\sum_i\sigma_i\otimes\sigma_i$. It is entangled exactly when $v>1/3$ (Proposition 1).
--
--   **Formalization Note** Defined for every real $v$; statements restrict $v$. A proved sanity check confirms Eq. (5) and $\operatorname{Tr}\rho(v)=1$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 1, p.19, Eq. (4)

import Mathlib
import Definitions.Def_CompNonlocal_singlet

set_option autoImplicit false

namespace CompNonlocal

/-- Werner states. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 1, p.19: "For v ∈ [0, 1], the Werner state ρ(v) ∈ S(C² ⊗ C²) is
ρ(v) := v |ψ⁻⟩⟨ψ⁻| + (1−v)/4 I ⊗ I." (Eq. (4)).

**Formalization Note** Defined for every real `v`; every statement of the mission restricts `v` to
the paper's range. Alice's qubit is the first tensor factor. -/
noncomputable def werner (v : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (v : ℂ) • singlet + (((1 - v) / 4 : ℝ) : ℂ) • 1

end CompNonlocal


