-- Prove2me | Definitions.Def_UniversalSubmod_CorrMatrix
-- name    : UniversalSubmod_CorrMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:51:30.344222+00:00
-- url     : https://prove2.me/theorems/a27c232d-4380-4ef9-a0bf-9b3995d1d787
-- title:
--   The correlation matrices $\mathcal E_n$ (PSD, unit diagonal)
-- statement:
--   Let $n\ge 0$. The set $\mathcal E_n$ consists of all real $n\times n$ matrices $\Sigma=(\sigma_{ij})$ that are positive semidefinite and have all diagonal entries equal to $1$:
--   $$
--   \mathcal E_n=\{\Sigma\in\mathbb R^{n\times n} : \Sigma\succeq 0,\ \sigma_{ii}=1\ \text{for all } i\in[n]\}.
--   $$
--   Equivalently, $\mathcal E_n$ is the set of Gram matrices $\sigma_{ij}=\langle v_i,v_j\rangle$ of unit vectors $v_1,\dots,v_n$, and the set of covariance matrices of Gaussian vectors with standard normal marginals.
--
--   These matrices are the second argument of the semidefinite extension $F(x,\Sigma)$ and the objects compared in the Gaussian comparison theorem (Theorem 2.3).
--
--   **Formalization Note** The ground set $[n]$ is `Fin n`; positive semidefiniteness is Mathlib's `Matrix.PosSemidef`, which includes symmetry.
-- source:
--   Adamczyk, Ueltzen, Vondrák, Optimal universal sets for submodular functions, manuscript (Nov. 3, 2026; sha256 8a53c0912e8ad39b1019cbabfbde98980fd3eea456a8c7e5b28eb55d58343714), §2.2, pp.5–6

import Mathlib

namespace UniversalSubmod

/-- **Correlation matrices `E_n`** (Adamczyk, Ueltzen, Vondrák, *Optimal universal sets for
submodular functions*, manuscript of November 3, 2026, §2.2, pp.5–6): `E_n` is the collection of
all `n × n` positive semidefinite matrices with diagonal entries all `1`, equivalently the Gram
matrices `σᵢⱼ = vᵢ · vⱼ` of unit vectors `v₁, …, vₙ`.

**Formalization Note.** The ground set `[n]` is `Fin n`; a matrix is a real `Matrix (Fin n) (Fin n) ℝ`
and positive semidefiniteness is Mathlib's `Matrix.PosSemidef` (which includes symmetry). -/
def CorrMatrix {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  S.PosSemidef ∧ ∀ i, S i i = 1

end UniversalSubmod


