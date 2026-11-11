-- Prove2me | Definitions.Def_QNoiseStab_ketBra
-- name    : QNoiseStab_ketBra
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:46.634751+00:00
-- url     : https://prove2.me/theorems/b81287d8-c654-4f39-a63e-2d7dc23ef62d
-- title:
--   Rank-one operator $|v\rangle\langle v|$
-- statement:
--   For a vector $v$ of a finite-dimensional Hilbert space $\mathbb C^{\iota}$, the operator $|v\rangle\langle v|$ is the matrix with entries
--
--   $$
--   \bigl(|v\rangle\langle v|\bigr)_{a,b}=v_a\,\overline{v_b}.
--   $$
--
--   For a unit vector it is the orthogonal projection onto $\mathbb C v$; the mission uses it for $|\hat z\rangle\langle\hat z|$ and $|\hat0\rangle\langle\hat0|$.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §3, pp.11–12 (the terms |ẑ⟩⟨ẑ| and |0̂⟩⟨0̂|)

import Mathlib

namespace QNoiseStab

/-- The rank-one operator `|v⟩⟨v|` of a vector `v` (Beame–Holman–Kornerup, *A Noise Operator
Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334
(version of 2026-11-02, sha256 814fe20e…), §3, pp.11–12, the terms `|ẑ⟩⟨ẑ|` and `|0̂⟩⟨0̂|`): the
matrix with entry `v_a · conj(v_b)` at `(a, b)`. -/
noncomputable def ketBra {ι : Type} (v : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  Matrix.of fun a b => v a * star (v b)

end QNoiseStab


