-- Prove2me | Definitions.Def_PreprocOWS_vnormSq
-- name    : PreprocOWS_vnormSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:17:28.997291+00:00
-- url     : https://prove2.me/theorems/a6be6065-41b1-4a4b-9376-c1e78e79a40c
-- title:
--   Euclidean norm $\|v\|$ and the operator norm $\|Y\|$
-- statement:
--   For a complex vector $v$ on a finite basis, $\|v\|^2=\sum_i|v_i|^2$ and $\|v\|=\big(\sum_i|v_i|^2\big)^{1/2}$. For a square complex matrix $Y$ acting on $\mathbb C^d$ with the Euclidean norm, the **operator norm** is
--   $$
--   \|Y\|=\sup_{\|\varphi\|=1}\|Y\varphi\| .
--   $$
--
--   States, winning probabilities and the matrix $Y_R$ of display (4) are measured in these norms.
--
--   **Formalization Note** Vectors are functions $\iota\to\mathbb C$; the operator norm is the norm of the continuous linear operator `Matrix.toEuclideanCLM Y` on `EuclideanSpace ℂ d` (Mathlib's $\ell_2$ operator norm).
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.1, display (4), p.17 (PDF p.20); proof of Theorem 5.2, p.19 (PDF p.22)

import Mathlib
open Matrix

namespace PreprocOWS

/-- The **squared Euclidean norm** `‖v‖² = ∑_i |v_i|²` of a complex vector on a finite basis, as used
for states and winning probabilities in arXiv:2610.02101 (Dong–Lombardi, version of 2026-11-02,
sha256 7a0bd8da…), §5.1, p.17 (PDF p.20).

**Formalization Note.** Vectors are plain functions `ι → ℂ` (Mathlib's default norm on them is the sup
norm, hence this separate definition). -/
noncomputable def vnormSq {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  ∑ i, ‖v i‖ ^ 2

/-- The Euclidean norm `‖v‖ = (∑_i |v_i|²)^{1/2}` (arXiv:2610.02101, proof of Theorem 5.2, p.19). -/
noncomputable def vnorm {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  Real.sqrt (vnormSq v)

/-- The **operator norm** `‖Y‖ = sup_{‖φ‖ = 1} ‖Y φ‖` of a square complex matrix, for the Euclidean
norm on `ℂ^d` (arXiv:2610.02101, display (4), p.17, PDF p.20: "from the definition of the operator
norm").

**Formalization Note.** It is the norm of the continuous linear operator
`Matrix.toEuclideanCLM Y` on `EuclideanSpace ℂ d`, i.e. Mathlib's L2 operator norm on matrices. -/
noncomputable def opNorm {d : Type*} [Fintype d] [DecidableEq d] (Y : Matrix d d ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) Y‖

end PreprocOWS


