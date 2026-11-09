-- Prove2me | Definitions.Def_GoodQLTC_cssDist
-- name    : GoodQLTC_cssDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:38:13.121041+00:00
-- url     : https://prove2.me/theorems/860c5183-7fa2-4987-abc3-528f0b106bfb
-- title:
--   Distance $d(Q)=\min\{d_X(Q),d_Z(Q)\}$ of a CSS code
-- statement:
--   The X and Z distances of the CSS code $(H_X,H_Z)$ are
--   $$
--   d_X(Q)=\min_{x\in\ker H_Z\setminus\operatorname{im}H_X^{\top}}|x|,\qquad d_Z(Q)=\min_{z\in\ker H_X\setminus\operatorname{im}H_Z^{\top}}|z|,
--   $$
--   where $|x|$ is the Hamming weight, and the distance is $d(Q)=\min\{d_X(Q),d_Z(Q)\}$, with $\min\emptyset=+\infty$.
--
--   **Formalization Note** Values in $\mathbb N\cup\{\infty\}$ (`ℕ∞`); the empty minimum is $\top=+\infty$ as in the paper's convention (§3.1).
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §3.2, p.14 (PDF p.17); convention min ∅ := +∞, §3.1, p.13

import Mathlib
open Matrix

namespace GoodQLTC

/-- The **X distance** `d_X(Q) := min_{x ∈ ker H_Z ∖ im H_X^⊺} |x|`, Gay–Jeronimo,
arXiv:2609.20780 (held version), §3.2, p.14, with `min ∅ := +∞` (§3.1, p.13). -/
noncomputable def distX {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    (HX : Matrix κX ι (ZMod 2)) (HZ : Matrix κZ ι (ZMod 2)) : ℕ∞ :=
  ⨅ (x : ι → ZMod 2) (_ : HZ *ᵥ x = 0 ∧ x ∉ LinearMap.range (Matrix.mulVecLin HXᵀ)),
    (hammingNorm x : ℕ∞)

/-- The **Z distance** `d_Z(Q) := min_{z ∈ ker H_X ∖ im H_Z^⊺} |z|` (arXiv:2609.20780, §3.2,
p.14), `min ∅ := +∞`. -/
noncomputable def distZ {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    (HX : Matrix κX ι (ZMod 2)) (HZ : Matrix κZ ι (ZMod 2)) : ℕ∞ :=
  ⨅ (z : ι → ZMod 2) (_ : HX *ᵥ z = 0 ∧ z ∉ LinearMap.range (Matrix.mulVecLin HZᵀ)),
    (hammingNorm z : ℕ∞)

/-- The **distance** `d(Q) := min{d_X(Q), d_Z(Q)}` of the CSS code `(H_X, H_Z)`, Gay–Jeronimo,
arXiv:2609.20780 (held version), §3.2, p.14.

**Formalization Note.** Values in `ℕ∞`; the empty minimum is `⊤ = +∞`, as in the paper's
convention `min ∅ := +∞` (§3.1, p.13). `|x|` is Mathlib's `hammingNorm`. -/
noncomputable def cssDist {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    (HX : Matrix κX ι (ZMod 2)) (HZ : Matrix κZ ι (ZMod 2)) : ℕ∞ :=
  min (distX HX HZ) (distZ HX HZ)

end GoodQLTC


