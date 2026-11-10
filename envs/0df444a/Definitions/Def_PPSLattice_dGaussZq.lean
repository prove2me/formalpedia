-- Prove2me | Definitions.Def_PPSLattice_dGaussZq
-- name    : PPSLattice_dGaussZq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:34:15.147252+00:00
-- url     : https://prove2.me/theorems/bc56fbe6-01a1-4ebb-b0d1-15bead1731bd
-- title:
--   Discrete Gaussian reduced modulo $q$
-- statement:
--   The image of $D_{\mathbb Z,\sigma}$ under $\mathbb Z\to\mathbb Z_q$: the law of the error $\mathbf e$ as it enters $\mathbf s^\top\mathbf A+\mathbf e^\top$ over $\mathbb Z_q$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Assumption 3.4, p.17; Construction 4.6, p.21

import Mathlib
import Definitions.Def_PPSLattice_dGauss
set_option autoImplicit false

namespace PPSLattice

/-- The **discrete Gaussian reduced modulo `q`**: the image of `D_{Z,σ}` under `Z → Z_q`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Assumption 3.4, p.17 ("e ← D^m_{Z,χ}" used in "s^⊤A + e^⊤" over Z_q) and Construction 4.6,
p.21 ("e ← D^{⌈log N⌉·m}_{Z,χ}", hardwired as "e ∈ Z_q^{⌈log N⌉·m}" in Figure 1, p.22). -/
noncomputable def dGaussZq (q : ℕ) (σ : ℝ) : PMF (ZMod q) :=
  (dGauss σ).map fun x : ℤ => (x : ZMod q)

end PPSLattice


