-- Prove2me | Definitions.Def_PPSLattice_uniformMat
-- name    : PPSLattice_uniformMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:19.752033+00:00
-- url     : https://prove2.me/theorems/68310c95-63a4-4c29-94cb-b08c0005c636
-- title:
--   Uniform law on $\mathbb Z_q^{a\times b}$
-- statement:
--   All $ab$ entries independent and uniform in $\mathbb Z_q$, as in "$\mathbf A\leftarrow\mathbb Z_q^{n\times m}$" and "$\mathbf P\leftarrow\mathbb Z_q^{n\times\lambda}$".
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Assumption 3.4, p.17; Construction 4.6, p.21

import Mathlib
import Definitions.Def_PPSLattice_iidVec
import Definitions.Def_PPSLattice_uniformZq
set_option autoImplicit false

namespace PPSLattice

/-- The **uniform law on `Z_q^{a×b}`**: all `a · b` entries independent and uniform in `Z_q`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Assumption 3.4, p.17 ("A ← Z_q^{n×m}"); Construction 4.6, p.21 ("Sample matrix
A ← Z_q^{n×(⌈log N⌉·m)}", "P ← Z_q^{n×λ}"). -/
noncomputable def uniformMat (q a b : ℕ) : PMF (Matrix (Fin a) (Fin b) (ZMod q)) :=
  (iidVec (iidVec (uniformZq q) b) a).map Matrix.of

end PPSLattice


