-- Prove2me | Definitions.Def_QMAPlusGap_onFirst
-- name    : QMAPlusGap_onFirst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:06:13.017102+00:00
-- url     : https://prove2.me/theorems/2d67e56b-1bfb-4da7-9ea3-b2830fc55062
-- title:
--   Single-register operators $X^{(1)}_i$, $X^{(2)}_j$ on two copies
-- statement:
--   On two copies $\mathcal H^{\otimes m}\otimes\mathcal H^{\otimes m}$, $X^{(1)}_i=X_i\otimes I$ acts as $X$ on register $i$ of the first copy and $X^{(2)}_j=I\otimes X_j$ as $X$ on register $j$ of the second copy. Here $X_i$ is $X$ on register $i$ of $\mathcal H^{\otimes m}$ and the identity on the others, the published `OptimalSpectrum.Entangled.copyOp`.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), App. A.1, p.31

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_copyOp

set_option autoImplicit false

open Matrix

namespace QMAPlusGap

/-- `X^{(1)}_i`: `X` acting on register `i` of the **first** of two copies of `H^{⊗m}`, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), App. A.1, p.31
("X^{(1)}_i (resp. X^{(2)}_j) denotes X acting on register i of the first copy (resp. register j of the second
copy)"). Two copies have basis `(Fin m → ι) × (Fin m → ι)`; `X` on one register of `H^{⊗m}` is the published
`OptimalSpectrum.Entangled.copyOp`. -/
def onFirst {ι : Type} [DecidableEq ι] {m : ℕ} (i : Fin m) (X : Matrix ι ι ℂ) :
    Matrix ((Fin m → ι) × (Fin m → ι)) ((Fin m → ι) × (Fin m → ι)) ℂ :=
  kroneckerMap (· * ·) (OptimalSpectrum.Entangled.copyOp i X) (1 : Matrix (Fin m → ι) (Fin m → ι) ℂ)

/-- `X^{(2)}_j`: `X` acting on register `j` of the **second** of two copies of `H^{⊗m}`, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), App. A.1,
p.31. -/
def onSecond {ι : Type} [DecidableEq ι] {m : ℕ} (j : Fin m) (X : Matrix ι ι ℂ) :
    Matrix ((Fin m → ι) × (Fin m → ι)) ((Fin m → ι) × (Fin m → ι)) ℂ :=
  kroneckerMap (· * ·) (1 : Matrix (Fin m → ι) (Fin m → ι) ℂ) (OptimalSpectrum.Entangled.copyOp j X)

end QMAPlusGap


