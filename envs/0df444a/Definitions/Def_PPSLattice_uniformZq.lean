-- Prove2me | Definitions.Def_PPSLattice_uniformZq
-- name    : PPSLattice_uniformZq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:14.969204+00:00
-- url     : https://prove2.me/theorems/af4cfbe1-9f01-42ab-bb85-9a03beeee0f3
-- title:
--   Uniform law on $\mathbb Z_q$
-- statement:
--   The uniform distribution on $\mathbb Z_q=\{0,\dots,q-1\}$ (point mass at $0$ for $q=0$, which the mission never uses: its moduli are prime).
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Assumption 3.4, p.17

import Mathlib
import Definitions.Def_MinSumClust_pexp
set_option autoImplicit false

namespace PPSLattice

/-- The **uniform law on Z_q**: the image of the uniform law on `{0, …, q − 1}`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Assumption 3.4, p.17 ("A ← Z_q^{n×m}, s ← Z_q^n, ..., c ← Z_q^m").

**Formalization Note.** `Z_q` is `ZMod q`. At `q = 0`, which no statement of the mission uses
(the moduli are prime), the law is the point mass at `0`. -/
noncomputable def uniformZq (q : ℕ) : PMF (ZMod q) :=
  (MinSumClust.unifOr (Finset.range q) 0).map fun v : ℕ => (v : ZMod q)

end PPSLattice


