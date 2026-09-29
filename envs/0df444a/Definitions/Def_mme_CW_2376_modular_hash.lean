-- Prove2me | Definitions.Def_mme_CW_2376_modular_hash
-- name    : mme_CW_2376_modular_hash
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T20:04:30.101916+00:00
-- url     : https://prove2.me/theorems/b76d7105-fa20-4cdd-8f35-38b88b276bbb
-- title:
--   Odd-modulus affine hashes for the outer CW profile
-- statement:
--   For an odd hashing modulus $M$, define the three ordinary outer CW hash labels by multiplying each doubled affine hash by $2^{-1}$ in $\mathbb Z/M\mathbb Z$. Thus
--
--   $$
--   H_X=2^{-1}H_X^{(2)},\qquad H_Y=2^{-1}H_Y^{(2)},\qquad H_Z=2^{-1}H_Z^{(2)}.
--   $$
--
--   The definitions are meaningful for every modulus; oddness is required by subsequent theorems to make two a unit. They isolate the modular labels used for restriction to a lower-half Salem--Spencer set.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), odd-modulus outer square-profile hashes on journal p. 268; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Data.ZMod.Basic
import Definitions.Def_mme_CW_2376_hash_arithmetic

namespace MME

def cw2376XHashMod {M N : ℕ}
    (w : Fin N → ZMod M) (x : Fin N → Fin 5) : ZMod M :=
  (2 : ZMod M)⁻¹ * cw2376DoubledXHash w x

def cw2376YHashMod {M N : ℕ}
    (b0 : ZMod M) (w : Fin N → ZMod M)
    (y : Fin N → Fin 5) : ZMod M :=
  (2 : ZMod M)⁻¹ * cw2376DoubledYHash b0 w y

def cw2376ZHashMod {M N : ℕ}
    (b0 : ZMod M) (w : Fin N → ZMod M)
    (z : Fin N → Fin 5) : ZMod M :=
  (2 : ZMod M)⁻¹ * cw2376DoubledZHash b0 w z

end MME


