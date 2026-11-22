-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:25.875038+00:00
-- url     : https://prove2.me/theorems/2cff1692-1ba2-40a7-9488-b927c2aa901d
-- title:
--   FIwasawa B
-- statement:
--   Definitions and structural lemmas for FIwasawa B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaB.lean

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
namespace Formalism.UG.P
section FIwasawaMat
variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}
def fIwasawaP (π : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun i j => if π i = j then 1 else 0
def fIwasawaE (e z : Fin n → L) (c : L) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun i j => (if i = j then 1 else 0) + z i * σ (e (Fin.rev j)) - e i * σ (z (Fin.rev j)) +
    c * e i * σ (e (Fin.rev j))
end FIwasawaMat
section FIwasawaInt
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
def fIwasawaInt (M : Matrix (Fin n) (Fin n) L) : Prop := ∀ i j, Valued.v (M i j) ≤ 1
end FIwasawaInt
end Formalism.UG.P


