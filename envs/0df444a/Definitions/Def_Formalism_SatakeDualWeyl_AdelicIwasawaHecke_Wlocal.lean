-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:19:45.938416+00:00
-- url     : https://prove2.me/theorems/b1c5275d-3a05-40ff-89bc-f91502c9ca25
-- title:
--   Wlocal
-- statement:
--   Definitions and structural lemmas for Wlocal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.UG.P
open Formalism.GradedWeylDivisibility
def wlocal_E {R : Type} [CommRing R] {r : ℕ} (a b : Fin r) (c : R) : Matrix (Fin r) (Fin r) R :=
  fun i j => (if i = j then 1 else 0) + (if i = a ∧ j = b then c else 0)
def wlocal_L {R : Type} [CommRing R] {r : ℕ} (k : Fin r) (c : Fin r → R) : Matrix (Fin r) (Fin r) R :=
  fun i j => (if i = j then 1 else 0) + (if i ≠ k ∧ j = k then c i else 0)
section
variable {R : Type} [CommRing R]
def wlocal_Good {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (M : Matrix (Fin r) (Fin r) R) : Prop :=
  ∀ f ∈ weyl R r n hn ν, rowAct R M f ∈ weyl R r n hn ν
end
section
variable {R : Type} [CommRing R]
end
section
variable {R : Type} [CommRing R]
variable [IsLocalRing R]
end
section
variable {R S : Type} [CommRing R] [CommRing S]
end
section
variable {R : Type} [CommRing R]
end
end Formalism.UG.P


