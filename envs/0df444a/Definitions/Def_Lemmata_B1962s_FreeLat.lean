-- Prove2me | Definitions.Def_Lemmata_B1962s_FreeLat
-- name    : Lemmata_B1962s_FreeLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:59:00.571132+00:00
-- url     : https://prove2.me/theorems/23acb0b1-ba28-49c7-87b6-0fcc8f1fde11
-- title:
--   Free Lat
-- statement:
--   Definitions and structural lemmas for Free Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/B1962s/FreeLat.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def Bl.FreeLattices.FreeLat :
  Prop :=
  ∀ (p : Nat) [inst : Fact (Nat.Prime p)] (σ : Type) (L : Submodule.{0, 0} (PadicInt p) (MvPolynomial.{0, 0} σ (Padic p)))
    (W : Submodule.{0, 0} (Padic p) (MvPolynomial.{0, 0} σ (Padic p))),
    FiniteDimensional.{0, 0} (Padic p)
        (Subtype.{1} fun (x : MvPolynomial.{0, 0} σ (Padic p)) ↦ Membership.mem.{0, 0} W x) →
      (∀ (x : MvPolynomial.{0, 0} σ (Padic p)), Membership.mem.{0, 0} L x → Membership.mem.{0, 0} W x) →
        Submodule.FG.{0, 0} L →
          Exists.{1} fun (m : Nat) ↦
            Exists.{1} fun (f : Fin m → MvPolynomial.{0, 0} σ (Padic p)) ↦
              And (∀ (a : Fin m), Membership.mem.{0, 0} L (f a))
                (And (LinearIndependent.{0, 0, 0} (PadicInt p) f)
                  (Eq.{1} (Submodule.span.{0, 0} (PadicInt p) (Set.range.{0, 1} f)) L))
namespace Bl.FreeLattices
end Bl.FreeLattices


