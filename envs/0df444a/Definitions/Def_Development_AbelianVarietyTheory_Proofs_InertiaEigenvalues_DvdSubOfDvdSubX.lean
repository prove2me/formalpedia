-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdSubOfDvdSubX
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdSubOfDvdSubX
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:05.432334+00:00
-- url     : https://prove2.me/theorems/4f3a7687-dee3-4573-91c1-1b838bb905e8
-- title:
--   Dvd Sub Of Dvd Sub X
-- statement:
--   Definitions and structural lemmas for Dvd Sub Of Dvd Sub X, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdSubOfDvdSubX.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
namespace GlobalTheory.NB.LT
def F (R : Type) [CommRing R] (l : ℕ) : Polynomial R :=
  Polynomial.X * (Polynomial.X + Polynomial.C (l : R)) ^ (l - 1)
def P (R : Type) [CommRing R] (l k : ℕ) : Polynomial R :=
  Nat.rec (Polynomial.X + Polynomial.C (l : R)) (fun _ p => p.comp (F R l)) k
abbrev EE (R : Type) [CommRing R] (l : ℕ) : Type :=
  AdicCompletion (Ideal.span {(l : Localization.Away (X : R⟦X⟧))}) (Localization.Away (X : R⟦X⟧))
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}
end GlobalTheory.NB.LT


