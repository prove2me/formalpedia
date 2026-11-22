-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymDStrip
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymDStrip
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:46:37.732241+00:00
-- url     : https://prove2.me/theorems/db0886c5-2e71-4b91-a934-db5e2e304f0d
-- title:
--   Sym DStrip
-- statement:
--   Definitions and structural lemmas for Sym DStrip, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymDStrip.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
open Classical in

def qs_psD (b : ℕ) (mu nu : Fin n → ℤ) : Matrix (TIdx mu × SymIdx n b) (TIdx nu) ℤ := fun y K =>
  ∑ m : ↥(qs_D nu mu) → Fin n,
    if (∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1) ∧ qs_ext mu y.1 = qs_add (qs_D nu mu) (qs_ext nu K) m then
      (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
        ∏ c : ↥(qs_D nu mu), qs_sg (qs_ext nu K c.1) (m c) else 0)
    else 0
open Classical in

def qs_midD (b : ℕ) (mu nu : Fin n → ℤ) (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) : GLCoord ℤ n :=
  ∑ a : ↥(qs_D nu mu) → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then
    ((detU n ^ nu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      (if ∀ c : ↥(qs_D nu mu), a c ∈ qs_ext mu J c.1 then
        (∏ c : ↥(qs_D nu mu), ((qs_sg ((qs_ext mu J c.1).erase (a c)) (a c) : ℤ) : GLCoord ℤ n)) *
          ∏ c ∈ Finset.Ioc (nu (lastIdx n)) (mu 0),
            qs_mn (qs_gC n) (qs_rem (qs_D nu mu) (qs_ext mu J) a c) (qs_ext nu K c) else 0)
  else 0
end Formalism.InvariantFactorPaths.ColumnFamilies


