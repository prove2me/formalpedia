-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LinFormOneZero
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LinFormOneZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:04.139932+00:00
-- url     : https://prove2.me/theorems/b3013ff7-df47-4dea-9765-fc410a6037f5
-- title:
--   Lin Form One Zero
-- statement:
--   Definitions and structural lemmas for Lin Form One Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LinFormOneZero.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp Xc)
def GenericFibreIdeal.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MRing (PBlk n))), IsArithVar P d →
    IsProjPrime (genericIdeal P) ∧
      (genericIdeal P).comap (MvPolynomial.map (Int.castRingHom ℚ)) = IndefiniteRowSideFullHecke.ArithBezout.finIdeal P
def DivSuppHorizontalArithVar.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ) (H : Ideal (MRing (PBlk n))),
    IsArithVar P (d + 1) → IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
      H ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) → IsHorizontal H → IsArithVar H d
def IntChowFormExists.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n))), IsArithVar P (e + 1) →
    ∃ (δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℤ), IndefiniteRowSideFullHecke.ArithBezout.IsIntChowForm P e δ f
end ObjectsChow
end GroundTheory.Heights₂.Heights


