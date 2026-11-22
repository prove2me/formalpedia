-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_IsBlockProd
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaValues_IsBlockProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:33.021966+00:00
-- url     : https://prove2.me/theorems/194fca16-51ee-4acf-8591-3d3efdd590a3
-- title:
--   Is Block Prod
-- statement:
--   Definitions and structural lemmas for Is Block Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/IsBlockProd.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BlockTh
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
structure Bk (Dw : Datum H) (n : ℕ) where
  τ : E →+* ℂ
  i : ℕ
  hi : i ≤ Dw.mult τ
  c : ℕ
  hc : 1 ≤ c
  col : Fin i → Fin n
  col_inj : Function.Injective col
variable {Dw : Datum H} {n : ℕ}
def Bk.poly (K : Type) [CommRing K] (B : Bk Dw n) : MvPolynomial (LtN Dw n) K :=
  (Matrix.of fun a b : Fin B.i => MvPolynomial.X (⟨B.τ, Fin.castLE B.hi a, B.col b⟩ : LtN Dw n)).det ^ B.c
def IsBlockProd {K : Type} [CommRing K] (P : MvPolynomial (LtN Dw n) K) : Prop :=
  ∃ (nb : ℕ) (bs : Fin nb → Bk Dw n), (∀ j j', j ≠ j' → ∀ a a', (bs j).col a ≠ (bs j').col a') ∧
    P = ∏ j, (bs j).poly K
variable {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
def ContainsTh (nab : NabV Xo c) (s : c.F) (P : MvPolynomial (LtN Dw n) c.F) {J : Type} (w : J → Rul Xo c) : Prop :=
  ∃ jb : (Fin n → LevQ Dw l) → J, Function.Injective jb ∧
    ∀ q, ∃ f : Rul Xo c, IsThRule Xo c nab (fun b => levRep (q b)) P f ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), w (jb q) p y = algebraMap c.F p.R s * f p y
variable (E) in

def p14 (r n m : ℕ) : ℝ :=
  (Real.log Real.pi + n * (Real.log 24 + (I2.dstar (E := E) m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) m : ℝ))) +
    (r + 2) * Real.log 2) / 2
end GlobalTheory.BlockTh


