-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CompInv
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CompInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:09.724939+00:00
-- url     : https://prove2.me/theorems/33715cef-d2b8-4c94-b559-d43a77b45433
-- title:
--   Comp Inv
-- statement:
--   Definitions and structural lemmas for Comp Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/CompInv.lean

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Theorems.Thm_Formalism_ELL_wSeriesUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
namespace Formalism.L2.Th1.A
section Tools
variable {R : Type u} [CommRing R]
abbrev toL : R⟦X⟧ →+* LaurentSeries R := HahnSeries.ofPowerSeries ℤ R
def uPow (n : ℤ) : LaurentSeries R := HahnSeries.single n 1
def dL : LaurentSeries R →ₗ[R] LaurentSeries R := LaurentSeries.hasseDeriv R 1
open Classical in

def compInv (s : R⟦X⟧) : R⟦X⟧ :=
  if h : ∃ t : R⟦X⟧, constantCoeff t = 0 ∧ s.subst t = X then h.choose else 0
end Tools
def integ {K : Type u} [Field K] (f : K⟦X⟧) : K⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else coeff (n - 1) f / (n : K)
section Curve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
def wSer : R⟦X⟧ := (Formalism.ELL.wSeriesUnique R W).choose
def wU : R⟦X⟧ := PowerSeries.mk fun n => coeff (n + 3) (wSer W)
def xS : R⟦X⟧ := invOfUnit (wU W) 1
def yS : R⟦X⟧ := -xS W
def xL : LaurentSeries R := uPow (-2) * toL (xS W)
def yL : LaurentSeries R := uPow (-3) * toL (yS W)
def fw : R⟦X⟧ :=
  1 - C W.a₁ * X - C W.a₂ * X ^ 2 - 2 * C W.a₃ * wSer W - 2 * C W.a₄ * X * wSer W
    - 3 * C W.a₆ * wSer W ^ 2
def fu : R⟦X⟧ :=
  3 * X ^ 2 + C W.a₁ * wSer W + 2 * C W.a₂ * X * wSer W + C W.a₄ * wSer W ^ 2
def om : R⟦X⟧ := invOfUnit (fw W) 1
def D : Derivation R R⟦X⟧ R⟦X⟧ := fw W • derivative R
def DL (f : LaurentSeries R) : LaurentSeries R := toL (fw W) * dL f
def iDen : R⟦X⟧ := -1 + C W.a₁ * X + C W.a₃ * wSer W
def iSer : R⟦X⟧ := X * invOfUnit (iDen W) (-1)
end Curve
section Law
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
def lam : MvPowerSeries (Fin 2) R := fun e => coeff (e 0 + e 1 + 1) (wSer W)
def nu : MvPowerSeries (Fin 2) R := (wSer W).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R)
  - lam W * MvPowerSeries.X 0
def cThree : MvPowerSeries (Fin 2) R :=
  1 + MvPowerSeries.C W.a₂ * lam W + MvPowerSeries.C W.a₄ * lam W ^ 2
    + MvPowerSeries.C W.a₆ * lam W ^ 3
def cTwo : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.C W.a₁ * lam W + MvPowerSeries.C W.a₂ * nu W + MvPowerSeries.C W.a₃ * lam W ^ 2
    + 2 * MvPowerSeries.C W.a₄ * lam W * nu W + 3 * MvPowerSeries.C W.a₆ * lam W ^ 2 * nu W
def uThird : MvPowerSeries (Fin 2) R :=
  -MvPowerSeries.X 0 - MvPowerSeries.X 1 - cTwo W * MvPowerSeries.invOfUnit (cThree W) 1
def wThird : MvPowerSeries (Fin 2) R := lam W * uThird W + nu W
def fgl : MvPowerSeries (Fin 2) R :=
  uThird W * MvPowerSeries.invOfUnit
    (-1 + MvPowerSeries.C W.a₁ * uThird W + MvPowerSeries.C W.a₃ * wThird W) (-1)
def nSer : ℕ → R⟦X⟧
  | 0 => 0
  | n + 1 => MvPowerSeries.subst (![X, nSer n] : Fin 2 → R⟦X⟧) (fgl W)
def zSer : ℤ → R⟦X⟧
  | Int.ofNat n => nSer W n
  | Int.negSucc n => (iSer W).subst (nSer W (n + 1))
def halfSer : R⟦X⟧ := compInv (nSer W 2)
end Law
section Log
variable {K : Type u} [Field K] (W : WeierstrassCurve K)
def logSer : K⟦X⟧ := integ (om W)
def expSer : K⟦X⟧ := compInv (logSer W)
def xZ : LaurentSeries K := (toL (expSer W))⁻¹ ^ 2 * toL ((xS W).subst (expSer W))
def yZ : LaurentSeries K := (toL (expSer W))⁻¹ ^ 3 * toL ((yS W).subst (expSer W))
def g₂ : K := W.c₄ / 12
def g₃ : K := W.c₆ / 216
def wpL : LaurentSeries K := xZ W + HahnSeries.C (W.b₂ / 12)
def wpReg : K⟦X⟧ := PowerSeries.mk fun n => (wpL W).coeff (n : ℤ)
end Log
section Translate
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (xP yP : R)
def tDen : R⟦X⟧ := xS W - C xP * X ^ 2
def tS : R⟦X⟧ := X ^ 2 * invOfUnit (tDen W xP) 1
def nS : R⟦X⟧ :=
  C (W.a₄ - W.a₁ * yP + 2 * W.a₂ * xP + 3 * xP ^ 2) * X * xS W
    - C (2 * yP + W.a₁ * xP + W.a₃) * yS W
    + C (2 * W.a₆ + W.a₄ * xP - W.a₃ * yP - xP ^ 3) * X ^ 3
def xPlus : R⟦X⟧ := C xP + X * nS W xP yP * invOfUnit (tDen W xP) 1 ^ 2
def yPlus : R⟦X⟧ :=
  -((yS W - C yP * X ^ 3) * nS W xP yP * invOfUnit (tDen W xP) 1 ^ 3) - C yP
    - C W.a₁ * xPlus W xP yP - C W.a₃
def slopeL : LaurentSeries R := (yL W - HahnSeries.C yP) * toL (tS W xP)
end Translate
end Formalism.L2.Th1.A


