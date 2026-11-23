-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:43.327848+00:00
-- url     : https://prove2.me/theorems/ebc2a273-e5c4-457a-9a58-789d2b46a107
-- title:
--   WChord
-- statement:
--   Definitions and structural lemmas for WChord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
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
namespace Formalism.ELL
namespace WeierstrassChordSeries
section Alg
variable {R : Type*} [CommRing R]
def G (a1 a2 a3 a4 a6 z v : R) : R :=
  z ^ 3 + a1 * (z * v) + a2 * (z ^ 2 * v) + a3 * v ^ 2 + a4 * (z * v ^ 2) + a6 * v ^ 3 - v
def c3 (a2 a4 a6 l : R) : R := 1 + a2 * l + a4 * l ^ 2 + a6 * l ^ 3
def c2 (a1 a2 a3 a4 a6 l n : R) : R :=
  a1 * l + a2 * n + a3 * l ^ 2 + 2 * a4 * l * n + 3 * a6 * l ^ 2 * n
def c1 (a1 a3 a4 a6 l n : R) : R :=
  a1 * n + 2 * a3 * l * n + a4 * n ^ 2 + 3 * a6 * l * n ^ 2 - l
def c0 (a3 a6 n : R) : R := a3 * n ^ 2 + a6 * n ^ 3 - n
section maps
variable {R' : Type*} [CommRing R'] (φ : R →+* R')
end maps
section mem
variable (T : Subring R)
end mem
end Alg
section Fld
variable {F : Type*} [Field F]
end Fld
section Wser
variable {K : Type u} [Field K] (W : WeierstrassCurve K)
def fw (v : PowerSeries K) : PowerSeries K :=
  X ^ 3 + C W.a₁ * X * v + C W.a₂ * X ^ 2 * v + C W.a₃ * v ^ 2 + C W.a₄ * X * v ^ 2
    + C W.a₆ * v ^ 3
def it : ℕ → PowerSeries K
  | 0 => 0
  | k + 1 => fw W (it k)
variable {W}
end Wser
section Mser
variable {K : Type u} [Field K]
def lam (w : PowerSeries K) : MvPowerSeries (Fin 2) K := fun e => coeff (e 0 + e 1 + 1) w
def Wi (w : PowerSeries K) (i : Fin 2) : MvPowerSeries (Fin 2) K := w.subst (MvPowerSeries.X i)
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable (W : WeierstrassCurve K) (w : PowerSeries K)
def nu : MvPowerSeries (Fin 2) K := Wi w 0 - lam w * MvPowerSeries.X 0
abbrev ca (a : K) : MvPowerSeries (Fin 2) K := MvPowerSeries.C a
def C3 : MvPowerSeries (Fin 2) K := c3 (ca W.a₂) (ca W.a₄) (ca W.a₆) (lam w)
def C2 : MvPowerSeries (Fin 2) K :=
  c2 (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄) (ca W.a₆) (lam w) (nu w)
def z3 : MvPowerSeries (Fin 2) K :=
  -MvPowerSeries.X 0 - MvPowerSeries.X 1 - C2 W w * (C3 W w)⁻¹
def w3 : MvPowerSeries (Fin 2) K := lam w * z3 W w + nu w
def dd : MvPowerSeries (Fin 2) K := -1 + ca W.a₁ * z3 W w + ca W.a₃ * w3 W w
def F2 : MvPowerSeries (Fin 2) K := z3 W w * (dd W w)⁻¹
def wF : MvPowerSeries (Fin 2) K := w3 W w * (dd W w)⁻¹
variable {W w}
abbrev Sadj (W : WeierstrassCurve K) : Subalgebra ℤ K :=
  Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)
def T (W : WeierstrassCurve K) : Subring (MvPowerSeries (Fin 2) K) :=
  (MvPowerSeries.map (algebraMap (Sadj W) K)).range
end Mser
end WeierstrassChordSeries
end Formalism.ELL


