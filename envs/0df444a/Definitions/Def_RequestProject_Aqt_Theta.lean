-- Prove2me | Definitions.Def_RequestProject_Aqt_Theta
-- name    : RequestProject_Aqt_Theta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T22:50:47.948744+00:00
-- url     : https://prove2.me/theorems/e59a617a-5e6a-4e2b-b81f-6060857e4dff
-- title:
--   Theta
-- statement:
--   Definitions and structural lemmas for Theta, from SashaIr/leaving-the-hall contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Dyck-path algebra and decorated-Dyck-path bijection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean

import Definitions.Def_RequestProject_Aqt_Rep
set_option autoImplicit true
namespace DyckAlgebra
namespace Theta
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
def s (u : 𝕜) (w y z : A) : A := u • (w * y * z)
def sStar (u : 𝕜) (y z : A) : A := u • ((1 - z) * y)
end Theta
end DyckAlgebra
namespace DyckAlgebra
open scoped BigOperators
universe v
def thetaTdown {A : Type*} [Ring A] (T : ℕ → A) : ℕ → A
  | 0 => 1
  | n + 1 => T (n + 1) * thetaTdown T n
def thetaTdownInv {A : Type*} [Ring A] (Tinv : ℕ → A) : ℕ → A
  | 0 => 1
  | n + 1 => Tinv (n + 1) * thetaTdownInv Tinv n
def thetaYY {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    (q : 𝕜) (level : ℕ) (Tinv T : ℕ → A) (dp dm : A) : ℕ → A
  | 0 => 0
  | 1 => (q ^ (level - 1) * (q - 1))⁻¹ •
      ((dp * dm - dm * dp) * thetaTdown T (level - 1))
  | i + 2 => q • (Tinv (i + 1) * thetaYY q level Tinv T dp dm (i + 1) * Tinv (i + 1))
def thetaZZ {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    (q t : 𝕜) (level : ℕ) (T Tinv : ℕ → A) (dps dm : A) : ℕ → A
  | 0 => 0
  | 1 => ((q * t)⁻¹ * (q ^ level * (1 - q)⁻¹)) •
      ((dps * dm - dm * dps) * thetaTdownInv Tinv (level - 1))
  | i + 2 => q⁻¹ • (T (i + 1) * thetaZZ q t level T Tinv dps dm (i + 1) * T (i + 1))
structure ThetaData (𝕜 : Type*) [Field 𝕜] (q cQ2 : 𝕜) where
  carrier : Type v
  [ring : Ring carrier]
  [algebra : Algebra 𝕜 carrier]
  T : ℕ → carrier
  Tinv : ℕ → carrier
  /-- The level represented by this local environment. -/
  level : ℕ
  /-- The second scalar parameter, needed for the normalized starred words. -/
  t : 𝕜
  dp : carrier
  dm : carrier
  dps : carrier
  skein : ∀ i, (T i - 1) * (T i + q • 1) = 0
  braid : ∀ i, T i * T (i+1) * T i = T (i+1) * T i * T (i+1)
  Tcomm : ∀ i j, i + 1 < j → T i * T j = T j * T i
  TinvL : ∀ i, T i * Tinv i = 1
  TinvR : ∀ i, Tinv i * T i = 1
  R1 : ∀ i, 2 ≤ i → i ≤ level - 2 → dm * T i = T i * dm
  R2 : ∀ i, 1 ≤ i → dp * T i = T (i+1) * dp
  R1s : ∀ i, 2 ≤ i → i ≤ level - 2 → dm * Tinv i = Tinv i * dm
  R2s : ∀ i, 1 ≤ i → dps * Tinv i = Tinv (i+1) * dps
  R3 : T 1 * dp * dp = dp * dp
  R3s : Tinv 1 * dps * dps = dps * dps
  R4 : 2 ≤ level → dm * dm * T (level - 1) = dm * dm
  R4s : 2 ≤ level → dm * dm * Tinv (level - 1) = dm * dm
  R5 : 2 ≤ level → dm * (dp * dm - dm * dp) * T (level - 1) =
    q • ((dp * dm - dm * dp) * dm)
  R5s : 2 ≤ level → dm * (dps * dm - dm * dps) * Tinv (level - 1) =
    q⁻¹ • ((dps * dm - dm * dps) * dm)
  R6 : T 1 * (dp * dm - dm * dp) * dp = q • (dp * (dp * dm - dm * dp))
  R6s : Tinv 1 * (dps * dm - dm * dps) * dps = q⁻¹ • (dps * (dps * dm - dm * dps))
  Q1 : ∀ i, thetaZZ q t level T Tinv dps dm (i+1) * dp = dp * thetaZZ q t level T Tinv dps dm i
  Q1s : ∀ i, thetaYY q level Tinv T dp dm (i+1) * dps = dps * thetaYY q level Tinv T dp dm i
  /-- At level `k`, the normalized `(Q2)` coefficient is `-q^k`. -/
  Q2scalar : cQ2 = -(q ^ level)
  Q2 : thetaZZ q t level T Tinv dps dm 1 * dp = cQ2 • (thetaYY q level Tinv T dp dm 1 * dps)
  yTcomm : ∀ i j, i ≠ j ∧ i ≠ j + 1 → thetaYY q level Tinv T dp dm i * T j = T j * thetaYY q level Tinv T dp dm i
  zTcomm : ∀ i j, i ≠ j ∧ i ≠ j + 1 → thetaZZ q t level T Tinv dps dm i * T j = T j * thetaZZ q t level T Tinv dps dm i
  ydm : ∀ i, thetaYY q level Tinv T dp dm i * dm = dm * thetaYY q level Tinv T dp dm i
  zdm : ∀ i, thetaZZ q t level T Tinv dps dm i * dm = dm * thetaZZ q t level T Tinv dps dm i
  yy_comm : ∀ i j, thetaYY q level Tinv T dp dm i * thetaYY q level Tinv T dp dm j = thetaYY q level Tinv T dp dm j * thetaYY q level Tinv T dp dm i
  zz_comm : ∀ i j, thetaZZ q t level T Tinv dps dm i * thetaZZ q t level T Tinv dps dm j = thetaZZ q t level T Tinv dps dm j * thetaZZ q t level T Tinv dps dm i
  z1y1 : thetaZZ q t level T Tinv dps dm 1 * T 1 * thetaYY q level Tinv T dp dm 1 = thetaYY q level Tinv T dp dm 2 * thetaZZ q t level T Tinv dps dm 1 * T 1
  y1z1 : thetaYY q level Tinv T dp dm 1 * Tinv 1 * thetaZZ q t level T Tinv dps dm 1 = thetaZZ q t level T Tinv dps dm 2 * thetaYY q level Tinv T dp dm 1 * Tinv 1
  T1symYa : T 1 * (thetaYY q level Tinv T dp dm 1 + thetaYY q level Tinv T dp dm 2) = (thetaYY q level Tinv T dp dm 1 + thetaYY q level Tinv T dp dm 2) * T 1
  T1symYm : T 1 * (thetaYY q level Tinv T dp dm 1 * thetaYY q level Tinv T dp dm 2) = (thetaYY q level Tinv T dp dm 1 * thetaYY q level Tinv T dp dm 2) * T 1
  T1symZa : T 1 * (thetaZZ q t level T Tinv dps dm 1 + thetaZZ q t level T Tinv dps dm 2) = (thetaZZ q t level T Tinv dps dm 1 + thetaZZ q t level T Tinv dps dm 2) * T 1
  T1symZm : T 1 * (thetaZZ q t level T Tinv dps dm 1 * thetaZZ q t level T Tinv dps dm 2) = (thetaZZ q t level T Tinv dps dm 1 * thetaZZ q t level T Tinv dps dm 2) * T 1
attribute [instance] ThetaData.ring ThetaData.algebra
namespace ThetaData
abbrev yy {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : ThetaData 𝕜 q cQ2) (i : ℕ) : ρ.carrier :=
  thetaYY q ρ.level ρ.Tinv ρ.T ρ.dp ρ.dm i
abbrev zz {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : ThetaData 𝕜 q cQ2) (i : ℕ) : ρ.carrier :=
  thetaZZ q ρ.t ρ.level ρ.T ρ.Tinv ρ.dps ρ.dm i
end ThetaData
structure DyckRepU (𝕜 : Type*) [Field 𝕜] (q cQ2 : 𝕜) extends ThetaData 𝕜 q cQ2 where
  /-- The formal parameter `u`. -/
  u : 𝕜
  /-- `w i = (1 + u y_i)⁻¹`. -/
  w : ℕ → carrier
  wL : ∀ i, (1 + u • ThetaData.yy toThetaData i) * w i = 1
  wR : ∀ i, w i * (1 + u • ThetaData.yy toThetaData i) = 1
  /-- `minv = (1 + s*)⁻¹`, where `s* = u(1-z₁)y₁`. -/
  minv : carrier
  mL : (1 + (u • ThetaData.yy toThetaData 1 - u • (ThetaData.zz toThetaData 1 * ThetaData.yy toThetaData 1))) * minv = 1
  mR : minv * (1 + (u • ThetaData.yy toThetaData 1 - u • (ThetaData.zz toThetaData 1 * ThetaData.yy toThetaData 1))) = 1
namespace DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
def sElt : ρ.carrier := ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.zz 1)
def Θdp : ρ.carrier := (1 - ρ.sElt) * ρ.dp
def Θdps : ρ.carrier := ρ.minv * ρ.dps
def Θy1 : ρ.carrier := (1 - ρ.sElt) * ρ.yy 1
def Θz1 : ρ.carrier := ρ.minv * ρ.zz 1
def sStarElt : ρ.carrier := ρ.u • ρ.yy 1 - ρ.u • (ρ.zz 1 * ρ.yy 1)
def s2Elt : ρ.carrier := ρ.u • (ρ.w 1 * ρ.zz 1 * ρ.yy 1)
end DyckRepU
end DyckAlgebra


