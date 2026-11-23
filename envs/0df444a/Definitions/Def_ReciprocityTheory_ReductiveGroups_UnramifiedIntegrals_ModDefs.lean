-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:38.803812+00:00
-- url     : https://prove2.me/theorems/64f7b668-9330-4b36-b928-843761c2b841
-- title:
--   Mod Defs
-- statement:
--   Definitions and structural lemmas for Mod Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModDefs.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_CMGoodModels_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass
namespace ReciprocityTheory.ChartRestriction.L1
def DD (τ : ℍ) : ℂ := ModularForm.discriminant τ
def AA (τ : ℍ) : ℂ := E₄ τ ^ 3
def jT (τ : ℍ) : ℂ := AA τ / DD τ
def Tm (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (m.divisors.sigma fun a => Finset.range (m / a)).image fun x => (x.1, x.2, m / x.1)
def pt (a b e : ℕ) (τ : ℍ) : ℍ := UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / e)
def fac (t : ℕ × ℕ × ℕ) (τ : ℍ) : ℂ :=
  AA τ * DD (pt t.1 t.2.1 t.2.2 τ) - AA (pt t.1 t.2.1 t.2.2 τ) * DD τ
def Gm (m : ℕ) (τ : ℍ) : ℂ := ∏ t ∈ Tm m, fac t τ
def zetaC (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)
def Rm (m : ℕ) : Subring ℂ := Subring.closure {zetaC m}
def CoeffIn (R : Subring ℂ) (f : PowerSeries ℂ) : Prop := ∀ n, PowerSeries.coeff n f ∈ R
def IsTauOf (L : PeriodPair) (c : ℂ) (τ : ℍ) : Prop :=
  c ≠ 0 ∧ ∀ x : ℂ, x ∈ L.lattice ↔ ∃ u v : ℤ, x = c * (u * (τ : ℂ) + v)
def Tmat (t : ℕ × ℕ × ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(t.1 : ℤ), (t.2.1 : ℤ); 0, (t.2.2 : ℤ)]
def IsMF (k : ℤ) (f : ℍ → ℂ) : Prop := ∃ g : ModularForm 𝒮ℒ k, ∀ τ, g τ = f τ
def e4Z : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℤ)
def e6Z : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℤ)
def aZ : PowerSeries ℤ := e4Z ^ 3
def dZ : PowerSeries ℤ := PowerSeries.mk fun n => PowerSeries.coeff n (e4Z ^ 3 - e6Z ^ 2) / 1728
def aC : PowerSeries ℂ := aZ.map (Int.castRingHom ℂ)
def dC : PowerSeries ℂ := dZ.map (Int.castRingHom ℂ)
def xp {R : Type*} [CommRing R] (k : ℕ) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => if k ∣ n then PowerSeries.coeff (n / k) f else 0
def Conv (f : PowerSeries ℂ) : Prop :=
  ∀ x : ℂ, ‖x‖ < 1 → Summable fun n => ‖PowerSeries.coeff n f‖ * ‖x‖ ^ n
def ev (f : PowerSeries ℂ) (x : ℂ) : ℂ := ∑' n, PowerSeries.coeff n f * x ^ n
def sub1 (c : ℂ) (k : ℕ) (f : PowerSeries ℂ) : PowerSeries ℂ := xp k (PowerSeries.rescale c f)
def facSer (m : ℕ) (t : ℕ × ℕ × ℕ) : PowerSeries ℂ :=
  xp m aC * sub1 (zetaC t.2.2 ^ t.2.1) (t.1 ^ 2) dC - sub1 (zetaC t.2.2 ^ t.2.1) (t.1 ^ 2) aC * xp m dC
def prodSer (m : ℕ) : PowerSeries ℂ := ∏ t ∈ Tm m, facSer m t
def LowUnit (R : Subring ℂ) (f : PowerSeries ℂ) (n0 : ℕ) (u : ℂ) : Prop :=
  u ∈ R ∧ u⁻¹ ∈ R ∧ u ≠ 0 ∧ (∀ n < n0, PowerSeries.coeff n f = 0) ∧ PowerSeries.coeff n0 f = u
def qm (m : ℕ) (τ : ℍ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ / m)
end ReciprocityTheory.ChartRestriction.L1


