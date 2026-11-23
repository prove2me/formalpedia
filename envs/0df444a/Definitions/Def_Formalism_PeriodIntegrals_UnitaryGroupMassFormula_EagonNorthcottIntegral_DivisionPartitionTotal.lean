-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:52.054247+00:00
-- url     : https://prove2.me/theorems/20975e5d-bc43-43c7-9ad4-538eff0e12f0
-- title:
--   Division Partition Total
-- statement:
--   Definitions and structural lemmas for Division Partition Total, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/DivisionPartitionTotal.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_YHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EagonNorthcottZ
open MvPolynomial PI.EagonNorthcott
def DivisionKillsEarlier : Prop := ∀ (D : ℕ) (ι : Fin D → Fin D ⊕ Fin D), Function.Injective ι → ∀ (m l : Fin D), l < m → ∀ f : P D,
  Dop ι m (X (ι l) * f) = 0
def DivisionCommutesLater : Prop := ∀ (D : ℕ) (ι : Fin D → Fin D ⊕ Fin D), Function.Injective ι → ∀ (m l : Fin D), m < l → ∀ f : P D,
  Dop ι m (X (ι l) * f) = X (ι l) * Dop ι m f
def DivisionPartitionUpto : Prop := ∀ (D : ℕ) (ι : Fin D → Fin D ⊕ Fin D), Function.Injective ι → ∀ (m : Fin D) (f : P D),
  ∑ i ∈ Finset.univ.filter (· < m), X (ι i) * Dop ι i f + Dop ι m (X (ι m) * f) = f
def DivisionPartitionTotal : Prop := ∀ (D : ℕ) (ι : Fin D → Fin D ⊕ Fin D), Function.Injective ι → ∀ f : P D,
  (∀ μ ∈ f.support, ∃ i, 0 < μ (ι i)) → ∑ i, X (ι i) * Dop ι i f = f
def DGy : Prop := ∀ (D a : ℕ) (i : Fin D) (f : P D), YHom (a + 1) f → YHom a (Dop Sum.inr i f)
def DGy0 : Prop := ∀ (D : ℕ) (i : Fin D) (f : P D), YHom 0 f → Dop Sum.inr i f = 0
def DGx : Prop := ∀ (D a : ℕ) (i : Fin D) (f : P D), YHom a f → YHom a (Dop Sum.inl i f)
def NoX {D : ℕ} (f : P D) : Prop := f ∈ Set.range (rename Sum.inr : S D → P D)
def IsCyc {D : ℕ} (a j : ℕ) (ω : W D) : Prop := Gr a j ω ∧ K ys ω = 0
def IsZL {D : ℕ} (a j : ℕ) (ω : W D) : Prop := IsCyc a j ω ∧ ∀ J, NoX (ω J)
def Phi {D r : ℕ} (b : Fin r → W D) (v : Fin r → S D) : W D := fun J => ∑ k, inx (v k) * b k J
def IsZBasis {D : ℕ} (a j : ℕ) {r : ℕ} (b : Fin r → W D) : Prop :=
  LinearIndependent ℤ b ∧ ∀ ω, IsZL a j ω ↔ ω ∈ Submodule.span ℤ (Set.range b)
def b0 {D m : ℕ} (e : Fin m → Fin D → ℕ) : Fin m → W D := fun k J => if J = ∅ then ∏ i, ys i ^ e k i else 0
def LBasis : Prop := ∀ D a j : ℕ, ∃ (r : ℕ) (b : Fin r → W D), IsZBasis a j b
def LEnum : Prop := ∀ D a : ℕ, ∃ (m : ℕ) (e : Fin m → Fin D → ℕ), Function.Injective e ∧ ∀ α : Fin D → ℕ, α ∈ Set.range e ↔ ∑ i, α i = a
def LBasis0 : Prop := ∀ (D a m : ℕ) (e : Fin m → Fin D → ℕ), Function.Injective e →
  (∀ α : Fin D → ℕ, α ∈ Set.range e ↔ ∑ i, α i = a) → IsZBasis a 0 (b0 e)
def LVan : Prop := ∀ D a j : ℕ, max D 1 ≤ j → ∀ ω : W D, IsZL a j ω → ω = 0
def LInj : Prop := ∀ (D a j r : ℕ) (b : Fin r → W D), IsZBasis a j b → Function.Injective (Phi b)
def LRan : Prop := ∀ (D a j r : ℕ) (b : Fin r → W D), IsZBasis a j b → ∀ ω, (∃ v, Phi b v = ω) ↔ IsCyc a j ω
def LCt : Prop := ∀ (D a j : ℕ) (i : Fin D) (ω : W D), IsZL a (j + 1) ω → IsZL a j (ct i ω)
def LKx : Prop := ∀ (D : ℕ) (ω : W D), K xs ω = fun J => ∑ i, xs i * ct i ω J
end PI.EagonNorthcottZ


