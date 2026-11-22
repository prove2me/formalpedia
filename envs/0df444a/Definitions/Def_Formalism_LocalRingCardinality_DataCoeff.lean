-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
-- name    : Formalism_LocalRingCardinality_DataCoeff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:26.44316+00:00
-- url     : https://prove2.me/theorems/299d63ec-59a2-4036-9582-0b2c96ea62e7
-- title:
--   Data Coeff
-- statement:
--   Definitions and structural lemmas for Data Coeff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataCoeff.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
namespace Formalism.BasicNotions
open MvPolynomial
noncomputable section
structure DomWeight (N : ℕ) where
  w : Fin N → ℤ
  anti : Antitone w
namespace DomWeight
variable {N : ℕ}
def detShift (lam : DomWeight N) : ℤ := if h : 0 < N then lam.w ⟨N - 1, by omega⟩ else 0
def natW (lam : DomWeight N) : Fin N → ℕ := fun i => (lam.w i - lam.detShift).toNat
def dual (lam : DomWeight N) : DomWeight N where
  w := fun i => -lam.w (Fin.rev i)
  anti := by
    intro i j hij
    have h1 : Fin.rev j ≤ Fin.rev i := Fin.rev_le_rev.mpr hij
    have h2 := lam.anti h1
    simp only
    omega
def spread (lam : DomWeight N) : ℤ :=
  if h : 0 < N then lam.w ⟨0, h⟩ - lam.w ⟨N - 1, by omega⟩ + N else 0
end DomWeight
def rhoVec (N : ℕ) (i : Fin N) : ℚ := ((N : ℚ) - 1) / 2 - (i : ℚ)
def hcToWeightQ {N : ℕ} (hc : Fin N → ℚ) : Fin N → ℚ := fun i => hc i - rhoVec N i
def IsIntegralHC {N : ℕ} (hc : Fin N → ℚ) : Prop := ∀ i, ∃ z : ℤ, hcToWeightQ hc i = z
section Modules
variable (R : Type) [CommRing R] (N : ℕ)
def nablaSq (lam : DomWeight N) : Submodule R (MvPolynomial (Fin N × Fin N) R) :=
  Formalism.GradedWeylDivisibility.dualWeyl R N N lam.natW
def delSq (lam : DomWeight N) : Submodule R (MvPolynomial (Fin N × Fin N) R) :=
  Formalism.GradedWeylDivisibility.weyl R N N le_rfl lam.natW
def extremal (lam : DomWeight N) : MvPolynomial (Fin N × Fin N) R :=
  Formalism.GradedWeylDivisibility.hw R le_rfl lam.natW
def detPow (g : GL (Fin N) R) (c : ℤ) : R :=
  ((Matrix.GeneralLinearGroup.det g ^ c : Rˣ) : R)
def sqAct (lam : DomWeight N) (g : GL (Fin N) R) (f : MvPolynomial (Fin N × Fin N) R) :
    MvPolynomial (Fin N × Fin N) R :=
  detPow R N g lam.detShift • Formalism.GradedWeylDivisibility.rowAct R (n := N) (g : Matrix (Fin N) (Fin N) R).transpose f
def roundAct (lam : DomWeight N) (g : GL (Fin N) R) (f : MvPolynomial (Fin N × Fin N) R) :
    MvPolynomial (Fin N × Fin N) R :=
  detPow R N g (-lam.detShift) • Formalism.UG.dwAct R N N g f
def inside₂ (g : GL (Fin N) R) : GL (Fin N) R where
  val := ((g⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R).transpose
  inv := (g : Matrix (Fin N) (Fin N) R).transpose
  val_inv := by rw [← Matrix.transpose_mul]; simp
  inv_val := by rw [← Matrix.transpose_mul]; simp
def diagGL (t : Fin N → Rˣ) : GL (Fin N) R where
  val := Matrix.diagonal fun a => (t a : R)
  inv := Matrix.diagonal fun a => ((t a)⁻¹ : Rˣ)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]
end Modules
noncomputable def normFock {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℂ) : ℂ :=
  Formalism.REAL.fockF f g / Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)
noncomputable def normFockQ {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℚ) : ℚ :=
  Formalism.GradedWeylDivisibility.fockQ f g / Formalism.GradedWeylDivisibility.fockQ (extremal ℚ N lam) (extremal ℚ N lam)
def colCoeff (R : Type) [CommRing R] (N : ℕ) {ι : Type} (lam : ι → DomWeight N) : Type :=
  PiTensorProduct R (fun τ => ↥(delSq R N (lam τ)))
def FactNatW : Prop := ∀ (N : ℕ) (lam : DomWeight N),
  Antitone lam.natW ∧ (∀ i, ((lam.natW i : ℕ) : ℤ) + lam.detShift = lam.w i) ∧
  (∀ h : 0 < N, lam.natW ⟨N - 1, by omega⟩ = 0)
def bridge_round_square : Prop := ∀ (R : Type) [CommRing R] (N : ℕ) (lam : DomWeight N)
  (g : GL (Fin N) R) (f : MvPolynomial (Fin N × Fin N) R),
  roundAct R N lam g f = sqAct R N lam (inside₂ R N g) f
def FactSqActMul : Prop := ∀ (R : Type) [CommRing R] (N : ℕ) (lam : DomWeight N)
  (g h : GL (Fin N) R) (f : MvPolynomial (Fin N × Fin N) R),
  sqAct R N lam (g * h) f = sqAct R N lam g (sqAct R N lam h f) ∧
  roundAct R N lam (g * h) f = roundAct R N lam g (roundAct R N lam h f)
def FactSqStable : Prop := ∀ (R : Type) [CommRing R] (N : ℕ) (lam : DomWeight N)
  (g : GL (Fin N) R),
  (∀ f ∈ nablaSq R N lam, sqAct R N lam g f ∈ nablaSq R N lam) ∧
  (∀ f ∈ delSq R N lam, sqAct R N lam g f ∈ delSq R N lam)
def FactSqHighestWeight : Prop := ∀ (R : Type) [CommRing R] (N : ℕ) (lam : DomWeight N),
  (∀ t : Fin N → Rˣ,
    sqAct R N lam (diagGL R N t) (extremal R N lam) =
      ((∏ a, (t a) ^ (lam.w a) : Rˣ) : R) • extremal R N lam) ∧
  (∀ g : GL (Fin N) R, (g : Matrix (Fin N) (Fin N) R).BlockTriangular id →
    (∀ a, (g : Matrix (Fin N) (Fin N) R) a a = 1) →
    sqAct R N lam g (extremal R N lam) = extremal R N lam)
def bridge_normFock_extremal : Prop := ∀ (N : ℕ) (lam : DomWeight N),
  normFock lam (extremal ℂ N lam) (extremal ℂ N lam) = 1
def FactNormFockUnitary : Prop := ∀ (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ),
  (g : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ →
  ∀ f h : MvPolynomial (Fin N × Fin N) ℂ,
    normFock lam (roundAct ℂ N lam g f) (roundAct ℂ N lam g h) = normFock lam f h
def FactDelDualNabla : Prop := ∀ (N : ℕ) (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℚ),
  f ∈ nablaSq ℚ N lam →
  ((∀ g ∈ nablaSq ℤ N lam, ∃ z : ℤ, normFockQ lam f (map (Int.castRingHom ℚ) g) = z) ↔
    ∃ f₀ ∈ delSq ℤ N lam, map (Int.castRingHom ℚ) f₀ = f)
def NablaMemDeltaLocallyAtLargePrime : Prop := ∀ (N : ℕ) (lam : DomWeight N) (p : ℕ), p.Prime → lam.spread < p →
  ∀ f ∈ nablaSq ℤ N lam, ∃ c : ℤ, ¬ (p : ℤ) ∣ c ∧ c • f ∈ delSq ℤ N lam
def bridge_hc_rho : Prop := ∀ (N : ℕ) (hc : Fin N → ℚ), StrictAnti hc → IsIntegralHC hc →
  ∃ lam : DomWeight N, ∀ i, (lam.w i : ℚ) = hcToWeightQ hc i
end
end Formalism.BasicNotions


