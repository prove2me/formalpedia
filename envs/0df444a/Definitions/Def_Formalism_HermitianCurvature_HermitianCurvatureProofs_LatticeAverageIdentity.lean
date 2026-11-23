-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:05.925694+00:00
-- url     : https://prove2.me/theorems/08162630-7c4c-4283-8b72-32f0a456ad5d
-- title:
--   Lattice Average Identity
-- statement:
--   Definitions and structural lemmas for Lattice Average Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_up_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_smul_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val


set_option autoImplicit false
section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
namespace Formalism.FourierDecayAlt.P.A5x9
noncomputable section
section Defs
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
def IsP (k : ℕ) (p : Matrix (Fin n) (Fin n) K) : Prop :=
  IsUpUni p ∧ ∀ a b : Fin n, (k < a.val ∨ b.val ≤ k) → p a b ∈ R
def IsPP (k : ℕ) (p : Matrix (Fin n) (Fin n) K) : Prop := IsP R k p ∧ IsP R k p⁻¹
def IsD (k : ℕ) (D : Matrix (Fin n) (Fin n) K) : Prop :=
  IsUpUni D ∧ IsInt R D ∧ ∀ a b : Fin n, a.val ≤ k → D a b = (1 : Matrix (Fin n) (Fin n) K) a b
def msk (k : ℕ) (y : Fin n → K) : Fin n → K := fun j => if k < j.val then y j else 0
def b22 (k : ℕ) (p : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  fun a b => if k < a.val then p a b else (1 : Matrix (Fin n) (Fin n) K) a b
def abelian₂ (k : ℕ) (Z : Matrix (Fin n) (Fin n) K) : (Fin n → R) →ₗ[R] (Fin n → K) :=
  LinearMap.pi (fun j => if k < j.val then lamTil R Z j.val else 0)
def colSpan (k : ℕ) (Z : Matrix (Fin n) (Fin n) K) : Submodule R (Fin n → R) where
  carrier := {x | ∃ t : Fin n → R, (∀ j : Fin n, k < j.val → t j = 0) ∧
    Z *ᵥ coeLin R t = coeLin R x}
  add_mem' := by
    rintro x y ⟨t, ht, e⟩ ⟨s, hs, e'⟩
    exact ⟨t + s, fun j hj => by simp [ht j hj, hs j hj], by
      rw [map_add, map_add, Matrix.mulVec_add, e, e']⟩
  zero_mem' := ⟨0, fun _ _ => rfl, by simp⟩
  smul_mem' := by
    rintro r x ⟨t, ht, e⟩
    refine ⟨r • t, fun j hj => by simp [ht j hj], ?_⟩
    rw [map_smul, map_smul, A5x2.smul_coe, A5x2.smul_coe, Matrix.mulVec_smul, e]
abbrev MM (k : ℕ) (Z : Matrix (Fin n) (Fin n) K) : Type := (Fin n → R) ⧸ colSpan R k Z
def dRel (k : ℕ) (Z₀ : Matrix (Fin n) (Fin n) K) :
    Setoid {D : Matrix (Fin n) (Fin n) K // IsD R k D} where
  r D₁ D₂ := ∀ (x : Fin n → R) (j : Fin n), ((D₁.1 - D₂.1) *ᵥ abelian₂ R k Z₀ x) j ∈ R
  iseqv := ⟨fun D x j => by simp [R.zero_mem],
    fun {D₁ D₂} h x j => by
      have := R.neg_mem (h x j)
      rwa [← Pi.neg_apply, ← Matrix.neg_mulVec, neg_sub] at this,
    fun {D₁ D₂ D₃} h h' x j => by
      have := R.add_mem (h x j) (h' x j)
      rwa [← Pi.add_apply, ← Matrix.add_mulVec, sub_add_sub_cancel] at this⟩
def Nrm (k : ℕ) (Z₀ : Matrix (Fin n) (Fin n) K) (D : {D : Matrix (Fin n) (Fin n) K // IsD R k D}) :
    Prop := Quotient.out (Quotient.mk (dRel R k Z₀) D) = D
structure GB (k : ℕ) (Z₀ Z₀' : Matrix (Fin n) (Fin n) K) (Ψ : MM R k Z₀ ≃ₗ[R] MM R k Z₀') :
    Prop where
  e : Ψ (Submodule.Quotient.mk (eLast R)) = Submodule.Quotient.mk (eLast R)
  lift : ∃ D : {D : Matrix (Fin n) (Fin n) K // IsD R k D}, Nrm R k Z₀ D ∧
    ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      abelian₂ R k Z₀' y = D.1 *ᵥ abelian₂ R k Z₀ x
  bad : ∃ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧
    abelian₂ R k Z₀ x = 0 ∧ lamTil R Z₀' k y - lamTil R Z₀ k x ∉ R
def Rel {k : ℕ} {Z₀ Z₀' : Matrix (Fin n) (Fin n) K} (Ψ : MM R k Z₀ ≃ₗ[R] MM R k Z₀')
    (L L' : Submodule R (Fin n → R)) : Prop :=
  ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y → (x ∈ L ↔ y ∈ L')
end Defs
end
end Formalism.FourierDecayAlt.P.A5x9
end
section
namespace Formalism.FourierDecayAlt.P.A5x9
end Formalism.FourierDecayAlt.P.A5x9
end
section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
namespace Formalism.FourierDecayAlt.P.A5x9
section Mat
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
theorem isMirabolic_mul {p q : Matrix (Fin n) (Fin n) K} (hp : IsP R k p) (hq : IsP R k q) :
    IsP R k (p * q) := by
  refine ⟨isUpUni_mul K hp.1 hq.1, fun a b hab => ?_⟩
  rw [Matrix.mul_apply]
  refine R.sum_mem fun l _ => ?_
  by_cases h1 : l < a
  · rw [up_zero hp.1 h1, zero_mul]; exact R.zero_mem
  by_cases h2 : b < l
  · rw [up_zero hq.1 h2, mul_zero]; exact R.zero_mem
  have h1' : a.val ≤ l.val := Fin.le_def.1 (not_lt.1 h1)
  have h2' : l.val ≤ b.val := Fin.le_def.1 (not_lt.1 h2)
  rcases hab with h | h
  · exact R.mul_mem (hp.2 a l (Or.inl h)) (hq.2 l b (Or.inl (by omega)))
  · exact R.mul_mem (hp.2 a l (Or.inr (by omega))) (hq.2 l b (Or.inr h))
theorem isP_one : IsP R k (1 : Matrix (Fin n) (Fin n) K) := by
  refine ⟨isUpUni_one K, fun a b _ => ?_⟩
  rw [Matrix.one_apply]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem
theorem isPP_one : IsPP R k (1 : Matrix (Fin n) (Fin n) K) := by
  refine ⟨isP_one R k, ?_⟩
  rw [inv_one]
  exact isP_one R k
theorem isPP_mul {p q : Matrix (Fin n) (Fin n) K} (hp : IsPP R k p) (hq : IsPP R k q) :
    IsPP R k (p * q) := by
  refine ⟨isMirabolic_mul R k hp.1 hq.1, ?_⟩
  rw [Matrix.mul_inv_rev]
  exact isMirabolic_mul R k hq.2 hp.2
theorem isPP_inv {p : Matrix (Fin n) (Fin n) K} (hp : IsPP R k p) : IsPP R k p⁻¹ := by
  refine ⟨hp.2, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv p (by simp [isUpUni_det K hp.1.1])]
  exact hp.1
end Mat
end Formalism.FourierDecayAlt.P.A5x9
end
section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
namespace Formalism.FourierDecayAlt.P.A5x9
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
section Mat
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
end Mat
end Formalism.FourierDecayAlt.P.A5x9
end
section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
namespace Formalism.FourierDecayAlt.P.A5x9
section Cnt
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
noncomputable def cntaCoef {D : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) (j : Fin n) : ℕ → R :=
  fun l => if h : l < n then ⟨D j ⟨l, h⟩, hD.2.1 _ _⟩ else 0
end Cnt
end Formalism.FourierDecayAlt.P.A5x9
end
section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
namespace Formalism.FourierDecayAlt.P.A5x9
section Cnt
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
end Cnt
end Formalism.FourierDecayAlt.P.A5x9
end
section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
namespace Formalism.FourierDecayAlt.P.A5x9
section Shf
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
end Shf
end Formalism.FourierDecayAlt.P.A5x9
end
section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
namespace Formalism.FourierDecayAlt.P.A5x9
end Formalism.FourierDecayAlt.P.A5x9
end
section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
namespace Formalism.FourierDecayAlt.P.A5x9
noncomputable section
section Grp
variable {K : Type} [CommRing K] (R : Subring K) (k : ℕ)
def PPsub (N : ℕ) : Subgroup (upUniG K N) where
  carrier := {u | IsPP R k ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)}
  one_mem' := by
    show IsPP R k (((1 : upUniG K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
    simpa using isPP_one R k
  mul_mem' := by
    intro a b ha hb
    show IsPP R k (((a * b : upUniG K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
    simpa using isPP_mul R k ha hb
  inv_mem' := by
    intro a ha
    show IsPP R k (((a⁻¹ : upUniG K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
    simpa [Matrix.coe_units_inv] using isPP_inv R k ha
def kap (w : Point K) (q : Cos R w) :
    Quotient (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))) ×
      (upUniG K w.1.sum ⧸ PPsub R k w.1.sum) :=
  (q.1, QuotientGroup.mk q.2.out)
def base (w : Point K) (y : Quotient (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))) ×
    (upUniG K w.1.sum ⧸ PPsub R k w.1.sum)) : Matrix (Fin w.1.sum) (Fin w.1.sum) K :=
  orbZ w (y.1.out, y.2.out)
end Grp
end
end Formalism.FourierDecayAlt.P.A5x9
end
section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.A5x9
noncomputable section
section Top
variable {K : Type} [CommRing K] (R : Subring K)
def badN (k : ℕ) (w w' : Point K) (q : Cos R w × Cos R w') : ℕ :=
  Nat.card {φ : coker R (orbZ w (rep R q.1)) ≃ₗ[R] coker R (orbZ w' (rep R q.2)) //
    φ ∈ isoZZ R (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) ∧
      InTT R (k + 1) (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) φ ∧
      ¬ InTT R k (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) φ}
end Top
end
end Formalism.FourierDecayAlt.P.A5x9
end
section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.A5x9
noncomputable section
section Top
variable {K : Type} [CommRing K] (R : Subring K)
end Top
end
end Formalism.FourierDecayAlt.P.A5x9
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end


