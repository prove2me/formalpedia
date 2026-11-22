-- Prove2me | Definitions.Def_Formalism_LogSumExpBounds_StatementC
-- name    : Formalism_LogSumExpBounds_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:49:06.044634+00:00
-- url     : https://prove2.me/theorems/ae59e8fd-1f10-47d0-9f9b-6c6922410e38
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/StatementC.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.NuclearRankWeightBounds.C
open Matrix
section
variable (RR : Type*) (K : Type*) [CommRing RR] [CommRing K] [Algebra RR K]
abbrev KmodR : Type _ := K ⧸ LinearMap.range (Algebra.linearMap RR K)
variable {RR}
abbrev coker {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) : Type _ :=
  (Fin k → RR) ⧸ LinearMap.range Z.mulVecLin
def toK {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) : Matrix (Fin k) (Fin k) K :=
  Z.map (algebraMap RR K)
noncomputable def rowInvMod {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) (r : Fin k → K) :
    (Fin k → RR) →ₗ[RR] KmodR RR K :=
  (Submodule.mkQ _).comp
    { toFun := fun v => ∑ i, ∑ j, r i * (toK K Z)⁻¹ i j * algebraMap RR K (v j)
      map_add' := by intro v w; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        rw [RingHom.id_apply]
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        rw [Algebra.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring }
noncomputable def descend {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) (r : Fin k → K) :
    coker Z →ₗ[RR] KmodR RR K := by
  classical
  exact if hZ : LinearMap.range Z.mulVecLin ≤ LinearMap.ker (rowInvMod K Z r) then
    (LinearMap.range Z.mulVecLin).liftQ (rowInvMod K Z r) hZ else 0
variable {m : ℕ}
def ebar (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : coker Z :=
  Submodule.Quotient.mk (Pi.single (Fin.last m) 1)
noncomputable def lam (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : coker Z →ₗ[RR] KmodR RR K :=
  descend K Z (Pi.single (Fin.last m) 1)
noncomputable def kappa (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : K :=
  (toK K Z)⁻¹ (Fin.last m) (Fin.last m)
def blk (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : Matrix (Fin m) (Fin m) RR :=
  Z.submatrix Fin.castSucc Fin.castSucc
def bbar (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : coker (blk Z) :=
  Submodule.Quotient.mk (fun i => Z (Fin.castSucc i) (Fin.last m))
noncomputable def cval (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : K :=
  algebraMap RR K (Z (Fin.last m) (Fin.last m)) -
    ∑ i, ∑ j, algebraMap RR K (Z (Fin.last m) (Fin.castSucc i)) * (toK K (blk Z))⁻¹ i j *
      algebraMap RR K (Z (Fin.castSucc j) (Fin.last m))
noncomputable def alpha (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : coker (blk Z) →ₗ[RR] KmodR RR K :=
  descend K (blk Z) (fun j => algebraMap RR K (Z (Fin.last m) (Fin.castSucc j)))
end
def CornerInv : Prop :=
  ∀ (K : Type) [CommRing K] (m : ℕ) (Z : Matrix (Fin (m+1)) (Fin (m+1)) K),
    IsUnit Z.det → IsUnit (Z.submatrix Fin.castSucc Fin.castSucc).det →
    (Z (Fin.last m) (Fin.last m) -
      ∑ i, ∑ j, Z (Fin.last m) (Fin.castSucc i) *
        (Z.submatrix Fin.castSucc Fin.castSucc)⁻¹ i j * Z (Fin.castSucc j) (Fin.last m)) *
      Z⁻¹ (Fin.last m) (Fin.last m) = 1
def KappaMod : Prop :=
  ∀ (RR K : Type) [CommRing RR] [CommRing K] [Algebra RR K] (m₁ m₂ : ℕ)
    (Z₁ : Matrix (Fin (m₁+1)) (Fin (m₁+1)) RR) (Z₂ : Matrix (Fin (m₂+1)) (Fin (m₂+1)) RR),
    IsUnit (toK K Z₁).det → IsUnit (toK K Z₂).det →
    ∀ θ : coker Z₁ ≃ₗ[RR] coker Z₂, θ (ebar Z₁) = ebar Z₂ →
      (lam K Z₂).comp θ.toLinearMap = lam K Z₁ →
      kappa K Z₁ - kappa K Z₂ ∈ Set.range (algebraMap RR K)
def IsoTransfer : Prop :=
  ∀ (RR K : Type) [CommRing RR] [CommRing K] [Algebra RR K], Function.Injective (algebraMap RR K) →
    ∀ (m₁ m₂ : ℕ)
    (Z₁ : Matrix (Fin (m₁+1)) (Fin (m₁+1)) RR) (Z₂ : Matrix (Fin (m₂+1)) (Fin (m₂+1)) RR),
    IsUnit (toK K Z₁).det → IsUnit (toK K Z₂).det →
    IsUnit (toK K (blk Z₁)).det → IsUnit (toK K (blk Z₂)).det →
    kappa K Z₁ = kappa K Z₂ →
    Nonempty ({θ : coker Z₁ ≃ₗ[RR] coker Z₂ //
        θ (ebar Z₁) = ebar Z₂ ∧ (lam K Z₂).comp θ.toLinearMap = lam K Z₁} ≃
      {θ : coker (blk Z₁) ≃ₗ[RR] coker (blk Z₂) //
        θ (bbar Z₁) = bbar Z₂ ∧ (alpha K Z₂).comp θ.toLinearMap = alpha K Z₁})
def EssSurj : Prop :=
  ∀ (RR K : Type) [CommRing RR] [CommRing K] [Algebra RR K], Function.Injective (algebraMap RR K) →
    ∀ (m : ℕ) (Z' : Matrix (Fin m) (Fin m) RR) (b : Fin m → RR) (α : coker Z' →ₗ[RR] KmodR RR K)
      (c : K), IsUnit (toK K Z').det → IsUnit c →
      (Submodule.Quotient.mk c : KmodR RR K) = -α (Submodule.Quotient.mk b) →
      ∃ Z : Matrix (Fin (m+1)) (Fin (m+1)) RR, IsUnit (toK K Z).det ∧ blk Z = Z' ∧
        (fun i => Z (Fin.castSucc i) (Fin.last m)) = b ∧
        (∀ v, alpha K Z (Submodule.Quotient.mk v) = α (Submodule.Quotient.mk v)) ∧
        cval K Z = c
def CharSumIso : Prop :=
  ∀ (RR Q : Type) [CommRing RR] [AddCommGroup Q] [Module RR Q] (ψ : AddChar Q ℂ)
    (C₁ C₂ : Type) [AddCommGroup C₁] [Module RR C₁] [Fintype C₁]
    [AddCommGroup C₂] [Module RR C₂] [Fintype C₂]
    [Fintype (C₁ ≃ₗ[RR] C₂)] [Fintype (C₁ →ₗ[RR] Q)]
    (e₁ : C₁) (e₂ : C₂) (la₁ : C₁ →ₗ[RR] Q) (la₂ : C₂ →ₗ[RR] Q),
    Function.Bijective (fun α : C₁ →ₗ[RR] Q => ψ.compAddMonoidHom α.toAddMonoidHom) →
    ∑ θ : C₁ ≃ₗ[RR] C₂, ∑ α : C₁ →ₗ[RR] Q, ∑ β : C₁,
        ψ (α (e₁ - θ.symm e₂) + (la₁ - la₂ ∘ₗ θ.toLinearMap) β)
      = ((Fintype.card C₁ : ℂ) ^ 2) *
        (Nat.card {θ : C₁ ≃ₗ[RR] C₂ // θ e₁ = e₂ ∧ la₂ ∘ₗ θ.toLinearMap = la₁} : ℂ)
end Formalism.NuclearRankWeightBounds.C


