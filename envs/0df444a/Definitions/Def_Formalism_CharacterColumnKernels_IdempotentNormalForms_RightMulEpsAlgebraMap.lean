-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:27:48.794458+00:00
-- url     : https://prove2.me/theorems/1e08b29e-0e2a-4547-b4c5-357b4d2a4cb5
-- title:
--   Right Mul Eps Algebra Map
-- statement:
--   Definitions and structural lemmas for Right Mul Eps Algebra Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/RightMulEpsAlgebraMap.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementMF
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
namespace Formalism.NG
namespace IdempotentImageSmul
section Adj
variable {O OO M Q : Type*} [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup M] [Module OO M]
    [Module O M] [IsScalarTower O OO M] [AddCommGroup Q] [Module O Q] (ε : OO)
def epsE : epsIdeal O ε := ⟨ε, LinearMap.mem_range.mpr ⟨1, by simp⟩⟩
lemma dual_smul_apply (a : OO) (φ : EpsDual O OO Q ε) (x : epsIdeal O ε) :
    (a • φ) x = φ (rightMulEps O ε a x) := rfl
lemma rightMulEps_algebraMap (c : O) (x : epsIdeal O ε) :
    rightMulEps O ε (algebraMap O OO c) x = c • x := by
  apply Subtype.ext
  show x.1 * algebraMap O OO c = c • x.1
  rw [Algebra.smul_def, Algebra.commutes]
variable {ε}
lemma smul_mem_epsImg (x : epsIdeal O ε) (m : M) : x.1 • m ∈ epsImg O (M := M) ε := by
  obtain ⟨y, hy⟩ := x.2
  simp only [LinearMap.mulLeft_apply] at hy
  refine ⟨y • m, ?_⟩
  show ε • (y • m) = x.1 • m
  rw [← hy, mul_smul]
variable (ε) [SMulCommClass OO O (EpsDual O OO Q ε)]
def fwd : (M →ₗ[OO] EpsDual O OO Q ε) →ₗ[O] (epsImg O (M := M) ε →ₗ[O] Q) where
  toFun Φ :=
    { toFun := fun y => Φ y.1 (epsE ε)
      map_add' := fun y z => by simp
      map_smul' := fun c y => by
        show Φ (c • y.1) (epsE ε) = c • Φ y.1 (epsE ε)
        rw [← algebraMap_smul OO c y.1, Φ.map_smul, dual_smul_apply, rightMulEps_algebraMap,
          map_smul] }
  map_add' Φ Ψ := rfl
  map_smul' c Φ := rfl
def bwdInner (ψ : epsImg O (M := M) ε →ₗ[O] Q) (m : M) : EpsDual O OO Q ε where
  toFun x := ψ ⟨x.1 • m, smul_mem_epsImg x m⟩
  map_add' x z := by
    rw [← map_add]; congr 1; apply Subtype.ext
    show (x.1 + z.1) • m = x.1 • m + z.1 • m
    rw [add_smul]
  map_smul' c x := by
    rw [← map_smul]; congr 1; apply Subtype.ext
    show (c • x.1) • m = c • (x.1 • m)
    rw [smul_assoc]
def bwd : (epsImg O (M := M) ε →ₗ[O] Q) →ₗ[O] (M →ₗ[OO] EpsDual O OO Q ε) where
  toFun ψ :=
    { toFun := bwdInner ε ψ
      map_add' := fun m m' => by
        apply LinearMap.ext; intro x
        show ψ ⟨x.1 • (m + m'), _⟩ = ψ ⟨x.1 • m, _⟩ + ψ ⟨x.1 • m', _⟩
        rw [← map_add]; congr 1; apply Subtype.ext
        show x.1 • (m + m') = x.1 • m + x.1 • m'
        rw [smul_add]
      map_smul' := fun a m => by
        apply LinearMap.ext; intro x
        show ψ ⟨x.1 • a • m, _⟩ = ψ ⟨(x.1 * a) • m, _⟩
        congr 1; apply Subtype.ext
        show x.1 • a • m = (x.1 * a) • m
        rw [mul_smul] }
  map_add' ψ ψ' := rfl
  map_smul' c ψ := rfl
variable {ε}
end Adj
section Matlis
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
def homQuotEquiv (a : O) :
    ((O ⧸ Ideal.span ({a} : Set O)) →ₗ[O] KO O) ≃ₗ[O]
      LinearMap.ker (matQ O (fun _ _ => a : Matrix Unit Unit O)) where
  toFun φ := ⟨fun _ => φ (Submodule.Quotient.mk 1), by
    rw [LinearMap.mem_ker]; funext i
    show ∑ _j : Unit, a • φ (Submodule.Quotient.mk 1) = 0
    rw [Fintype.sum_unique, ← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
      (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mem_span_singleton_self a), map_zero]⟩
  map_add' φ ψ := rfl
  map_smul' c φ := rfl
  invFun v := (Ideal.span ({a} : Set O)).liftQ (LinearMap.toSpanSingleton O _ (v.1 ())) (by
    rw [Ideal.span, Submodule.span_le, Set.singleton_subset_iff]
    show a • v.1 () = 0
    have h : (∑ j : Unit, a • v.1 j) = 0 := congrFun (LinearMap.mem_ker.mp v.2) ()
    rwa [Fintype.sum_unique] at h)
  left_inv φ := by
    apply LinearMap.ext; intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply]
      show x • φ (Submodule.Quotient.mk 1) = φ (Submodule.Quotient.mk x)
      rw [← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  right_inv v := by
    apply Subtype.ext; funext i
    show ((Ideal.span ({a} : Set O)).liftQ _ _) (Submodule.Quotient.mk 1) = v.1 i
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
end Matlis
end IdempotentImageSmul
open IdempotentImageSmul
end Formalism.NG


