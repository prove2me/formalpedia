-- Prove2me | Definitions.Def_OAIQ031A035
-- name    : OAIQ031A035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:03:26.375531+00:00
-- url     : https://prove2.me/theorems/db7154d4-cba1-4ccb-bf0e-4c04cc14ac20
-- title:
--   Definitions bundle OAIQ031A035 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 8 definitions, 1 inductive type or structure and 17 theorems. The definitions and types are `OAI.ArExplicit.CompleteComparison.rawAugmentation`, `OAI.ArExplicit.FiniteLeftModule.canonicalEnvelope`, `OAI.ArExplicit.FrobeniusTrace.regularFromDual`, `OAI.ArExplicit.TateKoszul.Model`, `OAI.ArExplicit.TwistedBimodule.leftLinearEquiv`, `OAI.ArExplicit.VectorCochain.gradedMap`, `OAI.ArExplicit.VectorCochain.representativesNaturality`, `OAI.ArExplicit.fullHomHomotopyLinearEquiv`, `OAI.ArExplicit.fullHomShiftedHomotopyEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Algebras_BaseRadical`, `AuslanderReiten_Algebras_Radical`, `AuslanderReiten_Algebras_TensorRadical`, `AuslanderReiten_Algebras_TensorStructure`, `AuslanderReiten_Algebras_TrivialExtensionRadical`, `AuslanderReiten_Complete_CompleteFunctorRawEndpoint`, `AuslanderReiten_Complete_TateKoszul`, `AuslanderReiten_Duality_SymmetricStableDuality`, `AuslanderReiten_HomComplex_FullHomShiftedHomotopy`, `AuslanderReiten_Homology_TriangleHomExact`, `AuslanderReiten_Homology_VectorCochainNaturality`, `AuslanderReiten_Modules_TwistedBimodule`, `AuslanderReiten_Resolutions_BinaryKoszul`, `AuslanderReiten_Stable_CanonicalCosyzygy`.
--
--   **Imports.** It imports the bundles `OAIQ031A001`, `OAIQ031A002`, `OAIQ031A003`, `OAIQ031A006`, `OAIQ031A010`, `OAIQ031A011`, `OAIQ031A012`, `OAIQ031A013` and `OAIQ031A016` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A050`, `OAIQ031A051`, `OAIQ031A052`, `OAIQ031A053`, `OAIQ031A055`, `OAIQ031A056`, `OAIQ031A057`, `OAIQ031A058`, `OAIQ031A059` and `OAIQ031A060`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A001
import Definitions.Def_OAIQ031A002
import Definitions.Def_OAIQ031A003
import Definitions.Def_OAIQ031A006
import Definitions.Def_OAIQ031A010
import Definitions.Def_OAIQ031A011
import Definitions.Def_OAIQ031A012
import Definitions.Def_OAIQ031A013
import Definitions.Def_OAIQ031A016

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_Radical
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable {R S : Type*} [Ring R] [Ring S]

theorem jacobson_eq_comap_of_nil_kernel (f : R →+* S)
    (hf : Function.Surjective f) (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
    Ring.jacobson R = Ideal.comap f (Ring.jacobson S) := by
  let : RingHomSurjective f := ⟨hf⟩
  exact (Module.comap_jacobson_of_ker_le (f := f.toSemilinearMap) hf
    (nilIdeal_le_jacobson (RingHom.ker f) hker)).symm

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_BaseRadical
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BaseAlgebra

open ArExplicit.Letter

variable {k : Type*} [Field k] (q : k)

theorem eCharacter_surjective : Function.Surjective (eCharacter q) := by
  intro a
  refine ⟨a • basisVector q e, ?_⟩
  change (a • basisVector q e).coeff e = a
  simp

theorem fCharacter_surjective : Function.Surjective (fCharacter q) := by
  intro a
  refine ⟨a • basisVector q f, ?_⟩
  change (a • basisVector q f).coeff f = a
  simp

theorem mem_jacobson_iff (a : BaseAlgebra k q) :
    a ∈ Ring.jacobson (BaseAlgebra k q) ↔ a.coeff e = 0 ∧ a.coeff f = 0 := by
  constructor
  · intro ha
    have : RingHomSurjective (eCharacter q) := ⟨eCharacter_surjective q⟩
    have : RingHomSurjective (fCharacter q) := ⟨fCharacter_surjective q⟩
    have he := Ring.le_comap_jacobson (eCharacter q) ha
    have hf := Ring.le_comap_jacobson (fCharacter q) ha
    rw [field_jacobson] at he hf
    exact ⟨he, hf⟩
  · rintro ⟨he, hf⟩
    have hn : RingHom.ker (diagonal q) ≤ Ring.jacobson (BaseAlgebra k q) := by
      apply ArExplicit.nilIdeal_le_jacobson
      intro b hb
      change (b.coeff e, b.coeff f) = (0, 0) at hb
      exact ⟨5, fifth_power_eq_zero q b (congrArg Prod.fst hb) (congrArg Prod.snd hb)⟩
    apply hn
    change (a.coeff e, a.coeff f) = (0, 0)
    exact Prod.ext he hf

end ArExplicit.BaseAlgebra

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorRadical
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

variable {k R S : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

theorem mem_rightTensorIdeal_iff (I : Ideal S) (x : R ⊗[k] S) :
    x ∈ rightTensorIdeal (R := R) I ↔
      ∃ z : R ⊗[k] (I.restrictScalars k),
        LinearMap.lTensor R (I.restrictScalars k).subtype z = x := by
  change x ∈ (rightTensorIdeal I).restrictScalars k ↔ _
  rw [rightTensorIdeal, Ideal.map_includeRight_eq]
  rfl

theorem tmul_mem_rightTensorIdeal (I : Ideal S) (r : R) {s : S} (hs : s ∈ I) :
    r ⊗ₜ[k] s ∈ rightTensorIdeal (R := R) I := by
  apply (mem_rightTensorIdeal_iff I _).mpr
  exact ⟨r ⊗ₜ[k] ⟨s, hs⟩, rfl⟩

theorem rightTensorIdeal_mul_le (I J : Ideal S) :
    rightTensorIdeal (k := k) (R := R) I * rightTensorIdeal J ≤ rightTensorIdeal (I * J) := by
  apply Ideal.mul_le.mpr
  intro x hx y hy
  obtain ⟨x, rfl⟩ := (mem_rightTensorIdeal_iff I x).mp hx
  obtain ⟨y, rfl⟩ := (mem_rightTensorIdeal_iff J y).mp hy
  clear hx hy
  induction x with
  | zero => simp
  | add x x' hx hx' => simpa only [map_add, add_mul] using
      (rightTensorIdeal (I * J)).add_mem hx hx'
  | tmul r x =>
      induction y with
      | zero => simp
      | add y y' hy hy' => simpa only [map_add, mul_add] using
          (rightTensorIdeal (I * J)).add_mem hy hy'
      | tmul r' y =>
          simpa only [LinearMap.lTensor_tmul, Submodule.coe_subtype,
            Algebra.TensorProduct.tmul_mul_tmul] using
            tmul_mem_rightTensorIdeal (I * J) (r * r') (Ideal.mul_mem_mul x.property y.property)

theorem rightTensorIdeal_pow_le (I : Ideal S) (n : ℕ) :
    (rightTensorIdeal (k := k) (R := R) I) ^ n ≤ rightTensorIdeal (I ^ n) := by
  induction n with
  | zero =>
      simp only [Submodule.pow_zero, Ideal.one_eq_top, rightTensorIdeal, Ideal.map_top]
      exact le_rfl
  | succ n hn =>
      rw [Submodule.pow_succ, Submodule.pow_succ]
      exact (Ideal.mul_mono_left hn).trans (rightTensorIdeal_mul_le (I ^ n) I)

theorem rightTensorIdeal_isNilpotent (I : Ideal S) (hI : IsNilpotent I) :
    IsNilpotent (rightTensorIdeal (k := k) (R := R) I) := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  apply le_antisymm _ bot_le
  have h := rightTensorIdeal_pow_le (k := k) (R := R) I n
  simpa only [hn, Ideal.zero_eq_bot, rightTensorIdeal, Ideal.map_bot] using h

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TrivialExtensionRadical
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.TrivialExtension

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

theorem mul_eq_zero_of_base_eq_zero (a b : TrivialExtension k A)
    (ha : a.base = 0) (hb : b.base = 0) : a * b = 0 := by
  apply TrivialExtension.ext
  · simp [ha, hb]
  · ext c
    simp [ha, hb]

end ArExplicit.TrivialExtension

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorStructure
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

namespace A

variable {k : Type*} [Field k] (q : k)

theorem quotient_jacobson : Ring.jacobson ((k × k) ⊗[k] (k × k)) = ⊥ :=
  jacobson_eq_bot_of_equiv (quotientCoordinates (k := k)).toRingEquiv
    (jacobson_prod_eq_bot
      (jacobson_prod_eq_bot (field_jacobson_eq_bot k) (field_jacobson_eq_bot k))
      (jacobson_prod_eq_bot (field_jacobson_eq_bot k) (field_jacobson_eq_bot k)))

end A
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteFunctorRawEndpoint
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ArExplicit.CompleteComparison
universe u
variable {R S : Type u} [Ring R] [Ring S]

def rawAugmentation (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    K.X 0 ⟶ ModuleCat.of R (CochainCokernel K) :=
  ModuleCat.ofHom (LinearMap.range (K.d (-1) 0).hom).mkQ

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_BinaryKoszul
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [CommRing k]

theorem row_surjective (n : ℕ) : Function.Surjective (row k n) := by
  intro f
  let u : Piece k n := Pi.single (Fin.last n) (f (Fin.last (n + 1)))
  let v : Piece k n := fun i => f i.castSucc
  refine ⟨(u, v), ?_⟩
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [row, mulX, mulY, u]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [row, mulX, mulY, v]
    · simp [row, mulX, mulY, u, v]

end ArExplicit.BinaryKoszul

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_TateKoszul
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TateKoszul

universe u
variable {k : Type u} [Field k]
variable (H : ℤ → Type u) [∀ a, AddCommGroup (H a)] [∀ a, Module k (H a)]

variable {H}

structure Model (x y : ∀ a : ℤ, H a →ₗ[k] H (a + 3)) where
  positive : ∀ n : ℕ, H (3 * (n : ℤ)) ≃ₗ[k] BinaryKoszul.Piece k n
  negative : ∀ n : ℕ, H (-1 - 3 * (n : ℤ)) ≃ₗ[k] BinaryKoszul.DualPiece k n
  outside : ∀ a : ℤ, (∀ n : ℕ, a ≠ 3 * (n : ℤ)) →
    (∀ n : ℕ, a ≠ -1 - 3 * (n : ℤ)) → Subsingleton (H a)
  positive_x : ∀ (a : ℤ) (n : ℕ) (ha : a = 3 * (n : ℤ)) (v : H a),
    ((degreeEquiv H (show a + 3 = 3 * ((n + 1 : ℕ) : ℤ) by omega)).trans
      (positive (n + 1))) (x a v) =
    BinaryKoszul.mulX k n (((degreeEquiv H ha).trans (positive n)) v)
  positive_y : ∀ (a : ℤ) (n : ℕ) (ha : a = 3 * (n : ℤ)) (v : H a),
    ((degreeEquiv H (show a + 3 = 3 * ((n + 1 : ℕ) : ℤ) by omega)).trans
      (positive (n + 1))) (y a v) =
    BinaryKoszul.mulY k n (((degreeEquiv H ha).trans (positive n)) v)
  negative_x : ∀ (a : ℤ) (n : ℕ) (ha : a = -1 - 3 * ((n + 1 : ℕ) : ℤ)) (v : H a),
    ((degreeEquiv H (show a + 3 = -1 - 3 * (n : ℤ) by omega)).trans
      (negative n)) (x a v) =
    (BinaryKoszul.mulX k n).dualMap
      (((degreeEquiv H ha).trans (negative (n + 1))) v)
  negative_y : ∀ (a : ℤ) (n : ℕ) (ha : a = -1 - 3 * ((n + 1 : ℕ) : ℤ)) (v : H a),
    ((degreeEquiv H (show a + 3 = -1 - 3 * (n : ℤ) by omega)).trans
      (negative n)) (y a v) =
    (BinaryKoszul.mulY k n).dualMap
      (((degreeEquiv H ha).trans (negative (n + 1))) v)

end ArExplicit.TateKoszul

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_SymmetricStableDuality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.FrobeniusTrace

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable {M N : Type u} [AddCommGroup M] [Module R M] [Module k M]
variable [IsScalarTower k R M] [AddCommGroup N] [Module R N] [Module k N]
variable [IsScalarTower k R N]

noncomputable def regularFromDual (φ : Module.Dual k M) : M →ₗ[R] R :=
  τ.leftEquiv.symm.toLinearMap.comp (Coinduced.adjoint φ)

theorem trace_leftEquiv_symm (v : Coinduced k R) :
    τ.trace (τ.leftEquiv.symm v) = v.functional 1 := by
  have h := τ.leftEquiv_apply (τ.leftEquiv.symm v) 1
  simpa using h.symm

end ArExplicit.FrobeniusTrace

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TriangleHomExact
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory CategoryTheory.Pretriangulated
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit

universe u v w

section Homotopy

variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable (K L : CochainComplex C ℤ) (n : ℤ)

noncomputable def fullHomHomotopyLinearEquiv :
    CohomologyClass K L n ≃ₗ[k]
      ((HomotopyCategory.quotient C _).obj K ⟶
        (HomotopyCategory.quotient C _).obj (L⟦n⟧)) :=
  { CohomologyClass.homAddEquiv with
    map_smul' := by
      intro a x
      obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
      change CohomologyClass.toHom (CohomologyClass.mk (a • x)) =
        a • CohomologyClass.toHom (CohomologyClass.mk x)
      rw [CohomologyClass.toHom_mk, CohomologyClass.toHom_mk,
        CompleteComparison.cocycleHom_smul, Functor.map_smul] }

end Homotopy

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomShiftedHomotopy
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable (K L : CochainComplex C ℤ) (n : ℤ)

def fullHomShiftedHomotopyEquiv : CohomologyClass K L n ≃ₗ[k]
    ((HomotopyCategory.quotient C _).obj K ⟶ ((HomotopyCategory.quotient C _).obj L)⟦n⟧) :=
  (fullHomHomotopyLinearEquiv k K L n).trans
    (Linear.homCongr k (Iso.refl _)
      (((HomotopyCategory.quotient C _).commShiftIso n).app L))

@[simp]
theorem fullHomShiftedHomotopyEquiv_mk (x : Cocycle K L n) :
    fullHomShiftedHomotopyEquiv k K L n (CohomologyClass.mk x) =
      (HomotopyCategory.quotient C _).map (Cocycle.equivHomShift.symm x) ≫
        (((HomotopyCategory.quotient C _).commShiftIso n).app L).hom := by
  simp only [fullHomShiftedHomotopyEquiv, LinearEquiv.trans_apply,
    Linear.homCongr_apply, Iso.refl_inv, Category.id_comp]
  rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_VectorCochainNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.VectorCochain
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (k : Type u) [Field k]

@[reassoc] theorem zeroHomologyIso_natural {X Y : ℕ → ModuleCat.{u} k}
    (f : zeroDifferential k X ⟶ zeroDifferential k Y) (n : ℕ) :
    homologyMap f n ≫ (zeroHomologyIso k Y n).hom =
      (zeroHomologyIso k X n).hom ≫ f.f n := by
  apply (cancel_epi ((zeroDifferential k X).homologyπ n)).1
  rw [homologyπ_naturality_assoc, zeroHomologyIso_π, ← Category.assoc,
    zeroHomologyIso_π]
  simp

variable {P Q : CochainComplex (ModuleCat.{u} k) ℕ}

def gradedMap (f : P ⟶ Q) : gradedHomology k P ⟶ gradedHomology k Q where
  f n := homologyMap f n
  comm' _ _ _ := by simp [gradedHomology, zeroDifferential]

@[simp] theorem homologyMap_splitting_inv (n : ℕ) :
    homologyMap (splitting k P).inv n =
      (zeroHomologyIso k (fun i => P.homology i) n).inv := by
  have he : (splitting k P).toHomologyIso n =
      zeroHomologyIso k (fun i => P.homology i) n := by
    apply Iso.ext
    change homologyMap (splitting k P).hom n = _
    rw [splitting_hom, homologyMap_representatives]
  exact congrArg Iso.inv he

theorem representatives_comp_splitting_inv (f : P ⟶ Q) :
    representatives k P ≫ f ≫ (splitting k Q).inv = gradedMap k f := by
  ext n : 1
  apply (cancel_epi (zeroHomologyIso k (fun i => P.homology i) n).hom).1
  calc
    (zeroHomologyIso k (fun i => P.homology i) n).hom ≫
        (representatives k P ≫ f ≫ (splitting k Q).inv).f n =
      homologyMap (representatives k P ≫ f ≫ (splitting k Q).inv) n ≫
        (zeroHomologyIso k (fun i => Q.homology i) n).hom :=
      (zeroHomologyIso_natural k _ n).symm
    _ = (zeroHomologyIso k (fun i => P.homology i) n).hom ≫ (gradedMap k f).f n := by
      simp only [homologyMap_comp, homologyMap_representatives, homologyMap_splitting_inv,
        Category.assoc, Iso.inv_hom_id, Category.comp_id, gradedMap]

def representativesNaturality (f : P ⟶ Q) :
    Homotopy (representatives k P ≫ f) (gradedMap k f ≫ representatives k Q) := by
  have hh := ((splitting k Q).homotopyInvHomId.compLeftId
    (representatives k P ≫ f)).symm
  have he : (representatives k P ≫ f) ≫
      ((splitting k Q).inv ≫ (splitting k Q).hom) =
      gradedMap k f ≫ representatives k Q := by
    rw [splitting_hom, ← Category.assoc, Category.assoc (representatives k P) f,
      representatives_comp_splitting_inv]
  exact hh.trans (Homotopy.ofEq he)

end ArExplicit.VectorCochain

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TwistedBimodule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace TwistedBimodule

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

def leftLinearEquiv : TwistedBimodule k R σ ≃ₗ[R] R := (coordinates σ).addEquiv.linearEquiv R

end TwistedBimodule
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_CanonicalCosyzygy
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.FiniteLeftModule

open CategoryTheory

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

def canonicalEnvelope (M : FiniteLeftModule k R) : ModuleCat.{u} R :=
  ModuleCat.of R (CoinducedModule k R M.carrier)

end ArExplicit.FiniteLeftModule

end

end OAI
end


