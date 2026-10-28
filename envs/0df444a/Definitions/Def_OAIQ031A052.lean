-- Prove2me | Definitions.Def_OAIQ031A052
-- name    : OAIQ031A052
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:07:17.132296+00:00
-- url     : https://prove2.me/theorems/51a3cafa-da3a-4ee4-b5af-465ef526f2b4
-- title:
--   Definitions bundle OAIQ031A052 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 10 definitions, 1 instance and 18 theorems. The definitions and types are `OAI.ArExplicit.CompleteComparison.fullHomRightMultiply`, `OAI.ArExplicit.ExternalBalanced.exteriorBimodule`, `OAI.ArExplicit.ExternalTensor.envelopingObject`, `OAI.ArExplicit.FrobeniusTrace.dualModuleHomEquiv`, `OAI.ArExplicit.FrobeniusTrace.freeHomDualEquiv`, `OAI.ArExplicit.FrobeniusTrace.freeTrace`, `OAI.ArExplicit.FrobeniusTrace.opposite`, `OAI.ArExplicit.LinearHomology.congr`, `OAI.ArExplicit.T.evaluateAtSimple`, `OAI.ArExplicit.T.squareEvaluation`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Algebras_FrobeniusOpposite`, `AuslanderReiten_Algebras_TensorRadical`, `AuslanderReiten_Algebras_TensorStructure`, `AuslanderReiten_Algebras_TrivialExtensionRadical`, `AuslanderReiten_Bar_TCasimirEvaluation`, `AuslanderReiten_Bar_TCasimirSquare`, `AuslanderReiten_Duality_SymmetricStableDuality`, `AuslanderReiten_Ext_CubicExtAction`, `AuslanderReiten_HomComplex_FullHomProductLinear`, `AuslanderReiten_Homology_LinearHomologyCongr`, `AuslanderReiten_Modules_TrivialInduction`, `AuslanderReiten_Tensor_ExternalBalancedCoordinates`, `AuslanderReiten_Tensor_ExternalEnveloping`.
--
--   **Imports.** It imports the bundles `OAIQ031A025`, `OAIQ031A026`, `OAIQ031A030`, `OAIQ031A031`, `OAIQ031A032`, `OAIQ031A033`, `OAIQ031A034` and `OAIQ031A035` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A068`, `OAIQ031A071`, `OAIQ031A072`, `OAIQ031A073`, `OAIQ031A074` and `OAIQ031A076`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A025
import Definitions.Def_OAIQ031A026
import Definitions.Def_OAIQ031A030
import Definitions.Def_OAIQ031A031
import Definitions.Def_OAIQ031A032
import Definitions.Def_OAIQ031A033
import Definitions.Def_OAIQ031A034
import Definitions.Def_OAIQ031A035

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorRadical
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

variable {k R S : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

variable {R' S' : Type*} [Ring R'] [Ring S'] [Algebra k R'] [Algebra k S']

theorem tensor_radical_eq_kernel (f : R →ₐ[k] R') (g : S →ₐ[k] S')
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hfnil : IsNilpotent (RingHom.ker f)) (hgnil : IsNilpotent (RingHom.ker g))
    (hquot : Ring.jacobson (R' ⊗[k] S') = ⊥) :
    Ring.jacobson (R ⊗[k] S) = RingHom.ker (Algebra.TensorProduct.map f g) := by
  let p : R ⊗[k] S →ₐ[k] R' ⊗[k] S' := Algebra.TensorProduct.map f g
  let : RingHomSurjective p.toRingHom := ⟨Algebra.TensorProduct.map_surjective f g hf hg⟩
  apply le_antisymm
  · intro x hx
    have h := Ring.le_comap_jacobson p.toRingHom hx
    simpa only [hquot, Ideal.mem_comap, Ideal.mem_bot, RingHom.mem_ker, p,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h
  · rw [Algebra.TensorProduct.map_ker f g hf hg]
    exact sup_le
      (nilpotentIdeal_le_jacobson _ (leftTensorIdeal_isNilpotent _ hfnil))
      (nilpotentIdeal_le_jacobson _ (rightTensorIdeal_isNilpotent _ hgnil))

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TrivialExtensionRadical
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.TrivialExtension

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

theorem radical_eq_comap :
    Ring.jacobson (TrivialExtension k A) =
      Ideal.comap projection (Ring.jacobson A) := by
  apply jacobson_eq_comap_of_nil_kernel _ projection_surjective
  intro a ha
  exact ⟨2, by simpa only [pow_two] using mul_eq_zero_of_base_eq_zero a a ha ha⟩

theorem mem_jacobson_iff (a : TrivialExtension k A) :
    a ∈ Ring.jacobson (TrivialExtension k A) ↔ a.base ∈ Ring.jacobson A := by
  rw [radical_eq_comap]
  rfl

end ArExplicit.TrivialExtension

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)

theorem radical_eq_ker_diagonal :
    Ring.jacobson (T k q) = RingHom.ker (diagonalAlg q) := by
  ext a
  rw [TrivialExtension.mem_jacobson_iff, BaseAlgebra.mem_jacobson_iff]
  change (a.base.coeff Letter.e = 0 ∧ a.base.coeff Letter.f = 0) ↔
    (a.base.coeff Letter.e, a.base.coeff Letter.f) = (0, 0)
  simp only [Prod.mk.injEq]

end ArExplicit.T

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorStructure
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

namespace A

variable {k : Type*} [Field k] (q : k)

theorem radical_eq_ker_tensorMap :
    Ring.jacobson (A k q) = RingHom.ker (quotientTensorMap q) := by
  have hnil : IsNilpotent (RingHom.ker (T.diagonalAlg q)) := by
    rw [← T.radical_eq_ker_diagonal]
    exact finiteAlgebra_radical_isNilpotent (k := k)
  exact tensor_radical_eq_kernel (T.diagonalAlg q) (T.diagonalAlg q)
    (T.diagonalAlg_surjective q) (T.diagonalAlg_surjective q) hnil hnil quotient_jacobson

theorem radical_eq_ker_diagonal :
    Ring.jacobson (A k q) = RingHom.ker (diagonalAlg q) := by
  rw [radical_eq_ker_tensorMap]
  ext a
  change quotientTensorMap q a = 0 ↔
    (quotientCoordinates (k := k)) (quotientTensorMap q a) = 0
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply (quotientCoordinates (k := k)).injective
    simpa only [map_zero] using h

end A
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_FrobeniusOpposite
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.FrobeniusTrace

variable {k R : Type*} [Field k] [Ring R] [Algebra k R]
variable (τ : FrobeniusTrace k R)
variable (hsym : ∀ a b, τ.trace (a * b) = τ.trace (b * a))

def opposite : FrobeniusTrace k Rᵐᵒᵖ where
  trace :=
    { toFun := fun a => τ.trace a.unop
      map_add' a b := τ.trace.map_add a.unop b.unop
      map_smul' a b := τ.trace.map_smul a b.unop }
  separates a ha := by
    apply MulOpposite.unop_injective
    change a.unop = 0
    apply τ.separates
    intro b
    rw [hsym]
    exact ha (MulOpposite.op b)

@[simp] theorem opposite_trace (a : Rᵐᵒᵖ) : (opposite τ hsym).trace a = τ.trace a.unop := rfl

end ArExplicit.FrobeniusTrace

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TCasimirEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q
local notation "S" => Resolution.Simple q

def evaluateAtSimple (s : S) : R ⊗[k] R →ₗ[k] R ⊗[k] S :=
  TensorProduct.map (LinearMap.id : R →ₗ[k] R) (simpleActionAt q s)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TCasimirSquare
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q
local notation "S" => Resolution.Simple q

def squareEvaluation (s t : S) : (R ⊗[k] R) ⊗[k] (R ⊗[k] R) →ₗ[k]
    (R ⊗[k] R) ⊗[k] (S ⊗[k] S) :=
  (TensorProduct.tensorTensorTensorComm k R S R S).toLinearMap.comp
    (TensorProduct.map (evaluateAtSimple q s) (evaluateAtSimple q t))

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_SymmetricStableDuality
attribute [-instance] _root_.OAI.ArExplicit.Coinduced.instModuleMulOpposite _root_.OAI.ArExplicit.Coinduced.instSMulCommClassMulOpposite _root_.OAI.ArExplicit.Coinduced.instSMulCommClassMulOpposite_1 _root_.OAI.ArExplicit.Coinduced.instSMulMulOpposite _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

@[simp]
theorem dualFromRegular_regularFromDual (φ : Module.Dual k M) :
    τ.dualFromRegular (τ.regularFromDual φ) = φ := by
  ext x
  exact (τ.trace_leftEquiv_symm (Coinduced.adjoint φ x)).trans
    (Coinduced.adjoint_eval_one φ x)

@[simp]
theorem regularFromDual_dualFromRegular (f : M →ₗ[R] R) :
    τ.regularFromDual (τ.dualFromRegular f) = f := by
  ext x
  apply τ.leftEquiv.injective
  change τ.leftEquiv (τ.leftEquiv.symm (Coinduced.adjoint (τ.dualFromRegular f) x)) =
    τ.leftEquiv (f x)
  rw [τ.leftEquiv.apply_symm_apply]
  ext r
  change τ.trace (f (r • x)) = (τ.leftEquiv (f x)).functional r
  rw [map_smul, τ.leftEquiv_apply]
  rfl

noncomputable def dualModuleHomEquiv : Module.Dual k M ≃ₗ[k] (M →ₗ[R] R) where
  toFun := τ.regularFromDual
  invFun := τ.dualFromRegular
  left_inv := τ.dualFromRegular_regularFromDual
  right_inv := τ.regularFromDual_dualFromRegular
  map_add' φ ψ := by
    ext x
    apply τ.leftEquiv.injective
    simp only [regularFromDual, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.add_apply, map_add]
    ext r
    rfl
  map_smul' c φ := by
    ext x
    apply τ.leftEquiv.injective
    change τ.leftEquiv (τ.leftEquiv.symm (Coinduced.adjoint (c • φ) x)) =
      τ.leftEquiv (c • τ.leftEquiv.symm (Coinduced.adjoint φ x))
    rw [τ.leftEquiv.apply_symm_apply]
    have hs := (τ.leftEquiv.restrictScalars k).map_smul c
      (τ.leftEquiv.symm (Coinduced.adjoint (R := R) φ x))
    change τ.leftEquiv (c • τ.leftEquiv.symm (Coinduced.adjoint (R := R) φ x)) =
      c • τ.leftEquiv (τ.leftEquiv.symm (Coinduced.adjoint (R := R) φ x)) at hs
    rw [τ.leftEquiv.apply_symm_apply] at hs
    rw [hs]
    ext r
    rfl

variable [SMulCommClass R k M]

noncomputable def freeHomDualEquiv (r : ℕ) :
    Module.Dual k ((Fin r → R) →ₗ[R] M) ≃ₗ[k] (M →ₗ[R] (Fin r → R)) :=
  (LinearEquiv.piRing R M (Fin r) k).symm.dualMap |>.trans
    ((LinearMap.lsum k (fun _ : Fin r => M) k).symm.trans
      ((LinearEquiv.piCongrRight (fun _ : Fin r => τ.dualModuleHomEquiv)).trans
        (LinearEquiv.linearMapPi k)))

theorem freeHomDualEquiv_symm_apply (r : ℕ) (g : M →ₗ[R] (Fin r → R))
    (f : (Fin r → R) →ₗ[R] M) :
    (τ.freeHomDualEquiv r).symm g f =
      ∑ i : Fin r, τ.trace (g (f (Pi.single i 1)) i) := by
  simp [freeHomDualEquiv, LinearMap.lsum_apply, LinearEquiv.piRing_apply,
    dualModuleHomEquiv, dualFromRegular]

def freeTrace (r : ℕ) (f : (Fin r → R) →ₗ[R] (Fin r → R)) : k :=
  ∑ i : Fin r, τ.trace (f (Pi.single i 1) i)

omit [Module.Finite k R] in
theorem trace_map_coordinate {r s : ℕ} (f : (Fin r → R) →ₗ[R] (Fin s → R))
    (v : Fin r → R) (i : Fin s) :
    τ.trace (f v i) = ∑ j : Fin r, τ.trace (v j * f (Pi.single j 1) i) := by
  rw [free_map_apply r f v]
  simp

omit [Module.Finite k R] in

theorem freeTrace_cyclic (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
    {r s : ℕ} (a : (Fin r → R) →ₗ[R] (Fin s → R))
    (b : (Fin s → R) →ₗ[R] (Fin r → R)) :
    τ.freeTrace r (b.comp a) = τ.freeTrace s (a.comp b) := by
  simp only [freeTrace, LinearMap.comp_apply]
  simp_rw [τ.trace_map_coordinate]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact hs _ _

theorem freeHomDual_naturality_source
    (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
    {r s : ℕ} (a : (Fin r → R) →ₗ[R] (Fin s → R))
    (f : (Fin s → R) →ₗ[R] M) (g : M →ₗ[R] (Fin r → R)) :
    (τ.freeHomDualEquiv r).symm g (f.comp a) =
      (τ.freeHomDualEquiv s).symm (a.comp g) f := by
  rw [freeHomDualEquiv_symm_apply, freeHomDualEquiv_symm_apply]
  exact τ.freeTrace_cyclic hs a (g.comp f)

end ArExplicit.FrobeniusTrace

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_CubicExtAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (hp : ∀ n, p (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ p n)
include hp

include k in
omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem cubicPrecomp_cochain {n : ℕ} (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f=0) :
    (closedCochain P (p n ≫ f) (cubicPrecomp_closed P p hp f hf)).val =
      (natCubicCocycle (k := k) P p hp).val.comp (closedCochain P f hf).val
        (by omega : (3 : ℤ)+(n : ℤ)=((n+3 : ℕ) : ℤ)) := by
  apply (Cochain.toSingleEquiv (show -((n+3 : ℕ) : ℤ)+((n+3 : ℕ) : ℤ)=0 by omega)).injective
  change (Cochain.toSingleMk ((P.cochainComplexXIso (-((n+3 : ℕ) : ℤ)) (n+3) rfl).hom ≫ p n ≫ f)
    (by omega)).v (-((n+3 : ℕ) : ℤ)) 0 (by omega) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom =
    (((natCubicCocycle (k := k) P p hp).val.comp (closedCochain P f hf).val (by omega)).v
      (-((n+3 : ℕ) : ℤ)) 0 (by omega)) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom
  rw [Cochain.toSingleMk_v]
  erw [Cochain.comp_v _ _ _ _ (-(n : ℤ)) 0 (by omega) (by omega)]
  change _ = ((natCubicCochain P p).v (-((n+3 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) ≫
    (Cochain.toSingleMk ((P.cochainComplexXIso (-(n : ℤ)) n rfl).hom ≫ f)
      (by omega)).v (-(n : ℤ)) 0 (by omega)) ≫ _
  rw [Cochain.toSingleMk_v]
  have h := natCubicCochain_v P p n
  rw [h]
  let e := P.cochainComplexXIso (-(n : ℤ)) n rfl
  let e₃ := P.cochainComplexXIso (-((n+3 : ℕ) : ℤ)) (n+3) rfl
  let s := HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y
  exact (congrArg (fun z => ((e₃.hom ≫ p n ≫ z ≫ f) ≫ s.inv) ≫ s.hom)
    e.inv_hom_id).symm

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomProductLinear
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u v
variable {k : Type u} [CommRing k]
variable {C : Type v} [Category* C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} {n m : ℤ}

theorem fullHomProduct_add_left (x x' : CohomologyClass K L n)
    (y : CohomologyClass L M m) :
    fullHomProduct (x+x') y = fullHomProduct x y + fullHomProduct x' y := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨x',rfl⟩ := CohomologyClass.mk_surjective x'
  obtain ⟨y,rfl⟩ := CohomologyClass.mk_surjective y
  rw [← CohomologyClass.mk_add, fullHomProduct_mk, fullHomProduct_mk, fullHomProduct_mk,
    ← CohomologyClass.mk_add]
  congr 1
  apply Subtype.ext
  exact Cochain.add_comp x.val x'.val y.val rfl

def fullHomRightMultiply (y : CohomologyClass L M m) :
    CohomologyClass K L n →ₗ[k] CohomologyClass K M (n+m) where
  toFun x := fullHomProduct x y
  map_add' x x' := fullHomProduct_add_left x x' y
  map_smul' c x := fullHomProduct_smul_left c x y

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_LinearHomologyCongr
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.LinearHomology

universe u

variable {k : Type u} [Field k]
variable {U V W U' V' W' : Type u}
variable [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W] [AddCommGroup U'] [Module k U']
variable [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']
variable (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0)
variable (f' : U' →ₗ[k] V') (g' : V' →ₗ[k] W') (h' : g'.comp f' = 0)
variable (a : U ≃ₗ[k] U') (b : V ≃ₗ[k] V') (c : W ≃ₗ[k] W')
variable (hf : ∀ x, b (f x) = f' (a x)) (hg : ∀ x, c (g x) = g' (b x))

include a hf in
theorem cycleEquiv_boundaries :
    (boundaries f g h).map (cycleEquiv g g' b c hg).toLinearMap = boundaries f' g' h' := by
  ext y
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨a u, Subtype.ext (hf u).symm⟩
  · rintro ⟨u, rfl⟩
    refine ⟨cycleMap f g h (a.symm u), ⟨a.symm u, rfl⟩, ?_⟩
    apply Subtype.ext
    change b (f (a.symm u)) = f' u
    rw [hf, a.apply_symm_apply]

def congr : Homology f g h ≃ₗ[k] Homology f' g' h' :=
  Submodule.Quotient.equiv _ _ (cycleEquiv g g' b c hg)
    (cycleEquiv_boundaries f g h f' g' h' a b c hf hg)

@[simp]
theorem congr_mk (x : LinearMap.ker g) :
    congr f g h f' g' h' a b c hf hg ((boundaries f g h).mkQ x) =
      (boundaries f' g' h').mkQ (cycleEquiv g g' b c hg x) := rfl

@[simp]
theorem congr_symm_mk (x : LinearMap.ker g') :
    (congr f g h f' g' h' a b c hf hg).symm ((boundaries f' g' h').mkQ x) =
      (boundaries f g h).mkQ ((cycleEquiv g g' b c hg).symm x) := rfl

end ArExplicit.LinearHomology

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TrivialInduction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TrivialInduction

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

local notation "T" => TrivialExtension k R

instance instIsScalarTowerTrivialExtensionCoinduced : IsScalarTower k T (Coinduced k R) where
  smul_assoc a t φ := smul_assoc a t.base φ

end ArExplicit.TrivialInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalEnveloping
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct

namespace ArExplicit.ExternalTensor

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

abbrev envelopingObject (M : ModuleCat.{u} (ProductEnveloping k A B)) :
    ModuleCat.{u} (EnvelopingProduct k A B) := (envelopingFunctor k A B).obj M

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalBalancedCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
variable (M : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) (N : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ))

abbrev exteriorBimodule (M : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ))
    (N : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) := EnvelopingBimodule k (A ⊗[k] B)
  (ExternalTensor.envelopingObject k A B (ExternalTensor.moduleObject k Ae Be M N))

end ArExplicit.ExternalBalanced

end

end OAI
end


