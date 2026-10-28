-- Prove2me | Definitions.Def_OAIQ031A003
-- name    : OAIQ031A003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:56:09.177247+00:00
-- url     : https://prove2.me/theorems/4a648c48-a78b-4aaa-bf1a-18a00cc567fb
-- title:
--   Definitions bundle OAIQ031A003 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 17 definitions, 5 inductive types or structures, 7 instances and 20 theorems. The definitions and types are `OAI.ArExplicit.Coinduced`, `OAI.ArExplicit.Coinduced.action`, `OAI.ArExplicit.Coinduced.adjoint`, `OAI.ArExplicit.Coinduced.coordinates`, `OAI.ArExplicit.Coinduced.finiteEmbedding`, `OAI.ArExplicit.Coinduced.fromFunctional`, `OAI.ArExplicit.Coinduced.scalarLinearEquiv`, `OAI.ArExplicit.CompleteComparison.CochainCokernel`, `OAI.ArExplicit.CompleteComparison.Cokernel`, `OAI.ArExplicit.CompleteComparison.DownPair`, `OAI.ArExplicit.CompleteComparison.chainOfCochain`, `OAI.ArExplicit.CompleteComparison.cochainCokernelMap`, `OAI.ArExplicit.CompleteComparison.cochainOfChain`, `OAI.ArExplicit.CompleteComparison.cokernelMap`, `OAI.ArExplicit.CompleteComparison.negIndexEmbedding`, `OAI.ArExplicit.ExactProjectiveComplex`, `OAI.ArExplicit.FrobeniusTrace`, `OAI.ArExplicit.FrobeniusTrace.dualEquiv`, `OAI.ArExplicit.FrobeniusTrace.finiteFreeEmbedding`, `OAI.ArExplicit.FrobeniusTrace.leftEquiv`, `OAI.ArExplicit.HomExactAt`, `OAI.ArExplicit.TotallyAcyclicComplex`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_FrobeniusTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/FrobeniusTrace.lean), [`AuslanderReiten_Complete_CompleteComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteComparison.lean), [`AuslanderReiten_Complete_CompleteResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteResolution.lean), [`AuslanderReiten_Cones_CochainCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/CochainCokernel.lean), [`AuslanderReiten_HomComplex_FullHomComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomComparison.lean), [`AuslanderReiten_Homology_CochainNullhomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/CochainNullhomotopy.lean), [`AuslanderReiten_Modules_Coinduced`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/Coinduced.lean), [`AuslanderReiten_Modules_CoinducedEmbedding`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/CoinducedEmbedding.lean), [`AuslanderReiten_Resolutions_FiniteCochainResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteCochainResolution.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A027`, `OAIQ031A028`, `OAIQ031A030`, `OAIQ031A031`, `OAIQ031A032`, `OAIQ031A034`, `OAIQ031A035`, `OAIQ031A037`, `OAIQ031A038` and `OAIQ031A043`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_Coinduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

@[ext] structure Coinduced (k R : Type*) [CommRing k] [Ring R] [Algebra k R] where
  functional : Module.Dual k R

namespace Coinduced

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

def coordinates : Coinduced k R ≃ Module.Dual k R where
  toFun := functional
  invFun := Coinduced.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroup : AddCommGroup (Coinduced k R) := coordinates.addCommGroup
instance instModule : Module k (Coinduced k R) := coordinates.addEquiv.module k

@[simp] theorem functional_zero (s : R) : (0 : Coinduced k R).functional s = 0 := rfl
@[simp] theorem functional_add (x y : Coinduced k R) (s : R) :
    (x + y).functional s = x.functional s + y.functional s := rfl
@[simp] theorem functional_smul (c : k) (x : Coinduced k R) (s : R) :
    (c • x).functional s = c * x.functional s := rfl

def action (r : R) (x : Coinduced k R) : Coinduced k R :=
  ⟨{ toFun := fun s => x.functional (s * r)
     map_add' := fun s t => by simp [add_mul]
     map_smul' := fun c s => by simp }⟩

instance instSMul : SMul R (Coinduced k R) := ⟨action⟩

@[simp] theorem functional_action (r : R) (x : Coinduced k R) (s : R) :
    (r • x).functional s = x.functional (s * r) := rfl

instance instModule_1 : Module R (Coinduced k R) where
  one_smul x := by ext s; simp
  mul_smul r s x := by ext t; simp [mul_assoc]
  smul_zero r := by ext s; simp
  smul_add r x y := by ext s; simp
  zero_smul x := by ext s; simp
  add_smul r s x := by ext t; simp [mul_add]

instance instIsScalarTower : IsScalarTower k R (Coinduced k R) where
  smul_assoc c r x := by ext s; simp

def scalarLinearEquiv : Coinduced k R ≃ₗ[k] Module.Dual k R :=
  coordinates.addEquiv.linearEquiv k

def fromFunctional (φ : Module.Dual k R) : R →ₗ[R] Coinduced k R where
  toFun r := action r ⟨φ⟩
  map_add' r s := by ext t; simp [action, mul_add]
  map_smul' r s := by
    ext t
    change φ (t * (r * s)) = φ ((t * r) * s)
    exact congrArg φ (mul_assoc t r s).symm

section Field

variable {k : Type*} [Field k] {R : Type*} [Ring R] [Algebra k R]

instance instFinite [Module.Finite k R] : Module.Finite k (Coinduced k R) :=
  Module.Finite.equiv scalarLinearEquiv.symm

theorem finrank_eq [Module.Finite k R] :
    Module.finrank k (Coinduced k R) = Module.finrank k R := by
  rw [scalarLinearEquiv.finrank_eq, Subspace.dual_finrank_eq]

end Field
end Coinduced
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_FrobeniusTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

structure FrobeniusTrace (k R : Type*) [Field k] [Ring R] [Algebra k R] where
  trace : R →ₗ[k] k
  separates : ∀ a : R, (∀ b : R, trace (b * a) = 0) → a = 0

namespace FrobeniusTrace

variable {k R : Type*} [Field k] [Ring R] [Algebra k R] (τ : FrobeniusTrace k R)

theorem leftMap_injective : Function.Injective (Coinduced.fromFunctional τ.trace) := by
  intro x y h
  apply sub_eq_zero.mp
  apply τ.separates
  intro b
  rw [mul_sub, map_sub, sub_eq_zero]
  exact congrArg (fun a : Coinduced k R => a.functional b) h

variable [Module.Finite k R]

noncomputable def leftEquiv : R ≃ₗ[R] Coinduced k R := by
  have hi := τ.leftMap_injective
  have hs : Function.Surjective ((Coinduced.fromFunctional τ.trace).restrictScalars k) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Coinduced.finrank_eq (k := k) (R := R)).symm).mp hi
  exact LinearEquiv.ofBijective (Coinduced.fromFunctional τ.trace) ⟨hi, hs⟩

@[simp] theorem leftEquiv_apply (a b : R) :
    (τ.leftEquiv a).functional b = τ.trace (b * a) := rfl

noncomputable def dualEquiv : R ≃ₗ[k] Module.Dual k R :=
  (τ.leftEquiv.restrictScalars k).trans Coinduced.scalarLinearEquiv

@[simp] theorem dualEquiv_apply (a b : R) : τ.dualEquiv a b = τ.trace (b * a) := rfl

end FrobeniusTrace

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

universe u v w x y z

variable {R : Type u} [Ring R]
variable {K : Type v} [AddCommGroup K] [Module R K]
variable {L : Type w} [AddCommGroup L] [Module R L]
variable {M : Type x} [AddCommGroup M] [Module R M]
variable {Q : Type y} [AddCommGroup Q] [Module R Q]

def HomExactAt (e : K →ₗ[R] L) (d : L →ₗ[R] M) : Prop :=
  ∀ f : L →ₗ[R] R, f.comp e = 0 → ∃ g : M →ₗ[R] R, g.comp d = f

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

structure ExactProjectiveComplex (P : ChainComplex (ModuleCat.{u} R) ℤ) : Prop where
  finite : ∀ n, Module.Finite R (P.X n)
  projective : ∀ n, Module.Projective R (P.X n)
  exactAt : ∀ n, LinearMap.range (P.d (n + 1) n).hom =
    LinearMap.ker (P.d n (n - 1)).hom

structure TotallyAcyclicComplex (P : ChainComplex (ModuleCat.{u} R) ℤ) : Prop
    extends ExactProjectiveComplex P where
  dualExact : ∀ n, HomExactAt (P.d (n + 1) n).hom (P.d n (n - 1)).hom

namespace CompleteComparison

variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

theorem differential_comp (P : ChainComplex (ModuleCat.{u} R) ℤ) (i j k : ℤ) :
    (P.d j k).hom.comp (P.d i j).hom = 0 :=
  congrArg (fun f : P.X i ⟶ P.X k => f.hom) (P.d_comp_d i j k)

abbrev Cokernel (P : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :=
  P.X n ⧸ LinearMap.range (P.d (n + 1) n).hom

structure DownPair (P Q : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) where
  hi : P.X (-(n : ℤ)) →ₗ[R] Q.X (-(n : ℤ))
  lo : P.X (Int.negSucc n) →ₗ[R] Q.X (Int.negSucc n)
  comm : (Q.d (-(n : ℤ)) (Int.negSucc n)).hom.comp hi =
    lo.comp (P.d (-(n : ℤ)) (Int.negSucc n)).hom

def cokernelMap (F : P ⟶ Q) (n : ℤ) : Cokernel P n →ₗ[R] Cokernel Q n :=
  (LinearMap.range (P.d (n + 1) n).hom).mapQ
    (LinearMap.range (Q.d (n + 1) n).hom) (F.f n).hom (by
      rintro _ ⟨x, rfl⟩
      refine ⟨(F.f (n + 1)).hom x, ?_⟩
      exact DFunLike.congr_fun
        (congrArg (fun f : P.X (n + 1) ⟶ Q.X n => f.hom) (F.comm (n + 1) n)) x)

@[simp]
theorem cokernelMap_mkQ (F : P ⟶ Q) (n : ℤ) :
    (cokernelMap F n).comp (LinearMap.range (P.d (n + 1) n).hom).mkQ =
      (LinearMap.range (Q.d (n + 1) n).hom).mkQ.comp (F.f n).hom :=
  Submodule.mapQ_mkQ _ _ _

@[simp]
theorem cokernelMap_id (n : ℤ) : cokernelMap (𝟙 P) n = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n + 1) n).hom) x
  rfl

@[simp]
theorem cokernelMap_comp {S : ChainComplex (ModuleCat.{u} R) ℤ}
    (F : P ⟶ Q) (G : Q ⟶ S) (n : ℤ) :
    cokernelMap (F ≫ G) n = (cokernelMap G n).comp (cokernelMap F n) := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n + 1) n).hom) x
  rfl

@[simp]
theorem cokernelMap_add (F G : P ⟶ Q) (n : ℤ) :
    cokernelMap (F + G) n = cokernelMap F n + cokernelMap G n := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n + 1) n).hom) x
  exact map_add (LinearMap.range (Q.d (n + 1) n).hom).mkQ _ _

@[simp]
theorem cokernelMap_zero (n : ℤ) : cokernelMap (0 : P ⟶ Q) n = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n + 1) n).hom) x
  exact map_zero (LinearMap.range (Q.d (n + 1) n).hom).mkQ

end CompleteComparison

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]

def negIndexEmbedding : (ComplexShape.up ℤ).Embedding (ComplexShape.down ℤ) :=
  ComplexShape.Embedding.mk' _ _ (fun i : ℤ => -i) neg_injective (by
    intro i j
    change i + 1 = j ↔ -j + 1 = -i
    omega)

instance instIsRelIffIntNegIndexEmbedding : negIndexEmbedding.IsRelIff := by
  dsimp [negIndexEmbedding]
  infer_instance

noncomputable abbrev chainOfCochain (K : CochainComplex (ModuleCat.{u} R) ℤ) :=
  K.extend negIndexEmbedding

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_CochainCokernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory HomologicalComplex

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

abbrev CochainCokernel := K.X 0 ⧸ LinearMap.range (K.d (-1) 0).hom

variable {K}
variable {L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)

def cochainCokernelMap : CochainCokernel K →ₗ[R] CochainCokernel L :=
  (LinearMap.range (K.d (-1) 0).hom).liftQ
    ((LinearMap.range (L.d (-1) 0).hom).mkQ.comp (f.f 0).hom) (by
      rintro _ ⟨x, rfl⟩
      change (LinearMap.range (L.d (-1) 0).hom).mkQ ((f.f 0).hom ((K.d (-1) 0).hom x)) = 0
      have h := congrArg (fun g : K.X (-1) ⟶ L.X 0 => g.hom x) (f.comm (-1) 0)
      change (L.d (-1) 0).hom ((f.f (-1)).hom x) = (f.f 0).hom ((K.d (-1) 0).hom x) at h
      rw [← h]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩)

@[simp]
theorem cochainCokernelMap_mk (x : K.X 0) :
    cochainCokernelMap f (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((f.f 0).hom x) := rfl

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_CochainNullhomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex

namespace ArExplicit.CompleteComparison

universe u
variable {R : Type u} [Ring R]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

@[simp]
theorem cochainCokernelMap_comp (f : K ⟶ L) (g : L ⟶ M) :
    cochainCokernelMap (f ≫ g) = (cochainCokernelMap g).comp (cochainCokernelMap f) := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range (K.d (-1) 0).hom).mkQ_surjective x
  rfl

@[simp]
theorem cochainCokernelMap_sub (f g : K ⟶ L) :
    cochainCokernelMap (f - g) = cochainCokernelMap f - cochainCokernelMap g := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range (K.d (-1) 0).hom).mkQ_surjective x
  change Submodule.Quotient.mk ((f.f 0).hom x - (g.f 0).hom x) = _
  exact Submodule.Quotient.mk_sub _

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_CoinducedEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.Coinduced

variable {k R M : Type*} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

def adjoint (φ : Module.Dual k M) : M →ₗ[R] Coinduced k R where
  toFun m := ⟨{
    toFun := fun r => φ (r • m)
    map_add' := fun r s => by simp [add_smul]
    map_smul' := fun c r => by simp [smul_assoc] }⟩
  map_add' m n := by ext r; simp [smul_add]
  map_smul' r m := by
    ext s
    change φ (s • r • m) = φ ((s * r) • m)
    rw [mul_smul]

@[simp] theorem adjoint_eval_one (φ : Module.Dual k M) (m : M) :
    (adjoint (R := R) φ m).functional (1 : R) = φ m := by simp [adjoint]

variable [Module.Finite k M]

noncomputable def finiteEmbedding : M →ₗ[R] (Fin (Module.finrank k M) → Coinduced k R) :=
  LinearMap.pi fun i => adjoint ((Module.finBasis k M).coord i)

theorem finiteEmbedding_injective :
    Function.Injective (finiteEmbedding (k := k) (R := R) (M := M)) := by
  intro x y h
  apply (Module.finBasis k M).ext_elem
  intro i
  have hi := congrArg (fun f : Fin (Module.finrank k M) → Coinduced k R =>
    (f i).functional 1) h
  simpa [finiteEmbedding, Module.Basis.coord_apply] using hi

end ArExplicit.Coinduced

namespace ArExplicit.FrobeniusTrace

variable {k R M : Type*} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable [Module.Finite k M]

noncomputable def finiteFreeEmbedding : M →ₗ[R] (Fin (Module.finrank k M) → R) :=
  LinearMap.pi fun i => τ.leftEquiv.symm.toLinearMap.comp
    (Coinduced.adjoint ((Module.finBasis k M).coord i))

theorem finiteFreeEmbedding_injective :
    Function.Injective (τ.finiteFreeEmbedding (M := M)) := by
  intro x y h
  apply Coinduced.finiteEmbedding_injective (k := k) (R := R)
  funext i
  have hi := congrFun h i
  exact τ.leftEquiv.symm.injective hi

end ArExplicit.FrobeniusTrace

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteCochainResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace CompleteComparison

def cochainOfChain (P : ChainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ := P.restriction negIndexEmbedding

end CompleteComparison

end ArExplicit

end OAI
end


