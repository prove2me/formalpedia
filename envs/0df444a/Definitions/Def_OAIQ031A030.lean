-- Prove2me | Definitions.Def_OAIQ031A030
-- name    : OAIQ031A030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:58:40.215714+00:00
-- url     : https://prove2.me/theorems/974cf4a9-932c-472b-9d14-e3815c06c594
-- title:
--   Definitions bundle OAIQ031A030 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 43 declarations of OpenAI's Lean: 17 definitions and 26 theorems. The definitions and types are `OAI.ArExplicit.A.diagonalAlg`, `OAI.ArExplicit.A.quotientTensorMap`, `OAI.ArExplicit.AbsoluteBar.contraction`, `OAI.ArExplicit.CocycleData.boundaryLeftContribution`, `OAI.ArExplicit.CocycleData.boundaryTerms`, `OAI.ArExplicit.CocycleData.evalPair`, `OAI.ArExplicit.CocycleData.z`, `OAI.ArExplicit.ExternalTensor.envelopingFunctor`, `OAI.ArExplicit.FrobeniusTrace.tensor`, `OAI.ArExplicit.FrobeniusTrace.tensorDualEquiv`, `OAI.ArExplicit.FrobeniusTrace.tensorTrace`, `OAI.ArExplicit.ModuleBar.boundary`, `OAI.ArExplicit.ModuleBar.left`, `OAI.ArExplicit.ModuleBar.leftModule`, `OAI.ArExplicit.ProjectiveNullhomotopyAbove.sequence`, `OAI.ArExplicit.Resolution.projection`, `OAI.ArExplicit.trivialExtensionFrobeniusTrace`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Algebras_BaseRadical`, `AuslanderReiten_Algebras_FrobeniusTrace`, `AuslanderReiten_Algebras_SymmetricSocle`, `AuslanderReiten_Algebras_TensorFrobenius`, `AuslanderReiten_Algebras_TensorStructure`, `AuslanderReiten_Algebras_TrivialExtensionRadical`, `AuslanderReiten_Bar_BarComplex`, `AuslanderReiten_Bar_ModuleBar`, `AuslanderReiten_Cocycles_CocycleTwist`, `AuslanderReiten_Cocycles_SparseCocycle`, `AuslanderReiten_Cocycles_TwistedBoundaryData`, `AuslanderReiten_Cocycles_TwistedBoundaryFormula`, `AuslanderReiten_Homology_ProjectiveNullhomotopyAbove`, `AuslanderReiten_Resolutions_Resolution`, `AuslanderReiten_Tensor_ExternalEnveloping`.
--
--   **Imports.** It imports the bundles `OAIQ031A001`, `OAIQ031A002`, `OAIQ031A003`, `OAIQ031A004`, `OAIQ031A005` and `OAIQ031A006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A044`, `OAIQ031A047`, `OAIQ031A048`, `OAIQ031A050`, `OAIQ031A052` and `OAIQ031A069`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A001
import Definitions.Def_OAIQ031A002
import Definitions.Def_OAIQ031A003
import Definitions.Def_OAIQ031A004
import Definitions.Def_OAIQ031A005
import Definitions.Def_OAIQ031A006

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_BaseRadical
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BaseAlgebra

open ArExplicit.Letter

variable {k : Type*} [Field k] (q : k)

theorem diagonalAlg_surjective : Function.Surjective (diagonalAlg q) := by
  rintro ⟨a, b⟩
  refine ⟨a • basisVector q e + b • basisVector q f, ?_⟩
  apply Prod.ext
  · change (a • basisVector q e + b • basisVector q f).coeff e = a
    simp
  · change (a • basisVector q e + b • basisVector q f).coeff f = b
    simp

end ArExplicit.BaseAlgebra

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_FrobeniusTrace
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

def trivialExtensionFrobeniusTrace (k R : Type*) [Field k] [Ring R] [Algebra k R] :
    FrobeniusTrace k (TrivialExtension k R) where
  trace := TrivialExtension.trace
  separates a h := (TrivialExtension.traceForm_nondegenerate (k := k) (A := R)).2 a h

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_SymmetricSocle
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.FrobeniusTrace

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (τ : FrobeniusTrace k R)
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
variable (J : Ideal R) [J.IsTwoSided]

include τ hs

theorem annihilator_right {u : R} (hu : ∀ j ∈ J, j * u = 0) {j : R} (hj : j ∈ J) :
    u * j = 0 := by
  apply τ.separates
  intro a
  rw [← mul_assoc, hs, ← mul_assoc, hu (j * a) (J.mul_mem_right a hj), map_zero]

end ArExplicit.FrobeniusTrace

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TrivialExtensionRadical
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.TrivialExtension

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

theorem projection_surjective : Function.Surjective (projection : TrivialExtension k A →ₐ[k] A) :=
  fun a => ⟨inl a, rfl⟩

end ArExplicit.TrivialExtension

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)

theorem diagonalAlg_surjective : Function.Surjective (diagonalAlg q) :=
  (BaseAlgebra.diagonalAlg_surjective q).comp TrivialExtension.projection_surjective

end ArExplicit.T

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorStructure
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

namespace A

variable {k : Type*} [Field k] (q : k)

def quotientTensorMap : A k q →ₐ[k] (k × k) ⊗[k] (k × k) :=
  Algebra.TensorProduct.map (T.diagonalAlg q) (T.diagonalAlg q)

noncomputable def diagonalAlg : A k q →ₐ[k] (k × k) × (k × k) :=
  (quotientCoordinates (k := k)).toAlgHom.comp (quotientTensorMap q)

end A
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorFrobenius
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.FrobeniusTrace

open TensorProduct

variable {k R S : Type*} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable [Module.Finite k R] [Module.Finite k S]
variable (τ : FrobeniusTrace k R) (σ : FrobeniusTrace k S)

noncomputable def tensorTrace : R ⊗[k] S →ₗ[k] k :=
  TensorProduct.dualDistrib k R S (τ.trace ⊗ₜ[k] σ.trace)

omit [Module.Finite k R] [Module.Finite k S] in
@[simp] theorem tensorTrace_tmul (r : R) (s : S) :
    tensorTrace τ σ (r ⊗ₜ[k] s) = τ.trace r * σ.trace s := rfl

noncomputable def tensorDualEquiv : R ⊗[k] S ≃ₗ[k] Module.Dual k (R ⊗[k] S) :=
  (TensorProduct.congr τ.dualEquiv σ.dualEquiv).trans
    (TensorProduct.dualDistribEquiv k R S)

theorem tensorDualEquiv_apply (a b : R ⊗[k] S) :
    tensorDualEquiv τ σ a b = tensorTrace τ σ (b * a) := by
  induction a with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, mul_add, ha, ha']
  | tmul r s =>
      induction b with
      | zero => simp
      | add b b' hb hb' => simp only [map_add, add_mul, hb, hb']
      | tmul r' s' =>
          simp [tensorDualEquiv, tensorTrace, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]

noncomputable def tensor : FrobeniusTrace k (R ⊗[k] S) where
  trace := tensorTrace τ σ
  separates a ha := by
    apply (tensorDualEquiv τ σ).injective
    rw [map_zero]
    apply LinearMap.ext
    intro b
    exact (tensorDualEquiv_apply τ σ a b).trans (ha b)

omit [Module.Finite k R] [Module.Finite k S] in
theorem tensorTrace_mul_comm
    (hτ : ∀ a b, τ.trace (a * b) = τ.trace (b * a))
    (hσ : ∀ a b, σ.trace (a * b) = σ.trace (b * a)) (a b : R ⊗[k] S) :
    tensorTrace τ σ (a * b) = tensorTrace τ σ (b * a) := by
  induction a with
  | zero => simp
  | add a a' ha ha' => simp only [add_mul, mul_add, map_add, ha, ha']
  | tmul r s =>
      induction b with
      | zero => simp
      | add b b' hb hb' => simp only [add_mul, mul_add, map_add, hb, hb']
      | tmul r' s' => simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorTrace_tmul, hτ, hσ]

end ArExplicit.FrobeniusTrace

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarComplex
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

variable [CharP k 2]

def contraction (n : ℕ) : object k R n →ₗ[k] object k R (n + 1) :=
  TensorProduct.mk k R (object k R n) 1

theorem contraction_identity (n : ℕ) (x : object k R (n + 1)) :
    boundary k R (n + 1) (contraction k R (n + 1) x) +
      contraction k R n (boundary k R n x) = x := by
  change boundary k R (n + 1) ((1 : R) ⊗ₜ[k] x) +
    (1 : R) ⊗ₜ[k] boundary k R n x = x
  rw [boundary_succ_tmul, left_one, add_assoc, double_zero_p1 k, add_zero]

omit [CharP k 2] in

theorem augmentation_contraction (x : R) : boundary k R 0 (contraction k R 0 x) = x := by
  exact one_mul x

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

def left : (n : ℕ) → R →ₐ[k] Module.End k (object k R M n)
  | 0 => Algebra.lsmul k k M
  | n + 1 => (Module.End.rTensorAlgHom k R (object k R M n)).comp (Algebra.lsmul k k R)

@[simp] theorem left_zero (a : R) (x : M) : left k R M 0 a x = a • x := rfl
@[simp] theorem left_tmul (n : ℕ) (a b : R) (x : object k R M n) :
    left k R M (n + 1) a (b ⊗ₜ[k] x) = (a * b) ⊗ₜ[k] x := rfl

@[simp] theorem left_one (n : ℕ) (x : object k R M n) : left k R M n 1 x = x := by
  rw [map_one]
  rfl

theorem left_mul (n : ℕ) (a b : R) (x : object k R M n) :
    left k R M n (a * b) x = left k R M n a (left k R M n b x) := by
  rw [map_mul]
  rfl

def boundary : (n : ℕ) → object k R M (n + 1) →ₗ[k] object k R M n
  | 0 => TensorProduct.lift (Algebra.lsmul k k M).toLinearMap
  | n + 1 => TensorProduct.lift (left k R M (n + 1)).toLinearMap + (boundary n).lTensor R

@[simp] theorem boundary_zero_tmul (a : R) (x : M) :
    boundary k R M 0 (a ⊗ₜ[k] x) = a • x := rfl
@[simp] theorem boundary_succ_tmul (n : ℕ) (a : R) (x : object k R M (n + 1)) :
    boundary k R M (n + 1) (a ⊗ₜ[k] x) =
      left k R M (n + 1) a x + a ⊗ₜ[k] boundary k R M n x := rfl

@[instance_reducible] def leftModule (n : ℕ) : Module R (object k R M n) :=
  Module.compHom (object k R M n) (left k R M n).toRingHom

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_SparseCocycle
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)

theorem TripleMonomial.linear_apply (p : TripleMonomial) (a b c : T k q) :
    p.linear q a b c = evalTriple q a b c p := by
  simp [TripleMonomial.linear, evalTriple, smul_smul]
  congr 1
  ring

theorem p_apply (a b c : T k q) : p q a b c = (cochain.map (evalTriple q a b c)).sum := by
  simp only [p, linearMap_list_sum_apply, List.map_map, Function.comp_def, TripleMonomial.linear_apply]

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleTwist
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)

def z (H : k) : T k q →ₗ[k] T k q :=
  ∑ i : TIndex, (T.coefficient q i).smulRight
    (if selected i then (H * q) • T.vector q i else 0)

theorem z_vector (H : k) (i : TIndex) :
    z q H (T.vector q i) = if selected i then (H * q) • T.vector q i else 0 := by
  simp only [z, LinearMap.sum_apply, LinearMap.smulRight_apply, T.coefficient_vector]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem coefficient_twist (H : kˣ) (a : T k q) (i : TIndex) :
    T.coefficient q i (TrivialExtension.twist H a) =
      (H : k) ^ i.weight * T.coefficient q i a := by
  obtain ⟨b, i⟩ := i
  cases b <;> simp [T.coefficient, TIndex.weight]

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_TwistedBoundaryData
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.CocycleData

def boundaryLeftContribution (p : TripleMonomial) (m : MulMonomial) : List PairMonomial :=
  if m.first = p.output ∧ m.second = p.third.star then
    [⟨p.first, p.second, m.output, p.degree + m.degree, p.third.weight⟩] else []

def boundaryTerms : List PairMonomial :=
  (cochain.flatMap fun p => multiplication.flatMap (boundaryLeftContribution p)) ++
    multiplication.flatMap boundaryRightContributions

theorem boundary_certificate :
    SparseParity.paired (SparseParity.sort (fun x y => decide (x.number ≤ y.number)) boundaryTerms) = true := by
  decide +kernel

theorem boundaryTerms_sum_zero {M : Type*} [AddCommMonoid M]
    (hchar : ∀ x : M, x + x = 0) (f : PairMonomial → M) :
    (boundaryTerms.map f).sum = 0 :=
  SparseParity.sum_eq_zero_of_sorted_paired hchar f _ _ boundary_certificate

end ArExplicit.CocycleData

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_TwistedBoundaryFormula
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {α β : Type*} {k : Type*} [Field k] (q : k)

def evalPair (H : k) (a b : T k q) (m : PairMonomial) : T k q :=
  (q ^ m.qDegree * H ^ m.hDegree * T.coefficient q m.first a *
    T.coefficient q m.second b) • T.vector q m.output

theorem list_right_mul_p1 (a : T k q) (l : List α) (f : α → T k q) :
    (l.map f).sum * a = (l.map fun x => f x * a).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [add_mul, ih]

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ProjectiveNullhomotopyAbove
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.ProjectiveNullhomotopyAbove

universe u
variable {R : Type u} [Ring R]
variable {P Q : ℕ → Type u}
variable [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]
variable [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)]
variable (dP : (n : ℕ) → P (n + 1) →ₗ[R] P n)
variable (dQ : (n : ℕ) → Q (n + 1) →ₗ[R] Q n)
variable (f : (n : ℕ) → Q (n + 2) →ₗ[R] P n)

variable (hproj : ∀ n, Module.Projective R (Q n))
variable (hQQ : ∀ n, (dQ n).comp (dQ (n + 1)) = 0)
variable (hexact : ∀ n, LinearMap.range (dP (n + 1)) = LinearMap.ker (dP n))
variable (hcomm : ∀ n, (dP n).comp (f (n + 1)) = (f n).comp (dQ (n + 2)))

include hproj hQQ hexact hcomm

theorem step (n : ℕ) (c : Pair dP dQ f n) :
    ∃ c' : Pair dP dQ f (n + 1), c'.lo = c.hi := by
  let := hproj (n + 3)
  obtain ⟨h, hh⟩ := extend_homotopy_up (dQ (n + 2)) (dQ (n + 1)) (hQQ (n + 1))
    (dP (n + 1)) (dP n) (hexact n) (f (n + 1)) (f n) (hcomm n) c.hi c.lo c.eqn
  exact ⟨⟨c.hi, h, hh⟩, rfl⟩

def sequence (c : Pair dP dQ f 0) : (n : ℕ) → Pair dP dQ f n
  | 0 => c
  | n + 1 => Classical.choose (step dP dQ f hproj hQQ hexact hcomm n
      (sequence c n))

theorem sequence_succ_lo (c : Pair dP dQ f 0) (n : ℕ) :
    (sequence dP dQ f hproj hQQ hexact hcomm c (n + 1)).lo =
      (sequence dP dQ f hproj hQQ hexact hcomm c n).hi :=
  Classical.choose_spec (step dP dQ f hproj hQQ hexact hcomm n
    (sequence dP dQ f hproj hQQ hexact hcomm c n))

variable {M : Type u} [AddCommGroup M] [Module R M]

theorem exists_homotopy (e : P 0 →ₗ[R] M) (hepi : Function.Surjective e)
    (he : LinearMap.range (dP 0) = LinearMap.ker e) (z : Q 1 →ₗ[R] M)
    (hz : e.comp (f 0) = z.comp (dQ 1)) :
    ∃ G : (n : ℕ) → Q (n + 1) →ₗ[R] P n,
      e.comp (G 0) = z ∧ ∀ n, f n = (dP n).comp (G (n + 1)) + (G n).comp (dQ (n + 1)) := by
  let := hproj 1
  obtain ⟨g₀, hg₀⟩ := Module.projective_lifting_property e z hepi
  have hc : e.comp (f 0 - g₀.comp (dQ 1)) = 0 := by
    ext x
    have h1 := LinearMap.congr_fun hz x
    have h2 := LinearMap.congr_fun hg₀ (dQ 1 x)
    simp only [LinearMap.comp_apply] at h1 h2
    change e (f 0 x - g₀ (dQ 1 x)) = 0
    rw [map_sub, h2]
    exact sub_eq_zero.mpr h1
  let := hproj 2
  obtain ⟨g₁, hg₁⟩ := lift_through_exact (dP 0) e he (f 0 - g₀.comp (dQ 1)) hc
  let c : Pair dP dQ f 0 := ⟨g₀, g₁, by rw [hg₁, sub_add_cancel]⟩
  refine ⟨fun n => (sequence dP dQ f hproj hQQ hexact hcomm c n).lo, hg₀, ?_⟩
  intro n
  simpa only [sequence_succ_lo] using (sequence dP dQ f hproj hQQ hexact hcomm c n).eqn

end ArExplicit.ProjectiveNullhomotopyAbove

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_Resolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

def projection (p : C) (hp : p * p = p) : C →ₗ[C] fixedRight q p where
  toFun a := ⟨a * p, by change (a * p) * p = a * p; rw [mul_assoc, hp]⟩
  map_add' a b := Subtype.ext (add_mul a b p)
  map_smul' c a := Subtype.ext (mul_assoc c a p)

theorem projection_surjective (p : C) (hp : p * p = p) :
    Function.Surjective (projection q p hp) := by
  intro a
  exact ⟨a, Subtype.ext a.property⟩

end ArExplicit.Resolution

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalEnveloping
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

abbrev envelopingFunctor : ModuleCat.{u} (ProductEnveloping k A B) ⥤
    ModuleCat.{u} (EnvelopingProduct k A B) :=
  ModuleCat.restrictScalars (envelopingEquiv k A B).symm.toRingHom

end ArExplicit.ExternalTensor

end

end OAI
end


