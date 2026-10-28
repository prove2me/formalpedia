-- Prove2me | Definitions.Def_OAIQ031A045
-- name    : OAIQ031A045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:03:46.308958+00:00
-- url     : https://prove2.me/theorems/b7c0fad0-118c-42a4-87b1-c5f5fc20759d
-- title:
--   Definitions bundle OAIQ031A045 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 10 definitions, 1 inductive type or structure and 20 theorems. The definitions and types are `OAI.ArExplicit.AbsoluteBar.augmentation`, `OAI.ArExplicit.AbsoluteBar.bimodule`, `OAI.ArExplicit.AbsoluteBar.cochain3Linear`, `OAI.ArExplicit.AbsoluteBar.complex`, `OAI.ArExplicit.AbsoluteBar.differential`, `OAI.ArExplicit.AbsoluteBar.moduleObject`, `OAI.ArExplicit.AbsoluteBar.representation`, `OAI.ArExplicit.AbsoluteBar.rotateLinear`, `OAI.ArExplicit.AbsoluteBar.suffix3`, `OAI.ArExplicit.AbsoluteBar.suffixComparison`, `OAI.ArExplicit.TotallyAcyclicCochain`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBimodule.lean), [`AuslanderReiten_Bar_BarCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarCochain.lean), [`AuslanderReiten_Bar_BarComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarComplex.lean), [`AuslanderReiten_Bar_BarProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarProjective.lean), [`AuslanderReiten_Bar_BarResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarResolution.lean), [`AuslanderReiten_Bar_BarSuffix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarSuffix.lean), [`AuslanderReiten_Complete_CompleteShiftDual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteShiftDual.lean), [`AuslanderReiten_Complete_FiniteCompleteResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/FiniteCompleteResolution.lean), [`AuslanderReiten_Cones_MappingConeTotal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/MappingConeTotal.lean), [`AuslanderReiten_Tensor_BalancedTensorFirst`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorFirst.lean), [`AuslanderReiten_Tensor_EnvelopingBalancedExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBalancedExact.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A026`, `OAIQ031A027`, `OAIQ031A028` and `OAIQ031A029` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A061`, `OAIQ031A062`, `OAIQ031A063`, `OAIQ031A066`, `OAIQ031A068`, `OAIQ031A069`, `OAIQ031A070` and `OAIQ031A074`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A026
import Definitions.Def_OAIQ031A027
import Definitions.Def_OAIQ031A028
import Definitions.Def_OAIQ031A029

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarComplex
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem boundary_right (n : ℕ) (a : Rᵐᵒᵖ) (x : object k R (n + 1)) :
    boundary k R n (right k R (n + 1) a x) = right k R n a (boundary k R n x) := by
  induction n with
  | zero =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b c => exact (mul_assoc _ _ _).symm
  | succ n ih =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x =>
      rw [right_tmul, boundary_succ_tmul, boundary_succ_tmul, map_add, right_tmul, ih, left_right]

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarBimodule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

def representation (n : ℕ) : Enveloping k R →ₐ[k] Module.End k (object k R n) :=
  Algebra.TensorProduct.lift (left k R n) (right k R n) fun a b => by
    apply LinearMap.ext
    intro x
    exact left_right k R n a b x

@[instance_reducible]
def bimodule (n : ℕ) : Module (Enveloping k R) (object k R n) :=
  Module.compHom (object k R n) (representation k R n).toRingHom

def moduleObject (n : ℕ) : ModuleCat.{u} (Enveloping k R) :=
  letI := bimodule k R n
  ModuleCat.of (Enveloping k R) (object k R n)

def differential (n : ℕ) : moduleObject k R (n + 1) →ₗ[Enveloping k R] moduleObject k R n where
  toAddHom := (boundary k R n).toAddHom
  map_smul' a x := by
    let y : object k R (n + 1) := x
    change boundary k R n ((representation k R (n + 1) a) y) =
      (representation k R n a) (boundary k R n y)
    induction a using OAI.tensorInductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | tmul a b =>
      change boundary k R n (left k R (n + 1) a (right k R (n + 1) b y)) =
        left k R n a (right k R n b (boundary k R n y))
      rw [boundary_left, boundary_right]

@[simp] theorem differential_apply (n : ℕ) (x : object k R (n + 1)) :
    differential k R n x = boundary k R n x := rfl

variable [CharP k 2]

def complex : ChainComplex (ModuleCat.{u} (Enveloping k R)) ℕ :=
  ChainComplex.of (fun n => moduleObject k R (n + 1))
    (fun n => ModuleCat.ofHom (X := moduleObject k R (n + 1 + 1))
      (Y := moduleObject k R (n + 1)) (differential k R (n + 1)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact boundary_squared k R (n + 1))

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def rotateLinear (n : ℕ) : object k R (n + 2) ≃ₗ[k] (object k R (n + 1) ⊗[k] R) :=
  (TensorProduct.assoc k R R (object k R n)).symm.trans
    (TensorProduct.rightComm k R R (object k R n))

@[simp] theorem rotateLinear_tmul (n : ℕ) (a b : R) (x : object k R n) :
    rotateLinear k R n (a ⊗ₜ[k] (b ⊗ₜ[k] x)) = (a ⊗ₜ[k] x) ⊗ₜ[k] b := rfl

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarResolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]

@[simp] theorem complex_d (n : ℕ) :
    (complex k R).d (n + 1) n =
      ModuleCat.ofHom (X := moduleObject k R (n + 2)) (Y := moduleObject k R (n + 1))
        (differential k R (n + 1)) := by
  simp only [complex, ChainComplex.of.d]
  apply Category.id_comp

def augmentation : complex k R ⟶
    (ChainComplex.single₀ (ModuleCat.{u} (Enveloping k R))).obj (moduleObject k R 0) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (X := moduleObject k R 1) (Y := moduleObject k R 0)
      (differential k R 0), by
      rw [complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact boundary_squared k R 0⟩

@[simp] theorem augmentation_zero :
    (augmentation k R).f 0 = ModuleCat.ofHom (X := moduleObject k R 1)
      (Y := moduleObject k R 0) (differential k R 0) := by
  apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarCochain
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

def suffix3 (p : Cochain3 k R) : object k R 3 →ₗ[k] R :=
  TensorProduct.lift {
    toFun := fun a => TensorProduct.lift {
      toFun := fun b => TensorProduct.lift ((LinearMap.mul k R).comp (p a b))
      map_add' := by
        intro b c
        apply TensorProduct.ext'
        intro d e
        simp
      map_smul' := by
        intro t b
        apply TensorProduct.ext'
        intro d e
        simp }
    map_add' := by
      intro a b
      apply TensorProduct.ext'
      intro c y
      induction y using OAI.tensorInductionOn with
      | add y z hy hz =>
        simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply] at *
        rw [hy, hz]
      | tmul d e => simp
    map_smul' := by
      intro t a
      apply TensorProduct.ext'
      intro b y
      induction y using OAI.tensorInductionOn with
      | add y z hy hz =>
        simp only [TensorProduct.tmul_add, map_add, LinearMap.smul_apply] at *
        rw [hy, hz]
      | tmul c d => simp }

@[simp] theorem suffix3_tmul (p : Cochain3 k R) (a b c d : R) :
    suffix3 k R p (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] d))) = p a b c * d := rfl

def cochain3Linear (p : Cochain3 k R) : object k R 4 →ₗ[k] R :=
  TensorProduct.lift ((LinearMap.mul k R).compl₂ (suffix3 k R p))

@[simp] theorem cochain3Linear_tmul (p : Cochain3 k R) (a b c d e : R) :
    cochain3Linear k R p (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] (d ⊗ₜ[k] e)))) =
      a * p b c d * e := by
  change a * (p b c d * e) = _
  exact (mul_assoc _ _ _).symm

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarSuffix
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

def suffixComparison (p : Cochain3 k R) : (n : ℕ) → object k R (n + 3) →ₗ[k] object k R n
  | 0 => suffix3 k R p
  | n + 1 => (suffixComparison p n).lTensor R

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteShiftDual
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace DualExactCochain

open CompleteComparison

theorem to_chain {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : DualExactCochain K) :
    ∀ i, HomExactAt ((chainOfCochain K).d (i + 1) i).hom
      ((chainOfCochain K).d i (i - 1)).hom := by
  intro i
  let E := reverseShortComplexIso K (-i - 1) (-i) (-i + 1) (i + 1) i (i - 1)
    (by change -(-i - 1) = i + 1; omega) (neg_neg i)
    (by change -(-i + 1) = i - 1; omega)
  exact HomExactAt.of_shortComplex_iso E.symm (hK (-i))

end DualExactCochain

structure TotallyAcyclicCochain (K : CochainComplex (ModuleCat.{u} R) ℤ) : Prop
    extends ExactProjectiveCochain K where
  dualExact : DualExactCochain K

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_FiniteCompleteResolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

attribute [instance] FiniteLeftModule.scalar FiniteLeftModule.tower FiniteLeftModule.finite

namespace FiniteLeftModule

variable {k R} [Module.Finite k R]

theorem completeComplex_exact (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) (n : ℤ) :
    LinearMap.range ((M.completeComplex τ).d (n + 1) n).hom =
      LinearMap.ker ((M.completeComplex τ).d n (n - 1)).hom := by
  have aux (i j : ℤ) (hi : i = j + 1) :
      LinearMap.range ((M.completeComplex τ).d (i + 1) i).hom =
        LinearMap.ker ((M.completeComplex τ).d i j).hom := by
    subst i
    simp only [completeComplex, ChainComplex.of_d]
    exact M.adjacent_exact τ j
  exact aux n (n - 1) (by omega)

theorem completeComplex_exactProjective (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    ExactProjectiveComplex (M.completeComplex τ) where
  finite n := by
    cases n with
    | ofNat n => exact inferInstanceAs (Module.Finite R (M.positiveTerm n))
    | negSucc n => exact inferInstanceAs (Module.Finite R (M.negativeTerm τ n))
  projective n := by
    cases n with
    | ofNat n => exact inferInstanceAs (Module.Projective R (M.positiveTerm n))
    | negSucc n => exact inferInstanceAs (Module.Projective R (M.negativeTerm τ n))
  exactAt := M.completeComplex_exact τ

theorem completeComplex_totallyAcyclic (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    TotallyAcyclicComplex (M.completeComplex τ) := by
  let := τ.regular_injective
  exact (M.completeComplex_exactProjective τ).totallyAcyclic

end FiniteLeftModule

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_MappingConeTotal
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex CompleteComparison
open CochainComplex CochainComplex.HomComplex

universe u

variable {R : Type u} [Ring R]
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

theorem cochain_adjacent_dualExact {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : DualExactCochain K) (i : ℤ) :
    HomExactAt (K.d i (i + 1)).hom (K.d (i + 1) ((i + 1) + 1)).hom := by
  have h := hK (i + 1)
  have hi : (i + 1) - 1 = i := by omega
  rw [hi] at h
  exact h

theorem mappingCone_exactProjective
    (hF : ExactProjectiveCochain F) (hG : ExactProjectiveCochain G) :
    ExactProjectiveCochain (mappingCone φ) where
  finite i := by
    let := hG.finite i
    let := hF.finite (i + 1)
    exact Module.Finite.equiv (coneTermEquiv φ i).symm
  projective i := by
    let := hG.projective i
    let := hF.projective (i + 1)
    exact Module.Projective.of_equiv (coneTermEquiv φ i).symm
  exactAt j := by
    obtain ⟨i, rfl⟩ : ∃ i : ℤ, j = i + 1 := ⟨j - 1, by omega⟩
    rw [(mappingCone φ).exactAt_iff' (i := i) (j := i + 1) (k := (i + 1) + 1) (by simp) (by simp)]
    apply ShortComplex.exact_of_iso (coneShortComplexIso φ i).symm
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (LinearMap.exact_iff.mp (coneBlock_exact _ _ _ _ _ _
      (cochain_adjacent_exact hG i) (cochain_adjacent_exact hF (i + 1))
      (congrArg ModuleCat.Hom.hom (φ.comm _ _)))).symm

theorem mappingCone_dualExact (hF : DualExactCochain F) (hG : DualExactCochain G) :
    DualExactCochain (mappingCone φ) := by
  intro j
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : (i + 1) - 1 = i := by omega
  rw [hi]
  apply HomExactAt.of_shortComplex_iso (coneShortComplexIso φ i).symm
  exact coneBlock_homExact _ _ _ _ _ _ (cochain_adjacent_dualExact hG i)
    (cochain_adjacent_dualExact hF (i + 1)) (congrArg ModuleCat.Hom.hom (φ.comm _ _))

theorem mappingCone_totallyAcyclic
    (hF : TotallyAcyclicCochain F) (hG : TotallyAcyclicCochain G) :
    TotallyAcyclicCochain (mappingCone φ) where
  toExactProjectiveCochain := mappingCone_exactProjective φ hF.toExactProjectiveCochain hG.toExactProjectiveCochain
  dualExact := mappingCone_dualExact φ hF.dualExact hG.dualExact

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorFirst
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor

universe u
variable {k R F G Q X : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [IsScalarTower k Rᵐᵒᵖ F]
variable [AddCommGroup G] [Module k G] [Module Rᵐᵒᵖ G] [IsScalarTower k Rᵐᵒᵖ G]
variable [AddCommGroup Q] [Module k Q] [Module Rᵐᵒᵖ Q] [IsScalarTower k Rᵐᵒᵖ Q]
variable [AddCommGroup X] [Module k X] [Module R X] [IsScalarTower k R X]

omit [IsScalarTower k R X] in
theorem mapFirst_shortExact (f : F →ₗ[Rᵐᵒᵖ] G) (g : G →ₗ[Rᵐᵒᵖ] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (he : LinearMap.range f = LinearMap.ker g) [Module.Projective Rᵐᵒᵖ Q] :
    Function.Injective (mapFirst (k := k) X f) ∧ Function.Surjective (mapFirst (k := k) X g) ∧
      LinearMap.range (mapFirst (k := k) X f) = LinearMap.ker (mapFirst (k := k) X g) := by
  obtain ⟨c, s, hcf, hgs, hsum⟩ := exists_splitting f g hf hg he
  have hcf' : (mapFirst (k := k) X c).comp (mapFirst (k := k) X f) = LinearMap.id := by
    rw [← mapFirst_comp, hcf, mapFirst_id]
  have hgs' : (mapFirst (k := k) X g).comp (mapFirst (k := k) X s) = LinearMap.id := by
    rw [← mapFirst_comp, hgs, mapFirst_id]
  have hsum' : (mapFirst (k := k) X f).comp (mapFirst (k := k) X c) +
      (mapFirst (k := k) X s).comp (mapFirst (k := k) X g) = LinearMap.id := by
    rw [← mapFirst_comp, ← mapFirst_comp, ← mapFirst_add, hsum, mapFirst_id]
  have hgf : g.comp f = 0 := LinearMap.range_le_ker_iff.mp he.le
  have hgf' : (mapFirst (k := k) X g).comp (mapFirst (k := k) X f) = 0 := by
    rw [← mapFirst_comp, hgf, mapFirst_zero]
  refine ⟨?_, ?_, le_antisymm (LinearMap.range_le_ker_iff.mpr hgf') ?_⟩
  · intro x y hxy
    have hx := DFunLike.congr_fun hcf' x
    have hy := DFunLike.congr_fun hcf' y
    change mapFirst (k := k) X c (mapFirst (k := k) X f x) = x at hx
    change mapFirst (k := k) X c (mapFirst (k := k) X f y) = y at hy
    rw [← hx, ← hy, hxy]
  · intro z
    exact ⟨mapFirst (k := k) X s z, DFunLike.congr_fun hgs' z⟩
  · intro z hz
    refine ⟨mapFirst (k := k) X c z, ?_⟩
    have h := DFunLike.congr_fun hsum' z
    change mapFirst (k := k) X f (mapFirst (k := k) X c z) + mapFirst (k := k) X s (mapFirst (k := k) X g z) = z at h
    simpa only [show mapFirst (k := k) X g z = 0 from hz, map_zero, add_zero] using h

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBalancedExact
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.EnvelopingBimodule

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {M N Q : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)}
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
variable [Module k N] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) N]
variable [Module k Q] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) Q]

theorem mapRight_injective (f : M ⟶ N) (hf : Function.Injective f.hom) :
    Function.Injective (mapRight f) := by
  intro x y h
  apply EnvelopingBimodule.ext
  apply hf
  exact congrArg EnvelopingBimodule.value h

theorem mapRight_surjective (f : M ⟶ N) (hf : Function.Surjective f.hom) :
    Function.Surjective (mapRight f) := by
  rintro ⟨y⟩
  obtain ⟨x, hx⟩ := hf y
  refine ⟨⟨x⟩, ?_⟩
  apply EnvelopingBimodule.ext
  exact hx

theorem mapRight_exact (f : M ⟶ N) (g : N ⟶ Q)
    (he : LinearMap.range f.hom = LinearMap.ker g.hom) :
    LinearMap.range (mapRight f) = LinearMap.ker (mapRight g) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change mapRight g (mapRight f x) = 0
    apply EnvelopingBimodule.ext
    have h : f.hom x.value ∈ LinearMap.range f.hom := ⟨x.value, rfl⟩
    rw [he] at h
    exact h
  · intro hy
    have hy' : y.value ∈ LinearMap.ker g.hom := congrArg EnvelopingBimodule.value hy
    rw [← he] at hy'
    obtain ⟨x, hx⟩ := hy'
    refine ⟨⟨x⟩, ?_⟩
    apply EnvelopingBimodule.ext
    exact hx

variable (X : ModuleCat.{u} R) [Module k X]

theorem tensorMap_shortExact (f : M ⟶ N) (g : N ⟶ Q)
    (hf : Function.Injective f.hom) (hg : Function.Surjective g.hom)
    (he : LinearMap.range f.hom = LinearMap.ker g.hom)
    [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R Q)] :
    Function.Injective (tensorMap X f) ∧ Function.Surjective (tensorMap X g) ∧
      LinearMap.range (tensorMap X f) = LinearMap.ker (tensorMap X g) := by
  obtain ⟨hi, hs, hx⟩ := BalancedTensor.mapFirst_shortExact (k := k) (X := X)
    (mapRight f) (mapRight g) (mapRight_injective f hf)
    (mapRight_surjective g hg) (mapRight_exact f g he)
  refine ⟨hi, hs, ?_⟩
  ext z
  exact Iff.of_eq (congrArg (fun S : Submodule k (BalancedTensor k R (EnvelopingBimodule k R N) X) =>
    z ∈ S) hx)

end ArExplicit.EnvelopingBimodule

end

end OAI
end


