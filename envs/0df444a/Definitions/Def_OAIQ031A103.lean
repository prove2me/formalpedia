-- Prove2me | Definitions.Def_OAIQ031A103
-- name    : OAIQ031A103
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:39:55.18437+00:00
-- url     : https://prove2.me/theorems/07868687-88d2-4bf1-9e61-ebc4d0c2fefe
-- title:
--   Definitions bundle OAIQ031A103 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 11 definitions, 5 instances and 12 theorems. The definitions and types are `OAI.ArExplicit.TriangularInduction.crossHomAdd`, `OAI.ArExplicit.TriangularInduction.eRegularInclusion`, `OAI.ArExplicit.TriangularInduction.eRegularProjection`, `OAI.ArExplicit.TriangularInduction.jCochain`, `OAI.ArExplicit.TriangularInduction.jFunctor`, `OAI.ArExplicit.TriangularInduction.jRegularInclusion`, `OAI.ArExplicit.TriangularInduction.jRegularProjection`, `OAI.ArExplicit.TwistedBimodule.leftModuleCoordinates`, `OAI.ArExplicit.TwoCone.cokernelRestrictionEquiv`, `OAI.ArExplicit.TwoConeKoszulCoordinates.topCoordinateEquiv`, `OAI.ArExplicit.TwoConeKoszulCoordinates.topProjectionEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Complete_TateKoszul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/TateKoszul.lean), [`AuslanderReiten_Cones_TwoConeKoszulCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeKoszulCoordinates.lean), [`AuslanderReiten_Cones_TwoConeProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeProjective.lean), [`AuslanderReiten_Cones_TwoConeRestriction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeRestriction.lean), [`AuslanderReiten_Tensor_TwistedTensorFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/TwistedTensorFunctor.lean), [`AuslanderReiten_Triangular_TriangularCategory`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularCategory.lean), [`AuslanderReiten_Triangular_TriangularCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularCochain.lean), [`AuslanderReiten_Triangular_TriangularCrossHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularCrossHom.lean), [`AuslanderReiten_Triangular_TriangularDualExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularDualExact.lean), [`AuslanderReiten_Triangular_TriangularInduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularInduction.lean), [`AuslanderReiten_Triangular_TriangularProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularProjective.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A067`, `OAIQ031A079`, `OAIQ031A086` and `OAIQ031A089` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A116` and `OAIQ031A117`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A067
import Definitions.Def_OAIQ031A079
import Definitions.Def_OAIQ031A086
import Definitions.Def_OAIQ031A089

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_TateKoszul
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

variable {x y : ∀ a : ℤ, H a →ₗ[k] H (a + 3)} (M : Model x y)

include M

theorem range_column_eq_ker_row (a : ℤ) :
    LinearMap.range (column (x := x) (y := y) a) =
      LinearMap.ker (row (x := x) (y := y) (a + 3)) := by
  by_cases hp : ∃ n : ℕ, a + 3 = 3 * (n : ℤ)
  · obtain ⟨n, hn⟩ := hp
    cases n with
    | zero =>
      have hs : a = -3 := by omega
      let : Subsingleton (H a) := M.outside _
        (fun n h => by omega) (fun n h => by omega)
      have hi : Function.Injective (row (x := x) (y := y) (a + 3)) :=
        injective_of_chart _ (BinaryKoszul.row k 0)
          ((positiveAt M (a + 3) 0 hn).prodCongr (positiveAt M (a + 3) 0 hn))
          (positiveAt M (a + 3 + 3) 1 (by omega))
          (positive_row M (a + 3) 0 hn) (BinaryKoszul.row_zero_injective k)
      ext v
      constructor
      · rintro ⟨u, rfl⟩
        rw [Subsingleton.elim u 0, map_zero]
        exact Submodule.zero_mem _
      · intro hv
        have hv0 : v = 0 := hi (by simpa using hv)
        exact ⟨0, (map_zero _).trans hv0.symm⟩
    | succ n =>
      exact exact_of_charts _ _ (BinaryKoszul.column k n) (BinaryKoszul.row k (n + 1))
        (positiveAt M a n (by omega))
        ((positiveAt M (a + 3) (n + 1) (by omega)).prodCongr
          (positiveAt M (a + 3) (n + 1) (by omega)))
        (positiveAt M (a + 3 + 3) (n + 2) (by omega))
        (positive_column M a n (by omega)) (positive_row M (a + 3) (n + 1) (by omega))
        (BinaryKoszul.range_column_eq_ker_row k n)
  · by_cases hn : ∃ n : ℕ, a + 3 = -1 - 3 * (n : ℤ)
    · obtain ⟨n, hn⟩ := hn
      cases n with
      | zero =>
        have hs : a = -4 := by omega
        let : Subsingleton (H (a + 3 + 3)) := M.outside _
          (fun n h => by omega) (fun n h => by omega)
        have hu : Function.Surjective (column (x := x) (y := y) a) :=
          surjective_of_chart _ (BinaryKoszul.dualColumn k 0)
            (negativeAt M a 1 (by omega))
            ((negativeAt M (a + 3) 0 hn).prodCongr (negativeAt M (a + 3) 0 hn))
            (negative_column M a 0 (by omega)) (BinaryKoszul.dualColumn_zero_surjective k)
        ext v
        constructor
        · intro _
          exact Subsingleton.elim _ _
        · intro _
          exact hu v
      | succ n =>
        exact exact_of_charts _ _ (BinaryKoszul.dualColumn k (n + 1))
          (BinaryKoszul.dualRow k n)
          (negativeAt M a (n + 2) (by omega))
          ((negativeAt M (a + 3) (n + 1) (by omega)).prodCongr
            (negativeAt M (a + 3) (n + 1) (by omega)))
          (negativeAt M (a + 3 + 3) n (by omega))
          (negative_column M a (n + 1) (by omega)) (negative_row M (a + 3) n (by omega))
          (BinaryKoszul.range_dualColumn_eq_ker_dualRow k n)
    · let : Subsingleton (H (a + 3)) := M.outside _
        (fun n h => hp ⟨n, h⟩) (fun n h => hn ⟨n, h⟩)
      ext v
      rw [Subsingleton.elim v 0]
      simp

end ArExplicit.TateKoszul

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeKoszulCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
universe u
variable {k : Type u} [Field k]
variable {H B D E K W : ℤ → Type u}
variable [∀ n, AddCommGroup (H n)] [∀ n, Module k (H n)]
variable [∀ n, AddCommGroup (B n)] [∀ n, Module k (B n)]
variable [∀ n, AddCommGroup (D n)] [∀ n, Module k (D n)]
variable [∀ n, AddCommGroup (E n)] [∀ n, Module k (E n)]
variable [∀ n, AddCommGroup (K n)] [∀ n, Module k (K n)]
variable [∀ n, AddCommGroup (W n)] [∀ n, Module k (W n)]
variable (F : TwoConeFiltration (k := k) B D E K W)
variable (x y : ∀ a : ℤ, H a →ₗ[k] H (a+3))

namespace TwoConeKoszulCoordinates
variable {F x y}
variable (C : TwoConeKoszulCoordinates F x y) (M : TateKoszul.Model x y)

include C M

theorem range_column_eq_ker_row (n : ℤ) :
    LinearMap.range (F.column n) = LinearMap.ker (F.row (n+1)) := by
  let e := (TateKoszul.degreeEquiv (k := k) H (show n-4+3=n+1-2 by omega)).prodCongr
    (TateKoszul.degreeEquiv (k := k) H (show n-4+3=n+1-2 by omega))
  have hrow (w : D (n+1)) : F.row (n+1) w = 0 ↔
      TateKoszul.row (x := x) (y := y) (n-4+3) (e.symm (C.middle (n+1) w)) = 0 := by
    have h0 : F.row (n+1) w = 0 ↔
        TateKoszul.row (x := x) (y := y) (n+1-2) (C.middle (n+1) w) = 0 := by
      rw [← (C.bottom (n+1+1)).map_eq_zero_iff, C.row_eq,
        LinearEquiv.map_eq_zero_iff]
    rw [h0]
    have hr := row_zero_reindex (x := x) (y := y)
      (show n-4+3=n+1-2 by omega) (e.symm (C.middle (n+1) w))
    change _ = 0 ↔ _ = 0 at hr
    rw [e.apply_symm_apply] at hr
    exact hr.symm
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    change F.row (n+1) (F.column n v) = 0
    rw [hrow, C.column_eq, e.symm_apply_apply]
    have hv : TateKoszul.column (x := x) (y := y) (n-4) (C.top n v) ∈
        LinearMap.range (TateKoszul.column (x := x) (y := y) (n-4)) := ⟨_, rfl⟩
    rw [TateKoszul.range_column_eq_ker_row M] at hv
    exact hv
  · intro hw
    have hw' := (hrow w).1 hw
    change e.symm (C.middle (n+1) w) ∈
      LinearMap.ker (TateKoszul.row (x := x) (y := y) (n-4+3)) at hw'
    rw [← TateKoszul.range_column_eq_ker_row M] at hw'
    obtain ⟨v, hv⟩ := hw'
    refine ⟨(C.top n).symm v, (C.middle (n+1)).injective ?_⟩
    rw [C.column_eq, LinearEquiv.apply_symm_apply, hv]
    exact e.apply_symm_apply _

theorem subsingleton_of_ne (n : ℤ) (h0 : n ≠ 0) (h3 : n ≠ 3) : Subsingleton (W n) :=
  F.subsingleton_of_ne (C.row_surjective M) (C.column_injective M)
    (C.range_column_eq_ker_row M) n h0 h3

def topProjectionEquiv : W 3 ≃ₗ[k] E 3 := by
  letI := C.middle_four_subsingleton M
  exact F.topProjectionEquiv (C.row_surjective M) (C.range_column_eq_ker_row M)

@[simp]
theorem topProjectionEquiv_apply (w : W 3) : C.topProjectionEquiv M w = F.projection 3 w := rfl

def topCoordinateEquiv : W 3 ≃ₗ[k] H (-1) :=
  (C.topProjectionEquiv M).trans (C.top 3)

@[simp]
theorem topCoordinateEquiv_apply (w : W 3) :
    C.topCoordinateEquiv M w = C.top 3 (F.projection 3 w) := rfl

end TwoConeKoszulCoordinates
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TwoCone

universe u

variable {R : Type u} [Ring R] (D : Data R)

theorem firstCokernel_projective
    (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
    (hp : ∀ n, Module.Projective R (BaseCokernel D n)) (n : ℕ) :
    Module.Projective R (FirstCokernel D n) := by
  let := hp n
  let := hp (n+2)
  exact ConeCokernel.projective (D.d n) (D.d (n+2)) (D.first n)
    (D.d (n+3)) (D.first (n+1)) (hex (n+2)) (D.first_comm n)

theorem cokernel_projective
    (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
    (hp : ∀ n, Module.Projective R (BaseCokernel D n)) (n : ℕ) :
    Module.Projective R (Cokernel D n) := by
  let := firstCokernel_projective D hex hp n
  let := firstCokernel_projective D hex hp (n+2)
  exact ConeCokernel.projective (firstD D n) (firstD D (n+2)) (secondOnFirst D n)
    (firstD D (n+3)) (secondOnFirst D (n+1)) (firstD_exact D hex (n+2))
    (secondOnFirst_comm D n)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeRestriction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.TwoCone

universe u
variable {R S : Type u} [Ring R] [Ring S] (j : S →+* R) (D : Data R)

def cokernelRestrictionEquiv (n : ℕ) :
    (ModuleCat.restrictScalars j).obj (ModuleCat.of R (Cokernel D n)) ≃ₗ[S]
      Cokernel (D.restrict j) n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensorFunctor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.TwistedBimodule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (σ : R ≃ₐ[k] R)

def leftModuleCoordinates (M : ModuleCat.{u} R) :
    TwistedLeftModule k R σ M ≃ₗ[R]
      (ModuleCat.restrictScalars σ.symm.toRingHom).obj M where
  toFun x := x.value
  invFun x := ⟨x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end ArExplicit.TwistedBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularInduction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TriangularInduction.instAdditiveModuleCatTriangularEFunctor _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable (k R F : Type*) [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable (M : Type*) [AddCommGroup M] [Module k M] [Module R M]

variable (N : Type*) [AddCommGroup N] [Module R N]

namespace TriangularInduction

variable {k R F M N}
variable {M' N' : Type*} [AddCommGroup M'] [Module k M'] [Module R M']
variable [AddCommGroup N'] [Module R N']
variable {ψ : BalancedTensor k R F M' →ₗ[R] N'}
variable [IsScalarTower k R M] [IsScalarTower k R M']

variable [Module k N] [Module k N']
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k Rᵐᵒᵖ F]
variable [IsScalarTower k R N] [IsScalarTower k R N']
variable [SMulCommClass k R M'] [SMulCommClass k R N']

theorem hom_E_J_eq_zero (g : TriangularE k R F M →ₗ[Triangular R F] TriangularJ k R F N) :
    g = 0 := by
  apply eHomEquiv.injective
  exact Subsingleton.elim _ _

end TriangularInduction
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TriangularInduction.instAdditiveModuleCatTriangularEFunctor _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

variable {k R F : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]

def eRegularInclusion : TriangularE k R F R →ₗ[Triangular R F] Triangular R F where
  toFun x := ⟨x.top, 0, BalancedTensor.runitLeft (S := R) x.bottom⟩
  map_add' x y := by ext <;> simp
  map_smul' a x := by
    ext
    · rfl
    · simp
    · change BalancedTensor.runitLeft (S := R)
          (BalancedTensor.tmul a.off x.top + a.bottom • x.bottom) =
        a.bottom • BalancedTensor.runitLeft (S := R) x.bottom + MulOpposite.op x.top • a.off
      rw [map_add, map_smul]
      exact add_comm _ _

def eRegularProjection : Triangular R F →ₗ[Triangular R F] TriangularE k R F R where
  toFun a := ⟨a.top, (BalancedTensor.runitLeft (k := k) (R := R) (S := R)).symm a.off⟩
  map_add' a b := by ext <;> simp
  map_smul' a b := by
    ext
    · rfl
    · change (BalancedTensor.runitLeft (S := R)).symm
          (a.bottom • b.off + MulOpposite.op b.top • a.off) =
        BalancedTensor.tmul a.off b.top +
          a.bottom • (BalancedTensor.runitLeft (S := R)).symm b.off
      apply (BalancedTensor.runitLeft (S := R)).injective
      rw [LinearEquiv.apply_symm_apply, map_add, map_smul, LinearEquiv.apply_symm_apply]
      exact add_comm _ _

def jRegularInclusion : TriangularJ k R F R →ₗ[Triangular R F] Triangular R F where
  toFun x := ⟨0, x.bottom, 0⟩
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp

def jRegularProjection : Triangular R F →ₗ[Triangular R F] TriangularJ k R F R where
  toFun a := ⟨0, a.bottom⟩
  map_add' a b := by ext; simp
  map_smul' a b := by ext; simp

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularDualExact
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TriangularInduction.instAdditiveModuleCatTriangularEFunctor _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.TriangularInduction

variable {k R F : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable {K L M U V : Type*}
variable [AddCommGroup K] [Module k K] [Module R K] [IsScalarTower k R K]
variable [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable [AddCommGroup U] [Module k U] [Module R U] [IsScalarTower k R U]
variable [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]

theorem eHomLift (e : K →ₗ[R] L) (d : L →ₗ[R] M) (h : HomExactAt e d)
    [Module.Finite R U] [Module.Projective R U]
    {ψ : BalancedTensor k R F U →ₗ[R] V}
    (g : TriangularE k R F L →ₗ[Triangular R F] TriangularModule k R F U V ψ)
    (hg : g.comp (eMap e) = 0) :
    ∃ G : TriangularE k R F M →ₗ[Triangular R F] TriangularModule k R F U V ψ,
      G.comp (eMap d) = g := by
  have ha : (TriangularModule.topMap g).comp e = 0 := by
    ext x
    have hx := congrArg TriangularModule.top (DFunLike.congr_fun hg ⟨x, 0⟩)
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, TriangularModule.top_zero,
      eMap, eHom, TriangularModule.hom, LinearMap.coe_mk, AddHom.coe_mk,
      map_zero, TriangularModule.topMap_apply] using hx
  obtain ⟨b, hb⟩ := h.projective (TriangularModule.topMap g) ha
  refine ⟨eHom b, ?_⟩
  apply eHomEquiv.injective
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun hb x

omit [IsScalarTower k R F] [SMulCommClass k Rᵐᵒᵖ F] in
theorem regular_decomposition (a : Triangular R F) :
    eRegularInclusion (eRegularProjection (k := k) a) +
      jRegularInclusion (jRegularProjection (k := k) a) = a := by
  ext <;> simp [eRegularInclusion, eRegularProjection, jRegularInclusion, jRegularProjection]

end ArExplicit.TriangularInduction

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularCategory
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

universe u

variable (k R F : Type u) [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def jFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} (Triangular R F) where
  obj M := ModuleCat.of _ (TriangularJ k R F M)
  map f := ModuleCat.ofHom (jMap f.hom)
  map_id M := by apply ModuleCat.hom_ext; exact jMap_id
  map_comp f g := by apply ModuleCat.hom_ext; exact jMap_comp f.hom g.hom

instance instAdditiveModuleCatTriangularJFunctor : (jFunctor k R F).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply jHomEquiv.injective
    ext m
    rfl

instance instFaithfulModuleCatTriangularEFunctor : (eFunctor k R F).Faithful where
  map_injective := by
    intro M N f g h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact congrArg (fun a : (eFunctor k R F).obj M ⟶ (eFunctor k R F).obj N =>
      (a.hom ⟨m, 0⟩).top) h

instance instFaithfulModuleCatTriangularJFunctor : (jFunctor k R F).Faithful where
  map_injective := by
    intro M N f g h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact congrArg (fun a : (jFunctor k R F).obj M ⟶ (jFunctor k R F).obj N =>
      (a.hom ⟨0, m⟩).bottom) h

instance instFullModuleCatTriangularEFunctor : (eFunctor k R F).Full where
  map_surjective := by
    intro M N g
    refine ⟨ModuleCat.ofHom (TriangularModule.topMap g.hom), ?_⟩
    apply ModuleCat.hom_ext
    exact eHom_topMap g.hom

instance instFullModuleCatTriangularJFunctor : (jFunctor k R F).Full where
  map_surjective := by
    intro M N g
    refine ⟨ModuleCat.ofHom (TriangularModule.bottomMap g.hom), ?_⟩
    apply ModuleCat.hom_ext
    exact jHom_bottomMap g.hom

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularCochain
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

open CategoryTheory

universe u

variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

abbrev jCochain (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((jFunctor k R F).mapHomologicalComplex _).obj P

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularCrossHom
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

open CategoryTheory CochainComplex.HomComplex

universe u

variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def crossHomAdd (M N : ModuleCat.{u} R) :
    (M ⟶ (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).obj N) →+
      ((jFunctor k R F).obj M ⟶ (eFunctor k R F).obj N) where
  toFun f := ModuleCat.ofHom (jHom f.hom)
  map_zero' := by
    apply ModuleCat.hom_ext
    apply jHomEquiv.injective
    exact map_zero jHomEquiv |>.symm
  map_add' f g := by
    apply ModuleCat.hom_ext
    apply jHomEquiv.injective
    ext z
    rfl

theorem crossHomAdd_source {M N L : ModuleCat.{u} R} (f : M ⟶ N)
    (g : N ⟶ (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).obj L) :
    crossHomAdd M L (f ≫ g) = (jFunctor k R F).map f ≫ crossHomAdd N L g := by
  apply ModuleCat.hom_ext
  apply jHomEquiv.injective
  rfl

theorem crossHomAdd_target {M N L : ModuleCat.{u} R}
    (f : M ⟶ (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).obj N)
    (g : N ⟶ L) :
    crossHomAdd M L (f ≫ (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).map g) =
      crossHomAdd M N f ≫ (eFunctor k R F).map g := by
  apply ModuleCat.hom_ext
  apply jHomEquiv.injective
  rfl

end ArExplicit.TriangularInduction

end

end OAI
end


