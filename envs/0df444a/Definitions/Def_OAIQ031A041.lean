-- Prove2me | Definitions.Def_OAIQ031A041
-- name    : OAIQ031A041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:03:51.655804+00:00
-- url     : https://prove2.me/theorems/17191744-c422-47dc-b631-f3b72642d44d
-- title:
--   Definitions bundle OAIQ031A041 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 1 definition and 11 theorems. The definitions and types are `OAI.ArExplicit.shiftedConjugate`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_TwoConeFiltration`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeFiltration.lean), [`AuslanderReiten_Coordinates_GradedConjugate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/GradedConjugate.lean), [`AuslanderReiten_Coordinates_IteratedCubicCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/IteratedCubicCoordinates.lean), [`AuslanderReiten_Coordinates_IteratedShiftAddition`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/IteratedShiftAddition.lean), [`AuslanderReiten_Coordinates_IteratedShiftNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/IteratedShiftNaturality.lean), [`AuslanderReiten_Coordinates_ShiftedConjugateAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ShiftedConjugateAction.lean), [`AuslanderReiten_HomComplex_FullHomMapLinear`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomMapLinear.lean), [`AuslanderReiten_Homology_TriangleConnectingProduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/TriangleConnectingProduct.lean), [`AuslanderReiten_Resolutions_CoverStepCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/CoverStepCoordinates.lean), [`AuslanderReiten_Resolutions_CoverStepFullHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/CoverStepFullHom.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A013`, `OAIQ031A018`, `OAIQ031A020`, `OAIQ031A021` and `OAIQ031A022` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A058` and `OAIQ031A059`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A013
import Definitions.Def_OAIQ031A018
import Definitions.Def_OAIQ031A020
import Definitions.Def_OAIQ031A021
import Definitions.Def_OAIQ031A022

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeFiltration
attribute [-instance] _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

universe u

variable {k : Type u} [Field k]
variable (B D E K W : ℤ → Type u)
variable [∀ n, AddCommGroup (B n)] [∀ n, Module k (B n)]
variable [∀ n, AddCommGroup (D n)] [∀ n, Module k (D n)]
variable [∀ n, AddCommGroup (E n)] [∀ n, Module k (E n)]
variable [∀ n, AddCommGroup (K n)] [∀ n, Module k (K n)]
variable [∀ n, AddCommGroup (W n)] [∀ n, Module k (W n)]

namespace TwoConeFiltration

variable {B D E K W}
variable (F : TwoConeFiltration (k := k) B D E K W)

theorem attach_injective (n : ℤ) (hcolumn : Function.Injective (F.column n)) :
    Function.Injective (F.attach n) := by
  intro x y h
  apply hcolumn
  have h' := congrArg (F.middle (n + 1)) h
  change (F.middle (n + 1)).comp (F.attach n) x =
    (F.middle (n + 1)).comp (F.attach n) y at h'
  simpa only [F.adjacent] using h'

end TwoConeFiltration
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_IteratedShiftNaturality
attribute [-instance] _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit

universe v u
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable (Y : ℕ → C) (s : ∀ n, Y n ≅ (Y (n + 1))⟦(1 : ℤ)⟧)

variable {Y s} {Z : ℕ → C} (t : ∀ n, Z n ≅ (Z (n + 1))⟦(1 : ℤ)⟧)
variable (f : ∀ n, Y n ⟶ Z n)

theorem iteratedShiftIso_natural
    (hs : ∀ n, f n ≫ (t n).hom = (s n).hom ≫
      (CategoryTheory.shiftFunctor C (1 : ℤ)).map (f (n + 1))) (n : ℕ) :
    f 0 ≫ (iteratedShiftIso Z t n).hom =
      (iteratedShiftIso Y s n).hom ≫ (CategoryTheory.shiftFunctor C (n : ℤ)).map (f n) := by
  induction n with
  | zero => exact (CategoryTheory.shiftFunctorZero C ℤ).inv.naturality (f 0)
  | succ n ih =>
    let F := CategoryTheory.shiftFunctor C (n : ℤ)
    let A := CategoryTheory.shiftFunctorAdd' C (1 : ℤ) (n : ℤ)
      ((n + 1 : ℕ) : ℤ) (by omega)
    have h₂ : F.map (f n) ≫ F.map (t n).hom =
        F.map (s n).hom ≫ F.map ((CategoryTheory.shiftFunctor C (1 : ℤ)).map (f (n + 1))) := by
      rw [← F.map_comp, hs n, F.map_comp]
    have h₃ : F.map ((CategoryTheory.shiftFunctor C (1 : ℤ)).map (f (n + 1))) ≫
        A.inv.app (Z (n + 1)) = A.inv.app (Y (n + 1)) ≫
          (CategoryTheory.shiftFunctor C ((n + 1 : ℕ) : ℤ)).map (f (n + 1)) :=
      A.inv.naturality (f (n + 1))
    simpa only [iteratedShiftIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Iso.symm_hom, F, A, Category.assoc] using compose_squares (compose_squares ih h₂) h₃

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ShiftedConjugateAction
attribute [-instance] _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X Y Z S : C} (n m : ℤ) (e : X ≅ Y⟦n⟧) (f : X ≅ Z⟦m⟧) (c : Z ⟶ Y)

def shiftedConjugate : X ⟶ X⟦m-n⟧ :=
  ShiftedHom.comp f.hom
    (ShiftedHom.comp (ShiftedHom.mk₀ (0:ℤ) rfl c) (negativeShiftIso n e).hom
      (by omega : -n+0 = -n)) (by omega : -n+m=m-n)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_GradedConjugate
attribute [-instance] _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X Y Z S : C} (n m d : ℤ) (h : -n+m=d)
variable (e : X ≅ Y⟦n⟧) (f : X ≅ Z⟦m⟧) (c : Z ⟶ Y)

theorem gradedConjugate_eq_of_square (p : X ⟶ X⟦d⟧)
    (hp : ShiftedHom.comp p e.hom (by omega : n+d=m) =
      ShiftedHom.comp f.hom (ShiftedHom.mk₀ (0:ℤ) rfl c) (by omega : 0+m=m)) :
    gradedConjugate n m d h e f c = p := by
  apply (cancel_mono (e.hom⟦d⟧' ≫
    (shiftFunctorAdd' C n d m (by omega)).inv.app Y)).mp
  change ShiftedHom.comp (gradedConjugate n m d h e f c) e.hom _ = ShiftedHom.comp p e.hom _
  rw [gradedConjugate_comp_hom]
  exact hp.symm

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_IteratedShiftAddition
attribute [-instance] _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable (Y : ℕ → C) (s : ∀ n, Y n ≅ (Y (n+1))⟦(1 : ℤ)⟧)

theorem iteratedShiftIso_succ_hom (n : ℕ) :
    (iteratedShiftIso Y s (n+1)).hom =
      ShiftedHom.comp (iteratedShiftIso Y s n).hom (s n).hom
        (by omega : 1+(n:ℤ)=((n+1:ℕ):ℤ)) := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_IteratedCubicCoordinates
attribute [-instance] _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable (Y : ℕ → C) (s : ∀ n, Y n ≅ (Y (n+1))⟦(1 : ℤ)⟧)

theorem iteratedShiftIso_three_hom (n : ℕ) :
    (iteratedShiftIso Y s (n+3)).hom =
      ShiftedHom.comp (iteratedShiftIso Y s 3).hom
        (iteratedShiftIso (fun j => Y (j+3)) (fun j => s (j+3)) n).hom
          (by omega : (n:ℤ)+3=((n+3:ℕ):ℤ)) := by
  induction n with
  | zero =>
    have hz : (iteratedShiftIso (fun j => Y (j+3)) (fun j => s (j+3)) 0).hom =
        ShiftedHom.mk₀ (0:ℤ) rfl (𝟙 (Y 3)) := by
      simp only [iteratedShiftIso, ShiftedHom.mk₀, shiftFunctorZero',
        eqToIso_refl, Iso.refl_trans, Category.id_comp]
      rfl
    rw [hz]
    exact (ShiftedHom.comp_mk₀_id _ 0 rfl).symm
  | succ n ih =>
    change (iteratedShiftIso Y s ((n+3)+1)).hom = _
    rw [iteratedShiftIso_succ_hom, ih, iteratedShiftIso_succ_hom]
    exact ShiftedHom.comp_assoc (iteratedShiftIso Y s 3).hom
      (iteratedShiftIso (fun j => Y (j+3)) (fun j => s (j+3)) n).hom
      (s (n+3)).hom (by omega) (by omega) (by omega)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomMapLinear
attribute [-instance] _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit
variable {k : Type*} [CommRing k]
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [Linear k C] [Linear k D]
variable (Φ : C ⥤ D) [Φ.Additive] [Φ.Linear k]
variable (K L : CochainComplex C ℤ) (n : ℤ)

variable {K L n}

theorem fullHomPostcomp_identity (f : K ⟶ L) :
    fullHomPostcomp f 0 (CohomologyClass.mk (Cocycle.ofHom (𝟙 K))) =
      CohomologyClass.mk (Cocycle.ofHom f) := by
  rw [fullHomPostcomp_mk]
  congr 1
  apply Subtype.ext
  exact Cochain.id_comp _

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TriangleConnectingProduct
attribute [-instance] _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
namespace ArExplicit.TriangleGradedSequence
universe u v w
variable (k : Type u) [CommRing k] [CharP k 2]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
variable (T : Triangle C) (X : C)

theorem second_eq_shift (n : ℤ) (v : Middle T X n) :
    second k T X n v = v ≫ T.mor₂⟦n⟧' := by
  change v ≫ (n.negOnePow • T.mor₂⟦n⟧') = _
  rw [integerUnit_smul k]

theorem nextIso_inv_first (n : ℤ) :
    (nextIso T n).inv.hom₁ =
      (CategoryTheory.shiftFunctorAdd' C n 1 (n+1) rfl).inv.app T.obj₁ := by
  simp [nextIso]
  rfl

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_CoverStepCoordinates
attribute [-instance] _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v w
section Category
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X Y Z S : C} (n : ℤ) (e : X ≅ Y⟦n⟧)
variable (s : Y ≅ Z⟦(1 : ℤ)⟧) (t : X ≅ Z⟦n+1⟧)
variable (ht : t.hom = ShiftedHom.comp e.hom s.hom (add_comm 1 n))

include ht in
theorem negativeShiftIso_step :
    ShiftedHom.comp s.hom (negativeShiftIso (n+1) t).hom
      (by omega : -(n+1)+1 = -n) = (negativeShiftIso n e).hom := by
  apply (CategoryTheory.shiftFunctor C n).map_injective
  apply (cancel_epi e.hom).mp
  apply (cancel_mono ((shiftFunctorAdd' C (-n) n 0 (by omega)).inv.app X)).mp
  simp only [Category.assoc]
  change ShiftedHom.comp e.hom
    (ShiftedHom.comp s.hom (negativeShiftIso (n+1) t).hom (by omega : -(n+1)+1 = -n))
      (by omega : -n+n=0) =
      ShiftedHom.comp e.hom (negativeShiftIso n e).hom (by omega : -n+n=0)
  rw [← ShiftedHom.comp_assoc e.hom s.hom (negativeShiftIso (n+1) t).hom
    (add_comm 1 n) (by omega : -(n+1)+1 = -n) (by omega), ← ht,
    hom_comp_negativeShiftIso, hom_comp_negativeShiftIso]

include ht in
theorem shiftedNegative_step (a : ℤ) (v : S ⟶ Y⟦a⟧) :
    ShiftedHom.comp (ShiftedHom.comp v s.hom (add_comm 1 a))
      (negativeShiftIso (n+1) t).hom (by omega : -(n+1)+(a+1)=a-n) =
    ShiftedHom.comp v (negativeShiftIso n e).hom (by omega : -n+a=a-n) := by
  rw [ShiftedHom.comp_assoc v s.hom (negativeShiftIso (n+1) t).hom
    (add_comm 1 a) (by omega : -(n+1)+1 = -n) (by omega),
    negativeShiftIso_step n e s t ht]

end Category
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_CoverStepFullHom
attribute [-instance] _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
universe u w
variable (k : Type u) [Field k]
variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear k C]
variable {K : CochainComplex C ℤ}
local notation "HC" => HomotopyCategory C (ComplexShape.up ℤ)
local notation "X₀" => sourceObject K

theorem shiftedNegative_step_at (Y Z : HC) (n : ℤ)
    (e : X₀ ≅ Y⟦n⟧) (s : Y ≅ Z⟦(1 : ℤ)⟧) (t : X₀ ≅ Z⟦n+1⟧)
    (ht : t.hom = ShiftedHom.comp e.hom s.hom (add_comm 1 n))
    (a d : ℤ) (hd : d=a-n) (v : X₀ ⟶ Y⟦a⟧) :
    ShiftedHom.comp (ShiftedHom.comp v s.hom (add_comm 1 a))
      (negativeShiftIso (n+1) t).hom (by omega : -(n+1)+(a+1)=d) =
      ShiftedHom.comp v (negativeShiftIso n e).hom (by omega : -n+a=d) := by
  subst d
  exact shiftedNegative_step n e s t ht a v

end ArExplicit

end

end OAI
end


