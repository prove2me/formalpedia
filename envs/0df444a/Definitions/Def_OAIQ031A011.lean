-- Prove2me | Definitions.Def_OAIQ031A011
-- name    : OAIQ031A011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:56:26.714403+00:00
-- url     : https://prove2.me/theorems/3589fd86-f358-4769-a8a9-36c411e84939
-- title:
--   Definitions bundle OAIQ031A011 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 46 declarations of OpenAI's Lean: 21 definitions, 2 instances and 23 theorems. The definitions and types are `OAI.ArExplicit.BinaryKoszul.DualPiece`, `OAI.ArExplicit.BinaryKoszul.Piece`, `OAI.ArExplicit.BinaryKoszul.column`, `OAI.ArExplicit.BinaryKoszul.dualColumn`, `OAI.ArExplicit.BinaryKoszul.dualRow`, `OAI.ArExplicit.BinaryKoszul.mulX`, `OAI.ArExplicit.BinaryKoszul.mulY`, `OAI.ArExplicit.BinaryKoszul.row`, `OAI.ArExplicit.CompleteComparison.RawCokernelAt`, `OAI.ArExplicit.ResolutionProducts.natCocycleProduct`, `OAI.ArExplicit.ResolutionProducts.natComparisonAugmentation`, `OAI.ArExplicit.ResolutionProducts.natComparisonCochain`, `OAI.ArExplicit.VectorCochain.cycleSection`, `OAI.ArExplicit.VectorCochain.gradedHomology`, `OAI.ArExplicit.VectorCochain.literalClass`, `OAI.ArExplicit.VectorCochain.literalCyclesIso`, `OAI.ArExplicit.VectorCochain.representatives`, `OAI.ArExplicit.VectorCochain.splitting`, `OAI.ArExplicit.VectorCochain.zeroDifferential`, `OAI.ArExplicit.VectorCochain.zeroHomologyIso`, `OAI.ArExplicit.supportedRestriction`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_Radical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/Radical.lean), [`AuslanderReiten_Algebras_TensorRadical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TensorRadical.lean), [`AuslanderReiten_Ext_NatComparisonExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/NatComparisonExt.lean), [`AuslanderReiten_HomComplex_FullHomProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomProducts.lean), [`AuslanderReiten_Homology_CochainCycleClass`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/CochainCycleClass.lean), [`AuslanderReiten_Homology_VectorCochainSplitting`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/VectorCochainSplitting.lean), [`AuslanderReiten_Modules_SupportedPi`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/SupportedPi.lean), [`AuslanderReiten_Resolutions_BinaryKoszul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/BinaryKoszul.lean), [`AuslanderReiten_Resolutions_BinaryKoszulDual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/BinaryKoszulDual.lean), [`AuslanderReiten_Resolutions_NatResolutionCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/NatResolutionCochain.lean), [`AuslanderReiten_Resolutions_ResolutionProductCompatibility`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionProductCompatibility.lean), [`AuslanderReiten_Stable_RawSourceDegrees`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/RawSourceDegrees.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A033`, `OAIQ031A034`, `OAIQ031A035`, `OAIQ031A036`, `OAIQ031A037` and `OAIQ031A038`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_Radical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable {R S : Type*} [Ring R] [Ring S]

theorem nilIdeal_le_jacobson (I : Ideal R)
    (hnil : ∀ x ∈ I, IsNilpotent x) : I ≤ Ring.jacobson R := by
  intro x hx
  rw [← Ideal.jacobson_bot]
  apply Ideal.mem_jacobson_iff.mpr
  intro y
  obtain ⟨u, hu⟩ := (hnil (y * x) (I.mul_mem_left y hx)).isUnit_add_one
  refine ⟨↑u⁻¹, ?_⟩
  change (↑u⁻¹ : R) * y * x + ↑u⁻¹ - 1 = 0
  calc
    (↑u⁻¹ : R) * y * x + ↑u⁻¹ - 1 = ↑u⁻¹ * (y * x + 1) - 1 := by
      rw [mul_add, mul_one, mul_assoc]
    _ = 0 := by rw [← hu]; simp

theorem nilpotentIdeal_le_jacobson (I : Ideal R) (hnil : IsNilpotent I) :
    I ≤ Ring.jacobson R := by
  apply nilIdeal_le_jacobson I
  intro x hx
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  have h := Ideal.pow_mem_pow hx n
  simpa only [hn, Ideal.zero_eq_bot, Ideal.mem_bot] using h

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorRadical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

variable {k R S : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

theorem finiteAlgebra_radical_isNilpotent [IsArtinianRing k] [Module.Finite k R] :
    IsNilpotent (Ring.jacobson R) := by
  let : IsArtinianRing R := IsArtinianRing.of_finite k R
  exact IsSemiprimaryRing.isNilpotent

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_NatResolutionCochain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]

variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable (r : ℕ) (f : ∀ n : ℕ, P.complex.X (r+n) ⟶ Q.complex.X n)

def natComparisonCochain : Cochain P.cochainComplex Q.cochainComplex (r : ℤ) :=
  Cochain.mk (fun p q hpq => if hq : q ≤ 0 then
    let m := (-q).toNat
    (P.cochainComplexXIso p (r+m) (by dsimp [m]; omega)).hom ≫ f m ≫
      (Q.cochainComplexXIso q m (by dsimp [m]; omega)).inv
    else 0)

theorem natComparisonCochain_v (m : ℕ) :
    (natComparisonCochain P Q r f).v (-((r+m : ℕ) : ℤ)) (-(m : ℤ)) (by omega) =
      (P.cochainComplexXIso (-((r+m : ℕ) : ℤ)) (r+m) rfl).hom ≫ f m ≫
        (Q.cochainComplexXIso (-(m : ℤ)) m rfl).inv := by
  cases m <;> rfl

theorem natComparisonCochain_v_of_eq (p : ℤ) (m : ℕ) (hp : p+(r : ℤ)=-(m : ℤ)) :
    (natComparisonCochain P Q r f).v p (-(m : ℤ)) hp =
      (P.cochainComplexXIso p (r+m) (by omega)).hom ≫ f m ≫
        (Q.cochainComplexXIso (-(m : ℤ)) m rfl).inv := by
  cases m <;> rfl

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit.CompleteComparison

universe u

section Cochains

variable {C : Type*} [Category* C] [Preadditive C]
variable {K L M : CochainComplex C ℤ} {n m : ℤ}

theorem cochain_component_transport (x : Cochain K L n)
    (p q r : ℤ) (hpq : p + n = q) (hqr : q = r) :
    x.v p q hpq ≫ (L.XIsoOfEq hqr).hom = x.v p r (hpq.trans hqr) := by
  subst r
  simp

end Cochains

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionProductCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

def natCocycleProduct {K L M : CochainComplex C ℤ} {n m : ℕ}
    (x : Cocycle K L (n : ℤ)) (y : Cocycle L M (m : ℤ)) :
    Cocycle K M ((n+m : ℕ) : ℤ) :=
  Cocycle.mk (x.val.comp y.val (by omega)) _ rfl (by
    rw [δ_comp x.val y.val (by omega) ((n : ℤ)+1) ((m : ℤ)+1)
      (((n+m : ℕ) : ℤ)+1) rfl rfl rfl]
    simp)

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_NatComparisonExt
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
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (r : ℕ) (f : ∀ n : ℕ, P.complex.X (r+n) ⟶ P.complex.X n)
variable (hf : ∀ n, f (n+1) ≫ P.complex.d (n+1) n =
  P.complex.d (r+(n+1)) (r+n) ≫ f n)
include f in
def natComparisonAugmentation : P.complex.X r ⟶ X := by
  exact f 0 ≫ P.π.f 0

include hf

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem natComparison_augmented_cycle :
    P.complex.d (r+1) r ≫ natComparisonAugmentation P r f = 0 := by
  have h := congrArg (fun z => z ≫ P.π.f 0) (hf 0)
  change (f 1 ≫ P.complex.d 1 0) ≫ P.π.f 0 =
    (P.complex.d (r+1) r ≫ f 0) ≫ P.π.f 0 at h
  rw [Category.assoc, P.complex_d_comp_π_f_zero, CategoryTheory.Limits.comp_zero,
    Category.assoc] at h
  exact h.symm

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_CochainCycleClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace ArExplicit.VectorCochain
universe u
variable (k : Type u) [Field k]
variable (P : CochainComplex (ModuleCat.{u} k) ℕ)

def literalCyclesIso (n : ℕ) :=
  P.cyclesIsoSc' (n-1) n (n+1) (by cases n <;> simp) (by simp) ≪≫
    (P.sc' (n-1) n (n+1)).moduleCatCyclesIso

def literalClass (n : ℕ) (x : LinearMap.ker (P.d n (n+1)).hom) : P.homology n :=
  (P.homologyπ n).hom ((literalCyclesIso k P n).inv.hom x)

@[simp] theorem literalCyclesIso_inv_iCycles (n : ℕ)
    (x : LinearMap.ker (P.d n (n+1)).hom) :
    (P.iCycles n).hom ((literalCyclesIso k P n).inv.hom x) = x.val := by
  have he : (literalCyclesIso k P n).inv ≫ P.iCycles n =
      ModuleCat.ofHom (LinearMap.ker (P.d n (n+1)).hom).subtype := by
    simp only [literalCyclesIso, Iso.trans_inv, Category.assoc,
      P.cyclesIsoSc'_inv_iCycles]
    exact (P.sc' (n-1) n (n+1)).moduleCatCyclesIso_inv_iCycles
  exact congrArg (fun f => f.hom x) he

theorem literalClass_eq_quotient (n : ℕ)
    (x : LinearMap.ker (P.d n (n+1)).hom) :
    literalClass k P n x =
      ((P.homologyIsoSc' (n-1) n (n+1) (by cases n <;> simp) (by simp)).inv).hom
        ((P.sc' (n-1) n (n+1)).moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk x)) := by
  have he : (literalCyclesIso k P n).inv ≫ P.homologyπ n =
      (P.sc' (n-1) n (n+1)).moduleCatLeftHomologyData.π ≫
        (P.sc' (n-1) n (n+1)).moduleCatHomologyIso.inv ≫
          (P.homologyIsoSc' (n-1) n (n+1) (by cases n <;> simp) (by simp)).inv := by
    simp only [literalCyclesIso, Iso.trans_inv, Category.assoc]
    rw [← P.π_homologyIsoSc'_inv (n-1) n (n+1) (by cases n <;> simp) (by simp),
      ← Category.assoc, ShortComplex.moduleCatCyclesIso_inv_π, Category.assoc]
  exact congrArg (fun f => f.hom x) he

variable {P} {Q : CochainComplex (ModuleCat.{u} k) ℕ}

theorem literalClass_map (f : P ⟶ Q) (n : ℕ)
    (x : LinearMap.ker (P.d n (n+1)).hom)
    (y : LinearMap.ker (Q.d n (n+1)).hom)
    (hxy : (f.f n).hom x.val = y.val) :
    (homologyMap f n).hom (literalClass k P n x) = literalClass k Q n y := by
  have hc : (cyclesMap f n).hom ((literalCyclesIso k P n).inv.hom x) =
      (literalCyclesIso k Q n).inv.hom y := by
    apply (ModuleCat.mono_iff_injective (Q.iCycles n)).mp inferInstance
    have hh := congrArg (fun u => u.hom ((literalCyclesIso k P n).inv.hom x))
      (cyclesMap_i f n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, literalCyclesIso_inv_iCycles] at hh ⊢
    exact hh.trans hxy
  have hh := congrArg (fun u => u.hom ((literalCyclesIso k P n).inv.hom x))
    (homologyπ_naturality f n)
  change (homologyMap f n).hom ((P.homologyπ n).hom _) = _
  rw [show (homologyMap f n).hom ((P.homologyπ n).hom ((literalCyclesIso k P n).inv.hom x)) =
    (Q.homologyπ n).hom ((cyclesMap f n).hom ((literalCyclesIso k P n).inv.hom x)) from hh]
  rw [hc]
  rfl

end ArExplicit.VectorCochain

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_VectorCochainSplitting
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

instance vectorSpaceInjective (M : ModuleCat.{u} k) : CategoryTheory.Injective M where
  factors g f hf := by
    obtain ⟨r, hr⟩ := f.hom.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective f).mp hf))
    refine ⟨ModuleCat.ofHom (g.hom.comp r), ?_⟩
    apply ModuleCat.hom_ext
    change (g.hom.comp r).comp f.hom = g.hom
    rw [LinearMap.comp_assoc, hr, LinearMap.comp_id]

abbrev zeroDifferential (X : ℕ → ModuleCat.{u} k) : CochainComplex (ModuleCat.{u} k) ℕ where
  X := X
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

def zeroHomologyIso (X : ℕ → ModuleCat.{u} k) (n : ℕ) :
    (zeroDifferential k X).homology n ≅ X n :=
  ((zeroDifferential k X).isoHomologyπ ((ComplexShape.up ℕ).prev n) n rfl rfl).symm ≪≫
    (zeroDifferential k X).iCyclesIso n ((ComplexShape.up ℕ).next n) rfl rfl

@[simp, reassoc] theorem zeroHomologyIso_π (X : ℕ → ModuleCat.{u} k) (n : ℕ) :
    (zeroDifferential k X).homologyπ n ≫ (zeroHomologyIso k X n).hom =
      (zeroDifferential k X).iCycles n := by
  let a := (zeroDifferential k X).isoHomologyπ ((ComplexShape.up ℕ).prev n) n rfl rfl
  let b := (zeroDifferential k X).iCyclesIso n ((ComplexShape.up ℕ).next n) rfl rfl
  change a.hom ≫ a.inv ≫ b.hom = b.hom
  exact a.hom_inv_id_assoc _

variable (P : CochainComplex (ModuleCat.{u} k) ℕ)

abbrev gradedHomology : CochainComplex (ModuleCat.{u} k) ℕ :=
  zeroDifferential k (fun n => P.homology n)

def cycleSection (n : ℕ) : P.homology n ⟶ P.cycles n :=
  Projective.factorThru (𝟙 (P.homology n)) (P.homologyπ n)

@[simp, reassoc] theorem cycleSection_π (n : ℕ) :
    cycleSection k P n ≫ P.homologyπ n = 𝟙 _ :=
  Projective.factorThru_comp _ _

def representatives : gradedHomology k P ⟶ P where
  f n := cycleSection k P n ≫ P.iCycles n
  comm' i j _ := by simp [gradedHomology, zeroDifferential]

theorem cyclesMap_representatives (n : ℕ) :
    cyclesMap (representatives k P) n =
      (gradedHomology k P).iCycles n ≫ cycleSection k P n := by
  apply (cancel_mono (P.iCycles n)).1
  simp [representatives, Category.assoc]

theorem homologyMap_representatives (n : ℕ) :
    homologyMap (representatives k P) n = (zeroHomologyIso k (fun n => P.homology n) n).hom := by
  apply (cancel_epi ((gradedHomology k P).homologyπ n)).1
  rw [homologyπ_naturality, cyclesMap_representatives, Category.assoc,
    cycleSection_π, Category.comp_id, zeroHomologyIso_π]

instance representatives_quasiIso : QuasiIso (representatives k P) := by
  constructor
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, homologyMap_representatives]
  infer_instance

def splitting : HomotopyEquiv (gradedHomology k P) P :=
  Classical.choose ((CochainComplex.quasiIso_iff_of_injective (representatives k P)).mp
    (representatives_quasiIso k P))

@[simp] theorem splitting_hom : (splitting k P).hom = representatives k P :=
  Classical.choose_spec ((CochainComplex.quasiIso_iff_of_injective (representatives k P)).mp
    (representatives_quasiIso k P))

end ArExplicit.VectorCochain

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_SupportedPi
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
universe u v w z
variable {k : Type u} [Field k] {ι : Type v} {κ : Type w}
variable (M : κ → Type z) [∀ j, AddCommGroup (M j)] [∀ j, Module k (M j)]
variable (f : ι → κ)

def supportedRestriction : (∀ j, M j) →ₗ[k] (∀ i, M (f i)) where
  toFun x i := x (f i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_BinaryKoszul
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [CommRing k]

abbrev Piece (n : ℕ) := Fin (n + 1) → k

def mulX (n : ℕ) : Piece k n →ₗ[k] Piece k (n + 1) where
  toFun f := Fin.cons 0 f
  map_add' f g := by ext i; cases i using Fin.cases <;> simp
  map_smul' a f := by ext i; cases i using Fin.cases <;> simp

def mulY (n : ℕ) : Piece k n →ₗ[k] Piece k (n + 1) where
  toFun f := Fin.snoc f 0
  map_add' f g := by ext i; cases i using Fin.lastCases <;> simp
  map_smul' a f := by ext i; cases i using Fin.lastCases <;> simp

@[simp]
theorem mulX_zero (n : ℕ) (f : Piece k n) : mulX k n f 0 = 0 := rfl
@[simp]
theorem mulX_succ (n : ℕ) (f : Piece k n) (i : Fin (n + 1)) :
    mulX k n f i.succ = f i := rfl
@[simp]
theorem mulY_last (n : ℕ) (f : Piece k n) : mulY k n f (Fin.last (n + 1)) = 0 := by
  simp [mulY]
@[simp]
theorem mulY_castSucc (n : ℕ) (f : Piece k n) (i : Fin (n + 1)) :
    mulY k n f i.castSucc = f i := by simp [mulY]

def row (n : ℕ) : Piece k n × Piece k n →ₗ[k] Piece k (n + 1) :=
  (mulX k n).coprod (mulY k n)

def column (n : ℕ) : Piece k n →ₗ[k] Piece k (n + 1) × Piece k (n + 1) :=
  (mulY k n).prod (-(mulX k n))

@[simp]
theorem row_apply (n : ℕ) (u v : Piece k n) : row k n (u, v) = mulX k n u + mulY k n v := rfl

@[simp]
theorem column_apply (n : ℕ) (w : Piece k n) :
    column k n w = (mulY k n w, -(mulX k n w)) := rfl

end ArExplicit.BinaryKoszul

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_BinaryKoszulDual
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [Field k]

abbrev DualPiece (n : ℕ) := Module.Dual k (Piece k n)

def dualRow (n : ℕ) : (DualPiece k (n + 1) × DualPiece k (n + 1)) →ₗ[k] DualPiece k n :=
  (mulX k n).dualMap.coprod (mulY k n).dualMap

def dualColumn (n : ℕ) : DualPiece k (n + 1) →ₗ[k]
    (DualPiece k n × DualPiece k n) :=
  (mulY k n).dualMap.prod (-(mulX k n).dualMap)

@[simp]
theorem dualRow_apply (n : ℕ) (f g : DualPiece k (n + 1)) (x : Piece k n) :
    dualRow k n (f, g) x = f (mulX k n x) + g (mulY k n x) := rfl

@[simp]
theorem dualColumn_apply (n : ℕ) (f : DualPiece k (n + 1)) :
    dualColumn k n f = (f.comp (mulY k n), -(f.comp (mulX k n))) := rfl

end ArExplicit.BinaryKoszul

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_RawSourceDegrees
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
universe u
variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)

abbrev RawCokernelAt := K.X (-n) ⧸ LinearMap.range (K.d (-(n+1)) (-n)).hom

end ArExplicit.CompleteComparison

end

end OAI
end


