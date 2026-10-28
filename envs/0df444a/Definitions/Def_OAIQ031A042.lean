-- Prove2me | Definitions.Def_OAIQ031A042
-- name    : OAIQ031A042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:02:19.861182+00:00
-- url     : https://prove2.me/theorems/634c3e97-3724-4204-98c1-75460223cadb
-- title:
--   Definitions bundle OAIQ031A042 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 3 definitions, 2 instances and 18 theorems. The definitions and types are `OAI.ArExplicit.Triangular.coordinateLinearEquiv`, `OAI.ArExplicit.coneComparison`, `OAI.ArExplicit.fullHomCohomologyEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_ConeCohomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeCohomology.lean), [`AuslanderReiten_Cones_ConeComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeComparison.lean), [`AuslanderReiten_Coordinates_TwoTwistLinear`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TwoTwistLinear.lean), [`AuslanderReiten_HomComplex_FullHomFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomFunctor.lean), [`AuslanderReiten_HomComplex_FullHomMapLinear`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomMapLinear.lean), [`AuslanderReiten_HomComplex_FullHomNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomNaturality.lean), [`AuslanderReiten_Triangular_Triangular`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/Triangular.lean), [`AuslanderReiten_Triangular_TriangularComplete`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularComplete.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A005`, `OAIQ031A006`, `OAIQ031A013`, `OAIQ031A015`, `OAIQ031A017`, `OAIQ031A021`, `OAIQ031A022` and `OAIQ031A023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A058` and `OAIQ031A059`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A005
import Definitions.Def_OAIQ031A006
import Definitions.Def_OAIQ031A013
import Definitions.Def_OAIQ031A015
import Definitions.Def_OAIQ031A017
import Definitions.Def_OAIQ031A021
import Definitions.Def_OAIQ031A022
import Definitions.Def_OAIQ031A023

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeComparison
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
variable {F G : CochainComplex C ℤ} (φ : F ⟶ G) (n : ℤ)

@[simp] theorem coneComparisonCochain_apply (a : Cochain G G n) (b : Cochain F F n) :
    coneComparisonCochain φ n (a, b) = b.comp (Cochain.ofHom φ) (add_zero n) +
      (n + 1).negOnePow • (Cochain.ofHom φ).comp a (zero_add n) := rfl

theorem coneComparison_differential (m : ℤ) (hm : n + 1 = m)
    (x : Cochain G G n × Cochain F F n) :
    coneComparisonCochain φ m (coneDiagonalDifferential n m x) =
      -(δ n m (coneComparisonCochain φ n x)) := by
  subst m
  simp [coneComparisonCochain, coneDiagonalDifferential, Int.negOnePow_succ]
  abel

def coneComparison :
    (CohomologyClass G G n × CohomologyClass F F n) →+ CohomologyClass F G n where
  toFun x := fullHomPostcomp φ n x.2 + (n + 1).negOnePow • fullHomPrecomp φ n x.1
  map_zero' := by simp
  map_add' x y := by simp [smul_add]; abel

theorem coneComparison_mk (a : Cocycle G G n) (b : Cocycle F F n) :
    coneComparison φ n (CohomologyClass.mk a, CohomologyClass.mk b) =
      CohomologyClass.mk (b.postcomp φ + (n + 1).negOnePow • a.precomp φ) := by
  change CohomologyClass.mk (b.postcomp φ) +
      (n + 1).negOnePow • CohomologyClass.mk (a.precomp φ) = _
  rw [CohomologyClass.mk_add]
  congr 1

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeCohomology
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
variable {F G : CochainComplex C ℤ} (φ : F ⟶ G) (n : ℤ)

theorem coneComparison_injective_lift (hinj : Function.Injective (coneComparison φ n))
    (x : Cochain G G n × Cochain F F n)
    (hx : coneDiagonalDifferential n (n + 1) x = 0)
    (hc : ∃ c : Cochain F G (n - 1), coneComparisonCochain φ n x = -(δ (n - 1) n c)) :
    ∃ a : Cochain G G (n - 1) × Cochain F F (n - 1),
      coneDiagonalDifferential (n - 1) n a = x := by
  have hx₁ : δ n (n + 1) x.1 = 0 := congrArg Prod.fst hx
  have hx₂ : δ n (n + 1) x.2 = 0 := neg_eq_zero.mp (congrArg Prod.snd hx)
  let a := Cocycle.mk x.1 (n + 1) rfl hx₁
  let b := Cocycle.mk x.2 (n + 1) rfl hx₂
  have hzero : coneComparison φ n (CohomologyClass.mk a, CohomologyClass.mk b) = 0 := by
    rw [coneComparison_mk, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    obtain ⟨c, hc⟩ := hc
    refine ⟨-c, ?_⟩
    rw [δ_neg]
    exact hc.symm
  have hpair := hinj (hzero.trans (map_zero (coneComparison φ n)).symm)
  have ha : CohomologyClass.mk a = 0 := congrArg Prod.fst hpair
  have hb : CohomologyClass.mk b = 0 := congrArg Prod.snd hpair
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at ha hb
  obtain ⟨a', ha'⟩ := ha
  obtain ⟨b', hb'⟩ := hb
  refine ⟨(a', -b'), ?_⟩
  ext <;> simp [coneDiagonalDifferential, ha', hb', a, b]

theorem coneComparison_surjective_lift (hsurj : Function.Surjective (coneComparison φ n))
    (c : Cochain F G n) (hc : δ n (n + 1) c = 0) :
    ∃ a : Cochain G G n × Cochain F F n,
      coneDiagonalDifferential n (n + 1) a = 0 ∧
      ∃ e : Cochain F G (n - 1), coneComparisonCochain φ n a + δ (n - 1) n e = c := by
  let z := Cocycle.mk c (n + 1) rfl hc
  obtain ⟨⟨a, b⟩, hab⟩ := hsurj (CohomologyClass.mk z)
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective b
  rw [coneComparison_mk, cohomology_eq_iff] at hab
  obtain ⟨e, he⟩ := hab
  refine ⟨(a.1, b.1), ?_, -e, ?_⟩
  · ext <;> simp [coneDiagonalDifferential]
  · rw [δ_neg, ← sub_eq_add_neg]
    rw [he]
    change coneComparisonCochain φ n (a.1, b.1) -
      (coneComparisonCochain φ n (a.1, b.1) - c) = c
    abel

variable [HasHomotopyCofiber φ]

theorem coneEnd_cocycle_is_boundary
    (hzero : ∀ m (x : Cochain G F m), x = 0)
    (hinj : Function.Injective (coneComparison φ n))
    (hsurj : Function.Surjective (coneComparison φ (n - 1)))
    (x : Cocycle (mappingCone φ) (mappingCone φ) n) :
    x ∈ coboundaries (mappingCone φ) (mappingCone φ) n := by
  let a := coneEndA φ x.1
  let b := coneEndB φ x.1
  let c := coneEndC φ x.1
  have hx : coneEnd φ a b c = x.1 := coneEnd_all_reconstruct φ hzero x.1
  have hz : δ n (n + 1) (coneEnd φ a b c) = 0 := by
    rw [hx, Cocycle.δ_eq_zero]
  obtain ⟨ha, hb, hc⟩ := (coneEnd_closed_iff φ a b c).mp hz
  have hdiag : coneDiagonalDifferential n (n + 1) (a, b) = 0 := by
    apply Prod.ext
    · exact ha
    · exact (congrArg Neg.neg hb).trans neg_zero
  have hoff : coneComparisonCochain φ n (a, b) = -(δ (n - 1) n c) := by
    apply eq_neg_iff_add_eq_zero.mpr
    change (b.comp (Cochain.ofHom φ) (add_zero n) +
      (n + 1).negOnePow • (Cochain.ofHom φ).comp a (zero_add n)) + δ (n - 1) n c = 0
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    abel
  obtain ⟨u, e, hu, he⟩ := fiber_cocycle_is_boundary
    (coneDiagonalDifferential (n - 1) n) (coneDiagonalDifferential n (n + 1))
    (-(δ_hom ℤ F G ((n - 1) - 1) (n - 1))) (-(δ_hom ℤ F G (n - 1) n))
    (coneComparisonCochain φ (n - 1)) (coneComparisonCochain φ n)
    (fun u => coneComparison_differential φ (n - 1) n (by omega) u)
    (fun u hu huc => coneComparison_injective_lift φ n hinj u hu huc)
    (by
      intro z hz
      have hz' : δ (n - 1) n z = 0 := neg_eq_zero.mp hz
      have hn : (n - 1) + 1 = n := by omega
      have hz'' : δ (n - 1) ((n - 1) + 1) z = 0 := by
        rw [hn]
        exact hz'
      obtain ⟨v, hv, w, hw⟩ := coneComparison_surjective_lift φ (n - 1) hsurj z hz''
      refine ⟨v, ?_, w, ?_⟩
      · rw [hn] at hv
        exact hv
      · simpa only [LinearMap.neg_apply, δ_hom_apply, sub_neg_eq_add] using hw)
    (a, b) c hdiag hoff
  rw [mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨coneEnd φ u.1 u.2 e, ?_⟩
  rw [← hx]
  change δ (n - 1) n (coneEnd φ u.1 u.2 e) =
    CochainComplex.mappingCone.descCochain φ
      (CochainComplex.mappingCone.liftCochain φ b c (by omega))
      (CochainComplex.mappingCone.liftCochain φ 0 a rfl) (by omega)
  apply (coneEnd_boundary_iff φ (n - 1) (by omega) u.1 u.2 e a b c).mpr
  refine ⟨congrArg Prod.fst hu, congrArg Prod.snd hu, ?_⟩
  have he' : coneComparisonCochain φ (n - 1) u + δ ((n - 1) - 1) (n - 1) e = c := by
    simpa only [LinearMap.neg_apply, δ_hom_apply, sub_neg_eq_add] using he
  change δ ((n - 1) - 1) (n - 1) e +
    u.2.comp (Cochain.ofHom φ) (add_zero (n - 1)) +
    ((n - 1) + 1).negOnePow • (Cochain.ofHom φ).comp u.1 (zero_add (n - 1)) = c
  rw [← he']
  change δ ((n - 1) - 1) (n - 1) e + _ + _ = (_ + _) + _
  abel

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TwoTwistLinear
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem twoTwistLinear_injective (a b : k) (hab : a ≠ b) :
    Function.Injective (twoTwistLinear (V := V) a b) := by
  rintro ⟨x,y⟩ ⟨x',y'⟩ h
  have h₁ : a • x + y = a • x' + y' := congrArg Prod.fst h
  have h₂ : b • x + y = b • x' + y' := congrArg Prod.snd h
  have he : (a-b) • x = (a-b) • x' := by
    rw [sub_smul, sub_smul]
    have ht := congrArg₂ (fun s t : V => s-t) h₁ h₂
    simpa only [add_sub_add_right_eq_sub] using ht
  have hx : x = x' := by
    have ht := congrArg (fun z : V => (a-b)⁻¹ • z) he
    simpa only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab), one_smul] using ht
  subst x'
  exact Prod.ext rfl (add_left_cancel h₁)

theorem twoTwistLinear_surjective (a b : k) (hab : a ≠ b) :
    Function.Surjective (twoTwistLinear (V := V) a b) := by
  rintro ⟨u,v⟩
  let x := (a-b)⁻¹ • (u-v)
  refine ⟨(x,u-a • x), Prod.ext ?_ ?_⟩
  · change a • x + (u-a • x) = u
    abel
  · have hx : (a-b) • x = u-v := by
      simp only [x, smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hab), one_smul]
    rw [sub_smul] at hx
    change b • x + (u-a • x) = v
    calc
      b • x + (u-a • x) = u-(a • x-b • x) := by abel
      _ = u-(u-v) := by rw [hx]
      _ = v := by abel

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomFunctor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable (Φ : C ⥤ D) [Φ.Additive] [Φ.Full] [Φ.Faithful]
variable (K L : CochainComplex C ℤ) (n : ℤ)

theorem fullHomCocycleMap_bijective : Function.Bijective (fullHomCocycleMap Φ K L n) := by
  constructor
  · intro x y h
    apply Cocycle.ext
    apply (fullHomCochainEquiv Φ K L n).injective
    exact congrArg Subtype.val h
  · intro y
    let x := (fullHomCochainEquiv Φ K L n).symm y.1
    have hx : δ n (n + 1) x = 0 := by
      apply (fullHomCochainEquiv Φ K L (n + 1)).injective
      rw [← fullHomCochainEquiv_differential, map_zero]
      change δ n (n + 1) (fullHomCochainEquiv Φ K L n
        ((fullHomCochainEquiv Φ K L n).symm y.1)) = 0
      rw [AddEquiv.apply_symm_apply, Cocycle.δ_eq_zero]
    refine ⟨Cocycle.mk x (n + 1) rfl hx, ?_⟩
    apply Cocycle.ext
    exact (fullHomCochainEquiv Φ K L n).apply_symm_apply y.1

theorem fullHomCohomologyMap_bijective : Function.Bijective (fullHomCohomologyMap Φ K L n) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective x
    exact (CohomologyClass.mk_eq_zero_iff y).mpr
      ((fullHomCocycleMap_boundary Φ K L n y).mp
        ((CohomologyClass.mk_eq_zero_iff _).mp hx))
  · intro y
    obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective y
    obtain ⟨x, rfl⟩ := (fullHomCocycleMap_bijective Φ K L n).surjective y
    exact ⟨CohomologyClass.mk x, rfl⟩

def fullHomCohomologyEquiv : CohomologyClass K L n ≃+
    CohomologyClass ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n :=
  AddEquiv.ofBijective (fullHomCohomologyMap Φ K L n) (fullHomCohomologyMap_bijective Φ K L n)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomMapLinear
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem mapFullHom_smul (a : k) (x : CohomologyClass K L n) :
    mapFullHom Φ K L n (a • x) = a • mapFullHom Φ K L n x := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  rw [← CompleteComparison.fullHom_mk_smul, mapFullHom_mk, mapFullHom_mk,
    ← CompleteComparison.fullHom_mk_smul]
  congr 1
  apply Subtype.ext
  apply Cochain.ext
  intro p q hpq
  exact Φ.map_smul a (x.val.v p q hpq)

theorem mapFullHom_identity :
    mapFullHom Φ K K 0 (CohomologyClass.mk (Cocycle.ofHom (𝟙 K))) =
      CohomologyClass.mk (Cocycle.ofHom (𝟙 ((Φ.mapHomologicalComplex _).obj K))) := by
  rw [mapFullHom_mk]
  congr 1
  apply Subtype.ext
  change (Cochain.ofHom (𝟙 K)).map Φ =
    Cochain.ofHom (𝟙 ((Φ.mapHomologicalComplex _).obj K))
  rw [Cochain.map_ofHom, CategoryTheory.Functor.map_id]

variable {K L n}
theorem fullHomPostcomp_smul (f : K ⟶ L) (n : ℤ) (a : k)
    (x : CohomologyClass K K n) :
    fullHomPostcomp f n (a • x) = a • fullHomPostcomp f n x := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  rw [← CompleteComparison.fullHom_mk_smul, fullHomPostcomp_mk, fullHomPostcomp_mk,
    ← CompleteComparison.fullHom_mk_smul]
  congr 1
  apply Subtype.ext
  exact Cochain.smul_comp a x.val (Cochain.ofHom f) (add_zero n)

theorem fullHomPrecomp_smul (f : K ⟶ L) (n : ℤ) (a : k)
    (x : CohomologyClass L L n) :
    fullHomPrecomp f n (a • x) = a • fullHomPrecomp f n x := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  rw [← CompleteComparison.fullHom_mk_smul, fullHomPrecomp_mk, fullHomPrecomp_mk,
    ← CompleteComparison.fullHom_mk_smul]
  congr 1
  apply Subtype.ext
  exact Cochain.comp_smul (Cochain.ofHom f) a x.val (zero_add n)

theorem fullHomPrecomp_identity (f : K ⟶ L) :
    fullHomPrecomp f 0 (CohomologyClass.mk (Cocycle.ofHom (𝟙 L))) =
      CohomologyClass.mk (Cocycle.ofHom f) := by
  rw [fullHomPrecomp_mk]
  congr 1
  apply Subtype.ext
  exact Cochain.comp_id _

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex CochainComplex.HomComplex
namespace ArExplicit
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable {Φ Ψ : C ⥤ D} [Φ.Additive] [Ψ.Additive]
variable {K L : CochainComplex C ℤ} {n : ℤ}

theorem mapFullHom_naturality (η : Φ ⟶ Ψ) (x : CohomologyClass K L n) :
    fullHomPostcomp ((η.mapHomologicalComplex _).app L) n (mapFullHom Φ K L n x) =
      fullHomPrecomp ((η.mapHomologicalComplex _).app K) n (mapFullHom Ψ K L n x) := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  rw [mapFullHom_mk, mapFullHom_mk, fullHomPostcomp_mk, fullHomPrecomp_mk]
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro i j hij
  change ((x.val.map Φ).comp (Cochain.ofHom ((η.mapHomologicalComplex _).app L))
      (add_zero n)).v i j hij =
    ((Cochain.ofHom ((η.mapHomologicalComplex _).app K)).comp (x.val.map Ψ)
      (zero_add n)).v i j hij
  rw [Cochain.comp_v _ _ (add_zero n) i j j hij (add_zero j),
    Cochain.comp_v _ _ (zero_add n) i i j (add_zero i) hij]
  simp only [Cochain.map_v, Cochain.ofHom_v, NatTrans.mapHomologicalComplex_app_f]
  exact η.naturality (x.val.v i j hij)

variable {F G H I : CochainComplex C ℤ}

theorem fullHomPostcomp_precomp (f : F ⟶ G) (g : H ⟶ I) (x : CohomologyClass G H n) :
    fullHomPostcomp g n (fullHomPrecomp f n x) =
      fullHomPrecomp f n (fullHomPostcomp g n x) := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  simp only [fullHomPostcomp_mk, fullHomPrecomp_mk]
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro i j hij
  change (((Cochain.ofHom f).comp x.val (zero_add n)).comp (Cochain.ofHom g)
      (add_zero n)).v i j hij =
    ((Cochain.ofHom f).comp (x.val.comp (Cochain.ofHom g) (add_zero n))
      (zero_add n)).v i j hij
  rw [Cochain.comp_v _ _ (add_zero n) i j j hij (add_zero j),
    Cochain.comp_v _ _ (zero_add n) i i j (add_zero i) hij,
    Cochain.comp_v _ _ (zero_add n) i i j (add_zero i) hij,
    Cochain.comp_v _ _ (add_zero n) i j j hij (add_zero j)]
  simp only [Cochain.ofHom_v, Category.assoc]

theorem fullHomPrecomp_comp (f : F ⟶ G) (g : G ⟶ H) (x : CohomologyClass H I n) :
    fullHomPrecomp f n (fullHomPrecomp g n x) = fullHomPrecomp (f ≫ g) n x := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  simp only [fullHomPrecomp_mk]
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro i j hij
  change ((Cochain.ofHom f).comp ((Cochain.ofHom g).comp x.val (zero_add n))
      (zero_add n)).v i j hij = ((Cochain.ofHom (f ≫ g)).comp x.val (zero_add n)).v i j hij
  rw [Cochain.comp_v _ _ (zero_add n) i i j (add_zero i) hij,
    Cochain.comp_v _ _ (zero_add n) i i j (add_zero i) hij,
    Cochain.comp_v _ _ (zero_add n) i i j (add_zero i) hij]
  simp only [Cochain.ofHom_v, HomologicalComplex.comp_f, Category.assoc]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_Triangular
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace Triangular

variable {R F : Type*}

variable [Ring R] [AddCommGroup F]
variable [Module R F] [Module Rᵐᵒᵖ F]

variable [SMulCommClass R Rᵐᵒᵖ F]

section Scalars

variable (k : Type*) [CommRing k] [Algebra k R] [Module k F]

variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass k Rᵐᵒᵖ F]

def coordinateLinearEquiv : Triangular R F ≃ₗ[k] (R × R) × F :=
  (coordinateAddEquiv (R := R) (F := F)).linearEquiv k

instance instFinite [Module.Finite k R] [Module.Finite k F] : Module.Finite k (Triangular R F) :=
  Module.Finite.equiv (coordinateLinearEquiv (R := R) (F := F) k).symm

end Scalars

end Triangular
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularComplete
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective
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

instance moduleCatBaseComm (M : ModuleCat.{u} R) : SMulCommClass k R M where
  smul_comm c r m := by
    change (algebraMap k R c) • (r • m) = r • ((algebraMap k R c) • m)
    rw [← mul_smul, Algebra.commutes c r, mul_smul]

end ArExplicit.TriangularInduction

end

end OAI
end


