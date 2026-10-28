-- Prove2me | Definitions.Def_OAIQ66So013
-- name    : OAIQ66So013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:17:49.872843+00:00
-- url     : https://prove2.me/theorems/023af417-2c98-4b78-828f-f034ffcf95a4
-- title:
--   Definitions bundle OAIQ66So013 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 293 declarations of OpenAI's Lean: 99 definitions, 1 inductive type or structure, 3 instances and 190 theorems. The definitions and types are `OAI.FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode.Cmd`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Corner.b`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Corner.coefficient0`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Corner.cornerRetract`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Corner.cornerTensor`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Corner.q`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Corner.q0`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Corner.q1`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Corner.s0`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Corner.s1`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Corner.t0`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Corner.t1`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Data`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Data.act`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Data.eq`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Data.mul`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Data.one`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Data.params`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Data.represent`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.E0`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.E1`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.Eh`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.U`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.UI`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.V`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.VI`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.evaluate`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.generator`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.monoid`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.testedClass`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.value`, `OAI.FiniteAlgebraicEnvelopes.PartialAffine.wordValue`, `OAI.FiniteAlgebraicEnvelopes.WordProblem.testedClass`, `OAI.FiniteAlgebraicEnvelopes.ZeroProduct.nonzeroEquiv`, `OAI.FiniteAlgebraicEnvelopes.ZeroProduct.nonzeroPair`, `OAI.FiniteAlgebraicEnvelopes.ZeroProduct.tensorBasis`, `OAI.FiniteAlgebraicEnvelopes.ZeroProduct.tensorLinearEquiv`, `OAI.FiniteIndexRegular.embedLM`, `OAI.FiniteIndexRegular.slices`, `OAI.FunctionalTree.equivariantComplex` and 60 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `BooneHigman_Contracted`, `BooneHigman_Corners`, `BooneHigman_MonoidAlgebras`, `BooneHigman_PartialAffine`, `BooneHigman_WordProblem`, `FiniteCompiler_Quotients`, `FiniteCompiler_UniformMachines`, `FiniteType_BinaryPrefixOperators`, `FiniteType_FiniteIndexRegular`, `FiniteType_FreeTensor`, `FiniteType_FreeTensorPureMem`, `FiniteType_ListChains`, `FiniteType_ListChainsHasPropagation`, `FiniteType_ListChainsMapChainComp`, `FiniteType_ListChainsShiftOrigin`, `FiniteType_PresentationGeometry`, `FiniteType_PresentationGeometryFiniteStage`, `FiniteType_PresentationGeometryRose`, `FiniteType_ProductCoefficient`, `FiniteType_Representation`, `FiniteType_SequentialColimit`, `FiniteType_SequentialColimitRangeInclMono`, `FiniteType_SphereCover`, `FiniteType_StandardShapiro`, `FiniteType_UniformProductSupport`, `SimpleOvergroups_ContextualCompiler`.
--
--   **Imports.** It imports the bundles `OAIQ66So001`, `OAIQ66So002`, `OAIQ66So003`, `OAIQ66So004`, `OAIQ66So005`, `OAIQ66So006` and `OAIQ66So007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So019`, `OAIQ66So020` and `OAIQ66So021`; the statements `OAI.ListChains.controlled_commuting_additivity` and `OAI.RegularProduct.coset_parent_local_nilpotence`; the proof of `OAI.ListChains.controlled_commuting_additivity`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So001
import Definitions.Def_OAIQ66So002
import Definitions.Def_OAIQ66So003
import Definitions.Def_OAIQ66So004
import Definitions.Def_OAIQ66So005
import Definitions.Def_OAIQ66So006
import Definitions.Def_OAIQ66So007

section
-- module Solutions.OAIQ066_SO.BooneHigman_Contracted
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Contracted.countableAlgebra _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Contracted monoid algebras, selectors, and the simplicity criterion.
-/


namespace FiniteAlgebraicEnvelopes.Contracted
open MonoidAlgebra
open scoped Classical
noncomputable section
variable (k H : Type*) [CommRing k] [MonoidWithZero H]

variable {k H}

section Embedded
variable {J : Type*} [MonoidWithZero J]
variable (c : H →ₙ* J)

/-- Every nonzero coefficient is retained at its distinct new basis element. -/
theorem coefficient_embedding (hc : Function.Injective c) (hz : ∀ h, c h ≠ 0)
    (h : H) (hh : h ≠ 0) (x : Algebra k H) :
    coefficient (c h) (hz h) (embedding (k:=k) c x) = coefficient h hh x := by
  obtain ⟨f,rfl⟩ := (zeroIdeal k H).ringCon.mkₐ_surjective (α:=k) x
  change coefficient (c h) (hz h) (embedding c (quotient k H f)) =
    coefficient h hh (quotient k H f)
  induction f using MonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg => simpa only [map_add] using congrArg₂ (·+·) hf hg
    | single g r =>
      change coefficient (c h) (hz h) (embedding (k:=k) c (basis k H g r)) = coefficient h hh (basis k H g r)
      rw [embedding_basis,map_smul,map_sub,coefficient_basis,coefficient_basis]
      have hne : c h ≠ c 0 := fun he => hh (hc he)
      simp only [ite_eq_right hne,sub_zero,coefficient_basis]
      by_cases he : h=g
      · subst g; simp
      · simp [he,hc.eq_iff]

theorem embedding_injective (hc : Function.Injective c) (hz : ∀ h, c h ≠ 0) :
    Function.Injective (embedding (k:=k) c) := by
  intro x y hxy
  apply coefficient_ext
  intro h hh
  rw [← coefficient_embedding c hc hz h hh,← coefficient_embedding c hc hz h hh,hxy]

end Embedded

end
end FiniteAlgebraicEnvelopes.Contracted


/- Finite weak components and bounded normalization for the finite compiler. -/

end OAI
end

section
-- module Solutions.OAIQ066_SO.BooneHigman_WordProblem
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Effective finite presentations, decidable word problem in simple groups, and the reverse implication.
-/

namespace FiniteAlgebraicEnvelopes

universe u

namespace WordProblem

open Primrec

theorem evalWord_invRev {H : Type*} [Group H] {n} (s : Fin n → H) (w : Word n) :
    evalWord s (FreeGroup.invRev w) = (evalWord s w)⁻¹ := by
  simp only [evalWord_eq_lift, ← FreeGroup.inv_mk, map_inv]

end WordProblem

end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Quotients
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical compiler quotients and effective tested classes for word problems.
-/

namespace FiniteAlgebraicEnvelopes

namespace WordProblem
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)

/-- The original word-problem algorithm gives a genuine two-word comparison. -/
theorem computable_word_equiv (h : ComputablePred (fun w : Word n => evalWord s w=1)) :
    ComputablePred (fun p : Word n × Word n => evalWord s p.1=evalWord s p.2) := by
  classical
  have hc : ComputablePred (fun p : Word n × Word n =>
      evalWord s (p.1 ++ FreeGroup.invRev p.2)=1) :=
    ⟨inferInstance,h.decide.comp (Primrec.list_append.comp Primrec.fst
      ((invRev_primrec n).comp Primrec.snd)).to_comp⟩
  exact hc.of_eq (fun p => by rw [evalWord_append,evalWord_invRev,mul_inv_eq_one])

end WordProblem
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.WordProblem

local instance instDecidableRelProdFinBoolLetterRel_rededfd_1 (n : ℕ) : DecidableRel (letterRel n) := fun _ _ => inferInstanceAs (Decidable (_ < _))
local instance instTrichotomousProdFinBoolLetterRel (n : ℕ) : Std.Trichotomous (letterRel n) := ⟨fun a b hab hba => by
  apply Encodable.encode_injective
  change ¬Encodable.encode a<Encodable.encode b at hab
  change ¬Encodable.encode b<Encodable.encode a at hba
  omega⟩

 theorem letterRel_wf (n : ℕ) : WellFounded (letterRel n) := InvImage.wf Encodable.encode Nat.lt_wfRel.wf

variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
noncomputable def testedClass : Word n → Word n :=
  Bootstrap.Canonical.least (letterRel_wf n) (evalWord s)

 theorem testedClass_eq_iff (u v : Word n) : testedClass s u=testedClass s v ↔ evalWord s u=evalWord s v := by
  classical
  exact Bootstrap.Canonical.least_eq_iff _ _

end FiniteAlgebraicEnvelopes.WordProblem

end OAI
end

section
-- module Solutions.OAIQ066_SO.BooneHigman_PartialAffine
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Primitive recursive dyadic partial affine monoid and its six-letter presentation.
-/

namespace FiniteAlgebraicEnvelopes.PartialAffine
namespace Dyad

theorem primrec_add : Primrec₂ add := by
  have ap : Primrec (fun p : Dyad × Dyad => p.1.1) := Primrec.fst.comp Primrec.fst
  have an : Primrec (fun p : Dyad × Dyad => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ak : Primrec (fun p : Dyad × Dyad => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bp : Primrec (fun p : Dyad × Dyad => p.2.1) := Primrec.fst.comp Primrec.snd
  have bn : Primrec (fun p : Dyad × Dyad => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have bk : Primrec (fun p : Dyad × Dyad => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp ap (primrec_pow2.comp bk))
    (Primrec.nat_mul.comp bp (primrec_pow2.comp ak))).pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp an (primrec_pow2.comp bk))
      (Primrec.nat_mul.comp bn (primrec_pow2.comp ak))).pair
        (Primrec.nat_add.comp ak bk))).to₂

theorem primrec_mul : Primrec₂ mul := by
  have ap : Primrec (fun p : Dyad × Dyad => p.1.1) := Primrec.fst.comp Primrec.fst
  have an : Primrec (fun p : Dyad × Dyad => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ak : Primrec (fun p : Dyad × Dyad => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bp : Primrec (fun p : Dyad × Dyad => p.2.1) := Primrec.fst.comp Primrec.snd
  have bn : Primrec (fun p : Dyad × Dyad => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have bk : Primrec (fun p : Dyad × Dyad => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp ap bp) (Primrec.nat_mul.comp an bn)).pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp ap bn) (Primrec.nat_mul.comp an bp)).pair
      (Primrec.nat_add.comp ak bk))).to₂

theorem primrec_le : Primrec₂ le := by
  have ap : Primrec (fun p : Dyad × Dyad => p.1.1) := Primrec.fst.comp Primrec.fst
  have an : Primrec (fun p : Dyad × Dyad => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ak : Primrec (fun p : Dyad × Dyad => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bp : Primrec (fun p : Dyad × Dyad => p.2.1) := Primrec.fst.comp Primrec.snd
  have bn : Primrec (fun p : Dyad × Dyad => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have bk : Primrec (fun p : Dyad × Dyad => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((Primrec.nat_le.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp ap (primrec_pow2.comp bk))
      (Primrec.nat_mul.comp bn (primrec_pow2.comp ak)))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp bp (primrec_pow2.comp ak))
      (Primrec.nat_mul.comp an (primrec_pow2.comp bk)))).decide).to₂

theorem primrec_eq : Primrec₂ eq :=
  (Primrec.and.comp (primrec_le.comp Primrec.fst Primrec.snd)
    (primrec_le.comp Primrec.snd Primrec.fst)).to₂

theorem primrec_max : Primrec₂ max :=
  (Primrec.ite (Primrec.eq.comp primrec_le (Primrec.const true)) Primrec.snd Primrec.fst).to₂

end Dyad

namespace Slope
theorem primrec_mul : Primrec₂ mul :=
  ((Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂
end Slope

namespace Bound

theorem primrec_sup : Primrec₂ sup := by
  have hh : Primrec (fun p : Option Dyad × Option Dyad =>
      (Option.casesOn p.1 p.2 (fun a => Option.casesOn p.2 (some a) (fun b => some (Dyad.max a b))) : Option Dyad)) := by
    apply Primrec.option_casesOn Primrec.fst Primrec.snd
    exact (Primrec.option_casesOn (Primrec.snd.comp Primrec.fst)
      (Primrec.option_some.comp Primrec.snd)
      (Primrec.option_some.comp (Dyad.primrec_max.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂).to₂
  exact hh.of_eq (by intro p; rcases p with ⟨a,b⟩; cases a <;> cases b <;> rfl)
end Bound

abbrev Data := Slope × Dyad × Option Dyad
namespace Data
def mul (a b : Data) : Data :=
  (Slope.mul a.1 b.1, Dyad.add (Dyad.mul (Slope.dyad a.1) b.2.1) a.2.1,
    Bound.sup b.2.2 (a.2.2.map fun r =>
      Dyad.mul (Slope.dyad (Slope.inv b.1)) (Dyad.add r (Dyad.neg b.2.1))))
def one : Data := ((0,0),Dyad.zero,none)
def act (a : Data) (x : ℚ) : Option ℚ :=
  if Bound.dom (a.2.2.map Dyad.val) x then some (Slope.val a.1*x+Dyad.val a.2.1) else none

def represent (a : Data) : Function.End (Option ℚ) := fun o => o.bind (act a)

 theorem act_mul (a b : Data) (x : ℚ) : act (mul a b) x = (act b x).bind (act a) := by
  have hd : Bound.dom ((mul a b).2.2.map Dyad.val) x ↔
      Bound.dom (b.2.2.map Dyad.val) x ∧
      Bound.dom (a.2.2.map Dyad.val) (Slope.val b.1*x+Dyad.val b.2.1) := by
    rw [mul,Bound.dom_sup,Bound.dom_preimage]
  simp only [act,hd]
  split_ifs <;> simp_all only [Option.bind_some,Option.bind_none,act,↓reduceIte,
    and_true,true_and,false_and,not_false_eq_true]
  change some (Slope.val (Slope.mul a.1 b.1)*x+
    Dyad.val (Dyad.add (Dyad.mul (Slope.dyad a.1) b.2.1) a.2.1)) = _
  rw [Slope.val_mul,Dyad.val_add,Dyad.val_mul]
  change some (Slope.val a.1*Slope.val b.1*x+(Slope.val a.1*Dyad.val b.2.1+Dyad.val a.2.1)) = _
  congr 1
  ring

 theorem represent_mul (a b : Data) : represent (mul a b)=represent a*represent b := by
  funext o
  cases o with
  | none => rfl
  | some x => exact act_mul a b x

 theorem represent_one : represent one=1 := by
  funext o
  change represent one o = o
  cases o <;> simp [represent,act,one,Bound.dom,Slope.val_eq,Dyad.val_zero]

/-- The three literal parameters determine exactly a partial affine map. -/
def params (a : Data) : ℚ × ℚ × Option ℚ :=
  (Slope.val a.1,Dyad.val a.2.1,a.2.2.map Dyad.val)

 theorem represent_of_params {a b : Data} (h : params a=params b) : represent a=represent b := by
  have hs := congrArg Prod.fst h
  have ht := congrArg (fun p : ℚ × ℚ × Option ℚ => p.2.1) h
  have hd := congrArg (fun p : ℚ × ℚ × Option ℚ => p.2.2) h
  funext o
  cases o <;> simp_all [params,represent,act]

theorem domain_eq {a b : Data} (h : represent a=represent b) (x : ℚ) :
    Bound.dom (a.2.2.map Dyad.val) x ↔ Bound.dom (b.2.2.map Dyad.val) x := by
  have hh := congrFun h (some x)
  simp only [represent,Option.bind_some,act] at hh
  split_ifs at hh <;> simp_all

 theorem params_of_represent {a b : Data} (h : represent a=represent b) : params a=params b := by
  have hd : a.2.2.map Dyad.val=b.2.2.map Dyad.val := by
    cases ha : a.2.2.map Dyad.val with
    | none =>
      cases hb : b.2.2.map Dyad.val with
      | none => rfl
      | some s =>
        have hh := (domain_eq h (s-1)).mp (by simp [ha,Bound.dom])
        simp only [hb,Bound.dom] at hh
        linarith
    | some r =>
      cases hb : b.2.2.map Dyad.val with
      | none =>
        have hh := (domain_eq h (r-1)).mpr (by simp [hb,Bound.dom])
        simp only [ha,Bound.dom] at hh
        linarith
      | some s =>
        apply congrArg some
        apply le_antisymm
        · have hh := (domain_eq h s).mpr (by simp [hb,Bound.dom])
          simpa only [ha,Bound.dom] using hh
        · have hh := (domain_eq h r).mp (by simp [ha,Bound.dom])
          simpa only [hb,Bound.dom] using hh
  let x : ℚ := (a.2.2.map Dyad.val).getD 0
  have hx : Bound.dom (a.2.2.map Dyad.val) x := by
    cases ha : a.2.2.map Dyad.val <;> simp [x,ha,Bound.dom]
  have hx' : Bound.dom (a.2.2.map Dyad.val) (x+1) := by
    cases ha : a.2.2.map Dyad.val <;> simp [x,ha,Bound.dom]
  have hv (y : ℚ) (hy : Bound.dom (a.2.2.map Dyad.val) y) :
      Slope.val a.1*y+Dyad.val a.2.1=Slope.val b.1*y+Dyad.val b.2.1 := by
    have hh := congrFun h (some y)
    simp only [represent,Option.bind_some,act,ite_eq_left hy,ite_eq_left ((domain_eq h y).mp hy),Option.some.injEq] at hh
    exact hh
  have h0 := hv x hx
  have h1 := hv (x+1) hx'
  have hs : Slope.val a.1=Slope.val b.1 := by nlinarith
  have ht : Dyad.val a.2.1=Dyad.val b.2.1 := by rw [hs] at h0; linarith
  exact Prod.ext hs (Prod.ext ht hd)

 theorem represent_eq_iff (a b : Data) : represent a=represent b ↔ params a=params b :=
  ⟨params_of_represent,represent_of_params⟩

end Data

namespace Bound

 theorem primrec_eq : Primrec₂ eq := by
  have hh : Primrec (fun p : Option Dyad × Option Dyad =>
      (Option.casesOn p.1 (Option.casesOn p.2 true (fun _ => false))
        (fun a => Option.casesOn p.2 false (fun b => Dyad.eq a b)) : Bool)) := by
    apply Primrec.option_casesOn Primrec.fst
    · exact Primrec.option_casesOn Primrec.snd (Primrec.const true) (Primrec.const false).to₂
    · exact (Primrec.option_casesOn (Primrec.snd.comp Primrec.fst) (Primrec.const false)
        (Dyad.primrec_eq.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact hh.of_eq (by intro p; rcases p with ⟨a,b⟩; cases a <;> cases b <;> rfl)

 theorem primrec_preimage {X : Type*} [Primcodable X]
    {r : X → Option Dyad} {c : X → Slope} {d : X → Dyad}
    (hr : Primrec r) (hc : Primrec c) (hd : Primrec d) :
    Primrec (fun x => (r x).map fun b =>
      Dyad.mul (Slope.dyad (Slope.inv (c x))) (Dyad.add b (Dyad.neg (d x)))) :=
  Primrec.option_map hr
    ((Dyad.primrec_mul.comp (Slope.primrec_dyad.comp (Slope.primrec_inv.comp (hc.comp Primrec.fst)))
      (Dyad.primrec_add.comp Primrec.snd (Dyad.primrec_neg.comp (hd.comp Primrec.fst)))).to₂)
end Bound

namespace Data
def eq (a b : Data) : Bool :=
  Dyad.eq (Slope.dyad a.1) (Slope.dyad b.1) &&
    Dyad.eq a.2.1 b.2.1 && Bound.eq a.2.2 b.2.2

 theorem eq_correct (a b : Data) : eq a b=true ↔ represent a=represent b := by
  rw [represent_eq_iff]
  simp only [eq,Bool.and_eq_true,Dyad.eq_correct,Bound.eq_correct,params,Prod.mk.injEq]
  change ((Slope.val a.1=Slope.val b.1) ∧ (Dyad.val a.2.1=Dyad.val b.2.1)) ∧ _ ↔ _
  exact and_assoc

 theorem primrec_mul : Primrec₂ mul := by
  have ac : Primrec (fun p : Data × Data => p.1.1) := Primrec.fst.comp Primrec.fst
  have ad : Primrec (fun p : Data × Data => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ar : Primrec (fun p : Data × Data => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bc : Primrec (fun p : Data × Data => p.2.1) := Primrec.fst.comp Primrec.snd
  have bd : Primrec (fun p : Data × Data => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have br : Primrec (fun p : Data × Data => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((Slope.primrec_mul.comp ac bc).pair
    ((Dyad.primrec_add.comp (Dyad.primrec_mul.comp (Slope.primrec_dyad.comp ac) bd) ad).pair
      (Bound.primrec_sup.comp br (Bound.primrec_preimage ar bc bd)))).to₂

 theorem primrec_eq : Primrec₂ eq := by
  exact (Primrec.and.comp
    (Primrec.and.comp
      (Dyad.primrec_eq.comp (Slope.primrec_dyad.comp (Primrec.fst.comp Primrec.fst))
        (Slope.primrec_dyad.comp (Primrec.fst.comp Primrec.snd)))
      (Dyad.primrec_eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
    (Bound.primrec_eq.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂
end Data

def generator (i : Letter) : Data :=
  if i=0 then ((0,1),Dyad.zero,none)
  else if i=1 then ((0,1),(1,0,1),none)
  else if i=2 then ((1,0),Dyad.zero,none)
  else if i=3 then ((1,0),(0,1,0),none)
  else if i=4 then ((0,0),Dyad.zero,some Dyad.zero)
  else ((0,0),Dyad.zero,some Dyad.one)

def evaluate (w : List Letter) : Data := w.foldr (fun i d => Data.mul (generator i) d) Data.one

def value (w : List Letter) : Function.End (Option ℚ) := (w.map (Data.represent ∘ generator)).prod

 theorem represent_evaluate (w : List Letter) : Data.represent (evaluate w)=value w := by
  induction w with
  | nil => exact Data.represent_one
  | cons i w ih =>
    simpa only [evaluate,List.foldr_cons,value,List.map_cons,List.prod_cons,Function.comp_apply]
      using (Data.represent_mul (generator i) (evaluate w)).trans (congrArg (Data.represent (generator i)*·) ih)

 theorem primrec_evaluate : Primrec evaluate :=
  Primrec.list_foldr Primrec.id (Primrec.const Data.one)
    (Data.primrec_mul.comp ((Primrec.dom_finite generator).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

/-- Lemma partial-affine, algorithmic part: a primitive-recursive equality test
    for the actual partial maps, not classical decidability. -/
 theorem primrec_word_equivalence : PrimrecPred (fun p : List Letter × List Letter => value p.1=value p.2) := by
  have hh : PrimrecPred (fun p : List Letter × List Letter => Data.eq (evaluate p.1) (evaluate p.2)=true) :=
    Primrec.eq.comp (Data.primrec_eq.comp (primrec_evaluate.comp Primrec.fst)
      (primrec_evaluate.comp Primrec.snd)) (Primrec.const true)
  exact hh.of_eq fun p => by rw [Data.eq_correct,represent_evaluate,represent_evaluate]

/-- A computable, uniquely comparable coding of the tested class for the
    auxiliary monoid. No rational-number coding is used as an oracle. -/
noncomputable def testedClass : List Letter → List Letter :=
  Bootstrap.Canonical.least (r:=fun a b : Letter => a<b) wellFounded_lt value

 theorem testedClass_eq_iff (u v : List Letter) : testedClass u=testedClass v ↔ value u=value v := by
  classical
  exact Bootstrap.Canonical.least_eq_iff _ _

/-- The manuscript's auxiliary monoid is generated by the six actual partial
    affine maps. `none` is an undefined value; composition is right first. -/
def monoid : Submonoid (Function.End (Option ℚ)) :=
  Submonoid.closure (Set.range (Data.represent ∘ generator))

 theorem value_mem (w : List Letter) : value w∈monoid := by
  apply Submonoid.list_prod_mem
  intro a ha
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  exact Submonoid.subset_closure ⟨i,rfl⟩

 theorem exists_word {a : Function.End (Option ℚ)} (ha : a∈monoid) : ∃ w,value w=a := by
  induction ha using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    exact ⟨[i],by simp [value]⟩
  | one => exact ⟨[],rfl⟩
  | mul a b ha hb ia ib =>
    obtain ⟨u,rfl⟩ := ia
    obtain ⟨v,rfl⟩ := ib
    exact ⟨u++v,by simp [value]⟩

def wordValue (w : List Letter) : monoid := ⟨value w,value_mem w⟩

 theorem wordValue_surjective : Function.Surjective wordValue := by
  intro a
  obtain ⟨w,hw⟩ := exists_word a.property
  exact ⟨w,Subtype.ext hw⟩

instance instFGSubtypeEndOptionRatMemSubmonoidMonoid : Monoid.FG monoid := by
  unfold monoid
  infer_instance

instance instCountableSubtypeEndOptionRatMemSubmonoidMonoid : Countable monoid := Function.Surjective.countable wordValue_surjective

 theorem generator_tail0 : Data.represent (generator 4)=tail 0 := by
  funext o
  cases o <;> simp [Data.represent,Data.act,generator,tail,Bound.dom,Slope.val_eq,Dyad.val_zero]

 theorem generator_tail1 : Data.represent (generator 5)=tail 1 := by
  funext o
  cases o <;> simp [Data.represent,Data.act,generator,tail,Bound.dom,Slope.val_eq,Dyad.val_zero,Dyad.val_one]

 theorem generator_u (o : Option ℚ) : Data.represent (generator 0) o=o.map (fun x => x/2) := by
  cases o <;> simp [Data.represent,Data.act,generator,Bound.dom,Slope.val_eq,Dyad.val_zero,
    div_eq_mul_inv,mul_comm]

 theorem generator_v (o : Option ℚ) : Data.represent (generator 1) o=o.map (fun x => (x+1)/2) := by
  cases o <;> simp [Data.represent,Data.act,generator,Bound.dom,Slope.val_eq,Dyad.val]
  ring

 theorem generator_ui (o : Option ℚ) : Data.represent (generator 2) o=o.map (fun x => 2*x) := by
  cases o <;> simp [Data.represent,Data.act,generator,Bound.dom,Slope.val_eq,Dyad.val_zero]

 theorem generator_vi (o : Option ℚ) : Data.represent (generator 3) o=o.map (fun x => 2*x-1) := by
  cases o <;> simp [Data.represent,Data.act,generator,Bound.dom,Slope.val_eq,Dyad.val]
  ring

end FiniteAlgebraicEnvelopes.PartialAffine

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_UniformMachines
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Parameterized effective machine realization and uniform finite data.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode
open Compiler.Simulator ParameterMachine
variable {S Γ Q : Type*}

abbrev Cmd (Q Γ : Type*) := Control Q × ((Bool×Γ) × Move)

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

end OAI
end

section
-- module Solutions.OAIQ066_SO.BooneHigman_MonoidAlgebras
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Contracted.countableAlgebra _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite compiler monoids, zero products, both F₂ algebras, and selector constructions.
-/

namespace FiniteAlgebraicEnvelopes.ZeroProduct
open scoped TensorProduct
open Contracted
variable (k K P : Type*) [CommRing k] [MonoidWithZero K] [Monoid P]

def nonzeroPair (a : {a : K // a≠0} × P) : {t : Mon K P // t≠0} :=
  ⟨pair K P (a.1,a.2),fun he => a.1.property ((pair_eq_zero K P _).mp he)⟩

theorem nonzeroPair_bijective : Function.Bijective (nonzeroPair K P) := by
  constructor
  · rintro ⟨⟨a,ha⟩,p⟩ ⟨⟨b,hb⟩,q⟩ he
    have hh := (pair_eq_iff K P _ _).mp (congrArg Subtype.val he)
    rcases hh with hh | hh
    · exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (congrArg (fun t : K×P => t.2) hh)
    · exact (ha hh.1).elim
  · rintro ⟨t,ht⟩
    obtain ⟨⟨a,p⟩,rfl⟩ := pair_surjective K P t
    have ha : a≠0 := fun he => ht ((pair_eq_zero K P _).mpr he)
    exact ⟨(⟨a,ha⟩,p),rfl⟩

def nonzeroEquiv : ({a : K // a≠0} × P) ≃ {t : Mon K P // t≠0} :=
  Equiv.ofBijective (nonzeroPair K P) (nonzeroPair_bijective K P)

def tensorBasis := (monoidBasis (k:=k) (H:=K)).tensorProduct (MonoidAlgebra.basis P k)

def tensorLinearEquiv : Contracted.Algebra k K ⊗[k] MonoidAlgebra k P ≃ₗ[k] Contracted.Algebra k (Mon K P) :=
  (tensorBasis k K P).equiv (monoidBasis (k:=k) (H:=Mon K P)) (nonzeroEquiv K P)

theorem tensorMap_linear : (tensorMap k K P).toLinearMap=(tensorLinearEquiv k K P).toLinearMap := by
  apply (tensorBasis k K P).ext
  rintro ⟨a,p⟩
  change tensorMap k K P ((tensorBasis k K P) (a,p))=tensorLinearEquiv k K P ((tensorBasis k K P) (a,p))
  rw [tensorLinearEquiv,Module.Basis.equiv_apply]
  simp only [tensorBasis,Module.Basis.tensorProduct_apply,monoidBasis_apply]
  change tensorMap k K P (basis k K a 1 ⊗ₜ[k] MonoidAlgebra.single p 1)=_
  rw [tensorMap_basis,one_mul]
  rfl

theorem tensorMap_bijective : Function.Bijective (tensorMap k K P) := by
  change Function.Bijective (tensorMap k K P).toLinearMap
  rw [tensorMap_linear]
  exact (tensorLinearEquiv k K P).bijective

end FiniteAlgebraicEnvelopes.ZeroProduct

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.BooneHigman_Corners
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Tensor embeddings and the nonunital corner maps between the two algebras.
-/

namespace FiniteAlgebraicEnvelopes.PartialAffine

def U : monoid := wordValue [0]
def V : monoid := wordValue [1]
def UI : monoid := wordValue [2]
def VI : monoid := wordValue [3]
def E0 : monoid := wordValue [4]
def E1 : monoid := wordValue [5]
def Eh : monoid := U*E1*UI

@[simp] theorem U_apply (o : Option ℚ) : U.val o=o.map (fun x => x/2) := by
  simpa [U,wordValue,value] using generator_u o
@[simp] theorem V_apply (o : Option ℚ) : V.val o=o.map (fun x => (x+1)/2) := by
  simpa [V,wordValue,value] using generator_v o
@[simp] theorem UI_apply (o : Option ℚ) : UI.val o=o.map (fun x => 2*x) := by
  simpa [UI,wordValue,value] using generator_ui o
@[simp] theorem VI_apply (o : Option ℚ) : VI.val o=o.map (fun x => 2*x-1) := by
  simpa [VI,wordValue,value] using generator_vi o
@[simp] theorem E0_val : E0.val=tail 0 := by
  simpa [E0,wordValue,value] using generator_tail0
@[simp] theorem E1_val : E1.val=tail 1 := by
  simpa [E1,wordValue,value] using generator_tail1

@[simp] theorem U_UI : U*UI=1 := by
  apply Subtype.ext
  funext o
  change U.val (UI.val o)=o
  cases o <;> simp
@[simp] theorem UI_U : UI*U=1 := by
  apply Subtype.ext
  funext o
  change UI.val (U.val o)=o
  cases o <;> simp
  ring
@[simp] theorem V_VI : V*VI=1 := by
  apply Subtype.ext
  funext o
  change V.val (VI.val o)=o
  cases o <;> simp
@[simp] theorem VI_V : VI*V=1 := by
  apply Subtype.ext
  funext o
  change VI.val (V.val o)=o
  cases o <;> simp
  ring

theorem U_tail (r : ℚ) : U.val*tail r*UI.val=tail (r/2) := by
  funext o
  cases o with
  | none =>
    change U.val ((tail r) (UI.val none))=none
    simp [tail]
  | some x =>
    change U.val ((tail r) (UI.val (some x)))=(tail (r/2)) (some x)
    simp only [UI_apply,Option.map_some,tail,Option.bind_some]
    by_cases hr : r≤2*x
    · have hr' : r/2≤x := by linarith
      simp [hr,hr']
    · have hr' : ¬r/2≤x := by linarith
      simp [hr,hr']

theorem V_tail (r : ℚ) : V.val*tail r*VI.val=tail ((r+1)/2) := by
  funext o
  cases o with
  | none =>
    change V.val ((tail r) (VI.val none))=none
    simp [tail]
  | some x =>
    change V.val ((tail r) (VI.val (some x)))=(tail ((r+1)/2)) (some x)
    simp only [VI_apply,Option.map_some,tail,Option.bind_some]
    by_cases hr : r≤2*x-1
    · have hr' : (r+1)/2≤x := by linarith
      simp [hr,hr']
    · have hr' : ¬(r+1)/2≤x := by linarith
      simp [hr,hr']

@[simp] theorem Eh_val : Eh.val=tail (1/2) := by
  exact (congrArg (fun e => U.val*e*UI.val) E1_val).trans (U_tail 1)

@[simp] theorem U_E0_UI : U*E0*UI=E0 := by
  apply Subtype.ext
  change U.val*E0.val*UI.val=E0.val
  rw [E0_val,U_tail]
  norm_num
@[simp] theorem U_E1_UI : U*E1*UI=Eh := rfl
@[simp] theorem V_E0_VI : V*E0*VI=Eh := by
  apply Subtype.ext
  change V.val*E0.val*VI.val=Eh.val
  rw [E0_val,Eh_val,V_tail]
  norm_num
@[simp] theorem V_E1_VI : V*E1*VI=E1 := by
  apply Subtype.ext
  change V.val*E1.val*VI.val=E1.val
  rw [E1_val,V_tail]
  norm_num

 theorem tails_mul {a b c : monoid} {r s : ℚ} (ha : a.val=tail r) (hb : b.val=tail s)
    (hc : c.val=tail (max r s)) : a*b=c := by
  apply Subtype.ext
  change a.val*b.val=c.val
  rw [ha,hb,hc,tail_mul]

@[simp] theorem E0_E0 : E0*E0=E0 := tails_mul E0_val E0_val (by simp)
@[simp] theorem E0_Eh : E0*Eh=Eh := tails_mul E0_val Eh_val (by norm_num)
@[simp] theorem E0_E1 : E0*E1=E1 := tails_mul E0_val E1_val (by norm_num)
@[simp] theorem Eh_E0 : Eh*E0=Eh := tails_mul Eh_val E0_val (by norm_num)
@[simp] theorem Eh_Eh : Eh*Eh=Eh := tails_mul Eh_val Eh_val (by simp)
@[simp] theorem Eh_E1 : Eh*E1=E1 := tails_mul Eh_val E1_val (by norm_num)
@[simp] theorem E1_E0 : E1*E0=E1 := tails_mul E1_val E0_val (by norm_num)
@[simp] theorem E1_Eh : E1*Eh=E1 := tails_mul E1_val Eh_val (by norm_num)
@[simp] theorem E1_E1 : E1*E1=E1 := tails_mul E1_val E1_val (by simp)

 theorem E0_ne_E1 : E0≠E1 := by
  intro h
  have hh := congrArg Subtype.val h
  rw [E0_val,E1_val] at hh
  have := tail_injective hh
  norm_num at this

end FiniteAlgebraicEnvelopes.PartialAffine

namespace FiniteAlgebraicEnvelopes.PartialAffine.Corner
open MonoidAlgebra
variable (k : Type*) [CommRing k]

def b (a : monoid) : MonoidAlgebra k monoid := single a 1
@[simp] theorem b_mul (a c : monoid) : b k a*b k c=b k (a*c) := by simp [b,single_mul_single]
@[simp] theorem b_one : b k 1=1 := rfl

def q : MonoidAlgebra k monoid := b k E0-b k E1
def q0 : MonoidAlgebra k monoid := b k E0-b k Eh
def q1 : MonoidAlgebra k monoid := b k Eh-b k E1

theorem q_idem : q k*q k=q k := by
  simp only [q,sub_mul,mul_sub,b_mul,E0_E0,E0_E1,E1_E0,E1_E1]
  abel
 theorem q0_idem : q0 k*q0 k=q0 k := by
  simp only [q0,sub_mul,mul_sub,b_mul,E0_E0,E0_Eh,Eh_E0,Eh_Eh]
  abel
 theorem q1_idem : q1 k*q1 k=q1 k := by
  simp only [q1,sub_mul,mul_sub,b_mul,Eh_Eh,Eh_E1,E1_Eh,E1_E1]
  abel
 theorem q0_q1 : q0 k*q1 k=0 := by
  simp only [q0,q1,sub_mul,mul_sub,b_mul,E0_Eh,E0_E1,Eh_Eh,Eh_E1]
  abel
 theorem q1_q0 : q1 k*q0 k=0 := by
  simp only [q0,q1,sub_mul,mul_sub,b_mul,Eh_E0,Eh_Eh,E1_E0,E1_Eh]
  abel
 theorem q0_add_q1 : q0 k+q1 k=q k := by unfold q0 q1 q; abel
 theorem q_q0 : q k*q0 k=q0 k := by rw [←q0_add_q1,add_mul,q0_idem,q1_q0,add_zero]
 theorem q0_q : q0 k*q k=q0 k := by rw [←q0_add_q1,mul_add,q0_idem,q0_q1,add_zero]
 theorem q_q1 : q k*q1 k=q1 k := by rw [←q0_add_q1,add_mul,q0_q1,q1_idem,zero_add]
 theorem q1_q : q1 k*q k=q1 k := by rw [←q0_add_q1,mul_add,q1_q0,q1_idem,zero_add]

def s0 : MonoidAlgebra k monoid := b k U*q k
def s1 : MonoidAlgebra k monoid := b k V*q k
def t0 : MonoidAlgebra k monoid := q k*b k UI
def t1 : MonoidAlgebra k monoid := q k*b k VI

 theorem conjugate0 : b k U*q k*b k UI=q0 k := by
  simp only [q,q0,mul_sub,sub_mul,b_mul,U_E0_UI,U_E1_UI]
 theorem conjugate1 : b k V*q k*b k VI=q1 k := by
  simp only [q,q1,mul_sub,sub_mul,b_mul,V_E0_VI,V_E1_VI]

 theorem t0_s0 : t0 k*s0 k=q k := by
  unfold t0 s0
  calc
    _=q k*(b k UI*b k U)*q k := by simp only [mul_assoc]
    _=q k := by rw [b_mul,UI_U,b_one,mul_one,q_idem]
 theorem t1_s1 : t1 k*s1 k=q k := by
  unfold t1 s1
  calc
    _=q k*(b k VI*b k V)*q k := by simp only [mul_assoc]
    _=q k := by rw [b_mul,VI_V,b_one,mul_one,q_idem]
 theorem s0_t0 : s0 k*t0 k=q0 k := by
  unfold s0 t0
  rw [mul_assoc,←mul_assoc (q k),q_idem,←mul_assoc,conjugate0]
 theorem s1_t1 : s1 k*t1 k=q1 k := by
  unfold s1 t1
  rw [mul_assoc,←mul_assoc (q k),q_idem,←mul_assoc,conjugate1]

 theorem s0_q : s0 k*q k=s0 k := by unfold s0; rw [mul_assoc,q_idem]
 theorem s1_q : s1 k*q k=s1 k := by unfold s1; rw [mul_assoc,q_idem]
 theorem q_t0 : q k*t0 k=t0 k := by unfold t0; rw [←mul_assoc,q_idem]
 theorem q_t1 : q k*t1 k=t1 k := by unfold t1; rw [←mul_assoc,q_idem]
 theorem q0_s0 : q0 k*s0 k=s0 k := by rw [←s0_t0,mul_assoc,t0_s0,s0_q]
 theorem q1_s1 : q1 k*s1 k=s1 k := by rw [←s1_t1,mul_assoc,t1_s1,s1_q]
 theorem t0_q0 : t0 k*q0 k=t0 k := by rw [←s0_t0,←mul_assoc,t0_s0,q_t0]
 theorem t1_q1 : t1 k*q1 k=t1 k := by rw [←s1_t1,←mul_assoc,t1_s1,q_t1]
 theorem q_s0 : q k*s0 k=s0 k := by nth_rw 1 [←q0_s0 k]; rw [←mul_assoc,q_q0,q0_s0]
 theorem q_s1 : q k*s1 k=s1 k := by nth_rw 1 [←q1_s1 k]; rw [←mul_assoc,q_q1,q1_s1]
 theorem t0_q : t0 k*q k=t0 k := by nth_rw 1 [←t0_q0 k]; rw [mul_assoc,q0_q,t0_q0]
 theorem t1_q : t1 k*q k=t1 k := by nth_rw 1 [←t1_q1 k]; rw [mul_assoc,q1_q,t1_q1]
 theorem t0_s1 : t0 k*s1 k=0 := by
  nth_rw 1 [←t0_q0 k,←q1_s1 k]
  calc
    _=t0 k*(q0 k*q1 k)*s1 k := by simp only [mul_assoc]
    _=0 := by rw [q0_q1,mul_zero,zero_mul]
 theorem t1_s0 : t1 k*s0 k=0 := by
  nth_rw 1 [←t1_q1 k,←q0_s0 k]
  calc
    _=t1 k*(q1 k*q0 k)*s0 k := by simp only [mul_assoc]
    _=0 := by rw [q1_q0,mul_zero,zero_mul]
 theorem s0_t0_add_s1_t1 : s0 k*t0 k+s1 k*t1 k=q k := by rw [s0_t0,s1_t1,q0_add_q1]

end FiniteAlgebraicEnvelopes.PartialAffine.Corner

section
namespace FiniteAlgebraicEnvelopes.PartialAffine.Corner
open scoped TensorProduct
variable (k B : Type*) [CommRing k] [Ring B] [Algebra k B]

def cornerTensor : B →ₙₐ[k] B ⊗[k] MonoidAlgebra k monoid where
  toFun x := x ⊗ₜ[k] q k
  map_zero' := TensorProduct.zero_tmul _ _
  map_add' x y := TensorProduct.add_tmul _ _ _
  map_mul' x y := by rw [Algebra.TensorProduct.tmul_mul_tmul,q_idem]
  map_smul' r x := TensorProduct.smul_tmul' _ _ _

def coefficient0 : MonoidAlgebra k monoid →ₗ[k] k where
  toFun f := f.coeff E0
  map_add' f g := by simp
  map_smul' r f := by simp

 theorem coefficient0_q : coefficient0 k (q k)=1 := by
  change (q k).coeff E0 = 1
  simp [q,b,E0_ne_E1]

def cornerRetract : B ⊗[k] MonoidAlgebra k monoid →ₗ[k] B :=
  (TensorProduct.rid k B).toLinearMap.comp (TensorProduct.map (LinearMap.id : B →ₗ[k] B) (coefficient0 k))

 theorem cornerRetract_cornerTensor (x : B) : cornerRetract k B (cornerTensor k B x)=x := by
  change TensorProduct.rid k B (TensorProduct.map (LinearMap.id : B →ₗ[k] B) (coefficient0 k) (x ⊗ₜ[k] q k))=x
  rw [TensorProduct.map_tmul,coefficient0_q]
  simp

 theorem cornerTensor_injective : Function.Injective (cornerTensor k B) :=
  Function.LeftInverse.injective (cornerRetract_cornerTensor k B)
end FiniteAlgebraicEnvelopes.PartialAffine.Corner

end

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometry
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology

noncomputable section

namespace PresentationGeometry

namespace Cells
section

open Metric

variable {X : Type*} [TopologicalSpace X] {k d : ℕ}
variable (f : C(boundary k d, X))

variable [T2Space X] [CompactSpace X] [Nonempty X]
variable [CWComplex (univ : Set X)]

variable (hdim : ∀ n, RelCWComplex.cell (univ : Set X) n → n < d)

variable [RelCWComplex.FiniteType (univ : Set X)]

theorem cwComplex_finite :
    letI := cwComplex f hdim
    RelCWComplex.Finite (univ : Set (Space f)) := by
  let := cwComplex f hdim
  exact { eventually_isEmpty_cell := newCell_eventually_isEmpty hdim
          finite_cell := newCell_finite }

end

instance disk_pathConnectedSpace (d : ℕ) : PathConnectedSpace (Disk d) :=
  isPathConnected_iff_pathConnectedSpace.mp
    ((convex_closedBall (0 : Fin d → ℝ) (1 : ℝ)).isPathConnected
      ⟨0, by simp⟩)

theorem pathConnectedSpace {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    {k d : ℕ} (f : C(boundary k d, X)) (hd : 0 < d) : PathConnectedSpace (Space f) := by
  classical
  let x : X := Classical.choice PathConnectedSpace.nonempty
  have hx : ∀ z : Space f, Joined (Adjunction.old f x) z := by
    intro z
    obtain ⟨xz | ⟨i, v⟩, rfl⟩ := Quotient.mk_surjective z
    · exact (PathConnectedSpace.joined x xz).map (Adjunction.continuous_old f)
    · let u : Disk d := ⟨boundaryVector d,
        Metric.sphere_subset_closedBall (boundaryVector_mem_sphere hd)⟩
      let b : boundary k d := ⟨(i, u), boundaryVector_mem_sphere hd⟩
      have h₁ := (PathConnectedSpace.joined x (f b)).map (Adjunction.continuous_old f)
      have h₂ := (PathConnectedSpace.joined u v).map
        (f := fun z => Adjunction.disk f (i, z))
        ((Adjunction.continuous_disk f).comp (continuous_const.prodMk continuous_id))
      rw [Adjunction.disk_boundary f b] at h₂
      exact h₁.trans h₂
  exact ⟨⟨Adjunction.old f x⟩, fun a b => (hx a).symm.trans (hx b)⟩

end Cells

end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SphereCover
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
namespace SphereCover
section
open Set Metric
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def overlapInterEquiv (v : Sphere E) : Overlap v ≃ₜ (Cap v ∩ Cap (-v) : Set (Sphere E)) where
  toEquiv :=
    { toFun := fun z => ⟨z.1.1,z.2,z.1.2⟩
      invFun := fun z => ⟨⟨z.1,z.2.2⟩,z.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

lemma overlap_pathConnected [FiniteDimensional ℝ E] (n : ℕ)
    (hd : Module.finrank ℝ E = n+3) (v : Sphere E) :
    IsPathConnected (Cap v ∩ Cap (-v)) := by
  let : Fact (Module.finrank ℝ E = (n+2)+1) := ⟨hd⟩
  have hv : ((-v : Sphere E) : E) ≠ 0 := by
    intro h
    have := norm_eq_of_mem_sphere (-v)
    simp [h] at this
  have ho : Module.finrank ℝ (Orth (-v)) = n+2 :=
    Submodule.finrank_orthogonal_span_singleton hv
  have hr : 1 < Module.rank ℝ (Orth (-v)) := by
    rw [← Module.finrank_eq_rank,ho]
    exact_mod_cast (by omega : 1 < n+2)
  let : PathConnectedSpace ({0}ᶜ : Set (Orth (-v))) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_compl_singleton_of_one_lt_rank hr 0)
  let : PathConnectedSpace (Overlap v) := (overlapEquiv v).symm.surjective.pathConnectedSpace (overlapEquiv v).symm.continuous
  let : PathConnectedSpace (Cap v ∩ Cap (-v) : Set (Sphere E)) :=
    (overlapInterEquiv v).surjective.pathConnectedSpace (overlapInterEquiv v).continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

theorem simplyConnected [FiniteDimensional ℝ E] (n : ℕ)
    (hd : Module.finrank ℝ E = n+3) : SimplyConnectedSpace (Sphere E) := by
  have hr : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank,hd]
    exact_mod_cast (by omega : 1 < n+3)
  let : PathConnectedSpace (Sphere E) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hr (0 : E) (by norm_num : (0 : ℝ) ≤ 1))
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance,fun x p => ?_⟩
  let v : Sphere E := -x
  let := cap_contractible v
  let := cap_contractible (-v)
  let b : Cap v := ⟨x,ne_neg x⟩
  have hs := PresentationVanKampen.fundamentalGroupMap_surjective_of_disjoint_open_cover
    (Cap v) (fun _ : Unit => Cap (-v)) isOpen_compl_singleton
    (fun _ => isOpen_compl_singleton) (by simpa only [iUnion_const, isOpen_compl_singleton.interior_eq] using cap_cover v)
    (fun _ _ h => False.elim (h (Subsingleton.elim _ _)))
    (fun _ => overlap_pathConnected n hd v) (fun _ => inferInstance) b
  obtain ⟨q,hq⟩ := hs (Path.Homotopic.Quotient.mk p)
  have hq' : q = 1 := Subsingleton.elim _ _
  apply Path.Homotopic.Quotient.eq.mp
  rw [← hq,hq',map_one]
  rfl
end

open Set Metric Topology
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma normed_simplyConnected [FiniteDimensional ℝ E] (n : ℕ)
    (hd : Module.finrank ℝ E = n+3) : SimplyConnectedSpace (Sphere E) := by
  let F := EuclideanSpace ℝ (Fin (n+3))
  have hdF : Module.finrank ℝ F = n+3 := finrank_euclideanSpace_fin
  let : ContinuousSMul ℝ F := IsBoundedSMul.continuousSMul
  let e : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq (hd.trans hdF.symm)
  let := simplyConnected n hdF
  exact (sphereHomotopyEquiv e).simplyConnectedSpace

end SphereCover

open scoped unitInterval
open Set

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SequentialColimit
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SequentialCoreTower

open Set Topology
variable (X : ℕ → Type) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  (I : ℕ → Type) (δ : ∀ i j, i ≤ j → I i ↪ I j)
  [DirectedSystem I (δ · · ·)]
  {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (Z : ∀ n, FiberBundleCore (I n) (X n) Q)
  (pot : ∀ n, I n → X n → Q)
  (hBase : ∀ i j (h : i ≤ j) a x,
    x ∈ (Z i).baseSet a ↔ f i j h x ∈ (Z j).baseSet (δ i j h a))
  (hPot : ∀ i j (h : i ≤ j) a x,
    pot j (δ i j h a) (f i j h x) = pot i a x)
  (hCoord : ∀ n a b x q, (Z n).coordChange a b x q = pot n b x * (pot n a x)⁻¹ * q)

noncomputable def coverIncl (n : ℕ) :
    C((Z n).TotalSpace,(core X f I δ Z pot hBase hPot hCoord).TotalSpace) :=
  FiberCoreMap.continuousMap (Z n) (core X f I δ Z pot hBase hPot hCoord)
    (SequentialColimit.incl X f n) (fun a => ⟨n,a⟩)
    (fun a x hx => (baseSet_incl X f I δ Z pot hBase hPot hCoord n a x).mpr hx)
    (fun a b x _ q => coordChange_incl X f I δ Z pot hBase hPot hCoord n a b x q)

@[simp] lemma coverIncl_proj (n : ℕ) (e : (Z n).TotalSpace) :
    (core X f I δ Z pot hBase hPot hCoord).proj (coverIncl X f I δ Z pot hBase hPot hCoord n e) =
      SequentialColimit.incl X f n ((Z n).proj e) := rfl

end SequentialCoreTower

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SequentialColimitRangeInclMono
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SequentialCW
open Set Topology Metric
universe u
variable (X : ℕ → Type u) [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
  [∀ i, CWComplex (univ : Set (X i))]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  (hf : ∀ i j h, IsClosedEmbedding (f i j h))
variable (δ : ∀ i j, i ≤ j → ∀ n, Cell X i n ↪ Cell X j n)
  [∀ n, DirectedSystem (fun i => Cell X i n) (fun i j h => δ i j h n)]
  (hδ : ∀ i j h n (c : Cell X i n) v, v ∈ closedBall (0 : Fin n → ℝ) 1 →
    f i j h (RelCWComplex.map n c v) = RelCWComplex.map n (δ i j h n c) v)

abbrev Space := SequentialColimit.Space X f

def stageChart (i n : ℕ) (c : Cell X i n) : PartialEquiv (Fin n → ℝ) (Space X f) :=
  (RelCWComplex.map n c).trans
    ((SequentialColimit.incl_isClosedEmbedding X f hf i).isEmbedding.toPartialHomeomorph
      (SequentialColimit.incl X f i)).toPartialEquiv

@[simp] lemma stageChart_apply (i n : ℕ) (c : Cell X i n) (v : Fin n → ℝ) :
    stageChart X f hf i n c v = SequentialColimit.incl X f i (RelCWComplex.map n c v) := rfl
@[simp] lemma stageChart_source (i n : ℕ) (c : Cell X i n) :
    (stageChart X f hf i n c).source = ball 0 1 := by
  simp [stageChart,PartialEquiv.trans_source,RelCWComplex.source_eq]
lemma stageChart_continuousOn (i n : ℕ) (c : Cell X i n) :
    ContinuousOn (stageChart X f hf i n c) (closedBall 0 1) :=
  (SequentialColimit.incl X f i).continuous.comp_continuousOn (RelCWComplex.continuousOn n c)
lemma stageChart_continuousOn_symm (i n : ℕ) (c : Cell X i n) :
    ContinuousOn (stageChart X f hf i n c).symm (stageChart X f hf i n c).target := by
  let e := (SequentialColimit.incl_isClosedEmbedding X f hf i).isEmbedding.toPartialHomeomorph
    (SequentialColimit.incl X f i)
  exact (RelCWComplex.continuousOn_symm n c).comp
    (e.continuousOn_symm.mono inter_subset_left) (fun _ h => h.2)

include hδ in
lemma stageChart_eq {i j n : ℕ} (c : Cell X i n) (d : Cell X j n)
    (he : cellMk X δ i n c = cellMk X δ j n d) (v : Fin n → ℝ)
    (hv : v ∈ closedBall 0 1) : stageChart X f hf i n c v = stageChart X f hf j n d v := by
  obtain ⟨k,hik,hjk,hcd⟩ := Quotient.eq.mp he
  simp only [stageChart_apply]
  rw [← SequentialColimit.incl_map X f i k hik,← SequentialColimit.incl_map X f j k hjk,
    hδ i k hik n c v hv,hδ j k hjk n d v hv,hcd]

def chart (n : ℕ) (c : FinalCell X δ n) : PartialEquiv (Fin n → ℝ) (Space X f) :=
  stageChart X f hf (repr X δ n c).1 n (repr X δ n c).2

include hδ in
lemma chart_mk (i n : ℕ) (c : Cell X i n) (v : Fin n → ℝ) (hv : v ∈ closedBall 0 1) :
    chart X f hf δ n (cellMk X δ i n c) v = SequentialColimit.incl X f i (RelCWComplex.map n c v) :=
  stageChart_eq X f hf δ hδ _ c (repr_eq X δ n _) v hv

lemma chart_source (n : ℕ) (c : FinalCell X δ n) : (chart X f hf δ n c).source = ball 0 1 :=
  stageChart_source X f hf _ _ _
lemma chart_continuousOn (n : ℕ) (c : FinalCell X δ n) :
    ContinuousOn (chart X f hf δ n c) (closedBall 0 1) := stageChart_continuousOn X f hf _ _ _
lemma chart_continuousOn_symm (n : ℕ) (c : FinalCell X δ n) :
    ContinuousOn (chart X f hf δ n c).symm (chart X f hf δ n c).target :=
  stageChart_continuousOn_symm X f hf _ _ _

include hδ in
lemma chart_union : (⋃ (n : ℕ) (c : FinalCell X δ n), chart X f hf δ n c '' closedBall 0 1) = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk f z
  have hx : x ∈ ⋃ (n : ℕ) (c : Cell X i n), RelCWComplex.map n c '' closedBall 0 1 := by
    change x ∈ ⋃ (n : ℕ) (c : Cell X i n), RelCWComplex.closedCell n c
    rw [CWComplex.union]; trivial
  simp only [mem_iUnion,mem_image] at hx
  obtain ⟨n,c,v,hv,rfl⟩ := hx
  exact mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨cellMk X δ i n c,⟨v,hv,chart_mk X f hf δ hδ i n c v hv⟩⟩⟩

@[simp] lemma cellMk_map (X : ℕ → Type u) [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
    [∀ i, CWComplex (univ : Set (X i))]
    (δ : ∀ i j, i ≤ j → ∀ n, Cell X i n ↪ Cell X j n)
    [∀ n, DirectedSystem (fun i => Cell X i n) (fun i j h => δ i j h n)]
    (i j : ℕ) (h : i ≤ j) (n : ℕ) (c : Cell X i n) :
    cellMk X δ j n (δ i j h n c) = cellMk X δ i n c := by
  unfold cellMk
  exact DirectLimit.mk_apply (f:=fun i j h => δ i j h n) i j c h

include hδ in
lemma chart_cell_eq {n m : ℕ} (c : FinalCell X δ n) (d : FinalCell X δ m)
    {v : Fin n → ℝ} {w : Fin m → ℝ} (hv : v ∈ ball 0 1) (hw : w ∈ ball 0 1)
    (he : chart X f hf δ n c v = chart X f hf δ m d w) :
    (⟨n,c⟩ : Σ n, FinalCell X δ n) = ⟨m,d⟩ := by
  classical
  induction c using Quotient.inductionOn with
  | h c =>
    rcases c with ⟨i,c⟩
    induction d using Quotient.inductionOn with
    | h d =>
      rcases d with ⟨j,d⟩
      change chart X f hf δ n (cellMk X δ i n c) v = chart X f hf δ m (cellMk X δ j m d) w at he
      rw [chart_mk X f hf δ hδ _ _ _ _ (ball_subset_closedBall hv),
        chart_mk X f hf δ hδ _ _ _ _ (ball_subset_closedBall hw),
        ← SequentialColimit.incl_map X f i (max i j) (le_max_left _ _),
        ← SequentialColimit.incl_map X f j (max i j) (le_max_right _ _),
        hδ i (max i j) (le_max_left _ _) n c v (ball_subset_closedBall hv),
        hδ j (max i j) (le_max_right _ _) m d w (ball_subset_closedBall hw)] at he
      have he' := (SequentialColimit.incl_isClosedEmbedding X f hf (max i j)).injective he
      have hn : (⟨n,δ i (max i j) (le_max_left _ _) n c⟩ : Σ n, Cell X (max i j) n) =
          ⟨m,δ j (max i j) (le_max_right _ _) m d⟩ := by
        by_contra hn
        exact Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne hn)
          ⟨v,hv,rfl⟩ ⟨w,hw,he'.symm⟩
      have hz := congrArg (fun a : Σ n, Cell X (max i j) n =>
        (⟨a.1,cellMk X δ (max i j) a.1 a.2⟩ : Σ n, FinalCell X δ n)) hn
      change (⟨n,cellMk X δ i n c⟩ : Σ n, FinalCell X δ n) = ⟨m,cellMk X δ j m d⟩
      simpa only [cellMk_map] using hz

include hδ in
lemma chart_pairwiseDisjoint :
    (univ : Set (Σ n, FinalCell X δ n)).PairwiseDisjoint
      (fun c => chart X f hf δ c.1 c.2 '' ball 0 1) := by
  intro c _ d _ hcd
  apply Set.disjoint_left.mpr
  rintro z ⟨v,hv,rfl⟩ ⟨w,hw,he⟩
  exact hcd (chart_cell_eq X f hf δ hδ c.2 d.2 hv hw he.symm)

include hδ in
lemma chart_mapsTo (n : ℕ) (c : FinalCell X δ n) :
    ∃ I : ∀ m, Finset (FinalCell X δ m),
      MapsTo (chart X f hf δ n c) (sphere 0 1)
        (⋃ (m < n) (j ∈ I m), chart X f hf δ m j '' closedBall 0 1) := by
  classical
  induction c using Quotient.inductionOn with
  | h c =>
    rcases c with ⟨i,c⟩
    obtain ⟨I,hI⟩ := CWComplex.mapsTo n c
    refine ⟨fun m => (I m).image (cellMk X δ i m),?_⟩
    intro v hv
    obtain ⟨m,hm,j,hj,w,hw,he⟩ := by
      simpa only [mem_iUnion,mem_image] using hI hv
    simp only [mem_iUnion,mem_image]
    refine ⟨m,hm,cellMk X δ i m j,Finset.mem_image_of_mem _ hj,w,hw,?_⟩
    change chart X f hf δ m (cellMk X δ i m j) w = chart X f hf δ n (cellMk X δ i n c) v
    rw [chart_mk X f hf δ hδ i m j w hw,
      chart_mk X f hf δ hδ i n c v (sphere_subset_closedBall hv)]
    exact congrArg (SequentialColimit.incl X f i) he

include hδ in
lemma chart_image (i n : ℕ) (c : Cell X i n) :
    chart X f hf δ n (cellMk X δ i n c) '' closedBall 0 1 =
      SequentialColimit.incl X f i '' RelCWComplex.closedCell n c := by
  rw [RelCWComplex.closedCell,← image_comp]
  exact image_congr (fun v hv => chart_mk X f hf δ hδ i n c v hv)

include hδ in
lemma chart_closed (A : Set (Space X f))
    (hA : ∀ n (c : FinalCell X δ n), IsClosed (A ∩ chart X f hf δ n c '' closedBall 0 1)) :
    IsClosed A := by
  apply isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage.mp
  apply isClosed_sigma_iff.mpr
  intro i
  change IsClosed (SequentialColimit.incl X f i ⁻¹' A)
  apply (CWComplex.closed (univ : Set (X i)) _ (subset_univ _)).mpr
  intro n c
  have hc := (hA n (cellMk X δ i n c)).preimage (SequentialColimit.incl X f i).continuous
  rw [chart_image X f hf δ hδ i n c,preimage_inter,
    (SequentialColimit.incl_isClosedEmbedding X f hf i).injective.preimage_image] at hc
  exact hc

@[instance_reducible] def cwComplex : CWComplex (univ : Set (Space X f)) where
  cell := FinalCell X δ
  map := chart X f hf δ
  source_eq := chart_source X f hf δ
  continuousOn := chart_continuousOn X f hf δ
  continuousOn_symm := chart_continuousOn_symm X f hf δ
  pairwiseDisjoint' := chart_pairwiseDisjoint X f hf δ hδ
  mapsTo' := chart_mapsTo X f hf δ hδ
  closed' A _ := chart_closed X f hf δ hδ A
  union' := chart_union X f hf δ hδ

end SequentialCW

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryRose
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry.AttachingLoops
open scoped unitInterval

theorem onCircle_naturality {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (p : Path x x) (q : Path y y) (f : C(X,Y))
    (h : ∀ t, f (p t) = q t) (z : AddCircle (1 : ℝ)) :
    f (onCircle p z) = onCircle q z := by
  obtain ⟨t,ht,rfl⟩ := AddCircle.eq_coe_Ico z
  have hu : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1,ht.2.le⟩
  change f (onCircle p (((⟨t,hu⟩ : I) : ℝ) : AddCircle (1 : ℝ))) =
    onCircle q (((⟨t,hu⟩ : I) : ℝ) : AddCircle (1 : ℝ))
  rw [onCircle_coe,onCircle_coe]
  exact h _

end PresentationGeometry.AttachingLoops

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryFiniteStage
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains

variable (G : Type*)

lemma mapChain_cone {H : Type*} (f : G → H) (a : G) (c : Chain G) :
    mapChain G f (cone G a c) = cone H (f a) (mapChain G f c) := by
  have h : mapChain G f ∘ₗ cone G a = cone H (f a) ∘ₗ mapChain G f := by
    apply Finsupp.lhom_ext
    intro s r
    simp [simplexCone]
  exact LinearMap.congr_fun h c

lemma boundary_mapChain {H : Type*} (f : G → H) (c : Chain G) :
    boundary H (mapChain G f c) = mapChain G f (boundary G c) := by
  have hb (l : List G) (a : G) :
      boundary H (mapChain G f (Finsupp.single (a,l) 1)) =
        mapChain G f (boundary G (Finsupp.single (a,l) 1)) := by
    induction l generalizing a with
    | nil =>
      change boundary H (mapChain G f (vertex G a)) = mapChain G f (boundary G (vertex G a))
      rw [mapChain_vertex, boundary_vertex, boundary_vertex, map_zero]
    | cons b l ih =>
      rw [single_cons]
      rw [mapChain_cone, boundary_cone, boundary_cone, map_sub, map_sub,
        mapChain_cone, mapChain_K, ih b]
  have he : boundary H ∘ₗ mapChain G f = mapChain G f ∘ₗ boundary G := by
    apply Finsupp.lhom_ext
    intro s r
    have hr : Finsupp.single s r = r • Finsupp.single s 1 := by simp
    simp only [LinearMap.comp_apply, hr, map_smul, hb s.2 s.1]
  exact LinearMap.congr_fun he c

lemma sign_cone (a : G) (c : Chain G) : sign G (cone G a c) = -cone G a (sign G c) := by
  have h : sign G ∘ₗ cone G a = -(cone G a ∘ₗ sign G) := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, cone_single, sign_single,
      map_smul, degree, simplexCone, List.length_cons, pow_succ, mul_neg_one, neg_smul]
  exact LinearMap.congr_fun h c

lemma boundary_sign (c : Chain G) : boundary G (sign G c) = -sign G (boundary G c) := by
  have hb (l : List G) (a : G) : boundary G (sign G (Finsupp.single (a,l) 1)) =
      -sign G (boundary G (Finsupp.single (a,l) 1)) := by
    induction l generalizing a with
    | nil =>
      change boundary G (sign G (vertex G a)) = -sign G (boundary G (vertex G a))
      rw [sign_vertex, boundary_vertex, map_zero, neg_zero]
    | cons b l ih =>
      rw [single_cons, sign_cone, map_neg, boundary_cone, boundary_cone,
        map_sub, map_sub, ih b, map_neg, K_sign, sign_cone, sign_K]
  have h : boundary G ∘ₗ sign G = -(sign G ∘ₗ boundary G) := by
    apply Finsupp.lhom_ext
    intro s r
    have hr : Finsupp.single s r = r • Finsupp.single s 1 := by simp
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, hr, map_smul,
      hb s.2 s.1, smul_neg]
  exact LinearMap.congr_fun h c

lemma supported_zero (P : Simplex G → Prop) : Supported G P 0 := by simp [Supported]

lemma supported_neg {P : Simplex G → Prop} {c : Chain G}
    (hc : Supported G P c) : Supported G P (-c) := by
  simpa only [Supported, Finsupp.support_neg] using hc

lemma supported_sub {P : Simplex G → Prop} {c d : Chain G}
    (hc : Supported G P c) (hd : Supported G P d) : Supported G P (c-d) := by
  rw [sub_eq_add_neg]
  exact supported_add G hc (supported_neg G hd)

lemma supported_single {P : Simplex G → Prop} {s : Simplex G} (hs : P s) (r : ℤ) :
    Supported G P (Finsupp.single s r) := by
  classical
  intro t ht
  have h : t = s := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
  simpa only [h] using hs

lemma supported_sum {ι : Type*} (t : Finset ι) {P : Simplex G → Prop}
    (c : ι → Chain G) (hc : ∀ i ∈ t, Supported G P (c i)) :
    Supported G P (∑ i ∈ t, c i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using supported_zero G P
  | @insert i t hit ih =>
    rw [Finset.sum_insert hit]
    exact supported_add G (hc i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hc j (Finset.mem_insert_of_mem hj)))

lemma supported_linearMap {H : Type*} {P : Simplex G → Prop} {Q : Simplex H → Prop}
    (T : Chain G →ₗ[ℤ] Chain H)
    (hT : ∀ s, P s → Supported H Q (T (Finsupp.single s 1)))
    {c : Chain G} (hc : Supported G P c) : Supported H Q (T c) := by
  classical
  have he : T c = ∑ s ∈ c.support, (c s) • T (Finsupp.single s 1) := by
    conv_lhs => rw [← Finsupp.sum_single c]
    rw [Finsupp.sum, map_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [he]
  exact supported_sum H c.support _ (fun s hs => supported_smul H _ (hT s (hc s hs)))

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FreeTensor
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains
section

variable (G H : Type*)

abbrev tensorMap {G' H' : Type*} (f : Chain G →ₗ[ℤ] Chain G')
    (g : Chain H →ₗ[ℤ] Chain H') : BiChain G H →ₗ[ℤ] BiChain G' H' :=
  FreeTensor.map (Simplex G) (Simplex H) f g

lemma tensorMap_tensor {G' H' : Type*} (f : Chain G →ₗ[ℤ] Chain G')
    (g : Chain H →ₗ[ℤ] Chain H') (x : Chain G) (y : Chain H) :
    tensorMap G H f g (tensor G H x y) = tensor G' H' (f x) (g y) :=
  FreeTensor.map_pure ..

def biBoundary : BiChain G H →ₗ[ℤ] BiChain G H :=
  tensorMap G H (boundary G) LinearMap.id + tensorMap G H (sign G) (boundary H)

lemma biBoundary_tensor (x : Chain G) (y : Chain H) :
    biBoundary G H (tensor G H x y) =
      tensor G H (boundary G x) y + tensor G H (sign G x) (boundary H y) := by
  simp only [biBoundary, LinearMap.add_apply, tensorMap_tensor, LinearMap.id_apply]

lemma biBoundary_squared (c : BiChain G H) : biBoundary G H (biBoundary G H c) = 0 := by
  have he : biBoundary G H ∘ₗ biBoundary G H = 0 := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, biBoundary_tensor,
      map_add, boundary_boundary, map_zero,
      LinearMap.zero_apply, boundary_sign, map_neg, LinearMap.neg_apply,
      add_neg_cancel, add_zero, zero_add]
  exact LinearMap.congr_fun he c

def biAugmentation : BiChain G H →ₗ[ℤ] ℤ :=
  FreeTensor.lift (Simplex G) (Simplex H)
    (((LinearMap.mul ℤ ℤ).comp (augmentation G)).compl₂ (augmentation H))

lemma biAugmentation_tensor (x : Chain G) (y : Chain H) :
    biAugmentation G H (tensor G H x y) = augmentation G x * augmentation H y := by
  rw [biAugmentation, FreeTensor.lift_pure]
  rfl

lemma biAugmentation_boundary (c : BiChain G H) : biAugmentation G H (biBoundary G H c) = 0 := by
  have he : biAugmentation G H ∘ₗ biBoundary G H = 0 := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, biBoundary_tensor, map_add,
      biAugmentation_tensor, augmentation_boundary, zero_mul, mul_zero, zero_add]
  exact LinearMap.congr_fun he c

def biCone (a : G) (b : H) : BiChain G H →ₗ[ℤ] BiChain G H :=
  tensorMap G H (cone G a) LinearMap.id + tensorMap G H (K G a) (cone H b)

lemma biCone_tensor (a : G) (b : H) (x : Chain G) (y : Chain H) :
    biCone G H a b (tensor G H x y) =
      tensor G H (cone G a x) y + tensor G H (K G a x) (cone H b y) := by
  simp only [biCone, LinearMap.add_apply, tensorMap_tensor, LinearMap.id_apply]

lemma biBoundary_biCone (a : G) (b : H) (c : BiChain G H) :
    biBoundary G H (biCone G H a b c) + biCone G H a b (biBoundary G H c) =
      c - biAugmentation G H c • tensor G H (vertex G a) (vertex H b) := by
  have he : biBoundary G H ∘ₗ biCone G H a b + biCone G H a b ∘ₗ biBoundary G H =
      LinearMap.id - (biAugmentation G H).smulRight (tensor G H (vertex G a) (vertex H b)) := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.smulRight_apply, biCone_tensor, biBoundary_tensor,
      map_add, LinearMap.add_apply, boundary_cone, boundary_K, sign_cone, sign_K,
      K_boundary, K_sign, map_zero, LinearMap.zero_apply, map_sub, LinearMap.sub_apply,
      map_neg, LinearMap.neg_apply, biAugmentation_tensor]
    simp only [K_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_smul]
    abel
  exact LinearMap.congr_fun he c

end

variable (G : Type*)

lemma vertices_vertex (a : G) : vertices G (simplexVertex G a) = {a} := by
  ext x
  simp [vertices, simplexVertex]

lemma vertices_cone (a : G) (s : Simplex G) :
    vertices G (simplexCone G a s) = insert a (vertices G s) := by
  ext x
  simp [vertices, simplexCone]

lemma supported_cone {P Q : Simplex G → Prop} (a : G)
    (h : ∀ s, P s → Q (simplexCone G a s)) {c : Chain G}
    (hc : Supported G P c) : Supported G Q (cone G a c) := by
  refine supported_linearMap G (Q := Q) (cone G a) ?_ hc
  intro s hs
  rw [cone_single]
  exact supported_single G (h s hs) 1

theorem boundary_faces (s : Simplex G) :
    Supported G (fun t => degree G t + 1 = degree G s ∧ vertices G t ⊆ vertices G s)
      (boundary G (Finsupp.single s 1)) := by
  rcases s with ⟨a,l⟩
  induction l generalizing a with
  | nil =>
    change Supported G _ (boundary G (vertex G a))
    rw [boundary_vertex]
    exact supported_zero G _
  | cons b l ih =>
    rw [single_cons, boundary_cone]
    apply supported_sub
    · apply supported_sub
      · apply supported_single
        constructor
        · rfl
        · intro x hx
          exact Or.inr (by simpa only [vertices, Set.mem_ofPred_eq, List.mem_cons] using hx)
      · refine supported_cone G
          (Q := fun t => degree G t + 1 = degree G (a, b::l) ∧
            vertices G t ⊆ vertices G (a, b::l)) a ?_ (ih b)
        intro t ht
        constructor
        · change degree G t + 1 + 1 = l.length + 1
          exact congrArg (· + 1) ht.1
        · rw [vertices_cone]
          intro x hx
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (by simpa only [vertices, Set.mem_ofPred_eq, List.mem_cons] using ht.2 hx)
    · rw [K_apply, augmentation_single]
      by_cases hl : l = []
      · subst l
        rw [ite_eq_left rfl, one_smul]
        apply supported_single
        constructor
        · rfl
        · intro x hx
          exact Or.inl (by simpa only [vertices_vertex, Set.mem_singleton_iff] using hx)
      · rw [ite_eq_right hl, zero_smul]
        exact supported_zero G _

lemma boundary_lowers (s t : Simplex G)
    (ht : t ∈ (boundary G (Finsupp.single s 1)).support) :
    degree G t + 1 = degree G s := (boundary_faces G s t ht).1

lemma boundary_vertices (s t : Simplex G)
    (ht : t ∈ (boundary G (Finsupp.single s 1)).support) :
    vertices G t ⊆ vertices G s := (boundary_faces G s t ht).2

def vertexModule (V : Set G) : Submodule ℤ (Chain G) :=
  Finsupp.supported ℤ ℤ {s | vertices G s ⊆ V}

lemma mem_vertexModule {V : Set G} {c : Chain G} :
    c ∈ vertexModule G V ↔ Supported G (fun s => vertices G s ⊆ V) c := by
  rfl

lemma boundary_mem_vertexModule {V : Set G} {c : Chain G}
    (hc : c ∈ vertexModule G V) : boundary G c ∈ vertexModule G V := by
  apply (mem_vertexModule G).mpr
  refine supported_linearMap G (Q := fun s => vertices G s ⊆ V) (boundary G) ?_
    ((mem_vertexModule G).mp hc)
  intro s hs
  exact fun t ht => (boundary_vertices G s t ht).trans hs

lemma boundary_mem_degreeModule {n : ℕ} {c : Chain G}
    (hc : c ∈ degreeModule G (n+1)) : boundary G c ∈ degreeModule G n := by
  refine supported_linearMap G (Q := fun s => degree G s = n) (boundary G) ?_ hc
  intro s hs t ht
  have hl := boundary_lowers G s t ht
  exact Nat.add_right_cancel (hl.trans hs)

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FreeTensorPureMem
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FreeTensor

variable (ι κ : Type*)

lemma pure_mem (K : Submodule ℤ (Chains ι κ)) (x : ι →₀ ℤ) (y : κ →₀ ℤ)
    (h : ∀ i ∈ x.support, ∀ k ∈ y.support, Finsupp.single (i,k) 1 ∈ K) :
    pure ι κ x y ∈ K := by
  apply BasedComplex.map_mem_of_support ((pure ι κ).flip y) K x
  intro i hi
  change pure ι κ (Finsupp.single i 1) y ∈ K
  apply BasedComplex.map_mem_of_support (pure ι κ (Finsupp.single i 1)) K y
  intro k hk
  rw [pure_single_one]
  exact h i hi k hk

end FreeTensor

namespace ListChains
section

variable (G H : Type*)

def based : BasedComplex.Data (Simplex G) where
  degree := degree G
  d := boundary G
  aug := augmentation G
  d_squared := boundary_boundary G
  lowers := boundary_lowers G
  aug_single s := by simp only [augmentation_single, degree, List.length_eq_zero_iff]
  aug_d := augmentation_boundary G

def contraction (a : G) : BasedComplex.Contraction (boundary G) (augmentation G) where
  point := vertex G a
  cone := cone G a
  d_point := boundary_vertex G a
  aug_point := augmentation_vertex G a
  aug_cone := augmentation_cone G a
  identity c := by rw [boundary_cone, K_apply]; abel

def biDegree (s : Simplex G × Simplex H) : ℕ := degree G s.1 + degree H s.2

def biDegreeModule (n : ℕ) : Submodule ℤ (BiChain G H) :=
  Finsupp.supported ℤ ℤ {s | biDegree G H s = n}

def biVertexModule (V : Set G) (W : Set H) : Submodule ℤ (BiChain G H) :=
  Finsupp.supported ℤ ℤ {s | vertices G s.1 ⊆ V ∧ vertices H s.2 ⊆ W}

lemma biBoundary_lowers (s t : Simplex G × Simplex H)
    (ht : t ∈ (biBoundary G H (Finsupp.single s 1)).support) :
    biDegree G H t + 1 = biDegree G H s := by
  let K : Submodule ℤ (BiChain G H) :=
    Finsupp.supported ℤ ℤ {t | biDegree G H t + 1 = biDegree G H s}
  suffices hc : biBoundary G H (Finsupp.single s 1) ∈ K by exact hc ht
  rw [← FreeTensor.pure_single_one, biBoundary_tensor]
  apply K.add_mem
  · apply FreeTensor.pure_mem
    intro x hx y hy
    have he : y = s.2 := Finset.mem_singleton.mp (Finsupp.support_single_subset hy)
    subst y
    apply FreeTensor.single_mem_supported
    have hl := boundary_lowers G s.1 x hx
    change degree G x + degree H s.2 + 1 = degree G s.1 + degree H s.2
    omega
  · rw [sign_single]
    apply FreeTensor.pure_mem
    intro x hx y hy
    have he : x = s.1 := Finset.mem_singleton.mp
      (Finsupp.support_single_subset (Finsupp.support_smul hx))
    subst x
    apply FreeTensor.single_mem_supported
    have hl := boundary_lowers H s.2 y hy
    change degree G s.1 + degree H y + 1 = degree G s.1 + degree H s.2
    omega

lemma biAugmentation_single (s : Simplex G × Simplex H) (r : ℤ) :
    biAugmentation G H (Finsupp.single s r) = if biDegree G H s = 0 then r else 0 := by
  have hr : Finsupp.single s r = r • tensor G H
      (Finsupp.single s.1 1) (Finsupp.single s.2 1) := by
    rw [FreeTensor.pure_single_one, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hr, LinearMap.map_smul, biAugmentation_tensor, augmentation_single, augmentation_single]
  simp only [biDegree, degree, Nat.add_eq_zero_iff, List.length_eq_zero_iff]
  split_ifs <;> simp_all

lemma biAugmentation_biCone (a : G) (b : H) (c : BiChain G H) :
    biAugmentation G H (biCone G H a b c) = 0 := by
  have he : biAugmentation G H ∘ₗ biCone G H a b = 0 := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, biCone_tensor, map_add,
      biAugmentation_tensor, augmentation_cone, zero_mul, mul_zero, add_zero]
  exact LinearMap.congr_fun he c

def biBased : BasedComplex.Data (Simplex G × Simplex H) where
  degree := biDegree G H
  d := biBoundary G H
  aug := biAugmentation G H
  d_squared := biBoundary_squared G H
  lowers := biBoundary_lowers G H
  aug_single s := biAugmentation_single G H s 1
  aug_d := biAugmentation_boundary G H

def biContraction (a : G) (b : H) :
    BasedComplex.Contraction (biBoundary G H) (biAugmentation G H) where
  point := tensor G H (vertex G a) (vertex H b)
  cone := biCone G H a b
  d_point := by simp only [biBoundary_tensor, boundary_vertex, map_zero,
    LinearMap.zero_apply, add_zero]
  aug_point := by rw [biAugmentation_tensor, augmentation_vertex, augmentation_vertex, mul_one]
  aug_cone := biAugmentation_biCone G H a b
  identity := biBoundary_biCone G H a b

lemma vertices_map {G' : Type*} (f : G → G') (s : Simplex G) :
    vertices G' (f s.1, s.2.map f) = f '' vertices G s := by
  ext x
  simp only [mem_vertices, List.mem_map, Set.mem_image]
  constructor
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact ⟨s.1, Or.inl rfl, rfl⟩
    · exact ⟨a, Or.inr ha, rfl⟩
  · rintro ⟨a, rfl | ha, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨a, ha, rfl⟩

lemma mapChain_mem_vertices {G' : Type*} (f : G → G') {V : Set G} {W : Set G'}
    (hf : Set.MapsTo f V W) {c : Chain G} (hc : c ∈ vertexModule G V) :
    mapChain G f c ∈ vertexModule G' W := by
  apply BasedComplex.map_mem_of_support (mapChain G f) _ c
  intro s hs
  rw [mapChain_single]
  apply FreeTensor.single_mem_supported
  change vertices G' (f s.1, s.2.map f) ⊆ W
  rw [vertices_map]
  rintro _ ⟨a, ha, rfl⟩
  exact hf (hc hs ha)

lemma mapChain_mem_degree {G' : Type*} (f : G → G') {n : ℕ} {c : Chain G}
    (hc : c ∈ degreeModule G n) : mapChain G f c ∈ degreeModule G' n := by
  apply BasedComplex.map_mem_of_support (mapChain G f) _ c
  intro s hs
  rw [mapChain_single]
  apply FreeTensor.single_mem_supported
  change degree G' (f s.1, s.2.map f) = n
  simp only [degree, List.length_map]
  exact hc hs

def diagTensor : Chain G →ₗ[ℤ] BiChain G G :=
  BasedComplex.extend (based G) (biBoundary G G) (biAugmentation G G)
    (fun s => biContraction G G s.1 s.1)

def productComparison : BiChain G H →ₗ[ℤ] Chain (G × H) :=
  BasedComplex.extend (biBased G H) (boundary (G × H)) (augmentation (G × H))
    (fun s => contraction (G × H) (s.1.1, s.2.1))

end

variable (G : Type*)

def tensorHomotopy (F F' J : Chain G →ₗ[ℤ] Chain G) : BiChain G G →ₗ[ℤ] BiChain G G :=
  tensorMap G G J F + tensorMap G G (F' ∘ₗ sign G) J

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChains
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G H : Type*)

def projectLeft : BiChain G H →ₗ[ℤ] Chain G :=
  FreeTensor.lift (Simplex G) (Simplex H)
    (((augmentation H).smulRight (LinearMap.id : Chain G →ₗ[ℤ] Chain G)).flip)

def projectRight : BiChain G H →ₗ[ℤ] Chain H :=
  FreeTensor.lift (Simplex G) (Simplex H)
    ((augmentation G).smulRight (LinearMap.id : Chain H →ₗ[ℤ] Chain H))

end

variable (G H : Type*)

def localHomotopy (v : G → H) (F Q : Chain G →ₗ[ℤ] Chain H) :
    Chain G →ₗ[ℤ] Chain H :=
  BasedComplex.homotopy (based G) (boundary H) (augmentation H)
    (fun s => contraction H (v s.1)) F Q

def projectionHomotopyLeft : Chain G →ₗ[ℤ] Chain G :=
  localHomotopy G G id (projectLeft G G ∘ₗ diagTensor G) LinearMap.id

def projectionHomotopyRight : Chain G →ₗ[ℤ] Chain G :=
  localHomotopy G G id (projectRight G G ∘ₗ diagTensor G) LinearMap.id

def endpointHomotopyLeft (b : H) : Chain G →ₗ[ℤ] Chain (G × H) :=
  localHomotopy G (G × H) (fun a => (a,b))
    (productComparison G H ∘ₗ includeLeft G H b) (mapChain G (fun a => (a,b)))

def endpointHomotopyRight (a : G) : Chain H →ₗ[ℤ] Chain (G × H) :=
  localHomotopy H (G × H) (fun b => (a,b))
    (productComparison G H ∘ₗ includeRight G H a) (mapChain H (fun b => (a,b)))

def mappedDiagonalHomotopy (f : G → H) : Chain G →ₗ[ℤ] Chain (H × H) :=
  localHomotopy G (H × H) (fun a => (f a, f a))
    (mapChain G (fun a => (f a, f a)))
    (productComparison H H ∘ₗ tensorMap G G (mapChain G f) (mapChain G f) ∘ₗ diagTensor G)

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsHasPropagation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G H : Type*) [Group G] [Group H]

def biControlledModule (A : Set G) (B : Set H) : Submodule ℤ (BiChain G H) :=
  Finsupp.supported ℤ ℤ {s | hasPropagation G A s.1 ∧ hasPropagation H B s.2}

lemma vertexModule_le_controlledModule {V : Set G} {A : Set G}
    (h : ∀ x ∈ V, ∀ y ∈ V, x⁻¹ * y ∈ A) : vertexModule G V ≤ controlledModule G A := by
  intro c hc s hs x hx y hy
  exact h x (hc hs hx) y (hc hs hy)

lemma boundary_mem_controlledModule {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) : boundary G c ∈ controlledModule G A := by
  apply BasedComplex.map_mem_of_support (boundary G) _ c
  intro s hs
  apply vertexModule_le_controlledModule G (hc hs)
  exact boundary_mem_vertexModule G
    (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1)

lemma mapChain_mem_controlled (f : G →* H) {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) : mapChain G f c ∈ controlledModule H (f '' A) := by
  apply BasedComplex.map_mem_of_support (mapChain G f) _ c
  intro s hs
  apply vertexModule_le_controlledModule H (hom_image_propagation G H f (hc hs))
  exact mapChain_mem_vertices G f (fun _ hx => Set.mem_image_of_mem f hx)
    (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1)

end

section

variable (G : Type*) [Group G] (a : G)

def perturbedMap (F J : Chain G →ₗ[ℤ] Chain G) : Chain G →ₗ[ℤ] Chain G :=
  F - boundary G ∘ₗ J - J ∘ₗ boundary G

end

variable (G : Type*) [Group G]

def additivityFilling (a : G) (f : G → G) (J : Chain G →ₗ[ℤ] Chain G) :
    Chain G →ₗ[ℤ] Chain (G × G) :=
  mappedDiagonalHomotopy G G f +
  productComparison G G ∘ₗ tensorHomotopy G (mapChain G f) (perturbedMap G (mapChain G f) J) J ∘ₗ diagTensor G +
  endpointHomotopyRight G G a ∘ₗ mapChain G f ∘ₗ projectRight G G ∘ₗ diagTensor G +
  endpointHomotopyLeft G G a ∘ₗ mapChain G f ∘ₗ projectLeft G G ∘ₗ diagTensor G +
  mapChain G (fun b => (a,b)) ∘ₗ mapChain G f ∘ₗ projectionHomotopyRight G +
  mapChain G (fun b => (b,a)) ∘ₗ mapChain G f ∘ₗ projectionHomotopyLeft G

lemma IsBound.image {H : Type*} [Group H] {A : Set G} (ha : IsBound G A) (f : G →* H) :
    IsBound H (f '' A) where
  finite := ha.finite.image f
  one_mem := ⟨1,ha.one_mem,f.map_one⟩
  inv_mem := by
    rintro _ ⟨a,ha',rfl⟩
    exact ⟨a⁻¹,ha.inv_mem a ha',f.map_inv a⟩

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsMapChainComp
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G : Type*)

variable [Group G]

def FillsAt (B : Set G) (n : ℕ) (z : Chain G) : Prop :=
  ∃ w, w ∈ degreeModule G (n+1) ∧ w ∈ controlledModule G B ∧ boundary G w = z

open scoped Pointwise

end

section

variable (G : Type*) [Group G]

structure ControlledNullBelow (f : G →* G) (A : Set G) (n : ℕ) where
  bound : Set G
  isBound : IsBound G bound
  homotopy : Chain G →ₗ[ℤ] Chain G
  degree : ∀ m c, c ∈ degreeModule G m → homotopy c ∈ degreeModule G (m+1)
  controlled : ∀ c, c ∈ controlledModule G A → homotopy c ∈ controlledModule G bound
  zero : ∀ m, n ≤ m → ∀ c, c ∈ degreeModule G m → homotopy c = 0
  equation : ∀ m, m < n → ∀ c, c ∈ degreeModule G m → c ∈ controlledModule G A →
    boundary G (homotopy c) + homotopy (boundary G c) = mapChain G f c - K G 1 c

end

variable (G : Type*) [Group G]

def ControlledNullBelow.postcompose {f : G →* G} {A : Set G} {n : ℕ}
    (H : ControlledNullBelow G f A n) (g : G →* G) :
    ControlledNullBelow G (g.comp f) A n where
  bound := g '' H.bound
  isBound := H.isBound.image G g
  homotopy := mapChain G g ∘ₗ H.homotopy
  degree m c hc := mapChain_mem_degree G g (H.degree m c hc)
  controlled c hc := mapChain_mem_controlled G G g (H.controlled c hc)
  zero m hm c hc := by simp only [LinearMap.comp_apply,H.zero m hm c hc,map_zero]
  equation m hm c hc ha := by
    have he := congrArg (mapChain G g) (H.equation m hm c hc ha)
    simpa only [map_add,map_sub,← boundary_mapChain,mapChain_comp,mapChain_K_one,
      MonoidHom.coe_comp,LinearMap.comp_apply] using he

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BinaryPrefixOperators
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains
section

variable (G : Type*) [Group G]

def boundedBoundaries (B : Set G) (n : ℕ) : Submodule ℤ (Chain G) :=
  (degreeModule G (n+1) ⊓ controlledModule G B).map (boundary G)

def UniformFillings (f : G →* G) (n : ℕ) : Prop :=
  ∀ A : Set G, IsBound G A → ∃ k : ℕ, ∃ B : Set G, IsBound G B ∧
    ∀ z, z ∈ degreeModule G n → z ∈ controlledModule G A → boundary G z = 0 →
      (n = 0 → augmentation G z = 0) → FillsAt G B n (mapChain G (iterateHom G f k) z)

end

variable (G : Type*) {H K C D E : Type*}

def cosetModule (P : Submodule ℤ (Chain G)) : Submodule ℤ (C →₀ Chain G) where
  carrier := {z | ∀ c, z c ∈ P}
  zero_mem' := fun _ => P.zero_mem
  add_mem' := fun hz hw c => P.add_mem (hz c) (hw c)
  smul_mem' := fun r _ hz c => P.smul_mem r (hz c)

@[simp] lemma cosetBoundary_single (c : C) (z : Chain G) :
    cosetBoundary G (Finsupp.single c z) = Finsupp.single c (boundary G z) := by
  change Finsupp.mapRange (boundary G) (map_zero _) _ = _
  exact Finsupp.mapRange_single

@[simp] lemma cosetBoundary_squared (z : C →₀ Chain G) :
    cosetBoundary G (cosetBoundary G z) = 0 := by ext c s; simp

def mergeCosets (σ : C → D) : (C →₀ Chain G) →ₗ[ℤ] (D →₀ Chain G) :=
  Finsupp.lmapDomain (Chain G) ℤ σ

@[simp] lemma mergeCosets_single (σ : C → D) (c : C) (z : Chain G) :
    mergeCosets G σ (Finsupp.single c z) = Finsupp.single (σ c) z := by
  simp [mergeCosets]

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsShiftOrigin
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G : Type*) [Group G] {C : Type*}

def cosetShift (f : G →* G) (σ : C → C) (δ : C → G) :
    (C →₀ Chain G) →ₗ[ℤ] (C →₀ Chain G) :=
  cosetMap G σ (fun c x => δ c * f x)

end

section

variable (G I C : Type*) [Group G]

abbrev ProductAmbient := I → C →₀ Chain G

def boundedProducts : Submodule ℤ (ProductAmbient G I C) where
  carrier := {z | ∃ A : Set G, IsBound G A ∧
    ∀ i, z i ∈ cosetModule G (controlledModule G A)}
  zero_mem' := by
    refine ⟨{1},⟨Set.finite_singleton 1,by simp,by intro a ha;simpa using ha⟩,?_⟩
    intro i
    exact Submodule.zero_mem _
  add_mem' := by
    rintro z w ⟨A,hA,hz⟩ ⟨B,hB,hw⟩
    refine ⟨A ∪ B,hA.union G hB,?_⟩
    intro i c
    exact Submodule.add_mem _
      (controlledModule_mono G Set.subset_union_left (hz i c))
      (controlledModule_mono G Set.subset_union_right (hw i c))
  smul_mem' := by
    rintro r z ⟨A,hA,hz⟩
    exact ⟨A,hA,fun i => Submodule.smul_mem _ r (hz i)⟩

def degreeProducts (n : ℕ) : Submodule ℤ (ProductAmbient G I C) where
  carrier := {z | ∀ i, z i ∈ cosetModule G (degreeModule G n)}
  zero_mem' := fun _ => Submodule.zero_mem _
  add_mem' := fun hz hw i => Submodule.add_mem _ (hz i) (hw i)
  smul_mem' := fun r _ hz i => Submodule.smul_mem _ r (hz i)

def productBoundary : ProductAmbient G I C →ₗ[ℤ] ProductAmbient G I C :=
  LinearMap.pi (fun i => (cosetBoundary G).comp (LinearMap.proj i))

omit [Group G] in
@[simp] lemma productBoundary_apply (z : ProductAmbient G I C) (i : I) :
    productBoundary G I C z i = cosetBoundary G (z i) := rfl

omit [Group G] in
@[simp] lemma productBoundary_squared (z : ProductAmbient G I C) :
    productBoundary G I C (productBoundary G I C z) = 0 := by
  funext i
  exact cosetBoundary_squared G (z i)

lemma productBoundary_mem_bounded {z : ProductAmbient G I C}
    (hz : z ∈ boundedProducts G I C) : productBoundary G I C z ∈ boundedProducts G I C := by
  obtain ⟨A,hA,hz⟩ := hz
  exact ⟨A,hA,fun i c => boundary_mem_controlledModule G (hz i c)⟩

omit [Group G] in
lemma productBoundary_mem_degree {n : ℕ} {z : ProductAmbient G I C}
    (hz : z ∈ degreeProducts G I C (n+1)) : productBoundary G I C z ∈ degreeProducts G I C n :=
  fun i c => boundary_mem_degreeModule G (hz i c)

def productChains (n : ℕ) : Submodule ℤ (ProductAmbient G I C) :=
  boundedProducts G I C ⊓ degreeProducts G I C n

def productCycles (n : ℕ) : Submodule ℤ (ProductAmbient G I C) :=
  productChains G I C n ⊓ LinearMap.ker (productBoundary G I C)

def productDifferential (n : ℕ) : productChains G I C (n+1) →ₗ[ℤ] productCycles G I C n where
  toFun w := ⟨productBoundary G I C w.val,
    ⟨⟨productBoundary_mem_bounded G I C w.property.1,
      productBoundary_mem_degree G I C w.property.2⟩,productBoundary_squared G I C w.val⟩⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

def productBoundaries (n : ℕ) : Submodule ℤ (productCycles G I C n) :=
  LinearMap.range (productDifferential G I C n)

abbrev BoundedProductHomology (n : ℕ) :=
  productCycles G I C n ⧸ productBoundaries G I C n

def productShift (f : G →* G) (σ : C → C) (δ : C → G) :
    ProductAmbient G I C →ₗ[ℤ] ProductAmbient G I C :=
  LinearMap.pi (fun i => (cosetShift G f σ δ).comp (LinearMap.proj i))

@[simp] lemma productShift_apply (f : G →* G) (σ : C → C) (δ : C → G)
    (z : ProductAmbient G I C) (i : I) :
    productShift G I C f σ δ z i = cosetShift G f σ δ (z i) := rfl

end

section

variable (G : Type*) [Group G]

def relativeType (s : Simplex G) : List G := s.2.map (fun x => s.1⁻¹ * x)

@[simp] lemma relativeType_length (s : Simplex G) :
    (relativeType G s).length = degree G s := by simp [relativeType,degree]

end

variable (G C : Type*) [Group G]

def shapeBasisEquiv : (C × Simplex G) ≃ (List G × (C × G)) where
  toFun cs := (relativeType G cs.2,(cs.1,cs.2.1))
  invFun lc := (lc.2.1,(lc.2.2,lc.1.map (fun x => lc.2.2*x)))
  left_inv := by
    rintro ⟨c,g,l⟩
    simp only [relativeType,List.map_map]
    simp
  right_inv := by
    rintro ⟨l,c,g⟩
    simp only [relativeType,List.map_map]
    simp

def shapeCoordinates : (C →₀ Chain G) ≃ₗ[ℤ] (List G →₀ (C × G →₀ ℤ)) :=
  (Finsupp.curryLinearEquiv ℤ).symm.trans
    ((Finsupp.lcongr (shapeBasisEquiv G C) (LinearEquiv.refl ℤ ℤ)).trans
      (Finsupp.curryLinearEquiv ℤ))

@[simp] lemma shapeCoordinates_apply (z : C →₀ Chain G) (l : List G) (c : C) (g : G) :
    shapeCoordinates G C z l (c,g) = z c (g,l.map (fun x => g*x)) := rfl

lemma shapeCoordinates_at_relative (z : C →₀ Chain G) (c : C) (s : Simplex G) :
    shapeCoordinates G C z (relativeType G s) (c,s.1) = z c s := by
  rw [shapeCoordinates_apply]
  congr 1
  cases s with
  | mk g l => simp [relativeType,List.map_map]

lemma relativeType_translate (g : G) (l : List G) :
    relativeType G (g,l.map (fun x => g*x)) = l := by
  simp [relativeType,List.map_map]

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_UniformProductSupport
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains

variable (G I C : Type*) [Group G]

def realizeShapes : (List G →₀ CoefficientProduct G I C) →ₗ[ℤ] ProductAmbient G I C :=
  LinearMap.pi (fun i => (shapeCoordinates G C).symm.toLinearMap.comp
    (UniformProductSupport.evaluate (R := ℤ) i))

@[simp] lemma shapeCoordinates_realize (a : List G →₀ CoefficientProduct G I C) (i : I) :
    shapeCoordinates G C (realizeShapes G I C a i) = UniformProductSupport.evaluate (R := ℤ) (S := List G) (M := C × G →₀ ℤ) i a := by
  exact (shapeCoordinates G C).apply_symm_apply _

lemma realizeShapes_apply_relative (a : List G →₀ CoefficientProduct G I C)
    (i : I) (c : C) (s : Simplex G) :
    realizeShapes G I C a i c s = a (relativeType G s) i (c,s.1) := by
  rw [← shapeCoordinates_at_relative,shapeCoordinates_realize]
  rfl

lemma realizeShapes_apply (a : List G →₀ CoefficientProduct G I C)
    (i : I) (c : C) (g : G) (l : List G) :
    realizeShapes G I C a i c (g,l.map (fun x => g*x)) = a l i (c,g) := by
  rw [realizeShapes_apply_relative,relativeType_translate]

def shapeDomain (n : ℕ) :=
  Finsupp.supported (CoefficientProduct G I C) ℤ {l : List G | l.length = n}

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductCoefficient
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains
section
variable (G C : Type*) [Group G]

def place : (C × G →₀ ℤ) →ₗ[ℤ] (Chain G →ₗ[ℤ] (C →₀ Chain G)) :=
  Finsupp.linearCombination ℤ
    (fun p : C × G => (Finsupp.lsingle p.1).comp (mapChain G (fun x => p.2*x)))

@[simp] lemma place_single (c : C) (u : G) (r : ℤ) (z : Chain G) :
    place G C (Finsupp.single (c,u) r) z =
      r • Finsupp.single c (mapChain G (fun x => u*x) z) := by
  simp [place]

lemma boundary_place (a : C × G →₀ ℤ) (z : Chain G) :
    cosetBoundary G (place G C a z) = place G C a (boundary G z) := by
  have h : (cosetBoundary G).comp ((place G C).flip z) =
      (place G C).flip (boundary G z) := by
    apply Finsupp.lhom_ext
    rintro ⟨c,u⟩ r
    simp only [LinearMap.comp_apply,LinearMap.flip_apply,place_single,map_smul,
      cosetBoundary_single,boundary_mapChain]
  exact LinearMap.congr_fun h a

lemma place_rightShift_translate (a : C × G →₀ ℤ) (z : Chain G) (g : G) :
    place G C (ProductCoefficient.rightShift G C g a)
      (mapChain G (fun x => g*x) z) = place G C a z := by
  have h : ((place G C).flip (mapChain G (fun x => g*x) z)).comp
      (ProductCoefficient.rightShift G C g) = (place G C).flip z := by
    apply Finsupp.lhom_ext
    rintro ⟨c,u⟩ r
    simp only [LinearMap.comp_apply,LinearMap.flip_apply,
      ProductCoefficient.rightShift_single,place_single,mapChain_comp]
    congr 3
    apply congrArg (mapChain G)
    funext x
    simp [mul_assoc]
  exact LinearMap.congr_fun h a

end

section
variable (G I C : Type*) [Group G]

@[simp] lemma shapeCoordinates_single (c : C) (s : Simplex G) (r : ℤ) :
    shapeCoordinates G C (Finsupp.single c (Finsupp.single s r)) =
      Finsupp.single (relativeType G s) (Finsupp.single (c,s.1) r) := by
  classical
  simp [shapeCoordinates,shapeBasisEquiv]

end

variable (G : Type*)

def tupleBasisEquiv (n : ℕ) : (Fin (n+1) → G) ≃ {s : Simplex G // degree G s = n} where
  toFun c := ⟨(c 0,List.ofFn (fun i : Fin n => c i.succ)),List.length_ofFn⟩
  invFun s := Fin.cons s.val.1 (fun i => s.val.2.get ⟨i.val,by have hs : s.val.2.length = n := s.property; omega⟩)
  left_inv := by
    intro c
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp
  right_inv := by
    rintro ⟨⟨g,l⟩,hl⟩
    apply Subtype.ext
    change (g,List.ofFn (fun i : Fin n => l.get ⟨i.val,_⟩)) = (g,l)
    have he : n = l.length := hl.symm
    subst n
    exact congrArg (fun l => (g,l)) List.ofFn_getElem

def tupleChainEquiv (n : ℕ) : ((Fin (n+1) → G) →₀ ℤ) ≃ₗ[ℤ] degreeModule G n :=
  (Finsupp.lcongr (tupleBasisEquiv G n) (LinearEquiv.refl ℤ ℤ)).trans
    (Finsupp.supportedEquivFinsupp {s : Simplex G | degree G s = n}).symm

@[simp] lemma tupleChainEquiv_single (n : ℕ) (c : Fin (n+1) → G) (r : ℤ) :
    (tupleChainEquiv G n (Finsupp.single c r)).val =
      Finsupp.single (c 0,List.ofFn (fun i : Fin n => c i.succ)) r := by
  change ((Finsupp.supportedEquivFinsupp {s : Simplex G | degree G s = n}).symm
    ((Finsupp.lcongr (tupleBasisEquiv G n) (LinearEquiv.refl ℤ ℤ)) (Finsupp.single c r))).val = _
  rw [Finsupp.lcongr_single,Finsupp.supportedEquivFinsupp_symm_single]
  rfl

def fromTuples (n : ℕ) : ((Fin (n+1) → G) →₀ ℤ) →ₗ[ℤ] Chain G :=
  (degreeModule G n).subtype.comp (tupleChainEquiv G n).toLinearMap

@[simp] lemma fromTuples_single (n : ℕ) (c : Fin (n+1) → G) (r : ℤ) :
    fromTuples G n (Finsupp.single c r) =
      Finsupp.single (c 0,List.ofFn (fun i : Fin n => c i.succ)) r :=
  tupleChainEquiv_single G n c r

end ListChains

open _root_.CategoryTheory

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_Representation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory

namespace ListChains
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable (G I C : Type) [Group G]

lemma mapChain_relative_tuple (n : ℕ) (s : Fin (n+1) → G) :
    mapChain G (fun x => s 0*x)
      (Finsupp.single (1,List.ofFn (fun i : Fin n => (s 0)⁻¹*s i.succ)) 1) =
        fromTuples G n (Finsupp.single s 1) := by
  simp only [fromTuples_single,mapChain_single,List.map_ofFn,mul_one]
  congr 3
  funext i
  exact mul_inv_cancel_left _ _

lemma place_shifted_tuple (n : ℕ) (s : Fin (n+1) → G) (a : C × G →₀ ℤ) :
    place G C (ProductCoefficient.rightShift G C (s 0)⁻¹ a)
      (Finsupp.single (1,List.ofFn (fun i : Fin n => (s 0)⁻¹*s i.succ)) 1) =
        place G C a (fromTuples G n (Finsupp.single s 1)) := by
  rw [← mapChain_relative_tuple]
  have h := place_rightShift_translate G C
    (ProductCoefficient.rightShift G C (s 0)⁻¹ a)
    (Finsupp.single (1,List.ofFn (fun i : Fin n => (s 0)⁻¹*s i.succ)) 1) (s 0)
  have he : ProductCoefficient.rightShift G C (s 0)
      (ProductCoefficient.rightShift G C (s 0)⁻¹ a) = a := by
    rw [← LinearMap.comp_apply,← ProductCoefficient.rightShift_mul,mul_inv_cancel,
      ProductCoefficient.rightShift_one,LinearMap.id_apply]
  rw [he] at h
  exact h.symm

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StandardShapiro
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct

namespace FunctionalTree

open _root_.CategoryTheory
variable {R G V : Type*} [CommRing R] [Group G] [MulAction G V]
variable (A : Rep R G)

variable (p : V → V) (peq : ∀ (g : G) (v : V), p (g • v) = g • p v)

def equivariantComplex : ShortComplex (Rep R G) :=
  ShortComplex.mk (boundaryHom A p peq) (augmentationHom A) (by
    ext z
    exact augmentation_boundary p z)

end FunctionalTree

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FiniteIndexRegular
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteIndexRegular
open _root_.CategoryTheory _root_.OAI.CategoryTheory _root_.Representation _root_.OAI.Representation FiniteExtension
variable {L : Type} [Group L] (K : Subgroup L) [K.Normal] (I : Type)
open scoped Classical TensorProduct MonoidAlgebra

noncomputable def embedLM : RegularProductR.Module ℤ K I →ₗ[ℤ]
    RegularProductR.Module ℤ L I :=
  LinearMap.pi (fun i => (Finsupp.lmapDomain ℤ ℤ ((↑) : K → L)).comp (LinearMap.proj i))

noncomputable def slices (c : Q K) : RegularProductR.Module ℤ L I →ₗ[ℤ]
    RegularProductR.Module ℤ K I :=
  LinearMap.pi (fun i => (slice K c).comp (LinearMap.proj i))

lemma slice_map (c : Q K) (h : L) :
    (slice K c).comp (Finsupp.lmapDomain ℤ ℤ (fun k : K => (k : L)*h)) =
      if c = pi K h then RegularProductR.rightShift ℤ K (factor K h)⁻¹ else 0 := by
  classical
  apply Finsupp.lhom_ext
  intro k z
  by_cases hc : c = pi K h
  · subst c
    simp [slice_single]
  · simp [slice_single, hc]

end FiniteIndexRegular

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ContextualCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding.Source
noncomputable section
open FiniteAlgebraicEnvelopes Bootstrap Compiler Compiler.Simulator MachineRealization
open BoundedEncoding NamedAction
open scoped Classical

abbrev Sigma := ThreeCodes.Alphabet

end
end SimpleFInftyOvergroups.ContextualEncoding.Source

end OAI
end


