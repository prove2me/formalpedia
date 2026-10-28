-- Prove2me | Definitions.Def_OAIEGC003
-- name    : OAIEGC003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T03:00:33.082358+00:00
-- url     : https://prove2.me/theorems/ee34351e-682d-4385-8580-b3916d7af69b
-- title:
--   Definitions bundle OAIEGC003 of the split of OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, carved from OpenAI's openai/math development (OpenAI, *A finitely generated counterexample to the Eilenberg–Ganea conjecture*, OpenAI Math Release, September 23, 2026, result family 249, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 16 definitions and 14 theorems. The definitions and types are `OAI.EilenbergGanea.SeedConnection.boundaryEdgeWord`, `OAI.EilenbergGanea.SeedConnection.boundaryWords`, `OAI.EilenbergGanea.SeedConnection.cellRank`, `OAI.EilenbergGanea.SeedConnection.edgeAnchor`, `OAI.EilenbergGanea.cycleSumEquiv`, `OAI.EilenbergGanea.deletedInclusion`, `OAI.EilenbergGanea.evaluatedNormalFactor`, `OAI.EilenbergGanea.optionBackward`, `OAI.EilenbergGanea.quotientChainEquiv`, `OAI.EilenbergGanea.relatorFactorValue`, `OAI.EilenbergGanea.relatorSignedCounts`, `OAI.EilenbergGanea.signedUnit`, `OAI.EilenbergGanea.unitExtensionBasis`, `OAI.EilenbergGanea.wordBasisTransport`, `OAI.EilenbergGanea.wordChainEquiv`, `OAI.EilenbergGanea.wordCycleEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory, in whole or in part: [`PresentationAlignment`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/PresentationAlignment.lean), [`PresentationComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/PresentationComparison.lean), [`RightAngledArtin_ResidualFiniteness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/RightAngledArtin/ResidualFiniteness.lean), [`SeedConnection`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedConnection.lean), [`SmallHolonomy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SmallHolonomy.lean).
--
--   **Imports.** It imports the published bundle `Def_EilenbergGanea`; the bundles `OAIEG011` and `OAIEG018` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIEGC004`; the proofs of `OAI.EilenbergGanea.aligned_presentation_small_transport`, `OAI.EilenbergGanea.artin_residuallyFinite` and `OAI.EilenbergGanea.boundary_basis_small_transport`.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_EilenbergGanea
import Definitions.Def_OAIEG011
import Definitions.Def_OAIEG018

section
-- module Solutions.OAIEG.RightAngledArtin_ResidualFiniteness
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
universe u
/-! Finite permutation separation for free groups. -/

section ArtinOption

variable {V : Type*} (L : SimpleGraph (Option V))

def deletedInclusion : deletedGroup L →* ArtinGroup L :=
  artinMap (deletedGraph L) L Option.some (fun _ _ h => h)

theorem link_commutes_new (c : deletedGroup L) (hc : c ∈ linkSubgroup L) :
    Commute (deletedInclusion L c) (artinGenerator L none) := by
  have hle : linkSubgroup L ≤
      (Subgroup.centralizer {artinGenerator L none}).comap (deletedInclusion L) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨v, hv, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa [deletedInclusion, artinMap] using (adjacent_generators_commute L hv).symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hc))

def optionBackward : optionSemidirect L →* ArtinGroup L :=
  cosetSemidirectLift (linkSubgroup L) (deletedInclusion L) (artinGenerator L none)
    (link_commutes_new L)

end ArtinOption


end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.SmallHolonomy
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

open scoped Quaternion

namespace EilenbergGanea
open scoped Quaternion

def signedUnit (b : SU2) (ε : Bool) : SU2 := if ε then b else b⁻¹

def relatorFactorValue {I : Type*} (x : I → SU2) (r : RelatorFactor I) : SU2 :=
  r.1 * signedUnit (x r.2.1) r.2.2 * r.1⁻¹

def relatorSignedCounts {I : Type*} (l : List (RelatorFactor I)) : I →₀ ℤ :=
  (l.map (fun r => Finsupp.single r.2.1 (if r.2.2 then 1 else -1))).sum

end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.PresentationComparison
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
section EvaluatedNormalExpression
open scoped Quaternion
variable {Γ D S R : Type*} [Group Γ] [Group D]

def evaluatedNormalFactor (v : S → Γ) (a : Γ → S → SU2)
    (f : NormalFactor S R) (g : Γ) : RelatorFactor (Γ × R) :=
  (pathProduct v a f.1 g, (g * wordValue v f.1, f.2.1), f.2.2)

end EvaluatedNormalExpression
end EilenbergGanea

namespace EilenbergGanea

section QuotientChains
variable {Γ F R S T : Type*} [Group Γ] [Group F]

theorem translateChains_mul (g h : Γ) (c : BasedChains Γ S) :
    translateChains (g*h) c = translateChains g (translateChains h c) := by
  have he : (translateChains (g*h) : BasedChains Γ S →ₗ[ℤ] _) =
      (translateChains g).comp (translateChains h) := by
    apply Finsupp.lhom_ext
    rintro ⟨p,s⟩ n
    simp [mul_assoc]
  exact LinearMap.congr_fun he c

theorem quotientChains_translate (q : Γ →* F) (g : Γ) (c : BasedChains Γ S) :
    quotientChains q (translateChains g c) = translateChains (q g) (quotientChains q c) := by
  have he : (quotientChains q).comp (translateChains g) =
      ((translateChains (q g)).comp (quotientChains q) : BasedChains Γ S →ₗ[ℤ] _) := by
    apply Finsupp.lhom_ext
    rintro ⟨p,s⟩ n
    simp
  exact LinearMap.congr_fun he c

theorem quotientMatrix_equivariant (q : Γ →* F)
    (A : BasedChains Γ R →ₗ[ℤ] BasedChains Γ S) : ChainsEquivariant (quotientMatrix q A) := by
  intro f c
  have he : (quotientMatrix q A).comp (translateChains f) =
      (translateChains f).comp (quotientMatrix q A) := by
    apply Finsupp.lhom_ext
    rintro ⟨p,r⟩ n
    simp only [LinearMap.comp_apply, translateChains_single, quotientMatrix_single,
      map_smul, translateChains_mul]
  exact LinearMap.congr_fun he c

theorem quotientMatrix_natural (q : Γ →* F)
    (A : BasedChains Γ R →ₗ[ℤ] BasedChains Γ S) (hA : ChainsEquivariant A)
    (c : BasedChains Γ R) :
    quotientMatrix q A (quotientChains q c) = quotientChains q (A c) := by
  have he : (quotientMatrix q A).comp (quotientChains q) = (quotientChains q).comp A := by
    apply Finsupp.lhom_ext
    rintro ⟨g,r⟩ n
    have hb : Finsupp.single (g,r) n =
        n • translateChains g (Finsupp.single (1,r) (1 : ℤ)) := by simp
    simp only [LinearMap.comp_apply, quotientChains_single, quotientMatrix_single]
    rw [hb, map_smul, map_smul, hA, quotientChains_translate]
  exact LinearMap.congr_fun he c

theorem quotientMatrix_comp (q : Γ →* F)
    (A : BasedChains Γ R →ₗ[ℤ] BasedChains Γ S)
    (B : BasedChains Γ S →ₗ[ℤ] BasedChains Γ T) (hB : ChainsEquivariant B) :
    quotientMatrix q (B.comp A) = (quotientMatrix q B).comp (quotientMatrix q A) := by
  apply Finsupp.lhom_ext
  rintro ⟨f,r⟩ n
  simp only [LinearMap.comp_apply, quotientMatrix_single, map_smul]
  rw [quotientMatrix_equivariant q B f, quotientMatrix_natural q B hB]

theorem quotientMatrix_id (q : Γ →* F) :
    quotientMatrix q (LinearMap.id : BasedChains Γ R →ₗ[ℤ] _) = LinearMap.id := by
  apply Finsupp.lhom_ext
  rintro ⟨f,r⟩ n
  simp

/-- Tensoring an isomorphism is an isomorphism. This finite-column proof makes
no assertion that the quotient group ring is a flat module. -/
def quotientChainEquiv (q : Γ →* F) (A : BasedChains Γ R ≃ₗ[ℤ] BasedChains Γ S)
    (hA : ChainsEquivariant A.toLinearMap) : BasedChains F R ≃ₗ[ℤ] BasedChains F S where
  __ := quotientMatrix q A.toLinearMap
  invFun := quotientMatrix q A.symm.toLinearMap
  left_inv c := by
    have he := quotientMatrix_comp q A.toLinearMap A.symm.toLinearMap (ChainsEquivariant.symm A hA)
    have hi : A.symm.toLinearMap.comp A.toLinearMap = LinearMap.id := by ext; simp
    rw [hi, quotientMatrix_id] at he
    exact (LinearMap.congr_fun he c).symm
  right_inv c := by
    have he := quotientMatrix_comp q A.symm.toLinearMap A.toLinearMap hA
    have hi : A.toLinearMap.comp A.symm.toLinearMap = LinearMap.id := by ext; simp
    rw [hi, quotientMatrix_id] at he
    exact (LinearMap.congr_fun he c).symm

end QuotientChains
end EilenbergGanea



end

end OAI
end

section
-- module Solutions.OAIEG.PresentationAlignment
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

/-! Actual word and cycle-basis alignment. -/

namespace EilenbergGanea
section CycleSpaces
variable {Γ S T U R : Type*} [Group Γ]

/-- Naturality of the actual path chain under arbitrary finite-word substitution. -/
theorem pathChain_substitution (v : T → Γ) (f : S → FreeGroup T)
    (w : FreeGroup S) (g : Γ) :
    relatorChainMap v f (pathChain (fun s => wordValue v (f s)) w g) =
      pathChain v (FreeGroup.lift f w) g := by
  induction w using OAI.freeGroupInductionOn generalizing g with
  | one => simp
  | of s => simp
  | inv_of s _ih =>
      simp only [pathChain_inv,map_neg,pathChain_of,relatorChainMap_single,one_smul,
        map_inv,FreeGroup.lift_apply_of,wordValue]
  | mul w z hw hz =>
      rw [pathChain_mul,map_add,hw,hz,map_mul,pathChain_mul,wordValue_substitution]

@[simp] theorem relatorChainMap_of (v : S → Γ) :
    relatorChainMap v FreeGroup.of = LinearMap.id := by
  apply Finsupp.lhom_ext
  rintro ⟨g,s⟩ n
  simp

end CycleSpaces
end EilenbergGanea

namespace EilenbergGanea
section TrivialGenerators
variable {Γ S T : Type*} [Group Γ]

theorem edgeBoundary_sum_trivial (v : S → Γ) (c : BasedChains Γ (S ⊕ T)) :
    edgeBoundary (Sum.elim v (fun _ : T => 1)) c =
      edgeBoundary v (sumChainsEquiv c).1 := by
  have h : edgeBoundary (Sum.elim v (fun _ : T => 1)) =
      (edgeBoundary v).comp ((LinearMap.fst ℤ _ _).comp sumChainsEquiv.toLinearMap) := by
    apply Finsupp.lhom_ext
    rintro ⟨g,s | t⟩ n <;> simp
  exact LinearMap.congr_fun h c

/-- A trivial extra generator contributes an
independent free summand to the cycle module, with no cardinality restriction. -/
def cycleSumEquiv (v : S → Γ) :
    cycles (Sum.elim v (fun _ : T => 1)) ≃ₗ[ℤ] cycles v × BasedChains Γ T where
  toFun c := (⟨(sumChainsEquiv c.val).1, by
    rw [LinearMap.mem_ker, ← edgeBoundary_sum_trivial]
    exact c.property⟩, (sumChainsEquiv c.val).2)
  invFun c := ⟨sumChainsEquiv.symm (c.1.val,c.2), by
    rw [LinearMap.mem_ker,edgeBoundary_sum_trivial,LinearEquiv.apply_symm_apply]
    exact c.1.property⟩
  left_inv c := by
    apply Subtype.ext
    exact sumChainsEquiv.symm_apply_apply c.val
  right_inv c := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (sumChainsEquiv.apply_symm_apply (c.1.val,c.2))
    · exact congrArg (fun p : BasedChains Γ S × BasedChains Γ T => p.2) (sumChainsEquiv.apply_symm_apply (c.1.val,c.2))
  map_add' c d := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (sumChainsEquiv.map_add c.val d.val)
    · exact congrArg (fun p : BasedChains Γ S × BasedChains Γ T => p.2) (sumChainsEquiv.map_add c.val d.val)
  map_smul' n c := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (sumChainsEquiv.map_smul n c.val)
    · exact congrArg (fun p : BasedChains Γ S × BasedChains Γ T => p.2) (sumChainsEquiv.map_smul n c.val)

end TrivialGenerators
end EilenbergGanea

namespace EilenbergGanea
section WordEquivalence
variable {Γ S T : Type*} [Group Γ]

theorem pathChain_hom (v : S → Γ) (w : T → Γ) (e : FreeGroup S →* FreeGroup T)
    (he : (wordValue w).comp e = wordValue v) (a : FreeGroup S) (g : Γ) :
    relatorChainMap w (fun s => e (FreeGroup.of s)) (pathChain v a g) =
      pathChain w (e a) g := by
  have hv : (fun s => wordValue w (e (FreeGroup.of s))) = v := by
    funext s
    simpa [wordValue] using DFunLike.congr_fun he (FreeGroup.of s)
  have hl : FreeGroup.lift (fun s => e (FreeGroup.of s)) = e := by
    apply FreeGroup.ext_hom
    intro s
    simp
  rw [← hv,pathChain_substitution,hl]

theorem edgeBoundary_hom (v : S → Γ) (w : T → Γ) (e : FreeGroup S →* FreeGroup T)
    (he : (wordValue w).comp e = wordValue v) :
    (edgeBoundary w).comp (relatorChainMap w (fun s => e (FreeGroup.of s))) = edgeBoundary v := by
  apply Finsupp.lhom_ext
  rintro ⟨g,s⟩ n
  have hs : wordValue w (e (FreeGroup.of s)) = v s := by
    simpa [wordValue] using DFunLike.congr_fun he (FreeGroup.of s)
  simp [edgeBoundary_pathChain,hs]

/-- An honest free-generator equivalence gives an invertible integral edge-chain
map; the path chains, not only their augmented exponent sums, are transported. -/
def wordChainEquiv (v : S → Γ) (w : T → Γ) (e : FreeGroup S ≃* FreeGroup T)
    (he : (wordValue w).comp e.toMonoidHom = wordValue v) :
    BasedChains Γ S ≃ₗ[ℤ] BasedChains Γ T where
  __ := relatorChainMap w (fun s => e (FreeGroup.of s))
  invFun := relatorChainMap v (fun t => e.symm (FreeGroup.of t))
  left_inv c := by
    have hi : (wordValue v).comp e.symm.toMonoidHom = wordValue w := by
      ext t
      have h := DFunLike.congr_fun he (e.symm (FreeGroup.of t))
      simpa using h.symm
    have hh : (relatorChainMap v (fun t => e.symm (FreeGroup.of t))).comp
        (relatorChainMap w (fun s => e (FreeGroup.of s))) = LinearMap.id := by
      apply Finsupp.lhom_ext
      rintro ⟨g,s⟩ n
      simp only [LinearMap.comp_apply, relatorChainMap_single, map_zsmul,
        LinearMap.id_coe, id_eq]
      have hh := pathChain_hom w v e.symm.toMonoidHom hi (e (FreeGroup.of s)) g
      simpa using congrArg (n • ·) hh
    exact LinearMap.congr_fun hh c
  right_inv c := by
    have hh : (relatorChainMap w (fun s => e (FreeGroup.of s))).comp
        (relatorChainMap v (fun t => e.symm (FreeGroup.of t))) = LinearMap.id := by
      apply Finsupp.lhom_ext
      rintro ⟨g,t⟩ n
      simp only [LinearMap.comp_apply, relatorChainMap_single, map_zsmul,
        LinearMap.id_coe, id_eq]
      have hh := pathChain_hom v w e.toMonoidHom he (e.symm (FreeGroup.of t)) g
      simpa using congrArg (n • ·) hh
    exact LinearMap.congr_fun hh c

/-- Invertible change of free generators preserves the full cycle module. -/
def wordCycleEquiv (v : S → Γ) (w : T → Γ) (e : FreeGroup S ≃* FreeGroup T)
    (he : (wordValue w).comp e.toMonoidHom = wordValue v) : cycles v ≃ₗ[ℤ] cycles w :=
  (wordChainEquiv v w e he).ofSubmodules (cycles v) (cycles w) (by
    ext c
    rw [Submodule.mem_map_equiv]
    change edgeBoundary v ((wordChainEquiv v w e he).symm c) = 0 ↔ edgeBoundary w c = 0
    have h := LinearMap.congr_fun (edgeBoundary_hom v w e.toMonoidHom he)
      ((wordChainEquiv v w e he).symm c)
    change edgeBoundary w (wordChainEquiv v w e he ((wordChainEquiv v w e he).symm c)) =
      edgeBoundary v ((wordChainEquiv v w e he).symm c) at h
    rw [LinearEquiv.apply_symm_apply] at h
    rw [← h])

end WordEquivalence
end EilenbergGanea

namespace EilenbergGanea
section UnitExtensionBasis
variable {Γ S T R : Type*} [Group Γ]

/-- Completely explicit stabilization of a boundary-basis presentation. -/
def unitExtensionBasis (v : S → Γ) (B : BasedChains Γ R ≃ₗ[ℤ] cycles v) :
    BasedChains Γ (R ⊕ T) ≃ₗ[ℤ] cycles (Sum.elim v (fun _ : T => 1)) :=
  sumChainsEquiv.trans ((B.prodCongr (LinearEquiv.refl ℤ (BasedChains Γ T))).trans
    (cycleSumEquiv v).symm)

end UnitExtensionBasis
end EilenbergGanea

namespace EilenbergGanea
section Nielsen
variable {Γ S T A R : Type*} [Group Γ]

def wordBasisTransport (v : S → Γ) (w : T → Γ)
    (e : FreeGroup S ≃* FreeGroup T)
    (he : (wordValue w).comp e.toMonoidHom = wordValue v)
    (B : BasedChains Γ R ≃ₗ[ℤ] cycles v) : BasedChains Γ R ≃ₗ[ℤ] cycles w :=
  B.trans (wordCycleEquiv v w e he)

end Nielsen
end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.SeedConnection
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible _root_.OAI.EilenbergGanea.SeedEncoding.properFaceDecidable _root_.OAI.EilenbergGanea.SeedEncoding.seedAdjDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
namespace SeedConnection

def boundaryEdgeWord (s : Sector) : FreeGroup Bool :=
  if (sectorLetter s).2 then circleWord (sectorCircleEdge s) else
    (circleWord (sectorCircleEdge s))⁻¹

def boundaryWords (r : Bool) : List (FreeGroup Bool) :=
  List.ofFn (fun i : Fin (boundaryLength r) => boundaryEdgeWord ⟨r,i⟩)

@[simp] theorem boundaryWords_length (r : Bool) : (boundaryWords r).length = boundaryLength r :=
  List.length_ofFn

@[simp] theorem boundaryWords_get (s : Sector) :
    (boundaryWords s.1)[s.2.val]'(by simp) = boundaryEdgeWord s := by
  simp [boundaryWords]

def edgeAnchor : SeedEdge → SeedVertex
  | .inl e => .inl (circleStart e)
  | .inr s => .inr s.1

def cellRank : SeedCell → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

end SeedConnection



end EilenbergGanea

end

end OAI
end


