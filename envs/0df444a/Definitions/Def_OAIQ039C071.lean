-- Prove2me | Definitions.Def_OAIQ039C071
-- name    : OAIQ039C071
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:22:29.05482+00:00
-- url     : https://prove2.me/theorems/80924944-654c-483b-8ae7-f4d9002e26cb
-- title:
--   Definitions bundle OAIQ039C071 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 3 definitions and 4 theorems. The definitions and types are `OAI.Kadison.MatrixTower.generated`, `OAI.Kadison.MatrixTower.generatedStage`, `OAI.Kadison.MatrixTower.stageHom`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_EqualTraceRefinement`, `Commutator_IrreducibleMatrixTower`, `Commutator_MatrixTowerClosure`.
--
--   **Imports.** It imports the bundle `OAIQ039C066` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ039C073`; the statements `OAI.Kadison.MatrixTower.generated_factor`, `OAI.Kadison.MatrixTower.original_copies_average`, `OAI.Kadison.MatrixTower.original_copies_generated` and `OAI.Kadison.MatrixTower.original_gns_generated`; the proofs of `OAI.Kadison.MatrixTower.original_copies_average`, `OAI.Kadison.MatrixTower.original_copies_generated` and `OAI.Kadison.MatrixTower.original_gns_generated`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C066

section
-- module Solutions.OAIQ039_CM.Commutator_EqualTraceRefinement
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.NormalGNS

open ProjectionSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (hnormal : BoundedWOTContinuous M τ)

variable (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)

variable {J : Type} [Fintype J]

include hτ hnormal hfaith hone in
theorem equal_trace_refinement (hM : DiffuseProjection.HasNoMinimalProjections M)
    (p : J → M) (hp : ∀ j,IsStarProjection (p j))
    (horth : ∀ j k,j≠k → p j*p k=0) (hsum : ∑ j,p j=1)
    (b : ℕ) (hb : 0<b) :
    ∃ (I : Type) (_ : Fintype I) (q : I → M) (s : J → M),
      (∀ i,IsStarProjection (q i) ∧ (τ (q i)).re=1/(b:ℝ)) ∧
      (∀ i k,i≠k → q i*q k=0) ∧ (∑ i,q i)=1 ∧
      (∀ j,IsStarProjection (s j) ∧ s j≤p j ∧ (τ (p j-s j)).re<1/(b:ℝ) ∧
        s j∈StarAlgebra.adjoin ℂ (Set.range q)) := by
  classical
  have hbR : (0:ℝ)<b := Nat.cast_pos.mpr hb
  choose n s hs hsp hts herror using fun j =>
    exists_rational_subprojection M τ hτ hnormal hfaith hM (p j) (hp j) b hb
  have hsorth : ∀ j k,j≠k → s j*s k=0 := fun j k hjk =>
    subprojections_orthogonal (hs j) (hs k) (hp j) (hp k) (hsp j) (hsp k) (horth j k hjk)
  let S : M := ∑ j,s j
  have hS : IsStarProjection S := projection_sum s hs hsorth
  have hSle : S≤1 := by simpa only [hsum] using projection_sum_le s p hsp
  have htS : (τ S).re=(∑ j,n j : ℕ)/(b:ℝ) := by
    change (τ (∑ j,s j)).re=_
    rw [map_sum]
    change Complex.reAddGroupHom (∑ j,τ (s j))=_
    rw [map_sum]
    change (∑ j,(τ (s j)).re)=_
    simp only [hts,←Finset.sum_div,Nat.cast_sum]
  have hN : (∑ j,n j)≤b := by
    have hnonneg := (τ.map_nonneg (sub_nonneg.mpr hSle)).1
    rw [map_sub,Complex.sub_re,hone,Complex.one_re,Complex.zero_re,htS] at hnonneg
    have h : ((∑ j,n j : ℕ):ℝ)≤(b:ℝ) := by
      have hh := (div_le_iff₀ hbR).mp (show ((∑ j,n j : ℕ):ℝ)/(b:ℝ)≤1 by linarith)
      simpa only [one_mul] using hh
    exact_mod_cast h
  let m : ℕ := b-∑ j,n j
  have hrem : IsStarProjection (1-S) := hS.one_sub
  have htrem : (τ (1-S)).re=(m:ℝ)*(1/(b:ℝ)) := by
    rw [map_sub,Complex.sub_re,hone,Complex.one_re,htS]
    dsimp [m]
    rw [Nat.cast_sub hN]
    field_simp
  have hpart (j : J) : ∃ r : Fin (n j) → M,
      (∀ k,IsStarProjection (r k) ∧ r k ≤ s j ∧ (τ (r k)).re=1/(b:ℝ)) ∧
      (∀ k l,k≠l → r k*r l=0) ∧ ∑ k,r k=s j := by
    apply exists_projection_partition M τ hτ hnormal hfaith hM (n j) (s j) (hs j)
      (by positivity : (0:ℝ)≤1/(b:ℝ))
    rw [hts]; ring
  choose r hr hrorth hrsum using hpart
  obtain ⟨z,hz,hzorth,hzsum⟩ := exists_projection_partition M τ hτ hnormal hfaith hM
    m (1-S) hrem (by positivity : (0:ℝ)≤1/(b:ℝ)) htrem
  let I := (Σ j : J,Fin (n j)) ⊕ Fin m
  let q : I → M := Sum.elim (fun i => r i.1 i.2) z
  have hleS (j : J) (k : Fin (n j)) : r j k≤S :=
    (hr j k).2.1.trans (Finset.single_le_sum (fun l _ => (hs l).nonneg) (Finset.mem_univ j))
  have hcross (j : J) (k : Fin (n j)) (l : Fin m) : r j k*z l=0 :=
    subprojections_orthogonal (hr j k).1 (hz l).1 hS hrem (hleS j k) (hz l).2.1
      hS.mul_one_sub_self
  refine ⟨I,inferInstance,q,s,?_,?_,?_,?_⟩
  · intro i
    cases i with
    | inl i => exact ⟨(hr i.1 i.2).1,(hr i.1 i.2).2.2⟩
    | inr i => exact ⟨(hz i).1,(hz i).2.2⟩
  · intro i k hik
    cases i with
    | inl i =>
      cases k with
      | inl k =>
        obtain ⟨j,a⟩ := i
        obtain ⟨l,c⟩ := k
        change r j a*r l c=0
        by_cases hjl : j=l
        · subst l
          exact hrorth j a c (fun hac => hik (by subst c; rfl))
        · exact subprojections_orthogonal (hr j a).1 (hr l c).1 (hs j) (hs l)
            (hr j a).2.1 (hr l c).2.1 (hsorth j l hjl)
      | inr k => exact hcross i.1 i.2 k
    | inr i =>
      cases k with
      | inl k =>
        change z i*r k.1 k.2=0
        simpa only [star_mul,(hr k.1 k.2).1.isSelfAdjoint.star_eq,
          (hz i).1.isSelfAdjoint.star_eq,star_zero] using congrArg star (hcross k.1 k.2 i)
      | inr k => exact hzorth i k (fun he => hik (congrArg Sum.inr he))
  · change (∑ i : (Σ j : J,Fin (n j)) ⊕ Fin m,Sum.elim (fun i => r i.1 i.2) z i)=1
    rw [Fintype.sum_sum_type,Fintype.sum_sigma]
    change (∑ j,∑ k,r j k)+(∑ k,z k)=1
    simp only [hrsum,hzsum]
    change S+(1-S)=1
    abel
  · intro j
    refine ⟨hs j,hsp j,herror j,?_⟩
    rw [←hrsum j]
    apply (StarAlgebra.adjoin ℂ (Set.range q)).sum_mem
    intro k hk
    exact StarAlgebra.subset_adjoin ℂ (Set.range q) ⟨Sum.inl ⟨j,k⟩,rfl⟩

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTowerClosure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

def generated : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (stageAlgebra M F : Set (H →L[ℂ] H)))
  centralizer_centralizer' := by
    have h : ((StarSubalgebra.centralizer ℂ
        (StarSubalgebra.centralizer ℂ (stageAlgebra M F : Set (H →L[ℂ] H)))) :
        StarSubalgebra ℂ (H →L[ℂ] H)).carrier =
        Set.centralizer (Set.centralizer (stageAlgebra M F : Set (H →L[ℂ] H))) := by
      exact (StarSubalgebra.coe_centralizer_centralizer ℂ _).trans (by
        rw [StarMemClass.star_coe_eq,Set.union_self])
    change _ = ((StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (stageAlgebra M F : Set (H →L[ℂ] H)))) :
      StarSubalgebra ℂ (H →L[ℂ] H)).carrier
    rw [h]
    simp only [Set.centralizer_centralizer_centralizer]

lemma mem_generated (a : H →L[ℂ] H) : a∈generated M F ↔
    a∈Set.centralizer (Set.centralizer (stageAlgebra M F : Set (H →L[ℂ] H))) := by
  change a∈(StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (stageAlgebra M F : Set (H →L[ℂ] H)))) ↔ _
  rw [←SetLike.mem_coe,StarSubalgebra.coe_centralizer_centralizer,
    StarMemClass.star_coe_eq,Set.union_self]

lemma stageAlgebra_le : stageAlgebra M F≤M.toStarSubalgebra := by
  apply iSup_le
  intro n
  rintro a ⟨b,rfl⟩
  exact ((F n).hom b).property

lemma stage_mem (n : ℕ) (a : Matrix (F n).I (F n).I ℂ) : concreteStage M F n a∈generated M F := by
  apply (mem_generated M F _).mpr
  apply Set.subset_centralizer_centralizer
  exact (le_iSup (fun n => (concreteStage M F n).range) n) ⟨a,rfl⟩

def stageHom (n : ℕ) : Matrix (F n).I (F n).I ℂ →⋆ₐ[ℂ] generated M F :=
  (concreteStage M F n).codRestrict (generated M F).toStarSubalgebra (stage_mem M F n)

end Kadison.MatrixTower

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_IrreducibleMatrixTower
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def generatedStage (F : ℕ → Stage M) (n : ℕ) : Stage (generated M F) where
  I := (F n).I
  finite := (F n).finite
  dec := (F n).dec
  nonempty := (F n).nonempty
  hom := stageHom M F n

end Kadison.MatrixTower

end

end
end

end OAI
end


