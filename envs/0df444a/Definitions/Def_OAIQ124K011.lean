-- Prove2me | Definitions.Def_OAIQ124K011
-- name    : OAIQ124K011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:49:58.332999+00:00
-- url     : https://prove2.me/theorems/2a74d708-b6c1-406d-916d-53c5c12dc7cf
-- title:
--   Definitions bundle OAIQ124K011 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 196 declarations of OpenAI's Lean: 108 definitions, 3 inductive types or structures, 12 instances and 73 theorems. The definitions and types are `OAI.KLInvariance.BruhatGraph.costalkEquivDual`, `OAI.KLInvariance.BruhatGraph.fullKernel`, `OAI.KLInvariance.BruhatGraph.fullSubmodule`, `OAI.KLInvariance.BruhatGraph.incomingEquivInversions`, `OAI.KLInvariance.BruhatGraph.kernelEquivSingleSupport`, `OAI.KLInvariance.BruhatGraph.lowerCharacter`, `OAI.KLInvariance.BruhatGraph.mappedEdgeRoot`, `OAI.KLInvariance.BruhatGraph.normalizedKernel`, `OAI.KLInvariance.BruhatGraph.scaledInterval`, `OAI.KLInvariance.BruhatGraph.scaledStalk`, `OAI.KLInvariance.BruhatGraph.scheduleState`, `OAI.KLInvariance.BruhatGraph.stalkCharacter`, `OAI.KLInvariance.BruhatGraph.stateScale`, `OAI.KLInvariance.BruhatGraph.transportedSlope`, `OAI.KLInvariance.BruhatGraph.upperGraphInclusion`, `OAI.KLInvariance.BruhatGraph.upperIntervalIso`, `OAI.KLInvariance.BruhatGraph.upperSource`, `OAI.KLInvariance.BruhatGraph.upperTarget`, `OAI.KLInvariance.CanonicalP.defect`, `OAI.KLInvariance.CanonicalP.polynomial`, `OAI.KLInvariance.Dihedral.externalEdge`, `OAI.KLInvariance.Dihedral.inducedLabel`, `OAI.KLInvariance.Dihedral.inducedRoot`, `OAI.KLInvariance.Dihedral.interpolationRoot`, `OAI.KLInvariance.Dihedral.outgoingEquiv`, `OAI.KLInvariance.EdgeAlgebra.rootQuotientPolynomial`, `OAI.KLInvariance.FiniteIntervalModel.orderIso`, `OAI.KLInvariance.Graded.ModuleData.char`, `OAI.KLInvariance.Graded.character`, `OAI.KLInvariance.HeckeQ.dualR`, `OAI.KLInvariance.HeckeQ.rValue`, `OAI.KLInvariance.Hilbert.scalarDegreeEquiv`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Iso.kernelEquiv`, `OAI.KLInvariance.MomentGraph.GradedSheaf.ModelSum`, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnIso.extend`, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnIso.ofUniv`, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnIso.prodZero`, `OAI.KLInvariance.MomentGraph.GradedSheaf.freeKernelChar`, `OAI.KLInvariance.MomentGraph.GradedSheaf.freeStalkChar`, `OAI.KLInvariance.MomentGraph.GradedSheaf.kernelHilbert` and 71 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `KazhdanLusztig_CanonicalKL`, `KazhdanLusztig_CharacterReciprocity`, `KazhdanLusztig_Decomposition`, `KazhdanLusztig_Dihedral`, `KazhdanLusztig_DihedralIntervals`, `KazhdanLusztig_DyerPaths`, `KazhdanLusztig_EdgeLocalization`, `KazhdanLusztig_GradedModules`, `KazhdanLusztig_GradedSheaves`, `KazhdanLusztig_Hecke`, `KazhdanLusztig_Invariance`, `KazhdanLusztig_MinimalExtensions`, `KazhdanLusztig_OrdinaryR`, `KazhdanLusztig_PlaneLocalization`, `KazhdanLusztig_PositiveTransfer`, `KazhdanLusztig_ReflectionOrders`, `KazhdanLusztig_ReflectionSchedules`, `KazhdanLusztig_SheafMorphisms`, `KazhdanLusztig_Sheaves`, `KazhdanLusztig_SimultaneousInvariance`, `KazhdanLusztig_Support`, `KazhdanLusztig_TerminalKernels`.
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K004`, `OAIQ124K005`, `OAIQ124K006` and `OAIQ124K007` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ124K015`; the statements `OAI.KLInvariance.BruhatGraph.actual_comparison_of_upper_freeness`, `OAI.KLInvariance.BruhatGraph.actual_endpoint_of_rTilde_eq` and `OAI.KLInvariance.BruhatGraph.scaledStalk_reciprocity_upper`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K004
import Definitions.Def_OAIQ124K005
import Definitions.Def_OAIQ124K006
import Definitions.Def_OAIQ124K007

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Hecke
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hecke and Laurent actions, braid independence, bar involution, triangular support and inverse coefficients.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


namespace HeckeQ

open Hecke (Space basis end_ext)
variable {C : Type*} [CommRing C]

/-- R-value extracted from the genuine Hecke bar, with the classical sign
and leading q-power. No recurrence is imposed in this definition. -/
noncomputable def rValue (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) : C :=
  (-1 : C) ^ cs.length x * (-(q : C)) ^ cs.length y * barBasis cs q y x

end HeckeQ


end KLInvariance
end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_OrdinaryR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Construction of ordinary R-polynomials, left-simple recursion, degree bounds and inverse kernels.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}

namespace OrdinaryR

open LaurentPolynomial

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions_1
noncomputable def polynomial (cs : CoxeterSystem M W) (x y : W) : ℤ[X] :=
  LaurentPolynomial.trunc (HeckeQ.rValue cs variableUnit x y)

end OrdinaryR


end KLInvariance
end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CanonicalKL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical low-part construction, strict halfdegree, reciprocity and uniqueness; certification of the selected polynomials and interval ranks.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}

namespace CanonicalP

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions_2
/-- The standard lower-half KL recursion, on the actual Bruhat interval.
Its reciprocity will be proved from the genuine R-kernel, not stipulated. -/
noncomputable def polynomial (cs : CoxeterSystem M W) (x y : W) : ℤ[X] := by
  classical
  exact if BruhatLE cs x y then
    if x = y then 1 else
      -lowPart (rankDifference cs x y)
        (∑ z ∈ (properIntervalFinset cs x y).attach,
          OrdinaryR.polynomial cs x z.val * polynomial cs z.val y)
    else 0
termination_by rankDifference cs x y
decreasing_by
  have hz := (mem_properIntervalFinset cs x y z.val).mp z.property
  have hlt := length_lt_of_bruhat_ne cs hz.2.1 hz.2.2
  have hle := length_le_of_bruhat cs hz.1
  dsimp [rankDifference]
  omega

@[simp] theorem polynomial_diagonal (cs : CoxeterSystem M W) (x : W) :
    polynomial cs x x = 1 := by
  rw [polynomial]
  simp [bruhat_refl]

noncomputable def defect (cs : CoxeterSystem M W) (x y : W) : ℤ[X] :=
  ∑ z ∈ properIntervalFinset cs x y, OrdinaryR.polynomial cs x z * polynomial cs z y

end CanonicalP

end KLInvariance

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_GradedModules
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.pi_free _root_.OAI.KLInvariance.Graded.ModuleData.prod_free _root_.OAI.KLInvariance.Graded.ModuleData.shift_free
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded polynomial modules, projective presentations, finite homogeneous generators and uniqueness of minimal covers.
-/

section

namespace KLInvariance.Graded
open scoped Pointwise
universe uk ua um
variable {k : Type uk} {A : Type ua} {M : Type um} [Field k] [CommRing A] [klPreservedInstance9 : Algebra k A]
  [AddCommGroup M] [Module k M] [Module A M] [klPreservedInstance8 : IsScalarTower k A M]


theorem exists_homogeneous_basis_polynomial {σ : Type*} [Finite σ]
    [Module (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]
    [Module.Projective (MvPolynomial σ k) M] [Module.Finite (MvPolynomial σ k) M]
    (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul (polynomialGrading k σ) 𝓜]
    (d₀ : ℤ) (hbound : ∀ j < d₀, 𝓜 j = ⊥) :
    ∃ (ι : Type um), Finite ι ∧ ∃ b : Module.Basis ι (MvPolynomial σ k) M,
      ∀ i, ∃ d : ℤ, b i ∈ 𝓜 d := by
  exact exists_homogeneous_basis_connected (polynomialGrading k σ) 𝓜
    (polynomialGrading_negative k σ) (polynomialGrading_zero k σ) d₀ hbound

end KLInvariance.Graded


end


section

namespace KLInvariance.Graded
universe uk ua um

attribute [instance] ModuleData.kModule ModuleData.tower ModuleData.decomposition
  ModuleData.graded ModuleData.finite

end KLInvariance.Graded

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Dihedral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Interval restrictions, dihedral Coxeter and Hecke calculations, and the genuine square-parameter R normalization.
-/

section

namespace KLInvariance.HeckeQ

universe uR vR
variable {B : Type uR} {W : Type vR} [Group W] {M : CoxeterMatrix B}
variable {C : Type*} [CommRing C]

noncomputable def dualR (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) : C :=
  (-(q : C)) ^ cs.length y * (-(↑q⁻¹ : C)) ^ cs.length x * rValue cs q⁻¹ x y

end KLInvariance.HeckeQ

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Sheaves
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.instAddCommGroupCarrierObj
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Ordered moment graphs, sheaves, flabbiness, sections and boundary images.
-/

section


/-! The finite-section extension argument required by source §4.3. No BMP
character theorem is postulated. These definitions are ordinary module-valued
sheaves on a directed ordered graph; labels enter later through which edge
modules vanish after localization. -/

namespace KLInvariance.MomentGraph

universe u v w z

variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V] {E : Type w}

namespace Sheaf
variable {G : OrderedGraph V E} (B : Sheaf (R := R) G)

/-- One step of the descending extension in `loc:relative-flabbiness`.
Previously assigned lower neighbors can only be on zero edge modules. -/
theorem extend_one (hb : B.Flabby) (live : Set E)
    (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (Ω : Set V) (hΩ : B.ClosedUnder live Ω) (a : V) (ha : a ∉ Ω)
    (hmax : ∀ y, a < y → y ∈ Ω) (f : B.Assignment) (hf : B.CompatibleOn Ω f) :
    ∃ g : B.Assignment, B.CompatibleOn (insert a Ω) g ∧
      (∀ x ∈ Ω, g x = f x) := by
  classical
  have hu : IsUpperSet (Set.Ioi a) := fun x y hxy hx => lt_of_lt_of_le hx hxy
  obtain ⟨t, ht, htf⟩ := hb (Set.Ioi a) hu f
    (B.compatible_mono hf (fun y hy => hmax y hy))
  let g : B.Assignment := Function.update f a (t a)
  have hga : g a = t a := by simp [g]
  have hgf (x : V) (hx : x ≠ a) : g x = f x := by simp [g, hx]
  refine ⟨g, ?_, ?_⟩
  · intro e hs htt
    by_cases hlive : e ∈ live
    · by_cases hsa : G.source e = a
      · have hta : G.target e ≠ a := by simpa [hsa] using (G.increasing e).ne'
        have hT : G.target e ∈ Ω := hmax _ (hsa ▸ G.increasing e)
        have hsource : g (G.source e) = t (G.source e) := by subst a; exact hga
        rw [hsource, hgf _ hta, ← htf _ (hsa ▸ G.increasing e)]
        exact ht e (Set.mem_univ _) (Set.mem_univ _)
      · have hS : G.source e ∈ Ω := (Set.mem_insert_iff.mp hs).resolve_left hsa
        have hT : G.target e ∈ Ω := hΩ e hlive hS
        have hta : G.target e ≠ a := fun h => ha (h ▸ hT)
        rw [hgf _ hsa, hgf _ hta]
        exact hf e hS hT
    · let := hdead e hlive
      exact Subsingleton.elim _ _
  · intro x hx
    exact hgf x (fun h => ha (h ▸ hx))

/-- A finite flabby graph sheaf extends from every set closed under its
nonzero edges. This is the source's relative-flabbiness argument in full,
not merely a restatement of flabbiness for ambient upper sets. -/
theorem extend_closedUnder [Finite V] (hb : B.Flabby) (live : Set E)
    (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (Ω : Set V) (hΩ : B.ClosedUnder live Ω) (f : B.Assignment)
    (hf : B.CompatibleOn Ω f) :
    ∃ g : B.Assignment, B.IsGlobal g ∧ (∀ x ∈ Ω, g x = f x) := by
  classical
  let := Fintype.ofFinite V
  suffices h : ∀ s : Finset V, ∀ f : B.Assignment,
      B.ClosedUnder live (s : Set V)ᶜ → B.CompatibleOn (s : Set V)ᶜ f →
      ∃ g : B.Assignment, B.IsGlobal g ∧ ∀ x ∈ (s : Set V)ᶜ, g x = f x by
    have hs : ((Finset.univ.filter (fun x => x ∉ Ω) : Finset V) : Set V)ᶜ = Ω := by
      ext x
      simp
    have H := h (Finset.univ.filter (fun x => x ∉ Ω)) f
    rw [hs] at H
    exact H hΩ hf
  intro s
  refine Finset.strongInductionOn s ?_
  intro s ih f hΩ hf
  by_cases hs : s = ∅
  · subst s
    exact ⟨f, by simpa [IsGlobal] using hf, fun _ _ => rfl⟩
  obtain ⟨a, ha, hmax⟩ := s.exists_maximal (Finset.nonempty_iff_ne_empty.mpr hs)
  have ha' : a ∉ (s : Set V)ᶜ := by simpa using ha
  have hmax' (y : V) (hay : a < y) : y ∈ (s : Set V)ᶜ := by
    intro hy
    exact (not_le_of_gt hay) (hmax hy hay.le)
  obtain ⟨g, hg, hgf⟩ := B.extend_one hb live hdead (s : Set V)ᶜ hΩ a ha' hmax' f hf
  have hnew : ((s.erase a : Finset V) : Set V)ᶜ = insert a (s : Set V)ᶜ := by
    ext x
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_erase,
      Set.mem_insert_iff, not_and_or, not_not]
  have hsmall : s.erase a ⊂ s := Finset.erase_ssubset ha
  obtain ⟨t, ht, htg⟩ := ih (s.erase a) hsmall g
    (by rw [hnew]; exact B.closedUnder_insert live (s : Set V)ᶜ hΩ a hmax')
      (by rw [hnew]; exact hg)
  refine ⟨t, ht, ?_⟩
  intro x hx
  exact (htg x (by rw [hnew]; exact Set.mem_insert_of_mem _ hx)).trans (hgf x hx)

end Sheaf
end KLInvariance.MomentGraph

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ReflectionSchedules
attribute [-instance] _root_.OAI.KLInvariance.TitsSpace.simpleFixed_finite _root_.OAI.KLInvariance.TitsSpace.simpleFixed_free
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Reflection schedules, decreasing paths, root-space and edge algebra, and dihedral path recursions.
-/

section

namespace KLInvariance.EdgeAlgebra
open Module
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
noncomputable section

variable {κ : Type*}

/-- Polynomial coordinates on the actual symmetric-algebra quotient. -/
def rootQuotientPolynomial (a : V) (b : Basis κ k (V ⧸ rootLine (k := k) a)) :
    (SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) ≃ₐ[k] MvPolynomial κ k :=
  (rootQuotientEquiv a).trans (SymmetricAlgebra.equivMvPolynomial b)

end
end KLInvariance.EdgeAlgebra

namespace KLInvariance.TitsSpace
open Module EdgeAlgebra
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_5
def edgePolynomial (a : PositiveRoot M cs) : EdgeCoefficient a ≃ₐ[ℝ]
    MvPolynomial (Fin (Module.finrank ℝ (Extended M ⧸ rootLine (k := ℝ) (embed M a.val)))) ℝ :=
  rootQuotientPolynomial (embed M a.val) (Module.finBasis ℝ _)

end
end KLInvariance.TitsSpace

/-! NEW GRAPH CLOSURE -/


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_GradedSheaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded moment-graph sheaves, boundary sections, graded covers and morphisms.
-/


section


namespace KLInvariance.MomentGraph.Sheaf
universe u v w z z'
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}

namespace Iso
variable {B : Sheaf.{u,v,w,z} (R := R) G} {C : Sheaf.{u,v,w,z'} (R := R) G}
  (j : Iso B C)

def symm : Iso C B where
  vertex x := (j.vertex x).symm
  edge e := (j.edge e).symm
  lower e v := by
    apply (j.edge e).injective
    simp only [LinearEquiv.apply_symm_apply, j.lower]
  upper e v := by
    apply (j.edge e).injective
    simp only [LinearEquiv.apply_symm_apply, j.upper]

noncomputable def boundary (x : V) : B.Boundary x ≃ₗ[R] C.Boundary x :=
  LinearEquiv.piCongrRight (fun e => j.edge e.val)

theorem stalkMap (x : V) (v : B.vertex x) :
    j.boundary x (B.stalkMap x v) = C.stalkMap x (j.vertex x v) := by
  funext e
  rcases e with ⟨e,he⟩
  subst x
  exact j.lower e v

end Iso

variable (B : Sheaf.{u,v,w,z} (R := R) G)

namespace Iso
variable {B : Sheaf.{u,v,w,z} (R := R) G} {C : Sheaf.{u,v,w,z'} (R := R) G}
  (j : Iso B C)

theorem upwardKernel_iff (x : V) (F : Set (Outgoing (G := G) x)) (v : B.vertex x) :
    j.vertex x v ∈ C.upwardKernel x F ↔ v ∈ B.upwardKernel x F := by
  constructor <;> intro h e he
  · apply (j.edge e.val).injective
    rw [map_zero]
    exact (congrFun (j.stalkMap x v) e).trans (h e he)
  · have hh := congrFun (j.stalkMap x v) e
    change j.edge e.val (B.stalkMap x v e) = _ at hh
    rw [h e he,map_zero] at hh
    exact hh.symm

end Iso
end KLInvariance.MomentGraph.Sheaf

end


section

/-! Partial sheaf isomorphisms on upper sets, and their actual descending
extension. In particular the incoming edge component is induced by the upper
scalar quotient, not independently assumed. -/
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z z'
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}
  (B : Sheaf.{u,v,w,z} (R := R) G) (C : Sheaf.{u,v,w,z'} (R := R) G)

namespace OnIso
variable {B C} {U : Set V} (j : OnIso B C U)

 def above (x : V) (hx : Set.Ioi x ⊆ U) : AboveIso B C x where
  vertex y h := j.vertex y (hx h)
  edge e h := j.edge e (hx h)
  lower e h v := j.lower e (hx h) (hx (h.trans (G.increasing e))) v
  upper e h v := j.upper e (hx h) v

 def ofUniv (j : OnIso B C Set.univ) : Iso B C where
  vertex x := j.vertex x (Set.mem_univ x)
  edge e := j.edge e (Set.mem_univ _)
  lower e v := j.lower e (Set.mem_univ _) (Set.mem_univ _) v
  upper e v := j.upper e (Set.mem_univ _) v

/-- Given the new stalk and its outgoing commuting squares, all new incoming
edges are forced by the scalar quotient rule. -/
noncomputable def extend (hU : IsUpperSet U) (x : V) (hx : x ∉ U)
    (hmax : Set.Ioi x ⊆ U) (α : E → R)
    (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
    (jv : B.vertex x ≃ₗ[R] C.vertex x)
    (hout : ∀ e (he : G.source e = x) v,
      j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))
        (B.lower e v) = C.lower e (castStalkIso B C he.symm jv v)) :
    OnIso B C (insert x U) := by
  classical
  let vj : ∀ y, y ∈ insert x U → B.vertex y ≃ₗ[R] C.vertex y := fun y hy =>
    if h : y = x then castStalkIso B C h.symm jv
    else j.vertex y ((Set.mem_insert_iff.mp hy).resolve_left h)
  have vj_old (y : V) (hy : y ∈ U) : vj y (Set.mem_insert_of_mem x hy) = j.vertex y hy := by
    simp only [vj,dite_eq_right (show y ≠ x from fun h => hx (h ▸ hy))]
  have vj_new : vj x (Set.mem_insert x U) = jv := by simp [vj,castStalkIso]
  let ej : ∀ e, G.target e ∈ insert x U → B.edge e ≃ₗ[R] C.edge e := fun e he =>
    if h : G.target e = x then
      QuotientEdge.iso (B.upper e) (C.upper e) (hBq e).1 (hCq e).1
        (vj (G.target e) he)
        (QuotientEdge.map_kernel_scalar (B.upper e) (C.upper e) (α e)
          (hBq e).2 (hCq e).2 (vj (G.target e) he))
    else j.edge e ((Set.mem_insert_iff.mp he).resolve_left h)
  have ej_old (e : E) (he : G.target e ∈ U) :
      ej e (Set.mem_insert_of_mem x he) = j.edge e he := by
    simp only [ej,dite_eq_right (show G.target e ≠ x from fun h => hx (h ▸ he))]
  refine ⟨vj,ej,?_,?_⟩
  · intro e hs ht v
    have htU : G.target e ∈ U := by
      rcases Set.mem_insert_iff.mp hs with hs | hs
      · exact hmax (lt_of_eq_of_lt hs.symm (G.increasing e))
      · exact hU (G.increasing e).le hs
    rw [ej_old e htU]
    by_cases he : G.source e = x
    · subst x
      rw [vj_new]
      exact hout e rfl v
    · have hsU : G.source e ∈ U := (Set.mem_insert_iff.mp hs).resolve_left he
      rw [vj_old _ hsU]
      exact j.lower e hsU htU v
  · intro e ht v
    by_cases he : G.target e = x
    · simp only [ej,dite_eq_left he]
      exact QuotientEdge.iso_apply _ _ _ _ _ _ v
    · have htU : G.target e ∈ U := (Set.mem_insert_iff.mp ht).resolve_left he
      rw [ej_old e htU,vj_old _ htU]
      exact j.upper e htU v

end OnIso
end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_MinimalExtensions
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.pi_free _root_.OAI.KLInvariance.Graded.ModuleData.prod_free _root_.OAI.KLInvariance.Graded.ModuleData.shift_free
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Minimal-boundary extension sheaves, graded splittings and sheaf decomposition.
-/


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

 theorem quotient_iso_graded {M N E F : ModuleData.{uk,ua,um} 𝓐}
    (f : Hom M E) (g : Hom N F) (hf : Function.Surjective f.map)
    (hg : Function.Surjective g.map) (e : M ≃ₗ[A] N)
    (he : ∀ n v, v ∈ M.piece n → e v ∈ N.piece n)
    (hk : (LinearMap.ker f.map).map e.toLinearMap = LinearMap.ker g.map)
    (n : ℤ) (v : E) (hv : v ∈ E.piece n) :
    QuotientEdge.iso f.map g.map hf hg e hk v ∈ F.piece n := by
  obtain ⟨w,hw,rfl⟩ := f.homogeneous_preimage hf n v hv
  rw [QuotientEdge.iso_apply]
  exact g.graded n _ (he n w hw)

end KLInvariance.Graded.ModuleData

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}

namespace OnIso
variable {B C : GradedSheaf (𝓐 := 𝓐) G} {U : Set V} (j : OnIso B C U)

 def ofUniv (j : OnIso B C Set.univ) : Iso B C where
  toIso := j.toOnIso.ofUniv
  vertex_graded x := j.vertex_graded x (Set.mem_univ x)
  edge_graded e := j.edge_graded e (Set.mem_univ _)

noncomputable def extend (hU : IsUpperSet U) (x : V) (hx : x ∉ U)
    (hmax : Set.Ioi x ⊆ U) (α : E → A)
    (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
    (jv : B.vertex x ≃ₗ[A] C.vertex x)
    (hjv : ∀ n v, v ∈ (B.vertex x).piece n → jv v ∈ (C.vertex x).piece n)
    (hout : ∀ e (he : G.source e = x) v,
      j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))
        (B.forget.lower e v) = C.forget.lower e (Sheaf.castStalkIso B.forget C.forget he.symm jv v)) :
    OnIso B C (insert x U) := by
  classical
  let p := j.toOnIso.extend hU x hx hmax α hBq hCq jv hout
  have hvp : ∀ y (hy : y ∈ insert x U) n v,
      v ∈ (B.vertex y).piece n → p.vertex y hy v ∈ (C.vertex y).piece n := by
    intro y hy n v hv
    dsimp only [p,Sheaf.OnIso.extend]
    split_ifs with h
    · subst y
      exact hjv n v hv
    · exact j.vertex_graded y _ n v hv
  refine ⟨p,hvp,?_⟩
  intro e he n v hv
  dsimp only [p,Sheaf.OnIso.extend]
  split_ifs with h
  · apply ModuleData.quotient_iso_graded (B.upper e) (C.upper e) (hBq e).1 (hCq e).1
    · subst x
      exact hjv
    · exact hv
  · exact j.edge_graded e _ n v hv

end OnIso
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}
noncomputable section
 def shift (B : GradedSheaf (𝓐 := 𝓐) G) (d : ℕ) : GradedSheaf (𝓐 := 𝓐) G where
  vertex x := (B.vertex x).shift d
  edge e := (B.edge e).shift d
  lower e := (B.lower e).shift d
  upper e := (B.upper e).shift d

 def prod (B C : GradedSheaf (𝓐 := 𝓐) G) : GradedSheaf (𝓐 := 𝓐) G where
  vertex x := (B.vertex x).prod (C.vertex x)
  edge e := (B.edge e).prod (C.edge e)
  lower e := (B.lower e).prodMap (C.lower e)
  upper e := (B.upper e).prodMap (C.upper e)

 def pi {ι : Type um} [Fintype ι] (B : ι → GradedSheaf (𝓐 := 𝓐) G) :
    GradedSheaf (𝓐 := 𝓐) G where
  vertex x := ModuleData.pi (fun i => (B i).vertex x)
  edge e := ModuleData.pi (fun i => (B i).edge e)
  lower e := ModuleData.Hom.pi (fun i => (B i).lower e)
  upper e := ModuleData.Hom.pi (fun i => (B i).upper e)

 def OnIso.prodZero {B C : GradedSheaf (𝓐 := 𝓐) G} {U : Set V} (j : OnIso B C U)
    (D : GradedSheaf (𝓐 := 𝓐) G)
    (hV : ∀ x ∈ U, Subsingleton (D.vertex x))
    (hE : ∀ e, G.target e ∈ U → Subsingleton (D.edge e)) : OnIso B (prod C D) U where
  toOnIso := j.toOnIso.prodZero D.forget hV hE
  vertex_graded x hx n v hv := ⟨j.vertex_graded x hx n v hv,Submodule.zero_mem _⟩
  edge_graded e he n v hv := ⟨j.edge_graded e he n v hv,Submodule.zero_mem _⟩

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Finite sums of honest shifted normalized boundary models. A model family
is data for the decomposition lemma, not an assumption of the KL main. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}

instance zeroVertex_subsingleton (x : V) : Subsingleton ((zero (𝓐 := 𝓐) (G := G)).vertex x) :=
  inferInstanceAs (Subsingleton PUnit.{max ua um+1})
instance zeroEdge_subsingleton (e : E) : Subsingleton ((zero (𝓐 := 𝓐) (G := G)).edge e) :=
  inferInstanceAs (Subsingleton PUnit.{max ua um+1})

inductive ModelSum (O : V → GradedSheaf (𝓐 := 𝓐) G) (U : Set V) :
    GradedSheaf (𝓐 := 𝓐) G → Prop where
  | zero : ModelSum O U zero
  | add {B} : ModelSum O U B → ∀ c ∈ U, ∀ (n : ℕ) (d : ULift.{um} (Fin n) → ℕ),
      ModelSum O U (prod B (pi (fun i => (O c).shift (d i))))

end KLInvariance.MomentGraph.GradedSheaf

end


section


namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section

 theorem structureSheaf_free (x : V) : Module.Free R ((structureSheaf G α c).vertex x) :=
  inferInstanceAs (Module.Free R (PLift (x ≤ c) → R))

 theorem structureSheaf_finite (x : V) : Module.Finite R ((structureSheaf G α c).vertex x) :=
  inferInstanceAs (Module.Finite R (PLift (x ≤ c) → R))

 def structureVertexIso (x : V) (hx : x ≤ c) :
    (structureSheaf G α c).vertex x ≃ₗ[R] R where
  toFun f := f ⟨hx⟩
  invFun r := fun _ => r
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem structureSheaf_generated : (structureSheaf G α c).Generated := by
  classical
  intro x v
  by_cases hx : x ≤ c
  · refine ⟨fun _ _ => v ⟨hx⟩, fun _ _ _ => rfl, rfl⟩
  · let _ := structureSheaf_support G α c x hx
    exact ⟨0,fun _ _ _ => rfl,Subsingleton.elim _ _⟩

 theorem structureSheaf_upperQuotient : (structureSheaf G α c).UpperQuotient α := by
  classical
  intro e
  refine ⟨?_,?_⟩
  · intro v
    choose r hr using fun h : PLift (G.target e ≤ c) => Ideal.Quotient.mk_surjective (v h)
    exact ⟨r,funext hr⟩
  · intro v
    constructor
    · intro hv
      have hh (h : PLift (G.target e ≤ c)) :
          v h ∈ Ideal.span {α e} := Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hv h)
      choose r hr using fun h => Ideal.mem_span_singleton.mp (hh h)
      exact ⟨r,funext hr⟩
    · rintro ⟨w,rfl⟩
      funext h
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr ⟨w h,rfl⟩)

 theorem structureSheaf_minimal [IsLocalRing R]
    (hα : ∀ e, α e ∈ IsLocalRing.maximalIdeal R)
    (hreach : ∀ x, x < c → ∃ e, G.source e = x ∧ G.target e ≤ c)
    (x : V) (hxc : x ≠ c) :
    LinearMap.ker ((structureSheaf G α c).stalkMap x) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R ((structureSheaf G α c).vertex x)) := by
  classical
  intro v hv
  by_cases hx : x ≤ c
  · obtain ⟨e,he,het⟩ := hreach x (lt_of_le_of_ne hx hxc)
    subst x
    have heq := congrFun (LinearMap.mem_ker.mp hv) ⟨e,rfl⟩
    have hvα : v ⟨hx⟩ ∈ Ideal.span {α e} :=
      Ideal.Quotient.eq_zero_iff_mem.mp (congrFun heq ⟨het⟩)
    have hm : v ⟨hx⟩ ∈ IsLocalRing.maximalIdeal R :=
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hα e))) hvα
    let one : (structureSheaf G α c).vertex (G.source e) := fun _ => 1
    have hs : v ⟨hx⟩ • one ∈ IsLocalRing.maximalIdeal R •
        (⊤ : Submodule R ((structureSheaf G α c).vertex (G.source e))) :=
      Submodule.smul_mem_smul hm (show one ∈
        (⊤ : Submodule R ((structureSheaf G α c).vertex (G.source e))) from Submodule.mem_top)
    have heqv : v = v ⟨hx⟩ • one := by
      funext h
      exact (mul_one _).symm
    rw [heqv]
    exact hs
  · let _ := structureSheaf_support G α c x hx
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _

end
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)

/-- The finite section constraint whose kernel is the actual section module. -/
noncomputable def constraint (Ω : Set V) : B.Assignment →ₗ[R]
    (∀ e : {e : E // G.source e ∈ Ω ∧ G.target e ∈ Ω}, B.edge e.val) :=
  LinearMap.pi (fun e => (B.lower e.val).comp (LinearMap.proj (G.source e.val)) -
    (B.upper e.val).comp (LinearMap.proj (G.target e.val)))

lemma ker_constraint (Ω : Set V) : LinearMap.ker (B.constraint Ω) = B.sections Ω := by
  ext f
  constructor
  · intro h e hs ht
    have hh := congrFun (LinearMap.mem_ker.mp h) ⟨e,hs,ht⟩
    exact sub_eq_zero.mp hh
  · intro h
    apply LinearMap.mem_ker.mpr
    funext e
    exact sub_eq_zero.mpr (h e.val e.property.1 e.property.2)

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)
noncomputable section

 theorem tensorAssignments_bijective [Finite V] : Function.Bijective (B.tensorAssignments S) := by
  classical
  let := Fintype.ofFinite V
  exact (TensorProduct.piRight R S S (fun x => B.vertex x)).bijective

 theorem constraint_tensorAssignments (Ω : Set V) (z : S ⊗[R] B.Assignment) :
    (B.baseChange S).constraint Ω (B.tensorAssignments S z) =
      TensorProduct.piRightHom R S S (fun e : {e : E // G.source e ∈ Ω ∧ G.target e ∈ Ω} =>
        B.edge e.val) (AlgebraTensorModule.lTensor S S (B.constraint Ω) z) := by
  induction z using OAI.tensorInductionOn with
  | tmul s f =>
    ext e
    change s ⊗ₜ[R] B.lower e.val (f (G.source e.val)) -
      s ⊗ₜ[R] B.upper e.val (f (G.target e.val)) =
      s ⊗ₜ[R] (B.lower e.val (f (G.source e.val)) -
        B.upper e.val (f (G.target e.val)))
    exact (tmul_sub _ _ _).symm
  | add z w hz hw => simp only [map_add,hz,hw]; rfl

 theorem tensorSections_surjective [Finite V] [Finite E] [Module.Flat R S] (Ω : Set V) :
    Function.Surjective (B.tensorSections S Ω) := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  intro f
  obtain ⟨z,hz⟩ := (B.tensorAssignments_bijective S).2 f.val
  have hc : (B.baseChange S).constraint Ω (B.tensorAssignments S z) = 0 := by
    rw [hz]
    apply LinearMap.mem_ker.mp
    rw [(B.baseChange S).ker_constraint Ω]
    exact f.property
  have he : AlgebraTensorModule.lTensor S S (B.constraint Ω) z = 0 := by
    apply (TensorProduct.piRight R S S
      (fun e : {e : E // G.source e ∈ Ω ∧ G.target e ∈ Ω} => B.edge e.val)).injective
    rw [map_zero]
    exact (B.constraint_tensorAssignments S Ω z).symm.trans hc
  have hex : Function.Exact (B.sections Ω).subtype (B.constraint Ω) := by
    rw [← B.ker_constraint Ω]
    exact (B.constraint Ω).exact_subtype_ker_map
  obtain ⟨w,hw⟩ := (Module.Flat.lTensor_exact S hex z).mp he
  refine ⟨w,?_⟩
  apply Subtype.ext
  change B.tensorAssignments S (AlgebraTensorModule.lTensor S S (B.sections Ω).subtype w) = _
  exact (congrArg (B.tensorAssignments S) hw).trans hz

 theorem baseChange_flabby [Finite V] [Finite E] [Module.Flat R S]
    (hb : B.Flabby) : (B.baseChange S).Flabby := by
  intro Ω hΩ f hf
  obtain ⟨z,hz⟩ := B.tensorSections_surjective S Ω ⟨f,hf⟩
  suffices ∃ g : (B.baseChange S).Assignment, (B.baseChange S).IsGlobal g ∧
      ∀ x ∈ Ω, g x = (B.tensorSections S Ω z).val x by
    simpa only [hz] using this
  clear hz f hf
  induction z using OAI.tensorInductionOn with
  | tmul s f =>
    obtain ⟨g,hg,hgf⟩ := hb Ω hΩ f.val f.property
    refine ⟨fun x => s ⊗ₜ g x,B.baseChange_tmul_compatible S Set.univ s g hg,?_⟩
    intro x hx
    change s ⊗ₜ[R] g x = s ⊗ₜ[R] f.val x
    rw [hgf x hx]
  | add z w hz hw =>
    obtain ⟨f,hf,hfz⟩ := hz
    obtain ⟨g,hg,hgw⟩ := hw
    refine ⟨f+g,Submodule.add_mem ((B.baseChange S).sections Set.univ) hf hg,?_⟩
    intro x hx
    simp only [map_add,Submodule.coe_add,Pi.add_apply]
    rw [hfz x hx,hgw x hx]

end
end KLInvariance.MomentGraph.Sheaf

end


section


namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um un
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E}
noncomputable section

namespace Iso
variable {B : Sheaf.{ur,uv,ue,um} (R := R) G}
  {C : Sheaf.{ur,uv,ue,un} (R := R) G} (j : Iso B C)
include j

 theorem flabby (hb : B.Flabby) : C.Flabby := by
  intro Ω hΩ f hf
  have hsf : B.CompatibleOn Ω (j.symm.assignments f) :=
    (j.symm.compatible_iff Ω f).mpr hf
  obtain ⟨g,hg,hgf⟩ := hb Ω hΩ (j.symm.assignments f) hsf
  refine ⟨j.assignments g,(j.compatible_iff Set.univ g).mpr hg,?_⟩
  intro x hx
  change j.vertex x (g x) = f x
  rw [hgf x hx]
  exact (j.vertex x).apply_symm_apply _

end Iso

variable (S : Type us) [CommRing S] [Algebra R S]

@[simp] theorem baseChangeScalar_tmul (s : S) (r : R) :
    baseChangeScalar S (s ⊗ₜ[R] r) = s * algebraMap R S r := by
  change r • s = s * algebraMap R S r
  rw [Algebra.smul_def,mul_comm]

@[simp] theorem baseChangeQuotient_tmul (a r : R) (s : S) :
    baseChangeQuotient S a (s ⊗ₜ[R] Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (s * algebraMap R S r) := by
  simp only [baseChangeQuotient,LinearEquiv.trans_apply,AlgEquiv.toLinearEquiv_apply,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  change Ideal.Quotient.mk _ (r • s) = Ideal.Quotient.mk _ (s * algebraMap R S r)
  rw [Algebra.smul_def,mul_comm]


 def baseChangePiScalar (p : Prop) :
    S ⊗[R] (PLift p → R) ≃ₗ[S] (PLift p → S) := by
  classical
  exact (TensorProduct.piRight R S S (fun _ : PLift p => R)).trans
    (LinearEquiv.piCongrRight (fun _ => baseChangeScalar S))

 def baseChangePiQuotient (a : R) (p : Prop) :
    S ⊗[R] (PLift p → R ⧸ Ideal.span {a}) ≃ₗ[S]
      (PLift p → S ⧸ Ideal.span {algebraMap R S a}) := by
  classical
  exact (TensorProduct.piRight R S S
    (fun _ : PLift p => R ⧸ Ideal.span {a})).trans
      (LinearEquiv.piCongrRight (fun _ => baseChangeQuotient S a))

 theorem baseChangePiScalar_tmul (p : Prop) (s : S) (v : PLift p → R) (h : PLift p) :
    baseChangePiScalar S p (s ⊗ₜ v) h = s * algebraMap R S (v h) :=
  baseChangeScalar_tmul S s (v h)

 theorem baseChangePiQuotient_tmul (a : R) (p : Prop)
    (s : S) (v : PLift p → R ⧸ Ideal.span {a}) (h : PLift p) :
    baseChangePiQuotient S a p (s ⊗ₜ v) h = baseChangeQuotient S a (s ⊗ₜ v h) := rfl

 theorem baseChangePi_natural (a : R) (p q : Prop) (h : q → p)
    (v : S ⊗[R] (PLift p → R)) :
    baseChangePiQuotient S a q
      (AlgebraTensorModule.lTensor S S (quotientPullback a p q h) v) =
      quotientPullback (algebraMap R S a) p q h (baseChangePiScalar S p v) := by
  induction v using OAI.tensorInductionOn with
  | tmul s v =>
    funext hh
    change baseChangePiQuotient S a q (s ⊗ₜ quotientPullback a p q h v) hh = _
    rw [baseChangePiQuotient_tmul]
    change baseChangeQuotient S a (s ⊗ₜ Ideal.Quotient.mk _ (v ⟨h hh.down⟩)) = _
    rw [baseChangeQuotient_tmul]
    exact congrArg (Ideal.Quotient.mk _) (baseChangePiScalar_tmul S p s v _).symm
  | add v w hv hw => simp only [map_add,hv,hw]

 def structureBaseChangeIso (G : OrderedGraph V E) (α : E → R) (c : V) :
    Iso ((structureSheaf G α c).baseChange S)
      (structureSheaf G (fun e => algebraMap R S (α e)) c) where
  vertex x := baseChangePiScalar S (x ≤ c)
  edge e := baseChangePiQuotient S (α e) (G.target e ≤ c)
  lower e v := baseChangePi_natural S (α e) (G.source e ≤ c) (G.target e ≤ c)
    ((G.increasing e).le.trans ·) v
  upper e v := baseChangePi_natural S (α e) (G.target e ≤ c) (G.target e ≤ c) id v

 theorem structureSheaf_flat_flabby [Finite V] [Finite E] [Module.Flat R S]
    (G : OrderedGraph V E) (α : E → R) (c : V) (hf : (structureSheaf G α c).Flabby) :
    (structureSheaf G (fun e => algebraMap R S (α e)) c).Flabby :=
  (structureBaseChangeIso S G α c).flabby ((structureSheaf G α c).baseChange_flabby S hf)

end
end KLInvariance.MomentGraph.Sheaf

end


section

/-! Restriction to a full vertex subgraph, including the relative-flabbiness
criterion used after plane localization. -/

namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} (G : OrderedGraph V E) (α : E → R) (K : Set V)
noncomputable section

 theorem structureSheaf_edge_subsingleton (c : V) (e : E) (he : ¬ G.target e ≤ c) :
    Subsingleton ((structureSheaf G α c).edge e) :=
  ⟨fun _ _ => funext (fun h => False.elim (he h.down))⟩

end
end KLInvariance.MomentGraph.Sheaf

end


section

/-! Pullback along a directed graph map. Relative-order flabbiness requires
only outgoing completeness for the surviving edges, not equality of the two
orders on a coset. -/
namespace KLInvariance.MomentGraph
universe ur uv ue uw uf um
variable {V : Type uv} [PartialOrder V] {E : Type ue}
  {W : Type uw} [PartialOrder W] {F : Type uf}

namespace Sheaf
variable {R : Type ur} [CommRing R] {G : OrderedGraph V E} {H : OrderedGraph W F}
  (B : Sheaf.{ur,uw,uf,um} (R := R) H) (f : GraphMap G H)
noncomputable section

 theorem pullback_flabby_live [Finite W] (hb : B.Flabby)
    (hi : Function.Injective f.vertex) (live : Set F)
    (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (hlift : ∀ e ∈ live, ∀ x, f.vertex x = H.source e →
      ∃ a, f.edge a=e ∧ G.source a=x) : (B.pullback f).Flabby := by
  intro Ω hΩ s hs
  have hc : B.ClosedUnder live (f.vertex '' Ω) := by
    intro e he hsource
    obtain ⟨x,hx,hxe⟩ := hsource
    obtain ⟨a,rfl,rfl⟩ := hlift e he x hxe
    exact ⟨G.target a,hΩ (G.increasing a).le hx,f.target a⟩
  have hcompat : B.CompatibleOn (f.vertex '' Ω) (B.pushAssignment f s) := by
    intro e hsource htarget
    by_cases he : e ∈ live
    · obtain ⟨x,hx,hxe⟩ := hsource
      obtain ⟨a,rfl,rfl⟩ := hlift e he x hxe
      obtain ⟨y,hy,hye⟩ := htarget
      have hya : y=G.target a := hi (hye.trans (f.target a).symm)
      subst y
      have hh := hs a hx hy
      rw [← B.pull_push f hi s] at hh
      change (B.pullback f).lower a (B.pullAssignment f (B.pushAssignment f s) (G.source a)) =
        (B.pullback f).upper a (B.pullAssignment f (B.pushAssignment f s) (G.target a)) at hh
      rw [pull_lower,pull_upper] at hh
      exact hh
    · exact @Subsingleton.elim _ (hdead e he) _ _
  obtain ⟨t,ht,hts⟩ := B.extend_closedUnder hb live hdead (f.vertex '' Ω) hc
    (B.pushAssignment f s) hcompat
  refine ⟨B.pullAssignment f t,B.pull_global f t ht,?_⟩
  intro x hx
  change t (f.vertex x) = s x
  rw [hts (f.vertex x) ⟨x,hx,rfl⟩]
  exact congrFun (B.pull_push f hi s) x

end
end Sheaf
end KLInvariance.MomentGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SheafMorphisms
attribute [-instance] _root_.OAI.KLInvariance.TitsSpace.simpleFixed_finite _root_.OAI.KLInvariance.TitsSpace.simpleFixed_free
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded sheaf morphisms, exact section constructions and character sums.
-/

section

namespace KLInvariance.Graded
open Polynomial
universe uk us um ui
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {M : Type um} [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (polynomialGrading k σ) 𝓜]

attribute [instance] NonnegativeBasis.finite

theorem exists_nonnegativeBasis [Module.Free (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) M] (hneg : ∀ n < 0, 𝓜 n = ⊥) :
    Nonempty (NonnegativeBasis (σ := σ) 𝓜) := by
  classical
  obtain ⟨ι,hι,b,hb⟩ := exists_homogeneous_basis_polynomial (σ := σ) 𝓜 0 hneg
  let := hι
  let : Fintype ι := Fintype.ofFinite ι
  choose d hd using hb
  have hd0 (i : ι) : 0 ≤ d i := by
    by_contra h
    have hh := hd i
    rw [hneg _ (lt_of_not_ge h),Submodule.mem_bot] at hh
    exact b.ne_zero i hh
  exact ⟨⟨ι,inferInstance,b,fun i => (d i).toNat,fun i => by simpa [Int.toNat_of_nonneg (hd0 i)] using hd i⟩⟩

noncomputable def character [Module.Free (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) M] (hneg : ∀ n < 0, 𝓜 n = ⊥) : ℤ[X] :=
  (exists_nonnegativeBasis (σ := σ) 𝓜 hneg).some.polynomial

end KLInvariance.Graded

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
noncomputable section

def stalkCharacter (x : Interval cs u b) : Polynomial ℤ := by
  let B := boundarySheaf cs u b basis hub
  let := B.free x
  exact Graded.character (σ := σ) (B.sheaf.vertex x).piece (B.sheaf.vertex x).nonneg

end
end KLInvariance.BruhatGraph

end


section

/-! Parity matching in finite lower Bruhat intervals, used only to construct
actual dihedral interpolation sections. -/
namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W)
noncomputable section

 theorem external_parity_card_le {x c : W} (hxc : BruhatLE cs x c) :
    ((externalLower cs x c).filter (fun z => cs.length z % 2 = cs.length x % 2)).card ≤
      ((externalLower cs x c).filter (fun z => cs.length z % 2 ≠ cs.length x % 2)).card := by
  classical
  by_cases hc : c = 1
  · subst c
    have hx : x = 1 := bruhat_antisymm cs hxc (one_bruhat cs x)
    subst x
    simp [externalLower]
  have hp : cs.length x % 2 < 2 := Nat.mod_lt _ (by omega)
  have hbal := lower_parity_balance cs hc hp
  have hsub : lowerFinset cs x ⊆ lowerFinset cs c := by
    intro z hz
    exact (mem_lowerFinset cs c z).mpr (((mem_lowerFinset cs x z).mp hz).trans hxc)
  have hs₀ : (lowerFinset cs x).filter (fun z => cs.length z % 2 = cs.length x % 2) ⊆
      (lowerFinset cs c).filter (fun z => cs.length z % 2 = cs.length x % 2) :=
    Finset.filter_subset_filter _ hsub
  have hs₁ : (lowerFinset cs x).filter (fun z => cs.length z % 2 ≠ cs.length x % 2) ⊆
      (lowerFinset cs c).filter (fun z => cs.length z % 2 ≠ cs.length x % 2) :=
    Finset.filter_subset_filter _ hsub
  have heq (p : W → Prop) [DecidablePred p] :
      (externalLower cs x c).filter p = (lowerFinset cs c).filter p \ (lowerFinset cs x).filter p := by
    ext z
    simp only [externalLower,Finset.mem_filter,Finset.mem_sdiff]
    tauto
  rw [heq,heq,Finset.card_sdiff_of_subset hs₀,Finset.card_sdiff_of_subset hs₁]
  rw [hbal]
  apply Nat.sub_le_sub_left
  by_cases hx : x = 1
  · subst x
    have hh : lowerFinset cs (1:W) = {1} := by
      ext z
      simp only [mem_lowerFinset,Finset.mem_singleton]
      exact ⟨fun h => bruhat_antisymm cs h (one_bruhat cs z),fun h => h ▸ bruhat_refl cs 1⟩
    simp [hh,Finset.filter_singleton]
  · exact (lower_parity_balance cs hx hp).symm.le

end
end KLInvariance

end


section

/-! Honest polynomial characters commute with actual finite graded sums and
nonnegative shifts. No Hecke or KL identification enters these lemmas. -/
namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  (M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
noncomputable section

 abbrev char [Module.Free (MvPolynomial σ k) M] : Polynomial ℤ :=
  character (σ := σ) M.piece M.nonneg

end
end KLInvariance.Graded.ModuleData

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Decomposition
attribute [-instance] _root_.OAI.KLInvariance.TitsSpace.simpleFixed_finite _root_.OAI.KLInvariance.TitsSpace.simpleFixed_free
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded decomposition characters, reflection-plane algebras and reflection Frobenius structures.
-/

section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 def freeStalkChar (B : GradedSheaf (𝓐 := polynomialGrading k σ) G)
    (hf : ∀ x, Module.Free (MvPolynomial σ k) (B.vertex x)) (x : V) : Polynomial ℤ := by
  let := hf x
  exact (B.vertex x).char

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidable_solutions_1
def lowerCharacter (c x : Interval cs 1 b) : Polynomial ℤ :=
  if h : x ≤ c then stalkCharacter cs 1 c.val basis (one_bruhat cs c.val)
    ⟨x.val,x.property.1,h⟩ else 0

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- Relative dihedral paths give actual ambient Bruhat paths in the coset. -/
theorem coset_bruhat {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g h : planeSubgroup M cs P} (hgh : BruhatLE B.system g h) :
    BruhatLE cs ((g:W)*a₀) ((h:W)*a₀) := by
  induction hgh with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z _ hyz ih =>
    exact ih.tail ((B.coset_step_iff hmin y z).mpr hyz)

end PlaneBasis


end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded unit splittings, integral support and balanced cuts, and boundary-sheaf support and recognition.
-/


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
  (a : A) (d : ℤ) (ha : a ∈ 𝓐 d)

noncomputable def scalarDegreeEquiv
    (hinj : Function.Injective (fun m : M => a • m)) (n : ℤ) :
    𝓜 (n-d) ≃ₗ[k] subPiece 𝓜 (LinearMap.range (LinearMap.lsmul A M a)) n :=
  LinearEquiv.ofBijective (scalarDegreeMap 𝓐 𝓜 a d ha n)
    ⟨scalarDegreeMap_injective 𝓐 𝓜 a d ha hinj n,
      scalarDegreeMap_surjective 𝓐 𝓜 a d ha n⟩

end KLInvariance.Hilbert

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
  [Fintype (Edge cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section

 def kernelEquivSingleSupport (x : Interval cs u b) :
    LinearMap.ker (B.sheaf.forget.stalkMap x) ≃ₗ[Coefficient (σ := σ)]
      IntegralSupport.supported (B.sheaf.forget.sections Set.univ) x := by
  let _ (x : Interval cs u b) : Module.Free (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) := B.free x
  let _ (x : Interval cs u b) : Module.Finite (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) :=
    (B.sheaf.vertex x).finite
  let _ (x : Interval cs u b) : Fintype (Module.Free.ChooseBasisIndex
      (Coefficient (σ := σ)) (B.sheaf.forget.vertex x)) := Fintype.ofFinite _
  let bs := fun x : Interval cs u b =>
    Module.Free.chooseBasis (Coefficient (σ := σ)) (B.sheaf.forget.vertex x)
  exact (B.sheaf.forget.kernelEquivSingleStalk (polynomialLabel cs u b basis)
    (polynomialLabel_prime cs u b basis) (fun e => (B.quotient e).2) bs x
    (incoming_pairwise_relPrime cs u b basis x)
    (B.sheaf.forget.outgoing_product_regular (polynomialLabel cs u b basis)
      (polynomialLabel_prime cs u b basis) (fun e => (B.quotient e).1)
      (fun e => (B.quotient e).2) bs x
      (outgoing_incoming_not_dvd cs u b basis x))).trans
        (B.sheaf.forget.singleStalkEquivSupport x)


 def costalkEquivDual (d : SectionDuality cs u b basis hub B) (x : Interval cs u b) :
    LinearMap.ker (B.sheaf.forget.stalkMap x) ≃ₗ[Coefficient (σ := σ)]
      Dual (Coefficient (σ := σ)) (B.sheaf.vertex x) := by
  let _ (x : Interval cs u b) : Module.Free (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) := B.free x
  let _ (y : Interval cs u b) : Module.IsTorsionFree (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := inferInstance
  exact (kernelEquivSingleSupport cs u b basis hub B x).trans
    (B.sheaf.forget.singleSupportEquivDual (polynomialLabel cs u b basis)
      (polynomialLabel_ne_zero cs u b basis)
      (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
      d.pairing d.balanced B.generated x)

end
end KLInvariance.BruhatGraph

end


section

/-! The degree of the actual incoming root product on [1,b].  This is not
asserted for truncated intervals with arbitrary bottom. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (b : W)
noncomputable section

 def incomingEquivInversions (x : Interval cs 1 b) :
    {e : Edge cs 1 b // target cs 1 b e = x} ≃ {t : W // cs.IsLeftInversion x.val t} where
  toFun e := ⟨label cs 1 b e.val, label_isReflection cs 1 b e.val, by
    have hx : (target cs 1 b e.val).val = x.val := congrArg Subtype.val e.property
    have he := label_mul_target cs 1 b e.val
    rw [hx] at he
    rw [he]
    have h := e.val.property.1
    change cs.length (source cs 1 b e.val).val < cs.length (target cs 1 b e.val).val at h
    simpa only [hx] using h⟩
  invFun t := by
    have hstep : BruhatStep cs (t.val*x.val) x.val := by
      refine ⟨t.property.2,t.val,t.property.1,?_⟩
      rw [← mul_assoc,t.property.1.mul_self,one_mul]
    let y : Interval cs 1 b := ⟨t.val*x.val,one_bruhat cs _,
      (Relation.ReflTransGen.single hstep).trans x.property.2⟩
    exact ⟨⟨(y,x),hstep⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply eq_of_label_target_eq cs 1 b
    · change x.val * (label cs 1 b e.val*x.val)⁻¹ = label cs 1 b e.val
      rw [mul_inv_rev,← mul_assoc,mul_inv_cancel,one_mul,
        (label_isReflection cs 1 b e.val).inv]
    · exact e.property.symm
  right_inv t := by
    apply Subtype.ext
    change x.val * (t.val*x.val)⁻¹=t.val
    rw [mul_inv_rev,← mul_assoc,mul_inv_cancel,one_mul,t.property.1.inv]

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
  [Fintype (Edge cs u b)] [Fintype (Interval cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section

 def fullSubmodule (x : Interval cs u b) : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex x) :=
    LinearMap.ker (B.sheaf.forget.stalkMap x)

omit [Fintype σ] [Fintype (Edge cs u b)] [Fintype (Interval cs u b)]
  [DecidableEq (Interval cs u b)] in
 theorem fullKernel_eq (x : Interval cs u b) :
    B.sheaf.upwardSubmodule x Set.univ = fullSubmodule cs u b basis hub B x := by
  ext m
  change (∀ e ∈ Set.univ, B.sheaf.forget.stalkMap x m e = 0) ↔ B.sheaf.forget.stalkMap x m = 0
  simp only [Set.mem_univ,forall_const]
  exact funext_iff.symm

 def fullKernel (x : Interval cs u b) : ModuleData (polynomialGrading ℝ σ) :=
  ModuleData.sub (B.sheaf.vertex x) (fullSubmodule cs u b basis hub B x) (by
    simpa only [fullKernel_eq cs u b basis hub B x] using
      B.sheaf.upwardKernel_homogeneous x Set.univ)

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CharacterReciprocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Conditional boundary-sheaf duality and stalk-character propositions, free sheaves, actual R-reciprocity and lower convolution. StalkCharacterObligation remains a Prop, not an unconditional character theorem or a premise of the R-first route.
-/


section

/-! The finite sums used by the actual local decomposition. The model criteria
are kept explicit here; they are not asserted for the constructed BMP object
or inserted into the main KL theorem. -/
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {V : Type v} [PartialOrder V] {E : Type w} {G : OrderedGraph V E}


instance zeroVertex_subsingleton (x : V) : Subsingleton ((zero (R := R) (G := G)).vertex x) :=
  inferInstanceAs (Subsingleton PUnit)

instance zeroEdge_subsingleton (e : E) : Subsingleton ((zero (R := R) (G := G)).edge e) :=
  inferInstanceAs (Subsingleton PUnit)

structure LocalModels (α : E → R) where
  sheaf : V → Sheaf.{u,v,w,z} (R := R) G
  free : ∀ c x, Module.Free R ((sheaf c).vertex x)
  finite : ∀ c x, Module.Finite R ((sheaf c).vertex x)
  quotient : ∀ c, (sheaf c).UpperQuotient α
  generated : ∀ c, (sheaf c).Generated
  flabby : ∀ c, (sheaf c).Flabby
  support : ∀ c x, ¬x ≤ c → Subsingleton ((sheaf c).vertex x)
  top : ∀ c, (sheaf c).vertex c ≃ₗ[R] R
  minimal : ∀ c x, x ≠ c → LinearMap.ker ((sheaf c).stalkMap x) ≤
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R ((sheaf c).vertex x))

inductive ModelSum (O : V → Sheaf.{u,v,w,z} (R := R) G) (U : Set V) :
    Sheaf.{u,v,w,z} (R := R) G → Prop where
  | zero : ModelSum O U zero
  | add {B} : ModelSum O U B → ∀ c ∈ U, ∀ n : ℕ,
      ModelSum O U (prod B (pi (fun _ : Fin n => O c)))

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
open scoped Pointwise
universe ur uv ue uz
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E}

/-- Equality of embedded images with a scalar on the upper image. -/
def ScaledImages (B : Sheaf.{ur,uv,ue,uz} (R := R) G) (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R) : Prop :=
  ∀ z : B.edge e,
    (∃ v ∈ B.upwardKernel (G.source e) F, B.lower e v=z) ↔
    ∃ w ∈ B.upwardKernel (G.target e) H, r • B.upper e w=z

theorem prod_upwardKernel_iff (B C : Sheaf.{ur,uv,ue,uz} (R := R) G)
    (x : V) (F : Set (Outgoing (G := G) x)) (v : (prod B C).vertex x) :
    v ∈ (prod B C).upwardKernel x F ↔
      v.1 ∈ B.upwardKernel x F ∧ v.2 ∈ C.upwardKernel x F := by
  constructor
  · intro h
    constructor
    · rintro ⟨e,heq⟩ he
      subst x
      exact congrArg Prod.fst (h ⟨e,rfl⟩ he)
    · rintro ⟨e,heq⟩ he
      subst x
      exact congrArg Prod.snd (h ⟨e,rfl⟩ he)
  · rintro ⟨hB,hC⟩ ⟨e,heq⟩ he
    subst x
    exact Prod.ext (hB ⟨e,rfl⟩ he) (hC ⟨e,rfl⟩ he)

theorem pi_upwardKernel_iff {ι : Type*} (B : ι → Sheaf.{ur,uv,ue,uz} (R := R) G)
    (x : V) (F : Set (Outgoing (G := G) x)) (v : (pi B).vertex x) :
    v ∈ (pi B).upwardKernel x F ↔ ∀ i, v i ∈ (B i).upwardKernel x F := by
  constructor
  · rintro h i ⟨e,heq⟩ he
    subst x
    exact congrFun (h ⟨e,rfl⟩ he) i
  · rintro h ⟨e,heq⟩ he
    subst x
    exact funext (fun i => h i ⟨e,rfl⟩ he)

end KLInvariance.MomentGraph.Sheaf

end


section

/-! Actual full upward kernels commute with finite graded sums, shifts and
sheaf isomorphisms. No freeness is inferred without a free model. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  [IsNoetherianRing A] {𝓐 : ℤ → Submodule k A}
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 def kernelProdEquiv (B C : GradedSheaf (𝓐 := 𝓐) G) (x : V) :
    kernelData (prod B C) x ≃ₗ[A] ((kernelData B x).prod (kernelData C x)) where
  toFun m := ⟨⟨m.val.1,((Sheaf.prod_upwardKernel_iff B.forget C.forget x Set.univ m.val).mp m.property).1⟩,
    ⟨m.val.2,((Sheaf.prod_upwardKernel_iff B.forget C.forget x Set.univ m.val).mp m.property).2⟩⟩
  invFun m := ⟨⟨m.1.val,m.2.val⟩,(Sheaf.prod_upwardKernel_iff B.forget C.forget x Set.univ _).mpr
    ⟨m.1.property,m.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 def kernelPiEquiv {ι : Type um} [Fintype ι] (B : ι → GradedSheaf (𝓐 := 𝓐) G) (x : V) :
    kernelData (pi B) x ≃ₗ[A] ModuleData.pi (fun i => kernelData (B i) x) where
  toFun m i := ⟨m.val i,(Sheaf.pi_upwardKernel_iff (fun i => (B i).forget) x Set.univ m.val).mp m.property i⟩
  invFun m := ⟨(fun i => (m i).val),(Sheaf.pi_upwardKernel_iff (fun i => (B i).forget) x Set.univ _).mpr
    (fun i => (m i).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 def kernelShiftEquiv (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) (d : ℕ) :
    kernelData (B.shift d) x ≃ₗ[A] (kernelData B x).shift d := LinearEquiv.refl A _

 def Iso.kernelEquiv {B C : GradedSheaf (𝓐 := 𝓐) G} (j : Iso B C) (x : V) :
    kernelData B x ≃ₗ[A] kernelData C x where
  toFun m := ⟨j.vertex x m.val,(j.toIso.upwardKernel_iff x Set.univ m.val).mpr m.property⟩
  invFun m := ⟨(j.vertex x).symm m.val,(j.toIso.symm.upwardKernel_iff x Set.univ m.val).mpr m.property⟩
  left_inv m := Subtype.ext ((j.vertex x).symm_apply_apply m.val)
  right_inv m := Subtype.ext ((j.vertex x).apply_symm_apply m.val)
  map_add' m n := Subtype.ext (map_add (j.vertex x) m.val n.val)
  map_smul' a m := Subtype.ext (map_smul (j.vertex x) a m.val)

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 instance kernelShiftFree (B : GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V) (d : ℕ)
    [Module.Free (MvPolynomial σ k) (kernelData B x)] :
    Module.Free (MvPolynomial σ k) (kernelData (B.shift d) x) :=
  Module.Free.of_equiv (kernelShiftEquiv B x d).symm

 instance kernelProdFree (B C : GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V)
    [Module.Free (MvPolynomial σ k) (kernelData B x)]
    [Module.Free (MvPolynomial σ k) (kernelData C x)] :
    Module.Free (MvPolynomial σ k) (kernelData (prod B C) x) :=
  Module.Free.of_equiv (kernelProdEquiv B C x).symm

 instance kernelPiFree {ι : Type um} [Fintype ι]
    (B : ι → GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V)
    [∀ i, Module.Free (MvPolynomial σ k) (kernelData (B i) x)] :
    Module.Free (MvPolynomial σ k) (kernelData (pi B) x) :=
  Module.Free.of_equiv (kernelPiEquiv B x).symm

 instance kernelZeroFree (x : V) :
    Module.Free (MvPolynomial σ k) (kernelData (zero (𝓐 := polynomialGrading k σ) (G := G)) x) := by
  let : Subsingleton (kernelData (zero (𝓐 := polynomialGrading k σ) (G := G)) x) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  infer_instance

 theorem ModelSum.kernelFree {O : V → GradedSheaf (𝓐 := polynomialGrading k σ) G}
    (hf : ∀ y x, Module.Free (MvPolynomial σ k) (kernelData (O y) x))
    {U : Set V} {B : GradedSheaf (𝓐 := polynomialGrading k σ) G}
    (h : ModelSum O U B) (x : V) : Module.Free (MvPolynomial σ k) (kernelData B x) := by
  induction h with
  | zero => infer_instance
  | @add C _ c _ n d ih =>
    let _ := ih
    let _ := hf c x
    infer_instance

 def freeKernelChar (B : GradedSheaf (𝓐 := polynomialGrading k σ) G)
    (hf : ∀ x, Module.Free (MvPolynomial σ k) (kernelData B x)) (x : V) : Polynomial ℤ := by
  let := hf x
  exact (kernelData B x).char

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  [IsNoetherianRing A] {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}
noncomputable section
attribute [local instance] Classical.propDecidable
variable {K : Set V} {hK : IsLowerSet K}

omit [IsNoetherianRing A] in
 theorem lowerExtend_kernel_iff (B : GradedSheaf (𝓐 := 𝓐) (lowerGraph G K hK))
    (x : K) (m : B.lowerExtend.vertex x.val) :
    m∈B.lowerExtend.upwardSubmodule x.val Set.univ ↔
      B.lowerExtendVertex x m∈B.upwardSubmodule x Set.univ := by
  constructor
  · intro hm e _
    rcases e with ⟨⟨e,he⟩,hx⟩
    cases hx
    have hh := hm ⟨e,rfl⟩ (Set.mem_univ _)
    exact congrFun hh ⟨⟨he⟩⟩
  · intro hm e _
    rcases x with ⟨x,hx⟩
    rcases e with ⟨e,he⟩
    change G.source e=x at he
    subst x
    apply funext
    intro h
    have hh := hm ⟨⟨e,h.down.down⟩,rfl⟩ (Set.mem_univ _)
    exact hh

 def lowerExtendKernelEquiv (B : GradedSheaf (𝓐 := 𝓐) (lowerGraph G K hK))
    (x : K) : kernelData B.lowerExtend x.val ≃ₗ[A] kernelData B x where
  toFun m := ⟨B.lowerExtendVertex x m.val,(lowerExtend_kernel_iff B x m.val).mp m.property⟩
  invFun m := ⟨(B.lowerExtendVertex x).symm m.val,(lowerExtend_kernel_iff B x _).mpr (by
    simpa only [LinearEquiv.apply_symm_apply] using m.property)⟩
  left_inv m := Subtype.ext ((B.lowerExtendVertex x).symm_apply_apply m.val)
  right_inv m := Subtype.ext ((B.lowerExtendVertex x).apply_symm_apply m.val)
  map_add' m n := Subtype.ext (map_add (B.lowerExtendVertex x) m.val n.val)
  map_smul' a m := Subtype.ext (map_smul (B.lowerExtendVertex x) a m.val)

end
end KLInvariance.MomentGraph.GradedSheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DyerPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite character cancellation, reflection-ratio orders and adapted Dyer decreasing paths.
-/


section


namespace KLInvariance.TitsSpace.PlaneBasis
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

def cosetIntervalMap {a₀ u b : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P}
    (hlo : BruhatLE cs u ((g : W)*a₀)) (hhi : BruhatLE cs ((k : W)*a₀) b) :
    Interval B.system g k ↪ Interval cs u b where
  toFun z := ⟨(z.val : W)*a₀,bruhat_trans cs hlo (B.coset_bruhat hmin z.property.1),
    bruhat_trans cs (B.coset_bruhat hmin z.property.2) hhi⟩
  inj' := by
    intro x y he
    exact Subtype.ext (Subtype.ext (mul_right_cancel (congrArg Subtype.val he)))

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Geometric orders adapted to a fixed upper vertex. These are honest
ratios of linear functionals, with a strictly positive denominator. They
will be used only as a permissible choice of the source's schedule. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

namespace RatioOrder
variable (O : RatioOrder (M := M) (cs := cs))

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_8
theorem turn_ratio_injective (i : I) (k : ℝ) (hk : k ≠ 0)
    (hp : PositiveFunctional (O.turnDenominator i k)) :
    Function.Injective (fun a : PositiveRoot M cs =>
      O.turnNumerator i a.val / O.turnDenominator i k a.val) := by
  intro a b hab
  have hh (a : PositiveRoot M cs) : O.denominator (action M cs (cs.simple i) a.val) ≠ 0 := by
    rcases (a.property.1.act (cs.simple i)).sign with hpos|hneg
    · have h := O.denominator_pos (positiveAction (cs.simple i) a)
      rw [positiveAction_eq_of_nonneg _ _ hpos] at h
      exact h.ne'
    · have h := O.denominator_pos (positiveAction (cs.simple i) a)
      rw [positiveAction_eq_of_nonpos _ _ hneg,map_neg] at h
      exact (neg_pos.mp h).ne
  have hc := (div_eq_div_iff (hp.root_pos a).ne' (hp.root_pos b).ne').mp hab
  change O.numerator (action M cs (cs.simple i) a.val) *
      (O.numerator (action M cs (cs.simple i) b.val) -
        k*O.denominator (action M cs (cs.simple i) b.val)) =
    O.numerator (action M cs (cs.simple i) b.val) *
      (O.numerator (action M cs (cs.simple i) a.val) -
        k*O.denominator (action M cs (cs.simple i) a.val)) at hc
  have hcross : O.numerator (action M cs (cs.simple i) a.val) *
      O.denominator (action M cs (cs.simple i) b.val) =
    O.numerator (action M cs (cs.simple i) b.val) *
      O.denominator (action M cs (cs.simple i) a.val) := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show k * (O.numerator (action M cs (cs.simple i) a.val) *
      O.denominator (action M cs (cs.simple i) b.val) -
        O.numerator (action M cs (cs.simple i) b.val) *
      O.denominator (action M cs (cs.simple i) a.val)) = 0 by nlinarith [hc])).resolve_left hk
  have he := (div_eq_div_iff (hh a) (hh b)).mpr hcross
  have hval (a : PositiveRoot M cs) :
      O.numerator (action M cs (cs.simple i) a.val) /
          O.denominator (action M cs (cs.simple i) a.val) =
        O.slope (positiveAction (cs.simple i) a) := by
    unfold slope
    rcases (a.property.1.act (cs.simple i)).sign with hpos|hneg
    · rw [positiveAction_eq_of_nonneg _ _ hpos]
    · rw [positiveAction_eq_of_nonpos _ _ hneg,map_neg,map_neg,neg_div_neg_eq]
  rw [hval a,hval b] at he
  exact (positiveActionEquiv (cs.simple i)).injective (O.slope_injective he)

def turn (i : I) (k : ℝ) (hk : k ≠ 0)
    (hp : PositiveFunctional (O.turnDenominator i k)) : RatioOrder (M := M) (cs := cs) :=
  ⟨O.turnDenominator i k,O.turnNumerator i,hp,O.turn_ratio_injective i k hk hp⟩


end RatioOrder

end
end KLInvariance.TitsSpace

end


section

/-! Rank-two path reversal in the actual induced root plane, for every finite
full interval. This is a required Dyer wall-crossing relation, not the Dyer
identification itself. -/

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
open Dihedral BruhatGraph

attribute [local instance] OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable
/-- Restriction of the actual geometric root slope to a full plane interval. -/
def intervalEdgeSlope (lo hi : planeSubgroup M cs P) (e : Edge B.system lo hi) : ℝ :=
  geometricSlope (B.edgeRoot e.property)

end PlaneBasis
end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ReflectionOrders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite sweep algebra, wall orders and the full reflection-order path formula.
-/


section

/-! Algebra and finite ordered-list bookkeeping for wall crossings. -/
namespace KLInvariance.SchedulePaths
universe u v w
variable {E : Type u} {A : Type v} {Λ : Type w} [LinearOrder A] [LinearOrder Λ]
noncomputable section

attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions_4
attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidableEq_solutions
def scheduleBlock (F : Finset E) (primary : E → A) (score : E → Λ) (a : A) : List E :=
  sortedSchedule (F.filter (fun e => primary e=a)) score

def groupedSchedule (F : Finset E) (primary : E → A) (score : E → Λ) : List E :=
  (blockValues F primary).flatMap (scheduleBlock F primary score)

@[simp] theorem mem_blockValues (F : Finset E) (primary : E → A) (a : A) :
    a ∈ blockValues F primary ↔ ∃ e ∈ F, primary e=a := by
  simp [blockValues]

omit [LinearOrder A] in
@[simp] theorem mem_scheduleBlock (F : Finset E) (primary : E → A) (score : E → Λ)
    (a : A) (e : E) : e ∈ scheduleBlock F primary score a ↔ e ∈ F ∧ primary e=a := by
  simp [scheduleBlock]

@[simp] theorem mem_groupedSchedule (F : Finset E) (primary : E → A) (score : E → Λ)
    (e : E) : e ∈ groupedSchedule F primary score ↔ e ∈ F := by
  constructor
  · intro he
    obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp he
    exact ((mem_scheduleBlock F primary score a e).mp ha).1
  · intro he
    apply List.mem_flatMap.mpr
    exact ⟨primary e,(mem_blockValues F primary _).mpr ⟨e,he,rfl⟩,
      (mem_scheduleBlock F primary score _ _).mpr ⟨he,rfl⟩⟩

end
end KLInvariance.SchedulePaths

end


section

/-! Generic pencils of genuine linear root-label functionals. At a wall all
roots of a tied block belong to one full actual root plane. -/

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_11
omit [Fintype I] in
@[simp] theorem pencil_zero (f g : Module.Dual ℝ (I → ℝ)) : pencil f g 0=f := by
  simp [pencil]
omit [Fintype I] in
@[simp] theorem pencil_one (f g : Module.Dual ℝ (I → ℝ)) : pencil f g 1=g := by
  simp [pencil]

def rootDifference (a b : PositiveRoot M cs) : I → ℝ := normalizedRoot b-normalizedRoot a

def wallVector (f : Module.Dual ℝ (I → ℝ)) (a b c : PositiveRoot M cs) : I → ℝ :=
  f (rootDifference a b) • rootDifference a c -
    f (rootDifference a c) • rootDifference a b

/-- This is an actual genericity condition on linear functionals, not
an assumed path or Hecke identity. -/
def Transverse (f g : Module.Dual ℝ (I → ℝ)) : Prop :=
  ∀ a b c : PositiveRoot M cs, g (wallVector f a b c)=0 → wallVector f a b c=0

end
end KLInvariance.TitsSpace

end


section

/-! Finite wall crossing for actual reflection-edge path matrices. -/
namespace KLInvariance.WallDyer
open Module SchedulePaths TitsSpace AdaptedDyer
open scoped Topology
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.WallDyer.instDecidable_solutions
def rootValue (f : Module.Dual ℝ (I → ℝ)) (e : Edge cs) : ℝ :=
  f (normalizedRoot (rootLabel cs e))

def rootPlaneTies (f : Module.Dual ℝ (I → ℝ)) : Prop :=
  ∀ a b : PositiveRoot M cs, a ≠ b → f (normalizedRoot a)=f (normalizedRoot b) →
    ∀ c : PositiveRoot M cs, f (normalizedRoot c)=f (normalizedRoot a) ↔
      c.val ∈ rootPlane a b

def schedule (f : Module.Dual ℝ (I → ℝ)) (b : W) : List (Edge cs) :=
  sortedSchedule (edgeFinset cs b) (lexEdgeScore f)

def entry {R : Type*} [Semiring R] (T : R) (f : Module.Dual ℝ (I → ℝ))
    (b x y : W) : R :=
  dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) (schedule f b) x

end
end KLInvariance.WallDyer

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DihedralIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Signed dihedral coordinates, actual dihedral intervals, exact later-edge counts and root-plane calculations.
-/


section

/-! Actual degree-one splines in the ambient extended Tits realization.
They supply the interpolation factors needed for the relative rank-two model. -/
namespace KLInvariance.TitsSpace
open Module
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def linearPolynomial : Extended M →ₗ[ℝ] MvPolynomial σ ℝ :=
  (SymmetricAlgebra.equivMvPolynomial basis).toLinearMap.comp
    (SymmetricAlgebra.ι ℝ (Extended M))

 def orbitSpline (y : W) (v₀ : Extended M) (v : W) : MvPolynomial σ ℝ :=
  linearPolynomial basis (extendedAction M cs (v*y⁻¹) v₀ - v₀)

 theorem orbitSpline_self (y : W) (v₀ : Extended M) : orbitSpline cs basis y v₀ y = 0 := by
  simp [orbitSpline]

 theorem orbitSpline_reflection {t : W} {a : I → ℝ}
    (ha : Represents M cs t a) (y x : W) (v₀ : Extended M) :
    linearPolynomial basis (embed M a) ∣
      orbitSpline cs basis y v₀ x - orbitSpline cs basis y v₀ (t*x) := by
  let c := extendedForm M (embed M a) (extendedAction M cs (x*y⁻¹) v₀)
  have heq : extendedAction M cs (t*x*y⁻¹) v₀ =
      extendedAction M cs (x*y⁻¹) v₀ - c • embed M a := by
    rw [mul_assoc,map_mul,LinearEquiv.mul_apply,ha.formula]
  unfold orbitSpline
  rw [← map_sub,heq]
  have hv : (extendedAction M cs (x*y⁻¹) v₀ - v₀) -
      (extendedAction M cs (x*y⁻¹) v₀ - c • embed M a - v₀) = c • embed M a := by abel
  rw [hv,map_smul]
  exact ⟨algebraMap ℝ (MvPolynomial σ ℝ) c, by simp [Algebra.smul_def,mul_comm]⟩

 theorem exists_pair_vector {t r : W} {a d : I → ℝ}
    (ha : Represents M cs t a) (hd : Represents M cs r d) (htr : t ≠ r) :
    ∃ v₀ : Extended M, extendedForm M (embed M a) v₀ = -1 ∧
      extendedForm M (embed M d) v₀ = 0 := by
  have hli := (ha.extended_independent_of_ne hd htr).map'
    (extendedForm M) (extendedForm_spec M).2.1.ker_eq_bot
  have hli' : LinearIndependent ℝ ![extendedForm M (embed M a),
      extendedForm M (embed M d)] := by
    convert hli using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    fin_cases i <;> rfl
  obtain ⟨v₀,hv₀⟩ := ReflectionPlane.formPair_surjective _ _ hli' (-1,0)
  exact ⟨v₀,congrArg Prod.fst hv₀,congrArg Prod.snd hv₀⟩

 theorem orbitSpline_pair_factor {x y z t r : W} {a d : I → ℝ}
    (ha : Represents M cs t a) (hd : Represents M cs r d)
    (hxy : x*y⁻¹=t) (hzy : z*y⁻¹=r) (hxz : x ≠ z) :
    ∃ v₀ : Extended M,
      orbitSpline cs basis y v₀ x = linearPolynomial basis (embed M a) ∧
      orbitSpline cs basis y v₀ y = 0 ∧ orbitSpline cs basis y v₀ z = 0 := by
  have htr : t ≠ r := by
    intro he
    apply hxz
    exact mul_right_cancel (hxy.trans (he.trans hzy.symm))
  obtain ⟨v₀,hv₀a,hv₀d⟩ := exists_pair_vector cs ha hd htr
  refine ⟨v₀,?_,orbitSpline_self cs basis y v₀,?_⟩
  · simp only [orbitSpline,hxy,ha.formula,hv₀a]
    congr 1
    module
  · simp only [orbitSpline,hzy,hd.formula,hv₀d,zero_smul,sub_zero,sub_self,map_zero]

 theorem orbitSpline_single_factor {x y t : W} {a : I → ℝ}
    (ha : Represents M cs t a) (hxy : x*y⁻¹=t) :
    ∃ v₀ : Extended M,
      orbitSpline cs basis y v₀ x = linearPolynomial basis (embed M a) ∧
      orbitSpline cs basis y v₀ y = 0 := by
  let v₀ : Extended M := (-1/2 : ℝ) • embed M a
  have hv₀ : extendedForm M (embed M a) v₀ = -1 := by
    simp only [v₀,map_smul,smul_eq_mul,embed,(extendedForm_spec M).2.2,ha.isRoot.norm]
    norm_num
  refine ⟨v₀,?_,orbitSpline_self cs basis y v₀⟩
  simp only [orbitSpline,hxy,ha.formula,hv₀]
  congr 1
  module

end
end KLInvariance.TitsSpace

end


section

/-! Polynomial interpolation on an actual dihedral reflection subgroup.
The ambient realization, including all fixed directions and degenerate root
planes, is retained; no character theorem is assumed. -/
namespace KLInvariance.Dihedral
open Module TitsSpace
universe u v w us
variable {H : Type w} [Group H] {N : CoxeterMatrix Bool} (ds : CoxeterSystem N H)
  {I : Type u} [Fintype I] {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (φ : H →* W)
  (hφ : ∀ t, ds.IsReflection t → cs.IsReflection (φ t))
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def interpolationRoot (x c : H) (y : oppositeExternal ds x c) : PositiveRoot M cs :=
  positiveRoot M cs ⟨φ (y.val*x⁻¹), hφ _ (oppositeExternal_reflection ds y.property)⟩

 theorem interpolation_exists (hφinj : Function.Injective φ) {x c : H}
    (hxc : BruhatLE ds x c) : ∃ F : H → MvPolynomial σ ℝ,
      (∀ t, ds.IsReflection t → ∀ (a : I → ℝ), Represents M cs (φ t) a → ∀ v,
        linearPolynomial basis (embed M a) ∣ F v-F (t*v)) ∧
      F x = ∏ y : oppositeExternal ds x c,
        linearPolynomial basis (embed M (interpolationRoot ds cs φ hφ x c y).val) ∧
      ∀ z, BruhatLE ds z c → ¬ BruhatLE ds z x → F z = 0 := by
  classical
  let Y := {y // y ∈ oppositeExternal ds x c}
  let Z := {z // z ∈ sameExternal ds x c}
  have hc : Fintype.card Z ≤ Fintype.card Y := by
    change Fintype.card ↥(sameExternal ds x c) ≤ Fintype.card ↥(oppositeExternal ds x c)
    rw [Fintype.card_coe,Fintype.card_coe]
    exact external_parity_card_le ds hxc
  obtain ⟨j⟩ := Function.Embedding.nonempty_of_card_le hc
  have hfac (y : Y) : ∃ v₀ : Extended M,
      orbitSpline cs basis (φ y.val) v₀ (φ x) =
        linearPolynomial basis (embed M (interpolationRoot ds cs φ hφ x c y).val) ∧
      orbitSpline cs basis (φ y.val) v₀ (φ y.val) = 0 ∧
      ∀ z : Z, j z = y → orbitSpline cs basis (φ y.val) v₀ (φ z.val) = 0 := by
    have ht := oppositeExternal_reflection ds y.property
    have ha := positiveRoot_represents M cs
      ⟨φ (y.val*x⁻¹),hφ _ ht⟩
    have hxy₀ : x*y.val⁻¹=y.val*x⁻¹ := by simpa only [mul_inv_rev,inv_inv] using ht.inv
    have hxy : φ x*(φ y.val)⁻¹=φ (y.val*x⁻¹) := by
      rw [← map_inv,← map_mul,hxy₀]
    by_cases hex : ∃ z : Z, j z = y
    · obtain ⟨z,hz⟩ := hex
      have hzprop := Finset.mem_filter.mp z.property
      have hyprop := Finset.mem_filter.mp y.property
      have hr : ds.IsReflection (z.val*y.val⁻¹) := reflection_of_parity ds (by omega)
      let d := positiveRoot M cs ⟨φ (z.val*y.val⁻¹),hφ _ hr⟩
      have hd : Represents M cs (φ (z.val*y.val⁻¹)) d.val := positiveRoot_represents M cs ⟨φ (z.val*y.val⁻¹),hφ _ hr⟩
      have hxz : φ x ≠ φ z.val := by
        intro he
        have he' := hφinj he
        have hh := (mem_externalLower ds x c z.val).mp hzprop.1
        exact hh.2 (he' ▸ bruhat_refl ds x)
      obtain ⟨v₀,ha',hy',hz0'⟩ := orbitSpline_pair_factor cs basis ha hd hxy
        (by rw [map_mul,map_inv]) hxz
      refine ⟨v₀,ha',hy',?_⟩
      intro z' hz'
      have he := j.injective (hz'.trans hz.symm)
      simpa only [he] using hz0'
    · obtain ⟨v₀,ha',hy'⟩ := orbitSpline_single_factor cs basis ha hxy
      exact ⟨v₀,ha',hy',fun z hz => (hex ⟨z,hz⟩).elim⟩
  choose v₀ hv₀ hy₀ hz₀ using hfac
  let F : H → MvPolynomial σ ℝ := fun v => ∏ y : Y,
    orbitSpline cs basis (φ y.val) (v₀ y) (φ v)
  refine ⟨F,?_,?_,?_⟩
  · intro t _ht a ha v
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq.mp
    change Ideal.Quotient.mk _ (∏ y : Y, orbitSpline cs basis (φ y.val) (v₀ y) (φ v)) =
      Ideal.Quotient.mk _ (∏ y : Y, orbitSpline cs basis (φ y.val) (v₀ y) (φ (t*v)))
    simp only [map_prod]
    apply Finset.prod_congr rfl
    intro y _
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    rw [map_mul]
    exact orbitSpline_reflection cs basis ha _ _ _
  · exact Finset.prod_congr rfl (fun y _ => hv₀ y)
  · intro z hzc hzx
    have hz : z ∈ externalLower ds x c := (mem_externalLower ds x c z).mpr ⟨hzc,hzx⟩
    by_cases hp : ds.length z % 2 = ds.length x % 2
    · let z' : Z := ⟨z,Finset.mem_filter.mpr ⟨hz,hp⟩⟩
      exact Finset.prod_eq_zero (Finset.mem_univ (j z')) (hz₀ (j z') z' rfl)
    · let y : Y := ⟨z,Finset.mem_filter.mpr ⟨hz,hp⟩⟩
      exact Finset.prod_eq_zero (Finset.mem_univ y) (hy₀ y)

end
end KLInvariance.Dihedral

end


section

/-! An elementary flabbiness criterion for the exact rank-one model. Flow-down
sections with the genuine product of outgoing labels suffice. The pairwise
relative-primality condition will be instantiated by actual root labels. -/
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] [DecompositionMonoid R]
  {V : Type uv} [PartialOrder V] {E : Type ue}
  (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section
variable [Fintype E] [DecidableEq V]

omit [DecompositionMonoid R] [Fintype E] [DecidableEq V] in
 theorem structureCompatible_iff (Ω : Set V) (f : (structureSheaf G α c).Assignment) :
    (structureSheaf G α c).CompatibleOn Ω f ↔
      ∀ e, G.source e ∈ Ω → G.target e ∈ Ω → ∀ h : PLift (G.target e ≤ c),
        α e ∣ f (G.source e) ⟨(G.increasing e).le.trans h.down⟩ - f (G.target e) h := by
  constructor
  · intro hf e hs ht h
    exact Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq.mp (congrFun (hf e hs ht) h))
  · intro hf e hs ht
    funext h
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (hf e hs ht h))

end
end KLInvariance.MomentGraph.Sheaf

end


section

/-! Flabbiness of the exact rank-one model with ambient labels, proved by
interpolation rather than an assumed character theorem. -/
namespace KLInvariance.Dihedral
open Module TitsSpace BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v w us
variable {H : Type w} [Group H] {N : CoxeterMatrix Bool} (ds : CoxeterSystem N H)
  {I : Type u} [Fintype I] {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (φ : H →* W)
  (hφ : ∀ t, ds.IsReflection t → cs.IsReflection (φ t))
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def inducedRoot (b : H) (e : Edge ds 1 b) : PositiveRoot M cs :=
  positiveRoot M cs ⟨φ (label ds 1 b e),hφ _ (label_isReflection ds 1 b e)⟩

 def inducedLabel (b : H) (e : Edge ds 1 b) : MvPolynomial σ ℝ :=
  linearPolynomial basis (embed M (inducedRoot ds cs φ hφ b e).val)

 theorem external_step {x c y : H} (hy : y ∈ oppositeExternal ds x c) :
    BruhatStep ds x y := by
  classical
  obtain ⟨hm,hp⟩ := Finset.mem_filter.mp hy
  obtain ⟨_,hn⟩ := (mem_externalLower ds x c y).mp hm
  have hl : ds.length x < ds.length y := by
    have hh : ¬ ds.length y < ds.length x := fun h => hn (shorter_bruhat ds h)
    omega
  exact ⟨hl,y*x⁻¹,oppositeExternal_reflection ds hy,by group⟩

 theorem step_external {x c y : H} (hy : BruhatStep ds x y) (hyc : BruhatLE ds y c) :
    y ∈ oppositeExternal ds x c := by
  classical
  refine Finset.mem_filter.mpr ⟨(mem_externalLower ds x c y).mpr ⟨hyc,?_⟩,?_⟩
  · exact fun h => (length_le_of_bruhat ds h).not_gt hy.1
  · have hh := (step_iff_odd ds x y).mp hy
    rw [Nat.odd_iff] at hh
    omega

 variable (b : H) [Fintype (Edge ds 1 b)] [DecidableEq (Interval ds 1 b)]

 def externalEdge (x c : Interval ds 1 b) (y : oppositeExternal ds x.val c.val) : Edge ds 1 b :=
  ⟨(x,⟨y.val,one_bruhat ds y.val,
    bruhat_trans ds ((mem_externalLower ds x.val c.val y.val).mp
      (Finset.mem_filter.mp y.property).1).1 c.property.2⟩),external_step ds y.property⟩

 theorem externalEdge_mem (x c : Interval ds 1 b) (y : oppositeExternal ds x.val c.val) :
    externalEdge ds b x c y ∈ modelOutgoing (graph ds 1 b) c x := by
  classical
  apply (mem_modelOutgoing _ _ _ _).mpr
  exact ⟨rfl,((mem_externalLower ds x.val c.val y.val).mp
    (Finset.mem_filter.mp y.property).1).1⟩

 def outgoingEquiv (x c : Interval ds 1 b) :
    ↥(oppositeExternal ds x.val c.val) ≃ ↥(modelOutgoing (graph ds 1 b) c x) where
  toFun y := ⟨externalEdge ds b x c y,externalEdge_mem ds b x c y⟩
  invFun e := ⟨(target ds 1 b e.val).val,by
    obtain ⟨hs,ht⟩ := (mem_modelOutgoing _ _ _ _).mp e.property
    have hh := e.val.property
    change BruhatStep ds (source ds 1 b e.val).val (target ds 1 b e.val).val at hh
    change source ds 1 b e.val = x at hs
    rw [hs] at hh
    exact step_external ds hh ht⟩
  left_inv _ := rfl
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact ((mem_modelOutgoing _ _ _ _).mp e.property).1.symm
    · rfl

omit [Fintype (Edge ds 1 b)] [DecidableEq (Interval ds 1 b)] in
 theorem inducedLabel_prime (e : Edge ds 1 b) : Prime (inducedLabel ds cs φ hφ basis b e) := by
  apply (MulEquiv.prime_iff (SymmetricAlgebra.equivMvPolynomial basis)).mpr
  apply EdgeAlgebra.symmetric_ι_prime
  intro h
  exact (inducedRoot ds cs φ hφ b e).property.1.ne_zero (congrArg Prod.fst h)

omit [Fintype (Edge ds 1 b)] [DecidableEq (Interval ds 1 b)] in
 theorem label_eq_of_induced_dvd (hφinj : Function.Injective φ) {e f : Edge ds 1 b}
    (h : inducedLabel ds cs φ hφ basis b e ∣ inducedLabel ds cs φ hφ basis b f) :
    label ds 1 b e = label ds 1 b f := by
  apply hφinj
  suffices he : inducedRoot ds cs φ hφ b e = inducedRoot ds cs φ hφ b f from
    congrArg Subtype.val ((positiveRootEquiv M cs).injective he)
  by_contra hn
  have hd : SymmetricAlgebra.ι ℝ (Extended M) (embed M (inducedRoot ds cs φ hφ b e).val) ∣
      SymmetricAlgebra.ι ℝ (Extended M) (embed M (inducedRoot ds cs φ hφ b f).val) := by
    obtain ⟨z,hz⟩ := h
    exact ⟨(SymmetricAlgebra.equivMvPolynomial basis).symm z,by
      apply (SymmetricAlgebra.equivMvPolynomial basis).injective
      simpa only [map_mul,AlgEquiv.apply_symm_apply,inducedLabel,linearPolynomial,LinearMap.comp_apply,AlgEquiv.toLinearMap_apply] using hz⟩
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp ((EdgeAlgebra.symmetric_ι_dvd_iff _ _).mp hd)
  have he : r • (inducedRoot ds cs φ hφ b e).val = (1:ℝ) • (inducedRoot ds cs φ hφ b f).val := by
    have hh := congrArg Prod.fst hr
    exact hh.trans (one_smul ℝ _).symm
  exact one_ne_zero ((positiveRoots_independent _ _ hn).eq_zero_of_pair' he).2

end
end KLInvariance.Dihedral

end


section

/-! Instantiation on the actual maximal subgroup of the ambient root plane.
The exact canonical roots, including degenerate/infinite planes, are used. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def modelLabel (b : planeSubgroup M cs P) (e : Edge B.system 1 b) : MvPolynomial σ ℝ :=
  Dihedral.inducedLabel B.system cs (planeSubgroup M cs P).subtype
    (fun t => (B.reflection_iff t).mp) basis b e

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Each finite rank-two set fits in a principal Bruhat interval, even in
an infinite dihedral group. No finite Coxeter-system hypothesis is used. -/
namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]

 theorem bruhat_top_of_all_descents (cs : CoxeterSystem M W) (w : W)
    (hw : ∀ i, cs.length (cs.simple i * w) < cs.length w) (x : W) :
    BruhatLE cs x w := by
  classical
  have hword : ∀ ω, BruhatLE cs (cs.wordProd ω) w := by
    intro ω
    induction ω with
    | nil => simpa only [cs.wordProd_nil] using one_bruhat cs w
    | cons i ω ih =>
      have hu := upperSimple_mono cs i ih
      have hz := le_upperSimple cs i (cs.simple i * cs.wordProd ω)
      rw [upperSimple_mul] at hz
      have he : upperSimple cs i w = w := by simp only [upperSimple,ite_eq_left (hw i)]
      rw [he] at hu
      change BruhatLE cs (cs.simple i * cs.wordProd ω) w
      exact hz.trans hu
  obtain ⟨ω,_,hx⟩ := cs.exists_isReduced x
  rw [hx]
  exact hword ω

namespace Dihedral
variable {N : CoxeterMatrix Bool} (ds : CoxeterSystem N W)

 theorem exists_common_upper (s : Finset W) : ∃ b, ∀ x ∈ s, BruhatLE ds x b := by
  classical
  by_cases hb : BddAbove (Set.range ds.length)
  · have hf : (Set.range ds.length).Finite := hb.finite
    obtain ⟨b,hb⟩ := (Set.range_nonempty ds.length).csSup_mem hf
    have hmax (x : W) : ds.length x ≤ ds.length b := by
      rw [hb]
      exact le_csSup (hf.bddAbove) (Set.mem_range_self x)
    refine ⟨b,fun x _ => bruhat_top_of_all_descents ds b ?_ x⟩
    intro i
    have hle := hmax (ds.simple i*b)
    have hne := ds.length_simple_mul b i
    omega
  · have hn : ∀ n : ℕ, ∃ w, n < ds.length w := by
      intro n
      by_contra h
      push Not at h
      exact hb ⟨n,by rintro m ⟨x,rfl⟩; exact h x⟩
    obtain ⟨b,hb⟩ := hn (s.sup ds.length)
    exact ⟨b,fun x hx => shorter_bruhat ds ((Finset.le_sup hx).trans_lt hb)⟩

end Dihedral
end KLInvariance

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

 theorem length_alt_le_length (cs : CoxeterSystem M W) (i : Bool) {n : ℕ} {w : W}
    (h : n ≤ cs.length w) : cs.length (cs.wordProd (alt i n)) = n := by
  obtain ⟨j,hj⟩ := exists_alt cs w
  have hr : cs.IsReduced (alt j (cs.length w)) := by
    change cs.length (cs.wordProd _) = _
    rw [← hj,length_alt]
  have hn := (reduced_alt_take cs hr h).eq
  rw [length_alt] at hn
  have hi : i=j ∨ i=(!j) := by cases i <;> cases j <;> simp
  rcases hi with rfl|rfl
  · exact hn
  · rw [← swap_alt,length_swap,hn]

 theorem length_indexWord_nat (cs : CoxeterSystem M W) {n : ℕ} {w : W}
    (h : n ≤ cs.length w) : cs.length (indexWord cs n) = n := by
  rw [indexWord_nat]
  exact length_alt_le_length cs false h

 theorem length_indexWord_neg_nat (cs : CoxeterSystem M W) {n : ℕ} {w : W}
    (h : n ≤ cs.length w) : cs.length (indexWord cs (-(n:ℤ))) = n := by
  rw [indexWord_neg_nat]
  exact length_alt_le_length cs true h

end
end KLInvariance.Dihedral

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

 theorem indexWord_step (cs : CoxeterSystem M W) {n : ℕ} {w : W}
    (h : n+1 ≤ cs.length w) : BruhatStep cs (indexWord cs n) (indexWord cs (n+1:ℕ)) := by
  rw [step_iff_odd,length_indexWord_nat cs (show n ≤ cs.length w by omega),
    length_indexWord_nat cs h]
  exact ⟨by omega,by simp⟩

 theorem neg_indexWord_step (cs : CoxeterSystem M W) {n : ℕ} {w : W}
    (h : n+1 ≤ cs.length w) :
    BruhatStep cs (indexWord cs (-(n:ℤ))) (indexWord cs (-((n+1:ℕ):ℤ))) := by
  rw [step_iff_odd,length_indexWord_neg_nat cs (show n ≤ cs.length w by omega),
    length_indexWord_neg_nat cs h]
  exact ⟨by omega,by simp⟩

end KLInvariance.Dihedral

namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 def prefixRoot (w : planeSubgroup M cs P) (n : ℕ) : PositiveRoot M cs :=
  if h : n < B.system.length w then B.edgeRoot (indexWord_step B.system h) else B.left

 def negPrefixRoot (w : planeSubgroup M cs P) (n : ℕ) : PositiveRoot M cs :=
  if h : n < B.system.length w then B.edgeRoot (neg_indexWord_step B.system h) else B.right

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 attribute [local instance] OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable_3
def afterIndicator (x : planeSubgroup M cs P) (α : PositiveRoot M cs)
    (z : planeSubgroup M cs P) : ℕ :=
  if h : BruhatStep B.system x z then
    if geometricSlope α < geometricSlope (B.edgeRoot h) then 1 else 0
  else 0

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 def laterCount (x : planeSubgroup M cs P) (α : PositiveRoot M cs)
    (c : planeSubgroup M cs P) : ℕ :=
  ∑ z ∈ lowerFinset B.system c, B.afterIndicator x α z

end
end KLInvariance.TitsSpace.PlaneBasis

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_PlaneLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Symmetric plane ideals, sheaf localization and scaled local products along genuine edges.
-/


section

/-! The rank-one plane models over the actual flat local coefficient ring.
The local-ring label condition is later supplied by the plane prime. -/
namespace KLInvariance.BruhatGraph
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (u b : W)

 theorem exists_outgoing_below (x c : Interval cs u b) (hxc : x < c) :
    ∃ e : Edge cs u b, source cs u b e = x ∧ target cs u b e ≤ c := by
  rcases Relation.ReflTransGen.cases_head hxc.le with heq | ⟨z,hxz,hzc⟩
  · exact (hxc.ne (Subtype.ext heq)).elim
  · let y : Interval cs u b := ⟨z,bruhat_trans cs x.property.1 (.single hxz),
      bruhat_trans cs hzc c.property.2⟩
    exact ⟨⟨(x,y),hxz⟩,rfl,hzc⟩

end KLInvariance.BruhatGraph

namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] [IsLocalRing R]
  {V : Type uv} [PartialOrder V] {E : Type ue} (G : OrderedGraph V E) (α : E → R)
noncomputable section

 def structureLocalModels
    (hα : ∀ e, α e ∈ IsLocalRing.maximalIdeal R)
    (hreach : ∀ x c, x < c → ∃ e, G.source e = x ∧ G.target e ≤ c)
    (hfl : ∀ c, (structureSheaf G α c).Flabby) : LocalModels (G := G) α where
  sheaf := structureSheaf G α
  free := structureSheaf_free G α
  finite := structureSheaf_finite G α
  quotient := structureSheaf_upperQuotient G α
  generated := structureSheaf_generated G α
  flabby := hfl
  support := structureSheaf_support G α
  top c := structureVertexIso G α c c le_rfl
  minimal c x hx := structureSheaf_minimal G α c hα (fun x => hreach x c) x hx

end
end KLInvariance.MomentGraph.Sheaf

end


section

/-! The actual plane prime and its localization in the coefficient polynomial
ring of the chosen nondegenerate ambient realization. -/
namespace KLInvariance.TitsSpace
open Module
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def embedLinear : (I → ℝ) →ₗ[ℝ] Extended M where
  toFun := embed M
  map_add' _ _ := by simp [embed]
  map_smul' _ _ := by simp [embed]

 theorem embedLinear_injective : Function.Injective (embedLinear (M := M)) := by
  intro a b hab
  exact congrArg Prod.fst hab

 def planePrime (P : Submodule ℝ (I → ℝ)) : Ideal (MvPolynomial σ ℝ) :=
  Ideal.map (SymmetricAlgebra.equivMvPolynomial basis).toRingHom
    (SymmetricPlaneIdeal.ideal (P.map (embedLinear (M := M))))

 instance planePrime_isPrime (P : Submodule ℝ (I → ℝ)) : (planePrime basis P).IsPrime :=
  Ideal.map_isPrime_of_equiv (SymmetricAlgebra.equivMvPolynomial basis)

 theorem linear_mem_planePrime_iff (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    linearPolynomial basis (embed M a) ∈ planePrime basis P ↔ a ∈ P := by
  rw [planePrime,Ideal.mem_map_iff_of_surjective (SymmetricAlgebra.equivMvPolynomial basis).toRingHom
    (SymmetricAlgebra.equivMvPolynomial basis).surjective]
  change (∃ z, z ∈ SymmetricPlaneIdeal.ideal (P.map (embedLinear (M := M))) ∧
    SymmetricAlgebra.equivMvPolynomial basis z =
      SymmetricAlgebra.equivMvPolynomial basis (SymmetricAlgebra.ι ℝ (Extended M) (embed M a))) ↔ _
  constructor
  · rintro ⟨z,hz,he⟩
    have h := (SymmetricAlgebra.equivMvPolynomial basis).injective he
    subst z
    have ha := (SymmetricPlaneIdeal.ι_mem_iff _ _).mp hz
    obtain ⟨b,hb,he⟩ := ha
    have he' : b = a := embedLinear_injective he
    exact he' ▸ hb
  · intro ha
    refine ⟨_,(SymmetricPlaneIdeal.ι_mem_iff _ _).mpr ?_,rfl⟩
    exact ⟨a,ha,rfl⟩

 abbrev PlaneRing (P : Submodule ℝ (I → ℝ)) := Localization.AtPrime (planePrime basis P)

 theorem linear_mem_maximal_iff (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (linearPolynomial basis (embed M a)) ∈
      IsLocalRing.maximalIdeal (PlaneRing basis P) ↔ a ∈ P := by
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ (planePrime basis P),
    linear_mem_planePrime_iff]

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem modelLabel_mem_maximal (b : planeSubgroup M cs P) (e : Edge B.system 1 b) :
    algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (B.modelLabel basis b e) ∈
      IsLocalRing.maximalIdeal (PlaneRing basis P) := by
  apply (linear_mem_maximal_iff basis P _).mpr
  apply (Represents.planeSubgroup_mem_iff M cs (positiveRoot_represents M cs _)).mp
  exact (label B.system 1 b e).property

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! The actual finite relative lower ideal in a maximal root-plane coset.
No order-reflection identification with ambient comparability is used. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  (a₀ b : W)
noncomputable section

 def CosetVertex := {d : planeSubgroup M cs P // BruhatLE B.system 1 d ∧
    BruhatLE cs ((d:W)*a₀) b}

 instance cosetOrder : PartialOrder (B.CosetVertex a₀ b) where
  le x y := BruhatLE B.system x.val y.val
  le_refl x := bruhat_refl B.system x.val
  le_trans _ _ _ := bruhat_trans B.system
  le_antisymm x y hxy hyx := Subtype.ext (bruhat_antisymm B.system hxy hyx)

 def cosetAmbient (x : B.CosetVertex a₀ b) : Interval cs 1 b :=
  ⟨(x.val:W)*a₀,one_bruhat cs _,x.property.2⟩

 theorem cosetAmbient_injective : Function.Injective (B.cosetAmbient a₀ b) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact mul_right_cancel (congrArg Subtype.val h)

 instance cosetFinite : Finite (B.CosetVertex a₀ b) := by
  let := interval_finite cs 1 b
  exact Finite.of_injective _ (B.cosetAmbient_injective a₀ b)

 def CosetEdge := {p : B.CosetVertex a₀ b × B.CosetVertex a₀ b //
    BruhatStep B.system p.1.val p.2.val}

 def cosetGraph : OrderedGraph (B.CosetVertex a₀ b) (B.CosetEdge a₀ b) where
  source e := e.val.1
  target e := e.val.2
  increasing e := ⟨.single e.property,fun h => not_lt_of_ge
    (length_le_of_bruhat B.system h) e.property.1⟩

variable (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))

 def cosetEdgeAmbient (e : B.CosetEdge a₀ b) : Edge cs 1 b :=
  ⟨(B.cosetAmbient a₀ b e.val.1,B.cosetAmbient a₀ b e.val.2),
    (B.coset_step_iff hmin _ _).mpr e.property⟩

 def cosetGraphMap : GraphMap (B.cosetGraph a₀ b) (graph cs 1 b) where
  vertex := B.cosetAmbient a₀ b
  edge := B.cosetEdgeAmbient a₀ b hmin
  source _ := rfl
  target _ := rfl

 include hmin in
 theorem coset_lower {d : planeSubgroup M cs P} {x : B.CosetVertex a₀ b}
    (hx : BruhatLE B.system d x.val) : BruhatLE cs ((d:W)*a₀) b :=
  bruhat_trans cs (B.coset_bruhat hmin hx) x.property.2

 include hmin in
 theorem coset_outgoing_below (x c : B.CosetVertex a₀ b) (hxc : x < c) :
    ∃ e : B.CosetEdge a₀ b, (B.cosetGraph a₀ b).source e=x ∧
      (B.cosetGraph a₀ b).target e ≤ c := by
  rcases Relation.ReflTransGen.cases_head hxc.le with heq | ⟨z,hxz,hzc⟩
  · exact (hxc.ne (Subtype.ext heq)).elim
  · let y : B.CosetVertex a₀ b := ⟨z,one_bruhat B.system z,
      B.coset_lower a₀ b hmin hzc⟩
    exact ⟨⟨(x,y),hxz⟩,rfl,hzc⟩

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Actual plane localization of the boundary-constructed sheaf. Its relative
coset restriction is free, generated and flabby with upper quotient maps;
no character or upward-kernel freeness theorem is used. -/

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us um
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 def cosetLabel (e : B.CosetEdge a₀ b) : PlaneRing basis P :=
  algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
    (polynomialLabel cs 1 b basis (B.cosetEdgeAmbient a₀ b hmin e))

 def localizedCoset (C : Sheaf.{us,v,v,um} (R := MvPolynomial σ ℝ) (graph cs 1 b)) :
    Sheaf (R := PlaneRing basis P) (B.cosetGraph a₀ b) :=
  (C.baseChange (PlaneRing basis P)).pullback (B.cosetGraphMap a₀ b hmin)

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! The relative rank-one structure models are natural under full strictly
order-compatible graph embeddings, with exactly the pulled-back labels. -/
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue uw uf
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E} {W : Type uw} [PartialOrder W]
  {F : Type uf} {H : OrderedGraph W F}
noncomputable section

 def structurePullbackIso (f : GraphMap G H) (α : F → R) (c : V)
    (ho : ∀ x y, f.vertex x ≤ f.vertex y ↔ x ≤ y) :
    Iso ((structureSheaf H α (f.vertex c)).pullback f)
      (structureSheaf G (fun e => α (f.edge e)) c) where
  vertex x := propPiEquiv R (ho x c)
  edge e := propPiEquiv (R ⧸ Ideal.span {α (f.edge e)}) (by
    rw [← f.target e]; exact ho (G.target e) c)
  lower e v := by
    change (PLift (f.vertex (G.source e) ≤ f.vertex c) → R) at v
    funext h
    change Ideal.Quotient.mk _
      (moduleEq (congrArg (fun z => ModuleCat.of R (PLift (z ≤ f.vertex c) → R))
        (f.source e)) v _) = Ideal.Quotient.mk _ (v _)
    apply congrArg (Ideal.Quotient.mk _)
    exact moduleEq_pi_apply (fun z => z ≤ f.vertex c) (f.source e) v _
  upper e v := by
    change (PLift (f.vertex (G.target e) ≤ f.vertex c) → R) at v
    funext h
    change Ideal.Quotient.mk _
      (moduleEq (congrArg (fun z => ModuleCat.of R (PLift (z ≤ f.vertex c) → R))
        (f.target e)) v _) = Ideal.Quotient.mk _ (v _)
    apply congrArg (Ideal.Quotient.mk _)
    exact moduleEq_pi_apply (fun z => z ≤ f.vertex c) (f.target e) v _

end
end KLInvariance.MomentGraph.Sheaf

end


section

/-! Rank-one models on the actual finite relative lower ideal in an ambient
plane coset. The ideal need not have a greatest element. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 def cosetInto (d : planeSubgroup M cs P) (hd : ∀ x : B.CosetVertex a₀ b, BruhatLE B.system x.val d) :
    B.CosetVertex a₀ b → Interval B.system 1 d := fun x => ⟨x.val,x.property.1,hd x⟩

 def cosetIntoEdge (d : planeSubgroup M cs P)
    (hd : ∀ x : B.CosetVertex a₀ b, BruhatLE B.system x.val d) (e : B.CosetEdge a₀ b) :
    Edge B.system 1 d := ⟨(B.cosetInto a₀ b d hd e.val.1,B.cosetInto a₀ b d hd e.val.2),e.property⟩

 def cosetIntoGraph (d : planeSubgroup M cs P)
    (hd : ∀ x : B.CosetVertex a₀ b, BruhatLE B.system x.val d) :
    GraphMap (B.cosetGraph a₀ b) (graph B.system 1 d) where
  vertex := B.cosetInto a₀ b d hd
  edge := B.cosetIntoEdge a₀ b d hd
  source _ := rfl
  target _ := rfl

 theorem cosetInto_injective (d : planeSubgroup M cs P)
    (hd : ∀ x : B.CosetVertex a₀ b, BruhatLE B.system x.val d) :
    Function.Injective (B.cosetInto a₀ b d hd) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : Interval B.system 1 d => z.val) h

 theorem coset_label_eq (e : B.CosetEdge a₀ b) :
    label cs 1 b (B.cosetEdgeAmbient a₀ b hmin e) = (e.val.2.val : W)*(e.val.1.val:W)⁻¹ := by
  change ((e.val.2.val:W)*a₀)*((e.val.1.val:W)*a₀)⁻¹ = _
  group

 theorem coset_modelLabel_eq (d : planeSubgroup M cs P)
    (hd : ∀ x : B.CosetVertex a₀ b, BruhatLE B.system x.val d) (e : B.CosetEdge a₀ b) :
    B.modelLabel basis d (B.cosetIntoEdge a₀ b d hd e) =
      polynomialLabel cs 1 b basis (B.cosetEdgeAmbient a₀ b hmin e) := by
  have ht : (⟨(label B.system 1 d (B.cosetIntoEdge a₀ b d hd e)).val,
      (B.reflection_iff _).mp (label_isReflection B.system 1 d _)⟩ : {t : W // cs.IsReflection t}) =
      ⟨label cs 1 b (B.cosetEdgeAmbient a₀ b hmin e),label_isReflection cs 1 b _⟩ := by
    apply Subtype.ext
    change (label B.system 1 d (B.cosetIntoEdge a₀ b d hd e)).val =
      label cs 1 b (B.cosetEdgeAmbient a₀ b hmin e)
    rw [B.coset_label_eq a₀ b hmin e]
    rfl
  exact congrArg (fun t : {t : W // cs.IsReflection t} =>
    linearPolynomial basis (embed M (positiveRoot M cs t).val)) ht

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Partial upward kernels of the actual rank-one model, with their embedded
edge images. No character or freeness property of BMP sheaves is assumed. -/
namespace KLInvariance.MomentGraph.Sheaf
open scoped Pointwise
universe ur uv ue
variable {R : Type ur} [CommRing R] [DecompositionMonoid R]
  {V : Type uv} [PartialOrder V] {E : Type ue} [Fintype E]
  (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section

 def supportedOutgoing (x : V) (F : Set (Outgoing (G := G) x)) : Finset (Outgoing (G := G) x) := by
  classical
  exact Finset.univ.filter (fun e => e ∈ F ∧ G.target e.val ≤ c)

 def kernelProduct (x : V) (F : Set (Outgoing (G := G) x)) : R :=
  ∏ e ∈ supportedOutgoing G c x F, α e.val

end
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 def cosetUpperVertex (x : B.CosetVertex a₀ b) (hx : BruhatLE cs u ((x.val:W)*a₀)) :
    Interval cs u b := ⟨(x.val:W)*a₀,hx,x.property.2⟩

 theorem outgoing_step (x : B.CosetVertex a₀ b)
    (f : Outgoing (G := B.cosetGraph a₀ b) x) :
    BruhatStep B.system x.val f.val.val.2.val := by
  rcases f with ⟨f,hf⟩
  change f.val.1=x at hf
  subst x
  exact f.property

 include hmin in
 theorem outgoing_upper (x : B.CosetVertex a₀ b) (hx : BruhatLE cs u ((x.val:W)*a₀))
    (f : Outgoing (G := B.cosetGraph a₀ b) x) :
    BruhatLE cs u ((f.val.val.2.val:W)*a₀) :=
  bruhat_trans cs hx (.single ((B.coset_step_iff hmin _ _).mpr (B.outgoing_step x f)))

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 include hmin in
 theorem cosetEdge_target_upper (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) : BruhatLE cs u ((e.val.2.val:W)*a₀) :=
  bruhat_trans cs hx (.single ((B.coset_step_iff hmin _ _).mpr e.property))

 def mappedCosetRoot (e : B.CosetEdge a₀ b) (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    PositiveRoot M' cs' :=
  graphRoot ((intervalIso_bruhatStep_iff_general cs cs' φ
    (B.cosetUpperVertex e.val.1 hx)
    (B.cosetUpperVertex e.val.2 (B.cosetEdge_target_upper hmin e hx))).mpr
    ((B.coset_step_iff hmin _ _).mpr e.property))

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Actual root labels in the localized edge quotient: every nonparallel
root in a given plane has a reduced label associated to any chosen one. -/
namespace KLInvariance.TitsSpace
open Module
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def localizedLinear (P : Submodule ℝ (I → ℝ)) : (I → ℝ) →ₗ[ℝ] PlaneRing basis P :=
  (IsScalarTower.toAlgHom ℝ (MvPolynomial σ ℝ) (PlaneRing basis P)).toLinearMap.comp
    ((linearPolynomial basis).comp (embedLinear (M := M)))

 def localizedEdgeIdeal (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) : Ideal (PlaneRing basis P) :=
  Ideal.span {localizedLinear basis P a}

 abbrev LocalizedEdgeRing (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :=
  PlaneRing basis P ⧸ localizedEdgeIdeal basis P a

 def localizedReduction (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    (I → ℝ) →ₗ[ℝ] LocalizedEdgeRing basis P a :=
  (Ideal.Quotient.mkₐ ℝ (localizedEdgeIdeal basis P a)).toLinearMap.comp
    (localizedLinear basis P)

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 def reducedCosetRoot (e : B.CosetEdge a₀ b) (β : PositiveRoot M cs) :
    PlaneRing basis P ⧸ Ideal.span {B.cosetLabel basis a₀ b hmin e} :=
  algebraMap (PlaneRing basis P) _ (localizedLinear basis P β.val)

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.BruhatGraph
open TitsSpace
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 def upperSource (e : Edge cs 1 b) (hx : BruhatLE cs u (source cs 1 b e).val) : Interval cs u b :=
  ⟨(source cs 1 b e).val,hx,(source cs 1 b e).property.2⟩
 def upperTarget (e : Edge cs 1 b) (hx : BruhatLE cs u (source cs 1 b e).val) : Interval cs u b :=
  ⟨(target cs 1 b e).val,bruhat_trans cs hx (.single e.property),(target cs 1 b e).property.2⟩
 def mappedEdgeRoot (e : Edge cs 1 b) (hx : BruhatLE cs u (source cs 1 b e).val) :
     PositiveRoot M' cs' :=
   graphRoot ((intervalIso_bruhatStep_iff_general cs cs' φ (upperSource e hx) (upperTarget e hx)).mpr e.property)

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_EdgeLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bruhat sheaf localization, graded transport, local edge-image bounds and support.
-/


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance scaledInterval : Fintype (Interval cs 1 b) := by
  let := interval_finite cs 1 b
  exact Fintype.ofFinite _

 def scaledStalk {C : Type*} [Field C] (t : C) (x : Interval cs 1 b) : C :=
  t^((cs.length x.val : ℤ)-cs.length b)*
    eval₂ (Int.castRingHom C) (t^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) x)

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_PositiveTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive transfer inequalities, strict Hilbert-series detection including higher-codimension support, and reverse-filtration projective-to-free arguments.
-/


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded _root_.OAI.KLInvariance.Hilbert
universe us um
variable {σ : Type us} [Fintype σ]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  (B : GradedSheaf (𝓐 := polynomialGrading ℝ σ) G)
noncomputable section

 def kernelHilbert (q : ℝ) (x : V) (F : Set (Sheaf.Outgoing (G := G) x)) : ℝ :=
  value (B.vertex x).piece ((B.upwardSubmodule x F).restrictScalars ℝ) q

 def lowerImage (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.source e))) :
    Submodule (MvPolynomial σ ℝ) (B.edge e) :=
  (B.upwardSubmodule (G.source e) F).map (B.lower e).map

 def upperImage (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.target e))) :
    Submodule (MvPolynomial σ ℝ) (B.edge e) :=
  (B.upwardSubmodule (G.target e) F).map (B.upper e).map

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

 def stateScale (t : ℝ) (x : Interval cs u b) : ℝ :=
  (1-t^2)^(Fintype.card σ) * t^((cs.length x.val : ℤ)-cs.length b)

 def normalizedKernel (t : ℝ) (x : Interval cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) x)) : ℝ :=
  stateScale (σ := σ) cs u b t x * B.sheaf.kernelHilbert (t^2) x F

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

 def scheduleState (t : ℝ) (p : List (Edge cs u b)) : Interval cs u b → ℝ :=
  fun x => normalizedKernel cs u b basis hub B t x (remainingConditions cs u b p x)

end
end KLInvariance.BruhatGraph

end


section

/-! Exact identification of chronological suffix conditions with the
strictly-later root conditions used in the height-one edge-image proof.
Equal-label edges may be ordered arbitrarily and cause no extra incident
condition. -/
namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths MomentGraph
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 def transportedSlope (e : Edge cs u b) : ℝ :=
  geometricSlope (AdaptedDyer.rootLabel cs' (transportedEdge φ e))

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_TerminalKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
All-section transport, terminal kernels, scalar quotients, height-one membership in free targets and scaled edge-image inclusion.
-/


section

namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)
noncomputable section

 def kernelConstraint (x : V) (F : Set (Outgoing (G := G) x)) :
    B.vertex x →ₗ[R] (∀ e : F, B.edge e.val.val) :=
  LinearMap.pi (fun e => (LinearMap.proj e.val).comp (B.stalkMap x))

end
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace EdgeAlgebra
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 instance edgeRing_ufm (a : PositiveRoot M cs) : UniqueFactorizationMonoid (EdgeRing cs basis a) :=
   ((edgeRingEquiv cs basis a).trans (edgePolynomial a)).toMulEquiv.symm.uniqueFactorizationMonoid inferInstance

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue um
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} [Finite E] {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)
noncomputable section
open scoped Classical

 def outgoingLabelProduct (α : E → R) (x : V) (F : Set (Outgoing (G := G) x)) : R :=
   ∏ f ∈ F.toFinite.toFinset, α f.val

end
end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SimultaneousInvariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
R-first simultaneous invariance and transported-schedule terminal-kernel freeness: upper-interval freeness, lower-interval cancellation, reversal and endpoint bottom freeness; all-entry transport and KL degree rigidity.
-/

section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v u' v' us
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  {cs : CoxeterSystem M W} {I' : Type u'} {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 def upperIntervalIso (x : Interval cs u b) :
    Interval cs x.val b ≃o Interval cs' (φ x).val b' where
  toFun z :=
    let zI : Interval cs u b := ⟨z.val,x.property.1.trans z.property.1,z.property.2⟩
    ⟨(φ zI).val,φ.monotone z.property.1,(φ zI).property.2⟩
  invFun z :=
    let zI : Interval cs' u' b' := ⟨z.val,(φ x).property.1.trans z.property.1,z.property.2⟩
    ⟨(φ.symm zI).val,by
      change x ≤ φ.symm zI
      simpa only [φ.symm_apply_apply] using φ.symm.monotone
        (show φ x ≤ zI from z.property.1),(φ.symm zI).property.2⟩
  left_inv z := by
    apply Subtype.ext
    change (φ.symm (φ ⟨z.val,x.property.1.trans z.property.1,z.property.2⟩)).val=z.val
    exact congrArg (fun a : Interval cs u b => a.val) (φ.symm_apply_apply _)
  right_inv z := by
    apply Subtype.ext
    change (φ (φ.symm ⟨z.val,(φ x).property.1.trans z.property.1,z.property.2⟩)).val=z.val
    exact congrArg (fun a : Interval cs' u' b' => a.val) (φ.apply_symm_apply _)
  map_rel_iff' := by
    intro x y
    exact φ.map_rel_iff

 def upperGraphInclusion (x : Interval cs u b) :
    GraphMap (graph cs x.val b) (graph cs u b) where
  vertex z := ⟨z.val,x.property.1.trans z.property.1,z.property.2⟩
  edge e := ⟨(⟨(source cs x.val b e).val,
      x.property.1.trans (source cs x.val b e).property.1,(source cs x.val b e).property.2⟩,
    ⟨(target cs x.val b e).val,
      x.property.1.trans (target cs x.val b e).property.1,(target cs x.val b e).property.2⟩),e.property⟩
  source _ := rfl
  target _ := rfl

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Invariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Genuine KL invariance, finite-parabolic transport and unrestricted finite interval models; the main theorem for two arbitrary Coxeter systems in four independent universes.
-/


section

/-! The finite-rank reduction of the exact main target.  The model's interval
and genuine KL polynomial are identified with those of the unrestricted
ambient Coxeter system, not with an order-theoretically defined invariant. -/
namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (u b : W)
noncomputable section

def intervalEndpointCongr {a b a' b' : W} (ha : a = a') (hb : b = b') :
    Interval cs a b ≃o Interval cs a' b' := by
  subst a'
  subst b'
  exact OrderIso.refl _

namespace FiniteIntervalModel
variable {cs u b} (F : FiniteIntervalModel cs u b)

 def orderIso : Interval (StandardParabolic.system (M := M) F.indices) F.lower F.upper ≃o
    Interval cs u b := by
  let _ : Fintype F.indices := F.finite.fintype
  have h := StandardParabolic.intervalIso cs F.indices F.lower F.upper
  exact h.trans (intervalEndpointCongr cs F.lower_eq F.upper_eq)

end FiniteIntervalModel
end
end KLInvariance

end


end OAI
end


