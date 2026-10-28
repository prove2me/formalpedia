-- Prove2me | Definitions.Def_OAIEG011
-- name    : OAIEG011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-24T23:54:34.317985+00:00
-- url     : https://prove2.me/theorems/f6af6f94-5530-4f1b-9fa4-c3a7c1fe2956
-- title:
--   Definitions bundle OAIEG011 of the split of OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, carved from OpenAI's openai/math development (OpenAI, *A finitely generated counterexample to the Eilenberg–Ganea conjecture*, OpenAI Math Release, September 23, 2026, result family 249, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 402 declarations of OpenAI's Lean: 145 definitions, 3 inductive types or structures, 6 instances and 248 theorems. The definitions and types are `OAI.EilenbergGanea.CWCollar.Attachment.annularBasis`, `OAI.EilenbergGanea.CWCollar.Attachment.annulusMap`, `OAI.EilenbergGanea.CWCollar.Attachment.annulusPoint`, `OAI.EilenbergGanea.CWCollar.Attachment.annulusRelator`, `OAI.EilenbergGanea.CWCollar.Attachment.collarHomotopy`, `OAI.EilenbergGanea.CWCollar.Attachment.compression`, `OAI.EilenbergGanea.CWCollar.Attachment.compressionChoice`, `OAI.EilenbergGanea.CWCollar.actualAttachment`, `OAI.EilenbergGanea.CWCollar.annulusGenerator`, `OAI.EilenbergGanea.CWCollar.baseAttachment`, `OAI.EilenbergGanea.CWCollar.liftedAttachment`, `OAI.EilenbergGanea.CWCollar.liftedOuterHomeomorph`, `OAI.EilenbergGanea.CWCollar.outerProjection`, `OAI.EilenbergGanea.CWCollar.topAttachmentQuotient`, `OAI.EilenbergGanea.CWCover.CellDisks`, `OAI.EilenbergGanea.CWCover.CellPullback`, `OAI.EilenbergGanea.CWCover.cellEndpoint`, `OAI.EilenbergGanea.CWCover.cellOrbitEquiv`, `OAI.EilenbergGanea.CWCover.cellPullbackHomotopy`, `OAI.EilenbergGanea.CWCover.cellPullbackStart`, `OAI.EilenbergGanea.CWCover.cellSheet`, `OAI.EilenbergGanea.CWCover.characteristicSum`, `OAI.EilenbergGanea.CWCover.chosenCell`, `OAI.EilenbergGanea.CWCover.cwComplex`, `OAI.EilenbergGanea.CWCover.diskContraction`, `OAI.EilenbergGanea.CWCover.liftedMap`, `OAI.EilenbergGanea.CWCover.liftedMapFun`, `OAI.EilenbergGanea.CWCover.liftedOpenCell`, `OAI.EilenbergGanea.CWPresentation.base`, `OAI.EilenbergGanea.CWPresentation.coefficientIndex`, `OAI.EilenbergGanea.CWPresentation.conjugateBasis`, `OAI.EilenbergGanea.CWPresentation.conjugator`, `OAI.EilenbergGanea.CWPresentation.deckEquiv`, `OAI.EilenbergGanea.CWPresentation.fromLift`, `OAI.EilenbergGanea.CWPresentation.kernelBasis`, `OAI.EilenbergGanea.CWPresentation.lifted`, `OAI.EilenbergGanea.CWPresentation.liftedKernelEquiv`, `OAI.EilenbergGanea.CWPresentation.projectedAnchor`, `OAI.EilenbergGanea.CWPresentation.projectedRelator`, `OAI.EilenbergGanea.CWPresentation.relator` and 108 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory, in whole or in part: `CWComplex_CellularPaths`, `CWComplex_Collar`, `CWComplex_Cover`, `CWComplex_CoverTopology`, `CWComplex_Presentation`, `CubicalCover`, `Cubical_ArtinChains`, `Cubical_Descending`, `Cubical_PathChains`, `Cubical_Realization`, `IntegralModules`, `LevelBasis`, `LevelTransport`, `PresentationAlignment`, `PresentationComparison`, `Presentation_KernelCycles`, `RightAngledArtin_TraceWords`, `SeedContraction`, `SmallHolonomy`.
--
--   **Imports.** It imports the published bundle `Def_EilenbergGanea`; the bundles `OAIEG000`, `OAIEG001` and `OAIEG002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIEG019` and `OAIEG022`; the statements `OAI.EilenbergGanea.aligned_presentation_small_transport` and `OAI.EilenbergGanea.boundary_basis_small_transport`.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_EilenbergGanea
import Definitions.Def_OAIEG000
import Definitions.Def_OAIEG001
import Definitions.Def_OAIEG002

section
-- module Solutions.OAIEG.CWComplex_Cover
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.annulusTwoPathConnected _root_.OAI.EilenbergGanea.CWCollar.openDiskContractible _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

/-! Actual characteristic-cell lifts for an ordinary Whitehead CW complex.
This is a dependency toward (not an assumption replacing) the arbitrary-CW
presentation and cellular-cycle bridge. -/
open Set Metric Topology
namespace EilenbergGanea.CWCover

variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

theorem cellLift_project {n : ℕ} (c : LiftedCell (p := p) n) (z : Disk n) :
    p (cellLift cov c z) = characteristic c.1 z :=
  congrFun (cov.existsUnique_continuousMap_lifts (characteristic c.1) (diskCenter n) c.2.val c.2.property).exists.choose_spec.2 z

def liftedOpenCell {n : ℕ} (c : LiftedCell (p := p) n) : Set E :=
  cellLift cov c '' {z : Disk n | z.val ∈ ball 0 1}

theorem cellLift_unique {n : ℕ} {c d : LiftedCell (p := p) n}
    (hi : c.1 = d.1) (z : Disk n) (hz : cellLift cov c z = cellLift cov d z) : c = d := by
  have he : (cellLift cov c : Disk n → E) = cellLift cov d :=
    cov.eq_of_comp_eq (cellLift cov c).continuous (cellLift cov d).continuous
      (by ext t; simp only [Function.comp_apply,cellLift_project,hi]) z hz
  have hc : c.2.val = d.2.val := by
    simpa only [cellLift_center] using congrFun he (diskCenter n)
  rcases c with ⟨i,e,he⟩
  rcases d with ⟨j,f,hf⟩
  dsimp at hi hc
  cases hi
  cases hc
  rfl

end EilenbergGanea.CWCover

namespace EilenbergGanea.CWCover
open Classical
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] [T2Space X]

abbrev CellDisks (X : Type*) [TopologicalSpace X] [CWComplex (univ : Set X)] :=
  Σ c : (Σ n, RelCWComplex.cell (univ : Set X) n), Disk c.1

def characteristicSum : CellDisks X → X := fun c => characteristic c.1.2 c.2

omit [T2Space X] in
theorem characteristicSum_continuous : Continuous (characteristicSum (X := X)) :=
  continuous_sigma fun c => (characteristic (X := X) c.2).continuous

omit [T2Space X] in
theorem characteristicSum_surjective : Function.Surjective (characteristicSum (X := X)) := by
  intro x
  have hx : x ∈ ⋃ (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n),
      RelCWComplex.closedCell n i := by rw [CWComplex.union]; trivial
  obtain ⟨n,i,z,hz,rfl⟩ := by simpa only [Set.mem_iUnion,RelCWComplex.closedCell,Set.mem_image] using hx
  exact ⟨⟨⟨n,i⟩,⟨z,hz⟩⟩,rfl⟩

/-- The ordinary CW topology is exactly the quotient topology of the disjoint
union of its closed characteristic disks. -/
theorem characteristicSum_quotient : IsQuotientMap (characteristicSum (X := X)) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨characteristicSum_surjective,fun A => ⟨fun h => h.preimage characteristicSum_continuous,?_⟩⟩
  intro hA
  apply (CWComplex.closed (univ : Set X) A (Set.subset_univ A)).mpr
  intro n i
  have hD : IsClosed ((characteristic (X := X) i) ⁻¹' A) :=
    hA.preimage (continuous_sigmaMk (i := (⟨n,i⟩ : Σ n, RelCWComplex.cell (univ : Set X) n)))
  have hcompact : IsCompact ((characteristic (X := X) i) ⁻¹' A) := hD.isCompact
  have he : characteristic i '' (characteristic i ⁻¹' A) = A ∩ RelCWComplex.closedCell n i := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨hz,z.val,z.property,rfl⟩
    · rintro ⟨hx,z,hz,rfl⟩
      exact ⟨⟨z,hz⟩,hx,rfl⟩
  rw [← he]
  exact (hcompact.image (characteristic i).continuous).isClosed

variable {p : E → X} (cov : IsCoveringMap p)

omit [T2Space X] in
/-- Every point over a characteristic disk is hit by exactly one lift of that
disk with the specified base cell. -/
theorem exists_cellLift_through {n : ℕ} (i : Cell (X := X) n) (z : Disk n)
    (e : E) (he : p e = characteristic i z) :
    ∃ c : LiftedCell (p := p) n, c.1 = i ∧ cellLift cov c z = e := by
  obtain ⟨f,hfz,hfp⟩ := (cov.existsUnique_continuousMap_lifts (characteristic i) z e he).exists
  let c : LiftedCell (p := p) n := ⟨i,f (diskCenter n),congrFun hfp (diskCenter n)⟩
  refine ⟨c,rfl,?_⟩
  have hf : (cellLift cov c : Disk n → E) = f :=
    cov.eq_of_comp_eq (cellLift cov c).continuous f.continuous
      (by ext w; rw [Function.comp_apply,cellLift_project cov c w]; exact (congrFun hfp w).symm)
      (diskCenter n) (cellLift_center cov c)
  rw [hf]
  exact hfz


/-- The pulled-back weak topology can be proved before constructing the
lifted CW structure: openness is detected by the actual lifted disks. -/
theorem isOpen_of_cellLift_preimages {A : Set E}
    (hA : ∀ n (c : LiftedCell (p := p) n), IsOpen (cellLift cov c ⁻¹' A)) : IsOpen A := by
  apply isOpen_iff_mem_nhds.mpr
  intro e he
  let s := cov.isLocalHomeomorph.localInverseAt e
  let B : Set X := s.source ∩ s ⁻¹' A
  have hp (x : E) : s.symm x = p x := congrFun (cov.isLocalHomeomorph.localInverseAt_symm e) x
  have hB : IsOpen B := by
    apply characteristicSum_quotient.isOpen_preimage.mp
    rw [isOpen_sigma_iff]
    rintro ⟨n,i⟩
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    change characteristic i z ∈ B at hz
    obtain ⟨c,hci,hcz⟩ := exists_cellLift_through cov i z (s (characteristic i z))
      (cov.isLocalHomeomorph.apply_localInverseAt_of_mem hz.1)
    let W := cellLift cov c ⁻¹' A ∩ cellLift cov c ⁻¹' s.target
    have hW : IsOpen W := (hA n c).inter (s.open_target.preimage (cellLift cov c).continuous)
    have hzW : z ∈ W := by
      change cellLift cov c z ∈ A ∧ cellLift cov c z ∈ s.target
      rw [hcz]
      exact ⟨hz.2,s.map_source hz.1⟩
    apply Filter.mem_of_superset (hW.mem_nhds hzW)
    intro w hw
    have hw₁ : s.symm (cellLift cov c w) = characteristic i w := by
      rw [hp,cellLift_project cov c w,hci]
    have hw₂ : s (characteristic i w) = cellLift cov c w := by
      rw [← hw₁]
      exact s.right_inv hw.2
    change characteristic i w ∈ s.source ∧ s (characteristic i w) ∈ A
    constructor
    · rw [← hw₁]; exact s.map_target hw.2
    · rw [hw₂]; exact hw.1
  have hU : IsOpen (s.target ∩ p ⁻¹' B) := s.open_target.inter (hB.preimage cov.continuous)
  have heU : e ∈ s.target ∩ p ⁻¹' B := by
    refine ⟨cov.isLocalHomeomorph.self_mem_localInverseAt_target,?_,?_⟩
    · exact cov.isLocalHomeomorph.apply_self_mem_localInverseAt_source
    · change s (p e) ∈ A
      simpa only [s,cov.isLocalHomeomorph.localInverseAt_apply_self] using he
  apply Filter.mem_of_superset (hU.mem_nhds heU)
  rintro x ⟨hx,hxB⟩
  have hx' : s (p x) = x := by rw [← hp]; exact s.right_inv hx
  exact hx' ▸ hxB.2

end EilenbergGanea.CWCover

namespace EilenbergGanea.CWCover
open Classical
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

/-- Extend the genuine lifted characteristic disk outside its domain only so
that it can be used in Mathlib's ordinary `PartialEquiv` CW convention. -/
def liftedMapFun {n : ℕ} (c : LiftedCell (p := p) n) (z : Fin n → ℝ) : E :=
  if h : z ∈ closedBall 0 1 then cellLift cov c ⟨z,h⟩ else c.2.val

theorem liftedMapFun_disk {n : ℕ} (c : LiftedCell (p := p) n) (z : Disk n) :
    liftedMapFun cov c z.val = cellLift cov c z := by
  simp only [liftedMapFun,dite_eq_left z.property]

theorem liftedMapFun_continuousOn {n : ℕ} (c : LiftedCell (p := p) n) :
    ContinuousOn (liftedMapFun cov c) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert (cellLift cov c).continuous using 1
  ext z
  exact liftedMapFun_disk cov c z

/-- The real inverse chart is obtained by projecting to the ordinary base
chart. It is not chosen by an abstract set-theoretic inverse. -/
def liftedMap {n : ℕ} (c : LiftedCell (p := p) n) : PartialEquiv (Fin n → ℝ) E where
  toFun := liftedMapFun cov c
  invFun := fun e => (RelCWComplex.map n c.1).symm (p e)
  source := ball 0 1
  target := liftedOpenCell cov c
  map_source' := by
    intro z hz
    let z' : Disk n := ⟨z,ball_subset_closedBall hz⟩
    exact ⟨z',hz,(liftedMapFun_disk cov c z').symm⟩
  map_target' := by
    rintro e ⟨z,hz,rfl⟩
    rw [cellLift_project cov c z]
    change (RelCWComplex.map n c.1).symm (RelCWComplex.map n c.1 z.val) ∈ ball 0 1
    rw [(RelCWComplex.map n c.1).left_inv (by rwa [RelCWComplex.source_eq])]
    exact hz
  left_inv' := by
    intro z hz
    let z' : Disk n := ⟨z,ball_subset_closedBall hz⟩
    rw [show liftedMapFun cov c z = cellLift cov c z' from liftedMapFun_disk cov c z']
    rw [cellLift_project cov c z']
    exact (RelCWComplex.map n c.1).left_inv (by rwa [RelCWComplex.source_eq])
  right_inv' := by
    rintro e ⟨z,hz,rfl⟩
    rw [cellLift_project cov c z]
    change liftedMapFun cov c ((RelCWComplex.map n c.1).symm
      (RelCWComplex.map n c.1 z.val)) = _
    rw [(RelCWComplex.map n c.1).left_inv (by rwa [RelCWComplex.source_eq])]
    exact liftedMapFun_disk cov c z

@[simp] theorem liftedMap_source {n : ℕ} (c : LiftedCell (p := p) n) :
    (liftedMap cov c).source = ball 0 1 := rfl

@[simp] theorem liftedMap_target {n : ℕ} (c : LiftedCell (p := p) n) :
    (liftedMap cov c).target = liftedOpenCell cov c := rfl

theorem liftedMap_continuousOn_symm {n : ℕ} (c : LiftedCell (p := p) n) :
    ContinuousOn (liftedMap cov c).symm (liftedMap cov c).target := by
  apply (RelCWComplex.continuousOn_symm n c.1).comp cov.continuous.continuousOn
  intro e he
  rcases he with ⟨z,hz,rfl⟩
  rw [cellLift_project cov c z]
  apply (RelCWComplex.map n c.1).map_source
  rwa [RelCWComplex.source_eq]

theorem liftedOpenCells_disjoint {n m : ℕ} (c : LiftedCell (p := p) n)
    (d : LiftedCell (p := p) m) (hne : (⟨n,c⟩ : Σ k, LiftedCell (p := p) k) ≠ ⟨m,d⟩) :
    Disjoint (liftedOpenCell cov c) (liftedOpenCell cov d) := by
  apply Set.disjoint_left.mpr
  rintro e ⟨z,hz,he⟩ ⟨w,hw,he'⟩
  have hbase : (⟨n,c.1⟩ : Σ k, Cell (X := X) k) = ⟨m,d.1⟩ := by
    by_contra h
    apply Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne h)
      (show p e ∈ RelCWComplex.openCell n c.1 from ?_)
      (show p e ∈ RelCWComplex.openCell m d.1 from ?_)
    · rw [← he,cellLift_project cov c z]; exact ⟨z.val,hz,rfl⟩
    · rw [← he',cellLift_project cov d w]; exact ⟨w.val,hw,rfl⟩
  have hnm : n = m := congrArg Sigma.fst hbase
  subst m
  have hci : c.1 = d.1 := by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hbase
  have hzw : z = w := by
    apply Subtype.ext
    apply (RelCWComplex.map n c.1).injOn
    · rwa [RelCWComplex.source_eq]
    · rwa [RelCWComplex.source_eq]
    · have h := congrArg p (he.trans he'.symm)
      rw [cellLift_project cov c z,cellLift_project cov d w] at h
      change RelCWComplex.map n c.1 z.val = RelCWComplex.map n d.1 w.val at h
      simpa only [hci] using h
  subst w
  have hcd : c = d := cellLift_unique cov hci z (he.trans he'.symm)
  exact hne (congrArg (fun c => Sigma.mk n c) hcd)

end EilenbergGanea.CWCover


end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_PathChains
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology

namespace EilenbergGanea.PathTransport.Local
open Set CubicalSingular
variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]
variable {U : Set (Set X)} (l : Local (G:=G) U)
variable (hU : ∀ u ∈ U, IsOpen u) (hcover : ⋃₀ U = univ)

/-- Traversal-order labels are a homomorphism to the opposite, because Mathlib's
fundamental group multiplication is categorical (right path first). -/
def fundamentalHom (x : X) : FundamentalGroup X x →* Gᵐᵒᵖ where
  toFun q := MulOpposite.op (l.quotientTransport hU hcover q)
  map_one' := congrArg MulOpposite.op (l.quotientTransport_refl hU hcover x)
  map_mul' p q := by
    rw [FundamentalGroup.mul_def,l.quotientTransport_trans,MulOpposite.op_mul]

end EilenbergGanea.PathTransport.Local

namespace EilenbergGanea.PathTransport
open CubicalSingular
variable {X : Type*} [TopologicalSpace X]

def halfPath₀ : Path (0 : I) (half true 0) := ⟨half false,half_false_zero,half_mid⟩
def halfPath₁ : Path (half true 0) (1 : I) := ⟨half true,rfl,half_true_one⟩

attribute [local instance] OAI.EilenbergGanea.PathTransport.instContractibleSpaceElemRealI
theorem holonomy_split {r : X} (q : ∀ x, Path r x) (γ : Cube₁ X) :
    holonomy q γ = holonomy q (cut₁ γ false) * holonomy q (cut₁ γ true) := by
  have hp := (SimplyConnectedSpace.paths_homotopic Path.id (halfPath₀.trans halfPath₁)).map γ
  have h := basedPath_homotopic q hp
  rw [Path.map_trans,basedPath_trans] at h
  calc
    holonomy q γ = basedPath q (Path.id.map γ.continuous) := basedPath_congr q _ _ (fun _ => rfl)
    _ = basedPath q (halfPath₀.map γ.continuous) * basedPath q (halfPath₁.map γ.continuous) := h
    _ = _ := congrArg₂ (· * ·)
      (basedPath_congr q (halfPath₀.map γ.continuous) (cubePath (cut₁ γ false)) (fun _ => rfl))
      (basedPath_congr q (halfPath₁.map γ.continuous) (cubePath (cut₁ γ true)) (fun _ => rfl))

end EilenbergGanea.PathTransport


end

end OAI
end

section
-- module Solutions.OAIEG.CWComplex_Collar
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.openDiskContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea.CWCollar
open Classical Set Metric Topology CWCover
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

theorem characteristic_mem_lower {k m : ℕ} (hk : k < m) (i : Cell (X := X) k) (z : Disk k) :
    characteristic i z ∈ lowerSkeleton (X := X) m := by
  apply RelCWComplex.skeletonLT_mono (show (k:ℕ∞)+1 ≤ (m:ℕ∞) by exact_mod_cast Nat.succ_le_of_lt hk)
    (RelCWComplex.closedCell_subset_skeletonLT k i (show characteristic i z ∈ RelCWComplex.closedCell k i from ?_))
  exact ⟨z.val,z.property,rfl⟩

def topAttachmentQuotient (m : ℕ) :
    lowerSkeleton (X := X) m ⊕ (Σ _ : Cell (X := X) m, Disk m) → X :=
  Sum.elim Subtype.val (fun c => characteristic c.1 c.2)

theorem topAttachmentQuotient_continuous (m : ℕ) :
    Continuous (topAttachmentQuotient (X := X) m) :=
  continuous_subtype_val.sumElim (continuous_sigma (fun i => (characteristic i).continuous))

theorem topAttachmentQuotient_surjective (m : ℕ)
    (hd : ∀ k, m < k → IsEmpty (Cell (X := X) k)) :
    Function.Surjective (topAttachmentQuotient (X := X) m) := by
  intro x
  obtain ⟨⟨⟨k,i⟩,z⟩,rfl⟩ := characteristicSum_surjective (X := X) x
  by_cases hk : k < m
  · exact ⟨.inl ⟨characteristic i z,characteristic_mem_lower hk i z⟩,rfl⟩
  · have hkm : k = m := by
      by_contra h
      have := hd k (by omega)
      exact isEmptyElim i
    subst k
    exact ⟨.inr ⟨i,z⟩,rfl⟩

theorem topAttachmentQuotient_quotient (m : ℕ)
    (hd : ∀ k, m < k → IsEmpty (Cell (X := X) k)) :
    IsQuotientMap (topAttachmentQuotient (X := X) m) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨topAttachmentQuotient_surjective m hd,fun A =>
    ⟨fun h => h.preimage (topAttachmentQuotient_continuous m),?_⟩⟩
  intro hA
  apply characteristicSum_quotient.isClosed_preimage.mp
  rw [isClosed_sigma_iff]
  rintro ⟨k,i⟩
  by_cases hk : k < m
  · let f : Disk k → lowerSkeleton (X := X) m ⊕ (Σ _ : Cell (X := X) m, Disk m) :=
      fun z => .inl ⟨characteristic i z,characteristic_mem_lower hk i z⟩
    have hf : Continuous f := continuous_inl.comp ((characteristic i).continuous.subtype_mk (characteristic_mem_lower hk i))
    exact hA.preimage hf
  · have hkm : k = m := by
      by_contra h
      have := hd k (by omega)
      exact isEmptyElim i
    subst k
    exact hA.preimage (continuous_inr.comp (continuous_sigmaMk (i := i)))

/-- The abstract single-stage attachment is obtained from the given ordinary
CW complex itself, with no restriction on or enumeration of its cells. -/
def actualAttachment (m : ℕ) (hd : ∀ k, m < k → IsEmpty (Cell (X := X) k)) :
    Attachment X (Cell (X := X) m) m where
  lower := lowerSkeleton m
  closed_lower := (CWComplex.skeletonLT (univ : Set X) m).closed'
  chart := characteristic
  boundary := by
    intro i z hz
    exact RelCWComplex.cellFrontier_subset_skeletonLT m i
      ⟨z.val,by simpa only [mem_sphere,dist_zero_right] using hz,rfl⟩
  interior := by
    intro i z hz hl
    exact Set.disjoint_left.mp (RelCWComplex.disjoint_skeletonLT_openCell le_rfl) hl
      ⟨z.val,by simpa only [mem_ball,dist_zero_right] using hz,rfl⟩
  disjoint := by
    intro i j z w hz hw he
    have hz' : z.val ∈ ball (0 : Fin m → ℝ) 1 := by simpa only [mem_ball,dist_zero_right] using hz
    have hw' : w.val ∈ ball (0 : Fin m → ℝ) 1 := by simpa only [mem_ball,dist_zero_right] using hw
    by_cases hij : i = j
    · subst j
      refine ⟨rfl,Subtype.ext ((RelCWComplex.map m i).injOn ?_ ?_ he)⟩
      · simpa only [RelCWComplex.source_eq] using hz'
      · simpa only [RelCWComplex.source_eq] using hw'
    · exfalso
      exact Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne
        (show (⟨m,i⟩ : Σ k,Cell (X := X) k) ≠ ⟨m,j⟩ by simpa using hij))
        ⟨z.val,hz',rfl⟩ ⟨w.val,hw',he.symm⟩
  quotient := topAttachmentQuotient_quotient m hd

end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar.Attachment
open Classical Set Metric Topology
open scoped unitInterval
variable {X J : Type*} [TopologicalSpace X] {n : ℕ} (a : Attachment X J n)

/-- The radial collar is a genuine strong deformation neighborhood of the
lower-dimensional CW skeleton. -/
def collarHomotopy : (ContinuousMap.id a.outer).Homotopy (a.sectionMap.comp a.retractMap) where
  toFun p := a.flow (p.2,p.1)
  continuous_toFun := a.flow_continuous.comp continuous_swap
  map_zero_left := a.flow_zero
  map_one_left _ := rfl

end EilenbergGanea.CWCollar.Attachment

namespace EilenbergGanea.CWCollar
open CubicalSingular PathTransport

noncomputable def annulusGenerator (x : Annulus 2) : Path x x :=
  Quotient.out ((annulusOppositeInt x).symm (Multiplicative.ofAdd 1)).unop

end EilenbergGanea.CWCollar


end

end OAI
end

section
-- module Solutions.OAIEG.CWComplex_CellularPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea.CubicalSingular
open Set
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

variable {J : Type*} (y₀ : Y)

def fiberProjection (j : J) : C((Σ _ : J,Y),Y) :=
  ⟨fun z => if z.1 = j then z.2 else y₀,continuous_sigma (fun k => by
    dsimp only
    by_cases h : k = j
    · simp only [h,ite_true]
      exact continuous_id
    · simp only [ite_eq_right h]
      exact continuous_const)⟩

@[simp] theorem fiberProjection_inclusion (j k : J) :
    (fiberProjection y₀ j).comp (fiberInclusion k) =
      if k = j then ContinuousMap.id Y else ContinuousMap.const Y y₀ := by
  ext y
  by_cases h : k = j <;> simp [fiberProjection,fiberInclusion,h]

theorem pushN₁_fiber_cube (j : J) (σ : Cube₁ (Σ _ : J,Y)) :
    pushN₁ (fiberInclusion j) (pushN₁ (fiberProjection y₀ j) (gen₁ σ)) =
      if (σ 0).1 = j then gen₁ σ else 0 := by
  obtain ⟨k,g,hg,he⟩ := σ.continuous.exists_lift_sigma
  have he₀ : (σ 0).1 = k := congrArg Sigma.fst (congrFun he 0)
  by_cases h : k = j
  · have hh := he₀.trans h
    rw [ite_eq_left hh,← pushN₁_comp]
    rw [pushN₁_gen]
    change gen₁ (((fiberInclusion j).comp (fiberProjection y₀ j)).comp σ) = gen₁ σ
    congr 1
    apply ContinuousMap.ext
    intro t
    rw [ContinuousMap.comp_apply,ContinuousMap.comp_apply,congrFun he t]
    subst j
    simp only [Function.comp_apply,fiberProjection,fiberInclusion,ContinuousMap.coe_mk,ite_true]
  · rw [ite_eq_right (fun hh => h (he₀.symm.trans hh))]
    have hc : (fiberProjection y₀ j).comp σ = ContinuousMap.const I y₀ := by
      ext t
      rw [ContinuousMap.comp_apply,congrFun he t]
      exact ite_eq_right h
    rw [pushN₁_gen]
    rw [hc]
    have hz : gen₁ (ContinuousMap.const I y₀) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨y₀,rfl⟩)
    rw [hz,map_zero]

variable (e : HomologyOne Y ≃ₗ[ℤ] ℤ)

def sigmaHomologyBasisMap : (J →₀ ℤ) →ₗ[ℤ] HomologyOne (Σ _ : J,Y) :=
  Finsupp.linearCombination ℤ (fun j => homologyOneMap (fiberInclusion j) (e.symm 1))

theorem sigmaHomologyBasis_coeff (c : J →₀ ℤ) (j : J) :
    e (homologyOneMap (fiberProjection y₀ j) (sigmaHomologyBasisMap e c)) = c j := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,Finsupp.add_apply,hc,hd]
  | single k n =>
    rw [sigmaHomologyBasisMap,Finsupp.linearCombination_single,map_smul,map_smul]
    rw [← LinearMap.comp_apply,← homologyOneMap_comp,fiberProjection_inclusion]
    by_cases h : k = j
    · subst k
      simp
    · simp [h,Finsupp.single_eq_of_ne (Ne.symm h)]

include y₀ in
theorem sigmaHomologyBasis_injective : Function.Injective (sigmaHomologyBasisMap (J:=J) e) := by
  intro a b h
  ext j
  rw [← sigmaHomologyBasis_coeff y₀ e a j,← sigmaHomologyBasis_coeff y₀ e b j,h]

theorem finite_fiber_decomposition (c : C₁ (Σ _ : J,Y)) :
    ∃ S : Finset J, ∑ j ∈ S, pushN₁ (fiberInclusion j) (pushN₁ (fiberProjection y₀ j) ((D₁ _).mkQ c)) = (D₁ _).mkQ c := by
  classical
  let S := c.support.image (fun σ => (σ 0).1)
  refine ⟨S,?_⟩
  have hgen (σ : Cube₁ (Σ _ : J,Y)) (hσ : σ ∈ c.support) :
      ∑ j ∈ S, pushN₁ (fiberInclusion j) (pushN₁ (fiberProjection y₀ j) (gen₁ σ)) = gen₁ σ := by
    simp_rw [pushN₁_fiber_cube]
    rw [Finset.sum_ite_eq]
    exact ite_eq_left (Finset.mem_image.mpr ⟨σ,hσ,rfl⟩)
  have hn (σ : Cube₁ (Σ _ : J,Y)) (m : ℤ) : (D₁ _).mkQ (Finsupp.single σ m) = m • gen₁ σ := by
    rw [← Finsupp.smul_single_one,map_smul]; rfl
  have hz : (D₁ _).mkQ c = ∑ σ ∈ c.support, c σ • gen₁ σ := by
    conv_lhs => rw [← Finsupp.sum_single c]
    simp only [Finsupp.sum,map_sum,hn]
  rw [hz]
  simp only [map_sum,map_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [← Finset.smul_sum]
  exact congrArg (c σ • ·) (hgen σ hσ)

include y₀ in
theorem sigmaHomologyBasis_surjective : Function.Surjective (sigmaHomologyBasisMap (J:=J) e) := by
  intro h
  obtain ⟨z,rfl⟩ := (boundaries (univ : Set (Σ _ : J,Y))).mkQ_surjective h
  obtain ⟨c,hc⟩ := (D₁ _).mkQ_surjective z.val
  obtain ⟨S,hS⟩ := finite_fiber_decomposition y₀ c
  rw [hc] at hS
  let d : J →₀ ℤ := ∑ j ∈ S, Finsupp.single j (e (homologyOneMap (fiberProjection y₀ j) ((boundaries univ).mkQ z)))
  refine ⟨d,?_⟩
  change sigmaHomologyBasisMap e (∑ j ∈ S, Finsupp.single j _) = _
  simp only [map_sum,sigmaHomologyBasisMap,Finsupp.linearCombination_single]
  have he (w : HomologyOne Y) : e w • e.symm 1 = w := by
    apply e.injective
    simp
  have he' (j : J) : e (homologyOneMap (fiberProjection y₀ j) ((boundaries univ).mkQ z)) •
      homologyOneMap (fiberInclusion j) (e.symm 1) =
      homologyOneMap (fiberInclusion j) (homologyOneMap (fiberProjection y₀ j) ((boundaries univ).mkQ z)) := by
    rw [← map_smul,he]
  simp_rw [he']
  simp only [homologyOneMap,homologyMap_mk,← map_sum]
  congr 1
  apply Subtype.ext
  rw [Submodule.coe_sum]
  change ∑ j ∈ S, pushN₁ (fiberInclusion j) (pushN₁ (fiberProjection y₀ j) z.val) = z.val
  exact hS

/-- The integral H1 basis of an arbitrary disjoint union of copies of a space
with H1=Z; all chains and decompositions have genuinely finite support. -/
def sigmaHomologyBasis : (J →₀ ℤ) ≃ₗ[ℤ] HomologyOne (Σ _ : J,Y) :=
  LinearEquiv.ofBijective (sigmaHomologyBasisMap e)
    ⟨sigmaHomologyBasis_injective y₀ e,sigmaHomologyBasis_surjective y₀ e⟩

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.PathTransport
open Set CubicalSingular
variable {X G : Type*} [TopologicalSpace X] [Group G]

structure TwoPotential (U V : Set X) where
  left : X → G
  right : X → G
  agree : ∀ γ : Cube₁ X, Set.range γ ⊆ U ∩ V →
    (left (γ 0))⁻¹ * left (γ 1) = (right (γ 0))⁻¹ * right (γ 1)

namespace TwoPotential
variable {U V : Set X} (a : TwoPotential (G:=G) U V)

def value (γ : Cube₁ X) : G := if Set.range γ ⊆ U then (a.left (γ 0))⁻¹ * a.left (γ 1)
  else (a.right (γ 0))⁻¹ * a.right (γ 1)

theorem value_left (γ : Cube₁ X) (h : Set.range γ ⊆ U) :
    a.value γ = (a.left (γ 0))⁻¹ * a.left (γ 1) := ite_eq_left h

theorem value_right (γ : Cube₁ X) (h : Set.range γ ⊆ V) :
    a.value γ = (a.right (γ 0))⁻¹ * a.right (γ 1) := by
  unfold value
  split_ifs with hU
  · exact a.agree γ (fun x hx => ⟨hU hx,h hx⟩)
  · rfl

theorem value_const (x : X) : a.value (ContinuousMap.const I x) = 1 := by
  unfold value
  split_ifs <;> simp

theorem small_either {Y : Type*} [MetricSpace Y] (γ : C(Y,X))
    (h : γ ∈ CubicalMesh.small ({U,V} : Set (Set X))) : Set.range γ ⊆ U ∨ Set.range γ ⊆ V := by
  rcases h with ⟨W,hW,hγ⟩
  simp only [mem_insert_iff,mem_singleton_iff] at hW
  rcases hW with rfl | rfl
  · exact Or.inl hγ
  · exact Or.inr hγ

def system : Local (G:=G) ({U,V} : Set (Set X)) where
  value := a.value
  constant := a.value_const
  split := by
    intro γ h
    rcases small_either γ h with h | h
    · rw [a.value_left γ h,a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨half false t,ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨half true t,ht⟩)]
      simp only [cut₁,ContinuousMap.coe_comp,Function.comp_apply,half_false_zero,half_true_one,half_mid]
      group
    · rw [a.value_right γ h,a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨half false t,ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨half true t,ht⟩)]
      simp only [cut₁,ContinuousMap.coe_comp,Function.comp_apply,half_false_zero,half_true_one,half_mid]
      group
  square := by
    intro σ h
    rcases small_either σ h with h | h
    · rw [a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(t,0),ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(1,t),ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(0,t),ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(t,1),ht⟩)]
      simp only [edge₁,edge₂,ContinuousMap.coe_mk]
      group
    · rw [a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(t,0),ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(1,t),ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(0,t),ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(t,1),ht⟩)]
      simp only [edge₁,edge₂,ContinuousMap.coe_mk]
      group

def transport (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) : Cube₁ X → G :=
  a.system.transport (cover_open hU hV) (cover_univ hUV)

end TwoPotential
end EilenbergGanea.PathTransport

namespace EilenbergGanea.ForestCover
open Set PathTransport CubicalSingular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

variable {r : X} (q : ∀ x, Path r x)

def potential (f : C(Y,X)) (x : Y) : (FundamentalGroup X r)ᵐᵒᵖ :=
  basedPath q ((componentStem x).map f.continuous)

theorem potential_path (hY : ThinPaths Y) (f : C(Y,X)) {x y : Y} (p : Path x y) :
    holonomy q (p.map f.continuous).toContinuousMap = (potential q f x)⁻¹ * potential q f y := by
  have h := (hY _ _ ((componentStem x).trans p)
    ((componentStem y).cast (componentRoot_eq p) rfl)).map f
  have he := basedPath_homotopic q h
  rw [Path.map_trans,basedPath_trans] at he
  have hy : basedPath q (((componentStem y).cast (componentRoot_eq p) rfl).map f.continuous) = potential q f y :=
    basedPath_congr q _ _ (fun _ => rfl)
  rw [hy] at he
  rw [holonomy_path]
  exact (eq_inv_mul_iff_mul_eq.mpr he)

variable (U V : Set X)

def gauge (x : X) : (FundamentalGroup X r)ᵐᵒᵖ :=
  if h : x ∈ U then potential q (inclusion U) ⟨x,h⟩
  else if h : x ∈ V then potential q (inclusion V) ⟨x,h⟩ else 1

def overlapValue (x : (U ∩ V : Set X)) : (FundamentalGroup X r)ᵐᵒᵖ :=
  potential q (inclusion V) ⟨x.val,x.property.2⟩ *
    (potential q (inclusion U) ⟨x.val,x.property.1⟩)⁻¹

theorem overlapValue_path (hU : ThinPaths U) (hV : ThinPaths V)
    {x y : (U ∩ V : Set X)} (p : Path x y) : overlapValue q U V x = overlapValue q U V y := by
  let pU : Path (⟨x.val,x.property.1⟩ : U) ⟨y.val,y.property.1⟩ :=
    p.map (continuous_subtype_val.subtype_mk (fun z => z.property.1))
  let pV : Path (⟨x.val,x.property.2⟩ : V) ⟨y.val,y.property.2⟩ :=
    p.map (continuous_subtype_val.subtype_mk (fun z => z.property.2))
  have h₁ := potential_path q hU (inclusion U) pU
  have h₂ := potential_path q hV (inclusion V) pV
  have he : (potential q (inclusion U) ⟨x.val,x.property.1⟩)⁻¹ * potential q (inclusion U) ⟨y.val,y.property.1⟩ =
      (potential q (inclusion V) ⟨x.val,x.property.2⟩)⁻¹ * potential q (inclusion V) ⟨y.val,y.property.2⟩ :=
    h₁.symm.trans h₂
  unfold overlapValue
  have hh := congrArg (fun z => potential q (inclusion V) ⟨x.val,x.property.2⟩ * z *
    (potential q (inclusion U) ⟨y.val,y.property.1⟩)⁻¹) he
  simpa only [mul_assoc,inv_mul_cancel,mul_inv_cancel,mul_one,one_mul,mul_inv_cancel_left] using hh

def evaluation (hU : ThinPaths U) (hV : ThinPaths V) :
    FreeGroup (ZerothHomotopy (U ∩ V : Set X)) →* (FundamentalGroup X r)ᵐᵒᵖ :=
  FreeGroup.lift (ZerothHomotopy.lift (overlapValue q U V) (fun _ _ p => overlapValue_path q U V hU hV p))

@[simp] theorem rightLabel_overlap (x : (U ∩ V : Set X)) :
    rightLabel U V x.val = FreeGroup.of (ZerothHomotopy.mk x) := dite_eq_left x.property

def labels : TwoPotential (G:=FreeGroup (ZerothHomotopy (U ∩ V : Set X))) U V where
  left := fun _ => 1
  right := rightLabel U V
  agree := by
    intro γ hγ
    let p : Path (⟨γ 0,hγ ⟨0,rfl⟩⟩ : (U ∩ V : Set X)) ⟨γ 1,hγ ⟨1,rfl⟩⟩ :=
      ⟨⟨fun t => ⟨γ t,hγ ⟨t,rfl⟩⟩,γ.continuous.subtype_mk _⟩,rfl,rfl⟩
    simp only [inv_one,mul_one]
    have hh : rightLabel U V (γ 0) = rightLabel U V (γ 1) := by
      rw [rightLabel_overlap U V ⟨γ 0,hγ ⟨0,rfl⟩⟩,
        rightLabel_overlap U V ⟨γ 1,hγ ⟨1,rfl⟩⟩]
      exact congrArg FreeGroup.of (ZerothHomotopy.sound p)
    rw [hh,inv_mul_cancel]

end EilenbergGanea.ForestCover

namespace EilenbergGanea.PathTransport
open Set CubicalSingular ForestCover
variable {X G : Type*} [TopologicalSpace X] [Group G]

structure LeftPotential (U V : Set X) (r : U) (q : ∀ x : U, Path r x) (ρ : (FundamentalGroup U r)ᵐᵒᵖ →* G) where
  right : X → G
  agree : ∀ (γ : Cube₁ X) (hc : Set.range γ ⊆ U ∩ V),
    ρ (holonomy q (liftCube U γ (fun _ hx => (hc hx).1))) = (right (γ 0))⁻¹ * right (γ 1)

namespace LeftPotential
variable {U V : Set X} {r : U} {q : ∀ x : U, Path r x} {ρ : (FundamentalGroup U r)ᵐᵒᵖ →* G}
variable (a : LeftPotential U V r q ρ)

def value (γ : Cube₁ X) : G := if h : Set.range γ ⊆ U then ρ (holonomy q (liftCube U γ h))
  else (a.right (γ 0))⁻¹ * a.right (γ 1)

theorem value_left (γ : Cube₁ X) (h : Set.range γ ⊆ U) :
    a.value γ = ρ (holonomy q (liftCube U γ h)) := dite_eq_left h

theorem value_right (γ : Cube₁ X) (h : Set.range γ ⊆ V) :
    a.value γ = (a.right (γ 0))⁻¹ * a.right (γ 1) := by
  unfold value
  split_ifs with hU
  · exact a.agree γ (fun x hx => ⟨hU hx,h hx⟩)
  · rfl

def system : Local (G:=G) ({U,V} : Set (Set X)) where
  value := a.value
  constant := by
    intro x
    unfold value
    split_ifs with h
    · have he : liftCube U (ContinuousMap.const I x) h = ContinuousMap.const I ⟨x,h ⟨0,rfl⟩⟩ := rfl
      rw [he,holonomy_const,map_one]
    · simp
  split := by
    intro γ h
    rcases TwoPotential.small_either γ h with h | h
    · rw [a.value_left γ h,a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨half false t,ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨half true t,ht⟩)]
      exact (congrArg ρ (holonomy_split q (liftCube U γ h))).trans (map_mul ρ _ _)
    · rw [a.value_right γ h,a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨half false t,ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨half true t,ht⟩)]
      simp only [cut₁,ContinuousMap.coe_comp,Function.comp_apply,half_false_zero,half_true_one,half_mid]
      group
  square := by
    intro σ h
    rcases TwoPotential.small_either σ h with h | h
    · rw [a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(t,0),ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(1,t),ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(0,t),ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(t,1),ht⟩)]
      exact (map_mul ρ _ _).symm.trans ((congrArg ρ (holonomy_square q (liftCube U σ h))).trans (map_mul ρ _ _))
    · rw [a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(t,0),ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(1,t),ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(0,t),ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(t,1),ht⟩)]
      simp only [edge₁,edge₂,ContinuousMap.coe_mk]
      group

end LeftPotential

@[simp] theorem basedPath_symm {r x y : X} (q : ∀ z, Path r z) (p : Path x y) :
    basedPath q p.symm = (basedPath q p)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← basedPath_trans]
  exact (basedPath_homotopic q (Path.Homotopic.symm_trans p)).trans (basedPath_refl q _)

variable {U V : Set X} {r : U} (q : ∀ x : U, Path r x) (ρ : (FundamentalGroup U r)ᵐᵒᵖ →* G)

def KillsOverlap : Prop := ∀ (z : (U ∩ V : Set X)) (p : Path z z), ρ (basedPath q (p.map capInclusion.continuous)) = 1

theorem overlap_potential_path (hk : KillsOverlap (V:=V) q ρ)
    {x y : (U ∩ V : Set X)} (p : Path x y) :
    ρ (basedPath q (p.map capInclusion.continuous)) =
      (ρ (potential q capInclusion x))⁻¹ * ρ (potential q capInclusion y) := by
  let sy := (componentStem y).cast (componentRoot_eq p) rfl
  have h := hk (componentRoot x) (((componentStem x).trans p).trans sy.symm)
  rw [Path.map_trans,Path.map_trans,← Path.map_symm] at h
  simp only [basedPath_trans,basedPath_symm,map_mul,map_inv] at h
  have he : basedPath q (sy.map capInclusion.continuous) = potential q capInclusion y :=
    basedPath_congr q _ _ (fun _ => rfl)
  rw [he] at h
  change ρ (potential q capInclusion x) * _ * (ρ (potential q capInclusion y))⁻¹ = 1 at h
  apply eq_inv_mul_iff_mul_eq.mpr
  exact mul_inv_eq_one.mp h

def overlapPotential (x : X) : G :=
  if h : x ∈ U ∩ V then ρ (potential q capInclusion ⟨x,h⟩) else 1

@[simp] theorem overlapPotential_cap (x : (U ∩ V : Set X)) :
    overlapPotential (V:=V) q ρ x.val = ρ (potential q capInclusion x) := dite_eq_left x.property

def patched (hk : KillsOverlap (V:=V) q ρ) : LeftPotential U V r q ρ where
  right := overlapPotential q ρ
  agree γ hc := by
    let p := cubePath (liftCube (U ∩ V) γ hc)
    rw [overlapPotential_cap q ρ ⟨γ 0,hc ⟨0,rfl⟩⟩,overlapPotential_cap q ρ ⟨γ 1,hc ⟨1,rfl⟩⟩]
    exact overlap_potential_path q ρ hk p

end EilenbergGanea.PathTransport

namespace EilenbergGanea.PathTransport
open CubicalSingular
variable {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Group G]
variable {r : X} (q : ∀ y, Path r y)

def basedHom (f : C(Y,X)) (y : Y) : (FundamentalGroup Y y)ᵐᵒᵖ →* (FundamentalGroup X r)ᵐᵒᵖ where
  toFun w := based q ((FundamentalGroup.map f y) w.unop)
  map_one' := by
    change based q ((FundamentalGroup.map f y) 1) = 1
    rw [map_one]
    exact based_refl q _
  map_mul' u v := by
    change based q ((FundamentalGroup.map f y) (v.unop * u.unop)) = _
    rw [map_mul]
    exact based_trans q _ _

@[simp] theorem basedHom_loop (f : C(Y,X)) {y : Y} (p : Path y y) :
    basedHom q f y (MulOpposite.op (asClass p)) = basedPath q (p.map f.continuous) := rfl

end EilenbergGanea.PathTransport

namespace EilenbergGanea.CWCollar.Attachment
open Set CubicalSingular PathTransport
variable {X J : Type*} [TopologicalSpace X] (a : Attachment X J 2)
variable {r : a.outer} (q : ∀ y, Path r y) (y₀ : Annulus 2)

def annulusMap (j : J) : C(Annulus 2,a.outer) :=
  capInclusion.comp ((a.annulusHomeomorph : C((Σ _ : J,Annulus 2),(a.outer ∩ a.inner : Set X))).comp (fiberInclusion j))

def annulusRelator (j : J) : (FundamentalGroup a.outer r)ᵐᵒᵖ :=
  basedPath q ((annulusGenerator y₀).map (a.annulusMap j).continuous)

end EilenbergGanea.CWCollar.Attachment

namespace EilenbergGanea.CWCollar
open Set CubicalSingular PathTransport
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace Attachment
variable {J : Type*} (a : Attachment X J 2)

def annularBasis [ContractibleSpace X] (y₀ : Annulus 2) :
    (J →₀ ℤ) ≃ₗ[ℤ] HomologyOne a.outer :=
  (sigmaHomologyBasis y₀ (annulusHomologyInt y₀)).trans
    ((homologyOneEquiv (a.annulusHomeomorph : C(_, _)) (a.annulusHomeomorph.symm : C(_, _))
      (by simpa using ContinuousMap.Homotopy.refl (ContinuousMap.id _))
      (by simpa using ContinuousMap.Homotopy.refl (ContinuousMap.id _))).trans a.outerCapHomologyEquiv)

end Attachment
end EilenbergGanea.CWCollar


namespace EilenbergGanea.PathTransport.Local
open Set CubicalSingular
variable {X G H : Type*} [TopologicalSpace X] [Group G] [Group H]
variable {U : Set (Set X)} (l : Local (G:=G) U) (φ : G →* H)

def map : Local (G:=H) U where
  value := fun γ => φ (l.value γ)
  constant := fun x => by rw [l.constant,map_one]
  split := fun γ h => by rw [l.split γ h,map_mul]
  square := fun σ h => by rw [← map_mul,← map_mul,l.square σ h]

end EilenbergGanea.PathTransport.Local


namespace EilenbergGanea.ForestCover
open Set PathTransport CubicalSingular
variable {X : Type*} [TopologicalSpace X] {r : X} (q : ∀ x, Path r x) (U V : Set X)
variable (hU : ThinPaths U) (hV : ThinPaths V)

def gauged (γ : Cube₁ X) : (FundamentalGroup X r)ᵐᵒᵖ :=
  gauge q U V (γ 0) * holonomy q γ * (gauge q U V (γ 1))⁻¹

end EilenbergGanea.ForestCover


namespace EilenbergGanea.CWSubspace
open Set Metric Topology CWCover CWCollar
variable {X : Type*} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

def characteristic {n : ℕ} (i : Cell C n) : C(Disk n,C) :=
  ⟨fun z => ⟨RelCWComplex.map n i z.val,
    RelCWComplex.closedCell_subset_complex n i ⟨z.val,z.property,rfl⟩⟩,
    (continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn n i)).subtype_mk _⟩

abbrev CellDisks := Σ c : (Σ n, Cell C n), Disk c.1
def diskSum : CellDisks C → C := fun c => characteristic C c.1.2 c.2

omit [T2Space X] in
theorem diskSum_continuous : Continuous (diskSum C) :=
  continuous_sigma (fun c => (characteristic C c.2).continuous)

omit [T2Space X] in
theorem diskSum_surjective : Function.Surjective (diskSum C) := by
  intro x
  have hx : x.val ∈ ⋃ (n : ℕ) (i : Cell C n), RelCWComplex.closedCell n i := by
    rw [CWComplex.union]; exact x.property
  obtain ⟨n,i,z,hz,he⟩ := by simpa only [Set.mem_iUnion,RelCWComplex.closedCell,Set.mem_image] using hx
  exact ⟨⟨⟨n,i⟩,⟨z,hz⟩⟩,Subtype.ext he⟩

theorem diskSum_quotient : IsQuotientMap (diskSum C) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨diskSum_surjective C,fun A => ⟨fun h => h.preimage (diskSum_continuous C),?_⟩⟩
  intro hA
  have hc : IsClosed ((Subtype.val : C → X) '' A) := by
    apply (CWComplex.closed C _ (by rintro _ ⟨x,_,rfl⟩; exact x.property)).mpr
    intro n i
    have hD : IsClosed (characteristic C i ⁻¹' A) :=
      hA.preimage (continuous_sigmaMk (i := (⟨n,i⟩ : Σ n,Cell C n)))
    have he : (fun z : Disk n => (characteristic C i z).val) '' (characteristic C i ⁻¹' A) =
        (Subtype.val '' A) ∩ RelCWComplex.closedCell n i := by
      ext x
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact ⟨⟨characteristic C i z,hz,rfl⟩,z.val,z.property,rfl⟩
      · rintro ⟨⟨y,hy,hxy⟩,z,hz,he⟩
        refine ⟨⟨z,hz⟩,?_,he⟩
        have h : characteristic C i ⟨z,hz⟩ = y := Subtype.ext (he.trans hxy.symm)
        simpa only [mem_preimage,h] using hy
    rw [← he]
    exact (hD.isCompact.image (continuous_subtype_val.comp (characteristic C i).continuous)).isClosed
  have hpre := hc.preimage (continuous_subtype_val : Continuous (Subtype.val : C → X))
  simpa only [Set.preimage_image_eq _ Subtype.val_injective] using hpre

theorem characteristic_lower {k m : ℕ} (hk : k < m) (i : Cell C k) (z : Disk k) :
    characteristic C i z ∈ lower C m := by
  apply RelCWComplex.skeletonLT_mono (show (k:ℕ∞)+1 ≤ (m:ℕ∞) by exact_mod_cast Nat.succ_le_of_lt hk)
    (RelCWComplex.closedCell_subset_skeletonLT k i (show (characteristic C i z).val ∈ RelCWComplex.closedCell k i from ?_))
  exact ⟨z.val,z.property,rfl⟩

def topSum (m : ℕ) : lower C m ⊕ (Σ _ : Cell C m, Disk m) → C :=
  Sum.elim Subtype.val (fun c => characteristic C c.1 c.2)

theorem topSum_continuous (m : ℕ) : Continuous (topSum C m) :=
  continuous_subtype_val.sumElim (continuous_sigma (fun i => (characteristic C i).continuous))

theorem topSum_surjective (m : ℕ) (hd : ∀ k, m < k → IsEmpty (Cell C k)) :
    Function.Surjective (topSum C m) := by
  intro x
  obtain ⟨⟨⟨k,i⟩,z⟩,rfl⟩ := diskSum_surjective C x
  by_cases hk : k < m
  · exact ⟨.inl ⟨characteristic C i z,characteristic_lower C hk i z⟩,rfl⟩
  · have hkm : k = m := by
      by_contra h
      have := hd k (by omega)
      exact isEmptyElim i
    subst k
    exact ⟨.inr ⟨i,z⟩,rfl⟩

theorem topSum_quotient (m : ℕ) (hd : ∀ k, m < k → IsEmpty (Cell C k)) :
    IsQuotientMap (topSum C m) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨topSum_surjective C m hd,fun A => ⟨fun h => h.preimage (topSum_continuous C m),?_⟩⟩
  intro hA
  apply (diskSum_quotient C).isClosed_preimage.mp
  rw [isClosed_sigma_iff]
  rintro ⟨k,i⟩
  by_cases hk : k < m
  · let f : Disk k → lower C m ⊕ (Σ _ : Cell C m,Disk m) :=
      fun z => .inl ⟨characteristic C i z,characteristic_lower C hk i z⟩
    exact hA.preimage (continuous_inl.comp ((characteristic C i).continuous.subtype_mk (characteristic_lower C hk i)))
  · have hkm : k = m := by
      by_contra h
      have := hd k (by omega)
      exact isEmptyElim i
    subst k
    exact hA.preimage (continuous_inr.comp (continuous_sigmaMk (i := i)))

def attachment (m : ℕ) (hd : ∀ k, m < k → IsEmpty (Cell C k)) : Attachment C (Cell C m) m where
  lower := lower C m
  closed_lower := (CWComplex.skeletonLT C m).closed'.preimage continuous_subtype_val
  chart := characteristic C
  boundary := by
    intro i z hz
    exact RelCWComplex.cellFrontier_subset_skeletonLT m i
      ⟨z.val,by simpa only [mem_sphere,dist_zero_right] using hz,rfl⟩
  interior := by
    intro i z hz hl
    exact Set.disjoint_left.mp (RelCWComplex.disjoint_skeletonLT_openCell le_rfl) hl
      ⟨z.val,by simpa only [mem_ball,dist_zero_right] using hz,rfl⟩
  disjoint := by
    intro i j z w hz hw he
    have he := congrArg Subtype.val he
    have hz' : z.val ∈ ball (0 : Fin m → ℝ) 1 := by simpa only [mem_ball,dist_zero_right] using hz
    have hw' : w.val ∈ ball (0 : Fin m → ℝ) 1 := by simpa only [mem_ball,dist_zero_right] using hw
    by_cases hij : i = j
    · subst j
      refine ⟨rfl,Subtype.ext ((RelCWComplex.map m i).injOn ?_ ?_ he)⟩
      · simpa only [RelCWComplex.source_eq] using hz'
      · simpa only [RelCWComplex.source_eq] using hw'
    · exact False.elim (Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne
        (show (⟨m,i⟩ : Σ k,Cell C k) ≠ ⟨m,j⟩ by simpa using hij))
        ⟨z.val,hz',rfl⟩ ⟨w.val,hw',he.symm⟩)
  quotient := topSum_quotient C m hd

end EilenbergGanea.CWSubspace



end

end OAI
end

section
-- module Solutions.OAIEG.CWComplex_CoverTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea.CWCover
open Classical
open scoped unitInterval
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

def diskContraction (n : ℕ) : C(unitInterval × Disk n,Disk n) where
  toFun tz := ⟨(1 - (tz.1 : ℝ)) • tz.2.val,
    (convex_closedBall (0 : Fin n → ℝ) 1).smul_mem_of_zero_mem (by simp) tz.2.property
      ⟨sub_nonneg.mpr tz.1.property.2,by linarith [tz.1.property.1]⟩⟩
  continuous_toFun := (by fun_prop : Continuous (fun tz : unitInterval × Disk n =>
    (1 - (tz.1 : ℝ)) • tz.2.val)).subtype_mk _

@[simp] theorem diskContraction_zero (n : ℕ) (z : Disk n) : diskContraction n (0,z) = z := by
  apply Subtype.ext
  simp [diskContraction]

@[simp] theorem diskContraction_one (n : ℕ) (z : Disk n) :
    diskContraction n (1,z) = diskCenter n := by
  apply Subtype.ext
  simp [diskContraction,diskCenter]

abbrev CellPullback {n : ℕ} (i : Cell (X := X) n) :=
  {ez : E × Disk n // p ez.1 = characteristic i ez.2}

def cellPullbackHomotopy {n : ℕ} (i : Cell (X := X) n) :
    C(unitInterval × CellPullback (p := p) i,X) :=
  (characteristic i).comp ((diskContraction n).comp
    ⟨fun tz => (tz.1,tz.2.val.2),by fun_prop⟩)

def cellPullbackStart {n : ℕ} (i : Cell (X := X) n) : C(CellPullback (p := p) i,E) :=
  ⟨fun ez => ez.val.1,by fun_prop⟩

theorem cellPullbackHomotopy_zero {n : ℕ} (i : Cell (X := X) n) (ez : CellPullback (p := p) i) :
    cellPullbackHomotopy i (0,ez) = p (cellPullbackStart i ez) := by
  change characteristic i (diskContraction n (0,ez.val.2)) = p ez.val.1
  rw [diskContraction_zero]
  exact ez.property.symm

def cellEndpoint {n : ℕ} (i : Cell (X := X) n) : C(CellPullback (p := p) i,E) :=
  (cov.liftHomotopy (cellPullbackHomotopy i) (cellPullbackStart i)
    (cellPullbackHomotopy_zero i)).comp ⟨fun ez => (1,ez),by fun_prop⟩

theorem cellEndpoint_project {n : ℕ} (i : Cell (X := X) n)
    (ez : CellPullback (p := p) i) :
    p (cellEndpoint cov i ez) = characteristic i (diskCenter n) := by
  have h := congrFun (cov.liftHomotopy_lifts (cellPullbackHomotopy i)
    (cellPullbackStart i) (cellPullbackHomotopy_zero i)) (1,ez)
  change p (cellEndpoint cov i ez) = characteristic i (diskContraction n (1,ez.val.2)) at h
  simpa only [diskContraction_one] using h

/-- The sheet-coordinate of a point on a lifted characteristic disk is
continuous, including along the disk's nonembedded attaching boundary. -/
def cellSheet {n : ℕ} (i : Cell (X := X) n) :
    C(CellPullback (p := p) i,{e : E // p e = characteristic i (diskCenter n)}) where
  toFun ez := ⟨cellEndpoint cov i ez,cellEndpoint_project cov i ez⟩
  continuous_toFun := (cellEndpoint cov i).continuous.subtype_mk _

/-- Sheet coordinates identify the actual origin of the unique lifted disk. -/
theorem cellSheet_lift {n : ℕ} (c : LiftedCell (p := p) n) (z : Disk n) :
    cellSheet cov c.1 ⟨(cellLift cov c z,z),cellLift_project cov c z⟩ = c.2 := by
  let ez : CellPullback (p := p) c.1 := ⟨(cellLift cov c z,z),cellLift_project cov c z⟩
  let f : C(unitInterval,E) := (cellLift cov c).comp
    ((diskContraction n).comp ⟨fun t => (t,z),by fun_prop⟩)
  let g : C(unitInterval,E) := (cov.liftHomotopy (cellPullbackHomotopy c.1)
    (cellPullbackStart c.1) (cellPullbackHomotopy_zero c.1)).comp
      ⟨fun t => (t,ez),by fun_prop⟩
  have he : (f : unitInterval → E) = g := cov.eq_of_comp_eq f.continuous g.continuous (by
    ext t
    change p (cellLift cov c (diskContraction n (t,z))) =
      p (cov.liftHomotopy (cellPullbackHomotopy c.1) (cellPullbackStart c.1)
        (cellPullbackHomotopy_zero c.1) (t,ez))
    rw [cellLift_project cov c]
    exact (congrFun (cov.liftHomotopy_lifts (cellPullbackHomotopy c.1)
      (cellPullbackStart c.1) (cellPullbackHomotopy_zero c.1)) (t,ez)).symm) 0 (by
    change cellLift cov c (diskContraction n (0,z)) =
      cov.liftHomotopy (cellPullbackHomotopy c.1) (cellPullbackStart c.1)
        (cellPullbackHomotopy_zero c.1) (0,ez)
    rw [diskContraction_zero,cov.liftHomotopy_zero]
    rfl)
  apply Subtype.ext
  change g 1 = c.2.val
  rw [← he]
  change cellLift cov c (diskContraction n (1,z)) = c.2.val
  rw [diskContraction_one,cellLift_center]

end EilenbergGanea.CWCover

namespace EilenbergGanea.CWCover
open Classical
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)
variable [T2Space X]

/-- A compact subset meets only finitely many sheets over each fixed closed
characteristic disk. Boundary points are included; the cell need not be regular. -/
theorem finite_touchingSheets {n : ℕ} (i : Cell (X := X) n) {K : Set E} (hK : IsCompact K) :
    {y : {e : E // p e = characteristic i (diskCenter n)} |
      ∃ z : Disk n, cellLift cov ⟨i,y⟩ z ∈ K}.Finite := by
  let S : Set (CellPullback (p := p) i) := {ez | ez.val.1 ∈ K}
  have hS : IsCompact S := by
    apply Subtype.isCompact_iff.mpr
    have he : Subtype.val '' S = (K ×ˢ Set.univ) ∩
        {ez : E × Disk n | p ez.1 = characteristic i ez.2} := by
      ext ez
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact ⟨⟨hw,trivial⟩,w.property⟩
      · rintro ⟨⟨hK,_⟩,he⟩
        exact ⟨⟨ez,he⟩,hK,rfl⟩
    rw [he]
    exact (hK.prod isCompact_univ).inter_right
      (isClosed_eq (cov.continuous.comp continuous_fst)
        ((characteristic i).continuous.comp continuous_snd))
  let : DiscreteTopology {e : E // p e = characteristic i (diskCenter n)} :=
    (cov (characteristic i (diskCenter n))).1
  have hfin : (cellSheet cov i '' S).Finite :=
    isCompact_iff_finite.mp (hS.image (cellSheet cov i).continuous)
  apply hfin.subset
  rintro y ⟨z,hz⟩
  refine ⟨⟨(cellLift cov ⟨i,y⟩ z,z),cellLift_project cov ⟨i,y⟩ z⟩,hz,?_⟩
  exact cellSheet_lift cov ⟨i,y⟩ z

end EilenbergGanea.CWCover


namespace EilenbergGanea.CWCover
open Classical
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] [T2Space X]
variable {p : E → X} (cov : IsCoveringMap p)

omit [T2Space X] in
@[simp] theorem liftedMap_image_disk {n : ℕ} (c : LiftedCell (p := p) n) :
    liftedMap cov c '' closedBall 0 1 = Set.range (cellLift cov c) := by
  ext e
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨⟨z,hz⟩,(liftedMapFun_disk cov c ⟨z,hz⟩).symm⟩
  · rintro ⟨z,rfl⟩
    exact ⟨z.val,z.property,liftedMapFun_disk cov c z⟩

omit [T2Space X] in
@[simp] theorem liftedMap_image_ball {n : ℕ} (c : LiftedCell (p := p) n) :
    liftedMap cov c '' ball 0 1 = liftedOpenCell cov c :=
  (liftedMap cov c).image_source_eq_target

/-- Compactness of the lifted boundary supplies the actual closure-finiteness
axiom, without assuming a locally finite or finite-cell classifying complex. -/
theorem lifted_mapsTo (n : ℕ) (c : LiftedCell (p := p) n) :
    ∃ J : Π m, Finset (LiftedCell (p := p) m),
      MapsTo (liftedMap cov c) (sphere 0 1)
        (⋃ (m < n) (j ∈ J m), liftedMap cov j '' closedBall 0 1) := by
  let K : Set E := liftedMap cov c '' sphere 0 1
  have hK : IsCompact K := (isCompact_sphere (0 : Fin n → ℝ) 1).image_of_continuousOn
    ((liftedMapFun_continuousOn cov c).mono sphere_subset_closedBall)
  obtain ⟨I,hI⟩ := CWComplex.mapsTo' n c.1
  let J (m : ℕ) : Finset (LiftedCell (p := p) m) := (I m).biUnion (fun i =>
    (finite_touchingSheets cov i hK).toFinset.image (fun y => ⟨i,y⟩))
  refine ⟨J,?_⟩
  intro z hz
  have hb := hI hz
  obtain ⟨m,hm,i,hi,w,hw,he⟩ := by
    simpa only [Set.mem_iUnion,Set.mem_image] using hb
  have he' : p (liftedMap cov c z) = characteristic i ⟨w,hw⟩ := by
    change p (liftedMapFun cov c z) = _
    have hzD : z ∈ closedBall (0 : Fin n → ℝ) 1 :=
      mem_closedBall.mpr (mem_sphere.mp hz).le
    rw [liftedMapFun_disk cov c ⟨z,hzD⟩]
    exact (cellLift_project cov c ⟨z,hzD⟩).trans he.symm
  obtain ⟨d,hdi,hdw⟩ := exists_cellLift_through cov i ⟨w,hw⟩ (liftedMap cov c z) he'
  have hdJ : d ∈ J m := by
    rcases d with ⟨j,y⟩
    dsimp at hdi
    subst j
    apply Finset.mem_biUnion.mpr
    refine ⟨i,hi,Finset.mem_image.mpr ⟨y,?_,rfl⟩⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨⟨w,hw⟩,hdw ▸ ⟨z,hz,rfl⟩⟩
  exact Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hm,Set.mem_iUnion.mpr
    ⟨d,Set.mem_iUnion.mpr ⟨hdJ,w,hw,(liftedMapFun_disk cov d ⟨w,hw⟩).trans hdw⟩⟩⟩⟩

/-- Every ordinary CW structure lifts through any covering, with exactly the
actual sheets times the base cells as cell indices. -/
@[instance_reducible] def cwComplex : CWComplex (univ : Set E) where
  cell := LiftedCell (p := p)
  map := fun _ c => liftedMap cov c
  source_eq := fun _ _ => rfl
  continuousOn := fun _ c => liftedMapFun_continuousOn cov c
  continuousOn_symm := fun _ c => liftedMap_continuousOn_symm cov c
  pairwiseDisjoint' := by
    intro a _ b _ hab
    simpa only [liftedMap_image_ball] using liftedOpenCells_disjoint cov a.2 b.2 hab
  mapsTo' := lifted_mapsTo cov
  closed' := by
    intro A _ hA
    apply isOpen_compl_iff.mp
    apply isOpen_of_cellLift_preimages cov
    intro n c
    have h := (hA n c).preimage (cellLift cov c).continuous
    have he : cellLift cov c ⁻¹' (A ∩ liftedMap cov c '' closedBall 0 1) =
        cellLift cov c ⁻¹' A := by
      rw [liftedMap_image_disk,Set.preimage_inter]
      simp only [Set.preimage_range,Set.inter_univ]
    rw [he] at h
    exact h.isOpen_compl
  union' := by
    apply Set.eq_univ_of_forall
    intro e
    obtain ⟨⟨⟨n,i⟩,z⟩,hz⟩ := characteristicSum_surjective (p e)
    obtain ⟨c,_,hc⟩ := exists_cellLift_through cov i z e hz.symm
    exact Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨c,z.val,z.property,
      (liftedMapFun_disk cov c z).trans hc⟩⟩

end EilenbergGanea.CWCover


namespace EilenbergGanea.CWCover
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] [T2Space X]
variable {p : E → X} (cov : IsCoveringMap p)

/-- Covering lifts preserve the literal absence of cells in each dimension. -/
theorem cwComplex_cell_isEmpty (n : ℕ) [IsEmpty (Topology.CWComplex.cell (univ : Set X) n)] :
    @IsEmpty (@Topology.CWComplex.cell E _ (univ : Set E) (cwComplex cov) n) := by
  change IsEmpty (LiftedCell (p := p) n)
  infer_instance

/-- No cardinality restriction is made in this dimension comparison. -/
theorem cwComplex_dimension_le (d : ℕ)
    (h : ∀ n, d < n → IsEmpty (Topology.CWComplex.cell (univ : Set X) n)) :
    ∀ n, d < n → @IsEmpty (@Topology.CWComplex.cell E _ (univ : Set E) (cwComplex cov) n) := by
  intro n hn
  let := h n hn
  exact cwComplex_cell_isEmpty cov n

end EilenbergGanea.CWCover


open Set Topology
open scoped unitInterval

namespace EilenbergGanea.CWCover
open CoverTopology
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

/-- Deck transformations act on the actual lifted cells through their centers. -/
instance liftedCellAction (n : ℕ) : MulAction (deckGroup p) (LiftedCell (p := p) n) where
  smul d c := ⟨c.1,⟨d • c.2.val,(deck_project p d c.2.val).trans c.2.property⟩⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem liftedCell_smul_base {n : ℕ} (d : deckGroup p) (c : LiftedCell (p := p) n) :
    (d • c).1 = c.1 := rfl

@[simp] theorem liftedCell_smul_center {n : ℕ} (d : deckGroup p) (c : LiftedCell (p := p) n) :
    (d • c).2.val = d • c.2.val := rfl

variable [ContractibleSpace E] (hs : Function.Surjective p)

/-- An arbitrary choice of one disk lift per base cell; no finiteness is needed. -/
def chosenCell {n : ℕ} (i : Cell (X := X) n) : LiftedCell (p := p) n :=
  ⟨i,⟨(hs (characteristic i (diskCenter n))).choose,
    (hs (characteristic i (diskCenter n))).choose_spec⟩⟩

/-- Every lifted ordinary cell is uniquely a deck translate of the chosen lift
of its base cell. This is the actual free-module coefficient indexing. -/
def cellOrbitEquiv (n : ℕ) : LiftedCell (p := p) n ≃ Cell (X := X) n × deckGroup p where
  toFun c := (c.1,(isQuotientCoveringMap_deck cov hs).fiberEquivGroup
    (chosenCell hs c.1).2 c.2)
  invFun j := j.2 • chosenCell hs j.1
  left_inv := by
    intro c
    change (⟨c.1, _⟩ : LiftedCell (p := p) n) = c
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact (isQuotientCoveringMap_deck cov hs).fiberEquivGroup_smul_self
        (chosenCell hs c.1).2
  right_inv := by
    rintro ⟨i,d⟩
    change (i, _) = (i,d)
    apply Prod.ext
    · rfl
    · exact ((isQuotientCoveringMap_deck cov hs).fiberEquivGroup_eq_iff _ _ _).mpr rfl

@[simp] theorem cellOrbitEquiv_symm {n : ℕ} (i : Cell (X := X) n) (d : deckGroup p) :
    (cellOrbitEquiv cov hs n).symm (i,d) = d • chosenCell hs i := rfl

end EilenbergGanea.CWCover


namespace EilenbergGanea.PathTransport
open Set CubicalSingular
variable {X : Type*} [TopologicalSpace X]

namespace Compression
variable {U V : Set X} (c : Compression U V)

def Represents {x y : X} (p : Path x y) : Prop :=
  ∃ s : Path (c.select x) (c.select y),
    (asClass (c.bridge x)).symm.trans ((asClass p).trans (asClass (c.bridge y))) = asClass (s.map continuous_subtype_val)

end Compression
end EilenbergGanea.PathTransport


namespace EilenbergGanea.CWCollar.Attachment
open Set Topology CWCover PathTransport CubicalSingular
variable {X J : Type*} [TopologicalSpace X] (a : Attachment X J 2)

noncomputable def annulusPoint : Annulus 2 := Classical.choice inferInstance

theorem annulus_inner (z : Σ _ : J, Annulus 2) :
    (a.annulusHomeomorph z).val = (a.innerHomeomorph ⟨z.1,z.2.val⟩).val := rfl

noncomputable def compressionChoice (x : X) :
    Σ y : a.outer, {p : Path x y.val //
      (x ∈ a.outer → Set.range p ⊆ a.outer) ∧ (x ∈ a.inner → Set.range p ⊆ a.inner)} := by
  by_cases hx : x ∈ a.outer
  · exact ⟨⟨x,hx⟩,Path.refl x,fun _ z hz => by obtain ⟨t,rfl⟩ := hz; exact hx,
      fun hv z hz => by obtain ⟨t,rfl⟩ := hz; exact hv⟩
  · have hv : x ∈ a.inner := by
      have he : x ∈ a.outer ∪ a.inner := by rw [a.outer_union_inner]; trivial
      exact he.resolve_left hx
    let z := a.innerHomeomorph.symm ⟨x,hv⟩
    let w : (a.outer ∩ a.inner : Set X) := a.annulusHomeomorph ⟨z.1,annulusPoint⟩
    let f : C(OpenDisk 2,X) := ⟨fun t => (a.innerHomeomorph ⟨z.1,t⟩).val,
      continuous_subtype_val.comp (a.innerHomeomorph.continuous.comp continuous_sigmaMk)⟩
    have hs : x = f z.2 := congrArg Subtype.val (a.innerHomeomorph.apply_symm_apply ⟨x,hv⟩).symm
    let p : Path x w.val := (((PathConnectedSpace.joined z.2 annulusPoint.val).somePath).map f.continuous).cast hs rfl
    refine ⟨⟨w.val,w.property.1⟩,p,fun ho => False.elim (hx ho),?_⟩
    intro _ y hy
    obtain ⟨t,rfl⟩ := hy
    exact (a.innerHomeomorph ⟨z.1,(PathConnectedSpace.joined z.2 annulusPoint.val).somePath t⟩).property

/-- The punctured-disk overlap is connected inside each open disk, so any
inner path joining overlap points can be replaced there. -/
theorem overlap_join (x y : (a.outer ∩ a.inner : Set X))
    (hp : Nonempty (Path (⟨x.val,x.property.2⟩ : a.inner) ⟨y.val,y.property.2⟩)) : Nonempty (Path x y) := by
  obtain ⟨p⟩ := hp
  let u := a.annulusHomeomorph.symm x
  let v := a.annulusHomeomorph.symm y
  let : TopologicalSpace J := ⊥
  let : DiscreteTopology J := ⟨rfl⟩
  let f : C(a.inner,J) := ⟨fun z => (a.innerHomeomorph.symm z).1,
    (continuous_sigma (fun _ => continuous_const)).comp a.innerHomeomorph.symm.continuous⟩
  have he₀ : f ⟨x.val,x.property.2⟩ = u.1 := by
    have h := congrArg (fun z : a.inner => (a.innerHomeomorph.symm z).1)
      (show (⟨x.val,x.property.2⟩ : a.inner) = a.innerHomeomorph ⟨u.1,u.2.val⟩ from
        Subtype.ext ((congrArg Subtype.val (a.annulusHomeomorph.apply_symm_apply x)).symm.trans (a.annulus_inner u)))
    simpa only [f,ContinuousMap.coe_mk,Homeomorph.symm_apply_apply] using h
  have he₁ : f ⟨y.val,y.property.2⟩ = v.1 := by
    have h := congrArg (fun z : a.inner => (a.innerHomeomorph.symm z).1)
      (show (⟨y.val,y.property.2⟩ : a.inner) = a.innerHomeomorph ⟨v.1,v.2.val⟩ from
        Subtype.ext ((congrArg Subtype.val (a.annulusHomeomorph.apply_symm_apply y)).symm.trans (a.annulus_inner v)))
    simpa only [f,ContinuousMap.coe_mk,Homeomorph.symm_apply_apply] using h
  have he : u.1 = v.1 := by
    have hh : f (p 0) = f (p 1) := (@inferInstance (PreconnectedSpace I)).constant (f.continuous.comp p.continuous)
    simpa only [p.source,p.target,he₀,he₁] using hh
  have hj : Joined u v := by
    obtain ⟨j,u⟩ := u
    obtain ⟨k,v⟩ := v
    dsimp only at he
    subst k
    exact (PathConnectedSpace.joined u v).map continuous_sigmaMk
  exact ⟨(hj.somePath.map a.annulusHomeomorph.continuous).cast
    (a.annulusHomeomorph.apply_symm_apply x).symm (a.annulusHomeomorph.apply_symm_apply y).symm⟩

noncomputable def compression : PathTransport.Compression a.outer a.inner where
  select x := (a.compressionChoice x).1
  bridge x := (a.compressionChoice x).2.val
  left x := (a.compressionChoice x).2.property.1
  right x := (a.compressionChoice x).2.property.2
  join := a.overlap_join

end EilenbergGanea.CWCollar.Attachment


namespace EilenbergGanea.CWCollar
open Set Metric Topology CWCover
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)


theorem lifted_characteristic {n : ℕ} (c : LiftedCell (p:=p) n) (z : Disk n) :
    let := CWCover.cwComplex cov
    characteristic (X:=E) c z = cellLift cov c z := liftedMapFun_disk cov c z

variable {m : ℕ} (hd : ∀ k, m < k → IsEmpty (Cell (X:=X) k))

abbrev baseAttachment := actualAttachment m hd
def liftedAttachment : Attachment E (LiftedCell (p:=p) m) m := by
  let := CWCover.t2Space cov
  let := CWCover.cwComplex cov
  exact actualAttachment m (cwComplex_dimension_le cov m hd)

/-- The radial coordinate is literally preserved by projection, including
all lower-skeleton points, not merely open-cell interiors. -/
theorem lifted_radius (e : E) :
    (liftedAttachment cov hd).radius e = (baseAttachment hd).radius (p e) := by
  let := CWCover.t2Space cov
  let := CWCover.cwComplex cov
  obtain ⟨⟨⟨k,c⟩,z⟩,rfl⟩ := characteristicSum_surjective (X:=E) e
  change (liftedAttachment cov hd).radius (characteristic c z) =
    (baseAttachment hd).radius (p (characteristic c z))
  by_cases hk : k < m
  · rw [(liftedAttachment cov hd).radius_lower
      ⟨characteristic c z,characteristic_mem_lower hk c z⟩]
    rw [lifted_characteristic cov c z,cellLift_project cov c z]
    exact ((baseAttachment hd).radius_lower ⟨characteristic c.1 z,characteristic_mem_lower hk c.1 z⟩).symm
  · have hkm : k = m := by
      by_contra he
      have := hd k (by omega)
      exact isEmptyElim c.1
    subst k
    change (liftedAttachment cov hd).radius ((liftedAttachment cov hd).chart c z) = _
    rw [(liftedAttachment cov hd).radius_chart]
    rw [lifted_characteristic cov c z,cellLift_project cov c z]
    exact ((baseAttachment hd).radius_chart c.1 z).symm

@[simp] theorem lifted_outer : (liftedAttachment cov hd).outer = p ⁻¹' (baseAttachment hd).outer := by
  ext e
  change 0 < (liftedAttachment cov hd).radius e ↔ 0 < (baseAttachment hd).radius (p e)
  rw [lifted_radius cov hd e]
@[simp] theorem lifted_inner : (liftedAttachment cov hd).inner = p ⁻¹' (baseAttachment hd).inner := by
  ext e
  change (liftedAttachment cov hd).radius e < 1 ↔ (baseAttachment hd).radius (p e) < 1
  rw [lifted_radius cov hd e]

def liftedOuterHomeomorph : (liftedAttachment cov hd).outer ≃ₜ p ⁻¹' (baseAttachment hd).outer :=
  Homeomorph.setCongr (lifted_outer cov hd)

def outerProjection : C((liftedAttachment cov hd).outer,(baseAttachment hd).outer) :=
  (⟨(baseAttachment hd).outer.restrictPreimage p,
    (cov.continuous.comp continuous_subtype_val).subtype_mk _⟩ :
    C(p ⁻¹' (baseAttachment hd).outer,(baseAttachment hd).outer)).comp
      (liftedOuterHomeomorph cov hd : C(_, _))

/-- The same parametrized annulus projects to the base annulus. -/
theorem lifted_annulus (c : LiftedCell (p:=p) m) (z : Annulus m) :
    p ((liftedAttachment cov hd).annulusHomeomorph ⟨c,z⟩).val =
      ((baseAttachment hd).annulusHomeomorph ⟨c.1,z⟩).val := by
  let := CWCover.cwComplex cov
  change p (characteristic c z.val.val) = characteristic c.1 z.val.val
  rw [lifted_characteristic cov,cellLift_project cov]

end EilenbergGanea.CWCollar



open Classical Set


namespace EilenbergGanea.PathTransport
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def anchored {r x : X} (q : Path r x) (p : Path x x) : (FundamentalGroup X r)ᵐᵒᵖ :=
  MulOpposite.op (asClass ((q.trans p).trans q.symm))
def difference {r x : X} (q s : Path r x) : (FundamentalGroup X r)ᵐᵒᵖ :=
  MulOpposite.op (asClass (q.trans s.symm))

@[simp] theorem anchored_map (f : C(X,Y)) {r x : X} (q : Path r x) (p : Path x x) :
    (FundamentalGroup.map f r).op (anchored q p) = anchored (q.map f.continuous) (p.map f.continuous) := by
  apply MulOpposite.unop_injective
  change asClass (((q.trans p).trans q.symm).map f.continuous) = _
  rw [Path.map_trans,Path.map_trans,← Path.map_symm]
  rfl

/-- Pointwise equality of anchored curves handles changes of endpoint proofs. -/
theorem anchored_congr {r x y : X} (q : Path r x) (s : Path r y)
    (p : Path x x) (t : Path y y) (hqs : ∀ z, q z = s z) (hpt : ∀ z, p z = t z) :
    anchored q p = anchored s t := by
  have hxy : x = y := by simpa using hqs 1
  subst y
  have hq : q = s := Path.ext (funext hqs)
  have hp : p = t := Path.ext (funext hpt)
  rw [hq,hp]

end EilenbergGanea.PathTransport




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

abbrev RelatorFactor (I : Type*) := SU2 × I × Bool

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

section QuotientChains
variable {Γ F R S T : Type*} [Group Γ] [Group F]

def translateChains (g : Γ) : BasedChains Γ S →ₗ[ℤ] BasedChains Γ S :=
  Finsupp.lmapDomain ℤ ℤ (fun i => (g*i.1, i.2))

def quotientChains (q : Γ →* F) : BasedChains Γ S →ₗ[ℤ] BasedChains F S :=
  Finsupp.lmapDomain ℤ ℤ (fun i => (q i.1, i.2))

@[simp] theorem translateChains_single (g h : Γ) (s : S) (n : ℤ) :
    translateChains g (Finsupp.single (h,s) n) = Finsupp.single (g*h,s) n := by
  simp [translateChains]

@[simp] theorem quotientChains_single (q : Γ →* F) (g : Γ) (s : S) (n : ℤ) :
    quotientChains q (Finsupp.single (g,s) n) = Finsupp.single (q g,s) n := by
  simp [quotientChains]

@[simp] theorem translateChains_one (c : BasedChains Γ S) : translateChains (1 : Γ) c = c := by
  have he : (translateChains (1 : Γ) : BasedChains Γ S →ₗ[ℤ] _) = LinearMap.id := by
    apply Finsupp.lhom_ext
    rintro ⟨g,s⟩ n
    simp
  exact LinearMap.congr_fun he c

/-- The elementary equivariance expressing a left integral group-ring map. -/
def ChainsEquivariant (A : BasedChains Γ R →ₗ[ℤ] BasedChains Γ S) : Prop :=
  ∀ g c, A (translateChains g c) = translateChains g (A c)

/-- Base change of a translation-equivariant matrix, directly on its finitely
supported columns. Its definition needs neither finite index sets nor flatness. -/
def quotientMatrix (q : Γ →* F) (A : BasedChains Γ R →ₗ[ℤ] BasedChains Γ S) :
    BasedChains F R →ₗ[ℤ] BasedChains F S :=
  Finsupp.linearCombination ℤ (fun i =>
    translateChains i.1 (quotientChains q (A (Finsupp.single (1,i.2) 1))))

@[simp] theorem quotientMatrix_single (q : Γ →* F)
    (A : BasedChains Γ R →ₗ[ℤ] BasedChains Γ S) (f : F) (r : R) (n : ℤ) :
    quotientMatrix q A (Finsupp.single (f,r) n) =
      n • translateChains f (quotientChains q (A (Finsupp.single (1,r) 1))) := by
  simp [quotientMatrix]

theorem ChainsEquivariant.symm (A : BasedChains Γ R ≃ₗ[ℤ] BasedChains Γ S)
    (hA : ChainsEquivariant A.toLinearMap) : ChainsEquivariant A.symm.toLinearMap := by
  intro g c
  apply A.injective
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using (hA g (A.symm c)).symm

end QuotientChains
end EilenbergGanea



namespace EilenbergGanea
section ChainProjection
variable {Γ D S T R : Type*} [Group Γ] [Group D]

def projectExtraChains : BasedChains Γ (S ⊕ T) →ₗ[ℤ] BasedChains Γ T :=
  Finsupp.linearCombination ℤ fun p => match p.2 with
    | .inl _ => 0
    | .inr t => Finsupp.single (p.1,t) 1

omit [Group Γ] in
@[simp] theorem projectExtraChains_single_left (g : Γ) (s : S) (n : ℤ) :
    projectExtraChains (Finsupp.single (g,Sum.inl s) n : BasedChains Γ (S ⊕ T)) = 0 := by
  simp [projectExtraChains]

omit [Group Γ] in
@[simp] theorem projectExtraChains_single_right (g : Γ) (t : T) (n : ℤ) :
    projectExtraChains (Finsupp.single (g,Sum.inr t) n : BasedChains Γ (S ⊕ T)) =
      Finsupp.single (g,t) n := by simp [projectExtraChains]

def extraRelatorMap (v : S ⊕ T → Γ) (r : R → FreeGroup (S ⊕ T)) :
    BasedChains Γ R →ₗ[ℤ] BasedChains Γ T :=
  projectExtraChains.comp (relatorChainMap v r)

@[simp] theorem extraRelatorMap_single (v : S ⊕ T → Γ) (r : R → FreeGroup (S ⊕ T))
    (g : Γ) (i : R) (n : ℤ) :
    extraRelatorMap v r (Finsupp.single (g,i) n) =
      n • projectExtraChains (pathChain v (r i) g) := by
  simp [extraRelatorMap, relatorChainMap]

end ChainProjection
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
section RelatorShears
variable {Γ S R I : Type*} [Group Γ]

@[simp] theorem relatorChainMap_single (v : S → Γ) (r : R → FreeGroup S)
    (g : Γ) (i : R) (n : ℤ) :
    relatorChainMap v r (Finsupp.single (g,i) n) = n • pathChain v (r i) g := by
  simp [relatorChainMap]

end RelatorShears
end EilenbergGanea

namespace EilenbergGanea
section CycleSpaces
variable {Γ S T U R : Type*} [Group Γ]

def edgeBoundary (v : S → Γ) : BasedChains Γ S →ₗ[ℤ] (Γ →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun p : Γ × S =>
    Finsupp.single (p.1 * v p.2) 1 - Finsupp.single p.1 1)

@[simp] theorem edgeBoundary_single (v : S → Γ) (g : Γ) (s : S) (n : ℤ) :
    edgeBoundary v (Finsupp.single (g,s) n) =
      n • (Finsupp.single (g * v s) 1 - Finsupp.single g 1) := by
  simp [edgeBoundary]

theorem edgeBoundary_pathChain (v : S → Γ) (w : FreeGroup S) (g : Γ) :
    edgeBoundary v (pathChain v w g) =
      Finsupp.single (g * wordValue v w) 1 - Finsupp.single g 1 := by
  induction w using OAI.freeGroupInductionOn generalizing g with
  | one => simp
  | of s => simp [wordValue]
  | inv_of s _ih => simp [pathChain_inv,wordValue]
  | mul w z hw hz =>
      rw [pathChain_mul,map_add,hw,hz,map_mul]
      simp only [mul_assoc]
      abel

abbrev cycles (v : S → Γ) := LinearMap.ker (edgeBoundary v)

end CycleSpaces
end EilenbergGanea

namespace EilenbergGanea
section SumChains
variable {Γ S T : Type*}

def sumChainsEquiv : BasedChains Γ (S ⊕ T) ≃ₗ[ℤ] BasedChains Γ S × BasedChains Γ T :=
  (Finsupp.domLCongr (Equiv.prodSumDistrib Γ S T)).trans (Finsupp.sumFinsuppLEquivProdFinsupp ℤ)

@[simp] theorem sumChainsEquiv_fst (c : BasedChains Γ (S ⊕ T)) (g : Γ) (s : S) :
    (sumChainsEquiv c).1 (g,s) = c (g,Sum.inl s) := by
  rfl

@[simp] theorem sumChainsEquiv_snd (c : BasedChains Γ (S ⊕ T)) (g : Γ) (t : T) :
    (sumChainsEquiv c).2 (g,t) = c (g,Sum.inr t) := by
  rfl

@[simp] theorem sumChainsEquiv_single_left (g : Γ) (s : S) (n : ℤ) :
    sumChainsEquiv (Finsupp.single (g,Sum.inl s) n : BasedChains Γ (S ⊕ T)) =
      (Finsupp.single (g,s) n,0) := by
  classical
  apply Prod.ext
  · ext ⟨h,i⟩
    simp [Finsupp.single_apply]
  · ext ⟨h,i⟩
    simp

@[simp] theorem sumChainsEquiv_single_right (g : Γ) (t : T) (n : ℤ) :
    sumChainsEquiv (Finsupp.single (g,Sum.inr t) n : BasedChains Γ (S ⊕ T)) =
      (0,Finsupp.single (g,t) n) := by
  classical
  apply Prod.ext
  · ext ⟨h,i⟩
    simp
  · ext ⟨h,i⟩
    simp [Finsupp.single_apply]

end SumChains
end EilenbergGanea

namespace EilenbergGanea
section Reindexing
variable {Γ S T U R I : Type*} [Group Γ]

def chainIndexEquiv (e : S ≃ T) : BasedChains Γ S ≃ₗ[ℤ] BasedChains Γ T :=
  Finsupp.domLCongr (Equiv.prodCongr (Equiv.refl Γ) e)

omit [Group Γ] in
@[simp] theorem chainIndexEquiv_single (e : S ≃ T) (g : Γ) (s : S) (n : ℤ) :
    chainIndexEquiv e (Finsupp.single (g,s) n) = Finsupp.single (g,e s) n := by
  simp [chainIndexEquiv]

end Reindexing
end EilenbergGanea

namespace EilenbergGanea
section ExtraProjectionAlignment
variable {Γ S T I R : Type*} [Group Γ]

/-- The ordinary diagonal block (1,-A), without finite-rank assumptions. -/
def ordinaryBlockEquiv (A : BasedChains Γ R ≃ₗ[ℤ] BasedChains Γ I) :
    BasedChains Γ (T ⊕ R) ≃ₗ[ℤ] BasedChains Γ (T ⊕ I) :=
  sumChainsEquiv.trans (((LinearEquiv.refl ℤ (BasedChains Γ T)).prodCongr
    (A.trans (LinearEquiv.neg ℤ))).trans sumChainsEquiv.symm)

omit [Group Γ] in
@[simp] theorem ordinaryBlockEquiv_value (A : BasedChains Γ R ≃ₗ[ℤ] BasedChains Γ I)
    (c : BasedChains Γ (T ⊕ R)) :
    sumChainsEquiv (ordinaryBlockEquiv A c) = ((sumChainsEquiv c).1,-A (sumChainsEquiv c).2) := by
  simp [ordinaryBlockEquiv]

end ExtraProjectionAlignment
end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.Presentation_KernelCycles
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff



namespace EilenbergGanea.KernelCycles
open Classical
variable {G A : Type*} [Group G] (a : A → G)

def kernelChainHom : Kernel a →* Multiplicative (cycles a) where
  toFun w := Multiplicative.ofAdd ⟨pathChain a w.val 1,by
    change edgeBoundary a (pathChain a w.val 1) = 0
    rw [edgeBoundary_pathChain,w.property,mul_one,sub_self]⟩
  map_one' := by apply (Equiv.refl _ : Multiplicative (cycles a) ≃ cycles a).injective; apply Subtype.ext; exact pathChain_one a 1
  map_mul' w z := by
    apply (Equiv.refl _ : Multiplicative (cycles a) ≃ cycles a).injective
    apply Subtype.ext
    change pathChain a (w.val*z.val) 1 = pathChain a w.val 1 + pathChain a z.val 1
    rw [pathChain_mul,w.property,mul_one]

def abKernelToCycles : AbKernel a →ₗ[ℤ] cycles a :=
  (Abelianization.lift (kernelChainHom a)).toAdditive.toIntLinearMap

@[simp] theorem abKernelToCycles_of (w : Kernel a) :
    (abKernelToCycles a (Additive.ofMul (Abelianization.of w))).val = pathChain a w.val 1 := rfl

variable (t : G → FreeGroup A) (ht : ∀ g, wordValue a (t g) = g)

def bridge (w : FreeGroup A) (g : G) : Kernel a :=
  ⟨t g * w * (t (g * wordValue a w))⁻¹,by
    change wordValue a (t g * w * (t (g * wordValue a w))⁻¹) = 1
    simp only [map_mul,map_inv,ht]
    group⟩

@[simp] theorem bridge_one (g : G) : bridge a t ht 1 g = 1 := by
  apply Subtype.ext
  simp [bridge]

theorem bridge_mul (w z : FreeGroup A) (g : G) :
    bridge a t ht (w*z) g = bridge a t ht w g * bridge a t ht z (g * wordValue a w) := by
  apply Subtype.ext
  simp only [bridge,Subgroup.coe_mul,map_mul,mul_assoc]
  group

theorem bridge_inv (w : FreeGroup A) (g : G) :
    bridge a t ht w⁻¹ g = (bridge a t ht w (g * (wordValue a w)⁻¹))⁻¹ := by
  apply Subtype.ext
  simp only [bridge,Subgroup.coe_inv,map_inv]
  simp only [inv_mul_cancel_right]
  group

def bridgeAb (w : FreeGroup A) (g : G) : AbKernel a :=
  Additive.ofMul (Abelianization.of (bridge a t ht w g))
@[simp] theorem bridgeAb_one (g : G) : bridgeAb a t ht 1 g = 0 := by simp [bridgeAb]
theorem bridgeAb_mul (w z : FreeGroup A) (g : G) :
    bridgeAb a t ht (w*z) g = bridgeAb a t ht w g + bridgeAb a t ht z (g * wordValue a w) := by
  unfold bridgeAb
  rw [bridge_mul,map_mul]
  rfl

theorem bridgeAb_inv (w : FreeGroup A) (g : G) :
    bridgeAb a t ht w⁻¹ g = -bridgeAb a t ht w (g * (wordValue a w)⁻¹) := by
  unfold bridgeAb
  rw [bridge_inv,map_inv]
  rfl

def chainsToKernel : BasedChains G A →ₗ[ℤ] AbKernel a :=
  Finsupp.linearCombination ℤ (fun p => bridgeAb a t ht (FreeGroup.of p.2) p.1)

@[simp] theorem chainsToKernel_single (g : G) (x : A) (n : ℤ) :
    chainsToKernel a t ht (Finsupp.single (g,x) n) = n • bridgeAb a t ht (FreeGroup.of x) g := by
  simp [chainsToKernel]

theorem chainsToKernel_pathChain (w : FreeGroup A) (g : G) :
    chainsToKernel a t ht (pathChain a w g) = bridgeAb a t ht w g := by
  induction w using OAI.freeGroupInductionOn generalizing g with
  | one => simp
  | of x => simp
  | inv_of x => rw [pathChain_inv,map_neg,bridgeAb_inv]; simp
  | mul w z hw hz => rw [pathChain_mul,map_add,hw,hz,bridgeAb_mul]

theorem bridgeAb_kernel (w : Kernel a) : bridgeAb a t ht w.val 1 = Additive.ofMul (Abelianization.of w) := by
  let u : Kernel a := ⟨t 1,ht 1⟩
  have he : bridge a t ht w.val 1 = u*w*u⁻¹ := by
    apply Subtype.ext
    change t 1 * w.val * (t (1 * wordValue a w.val))⁻¹ = t 1 * w.val * (t 1)⁻¹
    rw [w.property,mul_one]
  change Additive.ofMul (Abelianization.of (bridge a t ht w.val 1)) = _
  apply congrArg Additive.ofMul
  rw [he,map_mul,map_mul,map_inv]
  simp [mul_comm]

theorem chains_kernel_inverse (w : AbKernel a) :
    chainsToKernel a t ht (abKernelToCycles a w).val = w := by
  revert w
  change ∀ w : Abelianization (Kernel a),
    chainsToKernel a t ht (abKernelToCycles a (Additive.ofMul w)).val = Additive.ofMul w
  intro w
  induction w using QuotientGroup.induction_on with
  | H w =>
    change chainsToKernel a t ht (abKernelToCycles a (Additive.ofMul (Abelianization.of w))).val = Additive.ofMul (Abelianization.of w)
    rw [abKernelToCycles_of,chainsToKernel_pathChain,bridgeAb_kernel]

def anchors : (G →₀ ℤ) →ₗ[ℤ] BasedChains G A := Finsupp.linearCombination ℤ (fun g => pathChain a (t g) 1)

theorem bridge_chain (w : FreeGroup A) (g : G) :
    pathChain a (bridge a t ht w g).val 1 =
      pathChain a (t g) 1 + pathChain a w g - pathChain a (t (g * wordValue a w)) 1 := by
  change pathChain a (t g*w*(t (g*wordValue a w))⁻¹) 1 = _
  rw [pathChain_mul,pathChain_mul,pathChain_inv]
  simp only [ht,map_mul,one_mul,mul_inv_cancel,sub_eq_add_neg]

theorem kernel_chains_identity (c : BasedChains G A) :
    (abKernelToCycles a (chainsToKernel a t ht c)).val = c - anchors a t (edgeBoundary a c) := by
  have he : (cycles a).subtype.comp ((abKernelToCycles a).comp (chainsToKernel a t ht)) =
      LinearMap.id - (anchors a t).comp (edgeBoundary a) := by
    apply Finsupp.lhom_ext
    rintro ⟨g,x⟩ n
    simp only [LinearMap.comp_apply,chainsToKernel_single,map_smul,LinearMap.sub_apply,
      LinearMap.id_apply,edgeBoundary_single]
    change n • pathChain a (bridge a t ht (FreeGroup.of x) g).val 1 =
      Finsupp.single (g,x) n - n • anchors a t (Finsupp.single (g*a x) 1 - Finsupp.single g 1)
    rw [bridge_chain]
    simp only [pathChain_of,wordValue,FreeGroup.lift_apply_of,anchors,map_sub,Finsupp.linearCombination_single,one_smul]
    rw [← Finsupp.smul_single_one (g,x) n]
    simp only [smul_add,smul_sub]
    abel
  exact LinearMap.congr_fun he c

/-- The exact integral abelianized-kernel/Cayley-cycle comparison, with its
literal Fox/path-chain coefficients. No graph realization is assumed. -/
def abKernelCycleEquiv : AbKernel a ≃ₗ[ℤ] cycles a :=
  LinearEquiv.ofLinearMap (abKernelToCycles a) ((chainsToKernel a t ht).comp (cycles a).subtype)
    (by apply LinearMap.ext; intro c; apply Subtype.ext; exact (kernel_chains_identity a t ht c.val).trans (by rw [c.property,map_zero,sub_zero]; rfl))
    (by apply LinearMap.ext; intro w; exact chains_kernel_inverse a t ht w)

end EilenbergGanea.KernelCycles


end

end OAI
end

section
-- module Solutions.OAIEG.CWComplex_Presentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea.CWPresentation
open Set Topology CWCover CWCollar PathTransport CubicalSingular CoverTopology
open scoped ContinuousMap
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ : Set X)] {p : E → X}
variable (cov : IsCoveringMap p) (hd : ∀ k, 2 < k → IsEmpty (Cell (X:=X) k))

abbrev base := baseAttachment hd
abbrev lifted := liftedAttachment cov hd

variable [ContractibleSpace E]
variable (e : (lifted cov hd).outer)

abbrev root : (base hd).outer := outerProjection cov hd e
abbrev toTotal : (FundamentalGroup (base hd).outer (root cov hd e))ᵐᵒᵖ →*
    (FundamentalGroup X (p e.val))ᵐᵒᵖ :=
  (FundamentalGroup.map (CoverKernel.inclusion (base hd).outer) (root cov hd e)).op
abbrev fromLift : (FundamentalGroup (lifted cov hd).outer e)ᵐᵒᵖ →*
    (FundamentalGroup (base hd).outer (root cov hd e))ᵐᵒᵖ :=
  (FundamentalGroup.map (outerProjection cov hd) e).op

/-- Closed lifting gives the actual kernel, including all (possibly infinitely
many) lifted cells and without a cellular-homology assumption. -/
def liftedKernelEquiv : (FundamentalGroup (lifted cov hd).outer e)ᵐᵒᵖ ≃* (toTotal cov hd e).ker :=
  (homotopyFundamentalEquiv (liftedOuterHomeomorph cov hd).toHomotopyEquiv e).op.trans
    (CoverKernel.fundamentalKernelEquiv cov (base hd).outer (liftedOuterHomeomorph cov hd e))

@[simp] theorem liftedKernelEquiv_val (w : (FundamentalGroup (lifted cov hd).outer e)ᵐᵒᵖ) :
    (liftedKernelEquiv cov hd e w).val = fromLift cov hd e w := by
  obtain ⟨γ,hγ⟩ := Quotient.exists_rep w.unop
  have he : MulOpposite.op (asClass γ) = w := congrArg MulOpposite.op hγ
  rw [← he]
  rfl

variable (q : ∀ y : (lifted cov hd).outer, Path e y) (y₀ : Annulus 2)

def kernelBasis : (LiftedCell (p:=p) 2 →₀ ℤ) ≃ₗ[ℤ]
    Additive (Abelianization (toTotal cov hd e).ker) :=
  ((lifted cov hd).annularBasis y₀).trans ((hurewiczOne q).trans
    (liftedKernelEquiv cov hd e).abelianizationCongr.toAdditive.toIntLinearEquiv)

end EilenbergGanea.CWPresentation


namespace EilenbergGanea.CWPresentation
open Set Topology CWCover CWCollar PathTransport CubicalSingular CoverTopology
open scoped ContinuousMap
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ : Set X)] {p : E → X}
variable (cov : IsCoveringMap p) (hd : ∀ k, 2 < k → IsEmpty (Cell (X:=X) k))
variable [ContractibleSpace E] (e : (lifted cov hd).outer)
variable (q : ∀ y : (lifted cov hd).outer, Path e y) (y₀ : Annulus 2)

omit [ContractibleSpace E] in
@[simp] theorem project_annulus (c : LiftedCell (p:=p) 2) (z : Annulus 2) :
    outerProjection cov hd ((lifted cov hd).annulusMap c z) = (base hd).annulusMap c.1 z :=
  Subtype.ext (lifted_annulus cov hd c z)

def projectedAnchor (c : LiftedCell (p:=p) 2) :
    Path (root cov hd e) ((base hd).annulusMap c.1 y₀) :=
  ((q ((lifted cov hd).annulusMap c y₀)).map (outerProjection cov hd).continuous).cast rfl
    (project_annulus cov hd c y₀).symm

def projectedRelator (c : LiftedCell (p:=p) 2) :
    (FundamentalGroup (base hd).outer (root cov hd e))ᵐᵒᵖ :=
  anchored (projectedAnchor cov hd e q y₀ c)
    ((annulusGenerator y₀).map ((base hd).annulusMap c.1).continuous)

omit [ContractibleSpace E] in
theorem projectedRelator_eq (c : LiftedCell (p:=p) 2) :
    fromLift cov hd e ((lifted cov hd).annulusRelator q y₀ c) =
      projectedRelator cov hd e q y₀ c := by
  change (FundamentalGroup.map (outerProjection cov hd) e).op
    (anchored (q ((lifted cov hd).annulusMap c y₀))
      ((annulusGenerator y₀).map ((lifted cov hd).annulusMap c).continuous)) = _
  rw [anchored_map]
  apply anchored_congr
  · intro t; rfl
  · intro t; exact project_annulus cov hd c (annulusGenerator y₀ t)

variable (hs : Function.Surjective p)
def relator (j : Cell (X:=X) 2) := projectedRelator cov hd e q y₀ (chosenCell hs j)

@[simp] theorem relator_mem (j : Cell (X:=X) 2) : toTotal cov hd e (relator cov hd e q y₀ hs j) = 1 := by
  rw [relator,← projectedRelator_eq,← liftedKernelEquiv_val]
  exact (liftedKernelEquiv cov hd e ((lifted cov hd).annulusRelator q y₀ (chosenCell hs j))).property

end EilenbergGanea.CWPresentation


namespace EilenbergGanea.CWPresentation
open Set Topology CWCover CWCollar PathTransport CubicalSingular CoverTopology
open scoped ContinuousMap
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ : Set X)] {p : E → X}
variable (cov : IsCoveringMap p) (hd : ∀ k, 2 < k → IsEmpty (Cell (X:=X) k))
variable [ContractibleSpace E] (e : (lifted cov hd).outer)
variable (q : ∀ y : (lifted cov hd).outer, Path e y) (y₀ : Annulus 2) (hs : Function.Surjective p)

def deckEquiv : (FundamentalGroup X (p e.val))ᵐᵒᵖ ≃* deckGroup p :=
  CoverMonodromy.traversalEquiv (isQuotientCoveringMap_deck cov hs) e.val

def conjugator (d : deckGroup p) (j : Cell (X:=X) 2) :
    (FundamentalGroup (base hd).outer (root cov hd e))ᵐᵒᵖ :=
  difference (projectedAnchor cov hd e q y₀ (d • chosenCell hs j))
    (projectedAnchor cov hd e q y₀ (chosenCell hs j))

/-- Reindexing the genuine lifted-cell basis by monodromy gives the actual
integral basis on G×(base2-cells). -/
def coefficientIndex : (FundamentalGroup X (p e.val))ᵐᵒᵖ × Cell (X:=X) 2 ≃ LiftedCell (p:=p) 2 :=
  ((Equiv.prodCongr (deckEquiv cov hd e hs).toEquiv (Equiv.refl _)).trans
    (Equiv.prodComm _ _)).trans (cellOrbitEquiv cov hs 2).symm

def conjugateBasis : (((FundamentalGroup X (p e.val))ᵐᵒᵖ × Cell (X:=X) 2) →₀ ℤ) ≃ₗ[ℤ]
    Additive (Abelianization (toTotal cov hd e).ker) :=
  (Finsupp.domLCongr (coefficientIndex cov hd e hs)).trans (kernelBasis cov hd e q y₀)

end EilenbergGanea.CWPresentation




end

end OAI
end

section
-- module Solutions.OAIEG.RightAngledArtin_TraceWords
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
/-! Signed trace normal forms and slowly varying barycentric directions. -/

namespace TraceWords

variable {V : Type*} (L : SimpleGraph V)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)


/-! The occurrence-level normal form is now used to control an actual generator
step. No geometric normal-form or direction-vector assertion is assumed. -/

variable {L}


section RootCounts
variable [LinearOrder V]
variable (L)

variable {L}

theorem mem_predecessorRoots {s : Multiset (V × V)} {v r : V} :
    r ∈ predecessorRoots L s v ↔ ∃ p ∈ s, ¬ L.Adj p.1 v ∧ p.2 = r := by
  classical
  simp only [predecessorRoots,Multiset.mem_toFinset,Multiset.mem_map,Multiset.mem_filter]
  aesop

theorem nextRoot_mem_or_new (s : Multiset (V × V)) (v : V) :
    (∃ p ∈ s, p.2 = nextRoot L s v) ∨
      (nextRoot L s v = v ∧ ∀ p ∈ s, L.Adj p.1 v) := by
  classical
  by_cases h : (predecessorRoots L s v).Nonempty
  · left
    have hm := Finset.min'_mem (predecessorRoots L s v) h
    obtain ⟨p,hp,_,he⟩ := mem_predecessorRoots.mp hm
    exact ⟨p,hp,by simpa only [nextRoot,dite_eq_left h] using he⟩
  · refine Or.inr ⟨by simp [nextRoot,h],?_⟩
    intro p hp
    by_contra hn
    exact h ⟨p.2,mem_predecessorRoots.mpr ⟨p,hp,hn,rfl⟩⟩

theorem RootInvariant.insert {s : Multiset (V × V)} (hs : RootInvariant L s) (v : V) :
    RootInvariant L (rootInsert L s v) := by
  classical
  have hr : (nextRoot L s v,nextRoot L s v) ∈ rootInsert L s v := by
    rcases nextRoot_mem_or_new (L := L) s v with ⟨p,hp,he⟩ | ⟨he,_⟩
    · simp only [rootInsert,Multiset.mem_cons]
      right
      rw [← he]
      exact hs.1 p hp
    · simp [rootInsert,he]
  have ha : ∀ p ∈ s, nextRoot L s v ≠ p.2 → L.Adj (nextRoot L s v) p.2 := by
    intro p hp hne
    rcases nextRoot_mem_or_new (L := L) s v with ⟨q,hq,he⟩ | ⟨he,hv⟩
    · rw [← he] at hne ⊢
      exact hs.2 q hq p hp hne
    · rw [he]
      exact L.symm.symm _ _ (hv (p.2,p.2) (hs.1 p hp))
  constructor
  · intro p hp
    rcases Multiset.mem_cons.mp hp with rfl | hp
    · exact hr
    · exact Multiset.mem_cons.mpr (Or.inr (hs.1 p hp))
  · intro p hp q hq hne
    rcases Multiset.mem_cons.mp hp with rfl | hp
    · rcases Multiset.mem_cons.mp hq with rfl | hq
      · exact False.elim (hne rfl)
      · exact ha q hq hne
    · rcases Multiset.mem_cons.mp hq with rfl | hq
      · exact L.symm.symm _ _ (ha p hp hne.symm)
      · exact hs.2 p hp q hq hne

theorem RootInvariant.scan {s : Multiset (V × V)} (hs : RootInvariant L s) (w : Word V) :
    RootInvariant L (rootScan L s w) := by
  induction w generalizing s with
  | nil => exact hs
  | cons x w ih => exact ih (hs.insert x.1)

theorem rootInvariant_word (w : Word V) : RootInvariant L (rootScan L 0 w) :=
  RootInvariant.scan ⟨by simp,by simp⟩ w

variable (L)

omit [LinearOrder V] in
@[simp] theorem rootCounts_cons (p : V × V) (s : Multiset (V × V)) :
    rootCounts (p ::ₘ s) = Finsupp.single p.2 1 + rootCounts s := by
  simp [rootCounts]

omit [LinearOrder V] in
@[simp] theorem rootCounts_zero : rootCounts (0 : Multiset (V × V)) = 0 := by
  simp [rootCounts]


omit [LinearOrder V] in
 theorem rootCounts_mem_iff (s : Multiset (V × V)) (r : V) :
    rootCounts s r ≠ 0 ↔ ∃ p ∈ s, p.2 = r := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons p s ih =>
      by_cases hp : p.2 = r
      · simp [rootCounts_cons,hp]
      · simp [rootCounts_cons,hp,ih]

omit [LinearOrder V] in
 theorem rootCounts_support_clique {s : Multiset (V × V)} (hs : RootInvariant L s) :
    ((rootCounts s).support : Set V).Pairwise L.Adj := by
  intro r hr t ht hne
  obtain ⟨p,hp,hpr⟩ := (rootCounts_mem_iff s r).mp (Finsupp.mem_support_iff.mp hr)
  obtain ⟨q,hq,hqt⟩ := (rootCounts_mem_iff s t).mp (Finsupp.mem_support_iff.mp ht)
  rw [← hpr,← hqt] at hne ⊢
  exact hs.2 p hp q hq hne

theorem wordCounts_support_clique (w : Word V) : ((wordCounts L w).support : Set V).Pairwise L.Adj :=
  rootCounts_support_clique L (rootInvariant_word w)

theorem traceCounts_support_clique (t : Trace L) : ((traceCounts L t).support : Set V).Pairwise L.Adj := by
  induction t using Quotient.inductionOn with
  | h w => exact wordCounts_support_clique L w

omit [LinearOrder V] in
 theorem rootCounts_sum [Fintype V] (s : Multiset (V × V)) :
    ∑ v, rootCounts s v = s.card := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons p s ih =>
      simp [rootCounts_cons,Finset.sum_add_distrib,ih,Finsupp.single_apply,add_comm]

theorem rootScan_card (s : Multiset (V × V)) (w : Word V) :
    (rootScan L s w).card = s.card + w.length := by
  induction w generalizing s with
  | nil => simp
  | cons x w ih => simp [rootScan_cons,ih,rootInsert,add_comm,add_left_comm]

theorem wordCounts_sum [Fintype V] (w : Word V) : ∑ v, wordCounts L w v = w.length := by
  rw [wordCounts,rootCounts_sum,rootScan_card]
  simp

theorem traceCounts_sum [Fintype V] (t : Trace L) :
    ∑ v, traceCounts L t v = traceLength L t := by
  induction t using Quotient.inductionOn with
  | h w => exact wordCounts_sum L w

end RootCounts

variable (L)


section DirectionVectors
variable [Fintype V] [LinearOrder V]

/-- Barycentric direction, with value zero at the empty trace. -/
def traceDirection (t : Trace L) (v : V) : ℝ :=
  (traceCounts L t v : ℝ) / (traceLength L t : ℝ)

def artinDirection (g : ArtinGroup L) : V → ℝ :=
  traceDirection L (artinNormalTrace L g)

omit [Fintype V] in
theorem traceDirection_nonneg (t : Trace L) (v : V) : 0 ≤ traceDirection L t v :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem traceDirection_sum {t : Trace L} (ht : 0 < traceLength L t) :
    ∑ v, traceDirection L t v = 1 := by
  simp only [traceDirection,← Finset.sum_div,← Nat.cast_sum,traceCounts_sum]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt ht))

end DirectionVectors


section HeightAndExactDirections

theorem height_wordEval (w : Word V) :
    (height L (wordEval (artinGenerator L) w)).toAdd = wordHeight w := by
  induction w with
  | nil => simp [wordEval]
  | cons x w ih =>
      simp only [wordEval,List.map_cons,List.prod_cons,map_mul,
        wordHeight_cons] at *
      change (height L (letterValue (artinGenerator L) x)).toAdd +
        (height L ((w.map (letterValue (artinGenerator L))).prod)).toAdd = _
      rw [ih]
      congr 1
      cases x with
      | mk v b => cases b <;> simp [letterValue]

theorem wordHeight_abs_le (w : Word V) : |wordHeight w| ≤ (w.length : ℤ) := by
  induction w with
  | nil => simp
  | cons x w ih =>
      rw [wordHeight_cons]
      calc
        _ ≤ |(if x.2 then 1 else -1 : ℤ)| + |wordHeight w| := abs_add_le _ _
        _ = 1 + |wordHeight w| := by cases x.2 <;> norm_num
        _ ≤ ((x :: w).length : ℤ) := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; omega

theorem height_abs_le_traceLength (g : ArtinGroup L) :
    |(height L g).toAdd| ≤ (traceLength L (artinNormalTrace L g) : ℤ) := by
  obtain ⟨w,hw,rfl⟩ := exists_reduced_word L g
  rw [height_wordEval,artinNormalTrace_word,hw.normalTrace_eq]
  exact wordHeight_abs_le w

end HeightAndExactDirections

end TraceWords

end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_ArtinChains
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains CubicalChains.Reorientation
variable {V : Type*} (L : SimpleGraph V) [Fintype V] [Nonempty V] [LinearOrder V]
local instance signedLexOrder : LinearOrder (Letter V) :=
  LinearOrder.lift' (toLex : V × Bool → Lex (V × Bool)) toLex.injective

end EilenbergGanea.TraceWords.CubeDescents


end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_Descending
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology

open Classical Set Topology

namespace EilenbergGanea.DescendingCube.Data

variable {G A : Type*} [Group G] {f : A → G} (D : Data f)
variable [Fintype A] [Nonempty A]
open scoped unitInterval NNReal

def origin : D.Point where
  top := 1
  coord := fun _ => 0
  nonneg _ := le_rfl
  lt_one _ := zero_lt_one
  support _ h := False.elim (h rfl)

end EilenbergGanea.DescendingCube.Data

end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_Realization
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology

open Classical Set Topology

open Classical Set Topology

namespace EilenbergGanea.CubeRealization

section
open Metric
variable {G V : Type*} [Group G] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

variable {f comm}

omit [Group G] [Fintype V] in
theorem chartCoordinates_continuous {n : ℕ} (c : DimCell (G := G) (L := L) n) :
    Continuous (chartCoordinates c) := by
  apply continuous_pi
  intro v
  exact continuous_projIcc.comp (((continuous_apply _).add continuous_const).div_const 2)

variable (f comm)

theorem chart_continuous {n : ℕ} (c : DimCell (G := G) (L := L) n) :
    Continuous (chart f comm c) :=
  (characteristic_continuous f comm c.val).comp (chartCoordinates_continuous c)

end

open Metric
variable {G V : Type*} [Group G] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

omit [Group G] [Fintype V] in
theorem cubeCoordinatesInv_chart {n : ℕ} (c : DimCell (G := G) (L := L) n)
    {t : Fin n → ℝ} (ht : t ∈ closedBall 0 1) :
    cubeCoordinatesInv c (chartCoordinates c t) = t := by
  funext i
  simp only [cubeCoordinatesInv,chartCoordinates_disk c ht,Equiv.apply_symm_apply]
  ring

/-- Finite collection containing every closed face of a fixed cube. -/
def faceCell (c : Cell (G := G) L) (o a : Finset V) : Cell (G := G) L where
  base := c.base * product f comm (c.directions ∩ o) (c.clique.mono Finset.inter_subset_left)
  directions := c.directions ∩ a
  clique := c.clique.mono Finset.inter_subset_left

def faces (c : Cell (G := G) L) : Finset (Cell (G := G) L) :=
  Finset.univ.image (fun p : Finset V × Finset V => faceCell f comm c p.1 p.2)

def dimFaces (c : Cell (G := G) L) (m : ℕ) : Finset (DimCell (G := G) (L := L) m) :=
  (faces f comm c).subtype (fun d => d.directions.card = m)

theorem pointCell_characteristic_mem_faces (c : Cell (G := G) L) (x : Coordinates c) :
    pointCell (characteristic f comm c x) ∈ faces f comm c := by
  apply Finset.mem_image.mpr
  refine ⟨(ones c x,active (characteristic f comm c x)),Finset.mem_univ _,?_⟩
  apply Cell.ext
  · simp only [faceCell,Finset.inter_eq_right.mpr (ones_subset c x)]
    rfl
  · simp only [faceCell,Finset.inter_eq_right.mpr (active_characteristic_subset L f comm c x)]
    rfl

/-- Every point on a characteristic sphere lies in a strictly lower open cube. -/
theorem boundary_dimension_lt {n : ℕ} (c : DimCell (G := G) (L := L) n)
    {t : Fin n → ℝ} (ht : t ∈ sphere 0 1) :
    (pointCell (chart f comm c t)).directions.card < n := by
  let x := chartCoordinates c t
  have hs := active_characteristic_subset L f comm c.val x
  by_contra h
  change ¬ (active (characteristic f comm c.val x)).card < n at h
  have he : active (characteristic f comm c.val x) = c.val.directions :=
    Finset.eq_of_subset_of_card_le hs (by simpa only [c.property] using le_of_not_gt h)
  have hx : ∀ v : c.val.directions, (x v : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    intro v
    have hv : normalizedCoord c.val x v ≠ 0 := by
      have hv' : v.val ∈ active (characteristic f comm c.val x) := he.symm ▸ v.property
      exact (mem_active _ _).mp hv'
    rw [normalizedCoord_mem] at hv
    have hne : (x v : ℝ) ≠ 1 := by
      intro hh
      exact hv (by simp only [hh,ite_true])
    rw [ite_eq_right hne] at hv
    exact ⟨lt_of_le_of_ne (x v).property.1 (Ne.symm hv),
      lt_of_le_of_ne (x v).property.2 hne⟩
  have hi := cubeCoordinatesInv_open c x hx
  rw [show x = chartCoordinates c t from rfl,
    cubeCoordinatesInv_chart c (mem_closedBall.mpr (mem_sphere.mp ht).le)] at hi
  exact (ne_of_lt (mem_ball.mp hi)) (mem_sphere.mp ht)

theorem chart_mapsTo (n : ℕ) (c : DimCell (G := G) (L := L) n) :
    ∃ I : Π m, Finset (DimCell (G := G) (L := L) m),
      MapsTo (chart f comm c) (sphere 0 1)
        (⋃ (m < n) (j ∈ I m), chart f comm j '' closedBall 0 1) := by
  refine ⟨dimFaces f comm c.val,?_⟩
  intro t ht
  let p := chart f comm c t
  let d : DimCell (G := G) (L := L) (pointCell p).directions.card := ⟨pointCell p,rfl⟩
  have hd : d ∈ dimFaces f comm c.val _ := by
    rw [dimFaces,Finset.mem_subtype]
    exact pointCell_characteristic_mem_faces f comm c.val (chartCoordinates c t)
  refine Set.mem_iUnion.mpr ⟨_,Set.mem_iUnion.mpr ⟨boundary_dimension_lt f comm c ht,
    Set.mem_iUnion.mpr ⟨d,Set.mem_iUnion.mpr ⟨hd,?_⟩⟩⟩⟩
  rw [chart_image_disk]
  exact ⟨pointCoordinates p,characteristic_point f comm p⟩

end EilenbergGanea.CubeRealization

namespace EilenbergGanea.CubeRealization

section
open CubeInterpolation
variable {G V : Type*} [Group G] [Fintype V]
variable (L : SimpleGraph V) (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

def cliqueProduct (s : CliqueIndex L) : G := product f comm s.val s.property

def vertexStar (b : G) : Set (Point (G := G) L f comm) :=
  {p | interpolation L f comm p (fun a => if a = b then 1 else 0) ≠ 0}

/-- Every point with prescribed initial vertex belongs to some closed positive
cube at that vertex. -/
def cliqueCell (b : G) (s : CliqueIndex L) : Cell (G := G) L := ⟨b,s.val,s.property⟩

end

variable {G V : Type*} [Group G] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

instance pointContinuousConstSMul : ContinuousConstSMul G (Point (G := G) L f comm) where
  continuous_const_smul g := by
    apply (evaluation_quotient f comm).continuous_iff.mpr
    apply continuous_sigma
    intro c
    change Continuous (fun x : Coordinates c => g • characteristic f comm c x)
    simp only [smul_characteristic]
    change Continuous (characteristic f comm (translateCell g c))
    exact characteristic_continuous f comm (translateCell g c)

instance pointIsCancelSMul : IsCancelSMul G (Point (G := G) L f comm) where
  left_cancel' g p q he := by
    apply Point.ext
    · exact mul_left_cancel (congrArg Point.base he)
    · simpa only [smul_coord] using congrArg (fun r : Point (G := G) L f comm => r.coord) he
  right_cancel' g h p he := mul_right_cancel (congrArg Point.base he)

variable (h : G →* Multiplicative ℤ) (hf : ∀ v, (h (f v)).toAdd = 1)
variable (exponent : V → G →* Multiplicative ℝ)
variable (hexponent : ∀ v w, (exponent v (f w)).toAdd = if v = w then 1 else 0)

instance subgroupContinuousConstSMul (H : Subgroup G) :
    ContinuousConstSMul H (Point (G := G) L f comm) where
  continuous_const_smul g := show Continuous (fun p : Point (G := G) L f comm => (g : G) • p) from
    continuous_const_smul (g : G)

end EilenbergGanea.CubeRealization

end

end OAI
end

section
-- module Solutions.OAIEG.CubicalCover
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology
open scoped Quaternion

open Classical Topology

open Classical Set Topology

namespace EilenbergGanea.CubeRealization

section
open Metric
variable {G V : Type*} [Group G] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

theorem chartInverse_continuousOn_of_t2 [T2Space (Point (G := G) L f comm)]
    {n : ℕ} (c : DimCell (G := G) (L := L) n) :
    ContinuousOn (chart f comm c).symm (chart f comm c).target := by
  apply CompactChart.continuousOn_symm (chart f comm c) (closedBall 0 1)
    (isCompact_closedBall _ _) ball_subset_closedBall (chart_continuous f comm c).continuousOn
  intro t ht he
  change pointCell (chart f comm c t) = c.val at he
  change t ∈ ball 0 1
  by_contra hn
  have hs : t ∈ sphere 0 1 := mem_sphere.mpr
    (le_antisymm (mem_closedBall.mp ht) (le_of_not_gt hn))
  have hd := boundary_dimension_lt f comm c hs
  rw [he,c.property] at hd
  exact (lt_irrefl _) hd

/-- The ordinary CW structure follows from the genuine normalized-cube gluing;
only Hausdorffness and compact characteristic disks are used. -/
@[instance_reducible] def cwComplexOfT2 [T2Space (Point (G := G) L f comm)] : CWComplex (univ : Set (Point (G := G) L f comm)) where
  cell := DimCell (G := G) (L := L)
  map := fun _ c => chart f comm c
  source_eq := fun _ _ => rfl
  continuousOn := fun _ c => (chart_continuous f comm c).continuousOn
  continuousOn_symm := fun _ c => chartInverse_continuousOn_of_t2 f comm c
  pairwiseDisjoint' := by
    intro a _ b _ hab
    change Disjoint (chart f comm a.2 '' ball 0 1) (chart f comm b.2 '' ball 0 1)
    rw [chart_image_ball,chart_image_ball]
    apply Set.disjoint_left.mpr
    intro p ha hb
    apply hab
    have he : a.2.val = b.2.val := ha.symm.trans hb
    have hn : a.1 = b.1 := a.2.property.symm.trans ((congrArg (fun c => c.directions.card) he).trans b.2.property)
    cases a with | mk n a =>
      cases b with | mk m b =>
        dsimp at hn
        subst m
        exact congrArg (Sigma.mk n) (Subtype.ext he)
  mapsTo' := chart_mapsTo f comm
  closed' := by
    intro A _ hA
    apply (evaluation_quotient f comm).isClosed_preimage.mp
    rw [isClosed_sigma_iff]
    intro c
    let d : DimCell (G := G) (L := L) c.directions.card := ⟨c,rfl⟩
    have hh := (hA _ d).preimage (characteristic_continuous f comm c)
    rw [chart_image_disk] at hh
    change IsClosed (characteristic f comm c ⁻¹' (A ∩ Set.range (characteristic f comm c))) at hh
    change IsClosed (characteristic f comm c ⁻¹' A)
    simpa only [Set.preimage_inter,Set.preimage_range,Set.inter_univ] using hh
  union' := by
    apply Set.eq_univ_of_forall
    intro p
    let d : DimCell (G := G) (L := L) (pointCell p).directions.card := ⟨pointCell p,rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨_,Set.mem_iUnion.mpr ⟨d,?_⟩⟩
    rw [chart_image_disk]
    exact ⟨pointCoordinates p,characteristic_point f comm p⟩

end

variable {G Q V : Type*} [Group G] [Group Q] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))
variable (q : G →* Q)

/-- Applying a group homomorphism only to the initial vertices of cubes. -/
def mapPoint (p : Point (G := G) L f comm) : Point (G := Q) L (q ∘ f) (mappedComm f comm q) where
  base := q p.base
  coord := p.coord
  nonneg := p.nonneg
  lt_one := p.lt_one
  clique := p.clique

def mapCell (c : Cell (G := G) L) : Cell (G := Q) L where
  base := q c.base
  directions := c.directions
  clique := c.clique

omit [Fintype V] in
@[simp] theorem mapPoint_base (p : Point (G := G) L f comm) :
    (mapPoint f comm q p).base = q p.base := rfl

omit [Fintype V] in
@[simp] theorem mapPoint_coord (p : Point (G := G) L f comm) :
    (mapPoint f comm q p).coord = p.coord := rfl

omit [Fintype V] in
@[simp] theorem mapPoint_characteristic (c : Cell (G := G) L) (x : Coordinates c) :
    mapPoint f comm q (characteristic f comm c x) =
      characteristic (q ∘ f) (mappedComm f comm q) (mapCell q c) x := by
  apply Point.ext
  · change q (c.base * product f comm (ones c x) _) =
      q c.base * product (q ∘ f) (mappedComm f comm q) (ones c x) _
    rw [map_mul]
    congr 1
    exact Finset.map_noncommProd _ _ _ q
  · rfl

theorem mapPoint_continuous : Continuous (mapPoint f comm q) := by
  apply (evaluation_quotient f comm).continuous_iff.mpr
  apply continuous_sigma
  intro c
  change Continuous (fun x => mapPoint f comm q (characteristic f comm c x))
  simp only [mapPoint_characteristic]
  exact characteristic_continuous (q ∘ f) (mappedComm f comm q) (mapCell q c)

omit [Fintype V] in
theorem mapCell_surjective (hq : Function.Surjective q) : Function.Surjective (mapCell (L := L) q) := by
  rintro ⟨a,s,hs⟩
  obtain ⟨g,rfl⟩ := hq a
  exact ⟨⟨g,s,hs⟩,rfl⟩

omit [Fintype V] in
theorem mapPoint_surjective (hq : Function.Surjective q) : Function.Surjective (mapPoint f comm q) := by
  rintro ⟨a,x,hx,ht,hc⟩
  obtain ⟨g,rfl⟩ := hq a
  exact ⟨⟨g,x,hx,ht,hc⟩,rfl⟩

/-- The base-label quotient is a genuine topological quotient for the weak
cubical topologies, proved by lifting each actual characteristic disk. -/
theorem mapPoint_quotient (hq : Function.Surjective q) : IsQuotientMap (mapPoint f comm q) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨mapPoint_surjective f comm q hq,?_⟩
  intro A
  constructor
  · exact fun hA => hA.preimage (mapPoint_continuous f comm q)
  · intro hA
    apply (evaluation_quotient (q ∘ f) (mappedComm f comm q)).isClosed_preimage.mp
    rw [isClosed_sigma_iff]
    intro c
    obtain ⟨d,rfl⟩ := mapCell_surjective q hq c
    have hh := hA.preimage (characteristic_continuous f comm d)
    change IsClosed ((fun x => mapPoint f comm q (characteristic f comm d x)) ⁻¹' A) at hh
    change IsClosed ((fun x : Coordinates d =>
      characteristic (q ∘ f) (mappedComm f comm q) (mapCell q d) x) ⁻¹' A)
    simpa only [mapPoint_characteristic] using hh

omit [Fintype V] in
/-- The literal group-kernel orbits are exactly the fibers of the cube map. -/
theorem mapPoint_eq_iff_orbit (p r : Point (G := G) L f comm) :
    mapPoint f comm q p = mapPoint f comm q r ↔ p ∈ MulAction.orbit q.ker r := by
  constructor
  · intro he
    have hb : q p.base = q r.base := congrArg Point.base he
    have hx : p.coord = r.coord := congrArg (fun z : Point (G := Q) L (q ∘ f)
      (mappedComm f comm q) => z.coord) he
    let g : q.ker := ⟨p.base * r.base⁻¹,by simp only [MonoidHom.mem_ker,map_mul,map_inv,hb,mul_inv_cancel]⟩
    refine ⟨g,?_⟩
    apply Point.ext
    · change (p.base * r.base⁻¹) * r.base = p.base
      simp [mul_assoc]
    · exact hx.symm
  · rintro ⟨g,rfl⟩
    apply Point.ext
    · change q ((g : G) * r.base) = q r.base
      rw [map_mul,g.property,one_mul]
    · rfl

/-- The quotient homeomorphism respects the actual weak topologies. -/
def kernelQuotientHomeomorph (hq : Function.Surjective q) :
    Quotient (MulAction.orbitRel q.ker (Point (G := G) L f comm)) ≃ₜ
      Point (G := Q) L (q ∘ f) (mappedComm f comm q) :=
  (Homeomorph.Quotient.congrRight (fun p r => (mapPoint_eq_iff_orbit f comm q p r).symm)).trans
    (Topology.IsQuotientMap.homeomorph (f := ⟨mapPoint f comm q,mapPoint_continuous f comm q⟩)
      (mapPoint_quotient f comm q hq))

end EilenbergGanea.CubeRealization

end

end OAI
end

section
-- module Solutions.OAIEG.IntegralModules
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

/-! Group-ring augmentation and literal two-syzygy dimension criterion. -/

namespace EilenbergGanea
section ChainPackaging
variable {Γ S T : Type} [Group Γ]

/-- Reindex the actual integral edge chains as a free left group-ring module. -/
def chainPackaging : BasedChains Γ S ≃ₗ[ℤ] S →₀ IntegralGroupRing Γ :=
  ((Finsupp.domLCongr (Equiv.prodComm Γ S)).trans (Finsupp.curryLinearEquiv ℤ)).trans
    (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℤ).symm)

@[simp] theorem chainPackaging_single (g : Γ) (s : S) (n : ℤ) :
    chainPackaging (Finsupp.single (g,s) n) =
      Finsupp.single s (MonoidAlgebra.single g n) := by
  simp [chainPackaging, Finsupp.curry_single]

@[simp] theorem chainPackaging_symm_single (g : Γ) (s : S) (n : ℤ) :
    (chainPackaging (Γ := Γ) (S := S)).symm
        (Finsupp.single s (MonoidAlgebra.single g n)) = Finsupp.single (g,s) n := by
  apply (chainPackaging (Γ := Γ) (S := S)).injective
  simp

theorem chainPackaging_translate (g : Γ) (c : BasedChains Γ S) :
    chainPackaging (translateChains g c) =
      (MonoidAlgebra.single g 1 : IntegralGroupRing Γ) • chainPackaging c := by
  have he : (chainPackaging (Γ := Γ) (S := S)).toLinearMap.comp (translateChains g) =
      (DistribSMul.toLinearMap ℤ (S →₀ IntegralGroupRing Γ) (MonoidAlgebra.single g 1 : IntegralGroupRing Γ)).comp
        (chainPackaging (Γ := Γ) (S := S)).toLinearMap := by
    apply Finsupp.lhom_ext
    rintro ⟨h,s⟩ n
    simp [Finsupp.smul_single, MonoidAlgebra.single_mul_single]
  exact LinearMap.congr_fun he c

theorem chainPackaging_symm_translate (g : Γ) (c : S →₀ IntegralGroupRing Γ) :
    (chainPackaging (Γ := Γ) (S := S)).symm ((MonoidAlgebra.single g 1 : IntegralGroupRing Γ) • c) =
      translateChains g (chainPackaging.symm c) := by
  apply (chainPackaging (Γ := Γ) (S := S)).injective
  rw [chainPackaging_translate, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Equivariance on integral chains is exactly full group-ring linearity. -/
def chainRingMap (A : BasedChains Γ S →ₗ[ℤ] BasedChains Γ T)
    (hA : ChainsEquivariant A) :
    (S →₀ IntegralGroupRing Γ) →ₗ[IntegralGroupRing Γ] T →₀ IntegralGroupRing Γ where
  toFun c := chainPackaging (A (chainPackaging.symm c))
  map_add' _ _ := by simp only [map_add]
  map_smul' r c := by
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp only [zero_smul, map_zero]
    | add r t hr ht => simp only [add_smul, map_add, hr, ht]
    | single g n =>
        have hn : (MonoidAlgebra.single g n : IntegralGroupRing Γ) =
            n • MonoidAlgebra.single g 1 := by simp
        rw [hn]
        simp only [smul_assoc, map_smul, chainPackaging_symm_translate, RingHom.id_apply]
        rw [hA g _, chainPackaging_translate]

@[simp] theorem chainRingMap_apply (A : BasedChains Γ S →ₗ[ℤ] BasedChains Γ T)
    (hA : ChainsEquivariant A) (c : S →₀ IntegralGroupRing Γ) :
    chainRingMap A hA c = chainPackaging (A (chainPackaging.symm c)) := rfl

end ChainPackaging


end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.LevelTransport
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
namespace LevelTransport
open TraceWords AffineTransport

variable {V : Type*} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
variable (hdim : ∀ s : Finset V, (s : Set V).Pairwise L.Adj → s.card ≤ 3)

def point (g : ArtinGroup L) (hg : 0 < traceLength L (artinNormalTrace L g)) : TrianglePoint V :=
  ⟨artinDirection L g,by
    apply mem_triangleSet.mpr
    refine ⟨(traceCounts L (artinNormalTrace L g)).support,
      hdim _ (traceCounts_support_clique L _),⟨?_,?_⟩,?_⟩
    · exact traceDirection_nonneg L _
    · exact traceDirection_sum L hg
    · intro v hv
      simp only [Finsupp.notMem_support_iff] at hv
      simp [artinDirection,traceDirection,hv]⟩

@[simp] theorem point_val (g : ArtinGroup L) (hg : 0 < traceLength L (artinNormalTrace L g)) :
    (point L hdim g hg : V → ℝ) = artinDirection L g := rfl


/-- The integral level downstairs; the action is by left multiplication by the height kernel. -/
abbrev NegativeLevel (N : ℕ) := {g : ArtinGroup L // (height L g).toAdd = -(N : ℤ)}

omit [Fintype V] [LinearOrder V] in
theorem negative_level_length (N : ℕ) {g : ArtinGroup L}
    (hg : (height L g).toAdd = -(N : ℤ)) :
    N ≤ traceLength L (artinNormalTrace L g) := by
  have hh := height_abs_le_traceLength L g
  rw [hg,abs_neg,abs_of_nonneg (Nat.cast_nonneg N)] at hh
  exact_mod_cast hh

def levelPoint (N : ℕ) (hN : 0 < N) (g : NegativeLevel L N) : TrianglePoint V :=
  point L hdim g (lt_of_lt_of_le hN (negative_level_length L N g.property))

@[simp] theorem levelPoint_val (N : ℕ) (hN : 0 < N) (g : NegativeLevel L N) :
    (levelPoint L hdim N hN g : V → ℝ) = artinDirection L g := rfl

def upperVertex (N : ℕ) (hN : 1 < N) (g : NegativeLevel L N) (v : V) :
    NegativeLevel L (N-1) :=
  ⟨(g : ArtinGroup L) * artinGenerator L v,by
    rw [map_mul,height_generator]
    change (height L (g : ArtinGroup L)).toAdd + 1 = _
    rw [g.property]
    omega⟩

def edgeVertex (N : ℕ) (g : NegativeLevel L N) (q r : V) : NegativeLevel L N :=
  ⟨(g : ArtinGroup L) * artinGenerator L q * (artinGenerator L r)⁻¹,by
    simp only [map_mul,map_inv,height_generator]
    change (height L (g : ArtinGroup L)).toAdd + 1 + -1 = _
    rw [g.property]
    omega⟩

variable (h : V → V → SU2) (Q : V → ℍ)

def edgeLabel (N : ℕ) (hN : 1 < N) (g : NegativeLevel L N) (q r : V) : SU2 :=
  edgeTransport h Q (levelPoint L hdim N (by omega) g)
    (levelPoint L hdim (N-1) (by omega) (upperVertex L N hN g q))
    (levelPoint L hdim N (by omega) (edgeVertex L N g q r))


/-- A vertex of the simplex is also an honest point of its two-skeleton. -/
def vertexPoint (v : V) : TrianglePoint V :=
  ⟨fun w => if v = w then 1 else 0,by
    apply mem_triangleSet.mpr
    refine ⟨{v},by simp,⟨?_,?_⟩,?_⟩
    · intro w; dsimp only; split_ifs <;> norm_num
    · simp
    · intro w hw
      simp only [Finset.mem_singleton] at hw
      simp [Ne.symm hw]⟩

@[simp] theorem vertexPoint_val (v w : V) :
    (vertexPoint v : V → ℝ) w = if v = w then 1 else 0 := rfl

def powerVertex (N : ℕ) (q r : V) (j : ℕ) : NegativeLevel L N :=
  ⟨(artinGenerator L q)⁻¹ ^ (N - min j N) * (artinGenerator L r)⁻¹ ^ min j N,by
    simp only [map_mul,map_pow,map_inv,height_generator]
    change (N-min j N : ℕ) • (-1 : ℤ) + (min j N : ℕ) • (-1 : ℤ) = _
    simp only [nsmul_eq_mul,mul_neg,mul_one]
    have hh : min j N ≤ N := min_le_right _ _
    omega⟩


/-- Directed walks retain the chosen generator pair, including parallel edges. -/
inductive Walk (N : ℕ) : NegativeLevel L N → NegativeLevel L N → Type _
  | nil (g : NegativeLevel L N) : Walk N g g
  | cons {g k : NegativeLevel L N} (q r : V) (hqr : L.Adj q r)
      (p : Walk N (edgeVertex L N g q r) k) : Walk N g k

namespace Walk
variable {L} {N : ℕ}

def append {g k l : NegativeLevel L N} : Walk L N g k → Walk L N k l → Walk L N g l
  | .nil _, p => p
  | .cons q r hqr p, t => .cons q r hqr (append p t)

def cast {g k g' k' : NegativeLevel L N} (p : Walk L N g k)
    (hg : g = g') (hk : k = k') : Walk L N g' k' := hg ▸ hk ▸ p

end Walk

def walkProduct (N : ℕ) (hN : 1 < N) {g k : NegativeLevel L N} : Walk L N g k → SU2
  | .nil _ => 1
  | .cons (g := g) q r _ p => edgeLabel L hdim h Q N hN g q r * walkProduct N hN p

@[simp] theorem walkProduct_nil (N : ℕ) (hN : 1 < N) (g : NegativeLevel L N) :
    walkProduct L hdim h Q N hN (.nil g) = 1 := rfl

@[simp] theorem walkProduct_cons (N : ℕ) (hN : 1 < N) {g k : NegativeLevel L N}
    (q r : V) (hqr : L.Adj q r) (p : Walk L N (edgeVertex L N g q r) k) :
    walkProduct L hdim h Q N hN (.cons q r hqr p) =
      edgeLabel L hdim h Q N hN g q r * walkProduct L hdim h Q N hN p := rfl

@[simp] theorem walkProduct_append (N : ℕ) (hN : 1 < N) {g k l : NegativeLevel L N}
    (p : Walk L N g k) (t : Walk L N k l) :
    walkProduct L hdim h Q N hN (p.append t) =
      walkProduct L hdim h Q N hN p * walkProduct L hdim h Q N hN t := by
  induction p with
  | nil => simp [Walk.append]
  | cons q r hqr p ih => simp [Walk.append,ih,mul_assoc]

@[simp] theorem walkProduct_cast (N : ℕ) (hN : 1 < N) {g k g' k' : NegativeLevel L N}
    (p : Walk L N g k) (hg : g = g') (hk : k = k') :
    walkProduct L hdim h Q N hN (p.cast hg hk) = walkProduct L hdim h Q N hN p := by
  subst g'; subst k'; rfl

def pureVertex (N : ℕ) (q : V) : NegativeLevel L N :=
  ⟨(artinGenerator L q)⁻¹ ^ N,by
    simp only [map_pow,map_inv,height_generator]
    change N • (-1 : ℤ) = -(N : ℤ)
    simp⟩

def vertexGauge (v : V) : SU2 := gauge h Q v (vertexPoint v)

omit [Fintype V] [LinearOrder V] in
def graphWalkProduct {a b : V} : L.Walk a b → SU2
  | .nil => 1
  | .cons (u := u) (v := v) _ p => h u v * graphWalkProduct p


namespace Walk
variable {L} {N : ℕ}
omit [Fintype V] [LinearOrder V] in
def eval (a : NegativeLevel L N → V → V → SU2)
    {g k : NegativeLevel L N} : Walk L N g k → SU2
  | .nil _ => 1
  | .cons (g := g) q r _ p => a g q r * eval a p
end Walk

end LevelTransport

end EilenbergGanea



end

end OAI
end

section
-- module Solutions.OAIEG.LevelBasis
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.LevelExact CubicalChains.HeightFiltration
variable {G A : Type} [Group G] [LinearOrder A]
variable (L : SimpleGraph A) (φ : G →* Multiplicative ℤ) (v : A → G) (root : A)
@[simp] theorem ht_mul (g q : G) : ht φ (g*q) = ht φ g + ht φ q := by simp [ht]
@[simp] theorem ht_one : ht φ 1 = 0 := by simp [ht]
@[simp] theorem ht_inv (g : G) : ht φ g⁻¹ = -ht φ g := by simp [ht]
@[simp] theorem ht_zpow (g : G) (n : ℤ) : ht φ (g^n) = n * ht φ g := by simp [ht]
@[simp] theorem ht_ker (g : φ.ker) : ht φ g = 0 := by simp [ht,MonoidHom.mem_ker.mp g.property]
variable (hv : ∀ a, φ (v a) = Multiplicative.ofAdd (1 : ℤ))
include hv in
omit [LinearOrder A] in
@[simp] theorem ht_generator (a : A) : ht φ (v a) = 1 := by simp [ht,hv]
include hv in
omit [LinearOrder A] in
theorem ht_step (g : G) (a : A) : ht φ (g * v a) = ht φ g + 1 := by simp [ht_generator φ v hv]

def Shape (k : ℕ) := {p : List A × ℤ // SimplicialChains.Valid L p.1 ∧ p.1.length = k ∧
  p.2 < 0 ∧ 0 < p.2 + (k : ℤ)}
def basisIndex (k : ℕ) (p : φ.ker × Shape L k) : G × List A :=
  (p.1.val * (v (p.2.val.1.headD root)) ^ p.2.val.2,p.2.val.1)

include hv in
theorem basisIndex_height (k : ℕ) (p : φ.ker × Shape L k) :
    ht φ (basisIndex L φ v root k p).1 = p.2.val.2 := by
  simp only [basisIndex,ht_mul,ht_ker,ht_zpow,ht_generator φ v hv,mul_one,zero_add]

include hv in
theorem basisIndex_injective (k : ℕ) : Function.Injective (basisIndex L φ v root k) := by
  intro p q he
  have hw : p.2.val.1 = q.2.val.1 := congrArg Prod.snd he
  have hh := congrArg (fun x => ht φ x.1) he
  rw [basisIndex_height L φ v root hv,basisIndex_height L φ v root hv] at hh
  have hs : p.2 = q.2 := Subtype.ext (Prod.ext hw hh)
  have hg := congrArg Prod.fst he
  simp only [basisIndex,hs] at hg
  exact Prod.ext (Subtype.ext (mul_right_cancel hg)) hs

include hv in
theorem basisIndex_mem (k : ℕ) (p : φ.ker × Shape L k) :
    SimplicialChains.Valid L (basisIndex L φ v root k p).2 ∧
      (basisIndex L φ v root k p).2.length = k ∧
      ht φ (basisIndex L φ v root k p).1 < 0 ∧
      0 < ht φ (basisIndex L φ v root k p).1 + (k : ℤ) := by
  rw [basisIndex_height L φ v root hv]
  exact p.2.property

include hv in
theorem exists_basisIndex {k : ℕ} (p : G × List A)
    (hp : SimplicialChains.Valid L p.2 ∧ p.2.length = k ∧ ht φ p.1 < 0 ∧ 0 < ht φ p.1 + (k : ℤ)) :
    ∃ q : φ.ker × Shape L k, basisIndex L φ v root k q = p := by
  let s : Shape L k := ⟨(p.2,ht φ p.1),hp⟩
  let g : φ.ker := ⟨p.1 * (v (p.2.headD root)) ^ (-ht φ p.1),by
    apply (Multiplicative.toAdd.injective)
    change ht φ (p.1 * (v (p.2.headD root)) ^ (-ht φ p.1)) = 0
    simp only [ht_mul,ht_zpow,ht_generator φ v hv,mul_one,add_neg_cancel]⟩
  refine ⟨(g,s),?_⟩
  apply Prod.ext
  · change (p.1 * (v (p.2.headD root)) ^ (-ht φ p.1)) * (v (p.2.headD root)) ^ (ht φ p.1) = p.1
    rw [mul_assoc,← zpow_add,neg_add_cancel,zpow_zero,mul_one]
  · rfl

def includeBasis (k : ℕ) : (φ.ker × Shape L k →₀ ℤ) →ₗ[ℤ] CubicalChains.Chains G A :=
  Finsupp.lmapDomain ℤ ℤ (basisIndex L φ v root k)
@[simp] theorem includeBasis_single (k : ℕ) (p : φ.ker × Shape L k) (n : ℤ) :
    includeBasis L φ v root k (Finsupp.single p n) = Finsupp.single (basisIndex L φ v root k p) n := by
  simp [includeBasis]
include hv in
theorem includeBasis_injective (k : ℕ) : Function.Injective (includeBasis L φ v root k) :=
  Finsupp.mapDomain_injective (basisIndex_injective L φ v root hv k)

include hv in
theorem includeBasis_range (k : ℕ) : LinearMap.range (includeBasis L φ v root k) = crossing L (ht φ) k := by
  rw [includeBasis,Finsupp.range_lmapDomain,crossing,Finsupp.supported_eq_span_single]
  congr 1
  ext c
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨basisIndex L φ v root k p,basisIndex_mem L φ v root hv k p,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨q,rfl⟩ := exists_basisIndex L φ v root hv p hp
    exact ⟨q,rfl⟩

variable (comm : ∀ a b, L.Adj a b → Commute (v a) (v b))
include hv in
def projectBasis (k : ℕ) : CubicalChains.Chains G A →ₗ[ℤ] (φ.ker × Shape L k →₀ ℤ) :=
  Finsupp.lcomapDomain (basisIndex L φ v root k) (basisIndex_injective L φ v root hv k)

@[simp] theorem project_include (k : ℕ) (c : φ.ker × Shape L k →₀ ℤ) :
    projectBasis L φ v root hv k (includeBasis L φ v root k c) = c :=
  Finsupp.leftInverse_lcomapDomain_mapDomain _ _ c

include hv in
theorem include_project {k : ℕ} {c : CubicalChains.Chains G A} (hc : c ∈ crossing L (ht φ) k) :
    includeBasis L φ v root k (projectBasis L φ v root hv k c) = c := by
  rw [← includeBasis_range L φ v root hv k] at hc
  obtain ⟨d,rfl⟩ := hc
  rw [project_include]

include hv in
theorem includeBasis_mem (k : ℕ) (c : φ.ker × Shape L k →₀ ℤ) :
    includeBasis L φ v root k c ∈ crossing L (ht φ) k := by
  rw [← includeBasis_range L φ v root hv k]
  exact ⟨c,rfl⟩

def generator (s : Shape L 2) : φ.ker :=
  ⟨(v (s.val.1.headD root))⁻¹ * v (s.val.1.tail.headD root),by simp [hv]⟩

def includeVertices : (φ.ker →₀ ℤ) →ₗ[ℤ] CubicalChains.Chains G A :=
  Finsupp.lmapDomain ℤ ℤ (fun g => (g.val,[]))
omit [LinearOrder A] in
@[simp] theorem includeVertices_single (g : φ.ker) (n : ℤ) :
    includeVertices (A := A) φ (Finsupp.single g n) = Finsupp.single (g.val,[]) n := by simp [includeVertices]
omit [LinearOrder A] in
theorem includeVertices_injective : Function.Injective (includeVertices (A := A) φ) := by
  apply Finsupp.mapDomain_injective
  intro p q he
  exact Subtype.ext (congrArg Prod.fst he)

include hv in
omit [LinearOrder A] in
theorem boundary_square (g : G) (a b : A) (hab : Commute (v a) (v b))
    (hg : ht φ g = -1) :
    levelBoundary v (ht φ) (Finsupp.single (g,[a,b]) 1) =
      Finsupp.single (g*v b,[]) 1 - Finsupp.single (g*v a,[]) 1 := by
  have hga : ht φ (g * v a) = 0 := by rw [ht_step φ v hv,hg]; omega
  have hgb : ht φ (g * v b) = 0 := by rw [ht_step φ v hv,hg]; omega
  simp only [levelBoundary_apply,boundary_single,one_smul,boundaryTerm_cons,boundaryTerm_nil,
    map_zero,sub_zero,map_sub,front_single,plus,select_single,hga,hgb,hg]
  norm_num
  rw [mul_assoc,hab.eq,← mul_assoc]
  abel


include hv comm in
theorem levelBoundary_include_single (p : φ.ker × Shape L 2) :
    levelBoundary v (ht φ) (includeBasis L φ v root 2 (Finsupp.single p 1)) =
      includeVertices (A := A) φ (edgeBoundary (generator L φ v root hv) (Finsupp.single p 1)) := by
  rcases p with ⟨g,⟨⟨w,n⟩,hs⟩⟩
  obtain ⟨a,b,hw⟩ := List.length_eq_two.mp hs.2.1
  change w = [a,b] at hw
  subst w
  have hn : n = -1 := by have h₁ := hs.2.2.1; have h₂ := hs.2.2.2; norm_num at h₂; omega
  subst n
  have hab : L.Adj a b := (List.pairwise_cons.mp hs.1.2).1 b (by simp)
  rw [includeBasis_single]
  change levelBoundary v (ht φ) (Finsupp.single (g.val * (v a)^(-1 : ℤ),[a,b]) 1) = _
  rw [boundary_square φ v hv _ a b (comm a b hab) (by simp [ht_generator φ v hv])]
  simp only [edgeBoundary,Finsupp.linearCombination_single]
  simp only [zpow_neg_one,one_smul,map_sub,includeVertices_single,
    Subgroup.coe_mul,generator,List.headD_cons,List.tail_cons,mul_assoc,inv_mul_cancel,mul_one]

include hv comm in
theorem levelBoundary_include (c : φ.ker × Shape L 2 →₀ ℤ) :
    levelBoundary v (ht φ) (includeBasis L φ v root 2 c) =
      includeVertices (A := A) φ (edgeBoundary (generator L φ v root hv) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single p n =>
    have he : Finsupp.single p n = n • Finsupp.single p (1 : ℤ) := by simp
    rw [he,map_smul,map_smul,map_smul,map_smul,levelBoundary_include_single L φ v root hv comm]

/-- The literal based integral boundary of the crossing three-cubes. -/
def triangleBoundary : (φ.ker × Shape L 3 →₀ ℤ) →ₗ[ℤ] (φ.ker × Shape L 2 →₀ ℤ) :=
  (projectBasis L φ v root hv 2).comp ((crossPart (ht φ)).comp ((boundary v).comp (includeBasis L φ v root 3)))

include hv in
theorem triangleBoundary_inclusion (c : φ.ker × Shape L 3 →₀ ℤ) :
    includeBasis L φ v root 2 (triangleBoundary L φ v root hv c) =
      crossPart (ht φ) (boundary v (includeBasis L φ v root 3 c)) := by
  apply include_project L φ v root hv
  exact crossPart_mem L (ht φ) (boundary_total L v (ht φ) (ht_step φ v hv)
    (crossing_total L (ht φ) (includeBasis_mem L φ v root hv 3 c)))

include hv comm in
theorem triangleBoundary_cycle (c : φ.ker × Shape L 3 →₀ ℤ) :
    triangleBoundary L φ v root hv c ∈ cycles (generator L φ v root hv) := by
  apply includeVertices_injective φ
  rw [map_zero,← levelBoundary_include L φ v root hv comm,triangleBoundary_inclusion L φ v root hv]
  exact levelBoundary_cross_boundary L v (ht φ) (ht_step φ v hv) comm (includeBasis_mem L φ v root hv 3 c)

variable (K : SimplicialChains.Contraction L)
variable (exactTotal : ∀ {k : ℕ}, 0 < k → ∀ c, c ∈ total (G := G) L k → boundary v c = 0 →
      ∃ b ∈ total (G := G) L (k+1), boundary v b = c)
variable (dim : ∀ w, SimplicialChains.Valid L w → w.length ≤ 3)
include hv comm K exactTotal in
theorem triangleBoundary_range : LinearMap.range (triangleBoundary L φ v root hv) =
    cycles (generator L φ v root hv) := by
  apply le_antisymm
  · rintro _ ⟨c,rfl⟩
    exact triangleBoundary_cycle L φ v root hv comm c
  · intro c hc
    have hz : levelBoundary v (ht φ) (includeBasis L φ v root 2 c) = 0 := by
      rw [levelBoundary_include L φ v root hv comm,LinearMap.mem_ker.mp hc,map_zero]
    obtain ⟨t,ht,hdt⟩ := level_cycle_bounds L v (ht φ) K (ht_step φ v hv) comm exactTotal
      _ (includeBasis_mem L φ v root hv 2 c) hz
    rw [← includeBasis_range L φ v root hv 3] at ht
    obtain ⟨b,rfl⟩ := ht
    refine ⟨b,includeBasis_injective L φ v root hv 2 ?_⟩
    rwa [triangleBoundary_inclusion L φ v root hv]

include hv comm K exactTotal dim in
theorem triangleBoundary_injective : Function.Injective (triangleBoundary L φ v root hv) := by
  suffices hz : ∀ c, triangleBoundary L φ v root hv c = 0 → c = 0 by
    intro c d he
    exact sub_eq_zero.mp (hz (c-d) (by simp only [map_sub,he,sub_self]))
  intro c hc
  apply includeBasis_injective L φ v root hv 3
  rw [map_zero]
  apply level_boundary_injective L v (ht φ) K (ht_step φ v hv) comm exactTotal dim
    _ (includeBasis_mem L φ v root hv 3 c)
  rw [← triangleBoundary_inclusion L φ v root hv,hc,map_zero]


/-- Left translation on the actual ambient cube chains. -/
def leftTranslate (g : G) : CubicalChains.Chains G A →ₗ[ℤ] CubicalChains.Chains G A :=
  Finsupp.lmapDomain ℤ ℤ (fun p => (g*p.1,p.2))
omit [LinearOrder A] in
@[simp] theorem leftTranslate_single (g q : G) (w : List A) (n : ℤ) :
    leftTranslate g (Finsupp.single (q,w) n) = Finsupp.single (g*q,w) n := by simp [leftTranslate]

end EilenbergGanea.LevelBasis

namespace EilenbergGanea.LevelBasis
variable {V : Type} [LinearOrder V] (L : SimpleGraph V)

def pairShape (a b : V) (hab : a < b) (hadj : L.Adj a b) : Shape L 2 :=
  ⟨([a,b],-1),by simp [SimplicialChains.Valid,hab,hadj]⟩

@[simp] theorem generator_pair (root a b : V) (hab : a < b) (hadj : L.Adj a b) :
    (generator L (height L) (artinGenerator L) root (height_generator L)
      (pairShape L a b hab hadj)).val = (artinGenerator L a)⁻¹ * artinGenerator L b := rfl

end EilenbergGanea.LevelBasis

namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.LevelExact CubicalChains.HeightFiltration
variable {G A : Type} [Group G] [LinearOrder A]
variable (L : SimpleGraph A) (φ : G →* Multiplicative ℤ) (v : A → G) (root : A)
variable (hv : ∀ a, φ (v a) = Multiplicative.ofAdd (1 : ℤ))
variable (comm : ∀ a b, L.Adj a b → Commute (v a) (v b))

instance shape_finite [Fintype A] (k : ℕ) : Finite (Shape L k) := by
  let f : Shape L k → List.Vector A k × Fin k := fun s =>
    (⟨s.val.1,s.property.2.1⟩,⟨(-s.val.2).toNat,by
      have hn := s.property.2.2.1
      have hm := s.property.2.2.2
      omega⟩)
  apply Finite.of_injective f
  intro s t h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun p : List.Vector A k × Fin k => p.1.val) h
  · have he := congrArg (fun p : List.Vector A k × Fin k => p.2.val) h
    have hs := s.property.2.2.1
    have ht := t.property.2.2.1
    dsimp [f] at he
    omega

noncomputable instance shape_fintype [Fintype A] (k : ℕ) : Fintype (Shape L k) := Fintype.ofFinite _

def edgeShape (a b : A) (hab : SimplicialChains.Valid L [a,b]) : Shape L 2 :=
  ⟨([a,b],-1),hab,rfl,by norm_num,by norm_num⟩

def triangleShape (a b c : A) (habc : SimplicialChains.Valid L [a,b,c])
    (n : ℤ) (hn : n = -1 ∨ n = -2) : Shape L 3 :=
  ⟨([a,b,c],n),habc,rfl,by omega,by norm_num; omega⟩

@[simp] theorem generator_edgeShape (a b : A) (hab : SimplicialChains.Valid L [a,b]) :
    (generator L φ v root hv (edgeShape L a b hab) : G) = (v a)⁻¹ * v b := rfl

theorem valid_triangle_edges {a b c : A} (h : SimplicialChains.Valid L [a,b,c]) :
    SimplicialChains.Valid L [a,b] ∧ SimplicialChains.Valid L [a,c] ∧
      SimplicialChains.Valid L [b,c] := by
  simp [SimplicialChains.Valid] at h ⊢
  tauto

def lowerTriangleWord (ab ac bc : Shape L 2) : FreeGroup (Shape L 2) :=
  FreeGroup.of ac * (FreeGroup.of bc)⁻¹ * (FreeGroup.of ab)⁻¹

def upperTriangleWord (ab ac bc : Shape L 2) : FreeGroup (Shape L 2) :=
  FreeGroup.of ab * (FreeGroup.of bc * FreeGroup.of ab * (FreeGroup.of ac)⁻¹) *
    (FreeGroup.of ab)⁻¹

def triangleWordList : (w : List A) → SimplicialChains.Valid L w → ℤ → FreeGroup (Shape L 2)
  | [a,b,c],h,n =>
    let e := valid_triangle_edges L h
    if n = -1 then
      lowerTriangleWord L (edgeShape L a b e.1) (edgeShape L a c e.2.1) (edgeShape L b c e.2.2)
    else upperTriangleWord L (edgeShape L a b e.1) (edgeShape L a c e.2.1) (edgeShape L b c e.2.2)
  | _,_,_ => 1

def triangleWord (s : Shape L 3) : FreeGroup (Shape L 2) :=
  triangleWordList L s.val.1 s.property.1 s.val.2

end EilenbergGanea.LevelBasis
namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.HeightFiltration
variable {G A : Type} [Group G] [LinearOrder A]
variable (L : SimpleGraph A) (φ : G →* Multiplicative ℤ) (v : A → G) (root : A)
variable (hv : ∀ a, φ (v a) = Multiplicative.ofAdd (1 : ℤ))
variable (comm : ∀ a b, L.Adj a b → Commute (v a) (v b))

variable (K : SimplicialChains.Contraction L)
variable (exactTotal : ∀ {k : ℕ}, 0 < k → ∀ c, c ∈ total (G := G) L k → boundary v c = 0 →
      ∃ b ∈ total (G := G) L (k+1), boundary v b = c)
variable (dim : ∀ w, SimplicialChains.Valid L w → w.length ≤ 3)

noncomputable def triangleBasis : (φ.ker × Shape L 3 →₀ ℤ) ≃ₗ[ℤ]
    cycles (generator L φ v root hv) :=
  LinearEquiv.ofBijective
    ((triangleBoundary L φ v root hv).codRestrict (cycles (generator L φ v root hv))
      (triangleBoundary_cycle L φ v root hv comm))
    ⟨fun c d h => triangleBoundary_injective L φ v root hv comm K exactTotal dim
      (congrArg Subtype.val h),fun c => by
        have hc : c.val ∈ LinearMap.range (triangleBoundary L φ v root hv) := by
          rw [triangleBoundary_range L φ v root hv comm K exactTotal]
          exact c.property
        obtain ⟨b,hb⟩ := hc
        exact ⟨b,Subtype.ext hb⟩⟩

end EilenbergGanea.LevelBasis
namespace EilenbergGanea.LevelBasis
open LevelTransport
variable {V : Type} [LinearOrder V] (L : SimpleGraph V) (root : V) (N : ℕ)

noncomputable def levelEquiv : (height L).ker ≃ NegativeLevel L N where
  toFun := fun g => ⟨(artinGenerator L root)⁻¹ ^ N * g.val,by
    simp only [map_mul,map_pow,map_inv,height_generator]
    rw [show height L g.val = 1 from g.property,mul_one]
    change N • (-1 : ℤ) = -(N : ℤ)
    simp⟩
  invFun := fun g => ⟨artinGenerator L root ^ N * g.val,by
    change (height L (artinGenerator L root ^ N * g.val)).toAdd = 0
    simp only [map_mul,map_pow,height_generator]
    change N • (1 : ℤ) + (height L g.val).toAdd = 0
    rw [g.property]
    simp⟩
  left_inv := fun g => Subtype.ext (by dsimp; group)
  right_inv := fun g => Subtype.ext (by dsimp; group)

def basedLabel (a : NegativeLevel L N → V → V → SU2)
    (g : (height L).ker) (s : Shape L 2) : SU2 :=
  a (levelEquiv L root N g) (s.val.1.tail.headD root) (s.val.1.headD root)

@[simp] theorem basedLabel_edge (a : NegativeLevel L N → V → V → SU2)
    (g : (height L).ker) (q r : V) (h : SimplicialChains.Valid L [q,r]) :
    basedLabel L root N a g (edgeShape L q r h) = a (levelEquiv L root N g) r q := rfl

variable (a : NegativeLevel L N → V → V → SU2)
variable (rev : ∀ g q r, a (edgeVertex L N g q r) r q = (a g q r)⁻¹)

def orientedWord (q r : V) (h : L.Adj q r) : FreeGroup (Shape L 2) :=
  if hlt : q < r then
    (FreeGroup.of (edgeShape L q r (by simpa [SimplicialChains.Valid] using And.intro hlt h)))⁻¹
  else
    FreeGroup.of (edgeShape L r q (by
      have hlt' : r < q := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm (L.ne_of_adj h))
      simpa [SimplicialChains.Valid] using And.intro hlt' h.symm))

variable (tri : ∀ g₀ g₁ g₂ q₀ r₀ q₁ r₁ q₂ r₂,
    edgeVertex L N g₀ q₀ r₀ = g₁ → edgeVertex L N g₁ q₁ r₁ = g₂ →
      edgeVertex L N g₂ q₂ r₂ = g₀ → a g₀ q₀ r₀ * a g₁ q₁ r₁ * a g₂ q₂ r₂ = 1)


variable {L N}
def walkWord {g k : NegativeLevel L N} : Walk L N g k → FreeGroup (Shape L 2)
  | .nil _ => 1
  | .cons q r h p => orientedWord L q r h * walkWord p

end EilenbergGanea.LevelBasis


end

end OAI
end

section
-- module Solutions.OAIEG.SeedContraction
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

def h0CodeData : List (ℕ) := [h0CodeData_0,h0CodeData_1,h0CodeData_2,h0CodeData_3,h0CodeData_4,h0CodeData_5,h0CodeData_6].flatten

def h0Coeff (v : Fin 103) (e : Fin 372) : ℤ :=
  (((h0CodeData.getD v.val 0 >>> (2*e.val)) % 4 : ℕ) : ℤ) - 1

theorem d1_h0_cert_0 : ∀ v : Fin 103,
    rowEval (d1Row 0) (h0Coeff v) =
      (if 0 = v then 1 else 0) - (if 0 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_1 : ∀ v : Fin 103,
    rowEval (d1Row 1) (h0Coeff v) =
      (if 1 = v then 1 else 0) - (if 1 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_2 : ∀ v : Fin 103,
    rowEval (d1Row 2) (h0Coeff v) =
      (if 2 = v then 1 else 0) - (if 2 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_3 : ∀ v : Fin 103,
    rowEval (d1Row 3) (h0Coeff v) =
      (if 3 = v then 1 else 0) - (if 3 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_4 : ∀ v : Fin 103,
    rowEval (d1Row 4) (h0Coeff v) =
      (if 4 = v then 1 else 0) - (if 4 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_5 : ∀ v : Fin 103,
    rowEval (d1Row 5) (h0Coeff v) =
      (if 5 = v then 1 else 0) - (if 5 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_6 : ∀ v : Fin 103,
    rowEval (d1Row 6) (h0Coeff v) =
      (if 6 = v then 1 else 0) - (if 6 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_10 : ∀ v : Fin 103,
    rowEval (d1Row 10) (h0Coeff v) =
      (if 10 = v then 1 else 0) - (if 10 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_11 : ∀ v : Fin 103,
    rowEval (d1Row 11) (h0Coeff v) =
      (if 11 = v then 1 else 0) - (if 11 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_12 : ∀ v : Fin 103,
    rowEval (d1Row 12) (h0Coeff v) =
      (if 12 = v then 1 else 0) - (if 12 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_13 : ∀ v : Fin 103,
    rowEval (d1Row 13) (h0Coeff v) =
      (if 13 = v then 1 else 0) - (if 13 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_14 : ∀ v : Fin 103,
    rowEval (d1Row 14) (h0Coeff v) =
      (if 14 = v then 1 else 0) - (if 14 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_15 : ∀ v : Fin 103,
    rowEval (d1Row 15) (h0Coeff v) =
      (if 15 = v then 1 else 0) - (if 15 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_16 : ∀ v : Fin 103,
    rowEval (d1Row 16) (h0Coeff v) =
      (if 16 = v then 1 else 0) - (if 16 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_17 : ∀ v : Fin 103,
    rowEval (d1Row 17) (h0Coeff v) =
      (if 17 = v then 1 else 0) - (if 17 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_18 : ∀ v : Fin 103,
    rowEval (d1Row 18) (h0Coeff v) =
      (if 18 = v then 1 else 0) - (if 18 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_19 : ∀ v : Fin 103,
    rowEval (d1Row 19) (h0Coeff v) =
      (if 19 = v then 1 else 0) - (if 19 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_20 : ∀ v : Fin 103,
    rowEval (d1Row 20) (h0Coeff v) =
      (if 20 = v then 1 else 0) - (if 20 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_21 : ∀ v : Fin 103,
    rowEval (d1Row 21) (h0Coeff v) =
      (if 21 = v then 1 else 0) - (if 21 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_22 : ∀ v : Fin 103,
    rowEval (d1Row 22) (h0Coeff v) =
      (if 22 = v then 1 else 0) - (if 22 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_23 : ∀ v : Fin 103,
    rowEval (d1Row 23) (h0Coeff v) =
      (if 23 = v then 1 else 0) - (if 23 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_24 : ∀ v : Fin 103,
    rowEval (d1Row 24) (h0Coeff v) =
      (if 24 = v then 1 else 0) - (if 24 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_25 : ∀ v : Fin 103,
    rowEval (d1Row 25) (h0Coeff v) =
      (if 25 = v then 1 else 0) - (if 25 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_26 : ∀ v : Fin 103,
    rowEval (d1Row 26) (h0Coeff v) =
      (if 26 = v then 1 else 0) - (if 26 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_27 : ∀ v : Fin 103,
    rowEval (d1Row 27) (h0Coeff v) =
      (if 27 = v then 1 else 0) - (if 27 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_28 : ∀ v : Fin 103,
    rowEval (d1Row 28) (h0Coeff v) =
      (if 28 = v then 1 else 0) - (if 28 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_29 : ∀ v : Fin 103,
    rowEval (d1Row 29) (h0Coeff v) =
      (if 29 = v then 1 else 0) - (if 29 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_30 : ∀ v : Fin 103,
    rowEval (d1Row 30) (h0Coeff v) =
      (if 30 = v then 1 else 0) - (if 30 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_31 : ∀ v : Fin 103,
    rowEval (d1Row 31) (h0Coeff v) =
      (if 31 = v then 1 else 0) - (if 31 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_32 : ∀ v : Fin 103,
    rowEval (d1Row 32) (h0Coeff v) =
      (if 32 = v then 1 else 0) - (if 32 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_33 : ∀ v : Fin 103,
    rowEval (d1Row 33) (h0Coeff v) =
      (if 33 = v then 1 else 0) - (if 33 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_34 : ∀ v : Fin 103,
    rowEval (d1Row 34) (h0Coeff v) =
      (if 34 = v then 1 else 0) - (if 34 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_35 : ∀ v : Fin 103,
    rowEval (d1Row 35) (h0Coeff v) =
      (if 35 = v then 1 else 0) - (if 35 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_36 : ∀ v : Fin 103,
    rowEval (d1Row 36) (h0Coeff v) =
      (if 36 = v then 1 else 0) - (if 36 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_37 : ∀ v : Fin 103,
    rowEval (d1Row 37) (h0Coeff v) =
      (if 37 = v then 1 else 0) - (if 37 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_38 : ∀ v : Fin 103,
    rowEval (d1Row 38) (h0Coeff v) =
      (if 38 = v then 1 else 0) - (if 38 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_39 : ∀ v : Fin 103,
    rowEval (d1Row 39) (h0Coeff v) =
      (if 39 = v then 1 else 0) - (if 39 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_40 : ∀ v : Fin 103,
    rowEval (d1Row 40) (h0Coeff v) =
      (if 40 = v then 1 else 0) - (if 40 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_41 : ∀ v : Fin 103,
    rowEval (d1Row 41) (h0Coeff v) =
      (if 41 = v then 1 else 0) - (if 41 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_42 : ∀ v : Fin 103,
    rowEval (d1Row 42) (h0Coeff v) =
      (if 42 = v then 1 else 0) - (if 42 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_43 : ∀ v : Fin 103,
    rowEval (d1Row 43) (h0Coeff v) =
      (if 43 = v then 1 else 0) - (if 43 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_44 : ∀ v : Fin 103,
    rowEval (d1Row 44) (h0Coeff v) =
      (if 44 = v then 1 else 0) - (if 44 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_45 : ∀ v : Fin 103,
    rowEval (d1Row 45) (h0Coeff v) =
      (if 45 = v then 1 else 0) - (if 45 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_46 : ∀ v : Fin 103,
    rowEval (d1Row 46) (h0Coeff v) =
      (if 46 = v then 1 else 0) - (if 46 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_47 : ∀ v : Fin 103,
    rowEval (d1Row 47) (h0Coeff v) =
      (if 47 = v then 1 else 0) - (if 47 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_48 : ∀ v : Fin 103,
    rowEval (d1Row 48) (h0Coeff v) =
      (if 48 = v then 1 else 0) - (if 48 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_49 : ∀ v : Fin 103,
    rowEval (d1Row 49) (h0Coeff v) =
      (if 49 = v then 1 else 0) - (if 49 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_50 : ∀ v : Fin 103,
    rowEval (d1Row 50) (h0Coeff v) =
      (if 50 = v then 1 else 0) - (if 50 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_51 : ∀ v : Fin 103,
    rowEval (d1Row 51) (h0Coeff v) =
      (if 51 = v then 1 else 0) - (if 51 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_52 : ∀ v : Fin 103,
    rowEval (d1Row 52) (h0Coeff v) =
      (if 52 = v then 1 else 0) - (if 52 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_53 : ∀ v : Fin 103,
    rowEval (d1Row 53) (h0Coeff v) =
      (if 53 = v then 1 else 0) - (if 53 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_54 : ∀ v : Fin 103,
    rowEval (d1Row 54) (h0Coeff v) =
      (if 54 = v then 1 else 0) - (if 54 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_55 : ∀ v : Fin 103,
    rowEval (d1Row 55) (h0Coeff v) =
      (if 55 = v then 1 else 0) - (if 55 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_56 : ∀ v : Fin 103,
    rowEval (d1Row 56) (h0Coeff v) =
      (if 56 = v then 1 else 0) - (if 56 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_57 : ∀ v : Fin 103,
    rowEval (d1Row 57) (h0Coeff v) =
      (if 57 = v then 1 else 0) - (if 57 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_58 : ∀ v : Fin 103,
    rowEval (d1Row 58) (h0Coeff v) =
      (if 58 = v then 1 else 0) - (if 58 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_59 : ∀ v : Fin 103,
    rowEval (d1Row 59) (h0Coeff v) =
      (if 59 = v then 1 else 0) - (if 59 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_60 : ∀ v : Fin 103,
    rowEval (d1Row 60) (h0Coeff v) =
      (if 60 = v then 1 else 0) - (if 60 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_61 : ∀ v : Fin 103,
    rowEval (d1Row 61) (h0Coeff v) =
      (if 61 = v then 1 else 0) - (if 61 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_62 : ∀ v : Fin 103,
    rowEval (d1Row 62) (h0Coeff v) =
      (if 62 = v then 1 else 0) - (if 62 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_63 : ∀ v : Fin 103,
    rowEval (d1Row 63) (h0Coeff v) =
      (if 63 = v then 1 else 0) - (if 63 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_64 : ∀ v : Fin 103,
    rowEval (d1Row 64) (h0Coeff v) =
      (if 64 = v then 1 else 0) - (if 64 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_65 : ∀ v : Fin 103,
    rowEval (d1Row 65) (h0Coeff v) =
      (if 65 = v then 1 else 0) - (if 65 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_66 : ∀ v : Fin 103,
    rowEval (d1Row 66) (h0Coeff v) =
      (if 66 = v then 1 else 0) - (if 66 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_67 : ∀ v : Fin 103,
    rowEval (d1Row 67) (h0Coeff v) =
      (if 67 = v then 1 else 0) - (if 67 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_100 : ∀ v : Fin 103,
    rowEval (d1Row 100) (h0Coeff v) =
      (if 100 = v then 1 else 0) - (if 100 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_101 : ∀ v : Fin 103,
    rowEval (d1Row 101) (h0Coeff v) =
      (if 101 = v then 1 else 0) - (if 101 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_102 : ∀ v : Fin 103,
    rowEval (d1Row 102) (h0Coeff v) =
      (if 102 = v then 1 else 0) - (if 102 = 0 then 1 else 0) := by decide +kernel

noncomputable def h₀ := FiniteIntegralContraction.matrixMap h0Coeff

end EilenbergGanea.SeedChainCertificate


end

end OAI
end


