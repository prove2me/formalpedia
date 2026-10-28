-- Prove2me | Definitions.Def_OAIQ4Kq000
-- name    : OAIQ4Kq000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T08:30:08.424855+00:00
-- url     : https://prove2.me/theorems/284a6cf0-58f4-4631-88c9-02c2be2001c8
-- title:
--   Definitions bundle OAIQ4Kq000 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kaplansky.kaplansky_quasitrace_counterexample`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 294 declarations of OpenAI's Lean: 139 definitions, 5 inductive types or structures, 17 instances and 133 theorems. The definitions and types are `Convexity.StdSimplex.equivIcc`, `Convexity.StdSimplex.subBarycenter`, `Convexity.StdSimplex.topologicalSpaceInduced`, `OAI.Kaplansky.ActualHilbert`, `OAI.Kaplansky.ActualTestFiber`, `OAI.Kaplansky.ActualTestIndex`, `OAI.Kaplansky.BoundedProduct`, `OAI.Kaplansky.BundleWordValue`, `OAI.Kaplansky.BundleWordValue.lower`, `OAI.Kaplansky.BundleWordValue.raise`, `OAI.Kaplansky.ComplexGrassmann.Components`, `OAI.Kaplansky.ComplexGrassmann.GraphAmbient`, `OAI.Kaplansky.ComplexGrassmann.GraphFrame`, `OAI.Kaplansky.ComplexGrassmann.GraphHorizontal`, `OAI.Kaplansky.ComplexGrassmann.GraphMap`, `OAI.Kaplansky.ComplexGrassmann.GraphSlope`, `OAI.Kaplansky.ComplexGrassmann.GraphVertical`, `OAI.Kaplansky.ComplexGrassmann.Grassmann`, `OAI.Kaplansky.ComplexGrassmann.InGraphChart`, `OAI.Kaplansky.ComplexGrassmann.IndependentFrame`, `OAI.Kaplansky.ComplexGrassmann.PlaneFrameMap`, `OAI.Kaplansky.ComplexGrassmann.ProjectiveProduct`, `OAI.Kaplansky.ComplexGrassmann.SmoothLineSumBundle`, `OAI.Kaplansky.ComplexGrassmann.columnFrame`, `OAI.Kaplansky.ComplexGrassmann.frameBottom`, `OAI.Kaplansky.ComplexGrassmann.framePoint`, `OAI.Kaplansky.ComplexGrassmann.frameSlope`, `OAI.Kaplansky.ComplexGrassmann.frameTop`, `OAI.Kaplansky.ComplexGrassmann.graphBottom`, `OAI.Kaplansky.ComplexGrassmann.graphCoordinate`, `OAI.Kaplansky.ComplexGrassmann.graphInclusion`, `OAI.Kaplansky.ComplexGrassmann.graphLineProjection`, `OAI.Kaplansky.ComplexGrassmann.graphLineVector`, `OAI.Kaplansky.ComplexGrassmann.graphPartialEquiv`, `OAI.Kaplansky.ComplexGrassmann.graphPlane`, `OAI.Kaplansky.ComplexGrassmann.graphPlaneEquiv`, `OAI.Kaplansky.ComplexGrassmann.graphPoint`, `OAI.Kaplansky.ComplexGrassmann.graphProjection`, `OAI.Kaplansky.ComplexGrassmann.graphTop`, `OAI.Kaplansky.ComplexGrassmann.graphTransition` and 104 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: `BundleTests_Assembly`, `BundleTests_Base`, `BundleTests_Bundles`, `BundleTests_Multiplicities`, `BundleTests_Normalized`, `BundleTests_Sequence`, `BundleTests_Smooth`, `BundleTests_Twisted`, `ComplexBundle_Coordinates`, `ComplexBundle_CoordinatesMetric`, `ComplexBundle_DirectSum`, `ComplexBundle_Frames`, `ComplexBundle_Grassmann`, `ComplexBundle_GrassmannManifold`, `ComplexBundle_Hom`, `ComplexBundle_LineStage`, `ComplexBundle_Maps`, `ComplexBundle_Projection`, `ComplexBundle_ProjectionBundle`, `ComplexBundle_Projective`, `ComplexBundle_Pullback`, `ComplexBundle_RealModel`, `ComplexBundle_SmoothLine`, `ComplexBundle_Tuples`, `Kaplansky_BundleWords`, `Kaplansky_Products`, `Kaplansky_Shift`, `Kaplansky_ShiftAlgebra`, `Kaplansky_TestAlgebra`, `Kaplansky_Words`, `MatrixScaling_Continuous`, `MatrixScaling_Expansion`, `MatrixScaling_Spectrum`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ4Kq005`, `OAIQ4Kq006`, `OAIQ4Kq007` and `OAIQ4Kq008`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ4_Kq.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Grassmann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Graph charts and atlas of the complex Grassmannian. -/

section
open scoped BigOperators
namespace Kaplansky.ComplexGrassmann

abbrev GraphHorizontal (s : ℕ) := Fin s → ℂ
abbrev GraphVertical (k : ℕ) := Fin k → ℂ
abbrev GraphAmbient (s k : ℕ) := GraphHorizontal s × GraphVertical k
abbrev GraphMap (s k : ℕ) := GraphHorizontal s →ₗ[ℂ] GraphVertical k
abbrev Components (s k : ℕ) := Fin (s+k) → ℂ
abbrev GraphFrame (s k : ℕ) := Components s k ≃ₗ[ℂ] GraphAmbient s k

/-- Actual complex s-planes in complex dimension s+k. -/
def Grassmann (s k : ℕ) := {P : Submodule ℂ (Components s k) // Module.finrank ℂ P=s}

variable {s k : ℕ}

/-- The usual graph chart, transported by an arbitrary linear splitting. -/
def graphPlane (F : (GraphFrame s k)) (A : (GraphMap s k)) : Submodule ℂ (Components s k) :=
  A.graph.comap F.toLinearMap

@[simp] theorem mem_graphPlane (F : (GraphFrame s k)) (A : (GraphMap s k)) (z : (Components s k)) :
    z ∈ graphPlane F A ↔ (F z).2=A (F z).1 := Iff.rfl

def graphPlaneEquiv (F : (GraphFrame s k)) (A : (GraphMap s k)) : (GraphHorizontal s) ≃ₗ[ℂ] graphPlane F A where
  toFun v := ⟨F.symm (v,A v),by simp⟩
  invFun z := (F z.val).1
  left_inv v := by simp
  right_inv z := by
    apply Subtype.ext
    apply F.injective
    change F (F.symm ((F z.val).1,A (F z.val).1))=F z.val
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext rfl z.property.symm
  map_add' v w := by
    apply Subtype.ext
    change F.symm (v+w,A (v+w))=F.symm (v,A v)+F.symm (w,A w)
    rw [map_add]
    exact F.symm.map_add (v,A v) (w,A w)
  map_smul' c v := by
    apply Subtype.ext
    change F.symm (c • v,A (c • v))=c • F.symm (v,A v)
    rw [map_smul]
    exact F.symm.map_smul c (v,A v)

theorem graphPlane_finrank (F : (GraphFrame s k)) (A : (GraphMap s k)) : Module.finrank ℂ (graphPlane F A)=s := by
  rw [← (graphPlaneEquiv F A).finrank_eq]
  simp

def graphPoint (F : (GraphFrame s k)) (A : (GraphMap s k)) : (Grassmann s k) := ⟨graphPlane F A,graphPlane_finrank F A⟩

theorem graphPlane_injective (F : (GraphFrame s k)) : Function.Injective (graphPlane F) := by
  intro A B h
  apply LinearMap.ext
  intro v
  have hz : F.symm (v,A v) ∈ graphPlane F B := by
    rw [← h]
    simp
  simpa using hz

/-- A plane is in a splitting's graph domain exactly when its projection to
the horizontal factor is bijective. This is independent of its chosen basis. -/
def InGraphChart (F : (GraphFrame s k)) (P : Submodule ℂ (Components s k)) : Prop :=
  Function.Bijective (fun z : P => (F z.val).1)

theorem graphPlane_inChart (F : (GraphFrame s k)) (A : (GraphMap s k)) : InGraphChart F (graphPlane F A) :=
  (graphPlaneEquiv F A).symm.bijective

def graphProjection (F : (GraphFrame s k)) (P : Submodule ℂ (Components s k)) : P →ₗ[ℂ] (GraphHorizontal s) :=
  (LinearMap.fst ℂ (GraphHorizontal s) (GraphVertical k)).comp (F.toLinearMap.comp P.subtype)

def graphCoordinate (F : (GraphFrame s k)) (P : Submodule ℂ (Components s k)) (h : InGraphChart F P) : (GraphMap s k) :=
  (LinearMap.snd ℂ (GraphHorizontal s) (GraphVertical k)).comp (F.toLinearMap.comp
    (P.subtype.comp (LinearEquiv.ofBijective (graphProjection F P) h).symm.toLinearMap))

theorem graphCoordinate_plane (F : (GraphFrame s k)) (P : Submodule ℂ (Components s k)) (h : InGraphChart F P) :
    graphPlane F (graphCoordinate F P h)=P := by
  let e := LinearEquiv.ofBijective (graphProjection F P) h
  have he (z : P) : e z=(F z.val).1 := rfl
  have hi (v : (GraphHorizontal s)) : (F (e.symm v).val).1=v := e.apply_symm_apply v
  ext z
  constructor
  · intro hz
    have hzz : z=(e.symm (F z).1).val := by
      apply F.injective
      exact Prod.ext (hi _).symm hz
    rw [hzz]
    exact (e.symm _).property
  · intro hz
    change (F z).2=(F (e.symm (F z).1).val).2
    have hh : e.symm (F z).1=⟨z,hz⟩ := e.symm_apply_apply ⟨z,hz⟩
    rw [hh]

/-- Every actual s-plane is the center of a graph chart. -/
theorem graph_charts_cover (P : Submodule ℂ (Components s k)) (hP : Module.finrank ℂ P=s) :
    ∃ F : (GraphFrame s k), graphPlane F 0=P := by
  obtain ⟨Q,hQ⟩ := P.exists_isCompl
  have hsum := Submodule.finrank_add_eq_of_isCompl hQ
  have hV : Module.finrank ℂ (Components s k)=s+k := by simp [Components]
  have hq : Module.finrank ℂ Q=k := by omega
  obtain ⟨ep⟩ := (FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq (R := ℂ)
    (M := (GraphHorizontal s)) (M' := P)).mpr (by simp [hP])
  obtain ⟨eq⟩ := (FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq (R := ℂ)
    (M := (GraphVertical k)) (M' := Q)).mpr (by simp [hq])
  let e : (GraphAmbient s k) ≃ₗ[ℂ] (Components s k) :=
    (ep.prodCongr eq).trans (P.prodEquivOfIsCompl Q hQ)
  refine ⟨e.symm,?_⟩
  ext z
  constructor
  · intro hz
    have hv : (e.symm z).2=0 := hz
    have he : z=e ((e.symm z).1,0) := by
      rw [← hv]
      exact (e.apply_symm_apply z).symm
    rw [he]
    change ((ep (e.symm z).1 : P) : (Components s k))+((eq 0 : Q) : (Components s k)) ∈ P
    simp
  · intro hz
    have he : e (ep.symm ⟨z,hz⟩,0)=z := by simp [e,Submodule.coe_prodEquivOfIsCompl']
    have hi := congrArg e.symm he
    simp only [LinearEquiv.symm_apply_apply] at hi
    change (e.symm z).2=0
    exact (congrArg Prod.snd hi).symm

end Kaplansky.ComplexGrassmann

end

section
open scoped ContDiff
namespace Kaplansky.ComplexGrassmann
variable {s k : ℕ}

abbrev GraphSlope (s k : ℕ) := (GraphHorizontal s) →L[ℂ] (GraphVertical k)

def graphInclusion (A : (GraphSlope s k)) : (GraphHorizontal s) →L[ℂ] (GraphAmbient s k) :=
  ContinuousLinearMap.inl ℂ (GraphHorizontal s) (GraphVertical k)+
    (ContinuousLinearMap.inr ℂ (GraphHorizontal s) (GraphVertical k)).comp A

@[simp] theorem graphInclusion_apply (A : (GraphSlope s k)) (v : (GraphHorizontal s)) : graphInclusion A v=(v,A v) := by
  simp [graphInclusion]

def graphTransport (F G : (GraphFrame s k)) : (GraphAmbient s k) →L[ℂ] (GraphAmbient s k) :=
  (F.symm.trans G).toContinuousLinearEquiv.toContinuousLinearMap

def graphTop (F G : (GraphFrame s k)) (A : (GraphSlope s k)) : (GraphHorizontal s) →L[ℂ] (GraphHorizontal s) :=
  (ContinuousLinearMap.fst ℂ (GraphHorizontal s) (GraphVertical k)).comp ((graphTransport F G).comp (graphInclusion A))

def graphBottom (F G : (GraphFrame s k)) (A : (GraphSlope s k)) : (GraphSlope s k) :=
  (ContinuousLinearMap.snd ℂ (GraphHorizontal s) (GraphVertical k)).comp ((graphTransport F G).comp (graphInclusion A))

@[simp] theorem graphTop_apply (F G : (GraphFrame s k)) (A : (GraphSlope s k)) (v : (GraphHorizontal s)) :
    graphTop F G A v=(G (F.symm (v,A v))).1 := by simp [graphTop,graphTransport]

@[simp] theorem graphBottom_apply (F G : (GraphFrame s k)) (A : (GraphSlope s k)) (v : (GraphHorizontal s)) :
    graphBottom F G A v=(G (F.symm (v,A v))).2 := by simp [graphBottom,graphTransport]

/-- The exact change of graph slope: bottom block times inverse top block. -/
def graphTransition (F G : (GraphFrame s k)) (A : (GraphSlope s k)) : (GraphSlope s k) :=
  (graphBottom F G A).comp (Ring.inverse (graphTop F G A))

theorem graphTop_contDiff (F G : (GraphFrame s k)) : ContDiff ℂ ∞ (graphTop F G) := by
  exact contDiff_const.clm_comp (contDiff_const.clm_comp
    (contDiff_const.add (contDiff_const.clm_comp contDiff_id)))

theorem graphBottom_contDiff (F G : (GraphFrame s k)) : ContDiff ℂ ∞ (graphBottom F G) := by
  exact contDiff_const.clm_comp (contDiff_const.clm_comp
    (contDiff_const.add (contDiff_const.clm_comp contDiff_id)))

theorem graphOverlap_open (F G : (GraphFrame s k)) : IsOpen {A : (GraphSlope s k) | IsUnit (graphTop F G A)} :=
  Units.isOpen.preimage (graphTop_contDiff F G).continuous

theorem graphTransition_contDiffAt (F G : (GraphFrame s k)) (A : (GraphSlope s k)) (hA : IsUnit (graphTop F G A)) :
    ContDiffAt ℂ ∞ (graphTransition F G) A := by
  obtain ⟨u,hu⟩ := hA
  have hinv : ContDiffAt ℂ ∞ Ring.inverse (graphTop F G A) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℂ u
  exact (graphBottom_contDiff F G).contDiffAt.clm_comp (hinv.comp A (graphTop_contDiff F G).contDiffAt)

theorem graphTop_inverse_apply (F G : (GraphFrame s k)) (A : (GraphSlope s k))
    (hA : IsUnit (graphTop F G A)) (v : (GraphHorizontal s)) :
    graphTop F G A (Ring.inverse (graphTop F G A) v)=v := by
  have h := congrArg (fun L : (GraphHorizontal s) →L[ℂ] (GraphHorizontal s) => L v)
    (Ring.mul_inverse_cancel (graphTop F G A) hA)
  exact h

theorem graphTop_inverse_apply' (F G : (GraphFrame s k)) (A : (GraphSlope s k))
    (hA : IsUnit (graphTop F G A)) (v : (GraphHorizontal s)) :
    Ring.inverse (graphTop F G A) (graphTop F G A v)=v := by
  have h := congrArg (fun L : (GraphHorizontal s) →L[ℂ] (GraphHorizontal s) => L v)
    (Ring.inverse_mul_cancel (graphTop F G A) hA)
  exact h

/-- On overlap, the rational transition describes the identical actual plane. -/
theorem graphTransition_plane (F G : (GraphFrame s k)) (A : (GraphSlope s k)) (hA : IsUnit (graphTop F G A)) :
    graphPlane G (graphTransition F G A).toLinearMap=graphPlane F A.toLinearMap := by
  ext z
  constructor
  · intro hz
    let v := Ring.inverse (graphTop F G A) (G z).1
    have htop : (G (F.symm (v,A v))).1=(G z).1 := by
      simpa only [graphTop_apply] using graphTop_inverse_apply F G A hA (G z).1
    have hbottom : (G z).2=(G (F.symm (v,A v))).2 := by
      change (G z).2=graphBottom F G A v at hz
      simpa only [graphBottom_apply] using hz
    have he : z=F.symm (v,A v) := G.injective (Prod.ext htop.symm hbottom)
    rw [he]
    simp
  · intro hz
    have he : F.symm ((F z).1,A (F z).1)=z := by
      apply F.injective
      rw [LinearEquiv.apply_symm_apply]
      exact Prod.ext rfl hz.symm
    have htop : graphTop F G A (F z).1=(G z).1 := by rw [graphTop_apply,he]
    change (G z).2=graphBottom F G A (Ring.inverse (graphTop F G A) (G z).1)
    rw [← htop,graphTop_inverse_apply' F G A hA,graphBottom_apply,he]

theorem inGraphChart_iff_unit (F G : (GraphFrame s k)) (A : (GraphSlope s k)) :
    InGraphChart G (graphPlane F A.toLinearMap) ↔ IsUnit (graphTop F G A) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  let e := graphPlaneEquiv F A.toLinearMap
  have he : (fun v : (GraphHorizontal s) => (G (e v).val).1)=graphTop F G A := by
    funext v
    simp [graphTop_apply,e,graphPlaneEquiv]
  constructor
  · intro h
    rw [← he]
    exact h.comp e.bijective
  · intro h
    rw [← he] at h
    have hh := h.comp e.symm.bijective
    change Function.Bijective (fun z : graphPlane F A.toLinearMap => (G z.val).1)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    change (G z.val).1=(G (e (e.symm z)).val).1
    rw [e.apply_symm_apply]

end Kaplansky.ComplexGrassmann

end

open scoped ContDiff
open Set
namespace Kaplansky.ComplexGrassmann
variable {s k : ℕ}

def slopePoint (F : (GraphFrame s k)) (A : (GraphSlope s k)) : (Grassmann s k) := graphPoint F A.toLinearMap

theorem slopePoint_injective (F : (GraphFrame s k)) : Function.Injective (slopePoint F) := by
  intro A B h
  have he := graphPlane_injective F (congrArg Subtype.val h)
  exact ContinuousLinearMap.coe_injective he

def slopeCoordinate (F : (GraphFrame s k)) (P : (Grassmann s k)) : (GraphSlope s k) := by
  classical
  exact if h : InGraphChart F P.val then (graphCoordinate F P.val h).toContinuousLinearMap else 0

theorem slopePoint_coordinate (F : (GraphFrame s k)) (P : (Grassmann s k)) (h : InGraphChart F P.val) :
    slopePoint F (slopeCoordinate F P)=P := by
  apply Subtype.ext
  simp only [slopeCoordinate,dite_eq_left h,slopePoint,graphPoint]
  exact graphCoordinate_plane F P.val h

theorem slopeCoordinate_point (F : (GraphFrame s k)) (A : (GraphSlope s k)) :
    slopeCoordinate F (slopePoint F A)=A := by
  apply slopePoint_injective F
  exact slopePoint_coordinate F _ (graphPlane_inChart F A.toLinearMap)

/-- The (Grassmann s k) topology is specified by its full graph atlas on actual
subspaces. The following theorems verify that these maps are open charts. -/
instance grassmannTopology : TopologicalSpace (Grassmann s k) where
  IsOpen U := ∀ F : (GraphFrame s k), IsOpen (slopePoint F ⁻¹' U)
  isOpen_univ := by intro F; simp
  isOpen_inter := by intro s t hs ht F; exact (hs F).inter (ht F)
  isOpen_sUnion := by
    intro S hS F
    rw [sUnion_eq_biUnion,preimage_iUnion]
    apply isOpen_iUnion
    intro s
    rw [preimage_iUnion]
    exact isOpen_iUnion (fun hs => hS s hs F)

theorem slopePoint_continuous (F : (GraphFrame s k)) : Continuous (slopePoint F) := by
  apply continuous_def.mpr
  intro s hs
  exact hs F

theorem slopePoint_image_preimage (F G : (GraphFrame s k)) (U : Set (GraphSlope s k)) :
    slopePoint G ⁻¹' (slopePoint F '' U)=
      {A : (GraphSlope s k) | IsUnit (graphTop G F A)} ∩ graphTransition G F ⁻¹' U := by
  ext A
  constructor
  · rintro ⟨B,hB,he⟩
    have hp : graphPlane F B.toLinearMap=graphPlane G A.toLinearMap := congrArg Subtype.val he
    have hc : InGraphChart F (graphPlane G A.toLinearMap) := by
      rw [← hp]
      exact graphPlane_inChart F B.toLinearMap
    have hu := (inGraphChart_iff_unit G F A).mp hc
    have ht : graphTransition G F A=B := by
      apply slopePoint_injective F
      apply Subtype.ext
      exact (graphTransition_plane G F A hu).trans hp.symm
    refine ⟨hu,?_⟩
    change graphTransition G F A ∈ U
    rw [ht]
    exact hB
  · rintro ⟨hu,hU⟩
    refine ⟨graphTransition G F A,hU,?_⟩
    apply Subtype.ext
    exact graphTransition_plane G F A hu

theorem slopePoint_isOpenMap (F : (GraphFrame s k)) : IsOpenMap (slopePoint F) := by
  intro U hU G
  rw [slopePoint_image_preimage]
  have hc : ContinuousOn (graphTransition G F) {A | IsUnit (graphTop G F A)} :=
    fun A hA => (graphTransition_contDiffAt G F A hA).continuousAt.continuousWithinAt
  exact hc.isOpen_inter_preimage (graphOverlap_open G F) hU

def graphPartialEquiv (F : (GraphFrame s k)) : PartialEquiv (GraphSlope s k) (Grassmann s k) where
  toFun := slopePoint F
  invFun := slopeCoordinate F
  source := univ
  target := {P | InGraphChart F P.val}
  map_source' A _ := graphPlane_inChart F A.toLinearMap
  map_target' _ _ := mem_univ _
  left_inv' A _ := slopeCoordinate_point F A
  right_inv' P h := slopePoint_coordinate F P h

/-- A genuine open chart, with all s*k complex graph coordinates as its target. -/
def grassmannChart (F : (GraphFrame s k)) : OpenPartialHomeomorph (Grassmann s k) (GraphSlope s k) :=
  (OpenPartialHomeomorph.ofContinuousOpen (graphPartialEquiv F)
    (slopePoint_continuous F).continuousOn (slopePoint_isOpenMap F) isOpen_univ).symm

@[simp] theorem grassmannChart_source (F : (GraphFrame s k)) :
    (grassmannChart F).source={P | InGraphChart F P.val} := rfl

@[simp] theorem grassmannChart_target (F : (GraphFrame s k)) : (grassmannChart F).target=univ := rfl

@[simp] theorem grassmannChart_apply (F : (GraphFrame s k)) (P : (Grassmann s k)) :
    grassmannChart F P=slopeCoordinate F P := rfl

@[simp] theorem grassmannChart_symm_apply (F : (GraphFrame s k)) (A : (GraphSlope s k)) :
    (grassmannChart F).symm A=slopePoint F A := rfl

theorem grassmann_atlas_covers (P : (Grassmann s k)) : ∃ F : (GraphFrame s k), P ∈ (grassmannChart F).source := by
  obtain ⟨F,hF⟩ := graph_charts_cover P.val P.property
  refine ⟨F,?_⟩
  change InGraphChart F P.val
  rw [← hF]
  exact graphPlane_inChart F 0

end Kaplansky.ComplexGrassmann

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_GrassmannManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Grassmannian frames, smooth manifold structure, and countability. -/

section
open scoped ContDiff
open Filter Topology
namespace Kaplansky.ComplexGrassmann
variable {s k : ℕ}

abbrev PlaneFrameMap (s k : ℕ) := (GraphHorizontal s) →L[ℂ] (Components s k)
abbrev IndependentFrame (s k : ℕ) := {B : (PlaneFrameMap s k) // Function.Injective B}

def framePoint (B : (IndependentFrame s k)) : (Grassmann s k) :=
  ⟨LinearMap.range B.val.toLinearMap,by
    rw [LinearMap.finrank_range_of_inj B.property]
    simp⟩

def frameTop (F : (GraphFrame s k)) (B : (PlaneFrameMap s k)) : (GraphHorizontal s) →L[ℂ] (GraphHorizontal s) :=
  (ContinuousLinearMap.fst ℂ (GraphHorizontal s) (GraphVertical k)).comp
    (F.toContinuousLinearEquiv.toContinuousLinearMap.comp B)

def frameBottom (F : (GraphFrame s k)) (B : (PlaneFrameMap s k)) : (GraphSlope s k) :=
  (ContinuousLinearMap.snd ℂ (GraphHorizontal s) (GraphVertical k)).comp
    (F.toContinuousLinearEquiv.toContinuousLinearMap.comp B)

def frameSlope (F : (GraphFrame s k)) (B : (PlaneFrameMap s k)) : (GraphSlope s k) :=
  (frameBottom F B).comp (Ring.inverse (frameTop F B))

@[simp] theorem frameTop_apply (F : (GraphFrame s k)) (B : (PlaneFrameMap s k)) (v : (GraphHorizontal s)) :
    frameTop F B v=(F (B v)).1 := rfl

@[simp] theorem frameBottom_apply (F : (GraphFrame s k)) (B : (PlaneFrameMap s k)) (v : (GraphHorizontal s)) :
    frameBottom F B v=(F (B v)).2 := rfl

theorem frameTop_contDiff (F : (GraphFrame s k)) : ContDiff ℂ ∞ (frameTop F) :=
  contDiff_const.clm_comp (contDiff_const.clm_comp contDiff_id)

theorem frameSlope_contDiffAt (F : (GraphFrame s k)) (B : (PlaneFrameMap s k)) (hB : IsUnit (frameTop F B)) :
    ContDiffAt ℂ ∞ (frameSlope F) B := by
  obtain ⟨u,hu⟩ := hB
  have hb : ContDiff ℂ ∞ (frameBottom F) :=
    contDiff_const.clm_comp (contDiff_const.clm_comp contDiff_id)
  have hi : ContDiffAt ℂ ∞ Ring.inverse (frameTop F B) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℂ u
  exact hb.contDiffAt.clm_comp (hi.comp B (frameTop_contDiff F).contDiffAt)

theorem frameSlope_plane (F : (GraphFrame s k)) (B : (PlaneFrameMap s k)) (hB : IsUnit (frameTop F B)) :
    graphPlane F (frameSlope F B).toLinearMap=LinearMap.range B.toLinearMap := by
  have hleft (v : (GraphHorizontal s)) : Ring.inverse (frameTop F B) (frameTop F B v)=v :=
    congrArg (fun L : (GraphHorizontal s) →L[ℂ] (GraphHorizontal s) => L v) (Ring.inverse_mul_cancel _ hB)
  have hright (v : (GraphHorizontal s)) : frameTop F B (Ring.inverse (frameTop F B) v)=v :=
    congrArg (fun L : (GraphHorizontal s) →L[ℂ] (GraphHorizontal s) => L v) (Ring.mul_inverse_cancel _ hB)
  ext z
  constructor
  · intro hz
    refine ⟨Ring.inverse (frameTop F B) (F z).1,?_⟩
    apply F.injective
    exact Prod.ext (hright _) hz.symm
  · rintro ⟨v,rfl⟩
    change (F (B v)).2=frameBottom F B (Ring.inverse (frameTop F B) (frameTop F B v))
    rw [hleft]
    rfl

theorem frameTop_unit (F : (GraphFrame s k)) (B : (IndependentFrame s k))
    (h : InGraphChart F (framePoint B).val) : IsUnit (frameTop F B.val) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  let e := LinearEquiv.ofInjective B.val.toLinearMap B.property
  exact h.comp e.bijective

/-- Sending an arbitrary independent frame to its actual span is continuous
for the graph topology; this connects the atlas to geometric frame families. -/
theorem framePoint_continuous : Continuous (framePoint (s := s) (k := k)) := by
  apply continuous_iff_continuousAt.mpr
  intro B
  obtain ⟨F,hF⟩ := grassmann_atlas_covers (framePoint B)
  have hu := frameTop_unit F B hF
  have htop : Continuous (fun D : (IndependentFrame s k) => frameTop F D.val) :=
    (frameTop_contDiff F).continuous.comp continuous_subtype_val
  have hev : ∀ᶠ D : (IndependentFrame s k) in 𝓝 B, IsUnit (frameTop F D.val) :=
    htop.continuousAt (Units.isOpen.mem_nhds hu)
  have hs : ContinuousAt (fun D : (IndependentFrame s k) => slopePoint F (frameSlope F D.val)) B :=
    (slopePoint_continuous F).continuousAt.comp
      ((frameSlope_contDiffAt F B.val hu).continuousAt.comp continuous_subtype_val.continuousAt)
  apply hs.congr
  filter_upwards [hev] with D hD
  apply Subtype.ext
  exact frameSlope_plane F D.val hD

end Kaplansky.ComplexGrassmann

end

open Set Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_DirectSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite direct sums of line bundles, metrics, inclusions, and projections. -/

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky

variable {B S : Type*} [TopologicalSpace B] [Fintype S]
  {J : S → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

/-- The simultaneous finite cover for the direct sum of actual line cores. -/
def lineSumBaseSet (a : ∀ s, J s) : Set B := {x | ∀ s, x ∈ (C s).baseSet (a s)}

theorem isOpen_lineSumBaseSet (a : ∀ s, J s) : IsOpen (lineSumBaseSet C a) := by
  have he : lineSumBaseSet C a = ⋂ s, (C s).baseSet (a s) := by
    ext x
    simp [lineSumBaseSet]
  rw [he]
  exact isOpen_iInter_of_finite (fun s => (C s).isOpen_baseSet (a s))

/-- Componentwise transition on the finite Hilbert direct sum. -/
def lineSumTransition (a b : ∀ s, J s) (x : B) :
    EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S :=
  (EuclideanSpace.equiv S ℂ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun s =>
      ((C s).coordChange (a s) (b s) x).comp (ContinuousLinearMap.proj s))).comp
      (EuclideanSpace.equiv S ℂ).toContinuousLinearMap)

omit [Fintype S] in
@[simp] theorem lineSumTransition_apply (a b : ∀ s, J s) (x : B)
    (v : EuclideanSpace ℂ S) (s : S) :
    lineSumTransition C a b x v s = (C s).coordChange (a s) (b s) x (v s) := rfl

theorem continuousOn_lineSumTransition (a b : ∀ s, J s) :
    ContinuousOn (lineSumTransition C a b) (lineSumBaseSet C a ∩ lineSumBaseSet C b) := by
  apply continuousOn_clm_apply.mpr
  intro v
  apply (EuclideanSpace.equiv S ℂ).symm.continuous.comp_continuousOn
  apply continuousOn_pi.mpr
  intro s
  exact (((C s).continuousOn_coordChange (a s) (b s)).mono
    (fun x hx => ⟨hx.1 s,hx.2 s⟩)).clm_apply continuousOn_const

/-- A finite direct sum, with its ordinary vector-bundle topology and
finite Hilbert-space fibers. Neither a trivialization nor a trivial bundle
is asserted by the fact that the core uses a fixed model fiber. -/
def finiteLineSumCore : VectorBundleCore ℂ B (EuclideanSpace ℂ S) (∀ s, J s) where
  baseSet := lineSumBaseSet C
  isOpen_baseSet := isOpen_lineSumBaseSet C
  indexAt x s := (C s).indexAt x
  mem_baseSet_at x s := (C s).mem_baseSet_at x
  coordChange := lineSumTransition C
  coordChange_self a x hx v := by
    ext s
    exact (C s).coordChange_self (a s) x (hx s) (v s)
  continuousOn_coordChange := continuousOn_lineSumTransition C
  coordChange_comp a b c x hx v := by
    ext s
    exact (C s).coordChange_comp (a s) (b s) (c s) x
      ⟨⟨hx.1.1 s,hx.1.2 s⟩,hx.2 s⟩ (v s)

/-- The direct sum has the actual line-core fibers as its components. -/
def finiteLineSumFiberEquiv (x : B) :
    (finiteLineSumCore C).Fiber x ≃ₗ[ℂ] (∀ s, (C s).Fiber x) :=
  (EuclideanSpace.equiv S ℂ).toLinearEquiv

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky
variable {B S : Type*} [TopologicalSpace B] [Fintype S]
  {J : S → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

def finiteLineSumComponent (s : S)
    (z : TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore C).Fiber) :
    TotalSpace ℂ (C s).Fiber := ⟨z.proj, finiteLineSumFiberEquiv C z.proj z.2 s⟩

theorem continuous_finiteLineSumComponent (s : S) :
    Continuous (finiteLineSumComponent C s) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  rw [FiberBundle.continuousAt_totalSpace]
  constructor
  · exact (FiberBundle.continuous_proj _ _).continuousAt
  · let a : ∀ s, J s := (finiteLineSumCore C).indexAt z.proj
    have hz : z ∈ ((finiteLineSumCore C).localTriv a).source :=
      ((finiteLineSumCore C).localTriv a).mem_source.mpr
        ((finiteLineSumCore C).mem_baseSet_at z.proj)
    have h := (((finiteLineSumCore C).localTriv a).continuousAt hz).snd
    exact ((continuous_apply s).comp (EuclideanSpace.equiv S ℂ).continuous).continuousAt.comp h

/-- Continuity into the actual finite sum is exactly continuity of its
base and all of its actual line-bundle components. This includes the empty sum. -/
theorem continuous_finiteLineSum_iff {X : Type*} [TopologicalSpace X]
    (f : X → TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore C).Fiber) :
    Continuous f ↔ Continuous (fun x => (f x).proj) ∧
      ∀ s, Continuous (fun x => finiteLineSumComponent C s (f x)) := by
  constructor
  · intro hf
    exact ⟨(FiberBundle.continuous_proj _ _).comp hf,
      fun s => (continuous_finiteLineSumComponent C s).comp hf⟩
  · rintro ⟨hb,hc⟩
    apply continuous_iff_continuousAt.mpr
    intro x
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨hb.continuousAt, ?_⟩
    have h : ContinuousAt (fun y s =>
        (trivializationAt ℂ (C s).Fiber (f x).proj
          (finiteLineSumComponent C s (f y))).2) x := by
      apply continuousAt_pi.mpr
      intro s
      exact (FiberBundle.continuousAt_totalSpace ℂ _).mp ((hc s).continuousAt) |>.2
    exact (EuclideanSpace.equiv S ℂ).symm.continuous.continuousAt.comp h

end Kaplansky

open Bundle Topology
open scoped BigOperators InnerProductSpace
namespace Kaplansky
variable {B S : Type*} [TopologicalSpace B] [Fintype S]
  {J : S → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

instance finiteLineSumFiberNormedAddCommGroup (x : B) :
    NormedAddCommGroup ((finiteLineSumCore C).Fiber x) :=
  inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ S))

instance finiteLineSumFiberInnerProductSpace (x : B) :
    InnerProductSpace ℂ ((finiteLineSumCore C).Fiber x) :=
  inferInstanceAs (InnerProductSpace ℂ (EuclideanSpace ℂ S))

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky
variable {B S T : Type*} [TopologicalSpace B] [Fintype S] [Fintype T]
  {J : S⊕T → Type*} (L : ∀ u, VectorBundleCore ℂ B ℂ (J u))

def lineSumInl (x : B) : (finiteLineSumCore (fun s => L (Sum.inl s))).Fiber x →ₗ[ℂ]
    (finiteLineSumCore L).Fiber x where
  toFun v := WithLp.toLp 2 (Sum.elim (fun s => (show EuclideanSpace ℂ S from v) s) (fun _ => 0))
  map_add' v w := by
    apply (EuclideanSpace.equiv (S⊕T) ℂ).injective
    funext u
    cases u with
    | inl s => rfl
    | inr t => exact (zero_add (0 : ℂ)).symm
  map_smul' z v := by
    apply (EuclideanSpace.equiv (S⊕T) ℂ).injective
    funext u
    cases u with
    | inl s => rfl
    | inr t => exact (smul_zero z : z • (0 : ℂ) = 0).symm

def lineSumInr (x : B) : (finiteLineSumCore (fun t => L (Sum.inr t))).Fiber x →ₗ[ℂ]
    (finiteLineSumCore L).Fiber x where
  toFun v := WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun t => (show EuclideanSpace ℂ T from v) t))
  map_add' v w := by
    apply (EuclideanSpace.equiv (S⊕T) ℂ).injective
    funext u
    cases u with
    | inl s => exact (zero_add (0 : ℂ)).symm
    | inr t => rfl
  map_smul' z v := by
    apply (EuclideanSpace.equiv (S⊕T) ℂ).injective
    funext u
    cases u with
    | inl s => exact (smul_zero z : z • (0 : ℂ) = 0).symm
    | inr t => rfl

theorem continuous_lineSumInl : Continuous (fun z : TotalSpace (EuclideanSpace ℂ S)
    (finiteLineSumCore (fun s => L (Sum.inl s))).Fiber => TotalSpace.mk' (EuclideanSpace ℂ (S⊕T)) z.proj (lineSumInl L z.proj z.2)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  refine ⟨FiberBundle.continuous_proj _ _,?_⟩
  intro u
  cases u with
  | inl s => exact continuous_finiteLineSumComponent (fun s => L (Sum.inl s)) s
  | inr t =>
    apply continuous_iff_continuousAt.mpr
    intro z
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(FiberBundle.continuous_proj _ _).continuousAt,?_⟩
    change ContinuousAt (fun x : TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore (fun s => L (Sum.inl s))).Fiber =>
      (L (Sum.inr t)).coordChange ((L (Sum.inr t)).indexAt x.proj) ((L (Sum.inr t)).indexAt z.proj) x.proj 0) z
    simpa only [map_zero] using (continuousAt_const : ContinuousAt (fun _ : TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore (fun s => L (Sum.inl s))).Fiber => (0 : ℂ)) z)

theorem continuous_lineSumInr : Continuous (fun z : TotalSpace (EuclideanSpace ℂ T)
    (finiteLineSumCore (fun t => L (Sum.inr t))).Fiber => TotalSpace.mk' (EuclideanSpace ℂ (S⊕T)) z.proj (lineSumInr L z.proj z.2)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  refine ⟨FiberBundle.continuous_proj _ _,?_⟩
  intro u
  cases u with
  | inr t => exact continuous_finiteLineSumComponent (fun t => L (Sum.inr t)) t
  | inl s =>
    apply continuous_iff_continuousAt.mpr
    intro z
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(FiberBundle.continuous_proj _ _).continuousAt,?_⟩
    change ContinuousAt (fun x : TotalSpace (EuclideanSpace ℂ T) (finiteLineSumCore (fun t => L (Sum.inr t))).Fiber =>
      (L (Sum.inl s)).coordChange ((L (Sum.inl s)).indexAt x.proj) ((L (Sum.inl s)).indexAt z.proj) x.proj 0) z
    simpa only [map_zero] using (continuousAt_const : ContinuousAt (fun _ : TotalSpace (EuclideanSpace ℂ T) (finiteLineSumCore (fun t => L (Sum.inr t))).Fiber => (0 : ℂ)) z)

end Kaplansky

open Bundle Topology
open scoped BigOperators

end

open Bundle Topology
open scoped BigOperators
namespace Kaplansky
variable {B S T : Type*} [TopologicalSpace B] [Fintype S] [Fintype T]
  {J : S⊕T → Type*} (L : ∀ u, VectorBundleCore ℂ B ℂ (J u))

def lineSumFst (x : B) : (finiteLineSumCore L).Fiber x →ₗ[ℂ]
    (finiteLineSumCore (fun s => L (Sum.inl s))).Fiber x where
  toFun v := WithLp.toLp 2 (fun s => (show EuclideanSpace ℂ (S⊕T) from v) (Sum.inl s))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lineSumSnd (x : B) : (finiteLineSumCore L).Fiber x →ₗ[ℂ]
    (finiteLineSumCore (fun t => L (Sum.inr t))).Fiber x where
  toFun v := WithLp.toLp 2 (fun t => (show EuclideanSpace ℂ (S⊕T) from v) (Sum.inr t))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem continuous_lineSumFst : Continuous (fun z : TotalSpace (EuclideanSpace ℂ (S⊕T))
    (finiteLineSumCore L).Fiber => TotalSpace.mk' (EuclideanSpace ℂ S) z.proj (lineSumFst L z.proj z.2)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  exact ⟨FiberBundle.continuous_proj _ _,fun s => continuous_finiteLineSumComponent L (Sum.inl s)⟩

theorem continuous_lineSumSnd : Continuous (fun z : TotalSpace (EuclideanSpace ℂ (S⊕T))
    (finiteLineSumCore L).Fiber => TotalSpace.mk' (EuclideanSpace ℂ T) z.proj (lineSumSnd L z.proj z.2)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  exact ⟨FiberBundle.continuous_proj _ _,fun t => continuous_finiteLineSumComponent L (Sum.inr t)⟩

theorem lineSumFst_inner (x : B)
    (v : (finiteLineSumCore (fun s => L (Sum.inl s))).Fiber x)
    (w : (finiteLineSumCore L).Fiber x) :
    inner ℂ (lineSumFst L x w) v = inner ℂ w (lineSumInl L x v) := by
  change EuclideanSpace ℂ S at v
  change EuclideanSpace ℂ (S⊕T) at w
  change (∑ s, inner ℂ (w (Sum.inl s)) (v s)) =
    ∑ u : S ⊕ T, inner ℂ (w u) (Sum.elim (fun s => v s) (fun _ => 0) u)
  simp [Fintype.sum_sum_type]

theorem lineSumSnd_inner (x : B)
    (v : (finiteLineSumCore (fun t => L (Sum.inr t))).Fiber x)
    (w : (finiteLineSumCore L).Fiber x) :
    inner ℂ (lineSumSnd L x w) v = inner ℂ w (lineSumInr L x v) := by
  change EuclideanSpace ℂ T at v
  change EuclideanSpace ℂ (S⊕T) at w
  change (∑ t, inner ℂ (w (Sum.inr t)) (v t)) =
    ∑ u : S ⊕ T, inner ℂ (w u) (Sum.elim (fun _ => 0) (fun t => v t) u)
  simp [Fintype.sum_sum_type]

theorem lineSumFst_comp_inl (x : B) : (lineSumFst L x).comp (lineSumInl L x) = LinearMap.id := by
  ext v
  rfl

theorem lineSumSnd_comp_inr (x : B) : (lineSumSnd L x).comp (lineSumInr L x) = LinearMap.id := by
  ext v
  rfl

theorem lineSum_inl_fst_add_inr_snd (x : B) :
    (lineSumInl L x).comp (lineSumFst L x) + (lineSumInr L x).comp (lineSumSnd L x) = LinearMap.id := by
  ext v
  apply (EuclideanSpace.equiv (S⊕T) ℂ).injective
  funext u
  cases u with
  | inl s => exact add_zero ((show EuclideanSpace ℂ (S⊕T) from v) (Sum.inl s))
  | inr t => exact zero_add ((show EuclideanSpace ℂ (S⊕T) from v) (Sum.inr t))

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.MatrixScaling_Spectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral min-max bounds, continuity, and compactness of projections. -/

section

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {d : ℕ}

theorem projection_eigenvalue_zero_or_one {p : Matrix (Fin d) (Fin d) ℂ}
    (hp : p.IsHermitian) (hpp : p*p=p) (i : Fin d) :
    hp.eigenvalues i = 0 ∨ hp.eigenvalues i = 1 := by
  have h := congrArg (Unitary.conjStarAlgAut ℂ _ (star hp.eigenvectorUnitary)) hpp
  rw [map_mul, hp.conjStarAlgAut_star_eigenvectorUnitary] at h
  have hi := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i i) h
  simp only [Matrix.diagonal_mul_diagonal, diagonal_apply_eq,
    Function.comp_apply] at hi
  have hr : hp.eigenvalues i * hp.eigenvalues i = hp.eigenvalues i := by
    exact_mod_cast hi
  have hz : hp.eigenvalues i * (hp.eigenvalues i - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem projection_trace_eq_rank {p : Matrix (Fin d) (Fin d) ℂ}
    (hp : p.IsHermitian) (hpp : p*p=p) : p.trace = (p.rank : ℂ) := by
  rw [hp.trace_eq_sum_eigenvalues, hp.rank_eq_card_non_zero_eigs]
  calc
    ∑ i, (hp.eigenvalues i : ℂ) =
        ∑ i : Fin d, if hp.eigenvalues i ≠ 0 then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rcases projection_eigenvalue_zero_or_one hp hpp i with h | h <;> simp [h]
    _ = _ := by rw [Fintype.card_subtype]; simp only [Finset.sum_boole]

/-- Orthogonal rank-s projections, represented by equations with continuous
left-hand sides; the trace equation is equivalent to the rank condition. -/
abbrev projectionSpace (d s : ℕ) :=
  {p : Matrix (Fin d) (Fin d) ℂ // p.IsHermitian ∧ p*p=p ∧ p.trace.re=(s : ℝ)}

theorem projectionSpace_rank {s : ℕ} (p : projectionSpace d s) : p.val.rank = s := by
  have h := congrArg Complex.re (projection_trace_eq_rank p.property.1 p.property.2.1)
  rw [p.property.2.2] at h
  simpa only [Complex.natCast_re, Nat.cast_inj] using h.symm

theorem isCompact_projectionSpace (s : ℕ) :
    IsCompact {p : Matrix (Fin d) (Fin d) ℂ |
      p.IsHermitian ∧ p*p=p ∧ p.trace.re=(s : ℝ)} := by
  have hc : IsClosed {p : Matrix (Fin d) (Fin d) ℂ |
      p.IsHermitian ∧ p*p=p ∧ p.trace.re=(s : ℝ)} := by
    apply IsClosed.inter
    · exact isClosed_eq continuous_star continuous_id
    · apply IsClosed.inter
      · exact isClosed_eq (continuous_id.mul continuous_id) continuous_id
      · exact isClosed_eq (Complex.continuous_re.comp continuous_id.matrix_trace) continuous_const
  apply (isCompact_closedBall (0 : Matrix (Fin d) (Fin d) ℂ) 1).of_isClosed_subset hc
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  have hs : IsStarProjection p := ⟨hp.2.1, hp.1⟩
  exact hs.norm_le

instance instCompactSpaceProjectionSpace (s : ℕ) : CompactSpace (projectionSpace d s) :=
  isCompact_iff_compactSpace.mp (isCompact_projectionSpace s)

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.MatrixScaling_Continuous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous dependence of the unique normalized scaling. -/

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Topology
namespace Kaplansky
variable {n d r : ℕ}

theorem matrix_sqrt_factor {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef) :
    IsUnit (CFC.sqrt P) ∧ CFC.sqrt P * (CFC.sqrt P).conjTranspose = P := by
  refine ⟨CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hP.isStrictlyPositive, ?_⟩
  have hs : (CFC.sqrt P).conjTranspose = CFC.sqrt P := (CFC.sqrt_nonneg P).isSelfAdjoint.star_eq
  rw [hs, CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg]

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.MatrixScaling_Expansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic and finite-block expansion inequalities. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace Kaplansky
variable {n d r : ℕ} {E F D R : Type*}
variable [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
variable [AddCommGroup D] [Module ℂ D] [AddCommGroup R] [Module ℂ R]

def IntrinsicExpanding (T : Fin n → E →ₗ[ℂ] F) : Prop :=
  ∀ S : Submodule ℂ E, 2 * Module.finrank ℂ S ≤
    Module.finrank ℂ (⨆ i, S.map (T i) : Submodule ℂ F)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Multiplicities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplicity sequences and their arithmetic identities. -/


namespace Kaplansky
open scoped BigOperators

def testMultiplicity (m R j : ℕ) (i : Fin (j+1)) : ℕ :=
  if i.val=0 then 64*m*4^(R-j) else 960*m*4^(R+2*i.val-j-2)

def testRank (m R j : ℕ) : ℕ := 4^j*(64*m*4^R)

theorem testRank_eq (m R j : ℕ) : testRank m R j = 64*m*4^(R+j) := by
  simp only [testRank,pow_add]
  ring

theorem testMultiplicity_quarter {m R j : ℕ} (hj : j<R) (i : Fin (j+1)) :
    4*testMultiplicity m R (j+1) i.castSucc = testMultiplicity m R j i := by
  unfold testMultiplicity
  simp only [Fin.val_castSucc]
  split_ifs with hi
  · have he : R-j=(R-(j+1))+1 := by omega
    rw [he,pow_succ]
    ring
  · have he : R+2*i.val-j-2=(R+2*i.val-(j+1)-2)+1 := by omega
    rw [he,pow_succ]
    ring

theorem testMultiplicity_fresh {m R j : ℕ} (hj : j<R) :
    4*testMultiplicity m R (j+1) (Fin.last (j+1)) = 15*testRank m R j := by
  have hi : (Fin.last (j+1)).val ≠ 0 := by simp
  rw [testMultiplicity,ite_eq_right hi,testRank_eq]
  have he : R+j=(R+2*(Fin.last (j+1)).val-(j+1)-2)+1 := by
    simp only [Fin.val_last]
    omega
  rw [he,pow_succ]
  ring

theorem sum_testMultiplicity {m R j : ℕ} (hj : j≤R) :
    ∑ i, testMultiplicity m R j i = testRank m R j := by
  induction j with
  | zero => simp [testMultiplicity,testRank]
  | succ j ih =>
    have hlt : j<R := by omega
    have hprev := ih (by omega)
    have hq : 4*(∑ i : Fin (j+1), testMultiplicity m R (j+1) i.castSucc) =
        testRank m R j := by
      rw [Finset.mul_sum]
      simpa only [testMultiplicity_quarter hlt] using hprev
    rw [Fin.sum_univ_castSucc]
    have hf := testMultiplicity_fresh (m := m) hlt
    have hr : testRank m R (j+1)=4*testRank m R j := by
      simp only [testRank,pow_succ]
      ring
    rw [hr]
    omega

end Kaplansky

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Projection frames and faithful normalized vector projections. -/

section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix Topology NormedSpace
namespace Kaplansky
variable {d : ℕ}

/-- The actual one-dimensional subspace selected by a rank-one projection. -/
def projectionLine (p : projectionSpace d 1) : Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
  LinearMap.range (Matrix.toEuclideanLin p.val)

theorem projectionLine_finrank (p : projectionSpace d 1) : Module.finrank ℂ (projectionLine p) = 1 := by
  rw [projectionLine, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    ← Matrix.rank_eq_finrank_range_toLin]
  exact projectionSpace_rank p

/-- The projected coordinate vector supplies a local frame wherever nonzero. -/
def projectionColumn (p : projectionSpace d 1) (i : Fin d) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 (fun j => p.val j i)

theorem projectionColumn_mem (p : projectionSpace d 1) (i : Fin d) :
    projectionColumn p i ∈ projectionLine p := by
  refine ⟨WithLp.toLp 2 (Pi.single i (1 : ℂ)), ?_⟩
  ext j
  simp [projectionColumn, Matrix.toLpLin_apply]

theorem continuous_projectionColumn (i : Fin d) : Continuous (fun p : projectionSpace d 1 => projectionColumn p i) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℂ)).comp
  apply continuous_pi
  intro j
  exact (continuous_apply i).comp ((continuous_apply j).comp continuous_subtype_val)

theorem exists_projectionColumn_ne_zero (p : projectionSpace d 1) : ∃ i, projectionColumn p i ≠ 0 := by
  by_contra! h
  have hz : p.val = 0 := by
    ext j i
    have he := congrArg (fun v : EuclideanSpace ℂ (Fin d) => v j) (h i)
    exact he
  have hr := projectionSpace_rank p
  rw [hz, Matrix.rank_zero] at hr
  omega

def projectionChartSet (i : Fin d) : Set (projectionSpace d 1) := {p | projectionColumn p i ≠ 0}

theorem isOpen_projectionChartSet (i : Fin d) : IsOpen (projectionChartSet i) :=
  isOpen_ne.preimage (continuous_projectionColumn i)

def unitProjectionColumn (p : projectionSpace d 1) (i : Fin d) : EuclideanSpace ℂ (Fin d) :=
  NormedSpace.normalize (projectionColumn p i)

theorem unitProjectionColumn_norm (p : projectionSpace d 1) (i : Fin d)
    (hi : p ∈ projectionChartSet i) : ‖unitProjectionColumn p i‖ = 1 :=
  norm_normalize hi

theorem unitProjectionColumn_mem (p : projectionSpace d 1) (i : Fin d) :
    unitProjectionColumn p i ∈ projectionLine p := by
  unfold unitProjectionColumn NormedSpace.normalize
  exact (projectionLine p).smul_mem ((‖projectionColumn p i‖⁻¹ : ℝ) : ℂ) (projectionColumn_mem p i)

theorem continuousOn_unitProjectionColumn (i : Fin d) :
    ContinuousOn (fun p : projectionSpace d 1 => unitProjectionColumn p i) (projectionChartSet i) := by
  intro p hp
  apply ((continuous_projectionColumn i).norm.continuousWithinAt.inv₀ (norm_ne_zero_iff.mpr hp)).smul
    (continuous_projectionColumn i).continuousWithinAt

theorem projectionLine_eq_span (p : projectionSpace d 1) (i : Fin d)
    (hi : p ∈ projectionChartSet i) :
    projectionLine p = Submodule.span ℂ {unitProjectionColumn p i} :=
  eq_span_singleton_of_mem_of_finrank_eq_one (projectionLine_finrank p)
    (unitProjectionColumn_mem p i) (by intro h; simpa [h] using unitProjectionColumn_norm p i hi)

/-- The local frame gives the actual orthogonal coordinate formula on each line. -/
theorem unitProjectionColumn_reconstruct (p : projectionSpace d 1) (i : Fin d)
    (hi : p ∈ projectionChartSet i) (v : EuclideanSpace ℂ (Fin d)) (hv : v ∈ projectionLine p) :
    inner ℂ (unitProjectionColumn p i) v • unitProjectionColumn p i = v := by
  rw [projectionLine_eq_span p i hi] at hv
  obtain ⟨z,rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, unitProjectionColumn_norm p i hi]
  simp

end Kaplansky

end

section
open Matrix Topology
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator InnerProductSpace
namespace Kaplansky
variable {d : ℕ}

def vectorOuter (v : EuclideanSpace ℂ (Fin d)) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vecMulVec (fun i => v i) (fun i => star (v i))

theorem vectorOuter_hermitian (v : EuclideanSpace ℂ (Fin d)) : (vectorOuter v).IsHermitian := by
  ext i j
  simp [vectorOuter, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, star_mul]

theorem unitVector_dot (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖=1) :
    (fun i => star (v i)) ⬝ᵥ (fun i => v i) = 1 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v
  rw [hv] at h
  change (∑ i, v i * star (v i)) = ((1 : ℝ)^2 : ℂ) at h
  simpa [dotProduct,mul_comm] using h

theorem vectorOuter_idempotent (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖=1) :
    vectorOuter v * vectorOuter v = vectorOuter v := by
  unfold vectorOuter
  rw [Matrix.vecMulVec_mul_vecMulVec,unitVector_dot v hv,one_smul]

theorem vectorOuter_trace (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖=1) :
    (vectorOuter v).trace = 1 := by
  rw [vectorOuter,Matrix.trace_vecMulVec,dotProduct_comm]
  exact unitVector_dot v hv

/-- The ordinary rank-one orthogonal projector of a unit vector. -/
def unitVectorProjection (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖=1) : projectionSpace d 1 :=
  ⟨vectorOuter v, vectorOuter_hermitian v, vectorOuter_idempotent v hv,
    by rw [vectorOuter_trace v hv]; simp⟩

theorem continuous_vectorOuter : Continuous (vectorOuter (d := d)) := by
  apply continuous_matrix
  intro i j
  exact ((EuclideanSpace.proj i).continuous).mul ((EuclideanSpace.proj j).continuous.star)

theorem projection_toEuclideanLin_symmetricProjection (p : projectionSpace d 1) :
    (Matrix.toEuclideanLin p.val).IsSymmetricProjection := by
  refine ⟨?_,Matrix.isSymmetric_toEuclideanLin_iff.mpr p.property.1⟩
  change (Matrix.toEuclideanLin p.val).comp (Matrix.toEuclideanLin p.val) = _
  rw [← Matrix.toLpLin_mul_same,p.property.2.1]

theorem projectionLine_injective : Function.Injective (projectionLine (d := d)) := by
  intro p q h
  let f : Submodule ℂ (EuclideanSpace ℂ (Fin d)) →
      (EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) := fun U => U.starProjection
  obtain ⟨_,hp⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp
    (projection_toEuclideanLin_symmetricProjection p)
  obtain ⟨_,hq⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp
    (projection_toEuclideanLin_symmetricProjection q)
  apply Subtype.ext
  apply Matrix.toEuclideanLin.injective
  calc
    Matrix.toEuclideanLin p.val = f (projectionLine p) := hp
    _ = f (projectionLine q) := congrArg f h
    _ = Matrix.toEuclideanLin q.val := hq.symm

theorem vectorOuter_toEuclideanLin (v : EuclideanSpace ℂ (Fin d)) :
    Matrix.toEuclideanLin (vectorOuter v) = (InnerProductSpace.rankOne ℂ v v).toLinearMap := by
  change Matrix.toEuclideanLin (Matrix.vecMulVec v (star v)) = _
  rw [← InnerProductSpace.symm_toEuclideanLin_rankOne,LinearEquiv.apply_symm_apply]

theorem unitVectorProjection_line (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖=1) :
    projectionLine (unitVectorProjection v hv) = Submodule.span ℂ {v} := by
  change LinearMap.range (Matrix.toEuclideanLin (vectorOuter v)) = _
  rw [vectorOuter_toEuclideanLin]
  ext w
  constructor
  · rintro ⟨z,rfl⟩
    exact (Submodule.span ℂ {v}).smul_mem (inner ℂ v z) (Submodule.subset_span (Set.mem_singleton v))
  · intro hw
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
    refine ⟨c • v, ?_⟩
    simp [InnerProductSpace.rankOne_apply,inner_self_eq_norm_sq_to_K,hv]

end Kaplansky

end

open Matrix Topology NormedSpace
open scoped ComplexOrder Matrix.Norms.L2Operator
namespace Kaplansky
variable {d : ℕ}

def nonzeroVectorProjection (v : EuclideanSpace ℂ (Fin d)) (hv : v≠0) : projectionSpace d 1 :=
  unitVectorProjection (normalize v) (norm_normalize hv)

theorem nonzeroVectorProjection_line (v : EuclideanSpace ℂ (Fin d)) (hv : v≠0) :
    projectionLine (nonzeroVectorProjection v hv) = Submodule.span ℂ {v} := by
  rw [nonzeroVectorProjection,unitVectorProjection_line]
  change Submodule.span ℂ {((‖v‖⁻¹ : ℝ) : ℂ) • v} = _
  apply Submodule.span_singleton_smul_eq
  apply isUnit_iff_ne_zero.mpr
  exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr hv)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_ProjectionBundle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The projection line bundle and its dual. -/

section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix Topology Bundle
namespace Kaplansky
variable {d : ℕ}

def projectionLineTransition (i j : Fin d) (p : projectionSpace d 1) : ℂ :=
  inner ℂ (unitProjectionColumn p j) (unitProjectionColumn p i)

theorem projectionLineTransition_self (i : Fin d) (p : projectionSpace d 1)
    (hi : p ∈ projectionChartSet i) : projectionLineTransition i i p = 1 := by
  rw [projectionLineTransition, inner_self_eq_norm_sq_to_K, unitProjectionColumn_norm p i hi]
  simp

theorem projectionLineTransition_comp (i j k : Fin d) (p : projectionSpace d 1)
    (hj : p ∈ projectionChartSet j) :
    projectionLineTransition j k p * projectionLineTransition i j p = projectionLineTransition i k p := by
  have he := congrArg (inner ℂ (unitProjectionColumn p k))
    (unitProjectionColumn_reconstruct p j hj (unitProjectionColumn p i) (unitProjectionColumn_mem p i))
  simpa only [projectionLineTransition, inner_smul_right, mul_comm] using he

theorem continuousOn_projectionLineTransition (i j : Fin d) :
    ContinuousOn (projectionLineTransition i j) (projectionChartSet i ∩ projectionChartSet j) :=
  ((continuousOn_unitProjectionColumn j).mono Set.inter_subset_right).inner
    ((continuousOn_unitProjectionColumn i).mono Set.inter_subset_left)

/-- A genuine complex line-bundle core on the compact space of orthogonal
rank-one projections. Its transition functions are constructed, not assumed. -/
def projectionLineCore (d : ℕ) : VectorBundleCore ℂ (projectionSpace d 1) ℂ (Fin d) where
  baseSet := projectionChartSet
  isOpen_baseSet := isOpen_projectionChartSet
  indexAt p := (exists_projectionColumn_ne_zero p).choose
  mem_baseSet_at p := (exists_projectionColumn_ne_zero p).choose_spec
  coordChange i j p := projectionLineTransition i j p • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i p hp z := by simp [projectionLineTransition_self i p hp]
  continuousOn_coordChange i j := (continuousOn_projectionLineTransition i j).smul continuousOn_const
  coordChange_comp i j k p hp z := by
    change projectionLineTransition j k p * (projectionLineTransition i j p * z) =
      projectionLineTransition i k p * z
    rw [← mul_assoc, projectionLineTransition_comp i j k p hp.1.2]

end Kaplansky

end

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix Topology Bundle
namespace Kaplansky
variable {d : ℕ}

/-- The dual (hyperplane) line core, with inverse unitary transitions. -/
def projectionDualLineCore (d : ℕ) : VectorBundleCore ℂ (projectionSpace d 1) ℂ (Fin d) where
  baseSet := projectionChartSet
  isOpen_baseSet := isOpen_projectionChartSet
  indexAt := (projectionLineCore d).indexAt
  mem_baseSet_at := (projectionLineCore d).mem_baseSet_at
  coordChange i j p := star (projectionLineTransition i j p) • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i p hp z := by simp [projectionLineTransition_self i p hp]
  continuousOn_coordChange i j := (continuousOn_projectionLineTransition i j).star.smul continuousOn_const
  coordChange_comp i j k p hp z := by
    change star (projectionLineTransition j k p) * (star (projectionLineTransition i j p) * z) =
      star (projectionLineTransition i k p) * z
    rw [← mul_assoc, ← star_mul, mul_comm (projectionLineTransition i j p),
      projectionLineTransition_comp i j k p hp.1.2]

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Base
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact bundle-test base, prefix dimensions, and retained multiplicities. -/

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky

def testProjectiveDimension (m R : ℕ) (i : Fin R) : ℕ :=
  320 * m^2 * 4^(2*i.val) * (4^(R-i.val)-1)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Pullback line bundles and their continuous chart identifications. -/

section
open Bundle Topology
namespace Kaplansky

section
variable {B X J : Type*} [TopologicalSpace B] [TopologicalSpace X]
  (C : VectorBundleCore ℂ B ℂ J) (f : C(X,B))

/-- Pull a line core back along a continuous base map. -/
def pullbackLineCore : VectorBundleCore ℂ X ℂ J where
  baseSet j := f ⁻¹' C.baseSet j
  isOpen_baseSet j := (C.isOpen_baseSet j).preimage f.continuous
  indexAt x := C.indexAt (f x)
  mem_baseSet_at x := C.mem_baseSet_at (f x)
  coordChange i j x := C.coordChange i j (f x)
  coordChange_self i x hx z := C.coordChange_self i (f x) hx z
  continuousOn_coordChange i j := (C.continuousOn_coordChange i j).comp
    f.continuous.continuousOn (fun _ h => h)
  coordChange_comp i j k x hx z := C.coordChange_comp i j k (f x) hx z

/-- A single global identity chart for the trivial complex line. -/
def trivialLineCore (B : Type*) [TopologicalSpace B] : VectorBundleCore ℂ B ℂ Unit where
  baseSet _ := Set.univ
  isOpen_baseSet _ := isOpen_univ
  indexAt _ := ()
  mem_baseSet_at _ := Set.mem_univ _
  coordChange _ _ _ := ContinuousLinearMap.id ℂ ℂ
  coordChange_self _ _ _ _ := rfl
  continuousOn_coordChange _ _ := continuousOn_const
  coordChange_comp _ _ _ _ _ _ := rfl

end

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Bundles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Test bundles, Hermitian metrics, and their trivial initial stage. -/

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky

def testSummandLineIndex {R j : ℕ} (hj : j≤R) (i : Fin (j+1)) : Option (Fin R) :=
  if h : i.val=0 then none else some ⟨i.val-1,by omega⟩

@[simp] theorem testSummandLineIndex_zero {R j : ℕ} (hj : j≤R) :
    testSummandLineIndex hj 0 = none := by simp [testSummandLineIndex]

abbrev TestBundleSlot (m R j : ℕ) := Σ i : Fin (j+1), Fin (testMultiplicity m R j i)

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Projective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Projection models of complex projective space and products. -/

section
open Matrix Topology NormedSpace
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator InnerProductSpace
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

def projectionToGrassmann (p : projectionSpace (1+k) 1) : Grassmann 1 k :=
  ⟨(projectionLine p).map (EuclideanSpace.equiv (Fin (1+k)) ℂ).toLinearMap,
    by rw [LinearEquiv.finrank_map_eq]; exact projectionLine_finrank p⟩

def columnFrame (i : Fin (1+k)) (p : projectionSpace (1+k) 1) : PlaneFrameMap 1 k :=
  (ContinuousLinearMap.proj (0 : Fin 1)).smulRight
    ((EuclideanSpace.equiv (Fin (1+k)) ℂ) (unitProjectionColumn p i))

theorem columnFrame_injective (i : Fin (1+k)) (p : projectionSpace (1+k) 1)
    (hp : p ∈ projectionChartSet i) : Function.Injective (columnFrame i p) := by
  have hv : (EuclideanSpace.equiv (Fin (1+k)) ℂ) (unitProjectionColumn p i) ≠ 0 := by
    intro h
    have hz := (EuclideanSpace.equiv (Fin (1+k)) ℂ).injective (h.trans (map_zero _).symm)
    have hn := unitProjectionColumn_norm p i hp
    rw [hz,norm_zero] at hn
    norm_num at hn
  intro u v huv
  have hs : (u 0-v 0) • ((EuclideanSpace.equiv (Fin (1+k)) ℂ) (unitProjectionColumn p i))=0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr huv
  have h0 := sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hv)
  ext j
  have hj : j=0 := Fin.eq_zero j
  simpa only [hj] using h0

theorem columnFrame_point (i : Fin (1+k)) (p : projectionSpace (1+k) 1)
    (hp : p ∈ projectionChartSet i) :
    framePoint ⟨columnFrame i p,columnFrame_injective i p hp⟩ = projectionToGrassmann p := by
  apply Subtype.ext
  change LinearMap.range (columnFrame i p).toLinearMap =
    (projectionLine p).map (EuclideanSpace.equiv (Fin (1+k)) ℂ).toLinearMap
  rw [projectionLine_eq_span p i hp,Submodule.map_span,Set.image_singleton]
  ext z
  constructor
  · rintro ⟨v,rfl⟩
    exact (Submodule.span ℂ {_}).smul_mem (v 0) (Submodule.subset_span (Set.mem_singleton _))
  · intro hz
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨fun _ => c,rfl⟩

theorem continuousOn_columnFrame (i : Fin (1+k)) :
    ContinuousOn (columnFrame i) (projectionChartSet i) := by
  apply continuousOn_clm_apply.mpr
  intro v
  exact continuousOn_const.smul
    ((EuclideanSpace.equiv (Fin (1+k)) ℂ).continuous.comp_continuousOn
      (continuousOn_unitProjectionColumn i))

theorem continuous_projectionToGrassmann : Continuous (projectionToGrassmann (k := k)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨i,hi⟩ := exists_projectionColumn_ne_zero p
  have hc : ContinuousOn (projectionToGrassmann (k := k)) (projectionChartSet i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hf : Continuous (fun q : projectionChartSet (d := 1+k) i =>
        (⟨columnFrame i q.val,columnFrame_injective i q.val q.property⟩ : IndependentFrame 1 k)) :=
      (continuousOn_iff_continuous_domRestrict.mp (continuousOn_columnFrame i)).subtype_mk _
    exact (framePoint_continuous.comp hf).congr (fun q => columnFrame_point i q.val q.property)
  exact (hc p hi).continuousAt ((isOpen_projectionChartSet i).mem_nhds hi)

theorem projectionToGrassmann_injective : Function.Injective (projectionToGrassmann (k := k)) := by
  intro p q h
  apply projectionLine_injective
  exact (Submodule.map_injective_of_injective
    (EuclideanSpace.equiv (Fin (1+k)) ℂ).injective) (congrArg Subtype.val h)

end Kaplansky.ComplexGrassmann

end

section
open Matrix Topology NormedSpace
open scoped ComplexOrder Matrix.Norms.L2Operator
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

/-- A nonvanishing representative of a line in a graph chart. -/
def graphLineVector (F : GraphFrame 1 k) (A : GraphSlope 1 k) : EuclideanSpace ℂ (Fin (1+k)) :=
  (EuclideanSpace.equiv (Fin (1+k)) ℂ).symm (F.symm ((fun _ => 1),A (fun _ => 1)))

@[simp] theorem graphLineVector_coordinates (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    (EuclideanSpace.equiv (Fin (1+k)) ℂ) (graphLineVector F A) = F.symm ((fun _ => 1),A (fun _ => 1)) :=
  (EuclideanSpace.equiv (Fin (1+k)) ℂ).apply_symm_apply _

theorem graphLineVector_ne_zero (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    graphLineVector F A ≠ 0 := by
  intro h
  have hh := congrArg (fun v : EuclideanSpace ℂ (Fin (1+k)) =>
    (F ((EuclideanSpace.equiv (Fin (1+k)) ℂ) v)).1 (0 : Fin 1)) h
  rw [graphLineVector_coordinates,LinearEquiv.apply_symm_apply,map_zero,map_zero] at hh
  norm_num at hh

theorem continuous_graphLineVector (F : GraphFrame 1 k) : Continuous (graphLineVector F) := by
  apply (EuclideanSpace.equiv (Fin (1+k)) ℂ).symm.continuous.comp
  apply F.symm.toContinuousLinearEquiv.continuous.comp
  exact continuous_const.prodMk (continuous_id.clm_apply continuous_const)

def graphLineProjection (F : GraphFrame 1 k) (A : GraphSlope 1 k) : projectionSpace (1+k) 1 :=
  nonzeroVectorProjection (graphLineVector F A) (graphLineVector_ne_zero F A)

theorem continuous_graphLineProjection (F : GraphFrame 1 k) : Continuous (graphLineProjection F) := by
  apply Continuous.subtype_mk
  apply continuous_vectorOuter.comp
  exact ((continuous_graphLineVector F).norm.inv₀ (fun A =>
    norm_ne_zero_iff.mpr (graphLineVector_ne_zero F A))).smul (continuous_graphLineVector F)

theorem graphLineProjection_point (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    projectionToGrassmann (graphLineProjection F A) = slopePoint F A := by
  apply Subtype.ext
  change (projectionLine (nonzeroVectorProjection (graphLineVector F A) _)).map
    (EuclideanSpace.equiv (Fin (1+k)) ℂ).toLinearMap = graphPlane F A.toLinearMap
  rw [nonzeroVectorProjection_line,Submodule.map_span,Set.image_singleton]
  symm
  apply eq_span_singleton_of_mem_of_finrank_eq_one (graphPlane_finrank F A.toLinearMap)
  · change (F ((EuclideanSpace.equiv (Fin (1+k)) ℂ) (graphLineVector F A))).2 =
      A (F ((EuclideanSpace.equiv (Fin (1+k)) ℂ) (graphLineVector F A))).1
    rw [graphLineVector_coordinates,LinearEquiv.apply_symm_apply]
  · intro h
    apply graphLineVector_ne_zero F A
    exact (EuclideanSpace.equiv (Fin (1+k)) ℂ).injective (h.trans (map_zero _).symm)

theorem projectionToGrassmann_surjective : Function.Surjective (projectionToGrassmann (k := k)) := by
  intro P
  obtain ⟨F,hF⟩ := grassmann_atlas_covers P
  refine ⟨graphLineProjection F (slopeCoordinate F P),?_⟩
  rw [graphLineProjection_point,slopePoint_coordinate F P hF]

/-- Projection and graph-atlas models of complex projective space agree
as sets of actual complex lines. -/
def projectiveProjectionEquiv (k : ℕ) : projectionSpace (1+k) 1 ≃ Grassmann 1 k :=
  Equiv.ofBijective projectionToGrassmann ⟨projectionToGrassmann_injective,projectionToGrassmann_surjective⟩

end Kaplansky.ComplexGrassmann

end

section
open Topology Set
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

theorem projectiveProjectionEquiv_symm_slopePoint (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    (projectiveProjectionEquiv k).symm (slopePoint F A) = graphLineProjection F A := by
  apply (projectiveProjectionEquiv k).injective
  rw [Equiv.apply_symm_apply]
  exact (graphLineProjection_point F A).symm

theorem continuous_projectiveProjectionEquiv_symm : Continuous (projectiveProjectionEquiv k).symm := by
  apply continuous_def.mpr
  intro U hU
  change ∀ F : GraphFrame 1 k, IsOpen (slopePoint F ⁻¹' ((projectiveProjectionEquiv k).symm ⁻¹' U))
  intro F
  have he : (fun A => (projectiveProjectionEquiv k).symm (slopePoint F A)) = graphLineProjection F :=
    funext (projectiveProjectionEquiv_symm_slopePoint F)
  have hc : Continuous (fun A => (projectiveProjectionEquiv k).symm (slopePoint F A)) :=
    he ▸ continuous_graphLineProjection F
  exact hc.isOpen_preimage U hU

/-- Identification of the compact orthogonal-projection model with the
ordinary smooth graph-chart model of complex projective space. -/
def projectiveProjectionHomeomorph (k : ℕ) : projectionSpace (1+k) 1 ≃ₜ Grassmann 1 k where
  toEquiv := projectiveProjectionEquiv k
  continuous_toFun := continuous_projectionToGrassmann
  continuous_invFun := continuous_projectiveProjectionEquiv_symm

instance projectiveGrassmannT2 : T2Space (Grassmann 1 k) :=
  (projectiveProjectionHomeomorph k).t2Space

instance projectiveGrassmannCompact : CompactSpace (Grassmann 1 k) :=
  (projectiveProjectionHomeomorph k).compactSpace

end Kaplansky.ComplexGrassmann

open Topology Set
open scoped Manifold ContDiff BigOperators
namespace Kaplansky.ComplexGrassmann
variable {ι : Type*} [Fintype ι] (K : ι → ℕ)

abbrev ProjectiveProduct := ∀ i, Grassmann 1 (K i)

end Kaplansky.ComplexGrassmann

end

open Topology Set
open scoped Manifold ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_RealModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Real models of complex bundles and smooth finite line sums. -/

open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky
variable {B F G J : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  (C : VectorBundleCore ℂ B F J) (e : F ≃L[ℂ] G)

/-- A fixed linear change of model coordinates; the gluing is conjugated. -/
def changeModelCore : VectorBundleCore ℂ B G J where
  baseSet := C.baseSet
  isOpen_baseSet := C.isOpen_baseSet
  indexAt := C.indexAt
  mem_baseSet_at := C.mem_baseSet_at
  coordChange i j x := e.toContinuousLinearMap.comp ((C.coordChange i j x).comp e.symm.toContinuousLinearMap)
  coordChange_self i x hx v := by simp [C.coordChange_self i x hx]
  continuousOn_coordChange i j := continuousOn_const.clm_comp ((C.continuousOn_coordChange i j).clm_comp continuousOn_const)
  coordChange_comp i j k x hx v := by
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using
      congrArg e (C.coordChange_comp i j k x hx (e.symm v))

/-- The coordinate change is a homeomorphism of actual total spaces. -/
def changeModelCoreTotalHomeomorph : TotalSpace F C.Fiber ≃ₜ TotalSpace G (changeModelCore C e).Fiber where
  toFun z := ⟨z.proj,e z.2⟩
  invFun z := ⟨z.proj,e.symm z.2⟩
  left_inv z := by
    obtain ⟨x, v⟩ := z
    exact congrArg (fun w => TotalSpace.mk' F x w) (e.symm_apply_apply v)
  right_inv z := by
    obtain ⟨x, v⟩ := z
    exact congrArg (fun w => TotalSpace.mk' G x w) (e.apply_symm_apply v)
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro z
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(FiberBundle.continuous_proj F C.Fiber).continuousAt,?_⟩
    have h := ((C.localTriv (C.indexAt z.proj)).continuousAt
      ((C.localTriv _).mem_source.mpr (C.mem_baseSet_at z.proj))).snd
    change ContinuousAt (fun x : TotalSpace F C.Fiber =>
      e (C.coordChange (C.indexAt x.proj) (C.indexAt z.proj) x.proj (e.symm (e x.2)))) z
    change ContinuousAt (fun x : TotalSpace F C.Fiber =>
      C.coordChange (C.indexAt x.proj) (C.indexAt z.proj) x.proj x.2) z at h
    have he (x : TotalSpace F C.Fiber) : e.symm (e x.2) = x.2 := e.symm_apply_apply x.2
    simpa only [Function.comp_def, he] using e.continuous.continuousAt.comp h
  continuous_invFun := by
    apply continuous_iff_continuousAt.mpr
    intro z
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(FiberBundle.continuous_proj G (changeModelCore C e).Fiber).continuousAt,?_⟩
    have h := (((changeModelCore C e).localTriv (C.indexAt z.proj)).continuousAt
      (((changeModelCore C e).localTriv _).mem_source.mpr (C.mem_baseSet_at z.proj))).snd
    change ContinuousAt (fun x : TotalSpace G (changeModelCore C e).Fiber =>
      C.coordChange (C.indexAt x.proj) (C.indexAt z.proj) x.proj (e.symm x.2)) z
    change ContinuousAt (fun x : TotalSpace G (changeModelCore C e).Fiber =>
      e (C.coordChange (C.indexAt x.proj) (C.indexAt z.proj) x.proj (e.symm x.2))) z at h
    simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using e.symm.continuous.continuousAt.comp h

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_SmoothLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Smooth projective lines, product lines, finite sums, and restrictions. -/

section
open Bundle Topology NormedSpace
open scoped Manifold ContDiff Matrix.Norms.Elementwise
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

def projectiveProjectionMap (k : ℕ) : C(Grassmann 1 k,projectionSpace (1+k) 1) :=
  ⟨(projectiveProjectionEquiv k).symm,continuous_projectiveProjectionEquiv_symm⟩

def projectiveHyperplaneCore (k : ℕ) :=
  pullbackLineCore (projectionDualLineCore (1+k)) (projectiveProjectionMap k)

end Kaplansky.ComplexGrassmann

end

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky.ComplexGrassmann

section
variable {ι : Type*} [Fintype ι] (K : ι → ℕ)

def productLineChartIndex : Option ι → Type
  | none => Unit
  | some i => Fin (1+K i)

/-- L₀ is trivial; Lᵢ is the actual hyperplane line pulled back from factor i. -/
def productLineCore (i : Option ι) :
    VectorBundleCore ℂ (ProjectiveProduct K) ℂ (productLineChartIndex K i) :=
  match i with
  | none => trivialLineCore (ProjectiveProduct K)
  | some i => pullbackLineCore (projectiveHyperplaneCore (K i)) ⟨fun P => P i,continuous_apply i⟩

end

variable {ι S : Type*} [Fintype ι] [Fintype S] (K : ι → ℕ) (label : S → Option ι)

/-- The ordinary smooth Hermitian direct sum of the specified hyperplane
pullbacks and trivial lines on the actual projective product. -/
def smoothLineSumCore := finiteLineSumCore (fun s => productLineCore K (label s))
abbrev SmoothLineSumBundle := (smoothLineSumCore K label).Fiber

instance smoothLineSum_norm (P : ProjectiveProduct K) :
    NormedAddCommGroup (SmoothLineSumBundle K label P) := finiteLineSumFiberNormedAddCommGroup _ P
instance smoothLineSum_inner (P : ProjectiveProduct K) :
    InnerProductSpace ℂ (SmoothLineSumBundle K label P) := finiteLineSumFiberInnerProductSpace _ P

end Kaplansky.ComplexGrassmann

end

open Bundle Topology
namespace Kaplansky.ComplexGrassmann
variable {ι κ X : Type*} [Fintype ι] [Fintype κ] [TopologicalSpace X]
  (K : κ → ℕ) (f : ι → κ)

def projectiveRestrict : C(ProjectiveProduct K, ProjectiveProduct (fun i => K (f i))) :=
  ⟨fun x i => x (f i), continuous_pi (fun i => continuous_apply (f i))⟩

omit [Fintype ι] [Fintype κ] in
/-- Restricting the base preserves the actual local line coordinates, for
both the trivial line and every hyperplane pullback. -/
theorem continuous_productLine_restrict_iff (i : Option ι)
    (g : X → ProjectiveProduct K) (v : X → ℂ) (hg : Continuous g) :
    Continuous (fun x => TotalSpace.mk' ℂ (E := (productLineCore K (i.map f)).Fiber) (g x) (v x)) ↔
    Continuous (fun x => TotalSpace.mk' ℂ (E := (productLineCore (fun i => K (f i)) i).Fiber)
      (projectiveRestrict K f (g x)) (v x)) := by
  cases i with
  | none =>
    constructor <;> intro h <;> apply continuous_iff_continuousAt.mpr <;> intro x
    · rw [FiberBundle.continuousAt_totalSpace]
      exact ⟨((projectiveRestrict K f).continuous.comp hg).continuousAt,
        ((FiberBundle.continuousAt_totalSpace ℂ _).mp (h.continuousAt)).2⟩
    · rw [FiberBundle.continuousAt_totalSpace]
      exact ⟨hg.continuousAt,
        ((FiberBundle.continuousAt_totalSpace ℂ _).mp (h.continuousAt)).2⟩
  | some i =>
    constructor <;> intro h <;> apply continuous_iff_continuousAt.mpr <;> intro x
    · rw [FiberBundle.continuousAt_totalSpace]
      exact ⟨((projectiveRestrict K f).continuous.comp hg).continuousAt,
        ((FiberBundle.continuousAt_totalSpace ℂ _).mp (h.continuousAt)).2⟩
    · rw [FiberBundle.continuousAt_totalSpace]
      exact ⟨hg.continuousAt,
        ((FiberBundle.continuousAt_totalSpace ℂ _).mp (h.continuousAt)).2⟩

omit [Fintype ι] [Fintype κ] in
/-- The finite orthogonal sum has the ordinary pullback topology under
coordinate restriction. The base and fiber coordinates are explicit. -/
theorem continuous_lineSum_restrict_iff {S : Type*} [Fintype S]
    (label : S → Option ι) (g : X → ProjectiveProduct K)
    (v : X → EuclideanSpace ℂ S) (hg : Continuous g) :
    Continuous (fun x => TotalSpace.mk' (EuclideanSpace ℂ S)
      (E := SmoothLineSumBundle K (fun s => (label s).map f)) (g x) (v x)) ↔
    Continuous (fun x => TotalSpace.mk' (EuclideanSpace ℂ S)
      (E := SmoothLineSumBundle (fun i => K (f i)) label)
      (projectiveRestrict K f (g x)) (v x)) := by
  constructor
  · intro h
    have hc := (continuous_finiteLineSum_iff
      (fun s => productLineCore K ((label s).map f)) _).mp h
    apply (continuous_finiteLineSum_iff
      (fun s => productLineCore (fun i => K (f i)) (label s)) _).mpr
    refine ⟨(projectiveRestrict K f).continuous.comp hg,fun s => ?_⟩
    exact (continuous_productLine_restrict_iff K f (label s) g (fun x => v x s) hg).mp (hc.2 s)
  · intro h
    have hc := (continuous_finiteLineSum_iff
      (fun s => productLineCore (fun i => K (f i)) (label s)) _).mp h
    apply (continuous_finiteLineSum_iff
      (fun s => productLineCore K ((label s).map f)) _).mpr
    refine ⟨hg,fun s => ?_⟩
    exact (continuous_productLine_restrict_iff K f (label s) g (fun x => v x s) hg).mpr (hc.2 s)

end Kaplansky.ComplexGrassmann

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Smooth bases and test bundles with replacement maps. -/

section
open Topology
open scoped Manifold ContDiff BigOperators
namespace Kaplansky
open ComplexGrassmann

abbrev SmoothTestBase (m R : ℕ) := ProjectiveProduct (testProjectiveDimension m R)

abbrev SmoothPrefixBase (m R j : ℕ) (hj : j<R) :=
  ProjectiveProduct (fun i : Fin (j+1) => testProjectiveDimension m R (i.castLE hj))

end Kaplansky

end

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky
open ComplexGrassmann

abbrev stageProjectiveDimensions (m R b : ℕ) (hb : b≤R) : Fin b → ℕ :=
  fun i => testProjectiveDimension m R (i.castLE hb)

/-- E_n on the first b projective factors, retaining the full-R K_i. -/
def smoothTestBundleCore (m R b n : ℕ) (hb : b≤R) (hn : n≤b) :=
  smoothLineSumCore (stageProjectiveDimensions m R b hb)
    (fun s : TestBundleSlot m R n => testSummandLineIndex hn s.1)

abbrev SmoothTestBundle (m R b n : ℕ) (hb : b≤R) (hn : n≤b) :=
  (smoothTestBundleCore m R b n hb hn).Fiber

instance smoothTestBundle_norm (m R b n : ℕ) (hb : b≤R) (hn : n≤b)
    (P : ProjectiveProduct (stageProjectiveDimensions m R b hb)) :
    NormedAddCommGroup (SmoothTestBundle m R b n hb hn P) := smoothLineSum_norm _ _ P
instance smoothTestBundle_inner (m R b n : ℕ) (hb : b≤R) (hn : n≤b)
    (P : ProjectiveProduct (stageProjectiveDimensions m R b hb)) :
    InnerProductSpace ℂ (SmoothTestBundle m R b n hb hn P) := smoothLineSum_inner _ _ P

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky

def testReplacementMultiplicity (m R j : ℕ) (i : Fin (j+1)) : ℕ :=
  testMultiplicity m R (j+1) i.castSucc

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Frames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Hermitian frames, synthesis, and unitary transition functions. -/

section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix
namespace Kaplansky
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Change a finite frame by a matrix acting on its coefficient columns. -/
def frameMul (v : Fin d → E) (A : Matrix (Fin d) (Fin d) ℂ) : Fin d → E :=
  fun j => ∑ i, A i j • v i

theorem gram_frameMul (v : Fin d → E) (A : Matrix (Fin d) (Fin d) ℂ) :
    gram ℂ (frameMul v A) = Aᴴ * gram ℂ v * A := by
  ext i j
  simp only [gram_apply, frameMul, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [← starRingEnd_apply]
  ring

/-- The inverse positive square root orthonormalizes a positive Gram matrix. -/
theorem inverse_sqrt_gram_identity {G : Matrix (Fin d) (Fin d) ℂ} (hG : G.PosDef) :
    (CFC.sqrt G)⁻¹ᴴ * G * (CFC.sqrt G)⁻¹ = 1 := by
  obtain ⟨hu,he⟩ := matrix_sqrt_factor hG
  have hs : (CFC.sqrt G)ᴴ = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint.star_eq
  have hi : (CFC.sqrt G)⁻¹ᴴ = (CFC.sqrt G)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hs]
  rw [hi]
  conv_lhs => arg 1; arg 2; rw [← he, hs]
  have hl := Matrix.nonsing_inv_mul (CFC.sqrt G) ((CFC.sqrt G).isUnit_iff_isUnit_det.mp hu)
  have hr := Matrix.mul_nonsing_inv (CFC.sqrt G) ((CFC.sqrt G).isUnit_iff_isUnit_det.mp hu)
  simp only [← Matrix.mul_assoc, hl, Matrix.one_mul, hr]

def metricFrame (v : Fin d → E) : Fin d → E :=
  frameMul v (CFC.sqrt (gram ℂ v))⁻¹

theorem metricFrame_orthonormal (v : Fin d → E) (hv : LinearIndependent ℂ v) :
    Orthonormal ℂ (metricFrame v) := by
  apply Matrix.gram_eq_one_iff_orthonormal.mp
  rw [metricFrame, gram_frameMul]
  exact inverse_sqrt_gram_identity (Matrix.posDef_gram_of_linearIndependent hv)

theorem frameMul_mul (v : Fin d → E) (A B : Matrix (Fin d) (Fin d) ℂ) :
    frameMul (frameMul v A) B = frameMul v (A * B) := by
  funext j
  simp only [frameMul, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]

theorem frameMul_one (v : Fin d → E) : frameMul v 1 = v := by
  classical
  funext j
  simp [frameMul, Matrix.one_apply]

theorem span_frameMul_le (v : Fin d → E) (A : Matrix (Fin d) (Fin d) ℂ) :
    Submodule.span ℂ (Set.range (frameMul v A)) ≤ Submodule.span ℂ (Set.range v) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))

end Kaplansky

end

section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix Bundle Topology
namespace Kaplansky
variable {d : ℕ} {Y : Type*} [TopologicalSpace Y]
variable {E : Y → Type*} [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]

/-- Continuity of a Hermitian metric, expressed by its values on local
continuous sections of an ordinary complex vector bundle. -/
def ContinuousHermitianMetric : Prop :=
  ∀ (s : Set Y) (v w : ∀ y, E y),
    ContinuousOn (fun y => TotalSpace.mk' (Fin d → ℂ) y (v y)) s →
    ContinuousOn (fun y => TotalSpace.mk' (Fin d → ℂ) y (w y)) s →
    ContinuousOn (fun y => inner ℂ (v y) (w y)) s

/-- The ordinary frame obtained from a linear trivialization. -/
def bundleChartFrame (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E))
    [e.IsLinear ℂ] (y : Y) (i : Fin d) : E y :=
  e.symmₗ ℂ y (Pi.single i 1)

def bundleChartBasis (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E))
    [e.IsLinear ℂ] (y : Y) (hy : y ∈ e.baseSet) : Module.Basis (Fin d) ℂ (E y) :=
  (Pi.basisFun ℂ (Fin d)).map (e.linearEquivAt ℂ y hy).symm

theorem bundleChartBasis_apply (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E))
    [e.IsLinear ℂ] (y : Y) (hy : y ∈ e.baseSet) (i : Fin d) :
    bundleChartBasis e y hy i = bundleChartFrame e y i := by
  simp [bundleChartBasis, bundleChartFrame, hy]

/-- The actual orthonormal frame on the chart, extended by zero outside. -/
def bundleOrthonormalFrame
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ] (y : Y) : Fin d → E y :=
  metricFrame (bundleChartFrame e y)

end Kaplansky

end

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_CoordinatesMetric
attribute [-instance] _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite-coordinate smooth bundles and their metrics. -/

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky
open ComplexGrassmann
variable {S ι : Type*} [Fintype S] [Fintype ι]

def finiteCoordinateEquiv (d : ℕ) (hd : Fintype.card S=d) :
    EuclideanSpace ℂ S ≃L[ℂ] (Fin d → ℂ) :=
  (LinearEquiv.ofFinrankEq (R := ℂ) (EuclideanSpace ℂ S) (Fin d → ℂ) (by simpa using hd)).toContinuousLinearEquiv

variable (K : ι → ℕ) (label : S → Option ι) (d : ℕ) (hd : Fintype.card S=d)

def finiteCoordinateCore := changeModelCore (smoothLineSumCore K label) (finiteCoordinateEquiv d hd)
abbrev FiniteCoordinateBundle := (finiteCoordinateCore K label d hd).Fiber

/-- The finite-coordinate presentation is the same actual bundle, through
an explicit base-preserving linear homeomorphism of total spaces. -/
def finiteCoordinateTotalHomeomorph :
    TotalSpace (EuclideanSpace ℂ S) (SmoothLineSumBundle K label) ≃ₜ
      TotalSpace (Fin d → ℂ) (FiniteCoordinateBundle K label d hd) :=
  changeModelCoreTotalHomeomorph _ _

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {S ι : Type*} [Fintype S] [Fintype ι]
  (K : ι → ℕ) (label : S → Option ι) (d : ℕ) (hd : Fintype.card S=d)

/-- Pull back the Hilbert norm, keeping the already constructed fiber topology. -/
instance (priority := 2000) finiteCoordinateHilbertNorm (P : ProjectiveProduct K) :
    NormedAddCommGroup (FiniteCoordinateBundle K label d hd P) := by
  let e := (finiteCoordinateEquiv d hd).symm
  let N := NormedAddCommGroup.induced (FiniteCoordinateBundle K label d hd P)
    (EuclideanSpace ℂ S) e.toLinearEquiv.toAddEquiv e.injective
  exact { N.replaceTopology e.toHomeomorph.isInducing.eq_induced with
    norm := N.norm
    dist_eq := N.dist_eq }

instance (priority := 2000) finiteCoordinateHilbertInner (P : ProjectiveProduct K) :
    InnerProductSpace ℂ (FiniteCoordinateBundle K label d hd P) := by
  let e : FiniteCoordinateBundle K label d hd P ≃ₗ[ℂ] EuclideanSpace ℂ S :=
    (finiteCoordinateEquiv d hd).symm.toLinearEquiv
  exact
    { norm_smul_le := fun z v => by
        change ‖e (z • v)‖ ≤ ‖z‖ * ‖e v‖
        rw [map_smul, norm_smul]
      inner := fun v w => inner ℂ (e v) (e w)
      add_left := fun v w z => by simp only [map_add, inner_add_left]
      smul_left := fun v w z => by simp only [map_smul, inner_smul_left]
      norm_sq_eq_re_inner := fun v => norm_sq_eq_re_inner (e v)
      conj_inner_symm := fun v w => inner_conj_symm _ _ }

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Fresh bundle maps and assembly of the test-bundle step. -/

section
open Bundle Topology Module
open scoped Manifold ContDiff
namespace Kaplansky
open ComplexGrassmann

theorem testBundleSlot_card {m R j : ℕ} (hj : j≤R) :
    Fintype.card (TestBundleSlot m R j) = testRank m R j := by
  simpa [TestBundleSlot] using (sum_testMultiplicity (m := m) hj)

abbrev TestSourceCoordinates (m R j : ℕ) (hj : j<R) :=
  FiniteCoordinateBundle (stageProjectiveDimensions m R (j+1) hj)
    (fun s : TestBundleSlot m R j => testSummandLineIndex (Nat.le_succ j) s.1)
    (testRank m R j) (testBundleSlot_card (Nat.le_of_lt hj))

abbrev TestFreshRank (m R j : ℕ) := testMultiplicity m R (j+1) (Fin.last (j+1))

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

abbrev TestNextSlot (m R j : ℕ) :=
  (Σ i : Fin (j+1), Fin (testReplacementMultiplicity m R j i)) ⊕ Fin (TestFreshRank m R j)

def testNextLabel (m R j : ℕ) : TestNextSlot m R j → Option (Fin (j+1)) :=
  Sum.elim (fun s => testSummandLineIndex (Nat.le_succ j) s.1) (fun _ => some (Fin.last j))

theorem testNextSlot_card {m R j : ℕ} (hj : j<R) :
    Fintype.card (TestNextSlot m R j) = testRank m R (j+1) := by
  have h := sum_testMultiplicity (m := m) hj
  rw [Fin.sum_univ_castSucc] at h
  change Fintype.card ((Σ i : Fin (j+1), Fin (testReplacementMultiplicity m R j i)) ⊕
    Fin (TestFreshRank m R j)) = _
  rw [Fintype.card_sum, Fintype.card_sigma]
  calc
    _ = (∑ i : Fin (j+1), testReplacementMultiplicity m R j i) + TestFreshRank m R j := by
      apply congrArg₂ (fun a b : ℕ => a + b)
      · exact Finset.sum_congr rfl (fun i _ => Fintype.card_fin _)
      · exact Fintype.card_fin _
    _ = _ := h

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Descent of canonical scaling and Hermitian bundle homomorphisms. -/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky
variable {n d r : ℕ} {Y : Type*} [TopologicalSpace Y]
variable {E F : Y → Type*}
variable [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [∀ y, NormedAddCommGroup (F y)] [∀ y, InnerProductSpace ℂ (F y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]
variable [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
variable [FiberBundle (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
variable [FiberBundle (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]

def hermitianChartSet (a : Y) : Set Y :=
  (trivializationAt (Fin d → ℂ) E a).baseSet ∩ (trivializationAt (Fin r → ℂ) F a).baseSet

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Coordinates and realization of Hermitian scaling sections. -/

section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky
variable {n d r : ℕ} {Y : Type*} [TopologicalSpace Y]
variable {E F : Y → Type*}
variable [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [∀ y, NormedAddCommGroup (F y)] [∀ y, InnerProductSpace ℂ (F y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]
variable [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
variable [FiberBundle (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
variable [FiberBundle (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]

/-- Coordinates of genuine fiber maps in the constructed orthonormal frames. -/
def bundleMapCoordinates (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (a y : Y) :
    Fin n → Matrix (Fin r) (Fin d) ℂ :=
  fun i k j => inner ℂ
    (bundleOrthonormalFrame (trivializationAt (Fin r → ℂ) F a) y k)
    (T y i (bundleOrthonormalFrame (trivializationAt (Fin d → ℂ) E a) y j))

end Kaplansky

end

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Maps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Continuous bundle maps, adjoints, and normalized Hermitian scaling. -/

section
open Bundle Topology
namespace Kaplansky
variable {𝕜 Y V X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace Y] [TopologicalSpace X]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module 𝕜 (E y)]
variable [∀ y, TopologicalSpace (E y)] [TopologicalSpace (TotalSpace V E)]
variable [FiberBundle V E] [VectorBundle 𝕜 V E]

theorem continuousOn_bundle_smul_over (b : X → Y) {s : Set X} (hb : ContinuousOn b s)
    (f : X → 𝕜) (v : ∀ x, E (b x)) (hf : ContinuousOn f s)
    (hv : ContinuousOn (fun x => TotalSpace.mk' V (b x) (v x)) s) :
    ContinuousOn (fun x => TotalSpace.mk' V (b x) (f x • v x)) s := by
  intro x hx
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨hb x hx, ?_⟩
  have hc := (hf x hx).smul
    (((FiberBundle.continuousWithinAt_totalSpace V _).mp (hv x hx)).2)
  apply hc.congr_of_eventuallyEq
  · have hn := (trivializationAt V E (b x)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt V E (b x))
    filter_upwards [(hb x hx) hn] with z hz
    exact ((trivializationAt V E (b x)).linear 𝕜 hz).map_smul (f z) (v z)
  · exact ((trivializationAt V E (b x)).linear 𝕜
      (mem_baseSet_trivializationAt V E (b x))).map_smul (f x) (v x)

end Kaplansky

end

section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky
variable {n d r : ℕ} {Y : Type*} [TopologicalSpace Y]
variable {E F : Y → Type*}
variable [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [∀ y, NormedAddCommGroup (F y)] [∀ y, InnerProductSpace ℂ (F y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]
variable [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
variable [FiberBundle (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
variable [FiberBundle (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]

include d in
/-- Finite-dimensionality is derived from the ordinary bundle chart. -/
theorem bundleFiberFiniteDimensional (y : Y) : FiniteDimensional ℂ (E y) :=
  Module.Finite.of_basis (bundleChartBasis (trivializationAt (Fin d → ℂ) E y) y
    (mem_baseSet_trivializationAt (Fin d → ℂ) E y))

/-- The actual fiberwise adjoint, with finite-dimensionality supplied by
the original bundle rather than a new hypothesis. -/
def bundleAdjoint (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (y : Y) (i : Fin n) : F y →ₗ[ℂ] E y := by
  letI := bundleFiberFiniteDimensional (d := d) (E := E) y
  letI := bundleFiberFiniteDimensional (d := r) (E := F) y
  exact LinearMap.adjoint (T y i)

theorem bundleAdjoint_inner (T : ∀ y, Fin n → E y →ₗ[ℂ] F y)
    (y : Y) (i : Fin n) (v : E y) (w : F y) :
    inner ℂ (bundleAdjoint (d := d) (r := r) T y i w) v = inner ℂ w (T y i v) := by
  let := bundleFiberFiniteDimensional (d := d) (E := E) y
  let := bundleFiberFiniteDimensional (d := r) (E := F) y
  exact LinearMap.adjoint_inner_left (T y i) v w

end Kaplansky

end

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Tuples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Normalized Hermitian tuples, doubling, and unitary equivalence. -/

section
open scoped BigOperators ComplexOrder
namespace Kaplansky

/-- A normalized tuple with the adjoint identity proved for its displayed
reverse maps. No existence or topological obstruction is assumed here. -/
structure NormalizedHermitianTuple (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] where
  forward : Fin 24 → E →ₗ[ℂ] F
  reverse : Fin 24 → F →ₗ[ℂ] E
  adjoint_inner : ∀ i v w, inner ℂ (reverse i w) v = inner ℂ w (forward i v)
  column : ∑ i, (reverse i).comp (forward i) = LinearMap.id
  row : ∀ w, 0 ≤ inner ℂ w (((2/3 : ℂ) • (LinearMap.id : F →ₗ[ℂ] F) -
    ∑ i, (forward i).comp (reverse i)) w)

namespace NormalizedHermitianTuple
variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-- Transport the actual tuple and its actual adjoints through unitary
coordinates. The row and column identities are preserved. -/
def congr (T : NormalizedHermitianTuple E F)
    (e : E ≃ₗᵢ[ℂ] E') (f : F ≃ₗᵢ[ℂ] F') : NormalizedHermitianTuple E' F' where
  forward i := f.toLinearEquiv.toLinearMap.comp ((T.forward i).comp e.symm.toLinearEquiv.toLinearMap)
  reverse i := e.toLinearEquiv.toLinearMap.comp ((T.reverse i).comp f.symm.toLinearEquiv.toLinearMap)
  adjoint_inner i v w := by
    change inner ℂ (e (T.reverse i (f.symm w))) v = inner ℂ w (f (T.forward i (e.symm v)))
    rw [← e.apply_symm_apply v, e.inner_map_map]
    rw [← f.apply_symm_apply w, f.inner_map_map]
    simp only [LinearIsometryEquiv.symm_apply_apply]
    exact T.adjoint_inner i (e.symm v) (f.symm w)
  column := by
    ext v
    have h := congrArg (fun a : E →ₗ[ℂ] E => e (a (e.symm v))) T.column
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply,
      map_sum, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply] using h
  row w := by
    have h := T.row (f.symm w)
    have he : inner ℂ w
        (((2/3 : ℂ) • (LinearMap.id : F' →ₗ[ℂ] F') -
          ∑ i, (f.toLinearEquiv.toLinearMap.comp ((T.forward i).comp e.symm.toLinearEquiv.toLinearMap)).comp
            (e.toLinearEquiv.toLinearMap.comp ((T.reverse i).comp f.symm.toLinearEquiv.toLinearMap))) w) =
        inner ℂ (f.symm w) (((2/3 : ℂ) • (LinearMap.id : F →ₗ[ℂ] F) -
          ∑ i, (T.forward i).comp (T.reverse i)) (f.symm w)) := by
      rw [← f.inner_map_map]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        LinearMap.sum_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
        LinearIsometryEquiv.apply_symm_apply, map_sub, map_smul, map_sum]
    exact he ▸ h

end NormalizedHermitianTuple
end Kaplansky

end

section
open Bundle
namespace Kaplansky
variable {B : Type*} [TopologicalSpace B]

/-- A fiberwise unitary equivalence compatible with the actual total-space
topologies, even when the bundle models use different coordinates. -/
structure UnitaryBundleEquiv (U V : Type*) (E F : B → Type*)
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
    [TopologicalSpace (TotalSpace U E)] [TopologicalSpace (TotalSpace V F)] where
  fiber : ∀ x, E x ≃ₗᵢ[ℂ] F x
  continuous_forward : Continuous (fun z : TotalSpace U E => TotalSpace.mk' V z.proj (fiber z.proj z.2))
  continuous_reverse : Continuous (fun z : TotalSpace V F => TotalSpace.mk' U z.proj ((fiber z.proj).symm z.2))

namespace UnitaryBundleEquiv
variable {U V W : Type*} {E F G : B → Type*}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
    [∀ x, NormedAddCommGroup (G x)] [∀ x, InnerProductSpace ℂ (G x)]
    [TopologicalSpace (TotalSpace U E)] [TopologicalSpace (TotalSpace V F)]
    [TopologicalSpace (TotalSpace W G)]

def symm (e : UnitaryBundleEquiv U V E F) : UnitaryBundleEquiv V U F E where
  fiber x := (e.fiber x).symm
  continuous_forward := e.continuous_reverse
  continuous_reverse := e.continuous_forward

def trans (e : UnitaryBundleEquiv U V E F) (f : UnitaryBundleEquiv V W F G) :
    UnitaryBundleEquiv U W E G where
  fiber x := (e.fiber x).trans (f.fiber x)
  continuous_forward := f.continuous_forward.comp e.continuous_forward
  continuous_reverse := e.continuous_reverse.comp f.continuous_reverse
end UnitaryBundleEquiv

/-- The normalized maps and their true adjoints vary continuously over the
specified ordinary topological bundles. -/
structure ContinuousNormalizedStep (U V : Type*) (E F : B → Type*)
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
    [TopologicalSpace (TotalSpace U E)] [TopologicalSpace (TotalSpace V F)] where
  tuple : ∀ x, NormalizedHermitianTuple (E x) (F x)
  continuous_forward : ∀ i, Continuous (fun z : TotalSpace U E =>
    TotalSpace.mk' V z.proj ((tuple z.proj).forward i z.2))
  continuous_reverse : ∀ i, Continuous (fun z : TotalSpace V F =>
    TotalSpace.mk' U z.proj ((tuple z.proj).reverse i z.2))

namespace ContinuousNormalizedStep
variable {U V U' V' : Type*} {E F E' F' : B → Type*}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
    [∀ x, NormedAddCommGroup (E' x)] [∀ x, InnerProductSpace ℂ (E' x)]
    [∀ x, NormedAddCommGroup (F' x)] [∀ x, InnerProductSpace ℂ (F' x)]
    [TopologicalSpace (TotalSpace U E)] [TopologicalSpace (TotalSpace V F)]
    [TopologicalSpace (TotalSpace U' E')] [TopologicalSpace (TotalSpace V' F')]

def congr (T : ContinuousNormalizedStep U V E F)
    (e : UnitaryBundleEquiv U U' E E') (f : UnitaryBundleEquiv V V' F F') :
    ContinuousNormalizedStep U' V' E' F' where
  tuple x := (T.tuple x).congr (e.fiber x) (f.fiber x)
  continuous_forward i := f.continuous_forward.comp ((T.continuous_forward i).comp e.continuous_reverse)
  continuous_reverse i := e.continuous_forward.comp ((T.continuous_reverse i).comp f.continuous_reverse)

end ContinuousNormalizedStep
end Kaplansky

end

open scoped BigOperators ComplexOrder
namespace Kaplansky

def twoOfTwentyFour {A : Type*} [Zero A] (a b : A) (i : Fin 24) : A :=
  if i=0 then a else if i=1 then b else 0

theorem sum_twoOfTwentyFour {A : Type*} [AddCommMonoid A] (a b : A) :
    ∑ i : Fin 24, twoOfTwentyFour a b i = a+b := by
  simp [twoOfTwentyFour, Finset.sum_ite, Finset.filter_eq']

def doublingScale : ℂ := (Real.sqrt (1/2 : ℝ) : ℂ)

theorem doublingScale_sq : doublingScale * doublingScale = (1/2 : ℂ) := by
  rw [doublingScale, ← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (by norm_num)]
  norm_num

/-- Two scaled orthogonal inclusions, padded by twenty-two zero maps.
These algebraic hypotheses are discharged by the actual sum coordinates. -/
def doublingTuple {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (I₀ I₁ : E →ₗ[ℂ] F) (P₀ P₁ : F →ₗ[ℂ] E)
    (h₀ : ∀ v w, inner ℂ (P₀ w) v = inner ℂ w (I₀ v))
    (h₁ : ∀ v w, inner ℂ (P₁ w) v = inner ℂ w (I₁ v))
    (hP₀ : P₀.comp I₀ = LinearMap.id) (hP₁ : P₁.comp I₁ = LinearMap.id)
    (hI : I₀.comp P₀ + I₁.comp P₁ = LinearMap.id) : NormalizedHermitianTuple E F where
  forward := twoOfTwentyFour (doublingScale • I₀) (doublingScale • I₁)
  reverse := twoOfTwentyFour (doublingScale • P₀) (doublingScale • P₁)
  adjoint_inner i v w := by
    by_cases hi : i=0
    · simp [twoOfTwentyFour,hi,inner_smul_left,inner_smul_right,doublingScale,h₀] <;> ring
    · by_cases hj : i=1
      · simp [twoOfTwentyFour,hj,inner_smul_left,inner_smul_right,doublingScale,h₁] <;> ring
      · simp [twoOfTwentyFour,hi,hj]
  column := by
    have he : (fun i => (twoOfTwentyFour (doublingScale • P₀) (doublingScale • P₁) i).comp
        (twoOfTwentyFour (doublingScale • I₀) (doublingScale • I₁) i)) =
        twoOfTwentyFour ((1/2 : ℂ) • LinearMap.id) ((1/2 : ℂ) • (LinearMap.id : E →ₗ[ℂ] E)) := by
      funext i
      by_cases hi : i=0
      · simp [twoOfTwentyFour,hi,LinearMap.smul_comp,LinearMap.comp_smul,smul_smul,doublingScale_sq,hP₀]
      · by_cases hj : i=1
        · simp [twoOfTwentyFour,hj,LinearMap.smul_comp,LinearMap.comp_smul,smul_smul,doublingScale_sq,hP₁]
        · simp [twoOfTwentyFour,hi,hj]
    rw [he,sum_twoOfTwentyFour,← add_smul]
    norm_num
  row w := by
    have he : (fun i => (twoOfTwentyFour (doublingScale • I₀) (doublingScale • I₁) i).comp
        (twoOfTwentyFour (doublingScale • P₀) (doublingScale • P₁) i)) =
        twoOfTwentyFour ((1/2 : ℂ) • I₀.comp P₀) ((1/2 : ℂ) • I₁.comp P₁) := by
      funext i
      by_cases hi : i=0
      · simp [twoOfTwentyFour,hi,LinearMap.smul_comp,LinearMap.comp_smul,smul_smul,doublingScale_sq]
      · by_cases hj : i=1
        · simp [twoOfTwentyFour,hj,LinearMap.smul_comp,LinearMap.comp_smul,smul_smul,doublingScale_sq]
        · simp [twoOfTwentyFour,hi,hj]
    rw [he,sum_twoOfTwentyFour,← smul_add,hI,← sub_smul]
    have hh : (2/3 : ℂ)-(1/2 : ℂ)=1/6 := by norm_num
    rw [hh,LinearMap.smul_apply,LinearMap.id_apply,inner_smul_right]
    exact mul_nonneg (by simp) (by simp)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Normalized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Normalized test maps, slot regrouping, and unitary coordinate changes. -/

section
open Bundle Topology
open scoped BigOperators ComplexOrder
namespace Kaplansky
open ComplexGrassmann

abbrev TestNextCoordinates (m R j : ℕ) (hj : j<R) :=
  FiniteCoordinateBundle (stageProjectiveDimensions m R (j+1) hj)
    (testNextLabel m R j) (testRank m R (j+1)) (testNextSlot_card hj)

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

/-- The finite-coordinate change preserves the actual Hermitian metric and
the actual total-space topology simultaneously. -/
def finiteCoordinateUnitary {S ι : Type*} [Fintype S] [Fintype ι]
    (K : ι → ℕ) (label : S → Option ι) (d : ℕ) (hd : Fintype.card S=d) :
    UnitaryBundleEquiv (EuclideanSpace ℂ S) (Fin d → ℂ)
      (SmoothLineSumBundle K label) (FiniteCoordinateBundle K label d hd) where
  fiber x :=
    { toLinearEquiv := (finiteCoordinateEquiv d hd).toLinearEquiv
      norm_map' := fun v => by
        change ‖(finiteCoordinateEquiv d hd).symm (finiteCoordinateEquiv d hd v)‖ = ‖v‖
        exact congrArg norm ((finiteCoordinateEquiv d hd).symm_apply_apply
          (show EuclideanSpace ℂ S from v)) }
  continuous_forward := (finiteCoordinateTotalHomeomorph K label d hd).continuous
  continuous_reverse := (finiteCoordinateTotalHomeomorph K label d hd).symm.continuous

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

local instance (priority := 2100) coordinateSourceNorm (m R j : ℕ) (hj : j<R)
    (y : SmoothPrefixBase m R j hj) : NormedAddCommGroup (TestSourceCoordinates m R j hj y) :=
  finiteCoordinateHilbertNorm _ _ _ _ y
local instance (priority := 2100) coordinateSourceInner (m R j : ℕ) (hj : j<R)
    (y : SmoothPrefixBase m R j hj) : InnerProductSpace ℂ (TestSourceCoordinates m R j hj y) :=
  finiteCoordinateHilbertInner _ _ _ _ y
local instance (priority := 2100) coordinateNextNorm (m R j : ℕ) (hj : j<R)
    (y : SmoothPrefixBase m R j hj) : NormedAddCommGroup (TestNextCoordinates m R j hj y) :=
  finiteCoordinateHilbertNorm _ _ _ _ y
local instance (priority := 2100) coordinateNextInner (m R j : ℕ) (hj : j<R)
    (y : SmoothPrefixBase m R j hj) : InnerProductSpace ℂ (TestNextCoordinates m R j hj y) :=
  finiteCoordinateHilbertInner _ _ _ _ y

def TestCoordinateStepType (m R j : ℕ) (hj : j<R) : Type :=
    @ContinuousNormalizedStep (SmoothPrefixBase m R j hj)
      (Fin (testRank m R j) → ℂ) (Fin (testRank m R (j+1)) → ℂ)
      (TestSourceCoordinates m R j hj) (TestNextCoordinates m R j hj)
      (coordinateSourceNorm m R j hj) (coordinateSourceInner m R j hj)
      (coordinateNextNorm m R j hj) (coordinateNextInner m R j hj)
      inferInstance inferInstance

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_LineStage
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Doubling stages of line bundles and their Hilbert direct sums. -/

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

section Continuity
variable {B U V : Type*} [TopologicalSpace B]
    [NormedAddCommGroup U] [NormedAddCommGroup V] [NormedSpace ℂ V]
    {E F : B → Type*}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
    [TopologicalSpace (TotalSpace U E)] [TopologicalSpace (TotalSpace V F)]
    [FiberBundle U E]
    [FiberBundle V F] [VectorBundle ℂ V F]

theorem continuous_twoScaled (T₀ T₁ : ∀ x, E x →ₗ[ℂ] F x)
    (h₀ : Continuous (fun z : TotalSpace U E => TotalSpace.mk' V z.proj (T₀ z.proj z.2)))
    (h₁ : Continuous (fun z : TotalSpace U E => TotalSpace.mk' V z.proj (T₁ z.proj z.2)))
    (c : ℂ) (i : Fin 24) :
    Continuous (fun z : TotalSpace U E => TotalSpace.mk' V z.proj
      (twoOfTwentyFour (c • T₀ z.proj) (c • T₁ z.proj) i z.2)) := by
  have hs (d : ℂ) (T : ∀ x, E x →ₗ[ℂ] F x)
      (hT : Continuous (fun z : TotalSpace U E => TotalSpace.mk' V z.proj (T z.proj z.2))) :
      Continuous (fun z : TotalSpace U E => TotalSpace.mk' V z.proj (d • T z.proj z.2)) :=
    continuousOn_univ.mp (continuousOn_bundle_smul_over (fun z : TotalSpace U E => z.proj)
      (FiberBundle.continuous_proj U E).continuousOn (fun _ => d)
      (fun z => T z.proj z.2) continuousOn_const hT.continuousOn)
  by_cases h : i=0
  · simpa [twoOfTwentyFour,h] using hs c T₀ h₀
  · by_cases h' : i=1
    · simpa [twoOfTwentyFour,h,h'] using hs c T₁ h₁
    · simpa [twoOfTwentyFour,h,h'] using hs 0 T₀ h₀
end Continuity

def lineSumDoublingStep {ι S : Type*} [Fintype ι] [Fintype S]
    (K : ι → ℕ) (label : S → Option ι) :
    ContinuousNormalizedStep (EuclideanSpace ℂ S) (EuclideanSpace ℂ (S⊕S))
      (SmoothLineSumBundle K label) (SmoothLineSumBundle K (Sum.elim label label)) := by
  let L := fun u : S⊕S => productLineCore K (Sum.elim label label u)
  exact
    { tuple := fun x => doublingTuple (lineSumInl L x) (lineSumInr L x)
        (lineSumFst L x) (lineSumSnd L x)
        (lineSumFst_inner L x) (lineSumSnd_inner L x)
        (lineSumFst_comp_inl L x) (lineSumSnd_comp_inr L x) (lineSum_inl_fst_add_inr_snd L x)
      continuous_forward := continuous_twoScaled (lineSumInl L) (lineSumInr L)
        (continuous_lineSumInl L) (continuous_lineSumInr L) doublingScale
      continuous_reverse := continuous_twoScaled (lineSumFst L) (lineSumSnd L)
        (continuous_lineSumFst L) (continuous_lineSumSnd L) doublingScale }

/-- A finite list of actual projective-product line bundles. -/
structure LineStage {ι : Type*} (K : ι → ℕ) where
  Slot : Type
  finiteSlot : Fintype Slot
  label : Slot → Option ι

attribute [instance] LineStage.finiteSlot

namespace LineStage
variable {ι : Type*} [Fintype ι] {K : ι → ℕ}

abbrev Model (a : LineStage K) := EuclideanSpace ℂ a.Slot
abbrev Fiber (a : LineStage K) := SmoothLineSumBundle K a.label

abbrev Step (a b : LineStage K) := ContinuousNormalizedStep a.Model b.Model a.Fiber b.Fiber

def double (a : LineStage K) : LineStage K :=
  ⟨a.Slot⊕a.Slot,inferInstance,Sum.elim a.label a.label⟩

def doublingStep (a : LineStage K) : a.Step a.double := lineSumDoublingStep K a.label

def tail (a : LineStage K) : ℕ → LineStage K
  | 0 => a
  | n+1 => (tail a n).double

def tailStep (a : LineStage K) (n : ℕ) : (a.tail n).Step (a.tail (n+1)) :=
  (a.tail n).doublingStep

end LineStage
end Kaplansky

end

section
open Bundle Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Kaplansky
open ComplexGrassmann
namespace LineStage
variable {ι : Type*} {J : Type} [Fintype J] {K : ι → ℕ}

def sum (a : J → LineStage K) : LineStage K :=
  ⟨Σ j : J, (a j).Slot, inferInstance, fun (s : Σ j : J, (a j).Slot) => (a s.1).label s.2⟩

def sumProj (a : J → LineStage K) (j : J) (y : ProjectiveProduct K) :
    (sum a).Fiber y →ₗ[ℂ] (a j).Fiber y where
  toFun v := WithLp.toLp 2 (fun s => (show (sum a).Model from v) ⟨j,s⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def sumInj (a : J → LineStage K) (j : J) (y : ProjectiveProduct K) :
    (a j).Fiber y →ₗ[ℂ] (sum a).Fiber y where
  toFun v := WithLp.toLp 2 (fun s => if h : s.1 = j then
    (show (a j).Model from v) (h ▸ s.2) else 0)
  map_add' v w := by
    apply (EuclideanSpace.equiv _ ℂ).injective
    funext s
    change (if h : s.1=j then (show (a j).Model from v) (h ▸ s.2) +
      (show (a j).Model from w) (h ▸ s.2) else 0) =
      (if h : s.1=j then (show (a j).Model from v) (h ▸ s.2) else 0) +
      (if h : s.1=j then (show (a j).Model from w) (h ▸ s.2) else 0)
    by_cases h : s.1=j <;> simp [h]
  map_smul' c v := by
    apply (EuclideanSpace.equiv _ ℂ).injective
    funext s
    change (if h : s.1=j then c • (show (a j).Model from v) (h ▸ s.2) else 0) =
      c • (if h : s.1=j then (show (a j).Model from v) (h ▸ s.2) else 0)
    by_cases h : s.1=j <;> simp [h]

@[simp] theorem sumProj_sumInj_same (a : J → LineStage K) (j : J)
    (y : ProjectiveProduct K) (v : (a j).Fiber y) :
    sumProj a j y (sumInj a j y v) = v := by
  apply (EuclideanSpace.equiv _ ℂ).injective
  funext s
  change (if h : j = j then (show (a j).Model from v) (h ▸ s) else 0) =
    (show (a j).Model from v) s
  exact dite_eq_left rfl

@[simp] theorem sumProj_sumInj_ne (a : J → LineStage K) {j k : J} (h : k≠j)
    (y : ProjectiveProduct K) (v : (a j).Fiber y) :
    sumProj a k y (sumInj a j y v) = 0 := by
  apply (EuclideanSpace.equiv _ ℂ).injective
  funext s
  change (if h : k = j then (show (a j).Model from v) (h ▸ s) else 0) = 0
  exact dite_eq_right h

end LineStage
end Kaplansky

end

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Sequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Prefix and full test steps, pullbacks, and the infinite test sequence. -/

section
open Bundle Topology
namespace Kaplansky

section
open ComplexGrassmann

/-- Pull continuous normalized maps from a projective subproduct to the
full product. Continuity uses the actual line-sum pullback topology. -/
def lineSumPullbackStep {ι κ S T : Type*} [Fintype ι] [Fintype κ] [Fintype S] [Fintype T]
    (K : κ → ℕ) (f : ι → κ) (a : S → Option ι) (b : T → Option ι)
    (X : ContinuousNormalizedStep (EuclideanSpace ℂ S) (EuclideanSpace ℂ T)
      (SmoothLineSumBundle (fun i => K (f i)) a) (SmoothLineSumBundle (fun i => K (f i)) b)) :
    ContinuousNormalizedStep (EuclideanSpace ℂ S) (EuclideanSpace ℂ T)
      (SmoothLineSumBundle K (fun s => (a s).map f))
      (SmoothLineSumBundle K (fun t => (b t).map f)) where
  tuple x := X.tuple (projectiveRestrict K f x)
  continuous_forward i := by
    let g := fun z : TotalSpace (EuclideanSpace ℂ S)
      (SmoothLineSumBundle K (fun s => (a s).map f)) => z.proj
    have hg : Continuous g := FiberBundle.continuous_proj _ _
    have hin := (continuous_lineSum_restrict_iff K f a g (fun z => z.2) hg).mp continuous_id
    exact (continuous_lineSum_restrict_iff K f b g
      (fun z => (X.tuple (projectiveRestrict K f z.proj)).forward i z.2) hg).mpr
      ((X.continuous_forward i).comp hin)
  continuous_reverse i := by
    let g := fun z : TotalSpace (EuclideanSpace ℂ T)
      (SmoothLineSumBundle K (fun t => (b t).map f)) => z.proj
    have hg : Continuous g := FiberBundle.continuous_proj _ _
    have hin := (continuous_lineSum_restrict_iff K f b g (fun z => z.2) hg).mp continuous_id
    exact (continuous_lineSum_restrict_iff K f a g
      (fun z => (X.tuple (projectiveRestrict K f z.proj)).reverse i z.2) hg).mpr
      ((X.continuous_reverse i).comp hin)

attribute [local irreducible] bundleAdjoint finiteCoordinateEquiv

end

open ComplexGrassmann

/-- A single coherent presentation of the finite stages on full Y. -/
abbrev FullTestBundle (m R j : ℕ) (hj : j≤R) :=
  SmoothTestBundle m R R j (Nat.le_refl R) hj

def testLineStage (m R j : ℕ) (hj : j≤R) : LineStage (testProjectiveDimension m R) :=
  ⟨TestBundleSlot m R j,inferInstance,fun s => testSummandLineIndex hj s.1⟩

def testSequenceStage (m R : ℕ) (j : ℕ) : LineStage (testProjectiveDimension m R) :=
  if h : j≤R then testLineStage m R j h
  else (testLineStage m R R (Nat.le_refl R)).tail (j-R)

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.StdSimplexCompat
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

namespace Convexity

namespace StdSimplex

section Semiring

variable {R : Type u} [PartialOrder R] [Semiring R] {X Y Z : Type*}

@[simp]
lemma total_of_fintype [Fintype X] (w : StdSimplex R X) :
    ∑ i, w.weights i = 1 := by
  have := w.total
  rwa [Finsupp.sum_fintype _ _ (by simp)] at this

@[simp]
lemma total_fin_two (w : StdSimplex R (Fin 2)) :
    w.weights 0 + w.weights 1 = 1 := by
  rw [← w.total_of_fintype, Fin.sum_univ_two]

@[simp]
lemma weights_apply_eq_one [Subsingleton X] (s : StdSimplex R X) (m : X) :
    s.weights m = 1 := by
  rw [← s.total, Finsupp.sum_eq_single m
    (fun _ _ h ↦ (h (by subsingleton)).elim) (by simp)]

instance instSubsingleton [Subsingleton X] : Subsingleton (StdSimplex R X) where
  allEq := by
    intro a b
    ext m
    simp

variable [IsStrictOrderedRing R]

@[simp]
lemma weights_apply_le_one
    (s : StdSimplex R X) (m : X) : s.weights m ≤ 1 := by
  by_cases hm : s.weights m = 0
  · simpa only [hm] using zero_le_one' R
  · rw [← s.total, Finsupp.sum]
    exact Finset.single_le_sum (fun i _ => s.weights_nonneg i) (Finsupp.mem_support_iff.mpr hm)

instance instInhabited [Inhabited X] : Inhabited (StdSimplex R X) where
  default := .single default

instance instNonempty [Nonempty X] : Nonempty (StdSimplex R X) :=
  ⟨.single (Classical.arbitrary _)⟩

instance instUnique [Unique X] : Unique (StdSimplex R X) where
  uniq := by subsingleton

end Semiring

section

variable {R' : Type*} [Ring R'] [PartialOrder R'] [IsStrictOrderedRing R']

/-- The bijection between the one dimensional standard simplex and the interval `[0, 1]`. -/
@[simps -isSimp]
def equivIcc : StdSimplex R' (Fin 2) ≃ Set.Icc (0 : R') 1 where
  toFun s := ⟨s.weights 1, s.weights_nonneg 1, s.weights_apply_le_one 1⟩
  invFun t := duple (s := 1 - t) (t := t) 0 1 (sub_nonneg.mpr t.2.2) t.2.1 (by simp)
  left_inv s := by
    ext i
    fin_cases i
    · have := s.total_fin_two
      simp
      exact (eq_sub_of_add_eq this).symm
    · simp
  right_inv t := by
    ext
    simp [Finsupp.single_apply]

attribute [local simp] equivIcc_apply_coe

@[simp]
lemma equivIcc_single_zero : equivIcc (.single (R := R') 0) = 0 := by
  ext
  simp [Finsupp.single_apply]

@[simp]
lemma equivIcc_single_one : equivIcc (.single (R := R') 1) = 1 := by
  ext
  simp

@[simp]
lemma equivIcc_symm_zero : equivIcc.symm 0 = .single (R := R') 0 :=
  equivIcc.injective (by simp)

@[simp]
lemma equivIcc_symm_one : equivIcc.symm 1 = .single (R := R') 1 :=
  equivIcc.injective (by simp)

end

section ConvexSpace

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {I : Type*}

@[simp]
lemma iConvexComb_single (x : StdSimplex R I) :
    x.iConvexComb single = x := by
  ext : 1
  simp [weights_iConvexComb, Finsupp.smul_single_one, Finsupp.sum_single]

end ConvexSpace

end StdSimplex

/-! ### Topology (Mathlib `d13f23b`, `Geometry/Convex/ConvexSpace/Topology.lean`) -/

namespace StdSimplex

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

/-- The topology on `StdSimplex R ι` that is induced by the embedding
`StdSimplex R ι → (ι → R)`. This is the correct topoplogy only when
`ι` is finite, see `StdSimplex.isEmbedding_toFun_comp_weights`. -/
abbrev topologicalSpaceInduced (ι : Type*) : TopologicalSpace (StdSimplex R ι) :=
  .induced (fun t ↦ t.weights : StdSimplex R ι → ι → R) inferInstance

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

@[fun_prop]
lemma continuous_weights_apply {ι : Type*} (i : ι) :
    Continuous (fun (t : StdSimplex R ι) ↦ t.weights i) :=
  (continuous_apply i).comp (by rw [continuous_iff_le_induced])

open Classical in
@[fun_prop]
lemma continuous_map_weights_apply
    [IsStrictOrderedRing R] [IsTopologicalRing R] {ι₁ ι₂ : Type*}
    [Finite ι₁] (f : ι₁ → ι₂) (i₂ : ι₂) :
    Continuous (fun t ↦ (map (R := R) f t).weights i₂) := by
  have := Fintype.ofFinite ι₁
  have (t : StdSimplex R ι₁) :
      (map (R := R) f t).weights i₂ =
        ∑ i₁ with f i₁ = i₂, t.weights i₁ := by
    rw [weights_map, Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp),
      Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply, Finset.sum_filter]
  simp only [this]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

attribute [local instance] topologicalSpaceInduced in
/-- The topology on `StdSimplex R M`: the supremum of the coinduced topologies for the maps
`StdSimplex.map f : StdSimplex R ι → StdSimplex R M` with `ι` finite. When `M` is finite it is the
topology induced by the embedding `StdSimplex R M → (M → R)`. -/
noncomputable instance topologicalSpace (M : Type v) :
    TopologicalSpace (StdSimplex R M) :=
  ⨆ (ι : Type v) (_ : Finite ι) (f : ι → M), .coinduced (map f) inferInstance

end StdSimplex

/-! ### Compactness (Mathlib `d13f23b`, `CompactSpaceStdSimplex.lean`) -/

/-! ### Barycenters (Mathlib `d13f23b`, `Barycenter.lean`) -/

namespace StdSimplex

variable {K M : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]

/-- In the standard simplex with vertices `M`, the barycenter of a nonempty finite subset `S`. -/
@[simps -isSimp]
noncomputable def subBarycenter (S : Finset M) (hS : S.Nonempty) : StdSimplex K M where
  weights := S.sum (fun m ↦ .single m (S.card : K)⁻¹)
  nonneg := Finset.sum_nonneg (fun m _ => by
    classical
    intro i
    rw [Finsupp.single_apply]
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl)
  total := by
    rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
    simp only [Finsupp.sum_single_index, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Finset.card_pos.mpr hS).ne')

@[simp]
lemma subBarycenter_singleton (m : M) :
    subBarycenter (K := K) {m} (by simp) = .single m := by
  ext
  simp [weights_subBarycenter]

end StdSimplex

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

end Convexity

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

end StdSimplexCompat
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Twisted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Twisted hyperplane bundles, zeros, graph coordinates, and frame sections. -/

section
open Bundle Topology
namespace Kaplansky

section
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

abbrev TwistedHyperplaneSlot := Fin h ⊕ (Σ i, Fin (K i))

end

open ComplexGrassmann

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_Shift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert shifts, their relations, and block operator bounds. -/

noncomputable section
open scoped BigOperators ENNReal
namespace Kaplansky
variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)]

abbrev FiberHilbertSum (E : ℕ → Type*) [∀ j, NormedAddCommGroup (E j)] := lp E 2

def levelInclusion (j : ℕ) : E j →ₗᵢ[ℂ] FiberHilbertSum E where
  toLinearMap := lp.lsingle 2 j
  norm_map' v := lp.norm_single (by norm_num) j v

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_Words
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word propagation through Hilbert shifts and normalized tuple operators. -/

noncomputable section
open scoped BigOperators ComplexOrder
namespace Kaplansky.NormalizedHermitianTuple
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

local instance instCompleteSpace_rc43edd_1 : CompleteSpace E := FiniteDimensional.complete ℂ E
local instance instCompleteSpace_1_rc43edd_1 : CompleteSpace F := FiniteDimensional.complete ℂ F
/-- Actual bounded operators on the finite-dimensional Hilbert fibers. -/
def operator (T : NormalizedHermitianTuple E F) (i : Fin 24) : E →L[ℂ] F :=
  (T.forward i).toContinuousLinearMap

end Kaplansky.NormalizedHermitianTuple

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_BundleWords
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Continuous bundle words and their finite-tower Hilbert realization. -/

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} {K : ι → ℕ}

section WordValues

/-- One monomial restricted to the bottom level, as an actual continuous
bundle map into its single output level. -/
structure BundleWordValue (a : ℕ → LineStage K) where
  level : ℕ
  map : ∀ y, (a 0).Fiber y →ₗ[ℂ] (a level).Fiber y
  continuous_map : Continuous (fun z : TotalSpace (a 0).Model (a 0).Fiber =>
    TotalSpace.mk' (a level).Model z.proj (map z.proj z.2))

namespace BundleWordValue
variable {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1)))

def raise (W : BundleWordValue a) (i : Fin 24) : BundleWordValue a where
  level := W.level+1
  map y := ((X W.level).tuple y).forward i |>.comp (W.map y)
  continuous_map := ((X W.level).continuous_forward i).comp W.continuous_map

def lower (W : BundleWordValue a) (i : Fin 24) : BundleWordValue a := by
  obtain ⟨k,T,hT⟩ := W
  cases k with
  | zero =>
    refine ⟨0,fun _ => 0,?_⟩
    exact (Bundle.Trivialization.continuous_zeroSection ℂ (F := (a 0).Model) (E := (a 0).Fiber)).comp
      (FiberBundle.continuous_proj (a 0).Model (a 0).Fiber)
  | succ k =>
    exact ⟨k,fun y => ((X k).tuple y).reverse i |>.comp (T y),
      ((X k).continuous_reverse i).comp hT⟩

@[simp] theorem raise_level (W : BundleWordValue a) (i : Fin 24) : (raise X W i).level = W.level+1 := rfl
@[simp] theorem lower_level (W : BundleWordValue a) (i : Fin 24) : (lower X W i).level = W.level-1 := by
  obtain ⟨k,T,hT⟩ := W
  cases k <;> rfl
end BundleWordValue

end WordValues

open scoped BigOperators

/-- The finite retained tower embeds into the actual Hilbert direct sum. -/
def finiteTowerHilbert (a : ℕ → LineStage K) (R : ℕ) (y : ProjectiveProduct K) :
    (LineStage.sum (fun j : Fin (R+1) => a j.val)).Fiber y →ₗ[ℂ]
      lp (fun j => (a j).Fiber y) 2 where
  toFun v := ∑ j : Fin (R+1), lp.single (E := fun j => (a j).Fiber y) 2 j.val
    (LineStage.sumProj (fun k : Fin (R+1) => a k.val) j y v)
  map_add' v w := by
    simp only [map_add]
    exact (Finset.sum_congr rfl (fun j _ =>
      lp.single_add (E := fun j => (a j).Fiber y) 2 j.val _ _)).trans
      (Finset.sum_add_distrib)
  map_smul' c v := by
    simp only [map_smul, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun j _ =>
      lp.single_smul (E := fun j => (a j).Fiber y) 2 j.val c _)

@[simp] theorem finiteTowerHilbert_inj (a : ℕ → LineStage K) (R : ℕ)
    (y : ProjectiveProduct K) (j : Fin (R+1)) (v : (a j.val).Fiber y) :
    finiteTowerHilbert a R y (LineStage.sumInj (fun k : Fin (R+1) => a k.val) j y v) =
      lp.single (E := fun j => (a j).Fiber y) 2 j.val v := by
  classical
  change (∑ k : Fin (R+1), lp.single (E := fun j => (a j).Fiber y) 2 k.val
    (LineStage.sumProj (fun k : Fin (R+1) => a k.val) k y
      (LineStage.sumInj (fun k : Fin (R+1) => a k.val) j y v))) = _
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have he := LineStage.sumProj_sumInj_ne (fun k : Fin (R+1) => a k.val) hkj y v
    exact (congrArg (lp.single (E := fun j => (a j).Fiber y) 2 k.val) he).trans
      (lp.single_zero (E := fun j => (a j).Fiber y) 2 k.val)
  · simp

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_Products
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded C-star products and the generated separable unital algebra. -/

noncomputable section
open scoped BigOperators ENNReal
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]

abbrev BoundedProduct (A : I → Type*) [∀ i, CStarAlgebra (A i)] : Type _ := lp A ∞

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_ShiftAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The generated Hilbert-shift algebra and its concrete realization. -/

noncomputable section
open scoped BigOperators ComplexOrder
namespace Kaplansky
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- A nonzero bottom fiber gives a nonzero ordinary Hilbert sum. -/
theorem fiberHilbertSum_nontrivial {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
    [∀ j, InnerProductSpace ℂ (E j)] [∀ j, CompleteSpace (E j)] [Nontrivial (E 0)] :
    Nontrivial (FiberHilbertSum E) :=
  (levelInclusion (E := E) 0).injective.nontrivial

attribute [local instance] fiberHilbertSum_nontrivial

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_TestAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Concrete test operators, their C-star algebra, and its faithful representation. -/

open Bundle Topology
open scoped BigOperators ComplexOrder
namespace Kaplansky
open ComplexGrassmann

abbrev ActualTestIndex := Σ m : ℕ+, Σ R : ℕ+, SmoothTestBase m.val R.val

abbrev ActualTestFiber (z : ActualTestIndex) (j : ℕ) :=
  EuclideanSpace ℂ (testSequenceStage z.1.val z.2.1.val j).Slot

open scoped BigOperators

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

abbrev ActualHilbert (z : ActualTestIndex) := FiberHilbertSum (ActualTestFiber z)

end Kaplansky

end

end OAI
end


