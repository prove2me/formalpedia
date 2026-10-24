-- Prove2me | Definitions.Def_OAIQWST000
-- name    : OAIQWST000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T19:29:25.212795+00:00
-- url     : https://prove2.me/theorems/43a95769-76d8-4b14-a395-e110a6adf515
-- title:
--   OpenAI split tangent bundles split: definitions bundle OAIQWST000
-- statement:
--   One of the three definitions bundles (`OAIQWST000`, `OAIQWST001`, `OAIQWST002`) of the split of OpenAI's proof that both summands of a holomorphic splitting of the tangent bundle of a rationally connected projective manifold are integrable (`OAI.SplitTangent.integrability_main`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Geometry/SplitTangent` (OpenAI, *Integrability of split tangent bundles on rationally connected manifolds*, OpenAI Math Release, September 23, 2026, result family 052, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies. The bundles split the material only to keep each one within the platform's compile limits.
--
--   The definitions of the published statement (`ComplexManifold`, `ProjectiveEmbedding`, `RationalCurve`, `RationallyConnected`, `TangentSplitting`, `Integrable` and the rest) are not repeated: every bundle imports them from the published bundle `Def_SplitTangentIntegrability`. It imports no other bundle of this split..
--
--   Modules (some only in part): `BracketIntegrability`, `FormalBoxes`, `OpenManifold`, `RationalFamilies`, `RationalTrivialization`.
--
--   The theorems the definitions do not need are proved in the four solutions of this split: three prove the published intermediate statements `OAI.SplitTangent.TangentSplitting.exists_projective_tangent_box`, `OAI.SplitTangent.RationalFamily.integrable_both_of_submersive` and `OAI.SplitTangent.RationallyConnected.exists_submersive_familyAlternative`, and the fourth proves `OAI.SplitTangent.integrability_main` from them. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Integrability of split tangent bundles on rationally connected manifolds, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 052; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integrability-of-split-tangent-bundles-on-rationally-connected-manifolds-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/SplitTangent at commit adc7f12

import Mathlib
import Definitions.Def_SplitTangentIntegrability

section
-- module Solutions.OAIQW_SplitTangent.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.BracketIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bracket Integrability. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

universe u
namespace SplitTangent
section

attribute [instance] ComplexManifold.topology ComplexManifold.charts
  ComplexManifold.holomorphicAtlas ComplexManifold.hausdorff
  ComplexManifold.secondCountable

open Filter Topology
namespace TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)
abbrev Field := ∀ x : X.Carrier, Tangent X x

def projectField (V : Field (X := X)) : Field (X := X) :=
  fun x => S.projector x (V x)

def complementAt (x : X.Carrier) : Tangent X x →L[ℂ] Tangent X x :=
  ContinuousLinearMap.id ℂ (Tangent X x) - S.projector x

@[simp] theorem complementAt_apply (x : X.Carrier) (v : Tangent X x) :
    S.complementAt x v = v - S.projector x v := rfl

@[simp] theorem complementAt_projector (x : X.Carrier) (v : Tangent X x) :
    S.complementAt x (S.projector x v) = 0 := by
  simp only [complementAt_apply, S.idempotent, sub_self]

@[simp] theorem projectField_add (V W : Field (X := X)) :
    S.projectField (V + W) = S.projectField V + S.projectField W := by
  funext x; exact map_add (S.projector x) (V x) (W x)

@[simp] theorem projectField_smul (f : X.Carrier → ℂ) (V : Field (X := X)) :
    S.projectField (f • V) = f • S.projectField V := by
  funext x; exact map_smul (S.projector x) (f x) (V x)

theorem mdifferentiableAt_projectField {V : Field (X := X)} {x : X.Carrier}
    (hV : MDifferentiableAt (ModelWithCorners X)
      ((ModelWithCorners X).prod 𝓘(ℂ, Model X))
      (fun y => (⟨y,V y⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) x) :
    MDifferentiableAt (ModelWithCorners X)
      ((ModelWithCorners X).prod 𝓘(ℂ, Model X))
      (fun y => (⟨y,S.projectField V y⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) x :=
  (S.holomorphic.mdifferentiable (by simp)).mdifferentiableAt.comp x hV

 

def bracketOperation (x : X.Carrier) (V W : Field (X := X)) : Tangent X x :=
  S.complementAt x (VectorField.mlieBracket (ModelWithCorners X)
    (S.projectField V) (S.projectField W) x)

theorem bracketOperation_tensorial_left (x : X.Carrier) (W : Field (X := X)) :
    TensorialAt (ModelWithCorners X) (Model X) (fun V => S.bracketOperation x V W) x := by
  constructor
  · intro f V hf hV
    simp only [bracketOperation, projectField_smul]
    rw [VectorField.mlieBracket_smul_left hf (S.mdifferentiableAt_projectField hV)]
    simp only [map_add, map_smul, projectField, complementAt_projector, smul_zero, zero_add]
  · intro V V' hV hV'
    simp only [bracketOperation, projectField_add]
    rw [VectorField.mlieBracket_add_left (S.mdifferentiableAt_projectField hV)
      (S.mdifferentiableAt_projectField hV'), map_add]

theorem bracketOperation_tensorial_right (x : X.Carrier) (V : Field (X := X)) :
    TensorialAt (ModelWithCorners X) (Model X) (S.bracketOperation x V) x := by
  constructor
  · intro f W hf hW
    simp only [bracketOperation, projectField_smul]
    rw [VectorField.mlieBracket_smul_right hf (S.mdifferentiableAt_projectField hW)]
    simp only [map_add, map_smul, projectField, complementAt_projector, smul_zero, zero_add]
  · intro W W' hW hW'
    simp only [bracketOperation, projectField_add]
    rw [VectorField.mlieBracket_add_right (S.mdifferentiableAt_projectField hW)
      (S.mdifferentiableAt_projectField hW'), map_add]

 

def bracketTensor (x : X.Carrier) : Tangent X x →L[ℂ] Tangent X x →L[ℂ] Tangent X x :=
  TensorialAt.mkHom₂ (S.bracketOperation x) x
    (fun W _ => S.bracketOperation_tensorial_left x W)
    (fun V _ => S.bracketOperation_tensorial_right x V)

theorem bracketTensor_apply {V W : Field (X := X)} {x : X.Carrier}
    (hV : MDifferentiableAt (ModelWithCorners X)
      ((ModelWithCorners X).prod 𝓘(ℂ, Model X))
      (fun y => (⟨y,V y⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) x)
    (hW : MDifferentiableAt (ModelWithCorners X)
      ((ModelWithCorners X).prod 𝓘(ℂ, Model X))
      (fun y => (⟨y,W y⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) x) :
    S.bracketTensor x (V x) (W x) = S.bracketOperation x V W :=
  TensorialAt.mkHom₂_apply _ _ hV hW

theorem mem_first_iff (x : X.Carrier) (v : Tangent X x) :
    v ∈ S.first x ↔ S.projector x v = v := by
  constructor
  · rintro ⟨w, rfl⟩; exact S.idempotent x w
  · intro hv; exact ⟨v,hv⟩

theorem mem_first_iff_complement_eq_zero (x : X.Carrier) (v : Tangent X x) :
    v ∈ S.first x ↔ S.complementAt x v = 0 := by
  rw [mem_first_iff, complementAt_apply, sub_eq_zero, eq_comm]

theorem holomorphicSectionOn_projectField {V : Field (X := X)} {U : Set X.Carrier}
    (hV : HolomorphicSectionOn X V U) : HolomorphicSectionOn X (S.projectField V) U :=
  S.holomorphic.comp_contMDiffOn hV



theorem holomorphicSectionOn_bracketOperation {V W : Field (X := X)}
    {U : Set X.Carrier} (hU : IsOpen U)
    (hV : HolomorphicSectionOn X V U) (hW : HolomorphicSectionOn X W U) :
    HolomorphicSectionOn X (fun x => S.bracketOperation x V W) U := by
  have hPV := S.holomorphicSectionOn_projectField hV
  have hPW := S.holomorphicSectionOn_projectField hW
  have hbr : HolomorphicSectionOn X
      (VectorField.mlieBracketWithin (ModelWithCorners X) (S.projectField V) (S.projectField W) U) U := by
    intro x hx
    exact (hPV x hx).mlieBracketWithin_vectorField (hPW x hx)
      (hU.uniqueMDiffOn (I := ModelWithCorners X)) hx (by simp)
  have hbr' : HolomorphicSectionOn X
      (VectorField.mlieBracket (ModelWithCorners X) (S.projectField V) (S.projectField W)) U := by
    apply hbr.congr
    intro x hx
    simp only [VectorField.mlieBracketWithin_of_isOpen hU hx]
  exact hbr'.sub_section (S.holomorphicSectionOn_projectField hbr')

theorem holomorphicSectionOn_bracketTensor_apply {V W : Field (X := X)}
    {U : Set X.Carrier} (hU : IsOpen U)
    (hV : HolomorphicSectionOn X V U) (hW : HolomorphicSectionOn X W U) :
    HolomorphicSectionOn X (fun x => S.bracketTensor x (V x) (W x)) U := by
  apply (S.holomorphicSectionOn_bracketOperation hU hV hW).congr
  intro x hx
  congr 1
  exact S.bracketTensor_apply
    ((hV x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))
    ((hW x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))

theorem range_complementAt (x : X.Carrier) :
    LinearMap.range (S.complementAt x).toLinearMap = S.second x := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    change S.projector x (w - S.projector x w) = 0
    rw [map_sub, S.idempotent, sub_self]
  · intro hv
    refine ⟨v,?_⟩
    change v - S.projector x v = v
    rw [show S.projector x v = 0 from hv, sub_zero]

theorem ker_complementAt (x : X.Carrier) :
    LinearMap.ker (S.complementAt x).toLinearMap = S.first x := by
  ext v
  exact (S.mem_first_iff_complement_eq_zero x v).symm

theorem holomorphic_complement : ContMDiff
    ((ModelWithCorners X).prod 𝓘(ℂ, Model X))
    ((ModelWithCorners X).prod 𝓘(ℂ, Model X)) ω
    (fun v : TangentBundle (ModelWithCorners X) X.Carrier =>
      (⟨v.proj, S.complementAt v.proj v.2⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) := by
  intro v
  rw [contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hid : ContMDiffAt ((ModelWithCorners X).prod 𝓘(ℂ, Model X))
      ((ModelWithCorners X).prod 𝓘(ℂ, Model X)) ω
      (id : TangentBundle (ModelWithCorners X) X.Carrier → _) v := contMDiffAt_id
  have h1 := (contMDiffAt_totalSpace.mp hid).2
  have h2 := (contMDiffAt_totalSpace.mp (S.holomorphic v)).2
  apply (h1.sub h2).congr_of_eventuallyEq
  let e := trivializationAt (Model X) (Tangent X) v.proj
  have hbase : ∀ᶠ w : TangentBundle (ModelWithCorners X) X.Carrier in nhds v,
      w.proj ∈ e.baseSet :=
    (FiberBundle.continuous_proj (F := Model X) (E := Tangent X)).continuousAt.eventually
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' v.proj))
  filter_upwards [hbase] with w hw
  exact (e.linear ℂ hw).map_sub _ _

 

def swap : TangentSplitting X where
  projector := S.complementAt
  idempotent := by
    intro x v
    simp only [complementAt_apply, map_sub, S.idempotent, sub_self, sub_zero]
  holomorphic := S.holomorphic_complement
  first_positive := by
    intro x
    rw [S.range_complementAt]
    exact S.second_positive x
  second_positive := by
    intro x
    rw [S.ker_complementAt]
    exact S.first_positive x

@[simp] theorem swap_first : S.swap.first = S.second := by
  funext x; exact S.range_complementAt x

@[simp] theorem swap_second : S.swap.second = S.first := by
  funext x; exact S.ker_complementAt x



end TangentSplitting

end

section



structure CurveTangentSection {X : ComplexManifold.{u}} (g : RationalCurve X) where
  finite : ∀ z : ℂ, Tangent X (g.finite z)
  infinity : ∀ z : ℂ, Tangent X (g.infinity z)
  finite_holomorphic : ContMDiff 𝓘(ℂ, ℂ)
    ((ModelWithCorners X).prod 𝓘(ℂ, Model X)) ω
    (fun z => (⟨g.finite z, finite z⟩ : TangentBundle (ModelWithCorners X) X.Carrier))
  infinity_holomorphic : ContMDiff 𝓘(ℂ, ℂ)
    ((ModelWithCorners X).prod 𝓘(ℂ, Model X)) ω
    (fun z => (⟨g.infinity z, infinity z⟩ : TangentBundle (ModelWithCorners X) X.Carrier))
  overlap : ∀ z : ℂ, z ≠ 0 → finite z = infinity z⁻¹

namespace TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

lemma localFrame_sum (t : Trivialization (Model X)
    (Bundle.TotalSpace.proj : TangentBundle (ModelWithCorners X) X.Carrier → X.Carrier))
    [MemTrivializationAtlas t] {x : X.Carrier} (hx : x ∈ t.baseSet) (v : Tangent X x) :
    ∑ i : Fin X.dim, (t ⟨x,v⟩).2 i • t.localFrame (Pi.basisFun ℂ (Fin X.dim)) i x = v := by
  have h := (t.basisAt (Pi.basisFun ℂ (Fin X.dim)) hx).sum_repr v
  simpa [Bundle.Trivialization.localFrame_apply_of_mem_baseSet t _ hx,
    Bundle.Trivialization.basisAt, Module.Basis.map_repr,
    Bundle.Trivialization.linearEquivAt_apply] using h

 

lemma bracketTensor_holomorphic_along {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (v w : ∀ z : ℂ, Tangent X (g z))
    (hv : ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,v z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)))
    (hw : ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,w z⟩ : TangentBundle (ModelWithCorners X) X.Carrier))) :
    ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,S.bracketTensor (g z) (v z) (w z)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) := by
  intro z
  let t := trivializationAt (Model X) (Tangent X) (g z)
  let b := Pi.basisFun ℂ (Fin X.dim)
  have hz : g z ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' (g z)
  have hsrc (v' : Tangent X (g z)) : (⟨g z,v'⟩ : TangentBundle (ModelWithCorners X) X.Carrier) ∈ t.source := by
    simpa only [t.mem_source] using hz
  apply (t.contMDiffAt_iff (f := fun q => (⟨g q,S.bracketTensor (g q) (v q) (w q)⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (hsrc _)).mpr
  refine ⟨hg z,?_⟩
  have hv' := ((t.contMDiffAt_iff (f := fun q => (⟨g q,v q⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (hsrc _)).mp (hv z)).2
  have hw' := ((t.contMDiffAt_iff (f := fun q => (⟨g q,w q⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (hsrc _)).mp (hw z)).2
  let H := fun (x : X.Carrier) (i j : Fin X.dim) =>
    (t ⟨x,S.bracketTensor x (t.localFrame b i x) (t.localFrame b j x)⟩).2
  have hframe (i : Fin X.dim) : HolomorphicSectionOn X (t.localFrame b i) t.baseSet :=
    t.contMDiffOn_localFrame_baseSet ω b i
  have hH (i j : Fin X.dim) : ContMDiffOn (ModelWithCorners X) 𝓘(ℂ,Model X) ω
      (fun x => H x i j) t.baseSet :=
    t.contMDiffOn_section_baseSet_iff.mp
      (S.holomorphicSectionOn_bracketTensor_apply t.open_baseSet (hframe i) (hframe j))
  let T := fun z : ℂ => ∑ i : Fin X.dim, ∑ j : Fin X.dim,
    ((t ⟨g z,v z⟩).2 i * (t ⟨g z,w z⟩).2 j) • H (g z) i j
  have hT : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,Model X) ω T z := by
    apply ContMDiffAt.sum
    intro i hi
    apply ContMDiffAt.sum
    intro j hj
    apply ContMDiffAt.smul (I := 𝓘(ℂ,ℂ))
      (f := fun q => (t ⟨g q,v q⟩).2 i * (t ⟨g q,w q⟩).2 j)
      (g := fun q => H (g q) i j)
    · exact ((contMDiffAt_pi_space.mp hv') i).mul ((contMDiffAt_pi_space.mp hw') j)
    · exact ((hH i j (g z) hz).contMDiffAt (t.open_baseSet.mem_nhds hz)).comp z (hg z)
  have he : (fun z => (t ⟨g z,S.bracketTensor (g z) (v z) (w z)⟩).2) =ᶠ[nhds z] T := by
    filter_upwards [(hg z).continuousAt.eventually (t.open_baseSet.mem_nhds hz)] with q hq
    have hvq := localFrame_sum t hq (v q)
    have hwq := localFrame_sum t hq (w q)
    change (t.linearEquivAt ℂ (g q) hq) (S.bracketTensor (g q) (v q) (w q)) = _
    conv_lhs => rw [←hvq,←hwq]
    simp only [map_sum,map_smul,sum_apply,smul_apply,Finset.smul_sum,smul_smul]
    rw [Finset.sum_comm]
    simp only [T,H,b,Bundle.Trivialization.linearEquivAt_apply,mul_comm]
  exact hT.congr_of_eventuallyEq he

end TangentSplitting

namespace CurveTangentSection
variable {X : ComplexManifold.{u}} {g : RationalCurve X}

 
def bracket (S : TangentSplitting X) (v w : CurveTangentSection g) : CurveTangentSection g where
  finite z := S.bracketTensor (g.finite z) (v.finite z) (w.finite z)
  infinity z := S.bracketTensor (g.infinity z) (v.infinity z) (w.infinity z)
  finite_holomorphic := S.bracketTensor_holomorphic_along g.finite_holomorphic
    v.finite w.finite v.finite_holomorphic w.finite_holomorphic
  infinity_holomorphic := S.bracketTensor_holomorphic_along g.infinity_holomorphic
    v.infinity w.infinity v.infinity_holomorphic w.infinity_holomorphic
  overlap z hz := by
    rw [g.overlap z hz,v.overlap z hz,w.overlap z hz]

end CurveTangentSection

open Filter


namespace RationalCurve
variable {X : ComplexManifold.{u}}
def constant (x : X.Carrier) : RationalCurve X where
  finite := fun _ => x
  infinity := fun _ => x
  finite_holomorphic := contMDiff_const
  infinity_holomorphic := contMDiff_const
  overlap _ _ := rfl
end RationalCurve

end


 

structure CurveBundleMap {X : ComplexManifold.{u}} (g h : RationalCurve X) where
  finite : ∀ z, Tangent X (g.finite z) →L[ℂ] Tangent X (h.finite z)
  infinity : ∀ z, Tangent X (g.infinity z) →L[ℂ] Tangent X (h.infinity z)
  overlap : ∀ z : ℂ, z ≠ 0 → finite z = infinity z⁻¹
  finite_holomorphic : ∀ (U : Set ℂ), IsOpen U → ∀ v : ∀ z, Tangent X (g.finite z),
    ContMDiffOn 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g.finite z,v z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) U →
    ContMDiffOn 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨h.finite z,finite z (v z)⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) U
  infinity_holomorphic : ∀ (U : Set ℂ), IsOpen U → ∀ v : ∀ z, Tangent X (g.infinity z),
    ContMDiffOn 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g.infinity z,v z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) U →
    ContMDiffOn 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨h.infinity z,infinity z (v z)⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) U

namespace CurveBundleMap
variable {X : ComplexManifold.{u}} {g h : RationalCurve X}
def mapSection (A : CurveBundleMap g h) (σ : CurveTangentSection g) : CurveTangentSection h where
  finite z := A.finite z (σ.finite z)
  infinity z := A.infinity z (σ.infinity z)
  finite_holomorphic := contMDiffOn_univ.mp
    (A.finite_holomorphic univ isOpen_univ σ.finite σ.finite_holomorphic.contMDiffOn)
  infinity_holomorphic := contMDiffOn_univ.mp
    (A.infinity_holomorphic univ isOpen_univ σ.infinity σ.infinity_holomorphic.contMDiffOn)
  overlap z hz := by rw [A.overlap z hz,σ.overlap z hz]; rfl
end CurveBundleMap

 

structure NormalizedFactorTransport {X : ComplexManifold.{u}}
    (S : TangentSplitting X) (g : RationalCurve X) (b : ℂ) where
  factor : RationalCurve X
  diagonal : factor.finite b = g.finite b
  firstMap : CurveBundleMap g factor
  secondMap : CurveBundleMap factor (RationalCurve.constant (g.finite b))
  first_normalized : firstMap.finite b = S.projector (g.finite b)
  second_normalized : secondMap.finite b = S.complementAt (g.finite b)

end SplitTangent

open scoped Topology
open Filter

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.RationalTrivialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Trivialization. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

universe u

open scoped Topology
open Filter

namespace SplitTangent.TangentSplitting
section
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 
def coordinateProjector (x : X.Carrier) (z : Model X) : Model X →L[ℂ] Model X :=
  let t := trivializationAt (Model X) (Tangent X) x
  let y := (chartAt (Model X) x).symm z
  (t.continuousLinearMapAt ℂ y).comp ((S.projector y).comp (t.symmL ℂ y))

def coordinateMatrix (x : X.Carrier) (i j : Fin X.dim) (z : Model X) : ℂ :=
  LinearMap.toMatrix' (S.coordinateProjector x z).toLinearMap i j



theorem coordinateMatrix_analytic (x : X.Carrier) (i j : Fin X.dim) :
    AnalyticOnNhd ℂ (S.coordinateMatrix x i j) (chartAt (Model X) x).target := by
  let t := trivializationAt (Model X) (Tangent X) x
  let b := Pi.basisFun ℂ (Fin X.dim)
  let c := chartAt (Model X) x
  let H := fun y : X.Carrier => (t ⟨y,S.projector y (t.localFrame b j y)⟩).2
  have hframe : HolomorphicSectionOn X (t.localFrame b j) t.baseSet :=
    t.contMDiffOn_localFrame_baseSet ω b j
  have hH : ContMDiffOn (ModelWithCorners X) 𝓘(ℂ, Model X) ω H t.baseSet :=
    t.contMDiffOn_section_baseSet_iff.mp (S.holomorphicSectionOn_projectField hframe)
  have heq : Set.EqOn (S.coordinateMatrix x i j) (fun z => H (c.symm z) i) c.target := by
    intro z hz
    have hy : c.symm z ∈ t.baseSet := c.map_target hz
    have hb : t.symmL ℂ (c.symm z) (Pi.single j 1) = t.localFrame b j (c.symm z) := by
      rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet t b hy]
      simp only [Bundle.Trivialization.basisAt,Module.Basis.map_apply,b,Pi.basisFun_apply]
      simp only [Bundle.Trivialization.linearEquivAt_symm_apply,Bundle.Trivialization.symmL_apply t hy]
    simp only [coordinateMatrix,LinearMap.toMatrix'_apply,coordinateProjector,
      ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply]
    rw [hb,Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℂ t hy]
  intro z hz
  have hc : ContMDiffAt 𝓘(ℂ,Model X) (ModelWithCorners X) ω c.symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) x) hz
  have hh : AnalyticAt ℂ (fun z => H (c.symm z)) z :=
    ((hH.contMDiffAt (t.open_baseSet.mem_nhds (c.map_target hz))).comp z hc).contDiffAt.analyticAt
  apply (analyticAt_pi_iff.mp hh i).congr
  exact Filter.eventuallyEq_of_mem (c.open_target.mem_nhds hz) (fun z hz => (heq hz).symm)

end

end SplitTangent.TangentSplitting

end

noncomputable section
universe u
open Filter Topology Set Bundle
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace SplitTangent.HolomorphicLinearODE
section
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

def solutionCoeff (A : ℕ → R) (v : R) : ℕ → R
  | 0 => v
  | n+1 => ((n+1 : ℕ) : ℂ)⁻¹ •
      ∑ i ∈ Finset.range (n+1), A i * solutionCoeff A v (n-i)
termination_by n => n

omit [CompleteSpace R] in
lemma solutionCoeff_recurrence (A : ℕ → R) (v : R) (n : ℕ) :
    ((n+1 : ℕ) : ℂ) • solutionCoeff A v (n+1) =
      ∑ i ∈ Finset.range (n+1), A i * solutionCoeff A v (n-i) := by
  rw [solutionCoeff,smul_smul]
  have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [mul_inv_cancel₀ hn,one_smul]

omit [CompleteSpace R] in
lemma solutionCoeff_norm {A : ℕ → R} (v : R) {B : ℝ} (hB : 0 < B)
    (hA : ∀ n, ‖A n‖ ≤ B^(n+1)) (n : ℕ) :
    ‖solutionCoeff A v n‖ ≤ B^n * ‖v‖ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [solutionCoeff]
    | succ n =>
      rw [solutionCoeff,norm_smul]
      have hc : ‖(((n+1 : ℕ) : ℂ))⁻¹‖ = ((n+1 : ℕ) : ℝ)⁻¹ := by rw [norm_inv,Complex.norm_natCast]
      rw [hc]
      have hs : ‖∑ i ∈ Finset.range (n+1), A i * solutionCoeff A v (n-i)‖ ≤
          ((n+1 : ℕ) : ℝ) * (B^(n+1) * ‖v‖) := by
        calc
          _ ≤ ∑ i ∈ Finset.range (n+1), ‖A i * solutionCoeff A v (n-i)‖ := norm_sum_le _ _
          _ ≤ ∑ _i ∈ Finset.range (n+1), B^(n+1) * ‖v‖ := by
            apply Finset.sum_le_sum
            intro i hi
            have hin : i ≤ n := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
            calc
              _ ≤ ‖A i‖ * ‖solutionCoeff A v (n-i)‖ := norm_mul_le _ _
              _ ≤ B^(i+1) * (B^(n-i) * ‖v‖) := by
                exact mul_le_mul (hA i) (ih _ (by omega)) (norm_nonneg _) (pow_nonneg hB.le _)
              _ = B^(n+1) * ‖v‖ := by rw [← mul_assoc,← pow_add]; congr 2; omega
          _ = _ := by simp [nsmul_eq_mul]
      calc
        _ ≤ ((n+1 : ℕ) : ℝ)⁻¹ * (((n+1 : ℕ) : ℝ) * (B^(n+1) * ‖v‖)) := by gcongr
        _ = _ := by rw [inv_mul_cancel_left₀ (by positivity)]

def series (a : ℕ → R) : FormalMultilinearSeries ℂ ℂ R :=
  fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n)

omit [CompleteSpace R] in
@[simp] lemma series_coeff (a : ℕ → R) (n : ℕ) : (series a).coeff n = a n := by
  simp [series,FormalMultilinearSeries.coeff,ContinuousMultilinearMap.mkPiRing_apply]

omit [CompleteSpace R] in
lemma series_radius {a : ℕ → R} {B C : ℝ} (hB : 0 < B)
    (ha : ∀ n, ‖a n‖ ≤ B^n*C) :
    (ENNReal.ofReal B⁻¹) ≤ (series a).radius := by
  rw [ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr hB.le)]
  apply (series a).le_radius_of_bound C (r := ⟨B⁻¹,inv_nonneg.mpr hB.le⟩)
  intro n
  simp only [series,ContinuousMultilinearMap.norm_mkPiRing]
  change ‖a n‖ * (B⁻¹)^n ≤ C
  calc
    _ ≤ (B^n*C)*(B⁻¹)^n := mul_le_mul_of_nonneg_right (ha n) (by positivity)
    _ = (B^n*(B⁻¹)^n)*C := by ring
    _ = C := by rw [← mul_pow,mul_inv_cancel₀ hB.ne',one_pow,one_mul]

omit [CompleteSpace R] in
lemma solutionSeries_pos {A : ℕ → R} (v : R) {B : ℝ} (hB : 0 < B)
    (hA : ∀ n, ‖A n‖ ≤ B^(n+1)) :
    0 < (series (solutionCoeff A v)).radius :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (inv_pos.mpr hB))
    (series_radius hB (solutionCoeff_norm v hB hA))

omit [CompleteSpace R] in
lemma cauchy_eval (a b : ℕ → R) (z : ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), (z^i • a i) * (z^(n-i) • b (n-i))) =
      z^n • ∑ i ∈ Finset.range (n+1), a i * b (n-i) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_mul_smul,← pow_add]
  congr 2
  have : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  omega

lemma hasDerivAt_solutionSeries {A : ℕ → R} (v : R) {B : ℝ} (hB : 0 < B)
    (hA : ∀ n, ‖A n‖ ≤ B^(n+1)) {z : ℂ}
    (hzA : ‖z‖ₑ < (series A).radius)
    (hzY : ‖z‖ₑ < (series (solutionCoeff A v)).radius) :
    HasDerivAt (series (solutionCoeff A v)).sum
      ((series A).sum z * (series (solutionCoeff A v)).sum z) z := by
  let p := series (solutionCoeff A v)
  have hp : 0 < p.radius := solutionSeries_pos v hB hA
  have hzY' : z ∈ Metric.eball 0 p.radius := by simpa using hzY
  have hzA' : z ∈ Metric.eball 0 (series A).radius := by simpa using hzA
  have hD := (ContinuousLinearMap.apply ℂ R 1).hasSum
    ((p.hasFPowerSeriesOnBall hp).fderiv.hasSum hzY')
  have hprod := hasSum_sum_range_mul_of_summable_norm
    ((series A).summable_norm_apply hzA') (p.summable_norm_apply hzY')
  have he : (fun n => (ContinuousLinearMap.apply ℂ R 1)
      (p.derivSeries n fun _ => z)) =
      (fun n => ∑ i ∈ Finset.range (n+1),
        ((series A) i fun _ => z) * (p (n-i) fun _ => z)) := by
    funext n
    simp only [ContinuousLinearMap.apply_apply,FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      smul_apply,FormalMultilinearSeries.derivSeries_coeff_one]
    simp only [p,series_coeff]
    rw [cauchy_eval,← Nat.cast_smul_eq_nsmul ℂ,solutionCoeff_recurrence]
  rw [← he] at hprod
  have hdval := hD.unique hprod
  simp only [zero_add,ContinuousLinearMap.apply_apply] at hdval
  rw [(series A).hasSum hzA' |>.tsum_eq,p.hasSum hzY' |>.tsum_eq] at hdval
  have hder := ((p.hasFPowerSeriesOnBall hp).analyticAt_of_mem hzY').differentiableAt.hasFDerivAt.hasDerivAt
  rw [hdval] at hder
  exact hder

omit [CompleteSpace R] in
lemma coeff_bound {p : FormalMultilinearSeries ℂ ℂ R} (hp : 0 < p.radius) :
    ∃ B : ℝ, 0 < B ∧ ∀ n, ‖p.coeff n‖ ≤ B^(n+1) := by
  obtain ⟨r,hr0,hrp⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  have hr : 0 < r := by exact_mod_cast hr0
  obtain ⟨C,hC,hCp⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hr hrp
  let B := max C (r : ℝ)⁻¹
  have hCB : C ≤ B := le_max_left _ _
  have hrB : (r : ℝ)⁻¹ ≤ B := le_max_right _ _
  have hB : 0 < B := lt_of_lt_of_le hC hCB
  refine ⟨B,hB,fun n => ?_⟩
  calc
    ‖p.coeff n‖ = ‖p n‖ := (p.norm_apply_eq_norm_coef).symm
    _ ≤ C / (r : ℝ)^n := hCp n
    _ = C * ((r : ℝ)⁻¹)^n := by rw [div_eq_mul_inv,inv_pow]
    _ ≤ B * B^n := mul_le_mul hCB (pow_le_pow_left₀ (by positivity) hrB n)
      (by positivity) hB.le
    _ = B^(n+1) := by rw [pow_succ,mul_comm]

omit [CompleteSpace R] in
@[simp] lemma series_of_coeff (p : FormalMultilinearSeries ℂ ℂ R) :
    series p.coeff = p := by
  funext n
  exact p.mkPiRing_coeff_eq n

lemma exists_local_solution {A : ℂ → R} {x : ℂ} (hA : AnalyticAt ℂ A x) (v : R) :
    ∃ Y : ℂ → R, AnalyticAt ℂ Y x ∧ Y x = v ∧
      ∀ᶠ z in 𝓝 x, HasDerivAt Y (A z * Y z) z := by
  obtain ⟨p,r,hp⟩ := hA
  obtain ⟨B,hB,hbound⟩ := coeff_bound (hp.r_pos.trans_le hp.r_le)
  let q := series (solutionCoeff p.coeff v)
  have hq : 0 < q.radius := solutionSeries_pos v hB hbound
  let Y : ℂ → R := fun z => q.sum (z-x)
  have hqA : AnalyticAt ℂ q.sum 0 := (q.hasFPowerSeriesOnBall hq).analyticAt
  refine ⟨Y,?_,?_,?_⟩
  · simpa [Y] using hqA.comp_sub x
  · change q.sum (x-x) = v
    rw [sub_self,← (q.hasFPowerSeriesOnBall hq).coeff_zero (fun _ => 1)]
    simp [q,series,ContinuousMultilinearMap.mkPiRing_apply,solutionCoeff]
  · have hrN : ∀ᶠ z in 𝓝 x, z ∈ Metric.eball x r := Metric.eball_mem_nhds x hp.r_pos
    have hqN : ∀ᶠ z in 𝓝 x, z ∈ Metric.eball x q.radius := Metric.eball_mem_nhds x hq
    filter_upwards [hrN,hqN] with z hzr hzq
    have hzr' : z-x ∈ Metric.eball 0 r := by simpa [edist_eq_enorm_sub] using hzr
    have hzq' : ‖z-x‖ₑ < q.radius := by simpa [edist_eq_enorm_sub] using hzq
    have hzp : ‖z-x‖ₑ < (series p.coeff).radius := by
      simpa using (show ‖z-x‖ₑ < r by simpa using hzr').trans_le hp.r_le
    have hder := hasDerivAt_solutionSeries v hB hbound hzp hzq'
    have heA : (series p.coeff).sum (z-x) = A z := by
      rw [series_of_coeff,← hp.sum hzr',add_sub_cancel]
    rw [heA] at hder
    simpa [Y,Function.comp_def] using hder.scomp z ((hasDerivAt_id z).sub_const x)

lemma inverse_mul_horizontal {Y Z : ℂ → R} {A : R} {z : ℂ}
    (hY : HasDerivAt Y (A * Y z) z) (hZ : HasDerivAt Z (A * Z z) z)
    (hu : IsUnit (Y z)) :
    HasDerivAt (fun w => Ring.inverse (Y w) * Z w) 0 z := by
  obtain ⟨u,he⟩ := hu
  have hi : HasDerivAt (fun w => Ring.inverse (Y w))
      (-(Ring.inverse (Y z) * (A * Y z) * Ring.inverse (Y z))) z := by
    have h := (hasFDerivAt_ringInverse (𝕜 := ℂ) u)
    rw [he] at h
    convert! h.comp_hasDerivAt z hY using 1; try rfl
    simp only [neg_apply,ContinuousLinearMap.mulLeftRight_apply]
    rw [← Ring.inverse_unit u,he]
  convert! hi.mul hZ using 1; try rfl
  have hc : Y z * Ring.inverse (Y z) = 1 := Ring.mul_inverse_cancel _ ⟨u,he⟩
  simp only [neg_mul,mul_assoc,hc,mul_one,neg_add_cancel]

lemma exists_local_fundamental {A : ℂ → R} {x : ℂ} (hA : AnalyticAt ℂ A x) :
    ∃ Y : ℂ → R, AnalyticAt ℂ Y x ∧ Y x = 1 ∧
      ∀ᶠ z in 𝓝 x, HasDerivAt Y (A z * Y z) z ∧ IsUnit (Y z) := by
  obtain ⟨Y,hYa,hY0,hYd⟩ := exists_local_solution hA 1
  refine ⟨Y,hYa,hY0,hYd.and ?_⟩
  have hn : {a : R | IsUnit a} ∈ 𝓝 (Y x) :=
    Units.isOpen.mem_nhds (hY0 ▸ isUnit_one)
  exact hYa.continuousAt.eventually hn

lemma local_uniqueness {A f g : ℂ → R} {x : ℂ} (hA : AnalyticAt ℂ A x)
    (hf : ∀ᶠ z in 𝓝 x, HasDerivAt f (A z * f z) z)
    (hg : ∀ᶠ z in 𝓝 x, HasDerivAt g (A z * g z) z)
    (he : f x = g x) : f =ᶠ[𝓝 x] g := by
  obtain ⟨Y,hYa,hY0,hY⟩ := exists_local_fundamental hA
  obtain ⟨ε,hε,hs⟩ := Metric.eventually_nhds_iff_ball.mp (hY.and (hf.and hg))
  let D : ℂ → R := fun z => Ring.inverse (Y z) * (f z-g z)
  have hd (z : ℂ) (hz : z ∈ Metric.ball x ε) : HasDerivAt D 0 z := by
    have hsub : HasDerivAt (fun w => f w-g w) (A z * (f z-g z)) z := by
      convert! (hs z hz).2.1.sub (hs z hz).2.2 using 1; try rfl
      exact mul_sub _ _ _
    exact inverse_mul_horizontal (hs z hz).1.1 hsub (hs z hz).1.2
  filter_upwards [Metric.ball_mem_nhds x hε] with z hz
  have hc : D z = D x := Metric.isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball x ε).isPreconnected
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).deriv) hz (Metric.mem_ball_self hε)
  have hmul := congrArg (fun a => Y z*a) hc
  have hcancel := Ring.mul_inverse_cancel (Y z) (hs z hz).1.2
  have hz0 : f z-g z = 0 := by
    simpa only [D,he,sub_self,mul_zero,← mul_assoc,hcancel,one_mul] using hmul
  exact sub_eq_zero.mp hz0

 

def transport (Y : ℂ → R) (s t : ℂ) : R := Y t * Ring.inverse (Y s)

omit [NormedAlgebra ℂ R] [CompleteSpace R] in
lemma transport_self {Y : ℂ → R} {s : ℂ} (hs : IsUnit (Y s)) :
    transport Y s s = 1 := Ring.mul_inverse_cancel _ hs

omit [NormedAlgebra ℂ R] [CompleteSpace R] in
lemma transport_trans {Y : ℂ → R} {s t u : ℂ} (ht : IsUnit (Y t)) :
    transport Y t u * transport Y s t = transport Y s u := by
  simp only [transport, mul_assoc, ← mul_assoc (Ring.inverse (Y t)),
    Ring.inverse_mul_cancel _ ht, one_mul]

omit [NormedAlgebra ℂ R] [CompleteSpace R] in
lemma transport_isUnit {Y : ℂ → R} {s t : ℂ}
    (hs : IsUnit (Y s)) (ht : IsUnit (Y t)) : IsUnit (transport Y s t) := by
  obtain ⟨u,hu⟩ := hs
  rw [transport, ← hu, Ring.inverse_unit]
  exact ht.mul (Units.isUnit _)

lemma transport_analyticAt {Y : ℂ → R} {s t : ℂ}
    (hs : AnalyticAt ℂ Y s) (ht : AnalyticAt ℂ Y t) (hu : IsUnit (Y s)) :
    AnalyticAt ℂ (fun w : ℂ × ℂ => transport Y w.1 w.2) (s,t) := by
  have hf : AnalyticAt ℂ (fun w : ℂ × ℂ => Y w.1) (s,t) := hs.comp analyticAt_fst
  have hg : AnalyticAt ℂ (fun w : ℂ × ℂ => Y w.2) (s,t) := ht.comp analyticAt_snd
  have hi : AnalyticAt ℂ (fun w : ℂ × ℂ => Ring.inverse (Y w.1)) (s,t) :=
    (analyticOnNhd_inverse (𝕜 := ℂ) _ hu).comp_of_eq hf rfl
  exact hg.mul hi

omit [CompleteSpace R] in
lemma transport_hasDerivAt {A Y : ℂ → R} {s t : ℂ}
    (ht : HasDerivAt Y (A t * Y t) t) :
    HasDerivAt (transport Y s) (A t * transport Y s t) t := by
  convert! ht.mul_const (Ring.inverse (Y s)) using 1; try rfl
  exact (mul_assoc _ _ _).symm



theorem eqOn_of_solution {A f g : ℂ → R} {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hA : AnalyticOnNhd ℂ A U)
    (hf : ∀ z ∈ U, HasDerivAt f (A z * f z) z)
    (hg : ∀ z ∈ U, HasDerivAt g (A z * g z) z)
    {x : ℂ} (hx : x ∈ U) (he : f x = g x) : EqOn f g U := by
  have hfa : AnalyticOnNhd ℂ f U :=
    (show DifferentiableOn ℂ f U from fun z hz => (hf z hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU
  have hga : AnalyticOnNhd ℂ g U :=
    (show DifferentiableOn ℂ g U from fun z hz => (hg z hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU
  apply hfa.eqOn_of_preconnected_of_eventuallyEq hga hUc hx
  apply local_uniqueness (hA x hx) _ _ he
  · exact Filter.Eventually.mono (hU.mem_nhds hx) (fun z hz => hf z hz)
  · exact Filter.Eventually.mono (hU.mem_nhds hx) (fun z hz => hg z hz)

 
omit [CompleteSpace R] in
lemma gauge_hasDerivAt {A B H Y : ℂ → R} {z : ℂ}
    (hH : HasDerivAt H (B z * H z - H z * A z) z)
    (hY : HasDerivAt Y (A z * Y z) z) :
    HasDerivAt (fun w => H w * Y w) (B z * (H z * Y z)) z := by
  convert! hH.mul hY using 1; try rfl
  simp only [sub_mul,mul_assoc,sub_add_cancel]

 

lemma intertwine_eventually {A P Y : ℂ → R} {x : ℂ}
    (hA : AnalyticAt ℂ A x) (hY0 : Y x = 1)
    (hY : ∀ᶠ z in 𝓝 x, HasDerivAt Y (A z * Y z) z)
    (hP : ∀ᶠ z in 𝓝 x, HasDerivAt P (A z * P z - P z * A z) z) :
    ∀ᶠ z in 𝓝 x, P z * Y z = Y z * P x := by
  apply local_uniqueness hA
  · filter_upwards [hP,hY] with z hp hy
    exact gauge_hasDerivAt hp hy
  · filter_upwards [hY] with z hz
    convert! hz.mul_const (P x) using 1; try rfl
    exact (mul_assoc _ _ _).symm
  · simp only [hY0,mul_one,one_mul]

omit [NormedAlgebra ℂ R] [CompleteSpace R] in
lemma transport_intertwines {Y P : ℂ → R} {x s t : ℂ}
    (hs : P s * Y s = Y s * P x) (ht : P t * Y t = Y t * P x)
    (hu : IsUnit (Y s)) : P t * transport Y s t = transport Y s t * P s := by
  have he : P x * Ring.inverse (Y s) = Ring.inverse (Y s) * P s := by
    have h := congrArg (fun a => Ring.inverse (Y s) * a * Ring.inverse (Y s)) hs
    simpa only [mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one,
      ← mul_assoc (Ring.inverse (Y s)) (Y s),Ring.inverse_mul_cancel _ hu,one_mul] using h.symm
  unfold transport
  rw [← mul_assoc, ht, mul_assoc, he, mul_assoc]


omit [CompleteSpace R] in
lemma solutionCoeff_differentiableOn {A : ℕ → ℂ → R} {U : Set ℂ}
    (hA : ∀ n, DifferentiableOn ℂ (A n) U) (v : R) (n : ℕ) :
    DifferentiableOn ℂ (fun s => solutionCoeff (fun i => A i s) v n) U := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [solutionCoeff]
    | succ n =>
      simp only [solutionCoeff]
      have hd : DifferentiableOn ℂ (fun s =>
          ∑ i ∈ Finset.range (n+1), A i s * solutionCoeff (fun i => A i s) v (n-i)) U := by
        apply DifferentiableOn.fun_sum
        intro i hi
        exact (hA i).fun_mul (ih (n-i) (by omega))
      exact hd.fun_const_smul (((n+1 : ℕ) : ℂ)⁻¹)

 

def parameterSolution (A : ℕ → ℂ → R) (v : R) (s t : ℂ) : R :=
  ∑' n, t^n • solutionCoeff (fun i => A i s) v n

 

lemma parameterSolution_differentiableOn {A : ℕ → ℂ → R} {U : Set ℂ}
    {t : ℂ → ℂ} {B r : ℝ} (hU : IsOpen U) (hB : 0 < B) (hr : 0 ≤ r)
    (hBr : r*B < 1) (hA : ∀ n, DifferentiableOn ℂ (A n) U)
    (hbound : ∀ n s, s ∈ U → ‖A n s‖ ≤ B^(n+1))
    (ht : DifferentiableOn ℂ t U) (htr : ∀ s ∈ U, ‖t s‖ ≤ r) (v : R) :
    DifferentiableOn ℂ (fun s => parameterSolution A v s (t s)) U := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    ((summable_geometric_of_lt_one (mul_nonneg hr hB.le) hBr).mul_right ‖v‖)
    (fun n => (ht.pow n).smul (solutionCoeff_differentiableOn hA v n)) hU
  intro n s hs
  change ‖t s ^ n • solutionCoeff (fun i => A i s) v n‖ ≤ (r*B)^n * ‖v‖
  rw [norm_smul,norm_pow]
  calc
    ‖t s‖^n * ‖solutionCoeff (fun i => A i s) v n‖ ≤
        r^n * (B^n * ‖v‖) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (htr s hs) n)
        (solutionCoeff_norm v hB (fun i => hbound i s hs) n)
        (norm_nonneg _) (pow_nonneg hr _)
    _ = (r*B)^n * ‖v‖ := by rw [mul_pow]; ring

lemma parameterSolution_analyticAt {A : ℕ → ℂ → R} {U : Set ℂ}
    {t : ℂ → ℂ} {B r : ℝ} (hU : IsOpen U) (hB : 0 < B) (hr : 0 ≤ r)
    (hBr : r*B < 1) (hA : ∀ n, DifferentiableOn ℂ (A n) U)
    (hbound : ∀ n s, s ∈ U → ‖A n s‖ ≤ B^(n+1))
    (ht : DifferentiableOn ℂ t U) (htr : ∀ s ∈ U, ‖t s‖ ≤ r)
    (v : R) {s : ℂ} (hs : s ∈ U) :
    AnalyticAt ℂ (fun s => parameterSolution A v s (t s)) s :=
  (parameterSolution_differentiableOn hU hB hr hBr hA hbound ht htr v).analyticAt
    (hU.mem_nhds hs)

omit [CompleteSpace R] in
@[simp] lemma parameterSolution_zero (A : ℕ → ℂ → R) (v : R) (s : ℂ) :
    parameterSolution A v s 0 = v := by
  rw [parameterSolution,tsum_eq_single 0]
  · simp [solutionCoeff]
  · intro n hn
    simp [zero_pow hn]

omit [CompleteSpace R] in
lemma parameterSolution_eq_series_sum (A : ℕ → ℂ → R) (v : R) (s t : ℂ) :
    parameterSolution A v s t = (series (solutionCoeff (fun i => A i s) v)).sum t := by
  simp only [parameterSolution,FormalMultilinearSeries.sum,series,
    ContinuousMultilinearMap.mkPiRing_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma parameterSolution_hasDerivAt {A : ℕ → ℂ → R} {B : ℝ} (hB : 0 < B)
    {s t : ℂ} (hbound : ∀ n, ‖A n s‖ ≤ B^(n+1)) (ht : ‖t‖ < B⁻¹) (v : R) :
    HasDerivAt (parameterSolution A v s)
      ((series (fun i => A i s)).sum t * parameterSolution A v s t) t := by
  have hradA : ENNReal.ofReal B⁻¹ ≤ (series (fun i => A i s)).radius :=
    series_radius hB (fun n => by simpa [pow_succ] using hbound n)
  have hradY : ENNReal.ofReal B⁻¹ ≤ (series (solutionCoeff (fun i => A i s) v)).radius :=
    series_radius hB (solutionCoeff_norm v hB hbound)
  have hte : ‖t‖ₑ < ENNReal.ofReal B⁻¹ := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hB) |>.mpr ht
  have he : parameterSolution A v s = (series (solutionCoeff (fun i => A i s) v)).sum :=
    funext (parameterSolution_eq_series_sum A v s)
  rw [he]
  exact
    hasDerivAt_solutionSeries v hB hbound (hte.trans_le hradA) (hte.trans_le hradY)


omit [CompleteSpace R] in
lemma changeOriginSeries_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : FormalMultilinearSeries ℂ E R) (n l : ℕ) :
    ‖p.changeOriginSeries n l‖ ≤ (2 : ℝ)^(n+l) * ‖p (n+l)‖ := by
  have hc : Fintype.card {s : Finset (Fin (n+l)) // s.card=l} ≤ 2^(n+l) := by
    simpa only [Fintype.card_finset,Fintype.card_fin] using
      (Fintype.card_subtype_le (fun s : Finset (Fin (n+l)) => s.card=l))
  have hn := p.nnnorm_changeOriginSeries_le_tsum n l
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hn
  calc
    ‖p.changeOriginSeries n l‖ ≤
        (Fintype.card {s : Finset (Fin (n+l)) // s.card=l} : ℝ) * ‖p (n+l)‖ := by
      exact_mod_cast hn
    _ ≤ (2 : ℝ)^(n+l) * ‖p (n+l)‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact_mod_cast hc

omit [CompleteSpace R] in
lemma changeOrigin_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : FormalMultilinearSeries ℂ E R} {D C : ℝ} (hD : 0 < D) (hC : 0 ≤ C)
    (hp : ∀ n, ‖p n‖ ≤ C*D^n) {x : E} (hx : ‖x‖ ≤ (4*D)⁻¹) (n : ℕ) :
    ‖p.changeOrigin x n‖ ≤ (2*C) * (2*D)^n := by
  have hterm (l : ℕ) : ‖p.changeOriginSeries n l (fun _ => x)‖ ≤
      (C*(2*D)^n) * ((1/2 : ℝ)^l) := by
    calc
      _ ≤ ‖p.changeOriginSeries n l‖ * ‖x‖^l := by
        simpa using (p.changeOriginSeries n l).le_opNorm (fun _ => x)
      _ ≤ ((2 : ℝ)^(n+l) * (C*D^(n+l))) * ((4*D)⁻¹)^l := by
        apply mul_le_mul
        · exact (changeOriginSeries_norm_bound p n l).trans
            (mul_le_mul_of_nonneg_left (hp (n+l)) (by positivity))
        · exact pow_le_pow_left₀ (norm_nonneg _) hx l
        · positivity
        · positivity
      _ = (C*(2*D)^n) * ((1/2 : ℝ)^l) := by
        have he0 : (2 : ℝ)^(n+l) * (C*D^(n+l)) = C*((2*D)^(n+l)) := by
          rw [mul_pow]; ring
        rw [he0,pow_add]
        have he : (2*D) * (4*D)⁻¹ = (1/2 : ℝ) := by field_simp [hD.ne']; ring
        rw [show C * ((2*D)^n * (2*D)^l) * ((4*D)⁻¹)^l =
          (C*(2*D)^n) * (((2*D)*((4*D)⁻¹))^l) by rw [mul_pow (2*D) ((4*D)⁻¹) l]; ring]
        rw [he]
  have hs : Summable (fun l : ℕ => (C*(2*D)^n) * (1/2 : ℝ)^l) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left _
  calc
    _ ≤ ∑' l : ℕ, (C*(2*D)^n) * (1/2 : ℝ)^l := by
      exact tsum_of_norm_bounded hs.hasSum hterm
    _ = (2*C) * (2*D)^n := by
      rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)]
      ring

 

def verticalCoeff (p : FormalMultilinearSeries ℂ (ℂ × ℂ) R) (n : ℕ) (s : ℂ) : R :=
  p.changeOrigin (s,0) n (fun _ => (0,1))

lemma verticalCoeff_differentiableAt {p : FormalMultilinearSeries ℂ (ℂ × ℂ) R}
    (hp : 0 < p.radius) (n : ℕ) {s : ℂ} (hs : ‖s‖ₑ < p.radius) :
    DifferentiableAt ℂ (verticalCoeff p n) s := by
  have hs' : (s, (0:ℂ)) ∈ Metric.eball 0 p.radius := by
    rw [Metric.mem_eball,edist_eq_enorm_sub,sub_zero,← ofReal_norm]
    simpa using hs
  have hc := (p.hasFPowerSeriesOnBall_changeOrigin n hp).analyticAt_of_mem hs'
  exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => ℂ × ℂ) R
    (fun _ => (0,1))).differentiableAt.comp s
      (hc.differentiableAt.comp s (differentiableAt_id.prodMk (differentiableAt_const (0:ℂ))))

omit [CompleteSpace R] in
lemma verticalCoeff_bound {p : FormalMultilinearSeries ℂ (ℂ × ℂ) R}
    {D C : ℝ} (hD : 0 < D) (hC : 0 ≤ C) (hp : ∀ n, ‖p n‖ ≤ C*D^n)
    {s : ℂ} (hs : ‖s‖ ≤ (4*D)⁻¹) (n : ℕ) :
    ‖verticalCoeff p n s‖ ≤ (2*C) * (2*D)^n := by
  have he : ‖verticalCoeff p n s‖ ≤ ‖p.changeOrigin (s,0) n‖ := by
    simpa [verticalCoeff] using
      (p.changeOrigin (s,0) n).le_opNorm (fun _ => ((0:ℂ),(1:ℂ)))
  exact he.trans (changeOrigin_norm_bound hD hC hp (by simpa using hs) n)

omit [CompleteSpace R] in
lemma verticalCoeff_sum (p : FormalMultilinearSeries ℂ (ℂ × ℂ) R) (s t : ℂ) :
    (series (fun n => verticalCoeff p n s)).sum t = (p.changeOrigin (s,0)).sum (0,t) := by
  unfold FormalMultilinearSeries.sum
  apply tsum_congr
  intro n
  simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,series_coeff,verticalCoeff]
  convert! ((p.changeOrigin (s,0) n).map_smul_univ (fun _ => t) (fun _ => ((0:ℂ),(1:ℂ)))).symm using 1 <;> simp


lemma analytic_coefficient_polydisk {A : ℂ × ℂ → R} (hA : AnalyticAt ℂ A (0,0)) :
    ∃ (c : ℕ → ℂ → R) (δ B : ℝ), 0 < δ ∧ 0 < B ∧ δ*B < 1 ∧
      (∀ n, DifferentiableOn ℂ (c n) (Metric.ball 0 δ)) ∧
      (∀ n s, ‖s‖ < δ → ‖c n s‖ ≤ B^(n+1)) ∧
      (∀ s t, ‖s‖ < δ → ‖t‖ < δ → (series (fun n => c n s)).sum t = A (s,t)) := by
  obtain ⟨p,ρ,hp⟩ := hA
  obtain ⟨r,hr0,hrρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hr : 0 < r := by exact_mod_cast hr0
  have hrr : (0 : ℝ) < r := hr
  have hrp : (r : ENNReal) < p.radius := hrρ.trans_le hp.r_le
  obtain ⟨C,hC,hCp⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hr hrp
  let D : ℝ := (r : ℝ)⁻¹
  have hD : 0 < D := inv_pos.mpr hrr
  have hpd (n : ℕ) : ‖p n‖ ≤ C*D^n := by
    simpa [D,div_eq_mul_inv,inv_pow] using hCp n
  let B := max (2*C) (2*D)
  have hCB : 2*C ≤ B := le_max_left _ _
  have hDB : 2*D ≤ B := le_max_right _ _
  have hB : 0 < B := lt_of_lt_of_le (by positivity) hCB
  let δ := min ((4*D)⁻¹) (min ((r:ℝ)/3) (B⁻¹/2))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hδD : δ ≤ (4*D)⁻¹ := min_le_left _ _
  have hδr : δ ≤ (r:ℝ)/3 := (min_le_right _ _).trans (min_le_left _ _)
  have hδB : δ ≤ B⁻¹/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hδBr : δ*B < 1 := by
    calc
      δ*B ≤ (B⁻¹/2)*B := mul_le_mul_of_nonneg_right hδB hB.le
      _ = 1/2 := by field_simp
      _ < 1 := by norm_num
  have hsr (s : ℂ) (hs : ‖s‖ < δ) : ‖s‖ < (r:ℝ) := by linarith
  have hse (s : ℂ) (hs : ‖s‖ < δ) : ‖s‖ₑ < (r:ENNReal) := by exact_mod_cast hsr s hs
  refine ⟨verticalCoeff p,δ,B,hδ,hB,hδBr,?_,?_,?_⟩
  · intro n s hs
    apply (verticalCoeff_differentiableAt (hp.r_pos.trans_le hp.r_le) n
      ((hse s (by simpa using hs)).trans hrp)).differentiableWithinAt
  · intro n s hs
    calc
      ‖verticalCoeff p n s‖ ≤ (2*C)*(2*D)^n := verticalCoeff_bound hD hC.le hpd (hs.le.trans hδD) n
      _ ≤ B*B^n := mul_le_mul hCB (pow_le_pow_left₀ (by positivity) hDB n) (by positivity) hB.le
      _ = B^(n+1) := by rw [pow_succ,mul_comm]
  · intro s t hs ht
    rw [verticalCoeff_sum]
    have hsum : ‖s‖ + ‖t‖ < (r:ℝ) := by linarith
    have hsum' : (‖(s,(0:ℂ))‖₊ + ‖((0:ℂ),t)‖₊ : ENNReal) < (r:ENNReal) := by
      simp only [Prod.nnnorm_def,nnnorm_zero,max_eq_left (show (0:NNReal) ≤ ‖s‖₊ from zero_le),max_eq_right (show (0:NNReal) ≤ ‖t‖₊ from zero_le)]
      exact_mod_cast hsum
    rw [p.changeOrigin_eval (hsum'.trans hrp)]
    have hmem : (s,t) ∈ Metric.eball (0:ℂ × ℂ) ρ := by
      rw [Metric.mem_eball,edist_eq_enorm_sub,sub_zero,← ofReal_norm]
      apply lt_trans _ hrρ
      rw [← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_lt_ofReal_iff hrr |>.mpr
      exact max_lt (hsr s hs) (hsr t ht)
    simpa using (hp.sum hmem).symm

lemma parameterSolution_continuousOn {c : ℕ → ℂ → R} {U : Set ℂ}
    {B r : ℝ} (hB : 0 < B) (hr : 0 ≤ r) (hrB : r*B < 1)
    (hc : ∀ n, ContinuousOn (c n) U)
    (hbound : ∀ n s, s ∈ U → ‖c n s‖ ≤ B^(n+1)) (v : R) :
    ContinuousOn (fun w : ℂ × ℂ => parameterSolution c v w.1 w.2)
      (U ×ˢ Metric.closedBall 0 r) := by
  refine continuousOn_tsum (fun n => ?_)
    ((summable_geometric_of_lt_one (mul_nonneg hr hB.le) hrB).mul_right ‖v‖) ?_
  · have hsc (n : ℕ) : ContinuousOn (fun s => solutionCoeff (fun i => c i s) v n) U := by
      induction n using Nat.strong_induction_on with
      | h n ih =>
        cases n with
        | zero => simpa [solutionCoeff] using (continuousOn_const (c := v) (s := U))
        | succ n =>
          simp only [solutionCoeff]
          apply ContinuousOn.const_smul
          apply continuousOn_finsetSum
          intro i hi
          exact (hc i).mul (ih (n-i) (by omega))
    exact (continuousOn_snd.pow n).smul ((hsc n).comp continuousOn_fst (fun _ hw => hw.1))
  · intro n w hw
    change ‖w.2^n • solutionCoeff (fun i => c i w.1) v n‖ ≤ (r*B)^n * ‖v‖
    rw [norm_smul,norm_pow]
    have hwr : ‖w.2‖ ≤ r := by simpa using hw.2
    calc
      _ ≤ r^n * (B^n*‖v‖) := mul_le_mul
        (pow_le_pow_left₀ (norm_nonneg _) hwr n)
        (solutionCoeff_norm v hB (fun i => hbound i w.1 hw.1) n)
        (norm_nonneg _) (pow_nonneg hr _)
      _ = _ := by rw [mul_pow]; ring



lemma parameterSolution_analyticAt_curves {c : ℕ → ℂ → R} {δ B : ℝ}
    (hδ : 0 < δ) (hB : 0 < B) (hδB : δ*B < 1)
    (hc : ∀ n, DifferentiableOn ℂ (c n) (Metric.ball 0 δ))
    (hbound : ∀ n s, ‖s‖ < δ → ‖c n s‖ ≤ B^(n+1))
    {q t : ℂ → ℂ} {z : ℂ} (hq : AnalyticAt ℂ q z) (ht : AnalyticAt ℂ t z)
    (hqδ : ‖q z‖ < δ) (htδ : ‖t z‖ < δ) (v : R) :
    AnalyticAt ℂ (fun w => parameterSolution c v (q w) (t w)) z := by
  have hqb' : ∀ᶠ w in 𝓝 z, q w ∈ Metric.ball 0 δ :=
    hq.continuousAt.eventually (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hqδ))
  have htb' : ∀ᶠ w in 𝓝 z, t w ∈ Metric.ball 0 δ :=
    ht.continuousAt.eventually (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr htδ))
  have hqb : ∀ᶠ w in 𝓝 z, ‖q w‖ < δ := hqb'.mono (fun _ hw => mem_ball_zero_iff.mp hw)
  have htb : ∀ᶠ w in 𝓝 z, ‖t w‖ < δ := htb'.mono (fun _ hw => mem_ball_zero_iff.mp hw)
  obtain ⟨η,hη,he⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hq.eventually_analyticAt.and ht.eventually_analyticAt).and (hqb.and htb))
  have hqd : DifferentiableOn ℂ q (Metric.ball z η) := fun w hw =>
    (he w hw).1.1.differentiableAt.differentiableWithinAt
  have htd : DifferentiableOn ℂ t (Metric.ball z η) := fun w hw =>
    (he w hw).1.2.differentiableAt.differentiableWithinAt
  have hcd (n : ℕ) : DifferentiableOn ℂ (fun w => c n (q w)) (Metric.ball z η) :=
    (hc n).comp hqd (fun w hw => by simpa using (he w hw).2.1)
  exact parameterSolution_analyticAt Metric.isOpen_ball hB hδ.le hδB hcd
    (fun n w hw => hbound n (q w) (he w hw).2.1) htd
    (fun w hw => (he w hw).2.2.le) v (Metric.mem_ball_self hη)

 

lemma exists_parameter_fundamental {A : ℂ × ℂ → R} (hA : AnalyticAt ℂ A (0,0)) :
    ∃ (Y : ℂ → ℂ → R) (ε : ℝ), 0 < ε ∧
      (∀ s, Y s 0 = 1) ∧
      (∀ s t, ‖s‖ < ε → ‖t‖ < ε →
        HasDerivAt (Y s) (A (s,t)*Y s t) t ∧ IsUnit (Y s t)) ∧
      (∀ (q t : ℂ → ℂ) z, AnalyticAt ℂ q z → AnalyticAt ℂ t z →
        ‖q z‖ < ε → ‖t z‖ < ε → AnalyticAt ℂ (fun w => Y (q w) (t w)) z) := by
  obtain ⟨c,δ,B,hδ,hB,hδB,hc,hbound,hsum⟩ := analytic_coefficient_polydisk hA
  let Y := parameterSolution c (1:R)
  have hYc : ContinuousAt (fun w : ℂ × ℂ => Y w.1 w.2) (0,0) := by
    apply (parameterSolution_continuousOn hB hδ.le hδB
      (fun n => (hc n).continuousOn) (fun n s hs => hbound n s (by simpa using hs)) 1).continuousAt
    exact prod_mem_nhds (Metric.ball_mem_nhds 0 hδ) (Metric.closedBall_mem_nhds 0 hδ)
  have hYu : ∀ᶠ w : ℂ × ℂ in 𝓝 (0,0), IsUnit (Y w.1 w.2) := by
    apply hYc.eventually
    have hy0 : Y 0 0 = 1 := parameterSolution_zero c 1 0
    apply Units.isOpen.mem_nhds
    change IsUnit (Y 0 0)
    rw [hy0]
    exact isUnit_one
  obtain ⟨η,hη,hηu⟩ := Metric.eventually_nhds_iff_ball.mp hYu
  let ε := min δ η
  have hε : 0 < ε := lt_min hδ hη
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  refine ⟨Y,ε,hε,parameterSolution_zero c 1,?_,?_⟩
  · intro s t hs ht
    constructor
    · have htB : ‖t‖ < B⁻¹ := by
        have hdB : δ < B⁻¹ := by
          apply (mul_lt_mul_iff_left₀ hB).mp
          rw [inv_mul_cancel₀ hB.ne']
          simpa [mul_comm] using hδB
        exact (ht.trans_le hεδ).trans hdB
      have hd := parameterSolution_hasDerivAt hB (fun n => hbound n s (hs.trans_le hεδ)) htB (1:R)
      rw [hsum s t (hs.trans_le hεδ) (ht.trans_le hεδ)] at hd
      exact hd
    · apply hηu (s,t)
      simp only [Metric.mem_ball,dist_eq_norm,Prod.mk_sub_mk,sub_zero,Prod.norm_def]
      exact max_lt (hs.trans_le hεη) (ht.trans_le hεη)
  · intro q t z hq ht hqε htε
    exact parameterSolution_analyticAt_curves hδ hB hδB hc hbound hq ht
      (hqε.trans_le hεδ) (htε.trans_le hεδ) 1





end

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

omit [CompleteSpace R] in
lemma idempotent_derivative {P : ℂ → R} {P' : R} {z : ℂ}
    (hP : HasDerivAt P P' z) (hid : ∀ᶠ w in 𝓝 z, P w * P w = P w) :
    P' * P z + P z * P' = P' := by
  exact (hP.mul hP).unique (hP.congr_of_eventuallyEq hid)

omit [NormedAlgebra ℂ R] [CompleteSpace R] in
lemma projector_derivative_sandwich {p q : R} (hp : p*p=p)
    (hq : q*p+p*q=q) : p*q*p=0 := by
  have hh := congrArg (fun a => p*a) hq
  have he : p*q*p+p*q=p*q := by
    simpa only [mul_add,← mul_assoc,hp] using hh
  exact add_eq_right.mp he

 

def projectorODE (P B : ℂ → R) (z : ℂ) : R :=
  deriv P z * P z - P z * deriv P z - P z * B z * P z

omit [CompleteSpace R] in
lemma projectorODE_commutator {P B : ℂ → R} {z : ℂ}
    (hP : DifferentiableAt ℂ P z) (hid : ∀ᶠ w in 𝓝 z, P w*P w=P w) :
    projectorODE P B z * P z - P z * projectorODE P B z = deriv P z := by
  have hh := idempotent_derivative hP.hasDerivAt hid
  have hp := hid.self_of_nhds
  have hz := projector_derivative_sandwich hp hh
  calc
    projectorODE P B z * P z - P z * projectorODE P B z =
      deriv P z * (P z*P z) + (P z*P z)*deriv P z -
      (P z*deriv P z*P z+P z*deriv P z*P z) -
      P z*B z*(P z*P z)+(P z*P z)*B z*P z := by
        unfold projectorODE
        noncomm_ring
    _ = deriv P z := by rw [hp,hz,add_zero,sub_zero,sub_add_cancel,hh]

lemma projectorODE_analyticAt {P B : ℂ → R} {z : ℂ}
    (hP : AnalyticAt ℂ P z) (hB : AnalyticAt ℂ B z) :
    AnalyticAt ℂ (projectorODE P B) z :=
  ((hP.deriv.mul hP).sub (hP.mul hP.deriv)).sub ((hP.mul hB).mul hP)

 

theorem exists_local_projector_transport {P B : ℂ → R} {x : ℂ}
    (hP : AnalyticAt ℂ P x) (hB : AnalyticAt ℂ B x)
    (hid : ∀ᶠ z in 𝓝 x, P z*P z=P z) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ T : ℂ → ℂ → R,
      AnalyticOnNhd ℂ (fun w : ℂ × ℂ => T w.1 w.2)
        (Metric.ball x ε ×ˢ Metric.ball x ε) ∧
      (∀ s ∈ Metric.ball x ε, T s s=1) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε, IsUnit (T s t)) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε, ∀ u ∈ Metric.ball x ε,
        T t u*T s t=T s u) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε,
        HasDerivAt (T s) (projectorODE P B t * T s t) t) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε,
        P t*T s t=T s t*P s) := by
  have hA := projectorODE_analyticAt hP hB
  obtain ⟨Y,hYa,hYx,hY⟩ := exists_local_fundamental hA
  have hpd : ∀ᶠ z in 𝓝 x, HasDerivAt P
      (projectorODE P B z * P z-P z*projectorODE P B z) z := by
    filter_upwards [hP.eventually_analyticAt,eventually_eventually_nhds.mpr hid] with z hz hi
    rw [projectorODE_commutator hz.differentiableAt hi]
    exact hz.differentiableAt.hasDerivAt
  have hint := intertwine_eventually hA hYx (hY.mono fun _ h => h.1) hpd
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff_ball.mp
    (hYa.eventually_analyticAt.and (hY.and hint))
  refine ⟨ε,hε,transport Y,?_,?_,?_,?_,?_,?_⟩
  · intro w hw
    exact transport_analyticAt (he w.1 hw.1).1 (he w.2 hw.2).1 (he w.1 hw.1).2.1.2
  · intro s hs
    exact transport_self (he s hs).2.1.2
  · intro s hs t ht
    exact transport_isUnit (he s hs).2.1.2 (he t ht).2.1.2
  · intro s hs t ht u hu
    exact transport_trans (he t ht).2.1.2
  · intro s hs t ht
    exact transport_hasDerivAt (he t ht).2.1.1
  · intro s hs t ht
    exact transport_intertwines (he s hs).2.2 (he t ht).2.2 (he s hs).2.1.2

end SplitTangent.HolomorphicLinearODE

namespace SplitTangent.ParameterProjector
section
open HolomorphicLinearODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

 
def verticalDerivative (P : ℂ × ℂ → R) (w : ℂ × ℂ) : R := fderiv ℂ P w (0,1)

omit [CompleteSpace R] in
lemma hasDerivAt_vertical {P : ℂ × ℂ → R} {s t : ℂ}
    (hP : DifferentiableAt ℂ P (s,t)) :
    HasDerivAt (fun v => P (s,v)) (verticalDerivative P (s,t)) t := by
  exact hP.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))

lemma verticalDerivative_analyticAt {P : ℂ × ℂ → R} {w : ℂ × ℂ}
    (hP : AnalyticAt ℂ P w) : AnalyticAt ℂ (verticalDerivative P) w :=
  ((ContinuousLinearMap.apply ℂ R (E := ℂ × ℂ)).analyticAt_bilinear _).comp
    (analyticAt_const.prod hP.fderiv)

def equation (P B : ℂ × ℂ → R) (w : ℂ × ℂ) : R :=
  verticalDerivative P w * P w - P w * verticalDerivative P w - P w * B w * P w

lemma equation_analyticAt {P B : ℂ × ℂ → R} {w : ℂ × ℂ}
    (hP : AnalyticAt ℂ P w) (hB : AnalyticAt ℂ B w) : AnalyticAt ℂ (equation P B) w :=
  (((verticalDerivative_analyticAt hP).mul hP).sub
    (hP.mul (verticalDerivative_analyticAt hP))).sub ((hP.mul hB).mul hP)

omit [CompleteSpace R] in
lemma equation_eq {P B : ℂ × ℂ → R} {s t : ℂ}
    (hP : DifferentiableAt ℂ P (s,t)) :
    equation P B (s,t) = projectorODE (fun v => P (s,v)) (fun v => B (s,v)) t := by
  simp only [equation,projectorODE,(hasDerivAt_vertical hP).deriv]

 

lemma exists_preserving_parameter_fundamental {P B : ℂ × ℂ → R}
    (hP : AnalyticAt ℂ P (0,0)) (hB : AnalyticAt ℂ B (0,0))
    (hid : ∀ᶠ w in 𝓝 (0,0), P w*P w=P w) :
    ∃ (Y : ℂ → ℂ → R) (ε : ℝ), 0 < ε ∧
      (∀ s, Y s 0=1) ∧
      (∀ s t, ‖s‖ < ε → ‖t‖ < ε →
        HasDerivAt (Y s) (equation P B (s,t)*Y s t) t ∧ IsUnit (Y s t)) ∧
      (∀ s t, ‖s‖ < ε → ‖t‖ < ε → P (s,t)*Y s t=Y s t*P (s,0)) ∧
      (∀ (q t : ℂ → ℂ) z, AnalyticAt ℂ q z → AnalyticAt ℂ t z →
        ‖q z‖ < ε → ‖t z‖ < ε → AnalyticAt ℂ (fun w => Y (q w) (t w)) z) := by
  have hA := equation_analyticAt hP hB
  obtain ⟨Y,r,hr,hY0,hYd,hYa⟩ := exists_parameter_fundamental hA
  obtain ⟨η,hη,hηd⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hP.eventually_analyticAt.and hA.eventually_analyticAt).and hid)
  let ε := min r η
  have hε : 0 < ε := lt_min hr hη
  have hεr : ε ≤ r := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  have hpol (s t : ℂ) (hs : ‖s‖ < ε) (ht : ‖t‖ < ε) :
      AnalyticAt ℂ P (s,t) ∧ AnalyticAt ℂ (equation P B) (s,t) ∧ P (s,t)*P (s,t)=P (s,t) := by
    have hm : (s,t) ∈ Metric.ball (0,0) η := by
      simp only [Metric.mem_ball,dist_eq_norm,Prod.mk_sub_mk,sub_zero,Prod.norm_def]
      exact max_lt (hs.trans_le hεη) (ht.trans_le hεη)
    exact ⟨(hηd (s,t) hm).1.1,(hηd (s,t) hm).1.2,(hηd (s,t) hm).2⟩
  refine ⟨Y,ε,hε,hY0,fun s t hs ht => hYd s t (hs.trans_le hεr) (ht.trans_le hεr),?_,?_⟩
  · intro s t hs ht
    have hconn (v : ℂ) (hv : v ∈ Metric.ball 0 ε) :
        HasDerivAt (fun w => P (s,w))
          (equation P B (s,v)*P (s,v)-P (s,v)*equation P B (s,v)) v := by
      have hpa := (hpol s v hs (mem_ball_zero_iff.mp hv)).1
      have hpd := hasDerivAt_vertical hpa.differentiableAt
      have hi : ∀ᶠ w in 𝓝 v, P (s,w)*P (s,w)=P (s,w) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hv] with w hw
        exact (hpol s w hs (mem_ball_zero_iff.mp hw)).2.2
      rw [equation_eq hpa.differentiableAt,
        projectorODE_commutator hpd.differentiableAt hi]
      exact hpd.differentiableAt.hasDerivAt
    have ha : AnalyticOnNhd ℂ (fun v => equation P B (s,v)) (Metric.ball 0 ε) := by
      intro v hv
      exact (hpol s v hs (mem_ball_zero_iff.mp hv)).2.1.comp (analyticAt_const.prod analyticAt_id)
    have he := eqOn_of_solution (f := fun v => P (s,v)*Y s v)
      Metric.isOpen_ball (convex_ball (0:ℂ) ε).isPreconnected ha
      (fun v hv => gauge_hasDerivAt (A := fun v => equation P B (s,v))
        (B := fun v => equation P B (s,v)) (H := fun v => P (s,v)) (Y := Y s) (hconn v hv)
        (hYd s v (hs.trans_le hεr) ((mem_ball_zero_iff.mp hv).trans_le hεr)).1)
      (g := fun v => Y s v * P (s,0)) ?_ (Metric.mem_ball_self hε) ?_
    · exact he (mem_ball_zero_iff.mpr ht)
    · intro v hv
      convert! ((hYd s v (hs.trans_le hεr) ((mem_ball_zero_iff.mp hv).trans_le hεr)).1).mul_const (P (s,0)) using 1; try rfl
      exact (mul_assoc _ _ _).symm
    · simp only [hY0,mul_one,one_mul]
  · intro q t z hq ht hqε htε
    exact hYa q t z hq ht (hqε.trans_le hεr) (htε.trans_le hεr)

end

open HolomorphicLinearODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

lemma exists_preserving_parameter_transport {P B : ℂ × ℂ → R}
    (hP : AnalyticAt ℂ P (0,0)) (hB : AnalyticAt ℂ B (0,0))
    (hid : ∀ᶠ w in 𝓝 (0,0), P w*P w=P w) :
    ∃ (T : ℂ → ℂ → ℂ → R) (ε : ℝ), 0 < ε ∧
      (∀ s u, ‖s‖ < ε → ‖u‖ < ε → T s u u=1) ∧
      (∀ s u v, ‖s‖ < ε → ‖u‖ < ε → ‖v‖ < ε → IsUnit (T s u v)) ∧
      (∀ s u v w, ‖s‖ < ε → ‖u‖ < ε → ‖v‖ < ε → ‖w‖ < ε →
        T s v w*T s u v=T s u w) ∧
      (∀ s u v, ‖s‖ < ε → ‖u‖ < ε → ‖v‖ < ε →
        HasDerivAt (T s u) (equation P B (s,v)*T s u v) v ∧
        P (s,v)*T s u v=T s u v*P (s,u)) ∧
      (∀ (q u v : ℂ → ℂ) z, AnalyticAt ℂ q z → AnalyticAt ℂ u z → AnalyticAt ℂ v z →
        ‖q z‖ < ε → ‖u z‖ < ε → ‖v z‖ < ε →
        AnalyticAt ℂ (fun w => T (q w) (u w) (v w)) z) := by
  obtain ⟨Y,ε,hε,hY0,hYd,hYP,hYa⟩ := exists_preserving_parameter_fundamental hP hB hid
  refine ⟨fun s => transport (Y s),ε,hε,?_,?_,?_,?_,?_⟩
  · intro s u hs hu
    exact transport_self (hYd s u hs hu).2
  · intro s u v hs hu hv
    exact transport_isUnit (hYd s u hs hu).2 (hYd s v hs hv).2
  · intro s u v w hs hu hv hw
    exact transport_trans (hYd s v hs hv).2
  · intro s u v hs hu hv
    exact ⟨transport_hasDerivAt (A := fun t => equation P B (s,t)) (hYd s v hs hv).1,
      transport_intertwines (P := fun t => P (s,t)) (hYP s u hs hu) (hYP s v hs hv) (hYd s u hs hu).2⟩
  · intro q u v z hq hu hv hqs hus hvs
    have hsu := hYa q u z hq hu hqs hus
    have hsv := hYa q v z hq hv hqs hvs
    exact hsv.mul ((analyticOnNhd_inverse (𝕜 := ℂ) _ (hYd (q z) (u z) hqs hus).2).comp_of_eq hsu rfl)

end SplitTangent.ParameterProjector

namespace SplitTangent.HolomorphicLinearODE
open Filter Topology Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma inverse_apply_horizontal {Y : ℂ → E →L[ℂ] E} {v : ℂ → E}
    {A : E →L[ℂ] E} {z : ℂ}
    (hY : HasDerivAt Y (A * Y z) z) (hv : HasDerivAt v (A (v z)) z)
    (hu : IsUnit (Y z)) :
    HasDerivAt (fun w => Ring.inverse (Y w) (v w)) 0 z := by
  obtain ⟨u,he⟩ := hu
  have hi : HasDerivAt (fun w => Ring.inverse (Y w))
      (-(Ring.inverse (Y z) * (A * Y z) * Ring.inverse (Y z))) z := by
    have h := (hasFDerivAt_ringInverse (𝕜 := ℂ) u)
    rw [he] at h
    convert! h.comp_hasDerivAt z hY using 1; try rfl
    simp only [neg_apply,ContinuousLinearMap.mulLeftRight_apply]
    rw [← Ring.inverse_unit u,he]
  convert! hi.clm_apply hv using 1; try rfl
  have hc : Y z * Ring.inverse (Y z) = 1 := Ring.mul_inverse_cancel _ ⟨u,he⟩
  rw [mul_assoc (Ring.inverse (Y z)),mul_assoc A,hc,mul_one]
  simp only [neg_apply,mul_apply_eq_comp,neg_add_cancel]

 
theorem vector_local_uniqueness {A : ℂ → E →L[ℂ] E} {f g : ℂ → E} {x : ℂ}
    (hA : AnalyticAt ℂ A x)
    (hf : ∀ᶠ z in 𝓝 x, HasDerivAt f (A z (f z)) z)
    (hg : ∀ᶠ z in 𝓝 x, HasDerivAt g (A z (g z)) z)
    (he : f x = g x) : f =ᶠ[𝓝 x] g := by
  obtain ⟨Y,hYa,hY0,hY⟩ := exists_local_fundamental hA
  obtain ⟨ε,hε,hs⟩ := Metric.eventually_nhds_iff_ball.mp (hY.and (hf.and hg))
  let D : ℂ → E := fun z => Ring.inverse (Y z) (f z-g z)
  have hd (z : ℂ) (hz : z ∈ Metric.ball x ε) : HasDerivAt D 0 z := by
    have hsub : HasDerivAt (fun w => f w-g w) (A z (f z-g z)) z := by
      convert! (hs z hz).2.1.sub (hs z hz).2.2 using 1; try rfl
      exact map_sub _ _ _
    exact inverse_apply_horizontal (hs z hz).1.1 hsub (hs z hz).1.2
  filter_upwards [Metric.ball_mem_nhds x hε] with z hz
  have hc : D z = D x := Metric.isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball x ε).isPreconnected
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).deriv) hz (Metric.mem_ball_self hε)
  have hmul := congrArg (Y z) hc
  have hcancel := congrArg (fun A : E →L[ℂ] E => A (f z-g z))
    (Ring.mul_inverse_cancel (Y z) (hs z hz).1.2)
  have hz0 : f z-g z = 0 := by
    simpa only [D,he,sub_self,map_zero,← mul_apply_eq_comp,
      Ring.mul_inverse_cancel _ (hs z hz).1.2,one_apply_eq_self] using hmul
  exact sub_eq_zero.mp hz0

end SplitTangent.HolomorphicLinearODE

open Filter Topology Set

namespace SplitTangent.HorizontalCovering
section
open Bundle
variable {ι B V : Type*} [TopologicalSpace B] [TopologicalSpace V] [DiscreteTopology V]

 

structure HorizontalCocycle (ι B V : Type*) [TopologicalSpace B] where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet : ∀ x, x ∈ baseSet (indexAt x)
  change : ι → ι → B → V → V
  change_self : ∀ i x, x ∈ baseSet i → ∀ v, change i i x v=v
  change_comp : ∀ i j k x, x ∈ baseSet i ∩ baseSet j ∩ baseSet k → ∀ v,
    change j k x (change i j x v)=change i k x v
  change_locally_constant : ∀ i j x, x ∈ baseSet i ∩ baseSet j → ∀ v,
    ∀ᶠ y in 𝓝 x, change i j y v=change i j x v

namespace HorizontalCocycle
variable (D : HorizontalCocycle ι B V)

 

def toCore : FiberBundleCore ι B V where
  baseSet := D.baseSet
  isOpen_baseSet := D.isOpen_baseSet
  indexAt := D.indexAt
  mem_baseSet_at := D.mem_baseSet
  coordChange := D.change
  coordChange_self := D.change_self
  continuousOn_coordChange := by
    intro i j
    apply continuousOn_prod_of_discrete_right.mpr
    intro v x hx
    exact (continuousAt_const.congr_of_eventuallyEq
      (D.change_locally_constant i j x hx.1 v)).continuousWithinAt
  coordChange_comp := D.change_comp

 

theorem isCoveringMap : IsCoveringMap D.toCore.proj :=
  FiberBundle.isCoveringMap

 

theorem coordinates_locally_constant {A : Type*} [TopologicalSpace A]
    {f : A → B} {s : C(A,D.toCore.TotalSpace)} (hs : D.toCore.proj ∘ s=f)
    {a : A} {i : ι} (ha : f a ∈ D.baseSet i) :
    ∀ᶠ y in 𝓝 a, (D.toCore.localTriv i (s y)).2=(D.toCore.localTriv i (s a)).2 := by
  have hsource : s a ∈ (D.toCore.localTriv i).source := by
    rw [D.toCore.mem_localTriv_source,← D.toCore.baseSet_at]
    change D.toCore.proj (s a) ∈ D.baseSet i
    rw [show D.toCore.proj (s a)=f a from congrFun hs a]
    exact ha
  have hc : ContinuousAt (fun y => (D.toCore.localTriv i (s y)).2) a :=
    ((D.toCore.localTriv i).toOpenPartialHomeomorph.continuousAt hsource).snd.comp s.continuous.continuousAt
  simpa only [ContinuousAt,nhds_discrete,tendsto_pure] using hc

 

theorem lift_local_form {A : Type*} [TopologicalSpace A]
    {f : A → B} (hf : Continuous f) {s : C(A,D.toCore.TotalSpace)}
    (hs : D.toCore.proj ∘ s=f) {a : A} {i : ι} (ha : f a ∈ D.baseSet i) :
    ∀ᶠ y in 𝓝 a, s y=(D.toCore.localTriv i).toPartialEquiv.symm
      (f y,(D.toCore.localTriv i (s a)).2) := by
  filter_upwards [D.coordinates_locally_constant hs ha,
    hf.continuousAt ((D.isOpen_baseSet i).mem_nhds ha)] with y hy hbase
  have hsource : s y ∈ (D.toCore.localTriv i).source := by
    rw [D.toCore.mem_localTriv_source,← D.toCore.baseSet_at]
    change D.toCore.proj (s y) ∈ D.baseSet i
    rw [show D.toCore.proj (s y)=f y from congrFun hs y]
    exact hbase
  have he : D.toCore.localTriv i (s y)=(f y,(D.toCore.localTriv i (s a)).2) := by
    apply Prod.ext
    · exact ((D.toCore.localTriv i).coe_fst hsource).trans (congrFun hs y)
    · exact hy
  rw [← he]
  exact ((D.toCore.localTriv i).toPartialEquiv.left_inv hsource).symm



end HorizontalCocycle
end

variable {B : Type*} [TopologicalSpace B] {V : B → Type*}

 

structure LocalTransportData (B : Type*) [TopologicalSpace B] (V : B → Type*) where
  domain : B → Set B
  domain_open : ∀ x, IsOpen (domain x)
  domain_self : ∀ x, x ∈ domain x
  forward : ∀ x y, V x → V y
  reverse : ∀ x y, V y → V x
  left_inv : ∀ x y, y ∈ domain x → Function.LeftInverse (reverse x y) (forward x y)
  right_inv : ∀ x y, y ∈ domain x → Function.RightInverse (reverse x y) (forward x y)
  forward_self : ∀ x v, forward x x v=v
  overlap : ∀ x y z, z ∈ domain x ∩ domain y → ∀ v : V x,
    ∀ᶠ w in 𝓝 z, forward y w (reverse y z (forward x z v))=forward x w v

namespace LocalTransportData
variable (D : LocalTransportData B V)

def localEquiv (x y : B) (hy : y ∈ D.domain x) : V x ≃ V y where
  toFun := D.forward x y
  invFun := D.reverse x y
  left_inv := D.left_inv x y hy
  right_inv := D.right_inv x y hy

lemma reverse_self (x : B) (v : V x) : D.reverse x x v=v := by
  simpa only [D.forward_self] using D.left_inv x x (D.domain_self x) v

include D in
 

theorem equiv_nonempty [ConnectedSpace B] (a x : B) : Nonempty (V a ≃ V x) := by
  let Z : Set B := {x | Nonempty (V a ≃ V x)}
  have ho : IsOpen Z := isOpen_iff_mem_nhds.mpr fun x hx =>
    Filter.mem_of_superset ((D.domain_open x).mem_nhds (D.domain_self x))
      (fun y hy => hx.map (fun e => e.trans (D.localEquiv x y hy)))
  have hoc : IsOpen Zᶜ := isOpen_iff_mem_nhds.mpr fun x hx =>
    Filter.mem_of_superset ((D.domain_open x).mem_nhds (D.domain_self x)) (fun y hy he =>
      hx (he.map (fun e => e.trans (D.localEquiv x y hy).symm)))
  have hu : Z=univ := (show IsClopen Z from ⟨isOpen_compl_iff.mp hoc,ho⟩).eq_univ
    ⟨a,⟨Equiv.refl _⟩⟩
  exact (show x ∈ Z from hu ▸ mem_univ x)

def fiberEquiv [ConnectedSpace B] (a x : B) : V a ≃ V x :=
  Classical.choice (D.equiv_nonempty a x)

 

def toCocycle [ConnectedSpace B] (a : B) : HorizontalCocycle B B (V a) where
  baseSet := D.domain
  isOpen_baseSet := D.domain_open
  indexAt := id
  mem_baseSet := D.domain_self
  change := fun i j z v => (D.fiberEquiv a j).symm
    (D.reverse j z (D.forward i z (D.fiberEquiv a i v)))
  change_self := by
    intro i z hz v
    rw [D.left_inv i z hz]
    exact (D.fiberEquiv a i).symm_apply_apply v
  change_comp := by
    intro i j k z hz v
    simp only [Equiv.apply_symm_apply]
    rw [D.right_inv j z hz.1.2 (D.forward i z (D.fiberEquiv a i v))]
  change_locally_constant := by
    intro i j z hz v
    filter_upwards [D.overlap i j z hz (D.fiberEquiv a i v),
      (D.domain_open j).mem_nhds hz.2] with w he hw
    have hh := congrArg (D.reverse j w) he
    rw [D.left_inv j w hw] at hh
    exact congrArg (D.fiberEquiv a j).symm hh.symm

variable [ConnectedSpace B] (a : B) [TopologicalSpace (V a)] [DiscreteTopology (V a)]

 
def decode (p : (D.toCocycle a).toCore.TotalSpace) : (b : B) × V b :=
  ⟨p.proj,D.fiberEquiv a p.proj p.2⟩

def encode (x : B) (v : V x) : (D.toCocycle a).toCore.TotalSpace :=
  ⟨x,(D.fiberEquiv a x).symm v⟩

@[simp] lemma decode_encode (x : B) (v : V x) : D.decode a (D.encode a x v)=⟨x,v⟩ := by
  change (⟨x,D.fiberEquiv a x ((D.fiberEquiv a x).symm v)⟩ : (b : B) × V b)=_
  rw [Equiv.apply_symm_apply]

lemma decode_local_frame {i x : B} (_ : x ∈ D.domain i) (v : V a) :
    D.decode a (((D.toCocycle a).toCore.localTriv i).toPartialEquiv.symm (x,v)) =
      ⟨x,D.forward i x (D.fiberEquiv a i v)⟩ := by
  change (⟨x,D.fiberEquiv a x ((D.fiberEquiv a x).symm
    (D.reverse x x (D.forward i x (D.fiberEquiv a i v)) ))⟩ : (b : B) × V b) = _
  simp only [Equiv.apply_symm_apply,D.reverse_self]

 

theorem decode_lift_local_form {A : Type*} [TopologicalSpace A] {f : A → B}
    (hf : Continuous f) {s : C(A,(D.toCocycle a).toCore.TotalSpace)}
    (hs : (D.toCocycle a).toCore.proj ∘ s=f) {z : A} {i : B}
    (hi : f z ∈ D.domain i) :
    ∃ v : V i, ∀ᶠ y in 𝓝 z, D.decode a (s y)=⟨f y,D.forward i (f y) v⟩ := by
  refine ⟨D.fiberEquiv a i (((D.toCocycle a).toCore.localTriv i) (s z)).2,?_⟩
  filter_upwards [(D.toCocycle a).lift_local_form hf hs hi,
    hf.continuousAt ((D.domain_open i).mem_nhds hi)] with y hy hbase
  rw [hy,D.decode_local_frame a hbase]

end LocalTransportData
end SplitTangent.HorizontalCovering

namespace SplitTangent.HorizontalCovering.LocalTransportData
variable {B : Type*} [TopologicalSpace B] {V : B → Type*}
variable (D : LocalTransportData B V)

 

def IsHorizontalAlong {A : Type*} [TopologicalSpace A] (f : A → B)
    (σ : A → (b : B) × V b) : Prop :=
  ∀ a, ∃ v : V (f a), ∀ᶠ y in 𝓝 a, σ y=⟨f y,D.forward (f a) (f y) v⟩

lemma horizontal_local_form {A : Type*} [TopologicalSpace A] {f : A → B}
    {σ : A → (b : B) × V b} (hσ : D.IsHorizontalAlong f σ) (a : A) :
    ∃ v : V (f a), σ a=⟨f a,v⟩ ∧ ∀ᶠ y in 𝓝 a, σ y=⟨f y,D.forward (f a) (f y) v⟩ := by
  obtain ⟨v,hv⟩ := hσ a
  exact ⟨v,by simpa only [D.forward_self] using hv.self_of_nhds,hv⟩



theorem horizontal_equalizer_clopen {A : Type*} [TopologicalSpace A] {f : A → B}
    (hf : Continuous f) {σ τ : A → (b : B) × V b}
    (hσ : D.IsHorizontalAlong f σ) (hτ : D.IsHorizontalAlong f τ) :
    IsClopen {a | σ a=τ a} := by
  have hevent (a : A) : ∀ᶠ y in 𝓝 a, (σ y=τ y) ↔ (σ a=τ a) := by
    obtain ⟨v,hv,hσv⟩ := D.horizontal_local_form hσ a
    obtain ⟨w,hw,hτw⟩ := D.horizontal_local_form hτ a
    filter_upwards [hσv,hτw,hf.continuousAt ((D.domain_open (f a)).mem_nhds (D.domain_self (f a)))] with y hy hz hd
    rw [hy,hz,hv,hw]
    constructor
    · intro he
      have hvw : v=w := (D.left_inv (f a) (f y) hd).injective (sigma_mk_injective he)
      rw [hvw]
    · intro he
      rw [sigma_mk_injective he]
  constructor
  · apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    exact (hevent a).mono fun y hy he => ha (hy.mp he)
  · apply isOpen_iff_mem_nhds.mpr
    intro a ha
    exact (hevent a).mono fun y hy => hy.mpr ha

 

theorem horizontal_unique {A : Type*} [TopologicalSpace A] [ConnectedSpace A]
    {f : A → B} (hf : Continuous f) {σ τ : A → (b : B) × V b}
    (hσ : D.IsHorizontalAlong f σ) (hτ : D.IsHorizontalAlong f τ)
    (a : A) (he : σ a=τ a) : σ=τ := by
  have hu := (D.horizontal_equalizer_clopen hf hσ hτ).eq_univ ⟨a,he⟩
  exact funext fun y => show y ∈ {a | σ a=τ a} from hu ▸ mem_univ y

variable [ConnectedSpace B]

 

theorem exists_normalized_horizontal {A : Type*} [TopologicalSpace A]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    {f : A → B} (hf : Continuous f) (a : A) (v : V (f a)) :
    ∃ σ : A → (b : B) × V b, D.IsHorizontalAlong f σ ∧ σ a=⟨f a,v⟩ := by
  let : TopologicalSpace (V (f a)) := ⊥
  let : DiscreteTopology (V (f a)) := ⟨rfl⟩
  let C := D.toCocycle (f a)
  obtain ⟨s,⟨hsa,hsp⟩,_⟩ := C.isCoveringMap.existsUnique_continuousMap_lifts
    ⟨f,hf⟩ a (D.encode (f a) (f a) v) rfl
  refine ⟨fun y => D.decode (f a) (s y),?_,?_⟩
  · intro z
    exact D.decode_lift_local_form (f a) hf hsp (D.domain_self (f z))
  · change D.decode (f a) (s a)=_
    rw [hsa,D.decode_encode]



end SplitTangent.HorizontalCovering.LocalTransportData

open scoped Manifold LinearAlgebra.Projectivization
open Bundle

open Filter Topology
namespace SplitTangent.AnalyticContinuation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

 

theorem subset_of_local_analytic_equations {U Z : Set E} (hU : IsPreconnected U)
    (hlocal : ∀ x ∈ U, ∃ f : E → F, AnalyticAt ℂ f x ∧
      ∀ᶠ y in 𝓝 x, y ∈ Z ↔ f y = 0)
    (hne : (U ∩ interior Z).Nonempty) : U ⊆ Z := by
  suffices U ⊆ interior Z from this.trans interior_subset
  apply hU.subset_of_closure_inter_subset isOpen_interior hne
  rintro x ⟨hx,hxU⟩
  obtain ⟨f,hf,he⟩ := hlocal x hxU
  have hn : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ f y ∧ (y ∈ Z ↔ f y = 0) :=
    hf.eventually_analyticAt.and he
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨y,hy,hyI⟩ := mem_closure_iff.mp hx (Metric.ball x r) Metric.isOpen_ball
    (Metric.mem_ball_self hr)
  have hzero : f =ᶠ[𝓝 y] 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hy,isOpen_interior.mem_nhds hyI] with a ha hai
    exact (hrsub ha).2.mp (interior_subset hai)
  have ha : AnalyticOnNhd ℂ f (Metric.ball x r) := fun a ha => (hrsub ha).1
  have hball : Set.EqOn f 0 (Metric.ball x r) :=
    ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball x r).isPreconnected hy hzero
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x hr)
  intro y hy
  exact (hrsub hy).2.mpr (hball hy)

end SplitTangent.AnalyticContinuation

namespace SplitTangent.HorizontalCovering.LocalTransportData
open Filter Topology Set
variable {B : Type*} [TopologicalSpace B] [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
  {V : B → Type*} (D : LocalTransportData B V)

 
noncomputable def globalSection (a : B) (v : V a) : (b : B) → V b :=
  fun b => Classical.choose (D.horizontal_local_form
    (Classical.choose_spec (D.exists_normalized_horizontal continuous_id a v)).1 b)

lemma globalSection_horizontal (a : B) (v : V a) :
    D.IsHorizontalAlong id (fun b => ⟨b,D.globalSection a v b⟩) := by
  let σ := Classical.choose (D.exists_normalized_horizontal continuous_id a v)
  have hσ := (Classical.choose_spec (D.exists_normalized_horizontal continuous_id a v)).1
  have he : σ=(fun b => ⟨b,D.globalSection a v b⟩) := by
    funext b
    exact (Classical.choose_spec (D.horizontal_local_form hσ b)).1
  rw [← he]
  exact hσ

lemma globalSection_self (a : B) (v : V a) : D.globalSection a v a=v := by
  have hσ := (Classical.choose_spec (D.exists_normalized_horizontal continuous_id a v)).1
  have he := (Classical.choose_spec (D.horizontal_local_form hσ a)).1
  have hn := (Classical.choose_spec (D.exists_normalized_horizontal continuous_id a v)).2
  exact sigma_mk_injective (he.symm.trans hn)

lemma globalSection_unique {σ : (b : B) → V b}
    (hσ : D.IsHorizontalAlong id (fun b => ⟨b,σ b⟩)) (a : B) :
    D.globalSection a (σ a)=σ := by
  have he := D.horizontal_unique continuous_id
    (D.globalSection_horizontal a (σ a)) hσ a
    (by rw [D.globalSection_self])
  funext b
  exact sigma_mk_injective (congrFun he b)

lemma globalSection_cocycle (a b c : B) (v : V a) :
    D.globalSection b (D.globalSection a v b) c=D.globalSection a v c := by
  exact congrFun (D.globalSection_unique (D.globalSection_horizontal a v) b) c

 

noncomputable def globalTransport (a b : B) : V a ≃ V b where
  toFun v := D.globalSection a v b
  invFun v := D.globalSection b v a
  left_inv v := by
    change D.globalSection b (D.globalSection a v b) a=v
    rw [D.globalSection_cocycle,D.globalSection_self]
  right_inv v := by
    change D.globalSection a (D.globalSection b v a) b=v
    rw [D.globalSection_cocycle,D.globalSection_self]

lemma globalTransport_self (a : B) (v : V a) : D.globalTransport a a v=v :=
  D.globalSection_self a v

lemma globalTransport_cocycle (a b c : B) (v : V a) :
    D.globalTransport b c (D.globalTransport a b v)=D.globalTransport a c v :=
  D.globalSection_cocycle a b c v

lemma globalTransport_germ (a b : B) (v : V a) :
    ∀ᶠ z in 𝓝 b, D.globalTransport a z v =
      D.forward b z (D.globalTransport a b v) := by
  obtain ⟨w,hw,hh⟩ := D.horizontal_local_form (D.globalSection_horizontal a v) b
  have hwv : w=D.globalSection a v b := sigma_mk_injective hw.symm
  filter_upwards [hh] with z hz
  change D.globalSection a v z=_
  exact (sigma_mk_injective hz).trans (congrArg (D.forward b z) hwv)

end SplitTangent.HorizontalCovering.LocalTransportData

namespace SplitTangent.HorizontalCovering.LocalTransportData
open Filter Topology Set
variable {B : Type*} [TopologicalSpace B] [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
  {V : B → Type*} (D : LocalTransportData B V)

 

lemma globalTransport_local (a : B) (hc : IsConnected (D.domain a)) (v : V a)
    {b : B} (hb : b ∈ D.domain a) : D.globalTransport a b v=D.forward a b v := by
  let : ConnectedSpace (D.domain a) := isConnected_iff_connectedSpace.mp hc
  have hglobal : D.IsHorizontalAlong (fun z : D.domain a => (z : B))
      (fun z => ⟨(z : B),D.globalTransport a z v⟩) := by
    intro z
    obtain ⟨w,hw⟩ := D.globalSection_horizontal a v (z : B)
    exact ⟨w,continuous_subtype_val.continuousAt hw⟩
  have hlocal : D.IsHorizontalAlong (fun z : D.domain a => (z : B))
      (fun z => ⟨(z : B),D.forward a z v⟩) := by
    intro z
    refine ⟨D.forward a z v,?_⟩
    have hh := D.overlap a z z ⟨z.2,D.domain_self z⟩ v
    rw [D.reverse_self] at hh
    filter_upwards [continuous_subtype_val.continuousAt hh] with w hw
    exact congrArg (Sigma.mk (w : B)) hw.symm
  have he := D.horizontal_unique continuous_subtype_val hglobal hlocal
    (⟨a,D.domain_self a⟩ : D.domain a) (by rw [D.globalTransport_self,D.forward_self])
  exact sigma_mk_injective (congrFun he (⟨b,hb⟩ : D.domain a))

lemma globalTransport_reverse_local (a : B) (hc : IsConnected (D.domain a))
    {b : B} (hb : b ∈ D.domain a) (v : V b) :
    D.globalTransport b a v=D.reverse a b v := by
  apply (D.globalTransport a b).injective
  rw [D.globalTransport_cocycle,D.globalTransport_self,D.globalTransport_local a hc _ hb]
  exact (D.right_inv a b hb v).symm

end SplitTangent.HorizontalCovering.LocalTransportData

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.FormalBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Formal Boxes. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle Filter Topology
universe u
namespace SplitTangent

 

namespace FormalCauchy

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

 
def Causal (Φ : (ℕ → V) → ℕ → V) : Prop :=
  ∀ n f g, (∀ k, k ≤ n → f k = g k) → Φ f n = Φ g n

 

def coefficients (v : V) (Φ : (ℕ → V) → ℕ → V) : ℕ → V
  | 0 => v
  | n + 1 => ((n + 1 : ℂ)⁻¹) •
      Φ (fun k => if _ : k < n + 1 then coefficients v Φ k else 0) n
termination_by n => n

@[simp] theorem coefficients_zero (v : V) (Φ : (ℕ → V) → ℕ → V) :
    coefficients v Φ 0 = v := by rw [coefficients]

theorem coefficients_succ (v : V) (Φ : (ℕ → V) → ℕ → V)
    (hΦ : Causal Φ) (n : ℕ) :
    (n + 1 : ℂ) • coefficients v Φ (n + 1) = Φ (coefficients v Φ) n := by
  rw [coefficients, smul_smul, mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n : (n + 1 : ℂ) ≠ 0), one_smul]
  apply hΦ
  intro k hk
  simp [Nat.lt_succ_of_le hk]

 

theorem existsUnique_coefficients (v : V) (Φ : (ℕ → V) → ℕ → V)
    (hΦ : Causal Φ) :
    ∃! f : ℕ → V, f 0 = v ∧ ∀ n : ℕ, (n + 1 : ℂ) • f (n + 1) = Φ f n := by
  refine ⟨coefficients v Φ, ⟨coefficients_zero v Φ, coefficients_succ v Φ hΦ⟩, ?_⟩
  intro f hf
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact hf.1.trans (coefficients_zero v Φ).symm
    | succ n =>
      have hR : Φ f n = Φ (coefficients v Φ) n :=
        hΦ n f _ (fun k hk => ih k (Nat.lt_succ_of_le hk))
      apply (smul_right_injective V (by exact_mod_cast Nat.succ_ne_zero n : (n + 1 : ℂ) ≠ 0))
      exact (hf.2 n).trans (hR.trans (coefficients_succ v Φ hΦ n).symm)





def analyticAlgebra (U : Set ℂ) : Subalgebra ℂ (ℂ → ℂ) where
  carrier := {f | AnalyticOnNhd ℂ f U}
  zero_mem' := analyticOnNhd_const
  one_mem' := analyticOnNhd_const
  add_mem' := fun hf hg => hf.add hg
  mul_mem' := fun hf hg => hf.mul hg
  algebraMap_mem' := fun _ => analyticOnNhd_const

abbrev AnalyticFunction (U : Set ℂ) := analyticAlgebra U

instance instCoeFunSubtypeForallComplexMemSubalgebraAnalyticFunction (U : Set ℂ) : CoeFun (AnalyticFunction U) (fun _ => ℂ → ℂ) := ⟨Subtype.val⟩

 

def analyticDerivative {U : Set ℂ} (hU : IsOpen U) :
    AnalyticFunction U →ₗ[ℂ] AnalyticFunction U := by
  classical
  exact {
  toFun f := ⟨fun z => if z ∈ U then deriv (f : ℂ → ℂ) z else 0, by
    apply AnalyticOnNhd.congr hU f.property.deriv
    intro z hz
    simp [hz]⟩
  map_add' f g := by
    apply Subtype.ext
    funext z
    change (if z ∈ U then deriv (fun w => f w + g w) z else 0) =
      (if z ∈ U then deriv (f : ℂ → ℂ) z else 0) +
        (if z ∈ U then deriv (g : ℂ → ℂ) z else 0)
    by_cases hz : z ∈ U
    · simp only [ite_eq_left hz]
      exact deriv_add (f.property z hz).differentiableAt (g.property z hz).differentiableAt
    · simp [hz]
  map_smul' c f := by
    apply Subtype.ext
    funext z
    change (if z ∈ U then deriv (fun w => c * f w) z else 0) =
      c * (if z ∈ U then deriv (f : ℂ → ℂ) z else 0)
    by_cases hz : z ∈ U
    · simp only [ite_eq_left hz]
      exact deriv_const_mul c (f.property z hz).differentiableAt
    · simp [hz] }

@[simp] theorem analyticDerivative_apply {U : Set ℂ} (hU : IsOpen U)
    (f : AnalyticFunction U) {z : ℂ} (hz : z ∈ U) :
    analyticDerivative hU f z = deriv (f : ℂ → ℂ) z := by
  simp [analyticDerivative, hz]

theorem analyticDerivative_mul {U : Set ℂ} (hU : IsOpen U)
    (f g : AnalyticFunction U) :
    analyticDerivative hU (f * g) =
      f * analyticDerivative hU g + g * analyticDerivative hU f := by
  classical
  apply Subtype.ext
  funext z
  change (if z ∈ U then deriv (fun w => f w * g w) z else 0) =
    f z * (if z ∈ U then deriv (g : ℂ → ℂ) z else 0) +
      g z * (if z ∈ U then deriv (f : ℂ → ℂ) z else 0)
  by_cases hz : z ∈ U
  · simp only [ite_eq_left hz]
    simpa only [Pi.mul_apply, mul_comm, add_comm] using
      deriv_fun_mul (f.property z hz).differentiableAt (g.property z hz).differentiableAt
  · simp [hz]



def analyticEvaluation (U : Set ℂ) (z : ℂ) : AnalyticFunction U →+* ℂ :=
  (Pi.evalRingHom (fun _ : ℂ => ℂ) z).comp (analyticAlgebra U).val.toRingHom

@[simp] theorem analyticEvaluation_apply (U : Set ℂ) (z : ℂ) (f : AnalyticFunction U) :
    analyticEvaluation U z f = f z := rfl



open scoped MvPowerSeries.WithPiTopology

variable {R A σ : Type*} [CommRing R] [CommRing A] [Algebra R A]

 

def deriveCoefficients (δ : Derivation R A A) (f : MvPowerSeries σ A) : MvPowerSeries σ A :=
  fun d => δ (MvPowerSeries.coeff d f)

@[simp] theorem coeff_deriveCoefficients (δ : Derivation R A A) (f : MvPowerSeries σ A)
    (d : σ →₀ ℕ) : MvPowerSeries.coeff d (deriveCoefficients δ f) = δ (MvPowerSeries.coeff d f) := rfl

def coefficientDerivation (δ : Derivation R A A) :
    Derivation R (MvPowerSeries σ A) (MvPowerSeries σ A) where
  toFun := deriveCoefficients δ
  map_add' f g := by ext d; simp
  map_smul' r f := by
    ext d
    change δ (r • MvPowerSeries.coeff d f) = r • δ (MvPowerSeries.coeff d f)
    exact δ.map_smul r (MvPowerSeries.coeff d f)
  map_one_eq_zero' := by
    classical
    ext d
    simp [MvPowerSeries.coeff_one, apply_ite]
  leibniz' f g := by
    classical
    change deriveCoefficients δ (f * g) = f * deriveCoefficients δ g + g * deriveCoefficients δ f
    rw [mul_comm g]
    ext d
    simp only [coeff_deriveCoefficients, map_add, MvPowerSeries.coeff_mul, map_sum,
      Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
    apply congrArg₂ (· + ·)
    · rfl
    · apply Finset.sum_congr rfl
      intro x hx
      ring

@[simp] theorem coefficientDerivation_apply (δ : Derivation R A A)
    (f : MvPowerSeries σ A) : coefficientDerivation δ f = deriveCoefficients δ f := rfl

@[simp] theorem deriveCoefficients_C (δ : Derivation R A A) (a : A) :
    deriveCoefficients (σ := σ) δ (MvPowerSeries.C a) = MvPowerSeries.C (δ a) := by
  classical
  ext d
  by_cases hd : d = 0
  · subst d; simp
  · simp [MvPowerSeries.coeff_C, hd]

@[simp] theorem deriveCoefficients_X (δ : Derivation R A A) (i : σ) :
    deriveCoefficients δ (MvPowerSeries.X i) = 0 := by
  classical
  ext d
  simp [MvPowerSeries.coeff_X, apply_ite]



end FormalCauchy
end SplitTangent
section ReconstructionImports

open Set Filter Topology
namespace SplitTangent.DiagonalRationality



def taylorPolynomial (f : ℂ → ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k ((k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0)



def lineSections (d : ℤ) : Submodule ℂ ((ℂ → ℂ) × (ℂ → ℂ)) where
  carrier := {fg | Differentiable ℂ fg.1 ∧ Differentiable ℂ fg.2 ∧
    ∀ z : ℂ, z ≠ 0 → fg.1 z = z ^ d * fg.2 z⁻¹}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf,hf',htf⟩ ⟨hg,hg',htg⟩
    refine ⟨hf.add hg, hf'.add hg', ?_⟩
    intro z hz
    change f.1 z + g.1 z = z ^ d * (f.2 z⁻¹ + g.2 z⁻¹)
    rw [htf z hz, htg z hz, mul_add]
  smul_mem' := by
    rintro c f ⟨hf,hf',htf⟩
    refine ⟨hf.const_mul c, hf'.const_mul c, ?_⟩
    intro z hz
    change c * f.1 z = z ^ d * (c * f.2 z⁻¹)
    rw [htf z hz]
    ring


def sectionJet (d : ℤ) (n : ℕ) : lineSections d →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun s i := iteratedDeriv i.val s.val.1 0
  map_add' s t := by
    funext i
    exact iteratedDeriv_add s.property.1.contDiff.contDiffAt t.property.1.contDiff.contDiffAt
  map_smul' c s := by
    funext i
    exact iteratedDeriv_const_mul_field c s.val.1

open PowerSeries

 

def reciprocalNormal (z : ℂ) : PowerSeries ℂ :=
  (C z + X)⁻¹ - C z⁻¹

@[simp] theorem reciprocalNormal_constant (z : ℂ) :
    constantCoeff (reciprocalNormal z) = 0 := by
  simp [reciprocalNormal]

theorem reciprocalNormal_hasSubst (z : ℂ) : HasSubst (reciprocalNormal z) :=
  HasSubst.of_constantCoeff_zero' (reciprocalNormal_constant z)

@[simp] theorem reciprocalNormal_linear (z : ℂ) :
    coeff 1 (reciprocalNormal z) = -(z⁻¹ ^ 2) := by
  rw [reciprocalNormal, map_sub, coeff_C]
  norm_num only [show (1 : ℕ) ≠ 0 by decide, ite_false, sub_zero]
  rw [coeff_inv]
  simp [Finset.Nat.antidiagonal_succ,
    PowerSeries.coeff_X, PowerSeries.coeff_C, coeff_zero_eq_constantCoeff, pow_two]

theorem constant_subst {b f : PowerSeries ℂ} (hb : constantCoeff b = 0) :
    constantCoeff (subst b f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff, coeff_subst' (HasSubst.of_constantCoeff_zero' hb)]
  rw [finsum_eq_single _ 0]
  · simp [coeff_zero_eq_constantCoeff]
  · intro i hi
    simp [coeff_zero_eq_constantCoeff, hb, hi]

 
theorem leading_subst {k : ℕ} {b f T : PowerSeries ℂ}
    (hb : constantCoeff b = 0) (hf : ∀ j < k, coeff j f = 0) :
    coeff k (T * subst b f) = constantCoeff T * coeff 1 b ^ k * coeff k f := by
  obtain ⟨g, rfl⟩ := (X_pow_dvd_iff.mpr hf)
  obtain ⟨c, hc⟩ := (X_dvd_iff.mpr hb)
  have hbs : HasSubst b := HasSubst.of_constantCoeff_zero' hb
  rw [PowerSeries.subst_mul hbs, PowerSeries.subst_pow hbs, PowerSeries.subst_X hbs]
  rw [hc, mul_pow]
  have he : T * (X ^ k * c ^ k * subst (X * c) g) =
      X ^ k * (T * c ^ k * subst (X * c) g) := by ring
  rw [he, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self]
  simp only [coeff_zero_eq_constantCoeff, map_mul, map_pow]
  rw [constant_subst (by simp)]
  have hc1 : coeff 1 (X * c) = constantCoeff c := by
    simp
  rw [hc1, coeff_X_pow_mul']
  simp [coeff_zero_eq_constantCoeff]

 
def evaluateCoefficients (z : ℂ) : PowerSeries (ℂ → ℂ) →ₐ[ℂ] PowerSeries ℂ :=
  PowerSeries.mapAlgHom (Pi.evalAlgHom ℂ (fun _ : ℂ => ℂ) z)

@[simp] theorem coeff_evaluateCoefficients (z : ℂ) (f : PowerSeries (ℂ → ℂ)) (k : ℕ) :
    coeff k (evaluateCoefficients z f) = coeff k f z := rfl

 

def formalSections (T : ℂ → PowerSeries ℂ) :
    Submodule ℂ (PowerSeries (ℂ → ℂ) × PowerSeries (ℂ → ℂ)) where
  carrier := {fg | (∀ k, Differentiable ℂ (coeff k fg.1)) ∧
    (∀ k, Differentiable ℂ (coeff k fg.2)) ∧
    ∀ z : ℂ, z ≠ 0 → evaluateCoefficients z fg.1 =
      T z * subst (reciprocalNormal z) (evaluateCoefficients z⁻¹ fg.2)}
  zero_mem' := by
    refine ⟨fun k => by simp, fun k => by simp, ?_⟩
    intro z hz
    simp [← coe_substAlgHom (reciprocalNormal_hasSubst z)]
  add_mem' := by
    rintro f g ⟨hf, hf', hfg⟩ ⟨hg, hg', hgg⟩
    refine ⟨fun k => (hf k).add (hg k), fun k => (hf' k).add (hg' k), ?_⟩
    intro z hz
    change evaluateCoefficients z (f.1 + g.1) =
      T z * subst (reciprocalNormal z) (evaluateCoefficients z⁻¹ (f.2 + g.2))
    rw [map_add, map_add, subst_add (reciprocalNormal_hasSubst z), mul_add,
      hfg z hz, hgg z hz]
  smul_mem' := by
    rintro c f ⟨hf, hf', hfg⟩
    refine ⟨fun k => ?_, fun k => ?_, ?_⟩
    · change Differentiable ℂ (coeff k (c • f.1))
      rw [coeff_smul]
      exact (hf k).const_smul c
    · change Differentiable ℂ (coeff k (c • f.2))
      rw [coeff_smul]
      exact (hf' k).const_smul c
    · intro z hz
      change evaluateCoefficients z (c • f.1) =
        T z * subst (reciprocalNormal z) (evaluateCoefficients z⁻¹ (c • f.2))
      rw [map_smul, map_smul, subst_smul (reciprocalNormal_hasSubst z), hfg z hz,
        mul_smul_comm]

 
def orderFiltration (T : ℂ → PowerSeries ℂ) (k : ℕ) : Submodule ℂ (formalSections T) where
  carrier := {s | ∀ j < k, coeff j s.val.1 = 0 ∧ coeff j s.val.2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro s t hs ht j hj
    have hs' := hs j hj
    have ht' := ht j hj
    simpa using And.intro (congrArg₂ (· + ·) hs'.1 ht'.1) (congrArg₂ (· + ·) hs'.2 ht'.2)
  smul_mem' := by
    intro c s hs j hj
    obtain ⟨h1,h2⟩ := hs j hj
    constructor <;> simp [h1,h2]

 
def leadingSection {T : ℂ → PowerSeries ℂ} {d : ℤ}
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ d) (k : ℕ) :
    orderFiltration T k →ₗ[ℂ] lineSections (d - 2 * (k : ℤ)) where
  toFun s := ⟨(coeff k s.val.val.1, fun z => (-1 : ℂ) ^ k * coeff k s.val.val.2 z),
    s.val.property.1 k, (s.val.property.2.1 k).const_mul _, by
      intro z hz
      have he := congrArg (coeff k) (s.val.property.2.2 z hz)
      rw [leading_subst (reciprocalNormal_constant z) (fun j hj => by
          simp only [coeff_evaluateCoefficients]
          exact congrFun (s.property j hj).2 z⁻¹), hT z hz,
        reciprocalNormal_linear, coeff_evaluateCoefficients, coeff_evaluateCoefficients] at he
      change coeff k s.val.val.1 z = z ^ (d - 2 * (k : ℤ)) *
        ((-1 : ℂ) ^ k * coeff k s.val.val.2 z⁻¹)
      rw [he, neg_pow, zpow_sub₀ hz, zpow_mul, zpow_natCast]
      simp only [zpow_ofNat, inv_pow, div_eq_mul_inv]
      ring⟩
  map_add' s t := by
    apply Subtype.ext
    ext z <;> simp [mul_add]
  map_smul' c s := by
    apply Subtype.ext
    ext z <;> simp [mul_left_comm]

theorem leadingSection_eq_zero_iff {T : ℂ → PowerSeries ℂ} {d : ℤ}
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ d) (k : ℕ)
    (s : orderFiltration T k) :
    leadingSection hT k s = 0 ↔ coeff k s.val.val.1 = 0 ∧ coeff k s.val.val.2 = 0 := by
  constructor
  · intro h
    have he := congrArg Subtype.val h
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    refine ⟨h1, ?_⟩
    funext z
    have hz : (-1 : ℂ) ^ k * coeff k s.val.val.2 z = 0 := congrFun h2 z
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  · rintro ⟨h1,h2⟩
    apply Subtype.ext
    ext z <;> simp [leadingSection, h1, h2]

 
def leadingKernelEquiv {T : ℂ → PowerSeries ℂ} {d : ℤ}
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ d) (k : ℕ) :
    LinearMap.ker (leadingSection hT k) ≃ₗ[ℂ] orderFiltration T (k+1) where
  toFun s := ⟨s.val.val, fun j hj => by
    by_cases hjk : j < k
    · exact s.val.property j hjk
    · have hjk' : j = k := by omega
      subst j
      exact (leadingSection_eq_zero_iff hT k s.val).mp s.property⟩
  invFun s := ⟨⟨s.val, fun j hj => s.property j (by omega)⟩,
    (leadingSection_eq_zero_iff hT k _).mpr (s.property k (by omega))⟩
  left_inv s := rfl
  right_inv s := rfl
  map_add' s t := rfl
  map_smul' c s := rfl


def zeroFiltrationEquiv (T : ℂ → PowerSeries ℂ) :
    orderFiltration T 0 ≃ₗ[ℂ] formalSections T where
  toFun := Subtype.val
  invFun s := ⟨s, by simp [orderFiltration]⟩
  left_inv s := rfl
  right_inv s := rfl
  map_add' s t := rfl
  map_smul' c s := rfl


def entireSeries : Subalgebra ℂ (PowerSeries (ℂ → ℂ)) where
  carrier := {f | ∀ k, Differentiable ℂ (coeff k f)}
  zero_mem' := by simp
  one_mem' := by intro k; simp [coeff_one]; split <;> simp
  add_mem' := by intro f g hf hg k; simpa using (hf k).add (hg k)
  mul_mem' := by
    intro f g hf hg k
    rw [coeff_mul]
    exact Differentiable.sum (fun ij hij => (hf ij.1).mul (hg ij.2))
  algebraMap_mem' := by
    intro c k
    simp only [PowerSeries.algebraMap_apply, coeff_C]
    split <;> exact differentiable_const _

theorem C_mem_entireSeries {f : ℂ → ℂ} (hf : Differentiable ℂ f) : C f ∈ entireSeries := by
  intro k
  rw [coeff_C]
  split
  · exact hf
  · exact differentiable_const _

theorem X_mem_entireSeries : (X : PowerSeries (ℂ → ℂ)) ∈ entireSeries := by
  intro k
  rw [coeff_X]
  split <;> exact differentiable_const _

 
def twistTransition (m : ℕ) (z : ℂ) : PowerSeries ℂ :=
  (C z * (C z + X)) ^ m

@[simp] theorem twistTransition_constant (m : ℕ) (z : ℂ) :
    constantCoeff (twistTransition m z) = z ^ (2*m) := by
  simp [twistTransition, ← pow_two, ← pow_mul]

abbrev BiCoefficients (m : ℕ) := Fin (m+1) → Fin (m+1) → ℂ

def normalPolynomialSection (m : ℕ) (a : BiCoefficients m) : PowerSeries (ℂ → ℂ) :=
  ∑ j, C (fun z => ∑ i, a i j * z ^ i.val) * (C id + X) ^ j.val

def infinityPolynomialSection (m : ℕ) (a : BiCoefficients m) : PowerSeries (ℂ → ℂ) :=
  ∑ j, C (fun z => ∑ i, a i j * z ^ (m-i.val)) * (C id + X) ^ (m-j.val)

theorem normalPolynomialSection_entire (m : ℕ) (a : BiCoefficients m) :
    normalPolynomialSection m a ∈ entireSeries := by
  apply Subalgebra.sum_mem
  intro j hj
  apply Subalgebra.mul_mem
  · apply C_mem_entireSeries
    exact Differentiable.fun_sum (fun i hi => (differentiable_id.pow i.val).const_mul _)
  · exact Subalgebra.pow_mem _ (Subalgebra.add_mem _ (C_mem_entireSeries differentiable_id)
      X_mem_entireSeries) _

theorem infinityPolynomialSection_entire (m : ℕ) (a : BiCoefficients m) :
    infinityPolynomialSection m a ∈ entireSeries := by
  apply Subalgebra.sum_mem
  intro j hj
  apply Subalgebra.mul_mem
  · apply C_mem_entireSeries
    exact Differentiable.fun_sum (fun i hi => (differentiable_id.pow _).const_mul _)
  · exact Subalgebra.pow_mem _ (Subalgebra.add_mem _ (C_mem_entireSeries differentiable_id)
      X_mem_entireSeries) _

@[simp] theorem evaluateCoefficients_C (z : ℂ) (f : ℂ → ℂ) :
    evaluateCoefficients z (C f) = C (f z) := by
  exact PowerSeries.map_C _ _

@[simp] theorem evaluateCoefficients_X (z : ℂ) :
    evaluateCoefficients z X = X := by
  exact PowerSeries.map_X _

theorem cancel_complementary_powers {R : Type*} [CommRing R] {x y : R}
    (hxy : x*y=1) {m i : ℕ} (hi : i ≤ m) : x^m*y^(m-i) = x^i := by
  calc
    x^m*y^(m-i) = x^i * (x*y)^(m-i) := by
      rw [mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hi]
    _ = x^i := by rw [hxy, one_pow, mul_one]

 

theorem polynomialSection_gluing (m : ℕ) (a : BiCoefficients m) (z : ℂ) (hz : z ≠ 0) :
    evaluateCoefficients z (normalPolynomialSection m a) =
      twistTransition m z * subst (reciprocalNormal z)
        (evaluateCoefficients z⁻¹ (infinityPolynomialSection m a)) := by
  have hc : (C z : PowerSeries ℂ) * C z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  have hx : (C z + X : PowerSeries ℂ) * (C z + X)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simpa using hz)
  have hn : C z⁻¹ + reciprocalNormal z = (C z + X)⁻¹ := by simp [reciprocalNormal]
  simp only [normalPolynomialSection, infinityPolynomialSection, map_sum, map_mul, map_pow, map_add,
    evaluateCoefficients_C, evaluateCoefficients_X, id_eq]
  rw [← coe_substAlgHom (reciprocalNormal_hasSubst z)]
  simp only [map_sum, map_mul, map_pow, map_add, coe_substAlgHom, PowerSeries.subst_C,
    PowerSeries.subst_X (reciprocalNormal_hasSubst z)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (∑ i, C (a i j) * C z ^ i.val) * (C z + X) ^ j.val =
    twistTransition m z * ((∑ i, C (a i j) * C z⁻¹ ^ (m-i.val)) *
      (C z⁻¹ + reciprocalNormal z) ^ (m-j.val))
  rw [hn]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [twistTransition, mul_pow]
  calc
    C (a i j) * C z ^ i.val * (C z + X) ^ j.val =
        C (a i j) * (C z ^ m * C z⁻¹ ^ (m-i.val)) *
          ((C z+X)^m * ((C z+X)⁻¹)^(m-j.val)) := by
      rw [cancel_complementary_powers hc (Nat.le_of_lt_succ i.isLt),
        cancel_complementary_powers hx (Nat.le_of_lt_succ j.isLt)]
    _ = _ := by ring

def polynomialFunction : Polynomial ℂ →ₐ[ℂ] (ℂ → ℂ) :=
  AlgHom.pi (fun z => Polynomial.aeval z)

@[simp] theorem polynomialFunction_apply (p : Polynomial ℂ) (z : ℂ) :
    polynomialFunction p z = p.eval z := by simp [polynomialFunction]

def biPolynomial (m : ℕ) (a : BiCoefficients m) : Polynomial (Polynomial ℂ) :=
  ∑ j, Polynomial.monomial j.val (∑ i, Polynomial.monomial i.val (a i j))

@[simp] theorem biPolynomial_coeff (m : ℕ) (a : BiCoefficients m) (i j : Fin (m+1)) :
    ((biPolynomial m a).coeff j.val).coeff i.val = a i j := by
  simp [biPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    ← Fin.ext_iff]

def expandPolynomial (p : Polynomial (Polynomial ℂ)) : PowerSeries (ℂ → ℂ) :=
  (p.map polynomialFunction.toRingHom).comp (Polynomial.X + Polynomial.C id)

theorem C_complex_smul (c : ℂ) (f : ℂ → ℂ) : C (c • f) = c • C f := by
  ext k
  simp only [coeff_C, coeff_smul]
  split <;> simp

def chartPolynomialLinear (m : ℕ) (e h : Fin (m+1) → ℕ) :
    BiCoefficients m →ₗ[ℂ] PowerSeries (ℂ → ℂ) where
  toFun a := ∑ j, C (∑ i, a i j • (fun z : ℂ => z ^ e i)) * (C id + X) ^ h j
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add, add_mul]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum, C_complex_smul,
      smul_mul_assoc]
    simp only [RingHom.id_apply, Finset.smul_sum]

theorem normalPolynomialSection_eq_linear (m : ℕ) (a : BiCoefficients m) :
    normalPolynomialSection m a = chartPolynomialLinear m Fin.val Fin.val a := by
  unfold normalPolynomialSection chartPolynomialLinear
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  funext z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem infinityPolynomialSection_eq_linear (m : ℕ) (a : BiCoefficients m) :
    infinityPolynomialSection m a = chartPolynomialLinear m (fun i => m-i.val) (fun j => m-j.val) a := by
  unfold infinityPolynomialSection chartPolynomialLinear
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  funext z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

 

def polynomialSection (m : ℕ) : BiCoefficients m →ₗ[ℂ] formalSections (twistTransition m) where
  toFun a := ⟨(normalPolynomialSection m a, infinityPolynomialSection m a),
    normalPolynomialSection_entire m a, infinityPolynomialSection_entire m a,
    polynomialSection_gluing m a⟩
  map_add' a b := by
    apply Subtype.ext
    apply Prod.ext
    · exact (normalPolynomialSection_eq_linear m (a+b)).trans (by
        rw [map_add]; congr 1 <;> symm <;> apply normalPolynomialSection_eq_linear)
    · exact (infinityPolynomialSection_eq_linear m (a+b)).trans (by
        rw [map_add]; congr 1 <;> symm <;> apply infinityPolynomialSection_eq_linear)
  map_smul' c a := by
    apply Subtype.ext
    apply Prod.ext
    · exact (normalPolynomialSection_eq_linear m (c • a)).trans (by
        rw [map_smul]; congr 1; symm; apply normalPolynomialSection_eq_linear)
    · exact (infinityPolynomialSection_eq_linear m (c • a)).trans (by
        rw [map_smul]; congr 1; symm; apply infinityPolynomialSection_eq_linear)


def multiplySection {T U : ℂ → PowerSeries ℂ} (s : formalSections T) (t : formalSections U) :
    formalSections (fun z => T z * U z) :=
  ⟨(s.val.1*t.val.1, s.val.2*t.val.2),
    entireSeries.mul_mem s.property.1 t.property.1,
    entireSeries.mul_mem s.property.2.1 t.property.2.1, by
      intro z hz
      change evaluateCoefficients z (s.val.1*t.val.1) =
        (T z * U z) * subst (reciprocalNormal z) (evaluateCoefficients z⁻¹ (s.val.2*t.val.2))
      rw [map_mul, map_mul, subst_mul (reciprocalNormal_hasSubst z),
        s.property.2.2 z hz, t.property.2.2 z hz]
      ring⟩

 
def relationMap {T : ℂ → PowerSeries ℂ} (s t : formalSections T) (m : ℕ) :
    (BiCoefficients m × BiCoefficients m) →ₗ[ℂ]
      formalSections (fun z => twistTransition m z * T z) where
  toFun ab := multiplySection (polynomialSection m ab.1) s +
    multiplySection (polynomialSection m ab.2) t
  map_add' a b := by
    apply Subtype.ext
    apply Prod.ext <;> simp [multiplySection, map_add, add_mul] <;> ring
  map_smul' c a := by
    apply Subtype.ext
    apply Prod.ext <;> simp [multiplySection, map_smul, smul_add]



def normalPolynomial (m : ℕ) (a : BiCoefficients m) : Polynomial (ℂ → ℂ) :=
  ∑ j, Polynomial.C (fun z => ∑ i, a i j * z ^ i.val) *
    (Polynomial.C id + Polynomial.X) ^ j.val



def polynomialEvaluation (p : Polynomial (ℂ → ℂ)) (w : ℂ × ℂ) : ℂ :=
  p.eval₂ (Pi.evalRingHom (fun _ : ℂ => ℂ) w.1) w.2

@[simp] theorem polynomialEvaluation_diagonal (p : Polynomial (ℂ → ℂ)) (z : ℂ) :
    polynomialEvaluation p (z,0) = p.coeff 0 z := by
  simp [polynomialEvaluation, Polynomial.eval₂_at_zero]


def taylorSeries (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => iteratedDeriv n f 0 / (n.factorial : ℂ))

@[simp] theorem coeff_taylorSeries (f : ℂ → ℂ) (n : ℕ) :
    coeff n (taylorSeries f) = iteratedDeriv n f 0 / (n.factorial : ℂ) := by
  rw [taylorSeries, coeff_mk]

theorem taylorSeries_congr {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) :
    taylorSeries f = taylorSeries g := by
  apply PowerSeries.ext
  intro n
  rw [coeff_taylorSeries, coeff_taylorSeries, h.iteratedDeriv_eq n]

@[simp] theorem taylorSeries_zero : taylorSeries (fun _ => 0) = 0 := by
  ext n
  simp [taylorSeries]

theorem taylorSeries_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorSeries (f+g) = taylorSeries f + taylorSeries g := by
  ext n
  simp only [map_add, coeff_taylorSeries]
  rw [iteratedDeriv_add hf.contDiffAt hg.contDiffAt, add_div]

theorem taylorSeries_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorSeries (f*g) = taylorSeries f * taylorSeries g := by
  apply PowerSeries.ext
  intro n
  rw [coeff_taylorSeries, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i (taylorSeries f) * coeff j (taylorSeries g)) n]
  simp only [coeff_taylorSeries]
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_choose ℂ (by have := Finset.mem_range.mp hi; omega)]
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp

 
theorem hasFPowerSeries_taylorSeries {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => coeff n (taylorSeries f))) 0 := by
  simpa only [coeff_taylorSeries] using hf.hasFPowerSeriesAt

theorem polynomial_analyticAt (p : Polynomial ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun w => p.eval w) z :=
  (AnalyticOnNhd.eval_polynomial p) z (Set.mem_univ z)

@[simp] theorem taylorSeries_polynomial (p : Polynomial ℂ) :
    taylorSeries (fun z => p.eval z) = (p : PowerSeries ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, Polynomial.coe_add]
    rw [show (fun z => p.eval z + q.eval z) = (fun z => p.eval z) + (fun z => q.eval z) from rfl,
      taylorSeries_add (polynomial_analyticAt p 0) (polynomial_analyticAt q 0), hp, hq]
  | monomial n a =>
    apply PowerSeries.ext
    intro k
    simp only [coeff_taylorSeries, Polynomial.eval_monomial, Polynomial.coeff_coe,
      Polynomial.coeff_monomial]
    rw [iteratedDeriv_const_mul a (by fun_prop), iteratedDeriv_fun_pow_zero]
    by_cases h : k = n
    · subst k
      simp [Nat.factorial_ne_zero]
    · simp [h, Ne.symm h]


def polynomialFiber (p : Polynomial (ℂ → ℂ)) (z : ℂ) : Polynomial ℂ :=
  p.map (Pi.evalRingHom (fun _ : ℂ => ℂ) z)

@[simp] theorem polynomialFiber_coeff (p : Polynomial (ℂ → ℂ)) (z : ℂ) (n : ℕ) :
    (polynomialFiber p z).coeff n = p.coeff n z := by
  simp [polynomialFiber]

@[simp] theorem polynomialFiber_eval (p : Polynomial (ℂ → ℂ)) (z v : ℂ) :
    (polynomialFiber p z).eval v = polynomialEvaluation p (z,v) := by
  simp [polynomialFiber, polynomialEvaluation, Polynomial.eval_map]

@[simp] theorem evaluateCoefficients_polynomial (p : Polynomial (ℂ → ℂ)) (z : ℂ) :
    evaluateCoefficients z (p : PowerSeries (ℂ → ℂ)) =
      (polynomialFiber p z : PowerSeries ℂ) := by
  ext n
  simp



end SplitTangent.DiagonalRationality

open Set Filter Topology Polynomial PowerSeries
namespace SplitTangent.FormalProjective
section

 
def AnalyticSeriesAt (f : ℂ → PowerSeries ℂ) (z : ℂ) : Prop :=
  ∀ n : ℕ, AnalyticAt ℂ (fun w => PowerSeries.coeff n (f w)) z

namespace AnalyticSeriesAt

variable {f g : ℂ → PowerSeries ℂ} {z : ℂ}

theorem mul (hf : AnalyticSeriesAt f z) (hg : AnalyticSeriesAt g z) :
    AnalyticSeriesAt (fun w => f w * g w) z := by
  intro n
  simp only [PowerSeries.coeff_mul]
  exact Finset.analyticAt_fun_sum _ (fun ij _ => (hf ij.1).mul (hg ij.2))

theorem constant {a : ℂ → ℂ} (ha : AnalyticAt ℂ a z) :
    AnalyticSeriesAt (fun w => PowerSeries.C (a w)) z := by
  intro n
  simp only [PowerSeries.coeff_C]
  split_ifs
  · exact ha
  · exact analyticAt_const

theorem sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → PowerSeries ℂ}
    (hf : ∀ i ∈ s, AnalyticSeriesAt (f i) z) :
    AnalyticSeriesAt (fun w => ∑ i ∈ s, f i w) z := by
  intro n
  simp only [map_sum]
  exact Finset.analyticAt_fun_sum _ (fun i hi => hf i hi n)

theorem inv (hf : AnalyticSeriesAt f z) (h0 : PowerSeries.constantCoeff (f z) ≠ 0) :
    AnalyticSeriesAt (fun w => (f w)⁻¹) z := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hc0 : AnalyticAt ℂ (fun w => PowerSeries.constantCoeff (f w)) z := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hf 0
    have hconst : AnalyticAt ℂ (fun w => (PowerSeries.constantCoeff (f w))⁻¹) z :=
      hc0.fun_inv h0
    by_cases hn : n = 0
    · subst n
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.constantCoeff_inv] using hconst
    · have heq : (fun w => PowerSeries.coeff n ((f w)⁻¹)) =
          (fun w => -(PowerSeries.constantCoeff (f w))⁻¹ *
            ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, if ij.2 < n then
              PowerSeries.coeff ij.1 (f w) * PowerSeries.coeff ij.2 ((f w)⁻¹) else 0) := by
        funext w
        exact (PowerSeries.coeff_inv n (f w)).trans (ite_eq_right hn)
      rw [heq]
      apply hconst.neg.mul
      apply Finset.analyticAt_fun_sum
      intro ij _
      split_ifs with hj
      · exact (hf ij.1).mul (ih ij.2 hj)
      · exact analyticAt_const

end AnalyticSeriesAt

 

structure ChartData {ι : Type*} [Fintype ι] (p : ι → ℂ[X]) where
  basepoint_free : ∀ z : ℂ, ∃ k, (p k).eval z ≠ 0
  ratio : ι → ι → ℂ → PowerSeries ℂ
  analytic : ∀ k j z, (p k).eval z ≠ 0 → AnalyticSeriesAt (ratio k j) z
  diagonal : ∀ k j z, (p k).eval z ≠ 0 →
    PowerSeries.constantCoeff (ratio k j z) = (p j).eval z / (p k).eval z
  identity : ∀ k z, (p k).eval z ≠ 0 → ratio k k z = 1
  overlap : ∀ k l j z, (p k).eval z ≠ 0 → (p l).eval z ≠ 0 →
    ratio k l z * ratio l j z = ratio k j z

namespace ChartData
variable {ι : Type*} [Fintype ι] {p : ι → ℂ[X]} (F : ChartData p)
  (a : ι → ℂ[X]) (ha : ∑ i, a i * p i = 1)

 

def frame (k : ι) (z : ℂ) : PowerSeries ℂ :=
  ∑ i, PowerSeries.C ((a i).eval z) * F.ratio k i z

include ha in
theorem frame_constant (k : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    PowerSeries.constantCoeff (F.frame a k z) = ((p k).eval z)⁻¹ := by
  have he := congrArg (Polynomial.eval z) ha
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_one] at he
  simp only [frame,map_sum,map_mul,PowerSeries.constantCoeff_C,F.diagonal k _ z hk,div_eq_mul_inv,← mul_assoc]
  rw [← Finset.sum_mul,he,one_mul]

include ha in
theorem frame_unit (k : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    PowerSeries.constantCoeff (F.frame a k z) ≠ 0 := by
  rw [F.frame_constant a ha k z hk]
  exact inv_ne_zero hk

theorem frame_analytic (k : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    AnalyticSeriesAt (F.frame a k) z := by
  apply AnalyticSeriesAt.sum
  intro i _
  apply AnalyticSeriesAt.mul
  · exact AnalyticSeriesAt.constant (AnalyticOnNhd.eval_polynomial (a i) z (mem_univ z))
  · exact F.analytic k i z hk

theorem frame_overlap (k l : ι) (z : ℂ) (hk : (p k).eval z ≠ 0)
    (hl : (p l).eval z ≠ 0) : F.ratio k l z * F.frame a l z = F.frame a k z := by
  simp only [frame,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_left_comm,F.overlap k l i z hk hl]

 
def localSection (k j : ι) (z : ℂ) : PowerSeries ℂ :=
  (F.frame a k z)⁻¹ * F.ratio k j z

include ha in
theorem frame_mul_localSection (k j : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    F.frame a k z * F.localSection a k j z = F.ratio k j z := by
  rw [localSection,← mul_assoc,PowerSeries.mul_inv_cancel _ (F.frame_unit a ha k z hk),one_mul]

include ha in
theorem localSection_overlap (k l j : ι) (z : ℂ) (hk : (p k).eval z ≠ 0)
    (hl : (p l).eval z ≠ 0) : F.localSection a k j z = F.localSection a l j z := by
  have he : F.frame a k z * F.localSection a l j z = F.ratio k j z := by
    rw [← F.frame_overlap a k l z hk hl,mul_assoc,F.frame_mul_localSection a ha l j z hl,
      F.overlap k l j z hk hl]
  calc
    F.localSection a k j z = (F.frame a k z)⁻¹ * F.ratio k j z := rfl
    _ = (F.frame a k z)⁻¹ * (F.frame a k z * F.localSection a l j z) := by rw [he]
    _ = F.localSection a l j z := by
      rw [← mul_assoc,PowerSeries.inv_mul_cancel _ (F.frame_unit a ha k z hk),one_mul]

include ha in
theorem localSection_analytic (k j : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    AnalyticSeriesAt (F.localSection a k j) z :=
  ((F.frame_analytic a k z hk).inv (F.frame_unit a ha k z hk)).mul (F.analytic k j z hk)

 

def active (z : ℂ) : ι := Classical.choose (F.basepoint_free z)

theorem active_nonzero (z : ℂ) : (p (F.active z)).eval z ≠ 0 :=
  Classical.choose_spec (F.basepoint_free z)

def sectionValue (j : ι) (z : ℂ) : PowerSeries ℂ := F.localSection a (F.active z) j z

include ha in
theorem sectionValue_eq (k j : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    F.sectionValue a j z = F.localSection a k j z :=
  F.localSection_overlap a ha (F.active z) k j z (F.active_nonzero z) hk

include ha in
theorem sectionValue_analytic (j : ι) (z : ℂ) : AnalyticSeriesAt (F.sectionValue a j) z := by
  intro n
  let k := F.active z
  have hk : (p k).eval z ≠ 0 := F.active_nonzero z
  apply (F.localSection_analytic a ha k j z hk n).congr
  have hnear : ∀ᶠ w in nhds z, (p k).eval w ≠ 0 := (p k).continuous.continuousAt.eventually_ne hk
  filter_upwards [hnear] with w hw
  exact congrArg (PowerSeries.coeff n) (F.sectionValue_eq a ha k j w hw).symm



def sectionSeries (j : ι) : PowerSeries (ℂ → ℂ) :=
  PowerSeries.mk (fun n z => PowerSeries.coeff n (F.sectionValue a j z))

include ha in
theorem sectionSeries_entire (j : ι) (n : ℕ) :
    Differentiable ℂ (PowerSeries.coeff n (F.sectionSeries a j)) := by
  intro z
  simpa only [sectionSeries,PowerSeries.coeff_mk] using
    (F.sectionValue_analytic a ha j z n).differentiableAt

end ChartData

open SplitTangent.DiagonalRationality

 

structure TwoChartData {ι : Type*} [Fintype ι] (d : ℕ) (p q : ι → ℂ[X]) where
  finite : ChartData p
  infinity : ChartData q
  diagonal_transition : ∀ z : ℂ, z ≠ 0 → ∀ j,
    (p j).eval z = z^d * (q j).eval z⁻¹
  overlap : ∀ k j z, z ≠ 0 → (p k).eval z ≠ 0 →
    finite.ratio k j z = PowerSeries.subst (reciprocalNormal z) (infinity.ratio k j z⁻¹)

namespace TwoChartData
variable {ι : Type*} [Fintype ι] {d : ℕ} {p q : ι → ℂ[X]} (F : TwoChartData d p q)
  (a b : ι → ℂ[X]) (ha : ∑ i, a i * p i = 1) (hb : ∑ i, b i * q i = 1)

include F in
theorem infinity_nonzero (z : ℂ) (hz : z ≠ 0) (k : ι) (hk : (p k).eval z ≠ 0) :
    (q k).eval z⁻¹ ≠ 0 := by
  rw [F.diagonal_transition z hz k] at hk
  exact (mul_ne_zero_iff.mp hk).2

 

def normalizedTransition (z : ℂ) : PowerSeries ℂ :=
  (F.finite.frame a (F.finite.active z) z)⁻¹ *
    PowerSeries.subst (reciprocalNormal z) (F.infinity.frame b (F.finite.active z) z⁻¹)


theorem sectionSeries_evaluate {r : ι → ℂ[X]} (G : ChartData r)
    (c : ι → ℂ[X]) (j : ι) (z : ℂ) :
    evaluateCoefficients z (G.sectionSeries c j) = G.sectionValue c j z := by
  ext n
  simp only [coeff_evaluateCoefficients,ChartData.sectionSeries,PowerSeries.coeff_mk]

include ha hb in
theorem normalized_gluing (j : ι) (z : ℂ) (hz : z ≠ 0) :
    evaluateCoefficients z (F.finite.sectionSeries a j) =
      F.normalizedTransition a b z * PowerSeries.subst (reciprocalNormal z)
        (evaluateCoefficients z⁻¹ (F.infinity.sectionSeries b j)) := by
  let k := F.finite.active z
  have hk : (p k).eval z ≠ 0 := F.finite.active_nonzero z
  have hq := F.infinity_nonzero z hz k hk
  rw [sectionSeries_evaluate,sectionSeries_evaluate,
    F.finite.sectionValue_eq a ha k j z hk,F.infinity.sectionValue_eq b hb k j z⁻¹ hq]
  change (F.finite.frame a k z)⁻¹ * F.finite.ratio k j z =
    ((F.finite.frame a k z)⁻¹ * PowerSeries.subst (reciprocalNormal z)
      (F.infinity.frame b k z⁻¹)) * PowerSeries.subst (reciprocalNormal z)
        (F.infinity.localSection b k j z⁻¹)
  rw [mul_assoc,← PowerSeries.subst_mul (reciprocalNormal_hasSubst z),
    F.infinity.frame_mul_localSection b hb k j z⁻¹ hq,← F.overlap k j z hz hk]

 

def normalizedSection (j : ι) : formalSections (F.normalizedTransition a b) :=
  ⟨(F.finite.sectionSeries a j,F.infinity.sectionSeries b j),
    F.finite.sectionSeries_entire a ha j,F.infinity.sectionSeries_entire b hb j,
    F.normalized_gluing a b ha hb j⟩

end TwoChartData
end

open SplitTangent.DiagonalRationality
end SplitTangent.FormalProjective

end ReconstructionImports
open Set Filter Topology

namespace SplitTangent.HolomorphicJets
section
open SplitTangent.DiagonalRationality

 
def normalDeriv (H : ℂ × ℂ → ℂ) : ℂ × ℂ → ℂ :=
  fun w => fderiv ℂ H w (0,1)

def normalIterate : ℕ → (ℂ × ℂ → ℂ) → (ℂ × ℂ → ℂ)
  | 0, H => H
  | n+1, H => normalDeriv (normalIterate n H)

theorem normalDeriv_analytic {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) : AnalyticAt ℂ (normalDeriv H) w := by
  exact ((ContinuousLinearMap.apply ℂ ℂ ((0,1) : ℂ × ℂ)).analyticAt _).comp hH.fderiv

theorem normalIterate_analytic {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) (n : ℕ) : AnalyticAt ℂ (normalIterate n H) w := by
  induction n with
  | zero => exact hH
  | succ n ih => exact normalDeriv_analytic ih

theorem normalDeriv_eq {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) :
    deriv (fun v => H (w.1,v)) w.2 = normalDeriv H w := by
  have hd := hH.differentiableAt.hasFDerivAt.comp_hasDerivAt w.2
    ((hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id w.2))
  exact hd.deriv

theorem normalIterate_eq {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) (n : ℕ) :
    iteratedDeriv n (fun v => H (w.1,v)) w.2 = normalIterate n H w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun v => H (w.1,v)) =ᶠ[nhds w.2]
        (fun v => normalIterate n H (w.1,v)) := by
      have hc : ContinuousAt (fun v : ℂ => (w.1,v)) w.2 := by fun_prop
      filter_upwards [hc hH.eventually_analyticAt] with v hv
      exact ih hv
    rw [he.deriv_eq]
    exact normalDeriv_eq (normalIterate_analytic hH n)

 

theorem normalCoefficient_analytic {H : ℂ × ℂ → ℂ} {u : ℂ}
    (hH : AnalyticAt ℂ H (u,0)) (n : ℕ) :
    AnalyticAt ℂ (fun z => PowerSeries.coeff n (taylorSeries (fun v => H (z,v)))) u := by
  have hN0 : AnalyticAt ℂ (fun z => normalIterate n H (z,0)) u :=
    AnalyticAt.comp (f := fun z : ℂ => (z,(0 : ℂ))) (x := u)
      (normalIterate_analytic hH n) (analyticAt_id.prod analyticAt_const)
  have hN : AnalyticAt ℂ (fun z => normalIterate n H (z,0) / (n.factorial : ℂ)) u :=
    hN0.div_const
  apply hN.congr
  have hc : ContinuousAt (fun z : ℂ => (z,(0 : ℂ))) u := by fun_prop
  filter_upwards [hc hH.eventually_analyticAt] with z hz
  simp only [coeff_taylorSeries,normalIterate_eq hz n]

variable {σ : Type*} [Fintype σ]

 
def jetPolynomial (f : ℕ → σ → ℂ) (n : ℕ) (v : ℂ) : σ → ℂ :=
  fun i => ∑ k ∈ Finset.range (n+1), v^k * f k i

omit [Fintype σ] in
@[simp] theorem jetPolynomial_zero (f : ℕ → σ → ℂ) (n : ℕ) :
    jetPolynomial f n 0 = f 0 := by
  funext i
  unfold jetPolynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0; simp [zero_pow hk0]
  · intro h; exact (h (Finset.mem_range.mpr (by omega))).elim

omit [Fintype σ] in
theorem jetPolynomial_congr {f g : ℕ → σ → ℂ} {n : ℕ}
    (h : ∀ k, k ≤ n → f k = g k) : jetPolynomial f n = jetPolynomial g n := by
  funext v i
  apply Finset.sum_congr rfl
  intro k hk
  rw [h k (by have := Finset.mem_range.mp hk; omega)]

 

def composeCoefficient (h : (σ → ℂ) → ℂ) (f : ℕ → σ → ℂ) (n : ℕ) : ℂ :=
  PowerSeries.coeff n (taylorSeries (fun v => h (jetPolynomial f n v)))

omit [Fintype σ] in
theorem composeCoefficient_causal (h : (σ → ℂ) → ℂ) {f g : ℕ → σ → ℂ} {n : ℕ}
    (hfg : ∀ k, k ≤ n → f k = g k) :
    composeCoefficient h f n = composeCoefficient h g n := by
  rw [composeCoefficient,composeCoefficient,jetPolynomial_congr hfg]

 

theorem jetPolynomial_analytic {f : ℕ → ℂ → σ → ℂ} {u v : ℂ} (n : ℕ)
    (hf : ∀ k, k ≤ n → ∀ i, AnalyticAt ℂ (fun z => f k z i) u) :
    AnalyticAt ℂ (fun w : ℂ × ℂ => jetPolynomial (fun k => f k w.1) n w.2) (u,v) := by
  apply AnalyticAt.pi
  intro i
  apply Finset.analyticAt_fun_sum
  intro k hk
  have hf' := (hf k (by have := Finset.mem_range.mp hk; omega) i).comp
    (show AnalyticAt ℂ (fun w : ℂ × ℂ => w.1) (u,v) from analyticAt_fst)
  exact (analyticAt_snd.pow k).fun_mul hf'

 

theorem composeCoefficient_analytic {h : (σ → ℂ) → ℂ} {f : ℕ → ℂ → σ → ℂ}
    {u : ℂ} (n : ℕ)
    (hf : ∀ k, k ≤ n → ∀ i, AnalyticAt ℂ (fun z => f k z i) u)
    (hh : AnalyticAt ℂ h (f 0 u)) :
    AnalyticAt ℂ (fun z => composeCoefficient h (fun k => f k z) n) u := by
  unfold composeCoefficient
  refine normalCoefficient_analytic (H := fun w : ℂ × ℂ =>
    h (jetPolynomial (fun k => f k w.1) n w.2)) ?_ n
  exact hh.comp_of_eq (jetPolynomial_analytic n hf) (jetPolynomial_zero _ n)

end

section
open SplitTangent.DiagonalRationality
variable {σ : Type*} [Fintype σ]

 

def jetSeries (f : ℕ → σ → ℂ) : FormalMultilinearSeries ℂ ℂ (σ → ℂ) :=
  FormalMultilinearSeries.pi (fun i => FormalMultilinearSeries.ofScalars ℂ (fun n => f n i))

omit [Fintype σ] in
@[simp] theorem jetSeries_apply (f : ℕ → σ → ℂ) (n : ℕ) (v : Fin n → ℂ) (i : σ) :
    jetSeries f n v i = f n i * ∏ j, v j := by
  simp [jetSeries,FormalMultilinearSeries.pi,FormalMultilinearSeries.ofScalars,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, Fin.prod_ofFn]

def polynomialJet (f : ℕ → σ → ℂ) (n : ℕ) (i : σ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n+1), Polynomial.monomial k (f k i)

omit [Fintype σ] in
@[simp] theorem polynomialJet_coeff (f : ℕ → σ → ℂ) (n k : ℕ) (i : σ) :
    (polynomialJet f n i).coeff k = if k ≤ n then f k i else 0 := by
  classical
  simp [polynomialJet,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,
    Finset.mem_range]

omit [Fintype σ] in
theorem polynomialJet_eval (f : ℕ → σ → ℂ) (n : ℕ) (i : σ) (v : ℂ) :
    (polynomialJet f n i).eval v = jetPolynomial f n v i := by
  simp [polynomialJet,jetPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial,mul_comm]

theorem jetPolynomial_hasSeries (f : ℕ → σ → ℂ) (n : ℕ) :
    HasFPowerSeriesAt (jetPolynomial f n)
      (jetSeries (fun k i => if k ≤ n then f k i else 0)) 0 := by
  apply HasFPowerSeriesAt.pi
  intro i
  have h := hasFPowerSeries_taylorSeries (polynomial_analyticAt (polynomialJet f n i) 0)
  rw [taylorSeries_polynomial] at h
  simpa only [Polynomial.coeff_coe,polynomialJet_coeff,polynomialJet_eval] using h

 
theorem formalComposition_causal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (q : FormalMultilinearSeries ℂ E G) {p p' : FormalMultilinearSeries ℂ ℂ E} {n : ℕ}
    (h : ∀ k, k ≤ n → p k = p' k) : (q.comp p) n = (q.comp p') n := by
  unfold FormalMultilinearSeries.comp
  apply Finset.sum_congr rfl
  intro c _
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [FormalMultilinearSeries.compAlongComposition_apply]
  congr 1
  funext i
  exact congrArg (fun L => L (v ∘ c.embedding i)) (h (c.blocksFun i) (c.blocksFun_le i))

 

theorem composeCoefficient_eq_formal {h : (σ → ℂ) → ℂ} (f : ℕ → σ → ℂ)
    {q : FormalMultilinearSeries ℂ (σ → ℂ) ℂ}
    (hq : HasFPowerSeriesAt h q (f 0)) (n : ℕ) :
    composeCoefficient h f n = (q.comp (jetSeries f)) n (fun _ => 1) := by
  have hq' : HasFPowerSeriesAt h q (jetPolynomial f n 0) := by
    simpa only [jetPolynomial_zero] using hq
  have hc := hq'.comp (jetPolynomial_hasSeries f n)
  have ht := hasFPowerSeries_taylorSeries hc.analyticAt
  have he := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => 1))
    (ht.eq_formalMultilinearSeries hc)
  have heq : (q.comp (jetSeries (fun k i => if k ≤ n then f k i else 0))) n =
      (q.comp (jetSeries f)) n := by
    apply formalComposition_causal
    intro k hk
    ext v
    simp only [jetSeries_apply,ite_eq_left hk]
  rw [heq] at he
  simpa [composeCoefficient,FormalMultilinearSeries.ofScalars,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, Function.comp_def] using he

 

theorem composeCoefficient_eq_laterJet {h : (σ → ℂ) → ℂ} (f : ℕ → σ → ℂ)
    (hh : AnalyticAt ℂ h (f 0)) {n m : ℕ} (hnm : n ≤ m) :
    composeCoefficient h f n =
      PowerSeries.coeff n (taylorSeries (fun v => h (jetPolynomial f m v))) := by
  obtain ⟨q,hq⟩ := hh
  have hc := (show HasFPowerSeriesAt h q (jetPolynomial f m 0) by
    simpa only [jetPolynomial_zero] using hq).comp (jetPolynomial_hasSeries f m)
  have ht := hasFPowerSeries_taylorSeries hc.analyticAt
  have he := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => 1))
    (ht.eq_formalMultilinearSeries hc)
  have heq : (q.comp (jetSeries (fun k i => if k ≤ m then f k i else 0))) n =
      (q.comp (jetSeries f)) n := by
    apply formalComposition_causal
    intro k hk
    ext v
    simp only [jetSeries_apply,ite_eq_left (hk.trans hnm)]
  rw [heq] at he
  rw [composeCoefficient_eq_formal f hq n]
  simpa [FormalMultilinearSeries.ofScalars,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, Function.comp_def] using he.symm

end
section
open SplitTangent.DiagonalRationality
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

def composeJet (H : (σ → ℂ) → τ → ℂ) (f : ℕ → σ → ℂ) : ℕ → τ → ℂ :=
  fun n i => composeCoefficient (fun x => H x i) f n

omit [Fintype τ] in
omit [Fintype σ] in
@[simp] theorem composeJet_zero (H : (σ → ℂ) → τ → ℂ) (f : ℕ → σ → ℂ) :
    composeJet H f 0 = H (f 0) := by
  funext i
  simp [composeJet,composeCoefficient,coeff_taylorSeries]

 

theorem composeJet_eq_formal (H : (σ → ℂ) → τ → ℂ) (f : ℕ → σ → ℂ)
    {q : FormalMultilinearSeries ℂ (σ → ℂ) (τ → ℂ)}
    (hq : HasFPowerSeriesAt H q (f 0)) :
    jetSeries (composeJet H f) = q.comp (jetSeries f) := by
  funext n
  have hc := (show HasFPowerSeriesAt H q (jetPolynomial f n 0) by
    simpa only [jetPolynomial_zero] using hq).comp (jetPolynomial_hasSeries f n)
  have ht : HasFPowerSeriesAt (H ∘ jetPolynomial f n)
      (jetSeries (fun k i => PowerSeries.coeff k
        (taylorSeries (fun v => H (jetPolynomial f n v) i)))) 0 := by
    apply HasFPowerSeriesAt.pi
    intro i
    exact hasFPowerSeries_taylorSeries (analyticAt_pi_iff.mp hc.analyticAt i)
  have he := congrArg (fun p : FormalMultilinearSeries ℂ ℂ (τ → ℂ) => p n)
    (ht.eq_formalMultilinearSeries hc)
  have heq : (q.comp (jetSeries (fun k i => if k ≤ n then f k i else 0))) n =
      (q.comp (jetSeries f)) n := by
    apply formalComposition_causal
    intro k hk
    ext v
    simp [jetSeries_apply,hk]
  rw [heq] at he
  exact he

 

theorem composeCoefficient_assoc (H : (σ → ℂ) → τ → ℂ)
    (h : (τ → ℂ) → ℂ) (f : ℕ → σ → ℂ)
    (hH : AnalyticAt ℂ H (f 0)) (hh : AnalyticAt ℂ h (H (f 0))) (n : ℕ) :
    composeCoefficient h (composeJet H f) n =
      composeCoefficient (h ∘ H) f n := by
  obtain ⟨q,hq⟩ := hH
  obtain ⟨r,hr⟩ := hh
  have hr' : HasFPowerSeriesAt h r (composeJet H f 0) := by
    simpa only [composeJet_zero] using hr
  rw [composeCoefficient_eq_formal _ hr',composeJet_eq_formal H f hq,
    ← FormalMultilinearSeries.comp_assoc,composeCoefficient_eq_formal _ (hr.comp hq)]

end
section
open SplitTangent.DiagonalRationality

 

theorem taylorSeries_deriv (h : ℂ → ℂ) :
    taylorSeries (deriv h) = PowerSeries.derivative _ (taylorSeries h) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_taylorSeries,PowerSeries.coeff_derivative]
  rw [← iteratedDeriv_succ']
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

 
def directionDeriv (a : ℂ × ℂ) (H : ℂ × ℂ → ℂ) : ℂ × ℂ → ℂ :=
  fun w => fderiv ℂ H w a

theorem directionDeriv_analytic {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) (a : ℂ × ℂ) :
    AnalyticAt ℂ (directionDeriv a H) w := by
  exact ((ContinuousLinearMap.apply ℂ ℂ a).analyticAt _).comp hH.fderiv

 

theorem directionDeriv_comm {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) (a b : ℂ × ℂ) :
    directionDeriv a (directionDeriv b H) w =
      directionDeriv b (directionDeriv a H) w := by
  unfold directionDeriv
  rw [fderiv_clm_apply hH.fderiv.differentiableAt (differentiableAt_const b),
    fderiv_clm_apply hH.fderiv.differentiableAt (differentiableAt_const a)]
  simpa using hH.contDiffAt.isSymmSndFDerivAt_of_omega a b

theorem directionDeriv_congr {H K : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (h : H =ᶠ[nhds w] K) (a : ℂ × ℂ) : directionDeriv a H w = directionDeriv a K w := by
  exact congrArg (fun L => L a) (h.fderiv_eq (𝕜 := ℂ))

 
theorem normalIterate_directionDeriv {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) (a : ℂ × ℂ) (n : ℕ) :
    normalIterate n (directionDeriv a H) w = directionDeriv a (normalIterate n H) w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    change directionDeriv (0,1) (normalIterate n (directionDeriv a H)) w = _
    have he : normalIterate n (directionDeriv a H) =ᶠ[nhds w]
        directionDeriv a (normalIterate n H) := by
      filter_upwards [hH.eventually_analyticAt] with z hz
      exact ih hz
    rw [directionDeriv_congr he]
    exact directionDeriv_comm (normalIterate_analytic hH n) (0,1) a

 
def tangentDeriv (H : ℂ × ℂ → ℂ) : ℂ × ℂ → ℂ := directionDeriv (1,0) H

theorem tangentDeriv_eq {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) :
    deriv (fun u => H (u,w.2)) w.1 = tangentDeriv H w := by
  exact (hH.differentiableAt.hasFDerivAt.comp_hasDerivAt w.1
    ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))).deriv

 

theorem deriv_normalCoefficient {H : ℂ × ℂ → ℂ} {u : ℂ}
    (hH : AnalyticAt ℂ H (u,0)) (n : ℕ) :
    deriv (fun z => PowerSeries.coeff n (taylorSeries (fun v => H (z,v)))) u =
      PowerSeries.coeff n (taylorSeries (fun v => tangentDeriv H (u,v))) := by
  have he : (fun z => PowerSeries.coeff n (taylorSeries (fun v => H (z,v)))) =ᶠ[nhds u]
      (fun z => normalIterate n H (z,0) / (n.factorial : ℂ)) := by
    have hc : ContinuousAt (fun z : ℂ => (z,(0 : ℂ))) u := by fun_prop
    filter_upwards [hc hH.eventually_analyticAt] with z hz
    simp only [coeff_taylorSeries,normalIterate_eq hz n]
  rw [he.deriv_eq,deriv_div_const]
  rw [tangentDeriv_eq (normalIterate_analytic hH n),coeff_taylorSeries]
  change directionDeriv (1,0) (normalIterate n H) (u,0) / _ =
    iteratedDeriv n (fun v => directionDeriv (1,0) H (u,v)) 0 / _
  rw [normalIterate_eq (directionDeriv_analytic hH (1,0)),normalIterate_directionDeriv hH]

end
section
open SplitTangent.DiagonalRationality
variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
@[simp] theorem composeCoefficient_zero (f : ℕ → σ → ℂ) (n : ℕ) :
    composeCoefficient (fun _ => 0) f n = 0 := by
  simp [composeCoefficient]

omit [Fintype σ] in
@[simp] theorem composeCoefficient_coordinate (f : ℕ → σ → ℂ) (n : ℕ) (i : σ) :
    composeCoefficient (fun x => x i) f n = f n i := by
  unfold composeCoefficient
  simp_rw [← polynomialJet_eval]
  rw [taylorSeries_polynomial,Polynomial.coeff_coe,polynomialJet_coeff]
  simp

theorem composeCoefficient_add {h k : (σ → ℂ) → ℂ} (f : ℕ → σ → ℂ)
    (hh : AnalyticAt ℂ h (f 0)) (hk : AnalyticAt ℂ k (f 0)) (n : ℕ) :
    composeCoefficient (fun x => h x + k x) f n =
      composeCoefficient h f n + composeCoefficient k f n := by
  unfold composeCoefficient
  change PowerSeries.coeff n (taylorSeries ((h ∘ jetPolynomial f n) + (k ∘ jetPolynomial f n))) = _
  rw [taylorSeries_add]
  · exact map_add _ _ _
  · exact hh.comp_of_eq (jetPolynomial_hasSeries f n).analyticAt (jetPolynomial_zero ..)
  · exact hk.comp_of_eq (jetPolynomial_hasSeries f n).analyticAt (jetPolynomial_zero ..)

theorem composeCoefficient_mul {h k : (σ → ℂ) → ℂ} (f : ℕ → σ → ℂ)
    (hh : AnalyticAt ℂ h (f 0)) (hk : AnalyticAt ℂ k (f 0)) (n : ℕ) :
    composeCoefficient (fun x => h x * k x) f n =
      ∑ l ∈ Finset.range (n+1), composeCoefficient h f l * composeCoefficient k f (n-l) := by
  unfold composeCoefficient
  change PowerSeries.coeff n (taylorSeries ((h ∘ jetPolynomial f n) * (k ∘ jetPolynomial f n))) = _
  rw [taylorSeries_mul]
  · rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a (taylorSeries (h ∘ jetPolynomial f n)) *
        PowerSeries.coeff b (taylorSeries (k ∘ jetPolynomial f n))) n]
    apply Finset.sum_congr rfl
    intro l hl
    have hln : l ≤ n := by have := Finset.mem_range.mp hl; omega
    simp only [Function.comp_def]
    rw [← composeCoefficient_eq_laterJet f hh hln,
      ← composeCoefficient_eq_laterJet f hk (Nat.sub_le ..)]
    rfl
  · exact hh.comp_of_eq (jetPolynomial_hasSeries f n).analyticAt (jetPolynomial_zero ..)
  · exact hk.comp_of_eq (jetPolynomial_hasSeries f n).analyticAt (jetPolynomial_zero ..)

theorem composeCoefficient_sum {ι : Type*} (s : Finset ι)
    (h : ι → (σ → ℂ) → ℂ) (f : ℕ → σ → ℂ)
    (hh : ∀ i ∈ s, AnalyticAt ℂ (h i) (f 0)) (n : ℕ) :
    composeCoefficient (fun x => ∑ i ∈ s, h i x) f n =
      ∑ i ∈ s, composeCoefficient (h i) f n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    rw [composeCoefficient_add f (hh a (by simp))
      (Finset.analyticAt_fun_sum s (fun i hi => hh i (by simp [hi]))) n,
      ih (fun i hi => hh i (by simp [hi]))]

end
section
open SplitTangent.DiagonalRationality
variable {σ : Type*} [Fintype σ]

 
def analyticJet (g : ℂ → σ → ℂ) : ℕ → σ → ℂ :=
  fun n i => PowerSeries.coeff n (taylorSeries (fun z => g z i))

omit [Fintype σ] in
@[simp] theorem analyticJet_zero (g : ℂ → σ → ℂ) : analyticJet g 0 = g 0 := by
  funext i
  simp [analyticJet,coeff_taylorSeries]

theorem taylorSeries_sum {ι : Type*} (s : Finset ι) (h : ι → ℂ → ℂ)
    (hh : ∀ i ∈ s, AnalyticAt ℂ (h i) 0) :
    taylorSeries (fun z => ∑ i ∈ s, h i z) = ∑ i ∈ s, taylorSeries (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    change taylorSeries (h a + (fun z => ∑ i ∈ s, h i z)) = _
    rw [taylorSeries_add (hh a (by simp))
      (Finset.analyticAt_fun_sum s (fun i hi => hh i (by simp [hi]))),
      ih (fun i hi => hh i (by simp [hi]))]

 
def coordinatePartial [DecidableEq σ] (h : (σ → ℂ) → ℂ) (j : σ) (x : σ → ℂ) : ℂ :=
  fderiv ℂ h x (Pi.single j 1)

theorem partial_analytic [DecidableEq σ] {h : (σ → ℂ) → ℂ} {x : σ → ℂ}
    (hh : AnalyticAt ℂ h x) (j : σ) : AnalyticAt ℂ (coordinatePartial h j) x := by
  exact ((ContinuousLinearMap.apply ℂ ℂ (Pi.single j (1 : ℂ))).analyticAt _).comp hh.fderiv

theorem linearMap_eq_sum [DecidableEq σ] (L : (σ → ℂ) →L[ℂ] ℂ) (v : σ → ℂ) :
    L v = ∑ j, L (Pi.single j 1) * v j := by
  have hv : v = ∑ j, v j • Pi.single j (1 : ℂ) := by
    funext i
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _; ring

theorem deriv_comp_eq_sum [DecidableEq σ] {h : (σ → ℂ) → ℂ} {g : ℂ → σ → ℂ} {z : ℂ}
    (hh : DifferentiableAt ℂ h (g z)) (hg : DifferentiableAt ℂ g z) :
    deriv (h ∘ g) z = ∑ j, coordinatePartial h j (g z) * deriv (fun w => g w j) z := by
  rw [(hh.hasFDerivAt.comp_hasDerivAt z hg.hasDerivAt).deriv,linearMap_eq_sum,
    deriv_pi (fun i => (differentiableAt_pi.mp hg i))]
  rfl

 
theorem taylor_deriv_comp [DecidableEq σ] {g : ℂ → σ → ℂ} {h : (σ → ℂ) → ℂ}
    (hg : AnalyticAt ℂ g 0) (hh : AnalyticAt ℂ h (g 0)) (n : ℕ) :
    PowerSeries.coeff n (taylorSeries (deriv (h ∘ g))) =
      ∑ j, ∑ k ∈ Finset.range (n+1),
        PowerSeries.coeff k (taylorSeries (coordinatePartial h j ∘ g)) *
        PowerSeries.coeff (n-k) (taylorSeries (deriv (fun z => g z j))) := by
  have he : deriv (h ∘ g) =ᶠ[nhds 0]
      (fun z => ∑ j, coordinatePartial h j (g z) * deriv (fun w => g w j) z) := by
    filter_upwards [hg.eventually_analyticAt,hg.continuousAt hh.eventually_analyticAt] with z hz hhz
    exact deriv_comp_eq_sum hhz.differentiableAt hz.differentiableAt
  rw [taylorSeries_congr he,taylorSeries_sum]
  · simp only [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show (fun z => coordinatePartial h j (g z) * deriv (fun w => g w j) z) =
      (coordinatePartial h j ∘ g) * deriv (fun w => g w j) from rfl,
      taylorSeries_mul ((partial_analytic hh j).comp hg) (analyticAt_pi_iff.mp hg j).deriv,
      PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff a (taylorSeries (coordinatePartial h j ∘ g)) *
          PowerSeries.coeff b (taylorSeries (deriv (fun z => g z j)))) n]
  · intro j _
    exact ((partial_analytic hh j).comp hg).fun_mul (analyticAt_pi_iff.mp hg j).deriv

 

theorem composeCoefficient_normal_chain [DecidableEq σ] {h : (σ → ℂ) → ℂ}
    (f : ℕ → σ → ℂ) (hh : AnalyticAt ℂ h (f 0)) (n : ℕ) :
    (n+1 : ℂ) * composeCoefficient h f (n+1) =
      ∑ j, ∑ k ∈ Finset.range (n+1),
        composeCoefficient (coordinatePartial h j) f k * (((n-k+1 : ℕ) : ℂ) * f (n-k+1) j) := by
  have hg := (jetPolynomial_hasSeries f (n+1)).analyticAt
  have hh' : AnalyticAt ℂ h (jetPolynomial f (n+1) 0) := by simpa using hh
  have he := taylor_deriv_comp hg hh' n
  rw [taylorSeries_deriv,PowerSeries.coeff_derivative] at he
  rw [mul_comm] at he
  change (n+1 : ℂ) * composeCoefficient h f (n+1) = _ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  have hp := composeCoefficient_eq_laterJet f (partial_analytic hh j) (hkn.trans (Nat.le_succ n))
  simp only [Function.comp_def] at hp ⊢
  rw [← hp]
  congr 1
  rw [taylorSeries_deriv,PowerSeries.coeff_derivative]
  simp_rw [← polynomialJet_eval]
  rw [taylorSeries_polynomial,Polynomial.coeff_coe,polynomialJet_coeff,ite_eq_left (by omega)]
  push_cast
  ring

end
section
open SplitTangent.DiagonalRationality
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

 
theorem tangentDeriv_comp {h : (σ → ℂ) → ℂ} {F : ℂ × ℂ → σ → ℂ} {w : ℂ × ℂ}
    (hh : AnalyticAt ℂ h (F w)) (hF : AnalyticAt ℂ F w) :
    tangentDeriv (h ∘ F) w =
      ∑ j, coordinatePartial h j (F w) * tangentDeriv (fun z => F z j) w := by
  have hFs : AnalyticAt ℂ (fun z => F (z,w.2)) w.1 :=
    AnalyticAt.comp (f := fun z : ℂ => (z,w.2)) hF
      (analyticAt_id.prod analyticAt_const)
  have he := deriv_comp_eq_sum hh.differentiableAt hFs.differentiableAt
  change deriv (fun z => (h ∘ F) (z,w.2)) w.1 = _ at he
  rw [tangentDeriv_eq (hh.comp hF)] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro j _
  rw [tangentDeriv_eq (analyticAt_pi_iff.mp hF j)]

 
theorem taylor_tangent_comp {h : (σ → ℂ) → ℂ} {F : ℂ × ℂ → σ → ℂ} {u : ℂ}
    (hh : AnalyticAt ℂ h (F (u,0))) (hF : AnalyticAt ℂ F (u,0)) (n : ℕ) :
    PowerSeries.coeff n (taylorSeries (fun v => tangentDeriv (h ∘ F) (u,v))) =
      ∑ j, ∑ k ∈ Finset.range (n+1),
        PowerSeries.coeff k (taylorSeries (fun v => coordinatePartial h j (F (u,v)))) *
        PowerSeries.coeff (n-k) (taylorSeries (fun v => tangentDeriv (fun z => F z j) (u,v))) := by
  have hi : AnalyticAt ℂ (fun v : ℂ => (u,v)) 0 := analyticAt_const.prod analyticAt_id
  have hFs : AnalyticAt ℂ (fun v => F (u,v)) 0 := hF.comp hi
  have he : (fun v => tangentDeriv (h ∘ F) (u,v)) =ᶠ[nhds 0]
      (fun v => ∑ j, coordinatePartial h j (F (u,v)) * tangentDeriv (fun z => F z j) (u,v)) := by
    filter_upwards [hi.continuousAt hF.eventually_analyticAt,
      hFs.continuousAt hh.eventually_analyticAt] with v hv hhv
    exact tangentDeriv_comp hhv hv
  rw [taylorSeries_congr he,taylorSeries_sum]
  · simp only [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hT : AnalyticAt ℂ (fun v => tangentDeriv (fun z => F z j) (u,v)) 0 :=
      (directionDeriv_analytic (analyticAt_pi_iff.mp hF j) (1,0)).comp hi
    have hP : AnalyticAt ℂ (fun v => coordinatePartial h j (F (u,v))) 0 :=
      AnalyticAt.comp (f := fun v => F (u,v)) (partial_analytic hh j) hFs
    rw [show (fun v => coordinatePartial h j (F (u,v)) * tangentDeriv (fun z => F z j) (u,v)) =
      (fun v => coordinatePartial h j (F (u,v))) *
        (fun v => tangentDeriv (fun z => F z j) (u,v)) from rfl,
      taylorSeries_mul hP hT,
      PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff a (taylorSeries (fun v => coordinatePartial h j (F (u,v)))) *
          PowerSeries.coeff b (taylorSeries (fun v => tangentDeriv (fun z => F z j) (u,v)))) n]
  · intro j _
    exact (AnalyticAt.comp (f := fun v => F (u,v)) (partial_analytic hh j) hFs).fun_mul
      ((directionDeriv_analytic (analyticAt_pi_iff.mp hF j) (1,0)).comp hi)

 

theorem composeCoefficient_tangent_chain {h : (σ → ℂ) → ℂ}
    (f : ℕ → ℂ → σ → ℂ) {u : ℂ} (n : ℕ)
    (hf : ∀ k, k ≤ n → ∀ i, AnalyticAt ℂ (fun z => f k z i) u)
    (hh : AnalyticAt ℂ h (f 0 u)) :
    deriv (fun z => composeCoefficient h (fun k => f k z) n) u =
      ∑ j, ∑ k ∈ Finset.range (n+1),
        composeCoefficient (coordinatePartial h j) (fun l => f l u) k *
          deriv (fun z => f (n-k) z j) u := by
  let F : ℂ × ℂ → σ → ℂ := fun w => jetPolynomial (fun k => f k w.1) n w.2
  have hF : AnalyticAt ℂ F (u,0) := jetPolynomial_analytic n hf
  have hh' : AnalyticAt ℂ h (F (u,0)) := by simpa [F] using hh
  change deriv (fun z => PowerSeries.coeff n (taylorSeries (fun v => (h ∘ F) (z,v)))) u = _
  rw [deriv_normalCoefficient (hh'.comp hF) n,taylor_tangent_comp hh' hF]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  have hp := composeCoefficient_eq_laterJet (fun l => f l u) (partial_analytic hh j) hkn
  change PowerSeries.coeff k (taylorSeries (fun v => coordinatePartial h j
    (jetPolynomial (fun l => f l u) n v))) * _ = _
  rw [← hp]
  congr 1
  rw [← deriv_normalCoefficient (analyticAt_pi_iff.mp hF j) (n-k)]
  congr 1
  funext z
  change PowerSeries.coeff (n-k) (taylorSeries (fun v => jetPolynomial (fun l => f l z) n v j)) = _
  simp_rw [← polynomialJet_eval]
  rw [taylorSeries_polynomial,Polynomial.coeff_coe,polynomialJet_coeff,ite_eq_left (Nat.sub_le ..)]

end
section
open SplitTangent.DiagonalRationality
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

 

def formalSubst (h : (σ → ℂ) → ℂ) (f : ℕ → σ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (composeCoefficient h f)

omit [Fintype σ] in
@[simp] theorem coeff_formalSubst (h : (σ → ℂ) → ℂ) (f : ℕ → σ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (formalSubst h f) = composeCoefficient h f n := by
  simp [formalSubst]

theorem formalSubst_congr {h k : (σ → ℂ) → ℂ} (f : ℕ → σ → ℂ)
    (he : h =ᶠ[nhds (f 0)] k) : formalSubst h f = formalSubst k f := by
  ext n
  simp only [coeff_formalSubst,composeCoefficient]
  apply congrArg (PowerSeries.coeff n)
  apply taylorSeries_congr
  exact he.comp_tendsto (by simpa only [ContinuousAt,jetPolynomial_zero] using
    (jetPolynomial_hasSeries f n).analyticAt.continuousAt)

theorem formalSubst_mul {h k : (σ → ℂ) → ℂ} (f : ℕ → σ → ℂ)
    (hh : AnalyticAt ℂ h (f 0)) (hk : AnalyticAt ℂ k (f 0)) :
    formalSubst (fun x => h x * k x) f = formalSubst h f * formalSubst k f := by
  ext n
  rw [coeff_formalSubst,composeCoefficient_mul f hh hk,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a (formalSubst h f) * PowerSeries.coeff b (formalSubst k f)) n]
  simp only [coeff_formalSubst]

theorem formalSubst_sum {ι : Type*} (s : Finset ι)
    (h : ι → (σ → ℂ) → ℂ) (f : ℕ → σ → ℂ)
    (hh : ∀ i ∈ s, AnalyticAt ℂ (h i) (f 0)) :
    formalSubst (fun x => ∑ i ∈ s, h i x) f = ∑ i ∈ s, formalSubst (h i) f := by
  ext n
  simp only [coeff_formalSubst,composeCoefficient_sum s h f hh,map_sum]

theorem formalSubst_assoc (H : (σ → ℂ) → τ → ℂ)
    (h : (τ → ℂ) → ℂ) (f : ℕ → σ → ℂ)
    (hH : AnalyticAt ℂ H (f 0)) (hh : AnalyticAt ℂ h (H (f 0))) :
    formalSubst h (composeJet H f) = formalSubst (h ∘ H) f := by
  ext n
  simp only [coeff_formalSubst,composeCoefficient_assoc H h f hH hh]

 
def normalVector (f : ℕ → σ → ℂ) : σ → PowerSeries ℂ :=
  fun i => PowerSeries.derivative _ (PowerSeries.mk (fun n => f n i))

 
def tangentVector (f : ℕ → ℂ → σ → ℂ) (u : ℂ) : σ → PowerSeries ℂ :=
  fun i => PowerSeries.mk (fun n => deriv (fun z => f n z i) u)

 
def substitutedJacobian [DecidableEq σ] (H : (σ → ℂ) → τ → ℂ)
    (f : ℕ → σ → ℂ) : Matrix τ σ (PowerSeries ℂ) :=
  fun i j => formalSubst (coordinatePartial (fun x => H x i) j) f

theorem normalVector_compose [DecidableEq σ] (H : (σ → ℂ) → τ → ℂ)
    (f : ℕ → σ → ℂ) (hH : AnalyticAt ℂ H (f 0)) :
    normalVector (composeJet H f) = (substitutedJacobian H f).mulVec (normalVector f) := by
  funext i
  ext n
  simp only [normalVector,PowerSeries.coeff_derivative,PowerSeries.coeff_mk,composeJet,
    Matrix.mulVec,dotProduct,map_sum,PowerSeries.coeff_mul]
  rw [mul_comm,composeCoefficient_normal_chain f (analyticAt_pi_iff.mp hH i) n]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (substitutedJacobian H f i j) *
      (f (b+1) j * (b+1 : ℂ))) n]
  apply Finset.sum_congr rfl
  intro k hk
  simp [substitutedJacobian,mul_comm]

theorem tangentVector_compose [DecidableEq σ] (H : (σ → ℂ) → τ → ℂ)
    (f : ℕ → ℂ → σ → ℂ) (u : ℂ)
    (hf : ∀ n i, AnalyticAt ℂ (fun z => f n z i) u)
    (hH : AnalyticAt ℂ H (f 0 u)) :
    tangentVector (fun n z => composeJet H (fun k => f k z) n) u =
      (substitutedJacobian H (fun k => f k u)).mulVec (tangentVector f u) := by
  funext i
  ext n
  simp only [tangentVector,PowerSeries.coeff_mk,composeJet,Matrix.mulVec,dotProduct,
    map_sum,PowerSeries.coeff_mul]
  rw [composeCoefficient_tangent_chain f n (fun k _ i => hf k i) (analyticAt_pi_iff.mp hH i)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (substitutedJacobian H (fun k => f k u) i j) *
      deriv (fun z => f b z j) u) n]
  simp only [substitutedJacobian,coeff_formalSubst]

 
def substitutedMatrix (P : σ → σ → (σ → ℂ) → ℂ)
    (f : ℕ → σ → ℂ) : Matrix σ σ (PowerSeries ℂ) :=
  fun i j => formalSubst (P i j) f

 

theorem substituted_intertwining [DecidableEq σ] [DecidableEq τ]
    (H : (σ → ℂ) → τ → ℂ) (P : σ → σ → (σ → ℂ) → ℂ)
    (Q : τ → τ → (τ → ℂ) → ℂ) (f : ℕ → σ → ℂ)
    (hH : AnalyticAt ℂ H (f 0))
    (hP : ∀ i j, AnalyticAt ℂ (P i j) (f 0))
    (hQ : ∀ i j, AnalyticAt ℂ (Q i j) (H (f 0)))
    (he : ∀ i j, (fun x => ∑ k, coordinatePartial (fun y => H y i) k x * P k j x)
      =ᶠ[nhds (f 0)] (fun x => ∑ k, Q i k (H x) * coordinatePartial (fun y => H y k) j x)) :
    substitutedJacobian H f * substitutedMatrix P f =
      substitutedMatrix Q (composeJet H f) * substitutedJacobian H f := by
  funext i j
  simp only [Matrix.mul_apply,substitutedJacobian,substitutedMatrix]
  have hah i j := partial_analytic (analyticAt_pi_iff.mp hH i) j
  have hleft := formalSubst_sum Finset.univ
    (fun k x => coordinatePartial (fun y => H y i) k x * P k j x) f
    (fun k _ => (hah i k).mul (hP k j))
  have hright := formalSubst_sum Finset.univ
    (fun k x => Q i k (H x) * coordinatePartial (fun y => H y k) j x) f
    (fun k _ => ((hQ i k).comp hH).mul (hah k j))
  rw [formalSubst_congr f (he i j)] at hleft
  rw [hright] at hleft
  simp only [formalSubst_mul f (hah i _) (hP _ j)] at hleft
  rw [← hleft]
  apply Finset.sum_congr rfl
  intro k _
  exact (formalSubst_mul f ((hQ i k).comp hH) (hah k j)).trans
    (congrArg (fun a => a * formalSubst (coordinatePartial (fun x => H x k) j) f)
      (formalSubst_assoc H (Q i k) f hH (hQ i k)).symm)

 

theorem cauchy_target_covariance [DecidableEq σ] [DecidableEq τ]
    (H : (σ → ℂ) → τ → ℂ) (P : σ → σ → (σ → ℂ) → ℂ)
    (Q : τ → τ → (τ → ℂ) → ℂ) (f : ℕ → ℂ → σ → ℂ) (u : ℂ)
    (hf : ∀ n i, AnalyticAt ℂ (fun z => f n z i) u)
    (hH : AnalyticAt ℂ H (f 0 u))
    (hP : ∀ i j, AnalyticAt ℂ (P i j) (f 0 u))
    (hQ : ∀ i j, AnalyticAt ℂ (Q i j) (H (f 0 u)))
    (he : ∀ i j, (fun x => ∑ k, coordinatePartial (fun y => H y i) k x * P k j x)
      =ᶠ[nhds (f 0 u)] (fun x => ∑ k, Q i k (H x) * coordinatePartial (fun y => H y k) j x))
    (hsol : normalVector (fun k => f k u) =
      (substitutedMatrix P (fun k => f k u)).mulVec (tangentVector f u)) :
    normalVector (composeJet H (fun k => f k u)) =
      (substitutedMatrix Q (composeJet H (fun k => f k u))).mulVec
        (tangentVector (fun n z => composeJet H (fun k => f k z) n) u) := by
  rw [normalVector_compose H _ hH,hsol,Matrix.mulVec_mulVec,
    substituted_intertwining H P Q _ hH hP hQ he,← Matrix.mulVec_mulVec,
    tangentVector_compose H f u hf hH]

end
section
open SplitTangent.DiagonalRationality
open PowerSeries


@[simp] theorem taylorSeries_const (c : ℂ) : taylorSeries (fun _ => c) = C c := by
  simpa using taylorSeries_polynomial (Polynomial.C c)


end
open SplitTangent.DiagonalRationality PowerSeries
variable {σ : Type*} [Fintype σ]

 
def reparamJet (b : PowerSeries ℂ) (f : ℕ → σ → ℂ) : ℕ → σ → ℂ :=
  fun n i => coeff n (subst b (PowerSeries.mk (fun k => f k i)))

end SplitTangent.HolomorphicJets
namespace SplitTangent.FormalCauchy
open PowerSeries

 

def analyticDerivation {U : Set ℂ} (hU : IsOpen U) :
    Derivation ℂ (AnalyticFunction U) (AnalyticFunction U) where
  toLinearMap := analyticDerivative hU
  map_one_eq_zero' := by
    classical
    apply Subtype.ext
    funext z
    change (if z ∈ U then deriv (fun _ : ℂ => (1 : ℂ)) z else 0) = 0
    simp
  leibniz' := analyticDerivative_mul hU

 
def dCoeff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (δ : Derivation R A A) (f : PowerSeries A) : PowerSeries A :=
  deriveCoefficients δ f

@[simp] theorem coeff_dCoeff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (δ : Derivation R A A) (f : PowerSeries A) (n : ℕ) :
    coeff n (dCoeff δ f) = δ (coeff n f) := rfl


@[simp] theorem coeff_eval_dCoeff {U : Set ℂ} (hU : IsOpen U) {u : ℂ} (hu : u ∈ U)
    (f : PowerSeries (AnalyticFunction U)) (n : ℕ) :
    coeff n (PowerSeries.map (analyticEvaluation U u) (dCoeff (analyticDerivation hU) f)) =
      deriv (fun z => coeff n f z) u := by
  rw [coeff_map,coeff_dCoeff]
  exact analyticDerivative_apply hU _ hu




def analyticPullback {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U) :
    AnalyticFunction U →ₐ[ℂ] AnalyticFunction W where
  toFun f := ⟨fun z => f (α z), fun z hz => (f.property (α z) (hαU hz)).comp (hα z hz)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl



end SplitTangent.FormalCauchy
namespace SplitTangent.HolomorphicJets
section
open PowerSeries SplitTangent.DiagonalRationality SplitTangent.FormalCauchy

 
def sourceDifference (α : ℂ → ℂ) : ℂ × ℂ → ℂ := fun w => α (w.1+w.2) - α w.1

def sourceNormal (α : ℂ → ℂ) (u : ℂ) : PowerSeries ℂ :=
  taylorSeries (fun v => sourceDifference α (u,v))

theorem sourceDifference_analytic {α : ℂ → ℂ} {u v : ℂ}
    (hα : AnalyticAt ℂ α u) (hα' : AnalyticAt ℂ α (u+v)) :
    AnalyticAt ℂ (sourceDifference α) (u,v) := by
  exact (AnalyticAt.comp (f := fun w : ℂ × ℂ => w.1+w.2) (x := (u,v)) hα'
    (analyticAt_fst.add analyticAt_snd)).sub
      (AnalyticAt.comp (f := fun w : ℂ × ℂ => w.1) (x := (u,v)) hα analyticAt_fst)

@[simp] theorem sourceNormal_constant (α : ℂ → ℂ) (u : ℂ) :
    constantCoeff (sourceNormal α u) = 0 := by
  rw [← coeff_zero_eq_constantCoeff,sourceNormal,coeff_taylorSeries]
  simp [sourceDifference]

 

def sourceNormalFamily {W : Set ℂ} (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W) :
    PowerSeries (AnalyticFunction W) :=
  PowerSeries.mk (fun n => ⟨fun u => coeff n (sourceNormal α u), fun u hu => by
    exact normalCoefficient_analytic
      (sourceDifference_analytic (hα u hu) (by simpa using hα u hu : AnalyticAt ℂ α (u+0))) n⟩)

@[simp] theorem sourceNormalFamily_eval {W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (u : ℂ) :
    PowerSeries.map (analyticEvaluation W u) (sourceNormalFamily α hα) = sourceNormal α u := by
  ext n
  simp [sourceNormalFamily]

end
section
open PowerSeries SplitTangent.DiagonalRationality SplitTangent.FormalCauchy
variable {σ : Type*} [Fintype σ] [DecidableEq σ]



def sourceTransform {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (F : σ → PowerSeries (AnalyticFunction U)) : σ → PowerSeries (AnalyticFunction W) :=
  fun i => subst (sourceNormalFamily α hα)
    (PowerSeries.map (analyticPullback α hα hαU).toRingHom (F i))


end
open PowerSeries SplitTangent.FormalCauchy

end SplitTangent.HolomorphicJets
namespace SplitTangent.ActualCauchy
open SplitTangent.HolomorphicJets SplitTangent.FormalCauchy
variable {σ : Type*} [Fintype σ] {U : Set ℂ}

 

def seed (g : σ → AnalyticFunction U) (f : ℕ → σ → AnalyticFunction U) :
    ℕ → σ → AnalyticFunction U := fun k => if k = 0 then g else f k

omit [Fintype σ] in
@[simp] theorem seed_zero (g : σ → AnalyticFunction U) (f : ℕ → σ → AnalyticFunction U) :
    seed g f 0 = g := by simp [seed]

omit [Fintype σ] in
theorem seed_eq {g : σ → AnalyticFunction U} {f : ℕ → σ → AnalyticFunction U}
    (hf : f 0 = g) : seed g f = f := by
  funext n; by_cases hn : n = 0
  · subst n; simpa using hf.symm
  · simp [seed,hn]

 
def actualComposition (g : σ → AnalyticFunction U) (h : (σ → ℂ) → ℂ)
    (hh : ∀ u ∈ U, AnalyticAt ℂ h (fun i => g i u))
    (f : ℕ → σ → AnalyticFunction U) (n : ℕ) : AnalyticFunction U :=
  ⟨fun u => composeCoefficient h (fun k i => seed g f k i u) n, by
    intro u hu
    apply composeCoefficient_analytic n
    · intro k _ i; exact (seed g f k i).property u hu
    · simpa using hh u hu⟩

@[simp] theorem actualComposition_apply (g : σ → AnalyticFunction U)
    (h : (σ → ℂ) → ℂ) (hh : ∀ u ∈ U, AnalyticAt ℂ h (fun i => g i u))
    (f : ℕ → σ → AnalyticFunction U) (n : ℕ) (u : ℂ) :
    actualComposition g h hh f n u =
      composeCoefficient h (fun k i => seed g f k i u) n := rfl

theorem actualComposition_causal (g : σ → AnalyticFunction U)
    (h : (σ → ℂ) → ℂ) (hh : ∀ u ∈ U, AnalyticAt ℂ h (fun i => g i u))
    {f f' : ℕ → σ → AnalyticFunction U} {n : ℕ}
    (hff : ∀ k, k ≤ n → f k = f' k) :
    actualComposition g h hh f n = actualComposition g h hh f' n := by
  apply Subtype.ext; funext u
  apply composeCoefficient_causal
  intro k hk
  by_cases hk0 : k = 0
  · simp [seed,hk0]
  · simp [seed,hk0,hff k hk]

 

def actualOperator (hU : IsOpen U) (g : σ → AnalyticFunction U)
    (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (fun r => g r u))
    (f : ℕ → σ → AnalyticFunction U) (n : ℕ) : σ → AnalyticFunction U :=
  fun i => ∑ j, ∑ k ∈ Finset.range (n+1),
    actualComposition g (P i j) (hP i j) f k * analyticDerivative hU (f (n-k) j)

theorem actualOperator_causal (hU : IsOpen U) (g : σ → AnalyticFunction U)
    (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (fun r => g r u)) :
    Causal (actualOperator hU g P hP) := by
  intro n f f' hff
  funext i
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [actualComposition_causal g (P i j) (hP i j) (fun l hl => hff l (hl.trans hkn)),
    hff (n-k) (Nat.sub_le ..)]

 

def IsActualSolution (hU : IsOpen U) (g : σ → AnalyticFunction U)
    (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (fun r => g r u))
    (f : ℕ → σ → AnalyticFunction U) : Prop :=
  f 0 = g ∧ ∀ n : ℕ, (n+1 : ℂ) • f (n+1) = actualOperator hU g P hP f n

 

theorem existsUnique_actualSolution (hU : IsOpen U) (g : σ → AnalyticFunction U)
    (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (fun r => g r u)) :
    ∃! f : ℕ → σ → AnalyticFunction U, IsActualSolution hU g P hP f :=
  existsUnique_coefficients g _ (actualOperator_causal hU g P hP)

theorem IsActualSolution.pointwise {hU : IsOpen U} {g : σ → AnalyticFunction U}
    {P : σ → σ → (σ → ℂ) → ℂ}
    {hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (fun r => g r u)}
    {f : ℕ → σ → AnalyticFunction U} (hf : IsActualSolution hU g P hP f)
    (n : ℕ) (i : σ) {u : ℂ} (hu : u ∈ U) :
    (n+1 : ℂ) * f (n+1) i u = ∑ j, ∑ k ∈ Finset.range (n+1),
      composeCoefficient (P i j) (fun l r => f l r u) k * deriv (f (n-k) j : ℂ → ℂ) u := by
  have he := congrArg (fun a : σ → AnalyticFunction U => a i u) (hf.2 n)
  simpa [actualOperator,actualComposition_apply,seed_eq hf.1,analyticDerivative_apply hU _ hu]
    using he

end SplitTangent.ActualCauchy
namespace SplitTangent.HolomorphicJets
section
open PowerSeries SplitTangent.FormalCauchy SplitTangent.ActualCauchy
variable {σ : Type*} [Fintype σ]

 

def CauchyOn (U : Set ℂ) (g : ℂ → σ → ℂ)
    (P : σ → σ → (σ → ℂ) → ℂ) (f : ℕ → ℂ → σ → ℂ) : Prop :=
  (∀ n i, AnalyticOnNhd ℂ (fun u => f n u i) U) ∧
  (∀ u ∈ U, f 0 u = g u) ∧
  ∀ u ∈ U, normalVector (fun n => f n u) =
    (substitutedMatrix P (fun n => f n u)).mulVec (tangentVector f u)

theorem cauchyOn_recurrence {U : Set ℂ} {g : ℂ → σ → ℂ}
    {P : σ → σ → (σ → ℂ) → ℂ} {f : ℕ → ℂ → σ → ℂ}
    (hf : CauchyOn U g P f) {u : ℂ} (hu : u ∈ U) (n : ℕ) (i : σ) :
    (n+1 : ℂ) * f (n+1) u i = ∑ j, ∑ k ∈ Finset.range (n+1),
      composeCoefficient (P i j) (fun l => f l u) k * deriv (fun z => f (n-k) z j) u := by
  have he := congrArg (coeff n) (congrFun (hf.2.2 u hu) i)
  simp only [normalVector,coeff_derivative,coeff_mk,Matrix.mulVec,dotProduct,
    map_sum,coeff_mul,substitutedMatrix,coeff_formalSubst,tangentVector] at he
  rw [mul_comm] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro j _
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => composeCoefficient (P i j) (fun l => f l u) a *
      deriv (fun z => f b z j) u) n).symm

 
theorem exists_cauchyOn {U : Set ℂ} (hU : IsOpen U) (g : ℂ → σ → ℂ)
    (hg : ∀ i, AnalyticOnNhd ℂ (fun u => g u i) U)
    (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (g u)) :
    ∃ f, CauchyOn U g P f := by
  let g' : σ → AnalyticFunction U := fun i => ⟨fun u => g u i, hg i⟩
  obtain ⟨f,hf,-⟩ := existsUnique_actualSolution hU g' P hP
  refine ⟨fun n u i => f n i u, ?_, ?_, ?_⟩
  · intro n i; exact (f n i).property
  · intro u hu; exact congrArg (fun a : σ → AnalyticFunction U => fun i => a i u) hf.1
  · intro u hu; funext i; ext n
    simp only [normalVector,coeff_derivative,coeff_mk,Matrix.mulVec,dotProduct,
      map_sum,coeff_mul,substitutedMatrix,coeff_formalSubst,tangentVector]
    rw [mul_comm, hf.pointwise n i hu]
    apply Finset.sum_congr rfl
    intro j _
    exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => composeCoefficient (P i j) (fun l r => f l r u) a *
        deriv (f b j : ℂ → ℂ) u) n).symm

 
theorem cauchyOn_unique {U : Set ℂ} (hU : IsOpen U) {g : ℂ → σ → ℂ}
    {P : σ → σ → (σ → ℂ) → ℂ} {f f' : ℕ → ℂ → σ → ℂ}
    (hf : CauchyOn U g P f) (hf' : CauchyOn U g P f') :
    ∀ n u, u ∈ U → f n u = f' n u := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u hu
    cases n with
    | zero => exact (hf.2.1 u hu).trans (hf'.2.1 u hu).symm
    | succ n =>
      funext i
      have hcoef (k : ℕ) (hk : k ≤ n) : (fun l => f l u) k = (fun l => f' l u) k :=
        ih k (by omega) u hu
      have hder (k : ℕ) (hk : k ≤ n) (j : σ) :
          deriv (fun z => f k z j) u = deriv (fun z => f' k z j) u := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [hU.mem_nhds hu] with z hz
        exact congrFun (ih k (by omega) z hz) j
      apply mul_left_cancel₀ (show (n+1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)
      rw [cauchyOn_recurrence hf hu, cauchyOn_recurrence hf' hu]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      rw [composeCoefficient_causal _ (fun l hl => hcoef l (hl.trans hkn)),
        hder (n-k) (Nat.sub_le ..) j]

 

theorem CauchyOn.mono {U W : Set ℂ} {g : ℂ → σ → ℂ}
    {P : σ → σ → (σ → ℂ) → ℂ} {f : ℕ → ℂ → σ → ℂ}
    (hf : CauchyOn U g P f) (hWU : W ⊆ U) : CauchyOn W g P f :=
  ⟨fun n i => (hf.1 n i).mono hWU, fun u hu => hf.2.1 u (hWU hu),
    fun u hu => hf.2.2 u (hWU hu)⟩

end
section
open PowerSeries SplitTangent.FormalCauchy SplitTangent.DiagonalRationality
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

 

theorem CauchyOn.target [DecidableEq σ] [DecidableEq τ]
    {U : Set ℂ} {g : ℂ → σ → ℂ} {P : σ → σ → (σ → ℂ) → ℂ}
    {f : ℕ → ℂ → σ → ℂ} (hf : CauchyOn U g P f)
    (H : (σ → ℂ) → τ → ℂ) (Q : τ → τ → (τ → ℂ) → ℂ)
    (hH : ∀ u ∈ U, AnalyticAt ℂ H (g u))
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (g u))
    (hQ : ∀ i j u, u ∈ U → AnalyticAt ℂ (Q i j) (H (g u)))
    (he : ∀ u ∈ U, ∀ i j,
      (fun x => ∑ k, coordinatePartial (fun y => H y i) k x * P k j x)
        =ᶠ[nhds (g u)]
      (fun x => ∑ k, Q i k (H x) * coordinatePartial (fun y => H y k) j x)) :
    CauchyOn U (H ∘ g) Q (fun n u => composeJet H (fun k => f k u) n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n i u hu
    apply composeCoefficient_analytic n (fun k _ j => hf.1 k j u hu)
    rw [hf.2.1 u hu]
    exact analyticAt_pi_iff.mp (hH u hu) i
  · intro u hu
    simp only [composeJet_zero,hf.2.1 u hu,Function.comp_apply]
  · intro u hu
    apply cauchy_target_covariance H P Q f u (fun n i => hf.1 n i u hu)
    · rw [hf.2.1 u hu]; exact hH u hu
    · intro i j; rw [hf.2.1 u hu]; exact hP i j u hu
    · intro i j; rw [hf.2.1 u hu]; exact hQ i j u hu
    · rw [hf.2.1 u hu]; exact he u hu
    · exact hf.2.2 u hu

 

theorem cauchyOn_target_glue [DecidableEq σ] [DecidableEq τ]
    {U : Set ℂ} (hU : IsOpen U) {g : ℂ → σ → ℂ}
    {P : σ → σ → (σ → ℂ) → ℂ} {f : ℕ → ℂ → σ → ℂ}
    (hf : CauchyOn U g P f) (H : (σ → ℂ) → τ → ℂ)
    (Q : τ → τ → (τ → ℂ) → ℂ) {f' : ℕ → ℂ → τ → ℂ}
    (hf' : CauchyOn U (H ∘ g) Q f')
    (hH : ∀ u ∈ U, AnalyticAt ℂ H (g u))
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (g u))
    (hQ : ∀ i j u, u ∈ U → AnalyticAt ℂ (Q i j) (H (g u)))
    (he : ∀ u ∈ U, ∀ i j,
      (fun x => ∑ k, coordinatePartial (fun y => H y i) k x * P k j x)
        =ᶠ[nhds (g u)]
      (fun x => ∑ k, Q i k (H x) * coordinatePartial (fun y => H y k) j x)) :
    ∀ n u, u ∈ U → composeJet H (fun k => f k u) n = f' n u :=
  cauchyOn_unique hU (hf.target H Q hH hP hQ he) hf'

 
def familySeries {U : Set ℂ} (f : ℕ → ℂ → σ → ℂ)
    (hf : ∀ n i, AnalyticOnNhd ℂ (fun u => f n u i) U) :
    σ → PowerSeries (AnalyticFunction U) :=
  fun i => PowerSeries.mk (fun n => ⟨fun u => f n u i, hf n i⟩)

omit [Fintype σ] in
@[simp] theorem familySeries_eval {U : Set ℂ} (f : ℕ → ℂ → σ → ℂ)
    (hf : ∀ n i, AnalyticOnNhd ℂ (fun u => f n u i) U) (u : ℂ) (i : σ) :
    PowerSeries.map (analyticEvaluation U u) (familySeries f hf i) =
      PowerSeries.mk (fun n => f n u i) := by
  ext n; simp [familySeries]

omit [Fintype σ] in
@[simp] theorem familySeries_coeff {U : Set ℂ} (f : ℕ → ℂ → σ → ℂ)
    (hf : ∀ n i, AnalyticOnNhd ℂ (fun u => f n u i) U) (u : ℂ) (i : σ) (n : ℕ) :
    coeff n (familySeries f hf i) u = f n u i := by simp [familySeries]

end
section
open PowerSeries SplitTangent.FormalCauchy SplitTangent.DiagonalRationality
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def sourceFamily {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (f : ℕ → ℂ → σ → ℂ) (hf : ∀ n i, AnalyticOnNhd ℂ (fun u => f n u i) U) :
    ℕ → ℂ → σ → ℂ :=
  fun n u i => coeff n (sourceTransform α hα hαU (familySeries f hf) i) u

end

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem CauchyOn.congr_initial {U : Set ℂ} {g g' : ℂ → σ → ℂ}
    {P : σ → σ → (σ → ℂ) → ℂ} {f : ℕ → ℂ → σ → ℂ}
    (hf : CauchyOn U g P f) (he : Set.EqOn g g' U) : CauchyOn U g' P f :=
  ⟨hf.1,fun u hu => (hf.2.1 u hu).trans (he hu),hf.2.2⟩
end SplitTangent.HolomorphicJets

namespace SplitTangent.TangentSplitting
section
open HolomorphicJets
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)



def coordinateDomain (g : ℂ → X.Carrier) (x : X.Carrier) : Set ℂ :=
  g ⁻¹' (chartAt (Model X) x).source

def coordinateCurve (g : ℂ → X.Carrier) (x : X.Carrier) : ℂ → Model X :=
  (chartAt (Model X) x) ∘ g

theorem coordinateDomain_open {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x : X.Carrier) :
    IsOpen (coordinateDomain g x) := (chartAt (Model X) x).open_source.preimage hg.continuous

theorem coordinateCurve_analytic_formal {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x : X.Carrier) :
    AnalyticOnNhd ℂ (coordinateCurve g x) (coordinateDomain g x) := by
  intro z hz
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hz
  exact (hc.comp z (hg z)).contDiffAt.analyticAt

 

def localJet {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x : X.Carrier) :
    ℕ → ℂ → Model X := Classical.choose
  (exists_cauchyOn (coordinateDomain_open hg x) (coordinateCurve g x)
    (fun i z hz => analyticAt_pi_iff.mp (coordinateCurve_analytic_formal hg x z hz) i)
    (S.coordinateMatrix x) (fun i j _ hz => S.coordinateMatrix_analytic x i j _
      ((chartAt (Model X) x).map_source hz)))

theorem localJet_solution {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x : X.Carrier) :
    CauchyOn (coordinateDomain g x) (coordinateCurve g x) (S.coordinateMatrix x)
      (S.localJet hg x) := Classical.choose_spec _



end

section
open HolomorphicJets PowerSeries
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

def scalarCoordinate (h : X.Carrier → ℂ) (x : X.Carrier) : Model X → ℂ :=
  h ∘ (chartAt (Model X) x).symm



def scalarJet {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (h : X.Carrier → ℂ) (u : ℂ) : PowerSeries ℂ :=
  formalSubst (scalarCoordinate h (g u)) (fun k => S.localJet hg (g u) k u)

@[simp] theorem scalarJet_constant {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (h : X.Carrier → ℂ) (u : ℂ) : constantCoeff (S.scalarJet hg h u) = h (g u) := by
  have hf0 := (S.localJet_solution hg (g u)).2.1 u (mem_chart_source (Model X) (g u))
  simp only [scalarJet,formalSubst,← coeff_zero_eq_constantCoeff,coeff_mk,
    composeCoefficient,DiagonalRationality.coeff_taylorSeries,iteratedDeriv_zero,
    Nat.factorial_zero,Nat.cast_one,div_one,jetPolynomial_zero]
  rw [hf0]
  simp only [scalarCoordinate,coordinateCurve,Function.comp_apply,
    (chartAt (Model X) (g u)).left_inv (mem_chart_source (Model X) (g u))]



end

open HolomorphicJets PowerSeries
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)


@[simp] theorem scalarJet_const {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (c : ℂ) (u : ℂ) :
    S.scalarJet hg (fun _ => c) u = C c := by
  ext n
  simp only [scalarJet,coeff_formalSubst,composeCoefficient,scalarCoordinate,Function.comp_apply]
  rw [taylorSeries_const]

end SplitTangent.TangentSplitting

section CurveImports

open Filter Topology Polynomial
namespace SplitTangent.ProjectiveLine

 
def MeromorphicAtInfinity (f : ℂ → ℂ) : Prop :=
  MeromorphicAt (fun z => f z⁻¹) 0



end SplitTangent.ProjectiveLine

namespace SplitTangent



namespace PolynomialTuple

 
theorem gcd_mem_span {ι : Type*} (p : ι → ℂ[X]) (s : Finset ι) :
    s.gcd p ∈ Ideal.span (Set.range p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.gcd_insert]
    obtain ⟨a,b,h⟩ := exists_gcd_eq_mul_add_mul (p i) (s.gcd p)
    rw [h]
    exact (Ideal.span (Set.range p)).add_mem
      ((Ideal.span (Set.range p)).mul_mem_right a (Ideal.subset_span ⟨i,rfl⟩))
      ((Ideal.span (Set.range p)).mul_mem_right b ih)

 
theorem bezout {ι : Type*} [Fintype ι] (p : ι → ℂ[X])
    (hp : Finset.univ.gcd p = 1) : ∃ a : ι → ℂ[X], ∑ i, a i * p i = 1 := by
  apply Ideal.mem_span_range_iff_exists_fun.mp
  rw [← hp]
  exact gcd_mem_span p Finset.univ

 
theorem basepoint_free {ι : Type*} [Fintype ι] (p : ι → ℂ[X])
    (hp : Finset.univ.gcd p = 1) (z : ℂ) : ∃ i, (p i).eval z ≠ 0 := by
  obtain ⟨a,ha⟩ := bezout p hp
  by_contra! h
  have he := congrArg (Polynomial.eval z) ha
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, h, mul_zero,
    Finset.sum_const_zero, Polynomial.eval_one, zero_ne_one] at he


end PolynomialTuple



end SplitTangent

end CurveImports

open Filter Topology

namespace AnalyticRetraction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

 

omit [CompleteSpace F] in
theorem localInverse_analytic {f : E → F} {a : E} (hf : AnalyticAt ℂ f a)
    (i : E ≃L[ℂ] F) (hi : fderiv ℂ f a = i.toContinuousLinearMap) :
    AnalyticAt ℂ ((hi ▸ hf.hasStrictFDerivAt).localInverse f i a) (f a) := by
  have hd : HasStrictFDerivAt f i.toContinuousLinearMap a := hi ▸ hf.hasStrictFDerivAt
  let R := hd.toOpenPartialHomeomorph f
  have hx : a ∈ R.source := hd.mem_toOpenPartialHomeomorph_source
  obtain ⟨p,hp⟩ := hf
  have h1 : p 1 = (continuousMultilinearCurryFin1 ℂ E F).symm i.toContinuousLinearMap := by
    apply (continuousMultilinearCurryFin1 ℂ E F).injective
    rw [LinearIsometryEquiv.apply_symm_apply, ← hp.fderiv_eq, hi]
  exact (R.hasFPowerSeriesAt_symm hx hp h1).analyticAt

 

omit [CompleteSpace F] in
theorem exists_left_inverse [FiniteDimensional ℂ F] {f : E → F} {a : E}
    (hf : AnalyticAt ℂ f a) (hinj : Function.Injective (fderiv ℂ f a)) :
    ∃ r : F → E, AnalyticAt ℂ r (f a) ∧ r (f a) = a ∧
      ∀ᶠ x in 𝓝 a, r (f x) = x := by
  let D := fderiv ℂ f a
  obtain ⟨L,hL⟩ := LinearMap.exists_leftInverse_of_injective D.toLinearMap
    (LinearMap.ker_eq_bot.mpr hinj)
  let C : F →L[ℂ] E := L.toContinuousLinearMap
  have hC : C.comp D = ContinuousLinearMap.id ℂ E := by
    ext x
    exact congrArg (fun T : E →ₗ[ℂ] E => T x) hL
  let g : E → E := C ∘ f
  have hg : AnalyticAt ℂ g a := (C.analyticAt _).comp hf
  have hd : fderiv ℂ g a = (ContinuousLinearEquiv.refl ℂ E).toContinuousLinearMap := by
    rw [fderiv_comp a C.differentiableAt hf.differentiableAt, C.fderiv]
    exact hC
  have hs : HasStrictFDerivAt g (ContinuousLinearEquiv.refl ℂ E).toContinuousLinearMap a :=
    hd ▸ hg.hasStrictFDerivAt
  let r := hs.localInverse g (ContinuousLinearEquiv.refl ℂ E) a ∘ C
  refine ⟨r, ?_, hs.localInverse_apply_image, hs.eventually_left_inverse⟩
  have hr := localInverse_analytic hg (ContinuousLinearEquiv.refl ℂ E) hd
  change AnalyticAt ℂ (hs.localInverse g (ContinuousLinearEquiv.refl ℂ E) a ∘ C) (f a)
  apply AnalyticAt.comp (f := C)
  · exact hr
  · exact C.analyticAt _

end AnalyticRetraction

namespace SplitTangent.HolomorphicJets
section
open DiagonalRationality Filter Topology
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

omit [Fintype σ] in
@[simp] theorem composeJet_id (f : ℕ → σ → ℂ) : composeJet id f = f := by
  funext n i
  simp only [composeJet,composeCoefficient,Function.id_def]
  simp_rw [← polynomialJet_eval]
  rw [taylorSeries_polynomial,Polynomial.coeff_coe,polynomialJet_coeff,ite_eq_left le_rfl]

end

open DiagonalRationality Filter Topology

end SplitTangent.HolomorphicJets

namespace SplitTangent.DiagonalRationality
open Polynomial

 

def normalBiPolynomial (m : ℕ) (a : BiCoefficients m) : Polynomial (Polynomial ℂ) :=
  (biPolynomial m a).comp (Polynomial.X + Polynomial.C Polynomial.X)

@[simp] theorem polynomialFunction_X : polynomialFunction (Polynomial.X : Polynomial ℂ) = id := by
  ext z
  simp


def bivariateEvaluation (P : Polynomial (Polynomial ℂ)) (w : ℂ × ℂ) : ℂ :=
  P.eval₂ (Polynomial.evalRingHom w.1) w.2

@[simp] theorem evaluate_polynomial_map (P : Polynomial (Polynomial ℂ)) (w : ℂ × ℂ) :
    polynomialEvaluation (P.map polynomialFunction.toRingHom) w = bivariateEvaluation P w := by
  simp only [polynomialEvaluation,bivariateEvaluation]
  rw [Polynomial.eval₂_map]
  rfl

end SplitTangent.DiagonalRationality

open Filter Topology

namespace SplitTangent.ProjectiveEmbedding
section
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)

 
def Incidence (x : X.Carrier) (v : Fin (e.N+1) → ℂ) : Prop :=
  ∀ i j, (e.map x).rep i * v j = (e.map x).rep j * v i

 

theorem incidence_iff_coordinates {x : X.Carrier} {v : Fin (e.N+1) → ℂ}
    {i : Fin (e.N+1)} (hi : (e.map x).rep i ≠ 0) :
    e.Incidence x v ↔ ∀ j, v j = v i * projectiveCoordinates i (e.map x) j := by
  constructor
  · intro h j
    have hj := h i j
    dsimp [projectiveCoordinates]
    field_simp
    linear_combination hj
  · intro h j k
    rw [h j,h k]
    dsimp [projectiveCoordinates]
    ring

theorem incidence_iff_projective {x : X.Carrier} {v : Fin (e.N+1) → ℂ}
    (hv : v ≠ 0) : e.Incidence x v ↔ e.map x = Projectivization.mk ℂ v hv := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map x).rep_nonzero
  change (e.map x).rep i ≠ 0 at hi
  rw [e.incidence_iff_coordinates hi]
  constructor
  · intro h
    have hvi : v i ≠ 0 := by
      intro hz
      apply hv
      ext j
      rw [h j,hz,zero_mul]
      rfl
    rw [← Projectivization.mk_rep (e.map x),Projectivization.mk_eq_mk_iff']
    refine ⟨(e.map x).rep i / v i,?_⟩
    ext j
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [h j]
    dsimp [projectiveCoordinates]
    field_simp
  · intro h
    have hm := (Projectivization.mk_eq_mk_iff' ℂ _ _ (e.map x).rep_nonzero hv).mp
      ((Projectivization.mk_rep (e.map x)).trans h)
    obtain ⟨a,ha⟩ := hm
    have hai (j) : (e.map x).rep j = a * v j := (congrFun ha j).symm
    have ha0 : a ≠ 0 := by
      intro hz
      apply (e.map x).rep_nonzero
      rw [← ha,hz,zero_smul]
    have hva : v i ≠ 0 := by contrapose! hi; rw [hai i,hi,mul_zero]
    intro j
    dsimp [projectiveCoordinates]
    rw [hai i,hai j]
    field_simp

theorem incidence_unique {x y : X.Carrier} {v : Fin (e.N+1) → ℂ}
    (hv : v ≠ 0) (hx : e.Incidence x v) (hy : e.Incidence y v) : x = y :=
  e.injective ((e.incidence_iff_projective hv).mp hx |>.trans
    ((e.incidence_iff_projective hv).mp hy).symm)

end

end SplitTangent.ProjectiveEmbedding

namespace SplitTangent.TangentSplitting

open Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']

 
def WedgeAt (F : E → X.Carrier) (A : E → ℂ) (z : E) : Prop :=
  ∀ v w : E, fderiv ℂ A z v • S.projector (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z w) =
    fderiv ℂ A z w • S.projector (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z v)

end SplitTangent.TangentSplitting

open Filter Topology Metric Set

 

open MvPowerSeries
namespace SplitTangent.FormalBlowup

abbrev D := MvPowerSeries (Fin 2) ℂ
abbrev x : D := X 0
abbrev y : D := X 1

lemma x_ne_zero : (x : D) ≠ 0 := by
  intro h
  have H := congrArg (coeff (Finsupp.single 0 1)) h
  simp [x] at H

 
def highOrder (k : ℕ) : Ideal D where
  carrier := {f | (k : ℕ∞) ≤ f.order}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact (le_min hf hg).trans min_order_le_add
  smul_mem' := by
    intro f g hg
    change (k : ℕ∞) ≤ (f * g).order
    exact (hg.trans (le_add_left le_rfl)).trans le_order_mul

lemma mem_highOrder {k : ℕ} {f : D} : f ∈ highOrder k ↔
    ∀ d : Fin 2 →₀ ℕ, d 0 + d 1 < k → coeff d f = 0 := by
  change ((k : ℕ∞) ≤ f.order) ↔ _
  constructor
  · intro hf d hd
    apply coeff_of_lt_order
    have hd' : (d.degree : ℕ∞) < k := by
      simpa [Finsupp.degree_eq_sum,Fin.sum_univ_two] using (show ((d 0 + d 1 : ℕ) : ℕ∞) < k by exact_mod_cast hd)
    exact hd'.trans_le hf
  · intro hf
    apply nat_le_order
    intro d hd
    apply hf d
    simpa [Finsupp.degree_eq_sum,Fin.sum_univ_two] using hd



def coordinateSubstitution : Fin 2 → D := ![x,x*y]

lemma coordinateSubstitution_hasSubst : HasSubst coordinateSubstitution := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [coordinateSubstitution,x,y]

def blowup : D →ₐ[ℂ] D := substAlgHom coordinateSubstitution_hasSubst

lemma substituted_monomial (d : Fin 2 →₀ ℕ) :
    d.prod (fun i n => coordinateSubstitution i ^ n) = x ^ (d 0 + d 1) * y ^ d 1 := by
  rw [Finsupp.prod_fintype _ _ (by simp),Fin.prod_univ_two]
  simp only [coordinateSubstitution,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,mul_pow,pow_add]
  ring

lemma exceptional_pow_dvd {k : ℕ} {f : D} (hf : f ∈ highOrder k) : x ^ k ∣ blowup f := by
  apply X_pow_dvd_iff.mpr
  intro e he
  rw [blowup,substAlgHom_apply]
  rw [coeff_subst coordinateSubstitution_hasSubst]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rw [substituted_monomial]
  by_cases hd : d 0 + d 1 < k
  · rw [(mem_highOrder.mp hf) d hd,zero_smul]
  · have hx : (x : D) ^ (d 0 + d 1) ∣ x ^ (d 0 + d 1) * y ^ d 1 := dvd_mul_right _ _
    have hc := X_pow_dvd_iff.mp hx e (he.trans_le (Nat.le_of_not_gt hd))
    rw [hc,smul_zero]

 
def transform (k : ℕ) : (highOrder k).restrictScalars ℂ →ₗ[ℂ] D where
  toFun f := (exceptional_pow_dvd f.property).choose
  map_add' f g := by
    apply mul_left_cancel₀ (pow_ne_zero _ x_ne_zero)
    rw [← (exceptional_pow_dvd (f+g).property).choose_spec,mul_add,
      ← (exceptional_pow_dvd f.property).choose_spec,
      ← (exceptional_pow_dvd g.property).choose_spec]
    exact map_add blowup (f : D) (g : D)
  map_smul' c f := by
    apply mul_left_cancel₀ (pow_ne_zero _ x_ne_zero)
    rw [mul_smul_comm,← (exceptional_pow_dvd (c • f).property).choose_spec,
      ← (exceptional_pow_dvd f.property).choose_spec]
    exact map_smul blowup c (f : D)

lemma exceptional_mul_transform (k : ℕ) (f : (highOrder k).restrictScalars ℂ) :
    x ^ k * transform k f = blowup f := (exceptional_pow_dvd f.property).choose_spec.symm

lemma transform_mul (k : ℕ) (q : D) (f : (highOrder k).restrictScalars ℂ) :
    transform k ⟨q*f, (highOrder k).mul_mem_left q f.property⟩ = blowup q * transform k f := by
  apply mul_left_cancel₀ (pow_ne_zero _ x_ne_zero)
  rw [exceptional_mul_transform]
  calc blowup (q * f) = blowup q * blowup f := map_mul blowup _ _
    _ = x^k * (blowup q * transform k f) := by rw [← exceptional_mul_transform]; ring

def exp (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

@[simp] lemma exp_zero (a b : ℕ) : exp a b 0 = a := by simp [exp]
@[simp] lemma exp_one (a b : ℕ) : exp a b 1 = b := by simp [exp]

lemma variable_monomial (a b : ℕ) : (x : D)^a * y^b = monomial (exp a b) 1 := by
  rw [X_pow_eq,X_pow_eq,monomial_mul_monomial]
  simp [exp]


lemma monomial_mem_highOrder (k a b : ℕ) (h : k ≤ a+b) :
    (x:D)^a*y^b ∈ highOrder k := by
  change (k : ℕ∞) ≤ _
  rw [variable_monomial,order_monomial_of_ne_zero one_ne_zero]
  exact_mod_cast (show k ≤ (exp a b).degree by simpa [Finsupp.degree_eq_sum,Fin.sum_univ_two] using h)

@[simp] lemma blowup_x : blowup x = x := by
  change substAlgHom coordinateSubstitution_hasSubst (X 0) = _
  rw [substAlgHom_X]
  rfl

@[simp] lemma blowup_y : blowup y = x*y := by
  change substAlgHom coordinateSubstitution_hasSubst (X 1) = _
  rw [substAlgHom_X]
  rfl


def yEmbedding : Unit ↪ Fin 2 := ⟨fun _ => 1,Function.injective_of_subsingleton _⟩
def row : D →ₐ[ℂ] PowerSeries ℂ := killCompl yEmbedding
def insertRow : PowerSeries ℂ →ₐ[ℂ] D := rename yEmbedding

@[simp] lemma insertRow_X : insertRow PowerSeries.X = y := by
  exact rename_X yEmbedding ()



def transformIdeal (I : Ideal D) (k : ℕ) (hI : I ≤ highOrder k) : Ideal D :=
  Ideal.span (Set.range (fun f : I => transform k ⟨f,hI f.property⟩))



abbrev B := MvPolynomial (Fin 2) ℂ

def polynomialTransform (k : ℕ) (p : B) : B :=
  ∑ d ∈ p.support, MvPolynomial.monomial (exp (d 0+d 1-k) (d 1)) (p.coeff d)


def rectangleMap (A B : ℕ) : (Fin A × Fin B → ℂ) →ₗ[ℂ] D :=
  ∑ ab : Fin A × Fin B, (monomial (exp ab.1 ab.2)).comp (LinearMap.proj ab)


open MvPowerSeries

 

def shearCoordinates (c : ℂ) : Fin 2 → D := ![x,y + C c * x]

lemma shearCoordinates_hasSubst (c : ℂ) : HasSubst (shearCoordinates c) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [shearCoordinates,x,y]

def shear (c : ℂ) : D →ₐ[ℂ] D := substAlgHom (shearCoordinates_hasSubst c)

@[simp] lemma shear_x (c : ℂ) : shear c x = x := by
  simpa [shear,shearCoordinates,x] using substAlgHom_X (R := ℂ) (shearCoordinates_hasSubst c) 0

@[simp] lemma shear_y (c : ℂ) : shear c y = y + C c * x := by
  simpa [shear,shearCoordinates,y] using substAlgHom_X (R := ℂ) (shearCoordinates_hasSubst c) 1

@[simp] lemma shear_C (c a : ℂ) : shear c (C a) = C a := by
  simpa only [c_eq_algebraMap] using (shear c).commutes a

lemma shear_neg_shear (c : ℂ) (f : D) : shear (-c) (shear c f) = f := by
  simp only [shear,substAlgHom_apply]
  rw [subst_comp_subst_apply (shearCoordinates_hasSubst c) (shearCoordinates_hasSubst (-c))]
  have H : (fun i => subst (shearCoordinates (-c)) (shearCoordinates c i)) = X := by
    funext i
    rw [← substAlgHom_apply (R := ℂ) (shearCoordinates_hasSubst (-c))]
    change shear (-c) (shearCoordinates c i) = X i
    fin_cases i
    · simp [shearCoordinates,x]
    · change shear (-c) (y + C c * x) = y
      simp only [map_add,map_mul,shear_y,shear_C,shear_x,map_neg]
      change y + -(C c) * x + C c * x = y
      ring
  rw [H,← map_algebraMap_eq_subst_X]
  simp

 

def shearEquiv (c : ℂ) : D ≃ₐ[ℂ] D := AlgEquiv.ofAlgHom (shear c) (shear (-c))
  (by apply AlgHom.ext; intro f
      change shear c (shear (-c) f) = f
      simpa only [neg_neg] using shear_neg_shear (-c) f)
  (by apply AlgHom.ext; intro f; exact shear_neg_shear c f)

lemma order_le_shear (c : ℂ) (f : D) : f.order ≤ (shear c f).order := by
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (shearCoordinates c i).order := by
    apply le_iInf
    intro i
    rw [one_le_order_iff_constCoeff_eq_zero]
    fin_cases i <;> simp [shearCoordinates,x,y]
  calc
    f.order = 1 * f.order := (one_mul _).symm
    _ ≤ (⨅ i, (shearCoordinates c i).order) * f.order := mul_le_mul h1 le_rfl bot_le bot_le
    _ ≤ (shear c f).order := by simpa only [shear,substAlgHom_apply] using le_order_subst (shearCoordinates_hasSubst c) f

lemma order_shear (c : ℂ) (f : D) : (shear c f).order = f.order := by
  apply le_antisymm
  · have H := order_le_shear (-c) (shear c f)
    rwa [shear_neg_shear] at H
  · exact order_le_shear c f

lemma shear_mem_highOrder_iff (c : ℂ) (f : D) (k : ℕ) :
    shear c f ∈ highOrder k ↔ f ∈ highOrder k := by
  change ((k : ℕ∞) ≤ (shear c f).order) ↔ (k : ℕ∞) ≤ f.order
  rw [order_shear]

def shearIdeal (I : Ideal D) (c : ℂ) : Ideal D := I.map (shear c).toRingHom

def shearQuotientEquiv (I : Ideal D) (c : ℂ) :
    (D ⧸ I) ≃ₐ[ℂ] D ⧸ shearIdeal I c :=
  Ideal.quotientEquivAlg I (shearIdeal I c) (shearEquiv c) rfl

end SplitTangent.FormalBlowup

namespace SplitTangent.PolynomialBlowup
open FormalBlowup

abbrev P := MvPolynomial (Fin 2) ℂ

def embed : P →ₐ[ℂ] D where
  toRingHom := MvPolynomial.coeToMvPowerSeries.ringHom
  commutes' a := by
    change ((MvPolynomial.C a : P) : D) = _
    rw [MvPolynomial.coe_C, ← MvPowerSeries.c_eq_algebraMap]

@[simp] lemma embed_apply (p : P) : embed p = (p : D) := rfl
@[simp] lemma embed_X (i : Fin 2) : embed (MvPolynomial.X i) = MvPowerSeries.X i := by simp
@[simp] lemma embed_C (a : ℂ) : embed (MvPolynomial.C a) = MvPowerSeries.C a := by
  change ((MvPolynomial.C a : P) : D) = _
  exact MvPolynomial.coe_C a

def shift (a : ℂ × ℂ) : P →ₐ[ℂ] P :=
  MvPolynomial.aeval ![MvPolynomial.X 0 + MvPolynomial.C a.1,
    MvPolynomial.X 1 + MvPolynomial.C a.2]

def shear (c : ℂ) : P →ₐ[ℂ] P :=
  MvPolynomial.aeval ![MvPolynomial.X 0,MvPolynomial.X 1 + MvPolynomial.C c * MvPolynomial.X 0]

def blowup : P →ₐ[ℂ] P :=
  MvPolynomial.aeval ![MvPolynomial.X 0,MvPolynomial.X 0 * MvPolynomial.X 1]

@[simp] lemma shift_X₀ (a : ℂ × ℂ) : shift a (MvPolynomial.X 0) = MvPolynomial.X 0 + MvPolynomial.C a.1 := by simp [shift]
@[simp] lemma shift_X₁ (a : ℂ × ℂ) : shift a (MvPolynomial.X 1) = MvPolynomial.X 1 + MvPolynomial.C a.2 := by simp [shift]
@[simp] lemma shear_X₀ (c : ℂ) : shear c (MvPolynomial.X 0) = MvPolynomial.X 0 := by simp [shear]
@[simp] lemma shear_X₁ (c : ℂ) : shear c (MvPolynomial.X 1) = MvPolynomial.X 1 + MvPolynomial.C c * MvPolynomial.X 0 := by simp [shear]
@[simp] lemma blowup_X₀ : blowup (MvPolynomial.X 0) = MvPolynomial.X 0 := by simp [blowup]
@[simp] lemma blowup_X₁ : blowup (MvPolynomial.X 1) = MvPolynomial.X 0 * MvPolynomial.X 1 := by simp [blowup]
@[simp] lemma shift_C (a : ℂ × ℂ) (b : ℂ) : shift a (MvPolynomial.C b) = MvPolynomial.C b := (shift a).commutes b
@[simp] lemma shear_C (c b : ℂ) : shear c (MvPolynomial.C b) = MvPolynomial.C b := (shear c).commutes b
@[simp] lemma blowup_C (c : ℂ) : blowup (MvPolynomial.C c) = MvPolynomial.C c := blowup.commutes c

def baseIdeal {ι : Type*} (p : ι → P) : Ideal D :=
  Ideal.span (Set.range (fun i => embed (p i)))

def transformPreimage (k : ℕ) (J : Ideal D) : Ideal D where
  carrier := {f | ∃ hf : f ∈ highOrder k, transform k ⟨f,hf⟩ ∈ J}
  zero_mem' := ⟨(highOrder k).zero_mem, by
    change transform k 0 ∈ J
    rw [map_zero]
    exact J.zero_mem⟩
  add_mem' := by
    rintro a b ⟨ha,hta⟩ ⟨hb,htb⟩
    refine ⟨(highOrder k).add_mem ha hb,?_⟩
    have h : transform k ⟨a+b,(highOrder k).add_mem ha hb⟩ =
        transform k ⟨a,ha⟩ + transform k ⟨b,hb⟩ := (transform k).map_add ⟨a,ha⟩ ⟨b,hb⟩
    rw [h]
    exact J.add_mem hta htb
  smul_mem' := by
    rintro a b ⟨hb,htb⟩
    refine ⟨(highOrder k).mul_mem_left a hb,?_⟩
    change transform k ⟨a*b,(highOrder k).mul_mem_left a hb⟩ ∈ J
    exact (transform_mul k a ⟨b,hb⟩).symm ▸ J.mul_mem_left _ htb

end SplitTangent.PolynomialBlowup

namespace SplitTangent.FormalBlowup

lemma shearIdeal_le_highOrder (I : Ideal D) (k : ℕ) (hI : I ≤ highOrder k) (c : ℂ) :
    shearIdeal I c ≤ highOrder k := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro f hf
  exact (shear_mem_highOrder_iff c f k).mpr (hI hf)

def swapCoordinates : Fin 2 → D := ![y,x]
lemma swapCoordinates_hasSubst : HasSubst swapCoordinates := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [swapCoordinates,x,y]
def swap : D →ₐ[ℂ] D := substAlgHom swapCoordinates_hasSubst
@[simp] lemma swap_x : swap x = y := by
  change substAlgHom swapCoordinates_hasSubst (X 0) = _
  rw [substAlgHom_X]
  rfl
@[simp] lemma swap_y : swap y = x := by
  change substAlgHom swapCoordinates_hasSubst (X 1) = _
  rw [substAlgHom_X]
  rfl
@[simp] lemma swap_C (a : ℂ) : swap (C a) = C a := by
  simpa only [c_eq_algebraMap] using swap.commutes a
lemma swap_swap (f : D) : swap (swap f) = f := by
  simp only [swap,substAlgHom_apply]
  rw [subst_comp_subst_apply swapCoordinates_hasSubst swapCoordinates_hasSubst]
  have H : (fun i => subst swapCoordinates (swapCoordinates i)) = X := by
    funext i
    rw [← substAlgHom_apply (R := ℂ) swapCoordinates_hasSubst]
    change swap (swapCoordinates i) = X i
    fin_cases i
    · exact swap_y
    · exact swap_x
  rw [H,← map_algebraMap_eq_subst_X]
  simp

def swapEquiv : D ≃ₐ[ℂ] D := AlgEquiv.ofAlgHom swap swap
  (by apply AlgHom.ext; intro f; exact swap_swap f)
  (by apply AlgHom.ext; intro f; exact swap_swap f)
def swapIdeal (I : Ideal D) : Ideal D := I.map swap.toRingHom
def swapQuotientEquiv (I : Ideal D) : (D ⧸ I) ≃ₐ[ℂ] D ⧸ swapIdeal I :=
  Ideal.quotientEquivAlg I (swapIdeal I) swapEquiv rfl

end SplitTangent.FormalBlowup

namespace SplitTangent.PolynomialBlowup
section
open FormalBlowup

def swap : P →ₐ[ℂ] P := MvPolynomial.aeval ![MvPolynomial.X 1,MvPolynomial.X 0]
@[simp] lemma swap_X₀ : swap (MvPolynomial.X 0) = MvPolynomial.X 1 := by simp [swap]
@[simp] lemma swap_X₁ : swap (MvPolynomial.X 1) = MvPolynomial.X 0 := by simp [swap]



def child {ι : Type*} (p : ι → P) (k : ℕ) (c : ℂ) : ι → P :=
  fun i => shift (0,c) (polynomialTransform k (p i))



def valueHom (w : ℂ × ℂ) : P →ₐ[ℂ] ℂ := MvPolynomial.aeval ![w.1,w.2]
def value (p : P) (w : ℂ × ℂ) : ℂ := valueHom w p
@[simp] lemma value_X₀ (w : ℂ × ℂ) : value (MvPolynomial.X 0) w = w.1 := by simp [value,valueHom]
@[simp] lemma value_X₁ (w : ℂ × ℂ) : value (MvPolynomial.X 1) w = w.2 := by simp [value,valueHom]
@[simp] lemma value_C (a : ℂ) (w : ℂ × ℂ) : value (MvPolynomial.C a) w = a := by simp [value,valueHom]

def constant : D →ₐ[ℂ] ℂ where
  toRingHom := MvPowerSeries.constantCoeff
  commutes' a := by simp [← MvPowerSeries.c_eq_algebraMap]



def linePolynomial : P →ₐ[ℂ] Polynomial ℂ := MvPolynomial.aeval ![0,Polynomial.X]

end

section
open FormalBlowup Filter Topology

def IsolatedAtOrigin {ι : Type*} (p : ι → P) : Prop :=
  ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), (∀ i, value (p i) w = 0) → w = 0

end

open FormalBlowup

end SplitTangent.PolynomialBlowup

open Filter Topology Set Metric
namespace SplitTangent.AffineBlowup

 
def first (w : ℂ × ℂ) : ℂ × ℂ := (w.1,w.1*w.2)
def second (w : ℂ × ℂ) : ℂ × ℂ := (w.1*w.2,w.1)

end SplitTangent.AffineBlowup

namespace SplitTangent.ProjectiveEmbedding
open Filter Topology
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)



def coneLift (x₀ : X.Carrier) (v : Fin (e.N+1) → ℂ) : X.Carrier := by
  classical
  exact if h : ∃ x, e.Incidence x v then Classical.choose h else x₀

lemma coneLift_incidence (x₀ : X.Carrier) {v : Fin (e.N+1) → ℂ}
    (h : ∃ x, e.Incidence x v) : e.Incidence (e.coneLift x₀ v) v := by
  simp only [coneLift,dite_eq_left h]
  exact Classical.choose_spec h

end SplitTangent.ProjectiveEmbedding

namespace SplitTangent.BasePointRemoval
open Filter Topology Set
open PolynomialBlowup
open FormalBlowup (D highOrder polynomialTransform)
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X) (S : TangentSplitting X)

def tuple (p : Fin (e.N+1) → P) (w : ℂ × ℂ) : Fin (e.N+1) → ℂ := fun i => value (p i) w

def lift (x₀ : X.Carrier) (p : Fin (e.N+1) → P) : ℂ × ℂ → X.Carrier :=
  fun w => e.coneLift x₀ (tuple e p w)



def Admissible (x₀ : X.Carrier) (p : Fin (e.N+1) → P) (A B : P) : Prop :=
  (∀ᶠ w in 𝓝 (0 : ℂ × ℂ), ∃ x, e.Incidence x (tuple e p w)) ∧
  (∀ᶠ w in 𝓝 (0 : ℂ × ℂ), tuple e p w ≠ 0 →
    S.WedgeAt (lift e x₀ p) (value A) w ∧ S.swap.WedgeAt (lift e x₀ p) (value B) w)

end SplitTangent.BasePointRemoval

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.OpenManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Open Manifold. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u
namespace SplitTangent
namespace OpenManifold
variable {d : ℕ} (U : Set (Fin d → ℂ)) (hU : IsOpen U) (hne : U.Nonempty)

abbrev Carrier := ULift.{u} U
include hne in
theorem nonempty : Nonempty (Carrier.{u} U) := ⟨⟨⟨hne.choose,hne.choose_spec⟩⟩⟩
def val (x : Carrier.{u} U) : Fin d → ℂ := x.down.val
include hU in
lemma isOpenEmbedding_val : IsOpenEmbedding (val (U := U) : Carrier.{u} U → _) :=
  hU.isOpenEmbedding_subtypeVal.comp Homeomorph.ulift.isOpenEmbedding

def manifold : ComplexManifold.{u} where
  dim := d
  Carrier := Carrier.{u} U
  charts := by
    letI := nonempty U hne
    exact (isOpenEmbedding_val U hU).singletonChartedSpace
  secondCountable := Homeomorph.ulift.isInducing.secondCountableTopology
  holomorphicAtlas := by
    let := nonempty U hne
    exact (isOpenEmbedding_val U hU).isManifold_singleton

lemma val_holomorphic : ContMDiff (ModelWithCorners (manifold.{u} U hU hne))
    𝓘(ℂ, Fin d → ℂ) ω (fun x : (manifold.{u} U hU hne).Carrier => val U x) := by
  let := nonempty U hne
  exact contMDiff_isOpenEmbedding (isOpenEmbedding_val U hU)

end OpenManifold
end SplitTangent

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.RationalFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Families. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover
abbrev Space (n : ℕ) := Fin n → ℂ

 
structure Patch (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  dim : ℕ
  domain : Set (Space dim)
  isOpen_domain : IsOpen domain
  preconnected_domain : IsPreconnected domain
  map : Space dim → E
  analytic : AnalyticOnNhd ℂ map domain

def Patch.image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (P : Patch E) : Set E :=
  P.map '' P.domain



end AnalyticZeroCover

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

open Set Filter Topology
open scoped ContDiff

open Filter Topology Set
open scoped ContDiff

open Filter Topology Set

open scoped Manifold LinearAlgebra.Projectivization
open Bundle

open Filter Topology


open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle Filter Topology
namespace SplitTangent

 

namespace FormalCauchy

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

instance instCoeFunSubtypeForallComplexMemSubalgebraAnalyticFunction_1 (U : Set ℂ) : CoeFun (AnalyticFunction U) (fun _ => ℂ → ℂ) := ⟨Subtype.val⟩

open scoped MvPowerSeries.WithPiTopology

end FormalCauchy
end SplitTangent

open Set Filter Topology

open Filter Topology

open Filter Topology

open Filter Topology Metric Set

 

open MvPowerSeries

open Filter Topology Set Metric

 

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]


def coeffDerivative {d : ℕ} (f : Space d → ℂ) (n : ℕ) (k : Fin n → Fin d) :
    Space d → ℂ := fun x => iteratedFDeriv ℂ n f x (fun i => Pi.single (k i) 1)

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff



open Set Filter Topology
open scoped ContDiff



open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover

 

structure AnalyticSetOn {d : ℕ} (U A : Set (Space d)) : Prop where
  subset : A ⊆ U
  closed : closure A ∩ U ⊆ A
  local_equations : ∀ x∈A, ∃ V : Set (Space d), IsOpen V ∧ x∈V ∧ V ⊆ U ∧
    ∃ F : Set (Space d → ℂ), (∀ f∈F, AnalyticOnNhd ℂ f V) ∧
      ∀ y∈V, y∈A ↔ ∀ f∈F, f y=0


end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 
def Patch.comp (P : Patch E) (Q : Patch (Space P.dim)) (h : Q.image ⊆ P.domain) : Patch E where
  dim := Q.dim
  domain := Q.domain
  isOpen_domain := Q.isOpen_domain
  preconnected_domain := Q.preconnected_domain
  map := P.map ∘ Q.map
  analytic z hz := (P.analytic _ (h ⟨z,hz,rfl⟩)).comp (Q.analytic z hz)

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators



open Set Filter Topology
open scoped ContDiff Manifold



open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff


 

open Set Filter Topology
open scoped ContDiff




open Set Filter Topology
open scoped ContDiff
namespace AnalyticZeroCover

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

 
def pivot {r : ℕ} (f : E → F) (p : F →L[ℂ] Space r) (s : Space r →L[ℂ] E) (x : E) : ℂ :=
  LinearMap.det ((p.comp (fderiv ℂ f x)).comp s).toLinearMap

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff ENNReal



open Set Filter Topology
open scoped ContDiff ENNReal



open Set Filter Topology IsManifold
open scoped ContDiff Manifold

 

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

end

end OAI
end


