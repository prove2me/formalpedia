-- Prove2me | Definitions.Def_OAIQWUFI005
-- name    : OAIQWUFI005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:46:03.62007+00:00
-- url     : https://prove2.me/theorems/35f963f9-c82a-4ac0-b267-068e7c3d7cd9
-- title:
--   OpenAI universal F∞ group split: definitions bundle 6 of 9
-- statement:
--   Definitions bundle 6 of 9 of the split of OpenAI's proof that a single group of type $F_\infty$ contains every finitely presented group (OpenAI, *A universal group of type F∞*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0). It holds OpenAI's Lean definitions, structures and instances from the modules listed below, ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas those definitions use in their bodies: several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs.
--
--   It imports bundles 2–4 of this split (`OAIQWUFI001`–`OAIQWUFI003`).
--
--   Modules: `BrownConstruction.lean`, `Cayley.lean`, `CellularApproximation.lean`, `CellularChains.lean`, `CellularLifting.lean`, `ControlledCells.lean`, `Cylinders.lean`, `FiniteEnvelopes.lean`, `GeneralPosition.lean`, `GraphActions.lean`, `GraphBundles.lean`, `HomotopyProducts.lean`, `Idempotents.lean`, `MatrixDiagrams.lean`, `Milnor.lean`, `MilnorControl.lean`, `MilnorProducts.lean`, `PathExtensions.lean`, `Simplicial.lean`, `SimplicialProducts.lean`, `SphereHomotopies.lean`, `TopologicalTowers.lean`, `TorusBundles.lean`, `TorusHomotopies.lean`, `TorusSpheres.lean`, `TowerCoverings.lean`, `TreeGeometry.lean`, `UniversalPresentation.lean`, `UniverseTransport.lean`.
--
--   The theorems the definitions do not need are proved in the solutions of this split. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/UniversalGroup at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWUFI001
import Definitions.Def_OAIQWUFI002
import Definitions.Def_OAIQWUFI003

section
-- module Solutions.OAIQW_UniversalFInfinity.UniversalPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x
noncomputable section

namespace UniversalFInfinity.ThreePresentation
open Monoid

abbrev Alphabet := Bool ⊕ Unit
abbrev Words := FreeGroup Alphabet

def A : Words := FreeGroup.of (Sum.inl false)
def P : Words := FreeGroup.of (Sum.inl true)
def T : Words := FreeGroup.of (Sum.inr ())
def conjugate (i : ℕ) : Words := A ^ i * P * (A ^ i)⁻¹
def substitute : FreeGroup ℕ →* Words :=
  FreeGroup.lift (fun i => T * conjugate i * T⁻¹ * (conjugate i)⁻¹)

variable (rels : Set (FreeGroup ℕ))
abbrev C := PresentedGroup rels
abbrev Q := PresentedGroup (substitute '' rels)

def fromC : C rels →* Q rels :=
  PresentedGroup.map substitute (fun _ hr => ⟨_,hr,rfl⟩)

end UniversalFInfinity.ThreePresentation

namespace UniversalFInfinity.RecursiveUniversal

abbrev Word := List (ℕ × Bool)
abbrev Code := List Word

def relations (P : Code) : Set (FreeGroup ℕ) := FreeGroup.mk '' {w | w ∈ P}
def rawAt (m j : ℕ) : Word := ((Encodable.decode (α := Code) m).getD []).getD j []
def colour (m : ℕ) (w : Word) : Word := w.map (fun x => (Nat.pair m x.1,x.2))
def relator (k : ℕ) : Word := colour k.unpair.1 (rawAt k.unpair.1 k.unpair.2)
def allRelations : Set (FreeGroup ℕ) := Set.range (fun k => FreeGroup.mk (relator k))
abbrev Universal := PresentedGroup allRelations

lemma raw_relation (P : Code) (j : ℕ) :
    PresentedGroup.mk (relations P) (FreeGroup.mk (P.getD j [])) = 1 := by
  simp only [List.getD_eq_getElem?_getD]
  cases hj : P[j]? with
  | none => change (PresentedGroup.mk (relations P)) 1 = 1; exact map_one _
  | some w =>
    simp only [Option.getD_some]
    exact PresentedGroup.one_of_mem ⟨w,List.mem_of_getElem? hj,rfl⟩

def rename {α β : Type*} (i : α ↪ β) (s : Set (FreeGroup α)) :
    PresentedGroup s →* PresentedGroup (FreeGroup.map i '' s) :=
  PresentedGroup.map (FreeGroup.map i) (fun _ hr => ⟨_,hr,rfl⟩)

noncomputable def renameValues {α β : Type*} (i : α ↪ β) (s : Set (FreeGroup α)) :
    β → PresentedGroup s := Function.extend i PresentedGroup.of (fun _ => 1)

lemma renameValues_comp {α β : Type*} (i : α ↪ β) (s : Set (FreeGroup α)) :
    (FreeGroup.lift (renameValues i s)).comp (FreeGroup.map i) = PresentedGroup.mk s := by
  apply FreeGroup.ext_hom
  intro a
  simp [renameValues,i.injective.extend_apply,PresentedGroup.of]

noncomputable def renameRetract {α β : Type*} (i : α ↪ β) (s : Set (FreeGroup α)) :
    PresentedGroup (FreeGroup.map i '' s) →* PresentedGroup s :=
  PresentedGroup.toGroup (by
    rintro _ ⟨r,hr,rfl⟩
    change ((FreeGroup.lift (renameValues i s)).comp (FreeGroup.map i)) r = 1
    rw [renameValues_comp]
    exact PresentedGroup.one_of_mem hr)

end UniversalFInfinity.RecursiveUniversal

namespace UniversalFInfinity.RecursiveUniversalThree
open ThreePresentation
abbrev Raw := List (Alphabet × Bool)

def positive (i : ℕ) : Raw := List.replicate i (Sum.inl false,true)
def v (i : ℕ) : Raw := positive i ++ [(Sum.inl true,true)] ++ FreeGroup.invRev (positive i)
def replacement (i : ℕ) : Raw :=
  [(Sum.inr (),true)] ++ v i ++ [(Sum.inr (),false)] ++ FreeGroup.invRev (v i)
def substituteRaw (w : RecursiveUniversal.Word) : Raw :=
  w.flatMap (fun x => if x.2 then replacement x.1 else FreeGroup.invRev (replacement x.1))
def enumerator (k : ℕ) : Raw := substituteRaw (RecursiveUniversal.relator k)

abbrev Universal := PresentedGroup (Set.range (fun k => FreeGroup.mk (enumerator k)))

end UniversalFInfinity.RecursiveUniversalThree

end
end UniversalFinitelyPresentedProof

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Simplicial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators

namespace UniversalFInfinity.Simplicial

section
universe u v
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

lemma continuous_eval (v : V) : Continuous (fun x : Space K => x.1 v) := by
  classical
  rw [continuous_iff]
  intro s
  by_cases hv : v ∈ s.1
  · have he : (fun x : Space K => x.1 v) ∘ faceMap K s = (fun x : SimplexDisk.Simplex s.1 => x.1 ⟨v,hv⟩) := by
      funext x
      exact weight_apply s.1 x ⟨v,hv⟩
    rw [he]
    exact (continuous_apply (⟨v,hv⟩ : s.1)).comp continuous_subtype_val
  · have he : (fun x : Space K => x.1 v) ∘ faceMap K s = (fun _ => (0:ℝ)) := by
      funext x
      exact weight_apply_not _ _ hv
    rw [he]
    exact continuous_const

instance instT2SpaceElemFinsuppRealSpace : T2Space (Space K) :=
  T2Space.of_injective_continuous (f := fun x : Space K => (x.1 : V → ℝ))
    (fun _ _ h => Subtype.ext (Finsupp.ext fun v => congrFun h v))
    (continuous_pi fun v => continuous_eval K v)

lemma isClosed_iff (A : Set (Space K)) :
    IsClosed A ↔ ∀ s : Face K, IsClosed ((faceMap K s) ⁻¹' A) := by
  rw [isClosed_coinduced]
  exact isClosed_sigma_iff

end

section
open Set Metric Topology BigOperators
open scoped Classical
universe u v w
variable {V : Type u} {W : Type v} {T : Type w}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)

lemma push_apply (f : V → W) (w : V →₀ ℝ) (s : Finset V) (hs : w.support ⊆ s) (b : W) :
    (w.mapDomain f) b = ∑ a ∈ s, if f a = b then w a else 0 := by
  classical
  rw [Finsupp.mapDomain,Finsupp.sum_apply]
  rw [w.sum_of_support_subset hs]
  · apply Finset.sum_congr rfl
    intro a _
    simp only [Finsupp.single_apply]
  · intro a _
    simp

lemma push_nonneg (f : V → W) (w : V →₀ ℝ) (hw : ∀ v, 0 ≤ w v) (b : W) :
    0 ≤ (w.mapDomain f) b := by
  classical
  rw [push_apply f w w.support (Finset.Subset.refl _) b]
  exact Finset.sum_nonneg fun a _ => by split; exact hw a; exact le_rfl

lemma push_sum (f : V → W) (w : V →₀ ℝ) :
    (w.mapDomain f).sum (fun _ r => r) = w.sum (fun _ r => r) :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

def map (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) (x : Space K) : Space L := by
  classical
  refine ⟨x.1.mapDomain f,push_nonneg f x.1 x.2.1,?_,?_⟩
  · rw [push_sum]; exact x.2.2.1
  · exact L.isRelLowerSet_faces.mem_of_le (hf ⟨x.1.support,x.2.2.2⟩) Finsupp.mapDomain_support
      (support_nonempty (by rw [push_sum]; exact x.2.2.1))

lemma map_support (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) (x : Space K) :
    (map K L f hf x).1.support ⊆ x.1.support.image f := by
  classical
  exact Finsupp.mapDomain_support

lemma map_comp {U : Type*} (M : PreAbstractSimplicialComplex U)
    (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L)
    (g : W → U) (hg : ∀ s : Face L, s.1.image g ∈ M)
    (hgf : ∀ s : Face K, s.1.image (g ∘ f) ∈ M) (x : Space K) :
    map L M g hg (map K L f hf x) = map K M (g ∘ f) hgf x := by
  apply Subtype.ext
  exact Finsupp.mapDomain_comp.symm

end

section
open Set Metric Topology BigOperators
open scoped Classical unitInterval
universe u v
variable {V : Type u} {W : Type v}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)

def mass : (V →₀ ℝ) →ₗ[ℝ] ℝ := Finsupp.lsum ℝ fun _ => LinearMap.id
lemma mass_apply (w : V →₀ ℝ) : mass w = w.sum (fun _ r => r) := rfl

lemma blend_support (x y : V →₀ ℝ) (t : I) :
    ((1-(t:ℝ)) • x + (t:ℝ) • y).support ⊆ x.support ∪ y.support :=
  Finsupp.support_add.trans (Finset.union_subset_union Finsupp.support_smul Finsupp.support_smul)

def blend (s : Face K) (x y : Space K) (hx : x.1.support ⊆ s.1) (hy : y.1.support ⊆ s.1) (t : I) : Space K := by
  let w := (1-(t:ℝ)) • x.1 + (t:ℝ) • y.1
  have hw : w.sum (fun _ r => r) = 1 := by
    rw [← mass_apply]
    simp only [w,map_add,map_smul,mass_apply,x.2.2.1,y.2.2.1,smul_eq_mul,mul_one]
    ring
  refine ⟨w,?_,hw,?_⟩
  · intro v
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (x.2.1 v)) (mul_nonneg t.2.1 (y.2.1 v))
  · exact K.isRelLowerSet_faces.mem_of_le s.2
      ((blend_support x.1 y.1 t).trans (Finset.union_subset hx hy)) (support_nonempty hw)

lemma blend_zero (s : Face K) (x y : Space K) (hx : x.1.support ⊆ s.1) (hy : y.1.support ⊆ s.1) :
    blend K s x y hx hy 0 = x := by
  apply Subtype.ext
  simp [blend]
lemma blend_one (s : Face K) (x y : Space K) (hx : x.1.support ⊆ s.1) (hy : y.1.support ⊆ s.1) :
    blend K s x y hx hy 1 = y := by
  apply Subtype.ext
  simp [blend]

variable (f g : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) (hg : ∀ s : Face K, s.1.image g ∈ L)
variable (hfg : ∀ s : Face K, s.1.image f ∪ s.1.image g ∈ L)

def straight (t : I) (x : Space K) : Space L :=
  blend L ⟨x.1.support.image f ∪ x.1.support.image g,hfg ⟨x.1.support,x.2.2.2⟩⟩
    (map K L f hf x) (map K L g hg x)
    ((map_support K L f hf x).trans Finset.subset_union_left)
    ((map_support K L g hg x).trans Finset.subset_union_right) t

end
open Set Metric Topology BigOperators
open scoped Classical
universe u
variable {V : Type u} (K L : PreAbstractSimplicialComplex V) (hKL : ∀ s ∈ K, s ∈ L)

lemma inclusion_injective : Function.Injective (inclusion K L hKL) :=
  fun _ _ h => Subtype.ext (congrArg (fun z : Space L => z.1) h)

end UniversalFInfinity.Simplicial

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Milnor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators

namespace UniversalFInfinity.Milnor
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v
local instance (priority := 2000) instDecidableEq_solutions (α : Type*) : DecidableEq α := Classical.decEq α
variable (G : Type u)

def bounded (N : ℕ) : PreAbstractSimplicialComplex (ℕ × G) where
  faces := {s | s ∈ complex G ∧ ∀ v ∈ s, v.1 < N}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1.1,fun t hts ht => ⟨(complex G).isRelLowerSet_faces.mem_of_le hs.1 hts ht,
      fun v hv => hs.2 v (hts hv)⟩⟩

lemma bounded_le (N : ℕ) : bounded G N ≤ complex G := fun _ hs => hs.1

variable {G} {H : Type v}
lemma map_face (φ : G → H) (ρ : ℕ → ℕ) (hρ : Function.Injective ρ)
    (s : Face (complex G)) : s.1.image (fun v => (ρ v.1,φ v.2)) ∈ complex H := by
  refine ⟨s.2.1.image _,?_⟩
  rintro a ha b hb hab
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
  exact congrArg (fun v : ℕ × G => (ρ v.1,φ v.2)) (s.2.2 hx hy (hρ hab))

def vertex (v : ℕ × G) : Space G :=
  ⟨Finsupp.single v 1,by intro w; simp only [Finsupp.single_apply]; split_ifs <;> norm_num,
    by simp,by
      simp only [Finsupp.support_single _ one_ne_zero]
      exact ⟨Finset.singleton_nonempty v,by simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst v⟩⟩

lemma bounded_union_apex (N : ℕ) (g : G) (s : Face (bounded G N)) :
    s.1 ∪ {(N,g)} ∈ complex G := by
  refine ⟨s.2.1.1.mono Finset.subset_union_left,?_⟩
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact s.2.1.2 hx hy hxy
  · have hyy := Finset.mem_singleton.mp hy
    subst y
    exact False.elim ((Nat.ne_of_lt (s.2.2 x hx)) hxy)
  · have hxx := Finset.mem_singleton.mp hx
    subst x
    exact False.elim ((Nat.ne_of_lt (s.2.2 y hy)) hxy.symm)
  · exact (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm

lemma bounded_id_face (N : ℕ) (s : Face (bounded G N)) : s.1.image id ∈ complex G := by
  simpa only [Finset.image_id] using s.2.1
lemma bounded_const_face (N : ℕ) (g : G) (s : Face (bounded G N)) :
    s.1.image (fun _ => (N,g)) ∈ complex G := by
  rw [Finset.image_const s.2.1.1]
  exact ⟨Finset.singleton_nonempty _,by simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst (N,g)⟩
lemma bounded_contiguous (N : ℕ) (g : G) (s : Face (bounded G N)) :
    s.1.image id ∪ s.1.image (fun _ => (N,g)) ∈ complex G := by
  rw [Finset.image_id,Finset.image_const s.2.1.1]
  exact bounded_union_apex N g s

lemma bounded_map_id (N : ℕ) (x : Simplicial.Space (bounded G N)) :
    Simplicial.map (bounded G N) (complex G) id (bounded_id_face N) x =
      Simplicial.inclusion (bounded G N) (complex G) (fun _ h => bounded_le G N h) x := by
  apply Subtype.ext
  exact Finsupp.mapDomain_id

lemma map_const_vertex (K : PreAbstractSimplicialComplex (ℕ × G)) (v : ℕ × G)
    (hf : ∀ s : Face K, s.1.image (fun _ => v) ∈ complex G) (x : Simplicial.Space K) :
    Simplicial.map K (complex G) (fun _ => v) hf x = vertex v := by
  apply Subtype.ext
  change x.1.mapDomain (fun _ => v) = Finsupp.single v 1
  rw [Finsupp.mapDomain,← Finsupp.single_sum]
  exact congrArg (Finsupp.single v) x.2.2.1

end UniversalFInfinity.Milnor

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CellularLifting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology


namespace UniversalFInfinity.Cellular
universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

def DiskRLP {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) : Prop :=
  ∀ n (a : C(Sphere n,E)) (b : C(Disk n,B)),
    (∀ x, p (a x) = b (boundary n x)) →
    ∃ e : C(Disk n,E), (∀ x, e (boundary n x) = a x) ∧ ∀ x, p (e x) = b x

section Attach
variable {E : Type v} [TopologicalSpace E] {n : ℕ}

noncomputable def attachValue (a : X → E) (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (x : X) : E := by
  classical
  exact if x ∈ Skeleton C n then a x
    else if h : ∃ i : RelCWComplex.cell C n, x ∈ CWComplex.openCell n i then
      let i := h.choose
      let y := h.choose_spec.choose
      e i ⟨y,ball_subset_closedBall h.choose_spec.choose_spec.1⟩
    else a x

end Attach

namespace PartialLift
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
variable {p : C(E,B)} {f : C(X,B)} {n : ℕ}

noncomputable def zero [Nonempty E] : PartialLift (C := C) p f 0 where
  val := fun _ => Classical.choice ‹Nonempty E›
  continuousOn := continuous_const.continuousOn
  fac := by
    intro x hx
    simp only [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty,Set.mem_empty_iff_false] at hx

end PartialLift

section Lift
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B] [Nonempty E]
variable {p : C(E,B)} (hp : DiskRLP p) (f : C(X,B))

lemma exists_skeleton {x : X} (hx : x ∈ C) : ∃ n : ℕ, x ∈ Skeleton C n := by
  rw [← CWComplex.iUnion_skeletonLT_eq_complex (C := C)] at hx
  exact Set.mem_iUnion.mp hx

end Lift

end UniversalFInfinity.Cellular

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.MilnorControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Milnor

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v
variable {G : Type u}

local instance (priority := 2000) instDecidableEqProdNat_solutions_r879784_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
def boundedInclusion (N : ℕ) : C(Simplicial.Space (bounded G N),Space G) :=
  ⟨Simplicial.inclusion (bounded G N) (complex G) (fun _ h => bounded_le G N h),
    Simplicial.continuous_inclusion _ _ _⟩

end

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical
universe u v
variable {G : Type u} [Group G]
attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_1
lemma translate_mul (g h : G) (s : Finset (ℕ × G)) : translate g (translate h s) = translate (g*h) s := by
  simp only [translate,Finset.image_image,Function.comp_def,mul_assoc]
lemma translate_mono (g : G) {s t : Finset (ℕ × G)} (h : s ⊆ t) : translate g s ⊆ translate g t :=
  Finset.image_subset_image h
lemma translate_valid (g : G) {s : Finset (ℕ × G)} (hs : s ∈ complex G) : translate g s ∈ complex G :=
  map_face (g * ·) id Function.injective_id ⟨s,hs⟩

lemma orbitSpan_invariant (S : Finset (Finset (ℕ × G))) (g : G)
    {t : Finset (ℕ × G)} (ht : t ∈ orbitSpan S) : translate g t ∈ orbitSpan S := by
  obtain ⟨h,s,hs,hts⟩ := ht.2
  exact ⟨translate_valid g ht.1,g*h,s,hs,by rw [←translate_mul]; exact translate_mono g hts⟩

end
section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]
local instance (priority := 2000) instDecidableEqProdNat_solutions_2 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

def vertexMap (φ : G →* H) (α : ℕ → ℕ) : ℕ × G → ℕ × H := fun v => (α v.1,φ v.2)
def faceImage (φ : G →* H) (α : ℕ → ℕ) (s : Finset (ℕ × G)) : Finset (ℕ × H) := s.image (vertexMap φ α)
def imageShapes (φ : G →* H) (α : ℕ → ℕ) (S : Finset (Finset (ℕ × G))) : Finset (Finset (ℕ × H)) := S.image (faceImage φ α)

lemma faceImage_translate (φ : G →* H) (α : ℕ → ℕ) (a : G) (s : Finset (ℕ × G)) :
    faceImage φ α (translate a s) = translate (φ a) (faceImage φ α s) := by
  simp only [faceImage,translate,Finset.image_image,vertexMap,Function.comp_def,map_mul]

lemma faceImage_valid (φ : G →* H) (α : ℕ → ℕ) (hα : Function.Injective α)
    {s : Finset (ℕ × G)} (hs : s ∈ complex G) : faceImage φ α s ∈ complex H :=
  map_face φ α hα ⟨s,hs⟩

lemma faceImage_controlled (φ : G →* H) (α : ℕ → ℕ) (hα : Function.Injective α)
    (S : Finset (Finset (ℕ × G))) (s : Face (orbitSpan S)) :
    faceImage φ α s.1 ∈ orbitSpan (imageShapes φ α S) := by
  obtain ⟨a,t,ht,hst⟩ := s.2.2
  refine ⟨faceImage_valid φ α hα s.2.1,φ a,faceImage φ α t,
    Finset.mem_image.mpr ⟨t,ht,rfl⟩,?_⟩
  rw [← faceImage_translate]
  exact Finset.image_subset_image hst

lemma unionFace_valid (φ : G →* H) (α β : ℕ → ℕ)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    {s : Finset (ℕ × G)} (hs : s ∈ complex G)
    (hc : ∀ v ∈ s, ∀ w ∈ s, α v.1 = β w.1 → v.1 = w.1) :
    faceImage φ α s ∪ faceImage φ β s ∈ complex H := by
  refine ⟨(faceImage_valid φ α hα hs).1.mono Finset.subset_union_left,?_⟩
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact (faceImage_valid φ α hα hs).2 hx hy hxy
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    have hvw : v = w := hs.2 hv hw (hc v hv w hw hxy)
    subst w
    apply Prod.ext
    · exact hxy
    · rfl
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    have hvw : w = v := hs.2 hw hv (hc w hw v hv hxy.symm)
    subst w
    apply Prod.ext
    · exact hxy
    · rfl
  · exact (faceImage_valid φ β hβ hs).2 hx hy hxy

def unionShapes (φ : G →* H) (α β : ℕ → ℕ) (S : Finset (Finset (ℕ × G))) :
    Finset (Finset (ℕ × H)) := S.image (fun s => faceImage φ α s ∪ faceImage φ β s)

lemma translate_union (a : H) (s t : Finset (ℕ × H)) : translate a (s ∪ t) = translate a s ∪ translate a t :=
  Finset.image_union _ _

lemma unionFace_controlled (φ : G →* H) (α β : ℕ → ℕ)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (S : Finset (Finset (ℕ × G))) (s : Face (orbitSpan S))
    (hc : ∀ v ∈ s.1, ∀ w ∈ s.1, α v.1 = β w.1 → v.1 = w.1) :
    faceImage φ α s.1 ∪ faceImage φ β s.1 ∈ orbitSpan (unionShapes φ α β S) := by
  obtain ⟨a,t,ht,hst⟩ := s.2.2
  refine ⟨unionFace_valid φ α β hα hβ s.2.1 hc,φ a,faceImage φ α t ∪ faceImage φ β t,
    Finset.mem_image.mpr ⟨t,ht,rfl⟩,?_⟩
  rw [translate_union,←faceImage_translate,←faceImage_translate]
  exact Finset.union_subset_union (Finset.image_subset_image hst) (Finset.image_subset_image hst)

def fresh (N : ℕ) (i : ℕ) : ℕ := if i = 0 then 0 else N+i
lemma fresh_zero (N : ℕ) : fresh N 0 = 0 := by simp [fresh]
lemma fresh_injective (N : ℕ) : Function.Injective (fresh N) := by
  intro i j h
  unfold fresh at h
  split_ifs at h with hi hj hj
  · exact hi.trans hj.symm
  · exfalso; omega
  · exfalso; omega
  · omega

end
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]
local instance (priority := 2000) instDecidableEqProdNat_solutions_3 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

def shapeBound (S : Finset (Finset (ℕ × G))) (α : ℕ → ℕ) : ℕ :=
  (S.biUnion id).sup (fun v => α v.1) + 1
lemma orbit_below_bound (S : Finset (Finset (ℕ × G))) (α : ℕ → ℕ)
    (s : Face (orbitSpan S)) {v : ℕ × G} (hv : v ∈ s.1) : α v.1 < shapeBound S α := by
  obtain ⟨a,t,ht,hst⟩ := s.2.2
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp (hst hv)
  have hh : α w.1 ≤ (S.biUnion id).sup (fun v => α v.1) :=
    Finset.le_sup (f := fun v : ℕ × G => α v.1) (Finset.mem_biUnion.mpr ⟨t,ht,hw⟩)
  exact Nat.lt_succ_of_le hh

def relayerFresh (S : Finset (Finset (ℕ × G))) (α β : ℕ → ℕ) : ℕ → ℕ :=
  fresh (max (shapeBound S α) (shapeBound S β))
def relayerTarget (φ : G →* H) (S : Finset (Finset (ℕ × G))) (α β : ℕ → ℕ) :=
  unionShapes φ α (relayerFresh S α β) S ∪ unionShapes φ β (relayerFresh S α β) S

end UniversalFInfinity.Milnor

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.HomotopyProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Milnor

open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical
universe u v
variable (G : Type u) [Group G]
local instance (priority := 2000) instDecidableEqProdNat_solutions_6 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

lemma stage_translate (S : Shapes G) (g : G) (s : Face (stage G S)) :
    s.1.image (fun v => (v.1,g*v.2)) ∈ stage G S := orbitSpan_invariant _ g s.2

end UniversalFInfinity.Milnor

open Set Metric Topology

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Cayley
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.PathSquares
open Set
open scoped unitInterval
variable {X : Type*} [TopologicalSpace X] {x a b : X}

lemma turn (p : Path x a) (q : Path x b) (e : Path a b)
    (h : (p.trans e).Homotopic q) : e.Homotopic (p.symm.trans q) := by
  apply (Path.Homotopic.refl_trans e).symm.trans
  apply ((Path.Homotopic.symm_trans p).symm.hcomp (Path.Homotopic.refl e)).trans
  exact (Path.Homotopic.trans_assoc p.symm p e).trans ((Path.Homotopic.refl p.symm).hcomp h)

def spanContract (p : Path x a) (q : Path x b) :
    (p.symm.trans q).toContinuousMap.Homotopy (.const _ x) where
  toFun z := if (z.2 : ℝ) ≤ 1/2 then p.extend ((1-z.1)*(1-2*z.2))
    else q.extend ((1-z.1)*(2*z.2-1))
  continuous_toFun := continuous_if_le (by fun_prop) continuous_const
    (by fun_prop) (by fun_prop) (by intro z hz; simp [hz])
  map_zero_left z := by simp [Path.trans,Path.extend_symm_apply]
  map_one_left z := by simp

lemma spanContract_source (p : Path x a) (q : Path x b) (t : I) :
    spanContract p q (t,0) = p.symm t := by
  change (if (0 : ℝ) ≤ 1/2 then p.extend ((1-(t:ℝ))*(1-2*0)) else q.extend ((1-(t:ℝ))*(2*0-1))) = _
  norm_num only [show (0:ℝ)≤1/2 by norm_num,ite_true,mul_zero,sub_zero,mul_one]
  rw [← Path.extend_symm_apply,Path.extend_extends' ]
lemma spanContract_target (p : Path x a) (q : Path x b) (t : I) :
    spanContract p q (t,1) = q.symm t := by
  change (if (1 : ℝ) ≤ 1/2 then p.extend ((1-(t:ℝ))*(1-2*1)) else q.extend ((1-(t:ℝ))*(2*1-1))) = _
  norm_num only [mul_one,show (2:ℝ)-1=1 by norm_num,show ¬(1:ℝ)≤1/2 by norm_num,ite_false]
  rw [← Path.extend_symm_apply,Path.extend_extends' ]

def pauseReverse (p : Path x a) : C(I,X) := ((Path.refl a).trans p.symm).toContinuousMap

end UniversalFInfinity.PathSquares
open Set Metric Topology

namespace UniversalFInfinity.LoopSphere
open Set Metric Topology Cellular
open scoped unitInterval
universe u v
variable {X : Type u} [TopologicalSpace X] {x : X}

def sides : C(Sphere 1,C(I,X)) := .const _ (.const _ x)
end UniversalFInfinity.LoopSphere

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.PathExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.PathExtension

section
open Path.Homotopic
universe u v
variable {X : Type u} [TopologicalSpace X]

namespace Q
variable {x y z : X}
lemma map_trans {Y : Type*} [TopologicalSpace Y]
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z) (f : C(X,Y)) :
    (p.trans q).map f = (p.map f).trans (q.map f) := by
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  induction q using Path.Homotopic.Quotient.ind with | mk q =>
  exact congrArg Path.Homotopic.Quotient.mk (p.map_trans q f.continuous)
lemma map_refl {Y : Type*} [TopologicalSpace Y] (x : X) (f : C(X,Y)) :
    (Path.Homotopic.Quotient.refl x).map f = Path.Homotopic.Quotient.refl (f x) := rfl

end Q

variable {G : Type v} [Group G] [MulAction G X] [ContinuousConstSMul G X]

def smulMap (g : G) : C(X,X) := ⟨fun x => g • x,continuous_const_smul g⟩

end
open Path.Homotopic
universe u v w
end UniversalFInfinity.PathExtension

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.GeneralPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal

open Set Metric Topology
open scoped NNReal ENNReal

namespace UniversalFInfinity
universe u v
variable {G : Type u} [Group G] {A : Type v} [MulAction G A]

abbrev Orbits := Quotient (MulAction.orbitRel G A)

lemma orbit_mk_smul (g : G) (a : A) : (Quotient.mk'' (g • a) : Orbits (G := G) (A := A)) = Quotient.mk'' a := by
  apply Quotient.sound
  exact ⟨g,rfl⟩

lemma orbit_out_translate (a : A) : ∃ g : G, a = g • (Quotient.mk'' a : Orbits (G := G)).out := by
  have h := Quotient.exact (Quotient.out_eq' (q := (Quotient.mk'' a : Orbits (G := G))))
  obtain ⟨g,hg⟩ := h
  refine ⟨g⁻¹,?_⟩
  rw [←hg,inv_smul_smul]

end UniversalFInfinity

open Set Metric Topology

namespace UniversalFInfinity.Milnor
open Set Metric Topology UniversalFInfinity.Simplicial
universe u
variable (G : Type u) [Group G]
local instance (priority := 2000) instDecidableEqProdNat_solutions_7 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

end UniversalFInfinity.Milnor

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CellularApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology

namespace UniversalFInfinity.Cellular

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
omit [MulAction G X] [ContinuousConstSMul G X] in
lemma isEmpty_skeleton_zero : IsEmpty (Skeleton (univ : Set X) 0) := by
  refine ⟨fun x => ?_⟩
  have hx := x.2
  change x.1 ∈ (CWComplex.skeletonLT (univ : Set X) 0 : Set X) at hx
  rw [CWComplex.skeletonLT_zero_eq_empty] at hx
  exact hx

end

open Set Metric Topology
universe u v
end UniversalFInfinity.Cellular

open scoped TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.MilnorProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Milnor

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical Topology.Homotopy unitInterval
universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable (N : Type w) [DecidableEq N] [Nontrivial N]
local instance (priority := 2000) instDecidableEqProdNat_solutions_9 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

end

open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical Topology.Homotopy unitInterval
universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable (N : Type w) [DecidableEq N] [Nontrivial N]
local instance (priority := 2000) instDecidableEqProdNat_solutions_10 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

end UniversalFInfinity.Milnor

namespace UniversalFInfinity.Simplicial

section
open Set Metric Topology BigOperators
open scoped Classical
universe u v w
variable {V : Type u} {W : Type v} {U : Type w}

def tensor (x : V →₀ ℝ) (y : W →₀ ℝ) : V × W →₀ ℝ :=
  Finsupp.onFinset (x.support ×ˢ y.support) (fun p => x p.1 * y p.2) (by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hp),
      Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hp)⟩)

lemma tensor_apply (x : V →₀ ℝ) (y : W →₀ ℝ) (p : V × W) : tensor x y p = x p.1*y p.2 := rfl
lemma tensor_support (x : V →₀ ℝ) (y : W →₀ ℝ) :
    (tensor x y).support = x.support ×ˢ y.support := by
  ext p
  simp only [Finsupp.mem_support_iff,tensor_apply,Finset.mem_product,mul_ne_zero_iff]
lemma tensor_sum (x : V →₀ ℝ) (y : W →₀ ℝ) :
    (tensor x y).sum (fun _ r => r) = x.sum (fun _ r => r)*y.sum (fun _ r => r) := by
  rw [Finsupp.sum,tensor_support,Finset.sum_product]
  simp only [tensor_apply,Finsupp.sum,← Finset.mul_sum,← Finset.sum_mul]

end

section
open Set Metric Topology BigOperators
open scoped Classical unitInterval
universe u v
variable {V : Type u} {W : Type v}

variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
variable (p : V × V → W) (hp : ∀ s t : Face K, (s.1 ×ˢ t.1).image p ∈ L)

include hp in
lemma diagonal_face (s : Face K) : s.1.image (fun v => p (v,v)) ∈ L := by
  apply L.isRelLowerSet_faces.mem_of_le (hp s s) _ ((K.isRelLowerSet_faces s.2).1.image _)
  intro z hz
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨(v,v),Finset.mem_product.mpr ⟨hv,hv⟩,rfl⟩

variable [Finite (Face K)]

def diagonalCarrier (s : Face K) : Face L := ⟨(s.1 ×ˢ s.1).image p,hp s s⟩
end

open Set Metric Topology BigOperators
open scoped Classical
universe u v w
end UniversalFInfinity.Simplicial

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.SimplicialProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Milnor
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical
universe u v w
variable {G : Type u} {H : Type v} {J : Type w}
local instance (priority := 2000) instDecidableEqProdNat_solutions_11 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

def pairVertex (β : G → H → J) (v : (ℕ × G) × (ℕ × H)) : ℕ × J :=
  (Nat.pair v.1.1 v.2.1,β v.1.2 v.2.2)

def pairFace (β : G → H → J) (s : Finset (ℕ × G)) (t : Finset (ℕ × H)) : Finset (ℕ × J) :=
  (s ×ˢ t).image (pairVertex β)

lemma pairFace_valid (β : G → H → J) {s : Finset (ℕ × G)} {t : Finset (ℕ × H)}
    (hs : s ∈ complex G) (ht : t ∈ complex H) : pairFace β s t ∈ complex J := by
  refine ⟨(hs.1.product ht.1).image _,?_⟩
  intro a ha b hb hab
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨⟨x',y'⟩,hxy',rfl⟩ := Finset.mem_image.mp hb
  have hh := Nat.pair_eq_pair.mp hab
  have hx : x = x' := hs.2 (Finset.mem_product.mp hxy).1 (Finset.mem_product.mp hxy').1 hh.1
  have hy : y = y' := ht.2 (Finset.mem_product.mp hxy).2 (Finset.mem_product.mp hxy').2 hh.2
  subst x'; subst y'; rfl

lemma pairFace_mono (β : G → H → J) {s s' : Finset (ℕ × G)} {t t' : Finset (ℕ × H)}
    (hs : s ⊆ s') (ht : t ⊆ t') : pairFace β s t ⊆ pairFace β s' t' :=
  Finset.image_subset_image (Finset.product_subset_product hs ht)

variable [Group G] [Group H] [Group J]
variable (φ : G →* J) (ψ : H →* J) (hc : ∀ g h, Commute (φ g) (ψ h))

include hc in
lemma pair_translate_vertex (a g : G) (b h : H) :
    φ (a*g)*ψ (b*h) = (φ a*ψ b)*(φ g*ψ h) := by
  rw [φ.map_mul,ψ.map_mul]
  calc
    (φ a*φ g)*(ψ b*ψ h) = φ a*(φ g*ψ b)*ψ h := by simp only [mul_assoc]
    _ = φ a*(ψ b*φ g)*ψ h := by
      have hh := hc g b
      change φ g * ψ b = ψ b * φ g at hh
      rw [hh]
    _ = (φ a*ψ b)*(φ g*ψ h) := by simp only [mul_assoc]

def productShapes (S : Finset (Finset (ℕ × G))) (T : Finset (Finset (ℕ × H))) :
    Finset (Finset (ℕ × J)) := (S ×ˢ T).image (fun p => pairFace (fun g h => φ g*ψ h) p.1 p.2)

end UniversalFInfinity.Milnor

namespace UniversalFInfinity.Simplicial

section
open Set Metric Topology BigOperators
open scoped Classical Topology.Homotopy
universe u v w
variable {V : Type u} {W : Type v}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
variable (p : V × V → W) (hp : ∀ s t : Face K, (s.1 ×ˢ t.1).image p ∈ L)
variable (x : Space K) (v : V) (hx : x.1 = Finsupp.single v 1)

include hx in
lemma anchorFace : ({v} : Finset V) ∈ K := by
  have hh := x.2.2.2
  rwa [hx,Finsupp.support_single _ one_ne_zero] at hh

include hx hp in
lemma leftAxisFace (s : Face K) : s.1.image (fun a => p (a,v)) ∈ L := by
  have hh := hp s ⟨{v},anchorFace K x v hx⟩
  simpa only [Finset.product_singleton,Finset.map_eq_image,Finset.image_image,
    Function.comp_def,Function.Embedding.sectL_apply,Function.Embedding.coeFn_mk] using hh
include hx hp in
lemma rightAxisFace (s : Face K) : s.1.image (fun a => p (v,a)) ∈ L := by
  have hh := hp ⟨{v},anchorFace K x v hx⟩ s
  simpa only [Finset.singleton_product,Finset.map_eq_image,Finset.image_image,
    Function.comp_def,Function.Embedding.sectR_apply,Function.Embedding.coeFn_mk] using hh

end

open scoped Classical Topology.Homotopy
universe u v w
end UniversalFInfinity.Simplicial

namespace UniversalFInfinity.Milnor
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical Topology.Homotopy
universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable (N : Type w) [DecidableEq N] [Nontrivial N]
local instance (priority := 2000) instDecidableEqProdNat_solutions_12 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

variable (φ ψ : G →* H) (hc : ∀ g h, Commute (φ g) (ψ h)) (S : Shapes G)
def commutingProduct : G →* H where
  toFun g := φ g*ψ g
  map_one' := by rw [φ.map_one,ψ.map_one,one_mul]
  map_mul' a b := pair_translate_vertex φ ψ hc a b a b

def addVertex := pairVertex (fun g h => φ g*ψ h)

def diagLayer (i : ℕ) := Nat.pair i i
def leftLayer (i : ℕ) := Nat.pair i 0
def rightLayer (i : ℕ) := Nat.pair 0 i
lemma diagLayer_injective : Function.Injective diagLayer := fun _ _ h => (Nat.pair_eq_pair.mp h).1
lemma leftLayer_injective : Function.Injective leftLayer := fun _ _ h => (Nat.pair_eq_pair.mp h).1
lemma rightLayer_injective : Function.Injective rightLayer := fun _ _ h => (Nat.pair_eq_pair.mp h).2

end UniversalFInfinity.Milnor

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.FiniteEnvelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity

section

variable {K D V : Type*} [Field K] [Ring D] [Algebra K D] [Group V]

abbrev ModelAlgebra (K D V : Type*) [Field K] [Ring D] [Algebra K D] [Group V] :=
  D ⊗[K] MonoidAlgebra K V

noncomputable def diagramElement (e : D) (v : V) : ModelAlgebra K D V :=
  (1 - e) ⊗ₜ[K] (1 : MonoidAlgebra K V) + e ⊗ₜ[K] MonoidAlgebra.of K V v

lemma diagramElement_one (e : D) : diagramElement (K := K) e (1 : V) = 1 := by
  simp only [diagramElement, map_one, TensorProduct.sub_tmul]
  rw [sub_add_cancel, Algebra.TensorProduct.one_def]

lemma diagramElement_mul (e : D) (he : e * e = e) (v w : V) :
    diagramElement (K := K) e v * diagramElement (K := K) e w =
      diagramElement (K := K) e (v * w) := by
  have h₁ : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h₂ : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h₃ : (1 - e) * (1 - e) = 1 - e := by
    rw [mul_sub, mul_one, h₁, sub_zero]
  simp only [diagramElement, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
    h₁, h₂, h₃, he, TensorProduct.zero_tmul, add_zero, zero_add, one_mul, map_mul]

end

namespace FiniteEnvelope

variable {I X : Type*}

abbrev RelationIndex (r : Set (FreeGroup X)) (S : Set (I × I))
    (T : Set (I × I × I)) :=
  (I × r) ⊕ (S × X) ⊕ (T × X × X) ⊕ (T × X)

def relationWord (r : Set (FreeGroup X)) (S : Set (I × I))
    (T : Set (I × I × I)) : RelationIndex r S T → FreeGroup (I × X)
  | .inl (i, w) => FreeGroup.map (fun x => (i, x)) w.val
  | .inr (.inl (s, x)) => FreeGroup.of (s.val.1, x) * (FreeGroup.of (s.val.2, x))⁻¹
  | .inr (.inr (.inl (t, x, y))) =>
      (FreeGroup.of (t.val.1, x) * FreeGroup.of (t.val.2.1, y)) *
        (FreeGroup.of (t.val.2.1, y) * FreeGroup.of (t.val.1, x))⁻¹
  | .inr (.inr (.inr (t, x))) =>
      FreeGroup.of (t.val.2.2, x) *
        (FreeGroup.of (t.val.1, x) * FreeGroup.of (t.val.2.1, x))⁻¹

abbrev relators (r : Set (FreeGroup X)) (S : Set (I × I))
    (T : Set (I × I × I)) := Set.range (relationWord r S T)

abbrev Envelope (r : Set (FreeGroup X)) (S : Set (I × I))
    (T : Set (I × I × I)) := PresentedGroup (relators r S T)

instance finiteRelators [Finite I] [Finite X] (r : Set (FreeGroup X))
    [Finite r] (S : Set (I × I)) (T : Set (I × I × I)) :
    Finite (relators r S T) := Set.finite_range (relationWord r S T)

instance finitelyPresented [Finite I] [Finite X] (r : Set (FreeGroup X))
    [Finite r] (S : Set (I × I)) (T : Set (I × I × I)) :
    Group.IsFinitelyPresented (Envelope r S T) := inferInstanceAs
      (Group.IsFinitelyPresented (PresentedGroup (relators r S T)))

variable (r : Set (FreeGroup X)) (S : Set (I × I)) (T : Set (I × I × I))

def copy (i : I) : PresentedGroup r →* Envelope r S T :=
  PresentedGroup.map (FreeGroup.map fun x => (i, x))
    (fun w hw => ⟨.inl (i, ⟨w, hw⟩), rfl⟩)

@[simp]
lemma copy_of (i : I) (x : X) :
    copy r S T i (PresentedGroup.of x) = PresentedGroup.of (i, x) := rfl

variable {r S T}

def commutingProduct {G H : Type*} [Group G] [Group H]
    (f g : G →* H) (h : ∀ u v, Commute (f u) (g v)) : G →* H where
  toFun u := f u * g u
  map_one' := by simp
  map_mul' u v := by
    simp only [map_mul]
    exact (h v u).mul_mul_mul_comm _ _

end FiniteEnvelope

structure FiniteIdempotentSystem (D : Type) [Ring D] where
  carrier : Set D
  finite : carrier.Finite
  one_mem : (1 : D) ∈ carrier
  idempotent : ∀ e ∈ carrier, e * e = e

namespace FiniteIdempotentSystem

variable {D : Type} [Ring D]

instance instFiniteElemCarrier (P : FiniteIdempotentSystem D) : Finite P.carrier := P.finite

def identity (P : FiniteIdempotentSystem D) : P.carrier := ⟨1, P.one_mem⟩

lemma isIdempotent (P : FiniteIdempotentSystem D) (e : P.carrier) :
    (e : D) * e = e := P.idempotent e.val e.property

end FiniteIdempotentSystem

namespace TwoEnvelope

variable {K₂ K₃ D₂ D₃ : Type}
variable [Field K₂] [Field K₃] [Ring D₂] [Ring D₃]
variable [Algebra K₂ D₂] [Algebra K₃ D₃]
variable (P₂ : FiniteIdempotentSystem D₂) (P₃ : FiniteIdempotentSystem D₃)

abbrev Index := P₂.carrier ⊕ P₃.carrier

def common : Set (Index P₂ P₃ × Index P₂ P₃) :=
  {(.inl P₂.identity, .inr P₃.identity)}

def triples : Set (Index P₂ P₃ × Index P₂ P₃ × Index P₂ P₃) :=
  {t | match t with
    | (.inl e, .inl p, .inl s) =>
        e.val * p.val = 0 ∧ p.val * e.val = 0 ∧ s.val = e.val + p.val
    | (.inr e, .inr p, .inr s) =>
        e.val * p.val = 0 ∧ p.val * e.val = 0 ∧ s.val = e.val + p.val
    | _ => False}

end TwoEnvelope
end UniversalFInfinity

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.MatrixDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity
namespace MatrixDiagram

open Matrix

variable {K T : Type*} [CommRing K] [AddCommGroup T]

def OrthogonallyAdditive (z : Matrix (Fin 3) (Fin 3) K → T) : Prop :=
  ∀ E P, IsIdempotentElem E → IsIdempotentElem P → E * P = 0 → P * E = 0 →
    z (E + P) = z E + z P

lemma rank_one_idempotent (u l : Fin 3 → K) (h : l ⬝ᵥ u = 1) :
    IsIdempotentElem (vecMulVec u l) := by
  change vecMulVec u l * vecMulVec u l = vecMulVec u l
  rw [vecMulVec_mul_vecMulVec, h, one_smul]

lemma rank_one_mul_zero (u l v m : Fin 3 → K) (h : l ⬝ᵥ v = 0) :
    vecMulVec u l * vecMulVec v m = 0 := by
  rw [vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]

def row (s : K) : Fin 3 → K := ![1, s, 0]
def along (s t : K) : Fin 3 → K := ![1 - s * t, t, 0]
def direction (s : K) : Fin 3 → K := ![-s, 1, 0]
def anchor : Fin 3 → K := ![1, 0, 1]
def witness (s t : K) : Fin 3 → K := ![-t, 1 - s * t, t]

lemma frame_identities (s t : K) :
    row s ⬝ᵥ along s t = 1 ∧ row s ⬝ᵥ direction s = 0 ∧
    witness s t ⬝ᵥ along s t = 0 ∧ witness s t ⬝ᵥ direction s = 1 ∧
    row s ⬝ᵥ (anchor : Fin 3 → K) = 1 ∧
    witness s t ⬝ᵥ (anchor : Fin 3 → K) = 0 := by
  simp [row, along, witness, direction, anchor, dotProduct, Fin.sum_univ_three]
  constructor <;> ring

lemma along_step (s t : K) : along s t + direction s = along s (t + 1) := by
  ext i
  fin_cases i <;> simp [along, direction]
  ring

lemma OrthogonallyAdditive.transpose {z : Matrix (Fin 3) (Fin 3) K → T}
    (hz : OrthogonallyAdditive z) : OrthogonallyAdditive (fun E => z E.transpose) := by
  intro E P hE hP hEP hPE
  have hEt : IsIdempotentElem E.transpose := by
    change E.transpose * E.transpose = E.transpose
    rw [← transpose_mul, hE]
  have hPt : IsIdempotentElem P.transpose := by
    change P.transpose * P.transpose = P.transpose
    rw [← transpose_mul, hP]
  have hEPt : E.transpose * P.transpose = 0 := by rw [← transpose_mul, hPE, transpose_zero]
  have hPEt : P.transpose * E.transpose = 0 := by rw [← transpose_mul, hEP, transpose_zero]
  simpa only [transpose_add] using hz _ _ hEt hPt hEPt hPEt

lemma OrthogonallyAdditive.comp {z : Matrix (Fin 3) (Fin 3) K → T}
    (hz : OrthogonallyAdditive z) (f : Matrix (Fin 3) (Fin 3) K →+* Matrix (Fin 3) (Fin 3) K) :
    OrthogonallyAdditive (fun E => z (f E)) := by
  intro E P hE hP hEP hPE
  have hEt : IsIdempotentElem (f E) := by
    change f E * f E = f E
    rw [← map_mul, hE]
  have hPt : IsIdempotentElem (f P) := by
    change f P * f P = f P
    rw [← map_mul, hP]
  have hEPt : f E * f P = 0 := by rw [← map_mul, hEP, map_zero]
  have hPEt : f P * f E = 0 := by rw [← map_mul, hPE, map_zero]
  simpa only [map_add] using hz _ _ hEt hPt hEPt hPEt

def basisVector (i : Fin 3) : Fin 3 → K := Pi.single i 1

def diagonalUnit (i : Fin 3) : Matrix (Fin 3) (Fin 3) K :=
  vecMulVec (basisVector i) (basisVector i)

lemma diagonalUnit_idempotent (i : Fin 3) :
    IsIdempotentElem (diagonalUnit i : Matrix (Fin 3) (Fin 3) K) := by
  apply rank_one_idempotent
  simp [basisVector, dotProduct, Pi.single_apply]

end MatrixDiagram

namespace PrefixAlgebra

variable (K : Type*) [CommRing K]

abbrev Sequences := Stream' Bool
abbrev Space := Sequences →₀ K
abbrev Operators := Module.End K (Space K)

noncomputable def prefixOp (i : Bool) : Operators K :=
  Finsupp.linearCombination K (fun s => Finsupp.single (Stream'.cons i s) 1)

noncomputable def delete (i : Bool) : Operators K :=
  Finsupp.linearCombination K (fun s => if s.head = i then Finsupp.single s.tail 1 else 0)

@[simp] lemma prefix_single (i : Bool) (s : Sequences) (a : K) :
    prefixOp K i (Finsupp.single s a) = Finsupp.single (Stream'.cons i s) a := by
  simp [prefixOp]

@[simp] lemma delete_single (i : Bool) (s : Sequences) (a : K) :
    delete K i (Finsupp.single s a) = if s.head = i then Finsupp.single s.tail a else 0 := by
  by_cases h : s.head = i <;> simp [delete, h]

lemma prefix_partition : prefixOp K false * delete K false + prefixOp K true * delete K true = 1 := by
  apply Finsupp.lhom_ext
  intro s a
  simp only [LinearMap.add_apply, Module.End.mul_apply, delete_single]
  cases h : s.head <;> simp
  all_goals rw [← h, Stream'.cons_head_tail]

noncomputable def algebra : Subalgebra K (Operators K) :=
  Algebra.adjoin K {prefixOp K false, prefixOp K true, delete K false, delete K true}

noncomputable def left (i : Bool) : algebra K :=
  ⟨prefixOp K i, by apply Algebra.subset_adjoin; cases i <;> simp⟩
noncomputable def right (i : Bool) : algebra K :=
  ⟨delete K i, by apply Algebra.subset_adjoin; cases i <;> simp⟩

noncomputable def leftWord : List Bool → algebra K
  | [] => 1
  | b :: w => left K b * leftWord w

noncomputable def rightWord : List Bool → algebra K
  | [] => 1
  | b :: w => rightWord w * right K b

@[simp] lemma leftWord_nil : leftWord K [] = 1 := rfl
@[simp] lemma rightWord_nil : rightWord K [] = 1 := rfl

def words : Fin 3 → Fin 3 → List Bool :=
  ![![[false,false], [false,true], [true]],
    ![[false,false,false], [false,true], [true]],
    ![[false,false,true], [false,true], [true]]]

end PrefixAlgebra

namespace MatrixCorners

variable {K D : Type*} [CommRing K] [Ring D] [Algebra K D]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (L R : ι → D) (h : ∀ i j, R i * L j = if i = j then 1 else 0)

abbrev unit (i j : ι) : D := L i * R j

include h

omit [Fintype ι] in
lemma unit_mul (i j k m : ι) :
    unit L R i j * unit L R k m = if j = k then unit L R i m else 0 := by
  dsimp only [unit]
  rw [mul_assoc, ← mul_assoc (R j), h]
  split_ifs <;> simp

omit [Fintype ι] in
lemma weighted_unit_mul (a b : K) (i j k m : ι) :
    (a • unit L R i j) * (b • unit L R k m) =
      if j = k then (a * b) • unit L R i m else 0 := by
  rw [smul_mul_smul, unit_mul L R h]
  split_ifs <;> simp

noncomputable def matrixMap (A : Matrix ι ι K) : D :=
  ∑ i, ∑ j, (A i j) • unit L R i j

lemma matrixMap_mul (A B : Matrix ι ι K) :
    matrixMap L R (A * B) = matrixMap L R A * matrixMap L R B := by
  classical
  have hr : matrixMap L R A * matrixMap L R B =
      ∑ i, ∑ j, ∑ m, (A i j * B j m) • unit L R i m := by
    simp only [matrixMap, Finset.sum_mul, Finset.mul_sum, weighted_unit_mul L R h]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    calc
      _ = ∑ j, ∑ i, ∑ m, (A i j * B j m) • unit L R i m := by
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hr]
  simp only [matrixMap, Matrix.mul_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

noncomputable def hom : Matrix ι ι K →ₙₐ[K] D where
  toFun := matrixMap L R
  map_zero' := by simp [matrixMap]
  map_add' A B := by simp [matrixMap, add_smul, Finset.sum_add_distrib]
  map_mul' := matrixMap_mul L R h
  map_smul' a A := by simp [matrixMap, Finset.smul_sum, smul_smul]

lemma map_diagonal (i : ι) :
    hom L R h (Matrix.diagonal (Pi.single i (1 : K))) = L i * R i := by
  change matrixMap L R _ = _
  simp [matrixMap, Matrix.diagonal, Pi.single_apply, unit]

end MatrixCorners
end UniversalFInfinity

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Idempotents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity
namespace IdempotentSystems

open PrefixAlgebra MatrixCorners

variable (K : Type) [CommRing K]

lemma sum_idempotent {D : Type*} [Ring D] {E P : D}
    (hE : IsIdempotentElem E) (hP : IsIdempotentElem P)
    (hEP : E * P = 0) (hPE : P * E = 0) : IsIdempotentElem (E + P) := by
  change (E + P) * (E + P) = E + P
  rw [add_mul, mul_add, mul_add, hE.eq, hP.eq, hEP, hPE]
  simp

lemma diagonalUnit_eq_diagonal (i : Fin 3) :
    (MatrixDiagram.diagonalUnit i : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (Pi.single i 1) := by
  classical
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [MatrixDiagram.diagonalUnit, MatrixDiagram.basisVector,
      Matrix.vecMulVec, Matrix.diagonal, Pi.single_apply]

end IdempotentSystems

namespace ConcreteEnvelopes

open PrefixAlgebra IdempotentSystems

def IsUniversal (U : Type) [Group U] : Prop :=
  ∀ (V : Type) [Group V] [Group.IsFinitelyPresented V],
    ∃ φ : V →* U, Function.Injective φ

end ConcreteEnvelopes
end UniversalFInfinity

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Cylinders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Cylinder

section
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Sphere (n : ℕ) := sphere (0 : Fin n → ℝ) 1
abbrev Rim (n : ℕ) := {p : unitInterval × Disk n // p.1 = 0 ∨ p.2.1 ∈ sphere 0 1}

variable {n : ℕ}
def denominator (p : unitInterval × Disk n) : ℝ := max (2-(p.1:ℝ)) (2*‖p.2.1‖)
lemma denominator_bounds (p : unitInterval × Disk n) : 1 ≤ denominator p ∧ denominator p ≤ 2 := by
  have hx : ‖p.2.1‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using p.2.2
  have ht0 := p.1.2.1
  have ht1 := p.1.2.2
  constructor
  · exact (by linarith : 1 ≤ 2-(p.1:ℝ)).trans (le_max_left _ _)
  · exact max_le (by linarith) (by linarith)
lemma denominator_pos (p : unitInterval × Disk n) : 0 < denominator p :=
  lt_of_lt_of_le (by norm_num) (denominator_bounds p).1

def factor (p : unitInterval × Disk n) : ℝ := 2 / denominator p
lemma factor_mul_denominator (p : unitInterval × Disk n) : factor p * denominator p = 2 :=
  div_mul_cancel₀ _ (ne_of_gt (denominator_pos p))
lemma factor_bounds (p : unitInterval × Disk n) : 1 ≤ factor p ∧ factor p ≤ 2 := by
  have hd := denominator_bounds p
  constructor
  · exact (le_div_iff₀ (denominator_pos p)).mpr (by simpa using hd.2)
  · exact (div_le_iff₀ (denominator_pos p)).mpr (by linarith)
lemma factor_nonneg (p : unitInterval × Disk n) : 0 ≤ factor p := (by norm_num : (0:ℝ)≤1).trans (factor_bounds p).1

lemma retract_time_mem (p : unitInterval × Disk n) :
    2 - factor p * (2-(p.1:ℝ)) ∈ (Set.Icc (0:ℝ) 1) := by
  have hd : 2-(p.1:ℝ) ≤ denominator p := le_max_left _ _
  have hmul := mul_le_mul_of_nonneg_left hd (factor_nonneg p)
  have heq := factor_mul_denominator p
  have hf := (factor_bounds p).1
  have ht0 := p.1.2.1
  have ht1 := p.1.2.2
  have hge := mul_le_mul_of_nonneg_right hf (by linarith : 0 ≤ 2-(p.1:ℝ))
  constructor <;> nlinarith

lemma retract_disk_mem (p : unitInterval × Disk n) :
    factor p • p.2.1 ∈ closedBall (0 : Fin n → ℝ) 1 := by
  simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg (factor_nonneg p)]
  have hd : 2*‖p.2.1‖ ≤ denominator p := le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_left hd (factor_nonneg p)
  have heq := factor_mul_denominator p
  nlinarith

end

open Set Metric Topology
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y]

lemma continuous_finite_closed_paste {A : Type*} [TopologicalSpace A] {ι : Type*} [Finite ι]
    (S : ι → Set A) (f : ∀ i, C(S i,Y))
    (hcompat : ∀ i j x (hi : x ∈ S i) (hj : x ∈ S j), f i ⟨x,hi⟩ = f j ⟨x,hj⟩)
    (hcover : ⋃ i, S i = Set.univ) (hclosed : ∀ i, IsClosed (S i)) :
    Continuous (Set.liftCover S (fun i => f i) hcompat hcover) := by
  rw [continuous_iff_isClosed]
  intro D hD
  rw [Set.preimage_liftCover]
  exact isClosed_iUnion_of_finite fun i => (hclosed i).isClosedMap_subtype_val _ (hD.preimage (f i).continuous)

def face (n : ℕ) : Bool → Set (Rim n)
  | false => {p | p.1.1 = 0}
  | true => {p | p.1.2.1 ∈ sphere 0 1}
lemma face_cover (n : ℕ) : ⋃ i, face n i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  rcases p.2 with h | h
  · exact Set.mem_iUnion.mpr ⟨false,h⟩
  · exact Set.mem_iUnion.mpr ⟨true,h⟩

end UniversalFInfinity.Cylinder

namespace UniversalFInfinity.DiskCube
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Sphere (n : ℕ) := sphere (0 : Fin n → ℝ) 1

def toCube (n : ℕ) : C(Disk n,Fin n → unitInterval) := by
  refine ⟨fun x i => ⟨(x.1 i+1)/2,?_⟩,?_⟩
  · have hx : ‖x.1 i‖ ≤ 1 := (norm_le_pi_norm x.1 i).trans (by simpa only [mem_closedBall,dist_zero_right] using x.2)
    rw [Real.norm_eq_abs,abs_le] at hx
    constructor <;> linarith [hx.1,hx.2]
  · apply continuous_pi
    intro i
    exact (((continuous_apply i).comp continuous_subtype_val).add continuous_const |>.div_const 2).subtype_mk _

end UniversalFInfinity.DiskCube

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.SphereHomotopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Cellular
open Set Metric Topology
universe u v
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
variable (Y : ℕ → Type v) [∀ i,TopologicalSpace (Y i)] (q : ∀ i,C(Y i,Y (i+1)))

def towerComposite (f : C(X,Y 0)) : ∀ i,C(X,Y i)
  | 0 => f
  | i+1 => (q i).comp (towerComposite f i)

end UniversalFInfinity.Cellular

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.GraphBundles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.GraphBundle

section
open Set Topology
open scoped unitInterval
universe u v w z
variable {C : Type u}
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))

variable [TopologicalSpace C] [DiscreteTopology C]

lemma closed_of_slices {D : Type*} [TopologicalSpace D] {S : Set (C × D)}
    (h : ∀ c,IsClosed ((fun x => (c,x)) ⁻¹' S)) : IsClosed S := by
  rw [←isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro z hz
  refine ⟨{z.1} ×ˢ ((fun x => (z.1,x)) ⁻¹' S)ᶜ,?_,
    (isOpen_discrete {z.1}).prod (h z.1).isOpen_compl,⟨rfl,hz⟩⟩
  intro p hp
  have he : p.1 = z.1 := hp.1
  simpa only [Set.mem_compl_iff,Set.mem_preimage,←he] using hp.2

end

open Set Topology
open scoped unitInterval
universe u v w
end UniversalFInfinity.GraphBundle

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.GraphActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.PathFamilies
open scoped unitInterval
universe u v
variable {J : Type u} [TopologicalSpace J] {Y : Type v} [TopologicalSpace Y]
def intervalPath : Path (0:I) 1 where
  toFun := id
  continuous_toFun := continuous_id
  source' := rfl
  target' := rfl

def unpause : C(I × I,I) := (Path.Homotopy.transRefl intervalPath).toContinuousMap

end UniversalFInfinity.PathFamilies

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.TorusBundles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.TorusGeometry

section
open Set Topology Milnor UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v
variable {U : Type u} [Group U] (f : Monoid.End U)
local instance (priority := 2000) instDecidableEqProdNat_solutions (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

end

open Set Topology Milnor
open scoped Classical unitInterval
universe u v
end UniversalFInfinity.TorusGeometry

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.TreeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.GraphBundle

open Set Topology
open scoped unitInterval
universe u v
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A]
variable (τ : C → C) (F : C → C(A,A))

def forward : ℕ → C → C(A,A)
  | 0,_ => .id _
  | n+1,c => (F (τ^[n] c)).comp (forward n c)
omit [TopologicalSpace C] [DiscreteTopology C] in
lemma forward_natural (n : ℕ) (c : C) (x : A) :
    forward τ F n (τ c) (F c x) = F (τ^[n] c) (forward τ F n c x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change F (τ^[n] (τ c)) (forward τ F n (τ c) (F c x)) =
      F (τ^[n+1] c) (F (τ^[n] c) (forward τ F n c x))
    rw [ih,Function.iterate_succ_apply]
end UniversalFInfinity.GraphBundle

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.ControlledCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Cellular

open Set Topology
open scoped unitInterval
universe u v w
variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
  {Z : Type w} [TopologicalSpace Z]
variable (a b : C(I × X,Y)) (A B : Y)
variable (h0 : ∀ x,a (0,x) = b (0,x)) (ha : ∀ x,a (1,x) = A) (hb : ∀ x,b (1,x) = B)

def contractionPath (a : C(I × X,Y)) (A : Y) (ha : ∀ x,a (1,x) = A) (x : X) : Path (a (0,x)) A :=
  { toFun t := a (t,x)
    continuous_toFun := a.continuous.comp (continuous_id.prodMk continuous_const)
    source' := rfl
    target' := ha x }

end UniversalFInfinity.Cellular

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.TorusHomotopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.TorusGeometry

section
open Set Topology Milnor
open scoped Classical unitInterval
universe u v
variable {U : Type u} [Group U] (f : Monoid.End U)
local instance (priority := 2000) instDecidableEqProdNat_solutions_2 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

end

open Set Topology Milnor
open scoped Classical unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)
local instance (priority := 2000) instDecidableEqProdNat_solutions_3 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

end UniversalFInfinity.TorusGeometry

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.TorusSpheres
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Milnor
open Set Topology UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v w
variable {G : Type u} {H : Type v}
local instance (priority := 2000) instDecidableEqProdNat_solutions_16 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
def evenLayer (n : ℕ) := 2*n
def oddLayer (n : ℕ) := 2*n+1
lemma evenLayer_injective : Function.Injective evenLayer := by intro a b h; unfold evenLayer at h; omega
lemma oddLayer_injective : Function.Injective oddLayer := by intro a b h; unfold oddLayer at h; omega
lemma even_ne_odd (a b : ℕ) : evenLayer a ≠ oddLayer b := by unfold evenLayer oddLayer; omega

end UniversalFInfinity.Milnor

namespace UniversalFInfinity.TorusGeometry

section
open Set Topology Cellular
open scoped unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)
variable [hfi : Fact (Function.Injective f)]
local notation "hf" => (Fact.out : Function.Injective f)
local instance (priority := 2000) instDecidableEqProdNat_solutions_4 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

end

open Set Topology ConcreteEnvelopes
end UniversalFInfinity.TorusGeometry

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CellularChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Cellular

open Set Metric Topology
universe u
variable {Y : Type u} [TopologicalSpace Y]
def pathZero : C(C(unitInterval,Y),Y) := ⟨fun p => p 0,continuous_eval_const 0⟩
def pathOne : C(C(unitInterval,Y),Y) := ⟨fun p => p 1,continuous_eval_const 1⟩

def pathEvaluation : (pathZero (Y := Y)).Homotopy pathOne where
  toFun z := z.2 z.1
  continuous_toFun := continuous_eval.comp (continuous_snd.prodMk continuous_fst)
  map_zero_left _ := rfl
  map_one_left _ := rfl

end UniversalFInfinity.Cellular

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.TopologicalTowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.TopologicalTower
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]

variable (hf : ∀ i j h, IsClosedEmbedding (f i j h))

def ExtendsReals : Prop := ∀ n (g : C(X n,ℝ)),
  ∃ G : C(X (n+1),ℝ), ∀ x, G (f n (n+1) (Nat.le_succ n) x) = g x

variable (hext : ExtendsReals X f)

def realExtension (n : ℕ) (g : C(X n,ℝ)) : C(X (n+1),ℝ) := (hext n g).choose

def realFamily (n : ℕ) (g : C(X n,ℝ)) (m : ℕ) (hm : n ≤ m) : C(X m,ℝ) :=
  Nat.leRecOn hm (fun {k} => realExtension X f hext k) g

end UniversalFInfinity.TopologicalTower

namespace UniversalFInfinity.Sequential
open Set Topology
universe u
variable (X : ℕ → Type u) [∀ n,TopologicalSpace (X n)]
variable (step : ∀ n,C(X n,X (n+1)))

def map (i j : ℕ) (h : i ≤ j) : C(X i,X j) :=
  Nat.leRecOn h (fun {k} F => (step k).comp F) (.id (X i))

@[simp] lemma map_self (i : ℕ) : map X step i i le_rfl = .id _ := by
  simp only [map,Nat.leRecOn_self]

variable [∀ n,CWComplex (univ : Set (X n))]

structure CellSteps where
  cell : ∀ n m,RelCWComplex.cell (univ : Set (X n)) m → RelCWComplex.cell (univ : Set (X (n+1))) m
  injective : ∀ n m,Function.Injective (cell n m)
  dim : ∀ n m (_ : RelCWComplex.cell (univ : Set (X n)) m),m ≤ n
  exhaustive : ∀ n m,m ≠ n+1 → ∀ j, ∃ i,cell n m i = j
  compatibility : ∀ n m i x,step n (RelCWComplex.map m i x) = RelCWComplex.map m (cell n m i) x

variable (D : CellSteps X step)
def cellMap (i j : ℕ) (h : i ≤ j) (m : ℕ) :
    RelCWComplex.cell (univ : Set (X i)) m → RelCWComplex.cell (univ : Set (X j)) m :=
  Nat.leRecOn h (fun {k} F => D.cell k m ∘ F) id

lemma cellMap_self (i m : ℕ) : cellMap X step D i i le_rfl m = id := by
  simp only [cellMap,Nat.leRecOn_self]
end UniversalFInfinity.Sequential

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.TowerCoverings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.TopologicalTower

section
open Set Topology
universe u v w
variable {G : Type w} [Group G]
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)] [∀ n, MulAction G (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]

class EquivariantSystem : Prop where
  map_smul : ∀ i j h (g : G) x, f i j h (g • x) = g • f i j h x

end

section
open Set Topology
universe u w
variable {G : Type w} [Group G]
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)] [∀ n, MulAction G (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
variable [EquivariantSystem (G := G) X f]
variable (hf : ∀ i j h, IsClosedEmbedding (f i j h))

structure Slice (n : ℕ) where
  carrier : Set (X n)
  isOpen : IsOpen carrier
  disjoint : ∀ g : G, ((g • ·) '' carrier ∩ carrier).Nonempty → g = 1

def ExtendsSlices : Prop := ∀ n (U : Slice (G := G) X n),
  ∃ V : Slice (G := G) X (n+1), f n (n+1) (Nat.le_succ n) ⁻¹' V.carrier = U.carrier

variable (hext : ExtendsSlices (G := G) X f)

def extendSlice (n : ℕ) (U : Slice (G := G) X n) : Slice (G := G) X (n+1) := (hext n U).choose

def sliceFamily (k : ℕ) (U : Slice (G := G) X k) (n : ℕ) (hn : k ≤ n) : Slice (G := G) X n :=
  Nat.leRecOn hn (fun {m} => extendSlice X f hext m) U

end

open Set Metric Topology
universe u v

end UniversalFInfinity.TopologicalTower

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.BrownConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Brown

section
open Set Metric Topology Cellular
universe u
variable (G : Type u) [Group G]

variable {G}

section Zero
variable [TopologicalSpace G] [DiscreteTopology G]
lemma discrete_dim {X : Type u} [TopologicalSpace X] [DiscreteTopology X]
    (m : ℕ) (i : RelCWComplex.cell (univ : Set X) m) : m ≤ 0 := by
  cases m with
  | zero => exact le_rfl
  | succ m => exact i.elim

def pointCover : C(G,PUnit.{u+1}) := .const _ PUnit.unit
lemma pointCover_quotient : IsQuotientCoveringMap (pointCover (G := G)) G where
  __ := show IsQuotientMap (pointCover (G := G)) from
    (show IsOpenMap (pointCover (G := G)) from fun _ _ => isOpen_discrete _).isQuotientMap
      (by fun_prop) (fun _ => ⟨1,rfl⟩)
  __ := (inferInstance : ContinuousConstSMul G G)
  apply_eq_iff_mem_orbit := by
    intro x y
    constructor
    · intro _; exact ⟨x*y⁻¹,by simp [smul_eq_mul]⟩
    · intro _; rfl
  disjoint x := by
    refine ⟨{x},(isOpen_discrete _).mem_nhds (Set.mem_singleton x),?_⟩
    rintro g ⟨z,⟨y,hy,rfl⟩,h⟩
    simp only [Set.mem_singleton_iff] at hy h
    rw [hy] at h
    exact mul_right_cancel (show g*x=1*x by simpa only [smul_eq_mul,one_mul] using h)

end Zero

end

open Set Metric Topology Cellular
universe u
end UniversalFInfinity.Brown

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.UniverseTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

open Set Metric Topology
namespace UniversalFInfinity.UniverseTransport

section
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
variable {C : Set X} [CWComplex C] {f : X → Y} (hf : IsClosedEmbedding f)

def transportedMap (n : ℕ) (i : RelCWComplex.cell C n) : PartialEquiv (Fin n → ℝ) Y :=
  (RelCWComplex.map n i).trans (hf.isEmbedding.toPartialHomeomorph f).toPartialEquiv

@[simp] lemma transportedMap_apply (n : ℕ) (i : RelCWComplex.cell C n) (x : Fin n → ℝ) :
    transportedMap hf n i x = f (RelCWComplex.map n i x) := rfl

lemma transportedMap_source (n : ℕ) (i : RelCWComplex.cell C n) :
    (transportedMap hf n i).source = ball 0 1 := by
  simp only [transportedMap,PartialEquiv.trans_source,
    IsEmbedding.toPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ,
    RelCWComplex.source_eq]

lemma transportedMap_image (n : ℕ) (i : RelCWComplex.cell C n) (S : Set (Fin n → ℝ)) :
    transportedMap hf n i '' S = f '' (RelCWComplex.map n i '' S) :=
  Set.image_comp f (RelCWComplex.map n i) S

lemma transportedMap_continuousOn (n : ℕ) (i : RelCWComplex.cell C n) :
    ContinuousOn (transportedMap hf n i) (closedBall 0 1) :=
  hf.continuous.comp_continuousOn (RelCWComplex.continuousOn n i)

end

open Set Topology
universe u v
end UniversalFInfinity.UniverseTransport

end

end OAI
end


