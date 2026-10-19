-- Prove2me | Definitions.Def_OAIQWUFI007
-- name    : OAIQWUFI007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:50:06.32323+00:00
-- url     : https://prove2.me/theorems/4eb61e50-fb18-4c4c-b744-d5d0f74fbdeb
-- title:
--   OpenAI universal F∞ group split: definitions bundle 8 of 9
-- statement:
--   Definitions bundle 8 of 9 of the split of OpenAI's proof that a single group of type $F_\infty$ contains every finitely presented group (OpenAI, *A universal group of type F∞*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0). It holds OpenAI's Lean definitions, structures and instances from the modules listed below, ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas those definitions use in their bodies: several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs.
--
--   It imports bundles 5 and 6 of this split (`OAIQWUFI004`, `OAIQWUFI005`).
--
--   Modules: `CoveringAttachments.lean`, `Cylinders.lean`, `FiniteEnvelopes.lean`, `HomotopyProducts.lean`, `MilnorControl.lean`, `MilnorProducts.lean`, `SimplicialProducts.lean`, `SphereHomotopies.lean`, `TorusBundles.lean`, `TorusHomotopies.lean`, `TorusSpheres.lean`, `TowerCoverings.lean`, `TreeGeometry.lean`, `UniversalPresentation.lean`, `UniverseTransport.lean`.
--
--   The theorems the definitions do not need are proved in the solutions of this split. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/UniversalGroup at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWUFI004
import Definitions.Def_OAIQWUFI005

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

variable (rels : Set (FreeGroup ℕ))
abbrev V := CountableOvergroup.Overgroup (PresentedGroup.of (rels := rels))

end UniversalFInfinity.ThreePresentation

namespace UniversalFInfinity.RecursiveUniversal

lemma rawAt_encode (P : Code) (j : ℕ) : rawAt (Encodable.encode P) j = P.getD j [] := by
  simp [rawAt]

lemma coloured_relation (P : Code) (w : Word) (hw : w ∈ P) :
    FreeGroup.map (Nat.pair (Encodable.encode P)) (FreeGroup.mk w) ∈ allRelations := by
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hw
  refine ⟨Nat.pair (Encodable.encode P) j,?_⟩
  simp only [relator,Nat.unpair_pair,rawAt_encode,List.getD_eq_getElem?_getD,hj,
    Option.getD_some,colour,FreeGroup.map.mk]

def embed (P : Code) : PresentedGroup (relations P) →* Universal :=
  PresentedGroup.map (FreeGroup.map (Nat.pair (Encodable.encode P))) (by
    rintro _ ⟨w,hw,rfl⟩
    exact coloured_relation P w hw)

def project (P : Code) (k : ℕ) : PresentedGroup (relations P) :=
  if k.unpair.1 = Encodable.encode P then PresentedGroup.of k.unpair.2 else 1

lemma eval_colour (P : Code) (m : ℕ) :
    (FreeGroup.lift (project P)).comp (FreeGroup.map (Nat.pair m)) =
      if m = Encodable.encode P then PresentedGroup.mk (relations P) else 1 := by
  apply FreeGroup.ext_hom
  intro i
  simp only [MonoidHom.comp_apply,FreeGroup.map.of,FreeGroup.lift_apply_of,project,
    Nat.unpair_pair]
  split_ifs <;> rfl

lemma project_relator (P : Code) (k : ℕ) :
    FreeGroup.lift (project P) (FreeGroup.mk (relator k)) = 1 := by
  change FreeGroup.lift (project P)
    (FreeGroup.mk ((rawAt k.unpair.1 k.unpair.2).map
      (fun x => (Nat.pair k.unpair.1 x.1,x.2)))) = 1
  rw [← FreeGroup.map.mk]
  rw [← MonoidHom.comp_apply]
  rw [eval_colour]
  split_ifs with h
  · rw [h,rawAt_encode]
    exact raw_relation P _
  · rfl

def retract (P : Code) : Universal →* PresentedGroup (relations P) :=
  PresentedGroup.toGroup (by rintro _ ⟨k,rfl⟩; exact project_relator P k)

end UniversalFInfinity.RecursiveUniversal

end
end UniversalFinitelyPresentedProof

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
open scoped Classical
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_2
lemma fresh_cross (N : ℕ) (α : ℕ → ℕ) (hα : Function.Injective α) (hzero : α 0 = 0)
    {i j : ℕ} (hi : α i < N) (h : α i = fresh N j) : i = j := by
  by_cases hj : j = 0
  · subst j
    apply hα
    simpa only [fresh_zero,hzero] using h
  · have hh : N ≤ fresh N j := by simp only [fresh,ite_eq_right hj]; exact Nat.le_add_right _ _
    omega
end
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_3
lemma relayerLeftValid (φ : G →* H) (S : Finset (Finset (ℕ × G)))
    (α β : ℕ → ℕ) (hα : Function.Injective α) (hα0 : α 0 = 0) (s : Face (orbitSpan S)) :
    faceImage φ α s.1 ∪ faceImage φ (relayerFresh S α β) s.1 ∈ orbitSpan (relayerTarget φ S α β) := by
  apply orbitSpan_mono Finset.subset_union_left
  apply unionFace_controlled φ α (relayerFresh S α β) hα (fresh_injective _) S s
  intro v hv w _ h
  exact fresh_cross _ α hα hα0 ((orbit_below_bound S α s hv).trans_le (le_max_left _ _)) h

lemma relayerRightValid (φ : G →* H) (S : Finset (Finset (ℕ × G)))
    (α β : ℕ → ℕ) (hβ : Function.Injective β) (hβ0 : β 0 = 0) (s : Face (orbitSpan S)) :
    faceImage φ β s.1 ∪ faceImage φ (relayerFresh S α β) s.1 ∈ orbitSpan (relayerTarget φ S α β) := by
  apply orbitSpan_mono Finset.subset_union_right
  apply unionFace_controlled φ β (relayerFresh S α β) hβ (fresh_injective _) S s
  intro v hv w _ h
  exact fresh_cross _ β hβ hβ0 ((orbit_below_bound S β s hv).trans_le (le_max_right _ _)) h

variable (φ : G →* H) (S : Finset (Finset (ℕ × G))) (α β : ℕ → ℕ)
variable (hα : Function.Injective α) (hβ : Function.Injective β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
include hα hα0 in
lemma relayerLeftMapValid (s : Face (orbitSpan S)) :
    s.1.image (vertexMap φ α) ∈ orbitSpan (relayerTarget φ S α β) :=
  (orbitSpan _).isRelLowerSet_faces.mem_of_le (relayerLeftValid φ S α β hα hα0 s)
    Finset.subset_union_left (s.2.1.1.image _)
include hβ hβ0 in
lemma relayerRightMapValid (s : Face (orbitSpan S)) :
    s.1.image (vertexMap φ β) ∈ orbitSpan (relayerTarget φ S α β) :=
  (orbitSpan _).isRelLowerSet_faces.mem_of_le (relayerRightValid φ S α β hβ hβ0 s)
    Finset.subset_union_left (s.2.1.1.image _)
include hα hα0 in
lemma relayerFreshMapValid (s : Face (orbitSpan S)) :
    s.1.image (vertexMap φ (relayerFresh S α β)) ∈ orbitSpan (relayerTarget φ S α β) :=
  (orbitSpan _).isRelLowerSet_faces.mem_of_le (relayerLeftValid φ S α β hα hα0 s)
    Finset.subset_union_right (s.2.1.1.image _)

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

namespace UniversalFInfinity.HomotopyFunctor

section
open scoped Topology Topology.Homotopy
universe u v w
variable {N : Type u} {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y}

variable {Z : Type*} [TopologicalSpace Z] {z : Z}

def loopPair (p : GenLoop N X x) (q : GenLoop N Y y) : GenLoop N (X × Y) (x,y) :=
  ⟨p.1.prodMk q.1,fun t ht => Prod.ext (GenLoop.boundary p t ht) (GenLoop.boundary q t ht)⟩

lemma pair_homotopic {p p' : GenLoop N X x} {q q' : GenLoop N Y y}
    (h : GenLoop.Homotopic p p') (k : GenLoop.Homotopic q q') :
    GenLoop.Homotopic (loopPair p q) (loopPair p' q') := by
  rcases h with ⟨h⟩
  rcases k with ⟨k⟩
  refine ⟨{ toHomotopy := h.toHomotopy.prodMk k.toHomotopy,prop' := ?_ }⟩
  intro t a ha
  exact Prod.ext (h.eq_fst t ha) (k.eq_fst t ha)

end
open scoped Topology Topology.Homotopy
universe u v w
end UniversalFInfinity.HomotopyFunctor
namespace UniversalFInfinity.Milnor

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical Topology.Homotopy
universe u v
variable (G : Type u) [Group G]

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_4
lemma stage_point_face (S : Shapes G) : {(0,1)} ∈ stage G S := by
  apply orbitSpan_contains (basedShapes G S)
  · exact ⟨Finset.singleton_nonempty _,by simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst (0,(1:G))⟩
  · exact ⟨{(0,1)},Finset.mem_insert_self _ _,Finset.Subset.refl _⟩

def stagePoint (S : Shapes G) : Simplicial.Space (stage G S) :=
  ⟨Finsupp.single (0,1) 1,by intro w; simp only [Finsupp.single_apply]; split_ifs <;> norm_num,
    by simp,by simpa only [Finsupp.support_single _ one_ne_zero] using stage_point_face G S⟩

end

open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical
universe u v
end UniversalFInfinity.Milnor

open Set Metric Topology

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CoveringAttachments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Milnor
open Set Metric Topology Attachment
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {A : Type u} (s : A → G)

omit [DiscreteTopology G] in
lemma group_compactFundamentalSet : CompactFundamentalSet G (X := G) := by
  refine ⟨{1},isCompact_singleton,?_⟩
  intro g
  exact ⟨g,1,Set.mem_singleton _,by simp only [smul_eq_mul,mul_one]⟩

end UniversalFInfinity.Milnor

open Set Topology

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

namespace UniversalFInfinity.Simplicial
open Set Metric Topology BigOperators
open scoped Classical
universe u v
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

def restrict (S : Finset V) : PreAbstractSimplicialComplex V where
  faces := {s | s ∈ K ∧ s ⊆ S}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨(K.isRelLowerSet_faces hs.1).1,fun t hts ht =>
      ⟨K.isRelLowerSet_faces.mem_of_le hs.1 hts ht,hts.trans hs.2⟩⟩

lemma restrict_le (S : Finset V) : restrict K S ≤ K := fun _ h => h.1
instance finiteFace_restrict (S : Finset V) : Finite (Face (restrict K S)) := by
  let f : Face (restrict K S) → {s : Finset V // s ∈ S.powerset} :=
    fun s => ⟨s.1,Finset.mem_powerset.mpr s.2.2⟩
  apply Finite.of_injective f
  intro a b h
  have hh := congrArg (fun z : {s : Finset V // s ∈ S.powerset} => z.1) h
  exact Subtype.ext hh

end UniversalFInfinity.Simplicial

namespace UniversalFInfinity.Simplicial

section
open Set Metric Topology BigOperators
open scoped Classical
universe u v w
variable {V : Type u} {W : Type v} {U : Type w}

variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
variable (M : PreAbstractSimplicialComplex U)
variable (p : V × W → U) (hp : ∀ s : Face K, ∀ t : Face L, (s.1 ×ˢ t.1).image p ∈ M)

def pairMap (x : Space K) (y : Space L) : Space M := by
  let z := (tensor x.1 y.1).mapDomain p
  have hz : z.sum (fun _ r => r) = 1 := by
    rw [push_sum,tensor_sum,x.2.2.1,y.2.2.1,mul_one]
  refine ⟨z,?_,hz,?_⟩
  · exact push_nonneg p _ (fun a => mul_nonneg (x.2.1 a.1) (y.2.1 a.2))
  · apply M.isRelLowerSet_faces.mem_of_le (hp ⟨x.1.support,x.2.2.2⟩ ⟨y.1.support,y.2.2.2⟩)
    · exact Finsupp.mapDomain_support.trans (by rw [tensor_support])
    · exact support_nonempty hz

lemma pairMap_support (x : Space K) (y : Space L) :
    (pairMap K L M p hp x y).1.support ⊆ (x.1.support ×ˢ y.1.support).image p := by
  exact Finsupp.mapDomain_support.trans (by rw [tensor_support])

end

section
open Set Metric Topology BigOperators
open scoped Classical unitInterval
universe u v
variable {V : Type u} {W : Type v}

lemma tensor_single (v : V) (w : W) (a b : ℝ) :
    tensor (Finsupp.single v a) (Finsupp.single w b) = Finsupp.single (v,w) (a*b) := by
  ext p
  simp only [tensor_apply,Finsupp.single_apply]
  by_cases hv : v = p.1 <;> by_cases hw : w = p.2
  · have h : (v,w) = p := Prod.ext hv hw
    simp only [ite_eq_left hv,ite_eq_left hw,ite_eq_left h]
  · have h : (v,w) ≠ p := fun h => hw (congrArg Prod.snd h)
    simp only [ite_eq_left hv,ite_eq_right hw,ite_eq_right h,mul_zero]
  · have h : (v,w) ≠ p := fun h => hv (congrArg Prod.fst h)
    simp only [ite_eq_right hv,ite_eq_left hw,ite_eq_right h,zero_mul]
  · have h : (v,w) ≠ p := fun h => hv (congrArg Prod.fst h)
    simp only [ite_eq_right hv,ite_eq_right hw,ite_eq_right h,zero_mul]

variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
variable (p : V × V → W) (hp : ∀ s t : Face K, (s.1 ×ˢ t.1).image p ∈ L)

variable [Finite (Face K)]

omit [Finite (Face K)] in
lemma pairMap_pure {M : PreAbstractSimplicialComplex V} (q : V × V → W)
    (hq : ∀ s : Face K, ∀ t : Face M, (s.1 ×ˢ t.1).image q ∈ L)
    (x : Space K) (y : Space M) (v w : V)
    (hx : x.1 = Finsupp.single v 1) (hy : y.1 = Finsupp.single w 1) :
    (pairMap K M L q hq x y).1 = Finsupp.single (q (v,w)) 1 := by
  change (tensor x.1 y.1).mapDomain q = _
  rw [hx,hy,tensor_single,Finsupp.mapDomain_single,one_mul]

end

open Set Metric Topology BigOperators
open scoped Classical
universe u v w
variable {V : Type u} {W : Type v} {U : Type w}
lemma tensor_single_right_push (x : V →₀ ℝ) (w : W) (p : V × W → U) :
    (tensor x (Finsupp.single w 1)).mapDomain p = x.mapDomain (fun v => p (v,w)) := by
  ext b
  rw [push_apply p _ (x.support ×ˢ {w}) (by
    rw [tensor_support]
    exact Finset.product_subset_product (Finset.Subset.refl _) Finsupp.support_single_subset)]
  rw [push_apply (fun v => p (v,w)) x x.support (Finset.Subset.refl _),Finset.sum_product]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Finset.sum_singleton,tensor_apply,Finsupp.single_eq_same,mul_one]
lemma tensor_single_left_push (v : V) (y : W →₀ ℝ) (p : V × W → U) :
    (tensor (Finsupp.single v 1) y).mapDomain p = y.mapDomain (fun w => p (v,w)) := by
  ext b
  rw [push_apply p _ ({v} ×ˢ y.support) (by
    rw [tensor_support]
    exact Finset.product_subset_product Finsupp.support_single_subset (Finset.Subset.refl _))]
  rw [push_apply (fun w => p (v,w)) y y.support (Finset.Subset.refl _),Finset.sum_product,Finset.sum_singleton]
  apply Finset.sum_congr rfl
  intro w _
  simp only [tensor_apply,Finsupp.single_eq_same,one_mul]
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

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_11
variable [Group G] [Group H] [Group J]
variable (φ : G →* J) (ψ : H →* J) (hc : ∀ g h, Commute (φ g) (ψ h))

include hc in
lemma pairFace_translate (a : G) (b : H) (s : Finset (ℕ × G)) (t : Finset (ℕ × H)) :
    pairFace (fun g h => φ g*ψ h) (translate a s) (translate b t) =
      translate (φ a*ψ b) (pairFace (fun g h => φ g*ψ h) s t) := by
  ext z
  simp only [pairFace,translate,Finset.mem_image,Finset.mem_product]
  constructor
  · rintro ⟨⟨x,y⟩,⟨⟨v,hv,rfl⟩,⟨w,hw,rfl⟩⟩,rfl⟩
    refine ⟨pairVertex (fun g h => φ g*ψ h) (v,w),⟨⟨v,w⟩,⟨hv,hw⟩,rfl⟩,?_⟩
    apply Prod.ext
    · rfl
    · exact (pair_translate_vertex φ ψ hc a v.2 b w.2).symm
  · rintro ⟨z,⟨⟨v,w⟩,⟨hv,hw⟩,rfl⟩,rfl⟩
    refine ⟨⟨(v.1,a*v.2),(w.1,b*w.2)⟩,⟨⟨v,hv,rfl⟩,⟨w,hw,rfl⟩⟩,?_⟩
    apply Prod.ext
    · rfl
    · exact pair_translate_vertex φ ψ hc a v.2 b w.2

include hc in
lemma pairFace_controlled (S : Finset (Finset (ℕ × G))) (T : Finset (Finset (ℕ × H)))
    (s : Face (orbitSpan S)) (t : Face (orbitSpan T)) :
    pairFace (fun g h => φ g*ψ h) s.1 t.1 ∈ orbitSpan (productShapes φ ψ S T) := by
  obtain ⟨a,s',hs',hss⟩ := s.2.2
  obtain ⟨b,t',ht',htt⟩ := t.2.2
  refine ⟨pairFace_valid _ s.2.1 t.2.1,φ a*ψ b,pairFace (fun g h => φ g*ψ h) s' t',?_,?_⟩
  · exact Finset.mem_image.mpr ⟨(s',t'),Finset.mem_product.mpr ⟨hs',ht'⟩,rfl⟩
  · rw [←pairFace_translate φ ψ hc]
    exact pairFace_mono _ hss htt

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

noncomputable def diagramHom (e : D) (he : e * e = e) : V →* (ModelAlgebra K D V)ˣ where
  toFun v :=
    { val := diagramElement e v
      inv := diagramElement e v⁻¹
      val_inv := by rw [diagramElement_mul e he, mul_inv_cancel, diagramElement_one]
      inv_val := by rw [diagramElement_mul e he, inv_mul_cancel, diagramElement_one] }
  map_one' := Units.ext (diagramElement_one e)
  map_mul' v w := Units.ext (diagramElement_mul e he v w).symm

@[simp]
lemma diagramHom_val (e : D) (he : e * e = e) (v : V) :
    (diagramHom (K := K) e he v : ModelAlgebra K D V) = diagramElement e v := rfl

@[simp]
lemma diagramHom_identity_val (v : V) :
    (diagramHom (K := K) (1 : D) (one_mul _) v : ModelAlgebra K D V) =
      Algebra.TensorProduct.includeRight (MonoidAlgebra.of K V v) := by
  simp [diagramElement]

end

namespace TwoEnvelope

variable {K₂ K₃ D₂ D₃ : Type}
variable [Field K₂] [Field K₃] [Ring D₂] [Ring D₃]
variable [Algebra K₂ D₂] [Algebra K₃ D₃]
variable (P₂ : FiniteIdempotentSystem D₂) (P₃ : FiniteIdempotentSystem D₃)

variable (V : Type) [Group V]

abbrev ModelGroup := (ModelAlgebra K₃ D₃ (ModelAlgebra K₂ D₂ V)ˣ)ˣ

noncomputable def family : Index P₂ P₃ → V →* ModelGroup (K₂ := K₂) (K₃ := K₃)
    (D₂ := D₂) (D₃ := D₃) V
  | .inl e =>
      (diagramHom (K := K₃) (1 : D₃) (one_mul _)).comp
        (diagramHom (K := K₂) e.val (P₂.isIdempotent e))
  | .inr e =>
      (diagramHom (K := K₃) e.val (P₃.isIdempotent e)).comp
        (diagramHom (K := K₂) (1 : D₂) (one_mul _))

end TwoEnvelope
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

namespace UniversalFInfinity.SphereCube
open Set Metric Topology Cellular
open scoped Topology.Homotopy
universe u v
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y]

def rimSphere (n : ℕ) : C(Cylinder.Rim n,Sphere (n+1)) := by
  refine ⟨fun p => ⟨(diskCons p.1.2 p.1.1).1,?_⟩,?_⟩
  · rcases p.2 with h | h
    · rw [h]; exact cons_zero_mem_sphere p.1.2
    · exact cons_mem_sphere_of_boundary ⟨p.1.2.1,h⟩ p.1.1
  · exact (continuous_subtype_val.comp
      (continuous_diskCons.comp ((continuous_snd.comp continuous_subtype_val).prodMk
        (continuous_fst.comp continuous_subtype_val)))).subtype_mk _

def rimSide (n : ℕ) : C(Sphere n × unitInterval,Cylinder.Rim n) :=
  ⟨fun p => ⟨(p.2,boundary n p.1),Or.inr p.1.2⟩,
    (continuous_snd.prodMk ((continuous_boundary n).comp continuous_fst)).subtype_mk _⟩

def rimBottom (n : ℕ) : C(Disk n,Cylinder.Rim n) :=
  ⟨fun x => ⟨(0,x),Or.inl rfl⟩,(continuous_const.prodMk continuous_id).subtype_mk _⟩

def top (n : ℕ) : C(Disk n,Sphere (n+1)) :=
  ⟨fun d => ⟨(diskCons d 1).1,cons_one_mem_sphere d⟩,
    (continuous_subtype_val.comp (continuous_diskCons.comp
      (continuous_id.prodMk continuous_const))).subtype_mk _⟩

variable (f : C(Sphere (n+1),Y)) (y : Y)
variable (K : (f.comp (rimSphere n)).Homotopy (ContinuousMap.const _ y))

def edgeTrace : C(unitInterval × Sphere n,Y) :=
  ⟨fun p => K (p.1,rimSide n (p.2,1)),K.continuous.comp
    (continuous_fst.prodMk ((rimSide n).continuous.comp
      (continuous_snd.prodMk continuous_const)))⟩

lemma edgeTrace_zero (s : Sphere n) : edgeTrace f y K (0,s) = (f.comp (top n)) (boundary n s) := by
  change K (0,rimSide n (s,1)) = _
  rw [ContinuousMap.Homotopy.apply_zero]
  rfl

def sidePaths : C(Sphere n,C(unitInterval,C(unitInterval,Y))) :=
  (⟨fun p : (Sphere n × unitInterval) × unitInterval => K (p.2,rimSide n p.1),
    K.continuous.comp (continuous_snd.prodMk ((rimSide n).continuous.comp continuous_fst))⟩ :
      C((Sphere n × unitInterval) × unitInterval,Y)).curry.curry

def bottomPaths : C(Disk n,C(unitInterval,Y)) :=
  (⟨fun p : Disk n × unitInterval => K (p.2,rimBottom n p.1),
    K.continuous.comp (continuous_snd.prodMk ((rimBottom n).continuous.comp continuous_fst))⟩ :
      C(Disk n × unitInterval,Y)).curry

lemma cons_tail_time (x : Disk (n+1)) : diskCons (diskTail x) (diskTime x) = x := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => rfl) i
  change 2*((x.1 0+1)/2)-1 = x.1 0
  ring

end UniversalFInfinity.SphereCube

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

namespace UniversalFInfinity.SphereCube

section
open Set Metric Topology Cellular
open scoped Topology.Homotopy
universe u v
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y]

lemma bottom_repr (s : Sphere (n+1)) (h : s.1 0 = -1) :
    rimSphere n (rimBottom n (diskTail (boundary (n+1) s))) = s := by
  apply Subtype.ext
  change (diskCons (diskTail (boundary (n+1) s)) 0).1 = s.1
  exact (congrArg (fun t => (diskCons (diskTail (boundary (n+1) s)) t).1)
    (faceTime_eq_zero s h)).symm.trans (congrArg Subtype.val (cons_tail_time (boundary (n+1) s)))
lemma top_repr (s : Sphere (n+1)) (h : s.1 0 = 1) :
    top n (diskTail (boundary (n+1) s)) = s := by
  apply Subtype.ext
  change (diskCons (diskTail (boundary (n+1) s)) 1).1 = s.1
  exact (congrArg (fun t => (diskCons (diskTail (boundary (n+1) s)) t).1)
    (faceTime_eq_one s h)).symm.trans (congrArg Subtype.val (cons_tail_time (boundary (n+1) s)))
lemma side_repr (s : Sphere (n+1)) (h : (diskTail (boundary (n+1) s)).1 ∈ sphere 0 1) :
    rimSphere n (rimSide n (faceSphere ⟨s,h⟩,faceTime none ⟨s,h⟩)) = s := by
  apply Subtype.ext
  change (diskCons (diskTail (boundary (n+1) s)) (diskTime (boundary (n+1) s))).1 = s.1
  exact congrArg Subtype.val (cons_tail_time (boundary (n+1) s))

variable (F : C(Sphere (n+1),Y)) (g : C(Disk n,Y)) (y : Y)
variable (hr : ∀ x, F (rimSphere n x) = y) (ht : ∀ x, F (top n x) = g x)
variable (H : g.Homotopy (ContinuousMap.const _ y))
variable (hb : ∀ t s, H (t,boundary n s) = y)

def nullTopPaths : C(Disk n,C(unitInterval,Y)) :=
  (H.toContinuousMap.comp ContinuousMap.prodSwap).curry

def nullSpherePaths : C(Sphere (n+1),C(unitInterval,Y)) :=
  cylinderBoundaryMap (ContinuousMap.const _ (ContinuousMap.const _ (ContinuousMap.const _ y)))
    ((ContinuousMap.const _ (ContinuousMap.const _ y)).prodMk (nullTopPaths g y H)) (by
      intro s
      apply Prod.ext
      · rfl
      · apply ContinuousMap.ext
        intro t
        exact (hb t s).symm)

include hr ht in
lemma nullSphere_zero (s : Sphere (n+1)) : nullSpherePaths g y H hb s 0 = F s := by
  rcases sphere_split s with h | h | h
  · rw [nullSpherePaths,cylinderBoundaryMap_face _ _ _ (some false) ⟨s,h⟩]
    change y = F s
    rw [← bottom_repr s h,hr]
  · rw [nullSpherePaths,cylinderBoundaryMap_face _ _ _ (some true) ⟨s,h⟩]
    change H (0,diskTail (boundary (n+1) s)) = F s
    rw [ContinuousMap.Homotopy.apply_zero,← ht,top_repr s h]
  · rw [nullSpherePaths,cylinderBoundaryMap_face _ _ _ none ⟨s,h⟩]
    change y = F s
    rw [← side_repr s h,hr]

lemma nullSphere_one (s : Sphere (n+1)) : nullSpherePaths g y H hb s 1 = y := by
  rcases sphere_split s with h | h | h
  · rw [nullSpherePaths,cylinderBoundaryMap_face _ _ _ (some false) ⟨s,h⟩]; rfl
  · rw [nullSpherePaths,cylinderBoundaryMap_face _ _ _ (some true) ⟨s,h⟩]
    exact H.apply_one _
  · rw [nullSpherePaths,cylinderBoundaryMap_face _ _ _ none ⟨s,h⟩]; rfl

def nullSphere : F.Homotopy (ContinuousMap.const _ y) where
  toFun p := nullSpherePaths g y H hb p.2 p.1
  continuous_toFun := continuous_eval.comp (((nullSpherePaths g y H hb).continuous.comp continuous_snd).prodMk continuous_fst)
  map_zero_left s := nullSphere_zero F g y hr ht H hb s
  map_one_left s := nullSphere_one g y H hb s

end

open scoped Topology Topology.Homotopy
universe u v
end UniversalFInfinity.SphereCube

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
open Set Topology AscendingTorus
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)

instance cosetTopology : TopologicalSpace (Coset f) := ⊥
instance instDiscreteTopologyCoset : DiscreteTopology (Coset f) := ⟨rfl⟩

local notation "hf" => (Fact.out : Function.Injective f)
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

namespace UniversalFInfinity.TorusGeometry
open Set Topology Milnor AscendingTorus
open scoped unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)

def forwardOffset : ℕ → Coset f → U
  | 0,_ => 1
  | n+1,c => cosetOffset f ((next f)^[n] c) * f (forwardOffset n c)
end UniversalFInfinity.TorusGeometry

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
open Set Topology Milnor AscendingTorus Cellular
open scoped Classical unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)

abbrev idx (n : ℕ) (c : Coset f) := (next f)^[n] c
lemma idx_next (n : ℕ) (c : Coset f) : idx f n (next f c) = next f (idx f n c) :=
  (Function.iterate_succ_apply _ _ _).symm.trans (Function.iterate_succ_apply' _ _ _)

variable (S T : Shapes U) (n : ℕ)
variable (z : Milnor.Stage U T)

variable (Z : Shapes U) (e : ℕ)
variable (w : Milnor.Stage U Z)

def finalIndex (n e : ℕ) (c : Coset f) := idx f e (idx f n c)
lemma finalIndex_next (n e : ℕ) (c : Coset f) : finalIndex f n e (next f c) = next f (finalIndex f n e c) := by
  simp only [finalIndex,idx_next]

end

open Set Topology Milnor AscendingTorus
open scoped Classical unitInterval
universe u
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

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_16
lemma mixed_face (φ ψ : G → H) (s : Face (complex G)) :
    s.1.image (fun v => (evenLayer v.1,φ v.2)) ∪ s.1.image (fun v => (oddLayer v.1,ψ v.2)) ∈ complex H := by
  have h1 := map_face φ evenLayer evenLayer_injective s
  have h2 := map_face ψ oddLayer oddLayer_injective s
  refine ⟨h1.1.mono Finset.subset_union_left,?_⟩
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact h1.2 hx hy hxy
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    exact False.elim (even_ne_odd a.1 b.1 hxy)
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    exact False.elim (even_ne_odd b.1 a.1 hxy.symm)
  · exact h2.2 hx hy hxy

end UniversalFInfinity.Milnor

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

open Set Metric Topology
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)] [∀ n, T1Space (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
variable (hf : ∀ i j h, IsClosedEmbedding (f i j h))

def EventuallyFills : Prop := ∀ n k (a : C(Cellular.Sphere n,X k)),
  ∃ (j : ℕ) (hkj : k ≤ j) (b : C(Cellular.Disk n,X j)),
    ∀ x, b (Cellular.boundary n x) = f k j hkj (a x)

end UniversalFInfinity.TopologicalTower

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

lemma transportedMap_continuousOn_symm (n : ℕ) (i : RelCWComplex.cell C n) :
    ContinuousOn (transportedMap hf n i).symm (transportedMap hf n i).target := by
  let e := hf.isEmbedding.toPartialHomeomorph f
  change ContinuousOn (fun y => (RelCWComplex.map n i).symm (e.symm y))
    (e.target ∩ e.symm ⁻¹' (RelCWComplex.map n i).target)
  exact (RelCWComplex.continuousOn_symm n i).comp
    (e.continuousOn_symm.mono Set.inter_subset_left) (fun _ h => h.2)

end

section
open Set Metric Topology
universe u v
variable {X : Type u} [TopologicalSpace X] [T2Space X] [Nonempty X]
  [CWComplex (univ : Set X)]

abbrev liftMap (n : ℕ) (i : ULift.{v} (RelCWComplex.cell (univ : Set X) n)) :=
  transportedMap (Homeomorph.ulift.symm : X ≃ₜ ULift.{v} X).isClosedEmbedding n i.down

@[instance_reducible]
def liftCW : CWComplex (univ : Set (ULift.{v} X)) where
  cell n := ULift.{v} (RelCWComplex.cell (univ : Set X) n)
  map := liftMap
  source_eq n i := transportedMap_source _ n i.down
  continuousOn n i := transportedMap_continuousOn _ n i.down
  continuousOn_symm n i := transportedMap_continuousOn_symm _ n i.down
  pairwiseDisjoint' := by
    intro p _ q _ hpq
    change Disjoint (liftMap p.1 p.2 '' ball 0 1) (liftMap q.1 q.2 '' ball 0 1)
    rw [transportedMap_image,transportedMap_image]
    apply (CWComplex.disjoint_openCell_of_ne ?_).image ULift.up_injective.injOn
      (Set.subset_univ _) (Set.subset_univ _)
    intro h
    apply hpq
    have hf : Function.Injective (fun p : Σ n, ULift.{v} (RelCWComplex.cell (univ : Set X) n) =>
        (⟨p.1,p.2.down⟩ : Σ n, RelCWComplex.cell (univ : Set X) n)) := by
      rintro ⟨n,⟨i⟩⟩ ⟨m,⟨j⟩⟩ h
      cases h
      rfl
    exact hf h
  mapsTo' := by
    intro n i
    obtain ⟨I,hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell n i.down
    refine ⟨fun m => (I m).map ⟨ULift.up,ULift.up_injective⟩,?_⟩
    intro x hx
    have h := hI (show RelCWComplex.map n i.down x ∈ CWComplex.cellFrontier n i.down from ⟨x,hx,rfl⟩)
    simp only [Set.mem_iUnion] at h
    obtain ⟨m,hm,j,hj,hx⟩ := h
    refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hm,Set.mem_iUnion.mpr
      ⟨ULift.up j,Set.mem_iUnion.mpr ⟨Finset.mem_map.mpr ⟨j,hj,rfl⟩,?_⟩⟩⟩⟩
    rw [transportedMap_image]
    exact ⟨_,hx,rfl⟩
  closed' := by
    intro A _ hclosed
    have hpre : IsClosed (ULift.up ⁻¹' A : Set X) := by
      apply (CWComplex.closed (univ : Set X) _ (Set.subset_univ _)).mpr
      intro n i
      have h := (hclosed n (ULift.up i)).preimage continuous_uliftUp
      rw [transportedMap_image,Set.preimage_inter] at h
      change IsClosed (ULift.up ⁻¹' A ∩ ULift.up ⁻¹'
        (ULift.up '' (RelCWComplex.map n i '' closedBall 0 1))) at h
      rw [Set.preimage_image_eq _ ULift.up_injective] at h
      exact h
    exact ULift.isClosed_iff.mpr hpre
  union' := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    intro y _
    have hy : y.down ∈ ⋃ n, ⋃ i : RelCWComplex.cell (univ : Set X) n, CWComplex.closedCell n i := by
      rw [CWComplex.union]
      trivial
    simp only [Set.mem_iUnion] at hy
    obtain ⟨n,i,hi⟩ := hy
    refine Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨ULift.up i,?_⟩⟩
    rw [transportedMap_image]
    exact ⟨y.down,hi,rfl⟩
end
open Set Topology
universe u v
end UniversalFInfinity.UniverseTransport

end

end OAI
end


