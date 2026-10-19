-- Prove2me | Definitions.Def_OAIQWUFI008
-- name    : OAIQWUFI008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:56:41.399051+00:00
-- url     : https://prove2.me/theorems/1fd72ba8-7b1e-464e-b0ac-71c15f33daf0
-- title:
--   OpenAI universal F∞ group split: definitions bundle 9 of 9
-- statement:
--   Definitions bundle 9 of 9 of the split of OpenAI's proof that a single group of type $F_\infty$ contains every finitely presented group (OpenAI, *A universal group of type F∞*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0). It holds OpenAI's Lean definitions, structures and instances from the modules listed below, ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas those definitions use in their bodies: several of OpenAI's definitions choose witnesses of existence theorems (for example the Milnor ghost maps `Milnor.ghostMap`, chosen from `uniform_diagram_sphere_ghost`), so the bundle has to contain those proofs.
--
--   It imports bundles 7 and 8 of this split (`OAIQWUFI006`, `OAIQWUFI007`).
--
--   Modules: `CellularApproximation.lean`, `ControlledHomotopies.lean`, `CoveringAttachments.lean`, `Cylinders.lean`, `HomotopyProducts.lean`, `Milnor.lean`, `MilnorControl.lean`, `MilnorProducts.lean`, `Simplicial.lean`, `SimplicialProducts.lean`, `SphereHomotopies.lean`, `TopologicalTowers.lean`, `TorusBundles.lean`, `TorusHomotopies.lean`, `TorusSpheres.lean`, `TowerCoverings.lean`, `TreeGeometry.lean`, `UniversalPresentation.lean`.
--
--   The theorems the definitions do not need are proved in the solutions of this split. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/UniversalGroup at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWUFI006
import Definitions.Def_OAIQWUFI007

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

noncomputable def generator : Alphabet → V rels
  | Sum.inl false => CountableOvergroup.a _
  | Sum.inl true => CountableOvergroup.p _
  | Sum.inr _ => CountableOvergroup.t _

lemma lift_substitute : (FreeGroup.lift (generator rels)).comp substitute =
    (CountableOvergroup.embed (PresentedGroup.of (rels := rels))).comp
      (PresentedGroup.mk rels) := by
  apply FreeGroup.ext_hom
  intro i
  simp only [MonoidHom.comp_apply,substitute,FreeGroup.lift_apply_of,
    map_mul,map_inv,conjugate,map_pow,A,P,T,generator]
  exact (CountableOvergroup.generator_formula _ i).symm

lemma substituted_relation (r : Words) (hr : r ∈ substitute '' rels) :
    FreeGroup.lift (generator rels) r = 1 := by
  obtain ⟨r,hr,rfl⟩ := hr
  change ((FreeGroup.lift (generator rels)).comp substitute) r = 1
  rw [lift_substitute,MonoidHom.comp_apply,PresentedGroup.one_of_mem hr,map_one]

noncomputable def toV : Q rels →* V rels :=
  PresentedGroup.toGroup (substituted_relation rels)

end UniversalFInfinity.ThreePresentation

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
open Set Metric Topology BigOperators
open scoped Classical unitInterval
universe u v
variable {V : Type u} {W : Type v}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)

variable (f g : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) (hg : ∀ s : Face K, s.1.image g ∈ L)
variable (hfg : ∀ s : Face K, s.1.image f ∪ s.1.image g ∈ L)

lemma straightHomotopy_fixed (x : Space K) (h : map K L f hf x = map K L g hg x) (t : I) :
    straightHomotopy K L f g hf hg hfg (t,x) = map K L f hf x := by
  apply Subtype.ext
  change (1-(t:ℝ)) • (map K L f hf x).1 + (t:ℝ) • (map K L g hg x).1 = (map K L f hf x).1
  rw [←h,←add_smul,sub_add_cancel,one_smul]
end
open Set Metric Topology BigOperators
open scoped Classical
universe u
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
attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEq_solutions
variable (G : Type u)

variable {G} {H : Type v}

lemma map_id (x : Space G) : map id id Function.injective_id x = x := by
  apply Subtype.ext
  exact Finsupp.mapDomain_id

end UniversalFInfinity.Milnor

end

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

open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_3
variable (φ : G →* H) (S : Finset (Finset (ℕ × G))) (α β : ℕ → ℕ)
variable (hα : Function.Injective α) (hβ : Function.Injective β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)

def relayerLeftMap := mapC (orbitSpan S) (orbitSpan (relayerTarget φ S α β))
  (vertexMap φ α) (relayerLeftMapValid φ S α β hα hα0)
def relayerRightMap := mapC (orbitSpan S) (orbitSpan (relayerTarget φ S α β))
  (vertexMap φ β) (relayerRightMapValid φ S α β hβ hβ0)
def relayerFreshMap := mapC (orbitSpan S) (orbitSpan (relayerTarget φ S α β))
  (vertexMap φ (relayerFresh S α β)) (relayerFreshMapValid φ S α β hα hα0)

def relayerLeftHomotopy : (relayerLeftMap φ S α β hα hα0).Homotopy (relayerFreshMap φ S α β hα hα0) :=
  straightHomotopy _ _ _ _ _ _ (relayerLeftValid φ S α β hα hα0)
def relayerRightHomotopy : (relayerRightMap φ S α β hβ hβ0).Homotopy (relayerFreshMap φ S α β hα hα0) :=
  straightHomotopy _ _ _ _ _ _ (relayerRightValid φ S α β hβ hβ0)

def relayerHomotopy : (relayerLeftMap φ S α β hα hα0).Homotopy (relayerRightMap φ S α β hβ hβ0) :=
  (relayerLeftHomotopy φ S α β hα hα0).trans (relayerRightHomotopy φ S α β hα hβ hα0 hβ0).symm

lemma relayerLeftPure (x : Simplicial.Space (orbitSpan S)) (g : G) (hx : x.1 = Finsupp.single (0,g) 1) :
    relayerLeftMap φ S α β hα hα0 x = relayerFreshMap φ S α β hα hα0 x := by
  apply Subtype.ext
  change x.1.mapDomain (vertexMap φ α) = x.1.mapDomain (vertexMap φ (relayerFresh S α β))
  rw [hx,Finsupp.mapDomain_single,Finsupp.mapDomain_single]
  congr 1
  exact Prod.ext (hα0.trans (fresh_zero (max (shapeBound S α) (shapeBound S β))).symm) rfl
lemma relayerRightPure (x : Simplicial.Space (orbitSpan S)) (g : G) (hx : x.1 = Finsupp.single (0,g) 1) :
    relayerRightMap φ S α β hβ hβ0 x = relayerFreshMap φ S α β hα hα0 x := by
  apply Subtype.ext
  change x.1.mapDomain (vertexMap φ β) = x.1.mapDomain (vertexMap φ (relayerFresh S α β))
  rw [hx,Finsupp.mapDomain_single,Finsupp.mapDomain_single]
  congr 1
  exact Prod.ext (hβ0.trans (fresh_zero (max (shapeBound S α) (shapeBound S β))).symm) rfl

lemma relayerLeftHomotopy_fixed (x : Simplicial.Space (orbitSpan S)) (g : G)
    (hx : x.1 = Finsupp.single (0,g) 1) (t : I) :
    relayerLeftHomotopy φ S α β hα hα0 (t,x) = relayerLeftMap φ S α β hα hα0 x :=
  straightHomotopy_fixed _ _ _ _ _ _ (relayerLeftValid φ S α β hα hα0) x
    (relayerLeftPure φ S α β hα hα0 x g hx) t
lemma relayerRightHomotopy_fixed (x : Simplicial.Space (orbitSpan S)) (g : G)
    (hx : x.1 = Finsupp.single (0,g) 1) (t : I) :
    relayerRightHomotopy φ S α β hα hβ hα0 hβ0 (t,x) = relayerRightMap φ S α β hβ hβ0 x :=
  straightHomotopy_fixed _ _ _ _ _ _ (relayerRightValid φ S α β hβ hβ0) x
    (relayerRightPure φ S α β hα hβ hα0 hβ0 x g hx) t

theorem relayerHomotopy_fixed (x : Simplicial.Space (orbitSpan S)) (g : G)
    (hx : x.1 = Finsupp.single (0,g) 1) (t : I) :
    relayerHomotopy φ S α β hα hβ hα0 hβ0 (t,x) = relayerLeftMap φ S α β hα hα0 x := by
  rw [relayerHomotopy,ContinuousMap.Homotopy.trans_apply]
  split
  · exact relayerLeftHomotopy_fixed φ S α β hα hα0 x g hx _
  · rw [ContinuousMap.Homotopy.symm_apply]
    exact (relayerRightHomotopy_fixed φ S α β hα hβ hα0 hβ0 x g hx _).trans
      ((relayerRightPure φ S α β hα hβ hα0 hβ0 x g hx).trans
        (relayerLeftPure φ S α β hα hα0 x g hx).symm)
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

def mapHom [DecidableEq N] [Nonempty N] (f : C(X,Y)) (hf : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := map f hf
  map_one' := by
    change Quotient.mk' (loopMap f hf GenLoop.const) = Quotient.mk' GenLoop.const
    exact congrArg Quotient.mk' (loopMap_const f hf)
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    have h₁ := HomotopyGroup.mul_spec (i := Classical.arbitrary N) (p := p) (q := q)
    have h₂ := HomotopyGroup.mul_spec (i := Classical.arbitrary N)
      (p := loopMap f hf p) (q := loopMap f hf q)
    exact (congrArg (map f hf) h₁).trans
      ((congrArg Quotient.mk' (loopMap_transAt (Classical.arbitrary N) f hf q p)).trans h₂.symm)

lemma map_id (a : HomotopyGroup N X x) : map (y := x) (ContinuousMap.id X) rfl a = a := by
  induction a using Quotient.inductionOn with | h p =>
  exact congrArg Quotient.mk' (by ext t; rfl)

lemma map_const [DecidableEq N] [Nonempty N] (a : HomotopyGroup N X x) :
    map (ContinuousMap.const X y) rfl a = 1 := by
  induction a using Quotient.inductionOn with | h p =>
  rfl

variable {Z : Type*} [TopologicalSpace Z] {z : Z}

lemma product_ext (a b : HomotopyGroup N (X × Y) (x,y))
    (h₁ : map ((ContinuousMap.fst : C(X × Y,X))) rfl a = map ((ContinuousMap.fst : C(X × Y,X))) rfl b)
    (h₂ : map ((ContinuousMap.snd : C(X × Y,Y))) rfl a = map ((ContinuousMap.snd : C(X × Y,Y))) rfl b) : a = b := by
  induction a using Quotient.inductionOn with | h p =>
  induction b using Quotient.inductionOn with | h q =>
  apply Quotient.sound
  have hh := pair_homotopic (Quotient.exact h₁) (Quotient.exact h₂)
  exact hh

lemma diagonal_split [DecidableEq N] [Nonempty N] (a : HomotopyGroup N X x) :
    map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.id X)) rfl a =
      (map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.const X x)) rfl a) *
      (map (y := (x,x)) ((ContinuousMap.const X x).prodMk (ContinuousMap.id X)) rfl a) := by
  apply product_ext
  · change mapHom ((ContinuousMap.fst : C(X × X,X))) rfl _ = mapHom ((ContinuousMap.fst : C(X × X,X))) rfl _
    rw [map_mul]
    change map (y := x) ContinuousMap.fst rfl
        (map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.id X)) rfl a) =
      map (y := x) ContinuousMap.fst rfl
        (map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.const X x)) rfl a) *
      map (y := x) ContinuousMap.fst rfl
        (map (y := (x,x)) ((ContinuousMap.const X x).prodMk (ContinuousMap.id X)) rfl a)
    calc
      _ = map (y := x) (ContinuousMap.id X) rfl a := map_comp _ _ _ _ a
      _ = map (y := x) (ContinuousMap.id X) rfl a *
          map (y := x) (ContinuousMap.const X x) rfl a :=
        (map_id a).trans (((congrArg₂ (fun left right : HomotopyGroup N X x => left * right)
          (map_id a) (map_const (y := x) a)).trans
          (mul_one a)).symm)
      _ = _ := congrArg₂ (fun left right : HomotopyGroup N X x => left * right)
        (map_comp (y := (x,x)) (z := x)
          ((ContinuousMap.id X).prodMk (ContinuousMap.const X x)) rfl
          ContinuousMap.fst rfl a).symm
        (map_comp (y := (x,x)) (z := x)
          ((ContinuousMap.const X x).prodMk (ContinuousMap.id X)) rfl
          ContinuousMap.fst rfl a).symm
  · change mapHom ((ContinuousMap.snd : C(X × X,X))) rfl _ = mapHom ((ContinuousMap.snd : C(X × X,X))) rfl _
    rw [map_mul]
    change map (y := x) ContinuousMap.snd rfl
        (map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.id X)) rfl a) =
      map (y := x) ContinuousMap.snd rfl
        (map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.const X x)) rfl a) *
      map (y := x) ContinuousMap.snd rfl
        (map (y := (x,x)) ((ContinuousMap.const X x).prodMk (ContinuousMap.id X)) rfl a)
    calc
      _ = map (y := x) (ContinuousMap.id X) rfl a := map_comp _ _ _ _ a
      _ = map (y := x) (ContinuousMap.const X x) rfl a *
          map (y := x) (ContinuousMap.id X) rfl a :=
        (map_id a).trans (((congrArg₂ (fun left right : HomotopyGroup N X x => left * right)
          (map_const (y := x) a) (map_id a)).trans
          (one_mul a)).symm)
      _ = _ := congrArg₂ (fun left right : HomotopyGroup N X x => left * right)
        (map_comp (y := (x,x)) (z := x)
          ((ContinuousMap.id X).prodMk (ContinuousMap.const X x)) rfl
          ContinuousMap.snd rfl a).symm
        (map_comp (y := (x,x)) (z := x)
          ((ContinuousMap.const X x).prodMk (ContinuousMap.id X)) rfl
          ContinuousMap.snd rfl a).symm

theorem product_additivity [DecidableEq N] [Nonempty N] (F : C(X × X,Y))
    (hF : F (x,x) = y) (a : HomotopyGroup N X x) :
    map (F.comp ((ContinuousMap.id X).prodMk (ContinuousMap.id X))) hF a =
      map (F.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X x))) hF a *
      map (F.comp ((ContinuousMap.const X x).prodMk (ContinuousMap.id X))) hF a := by
  have h := map_comp (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.id X)) rfl F hF a
  rw [← h,diagonal_split]
  change mapHom (N := N) F hF (_ * _) = _
  rw [map_mul]
  exact congrArg₂ (· * ·) (map_comp _ _ _ _ a) (map_comp _ _ _ _ a)
end
open scoped Topology Topology.Homotopy
universe u v w
variable {N : Type u} {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y}
lemma map_eq_of_homotopy (f g : C(X,Y)) (hf : f x = y) (hg : g x = y)
    (H : f.Homotopy g) (hH : ∀ t, H (t,x) = y) (a : HomotopyGroup N X x) :
    map f hf a = map g hg a := by
  induction a using Quotient.inductionOn with | h p =>
  apply Quotient.sound
  refine ⟨{ toHomotopy := H.compContinuousMap p.1,prop' := ?_ }⟩
  intro t z hz
  change H (t,p z) = f (p z)
  rw [GenLoop.boundary p z hz,hH,hf]
end UniversalFInfinity.HomotopyFunctor
namespace UniversalFInfinity.Milnor

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical Topology.Homotopy
universe u v
variable (G : Type u) [Group G]

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_4
variable (N : Type v) [DecidableEq N] [Nonempty N]
def stageHom (S T : Shapes G) (h : S ⊆ T) :
    HomotopyGroup N (Simplicial.Space (stage G S)) (stagePoint G S) →*
      HomotopyGroup N (Simplicial.Space (stage G T)) (stagePoint G T) :=
  HomotopyFunctor.mapHom (stageIncl G S T h) rfl

instance instDirectedSystemShapesHomotopyGroupElemFinsuppProdNatRealSpaceStageStagePointCoeMonoidHomStageHom : DirectedSystem (fun S : Shapes G => HomotopyGroup N (Simplicial.Space (stage G S)) (stagePoint G S))
    (fun S T h => stageHom G N S T h) where
  map_self _ a := by
    exact HomotopyFunctor.map_id a
  map_map _ _ _ h₁ h₂ a := by
    exact HomotopyFunctor.map_comp _ _ _ _ a

end

open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical
universe u v
variable (G : Type u) [Group G]

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_6
variable {X : Type v} [TopologicalSpace X] [MulAction G X]

lemma equivariant_controlled (hX : CompactFundamentalSet G (X := X))
    (f : C(X,Space G)) (hf : ∀ (g : G) x, f (g • x) = g • f x) :
    ∃ S : Shapes G, Set.range f ⊆ Set.range (stageFull G S) := by
  obtain ⟨K,hK,hcov⟩ := hX
  obtain ⟨S,hS⟩ := compact_orbit_controlled G (hK.image f.continuous)
  refine ⟨S,?_⟩
  rintro _ ⟨x,rfl⟩
  obtain ⟨g,y,hy,rfl⟩ := hcov x
  rw [hf]
  exact hS g ⟨f y,⟨y,hy,rfl⟩,rfl⟩

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

lemma graph_compactFundamentalSet [Finite A] : CompactFundamentalSet G (X := Cayley.Graph s) :=
  Attachment.compactFundamentalSet (Cayley.attaching s) group_compactFundamentalSet

variable (rels : Set (FreeGroup A)) (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
lemma presentation_compactFundamentalSet [Finite A] (hrels : rels.Finite) :
    CompactFundamentalSet G (X := Cayley.PresentationCover s rels hrel) := by
  let := hrels.to_subtype
  exact Attachment.compactFundamentalSet (Cayley.relatorAttaching s rels hrel)
    (graph_compactFundamentalSet s)

lemma presentation_equivariant_map :
    ∃ f : C(Cayley.PresentationCover s rels hrel,Space G),
      ∀ (g : G) x, f (g • x) = g • f x := by
  let f₀ : C(G,Space G) := ⟨fun g => g • vertex (0,1),continuous_of_discreteTopology⟩
  have hf₀ (g h : G) : f₀ (g • h) = g • f₀ h := mul_smul g h _
  obtain ⟨f₁,_,hf₁⟩ := Attachment.exists_equivariant_extension (Cayley.attaching s) f₀ hf₀
    (sphereFillable (1:G))
  obtain ⟨f₂,_,hf₂⟩ := Attachment.exists_equivariant_extension (Cayley.relatorAttaching s rels hrel)
    f₁ hf₁ (sphereFillable (1:G))
  exact ⟨f₂,hf₂⟩

end UniversalFInfinity.Milnor

open Set Topology

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

namespace UniversalFInfinity.SphereTopology
open Set Metric Topology
universe u
variable {Y : Type u} [TopologicalSpace Y]
lemma fill_one [PathConnectedSpace Y] (a : C(Cellular.Sphere 1,Y)) :
    ∃ e : C(Cellular.Disk 1,Y), ∀ x, e (Cellular.boundary 1 x) = a x := by
  let p := (PathConnectedSpace.joined (a Cayley.minus) (a Cayley.plus)).somePath
  let e : C(Cellular.Disk 1,Y) := p.toContinuousMap.comp ⟨Cayley.edgeTime,Cayley.continuous_edgeTime⟩
  refine ⟨e,?_⟩
  intro x
  obtain rfl|rfl := Cayley.sphere_one_eq x
  · change p (Cayley.edgeTime (Attachment.boundary 1 Cayley.minus)) = _
    rw [Cayley.edgeTime_minus,p.source]
  · change p (Cayley.edgeTime (Attachment.boundary 1 Cayley.plus)) = _
    rw [Cayley.edgeTime_plus,p.target]
end UniversalFInfinity.SphereTopology

namespace UniversalFInfinity.Milnor

section
open Set Metric Topology Cellular
universe u
variable {G : Type u} [Group G]
variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u} [∀ m,Finite (ι m)]
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)

lemma controlled_skeleton_homotopy (d : ℕ) (a b : C(Skeleton (univ : Set X) d,Space G))
    (H : a.Homotopy b)
    (hH : ∀ (g : G) t x, H (t,skeletonTranslate σ hσ d g x) = g • H (t,x)) :
    ∃ S : Shapes G, Set.range H ⊆ Set.range (stageFull G S) := by
  obtain ⟨K,hK,hcov⟩ := skeleton_compact_representatives σ hσ d
  obtain ⟨S,hS⟩ := compact_orbit_controlled G ((isCompact_univ.prod hK).image H.continuous)
  refine ⟨S,?_⟩
  rintro _ ⟨⟨t,x⟩,rfl⟩
  obtain ⟨g,y,hy,rfl⟩ := hcov x
  rw [hH]
  exact hS g ⟨H (t,y),⟨(t,y),⟨Set.mem_univ _,hy⟩,rfl⟩,rfl⟩

end
open Set Metric Topology Cellular
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {A : Type u} [Finite A] (s : A → G)
variable (rels : Set (FreeGroup A)) (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)

include hrel in

lemma uniform_low_connectivity (hrels : rels.Finite)
    (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) (S : Shapes G) :
    ∃ (T : Shapes G) (hST : S ⊆ T), ∀ n : ℕ, n = 1 ∨ n = 2 →
      ∀ a : C(Sphere n,Stage G S), ∃ d : C(Disk n,Stage G T),
        ∀ x, d (boundary n x) = stageIncl G S T hST (a x) := by
  classical
  let Z := Cayley.PresentationCover s rels hrel
  let : PathConnectedSpace Z := Cayley.presentationCover_pathConnected s rels hrel hs
  let : CWComplex (univ : Set (Stage G S)) := stageEquivariantCW G S
  let σ : ∀ n, (G × CellOrbits G S n) ≃ RelCWComplex.cell (univ : Set (Stage G S)) n :=
    fun _ => Equiv.refl _
  have hσ : ∀ n (g h : G) (i : CellOrbits G S n) (x : Fin n → ℝ),
    RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x := by
    intro n g h i x
    exact mul_smul g h _
  have hfill : ∀ n < 2, ∀ a : C(Sphere n,Z), ∃ e : C(Disk n,Z),
      ∀ x, e (boundary n x) = a x := by
    intro n hn
    have hn' : n=0 ∨ n=1 := by omega
    rcases hn' with rfl|rfl
    · exact SphereTopology.fill_zero
    · exact SphereTopology.fill_one
  obtain ⟨r,hr⟩ := exists_equivariant_map_on_skeleton σ hσ 2 hfill
  obtain ⟨q,hq⟩ := presentation_equivariant_map s rels hrel
  obtain ⟨P,hP⟩ := equivariant_controlled G (presentation_compactFundamentalSet s rels hrel hrels) q hq
  let a := (stageFull G S).comp (skeletonInclusion (C := (univ : Set (Stage G S))) 2)
  let b := q.comp r
  have ha (g : G) x : a (skeletonTranslate σ hσ 2 g x) = g • a x :=
    stageFull_smul G S g x.1
  have hb (g : G) x : b (skeletonTranslate σ hσ 2 g x) = g • b x := by
    change q (r (skeletonTranslate σ hσ 2 g x)) = g • q (r x)
    rw [hr,hq]
  obtain ⟨H,hH⟩ := exists_equivariant_homotopy_on_skeleton σ hσ 2 (sphereFillable (1:G)) a b ha hb
  obtain ⟨Q,hQ⟩ := controlled_skeleton_homotopy σ hσ 2 a b H hH
  let T := S ∪ P ∪ Q
  have hST : S ⊆ T := Finset.subset_union_left.trans Finset.subset_union_left
  have hPT : P ⊆ T := Finset.subset_union_right.trans Finset.subset_union_left
  have hQT : Q ⊆ T := Finset.subset_union_right
  have hpT : Set.range q ⊆ Set.range (stageFull G T) := by
    rintro _ ⟨z,rfl⟩
    obtain ⟨y,hy⟩ := hP (Set.mem_range_self z)
    exact ⟨stageIncl G P T hPT y,hy⟩
  have hhT : Set.range H ⊆ Set.range (stageFull G T) := by
    rintro _ ⟨z,rfl⟩
    obtain ⟨y,hy⟩ := hQ (Set.mem_range_self z)
    exact ⟨stageIncl G Q T hQT y,hy⟩
  let qT := factorStage G q T hpT
  let HTmap := factorStage G H.toContinuousMap T hhT
  let inc := stageIncl G S T hST
  let HT : (inc.comp (skeletonInclusion (C := (univ : Set (Stage G S))) 2)).Homotopy (qT.comp r) :=
    { toContinuousMap := HTmap
      map_zero_left := fun x => by
        apply (stageFull_embedding G T).injective
        change stageFull G T (HTmap (0,x)) = stageFull G T (inc x.1)
        rw [factorStage_spec]
        exact H.apply_zero x
      map_one_left := fun x => by
        apply (stageFull_embedding G T).injective
        change stageFull G T (HTmap (1,x)) = stageFull G T (qT (r x))
        rw [factorStage_spec,factorStage_spec]
        exact H.apply_one x }
  refine ⟨T,hST,?_⟩
  intro n hn k
  have hdim : dimH (univ : Set (Sphere n)) < 2 := by
    rcases hn with rfl|rfl
    · exact (GeneralPosition.dimH_cube_boundary_subtype_le 0).trans_lt (by norm_num)
    · exact (GeneralPosition.dimH_cube_boundary_subtype_le 1).trans_lt (by norm_num)
  let : Nonempty (Sphere n) := by
    rcases hn with rfl|rfl
    · exact SphereTopology.sphere_nonempty 0
    · exact SphereTopology.sphere_nonempty 1
  obtain ⟨v,J,_⟩ := exists_cellular_approximation_bundle 2 k (fun _ => Set.mem_univ _) hdim
  have hz : SphereTopology.Extends (r.comp v) := by
    rcases hn with rfl|rfl
    · obtain ⟨e,he⟩ := SphereTopology.fill_one (r.comp v)
      exact ⟨e,ContinuousMap.ext he⟩
    · exact Cayley.presentationCover_sphereFill s rels hrel hs hker (r.comp v)
  obtain ⟨e,he⟩ := hz
  have hzT : SphereTopology.Extends ((qT.comp r).comp v) := by
    refine ⟨qT.comp e,?_⟩
    apply ContinuousMap.ext; intro x
    exact congrArg qT (ContinuousMap.congr_fun he x)
  let J' := (ContinuousMap.Homotopy.refl inc).comp J
  obtain ⟨d,hd⟩ := SphereTopology.extends_of_homotopy (J'.trans (HT.compContinuousMap v)) hzT
  exact ⟨d,fun x => ContinuousMap.congr_fun hd x⟩
end UniversalFInfinity.Milnor

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

namespace UniversalFInfinity.Simplicial
open Set Metric Topology BigOperators
open scoped Classical
universe u v
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

def restrictInclusion (S : Finset V) : C(Space (restrict K S),Space K) :=
  ⟨inclusion (restrict K S) K (fun _ h => restrict_le K S h),continuous_inclusion _ _ _⟩

lemma compactMap_finiteRestriction {A : Type v} [TopologicalSpace A] [CompactSpace A] (f : C(A,Space K)) :
    ∃ S : Finset V, ∃ F : C(A,Space (restrict K S)), (restrictInclusion K S).comp F = f := by
  obtain ⟨S,hS⟩ := compact_bounded_vertices K (isCompact_range f.continuous)
  let F : A → Space (restrict K S) := fun a =>
    ⟨(f a).1,(f a).2.1,(f a).2.2.1,(f a).2.2.2,hS (f a) (mem_range_self a)⟩
  have hc : Continuous F := (inclusion_closedEmbedding (restrict K S) K
    (fun _ h => restrict_le K S h)).isEmbedding.continuous_iff.mpr f.continuous
  exact ⟨S,⟨F,hc⟩,rfl⟩

end UniversalFInfinity.Simplicial

namespace UniversalFInfinity.Milnor

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical Topology.Homotopy
universe u v w
variable (G : Type u) [Group G] (N : Type v) [DecidableEq N] [Nontrivial N]
variable (A : Type w) [Group A]

local instance (priority := 2000) instDecidableEqProdNat_solutions_8_rbfe4b0_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
abbrev StagePi (S : Shapes G) := HomotopyGroup N (Simplicial.Space (stage G S)) (stagePoint G S)
abbrev StageValues (S : Shapes G) := A →* StagePi G N S

def valueHom (S T : Shapes G) (h : S ⊆ T) : StageValues G N A S →* StageValues G N A T where
  toFun f := (stageHom G N S T h).comp f
  map_one' := by ext; rfl
  map_mul' f g := by ext a; exact (stageHom G N S T h).map_mul (f a) (g a)

instance instDirectedSystemShapesStageValuesCoeMonoidHomValueHom : DirectedSystem (StageValues G N A) (fun S T h => valueHom G N A S T h) where
  map_self _ f := by ext a; exact DirectedSystem.map_self (f := fun _ _ h => stageHom G N _ _ h) (f a)
  map_map _ _ _ h₁ h₂ f := by ext a; exact DirectedSystem.map_map (f := fun _ _ h => stageHom G N _ _ h) h₁ h₂ (f a)

abbrev ControlledValues := DirectLimit (StageValues G N A) (valueHom G N A)

def value (S : Shapes G) (f : StageValues G N A S) : ControlledValues G N A := Quotient.mk _ ⟨S,f⟩

lemma value_eq_one_iff (S : Shapes G) (f : StageValues G N A S) :
    value G N A S f = 1 ↔ ∃ T, ∃ h : S ⊆ T, (stageHom G N S T h).comp f = 1 :=
  DirectLimit.exists_eq_one (f := valueHom G N A) ⟨S,f⟩

lemma value_mul (S : Shapes G) (f g : StageValues G N A S) :
    value G N A S (f*g) = value G N A S f * value G N A S g :=
  (DirectLimit.mul_def (f := valueHom G N A) S f g).symm
end

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical Topology.Homotopy unitInterval
universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable (N : Type w) [DecidableEq N] [Nontrivial N]

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_9
variable (φ : G →* H) (α : ℕ → ℕ) (S : Shapes G) (T : Shapes H)
variable (hv : ∀ s : Face (stage G S), faceImage φ α s.1 ∈ stage H T)

lemma stageMap_point (hα : α 0 = 0) : stageMap φ α S T hv (stagePoint G S) = stagePoint H T := by
  apply Subtype.ext
  change (Finsupp.single (0,(1:G)) (1:ℝ)).mapDomain (vertexMap φ α) = Finsupp.single (0,1) 1
  rw [Finsupp.mapDomain_single]
  congr 1
  exact Prod.ext hα φ.map_one

variable (hα : α 0 = 0)
def stageMapHom : StagePi G N S →* StagePi H N T :=
  HomotopyFunctor.mapHom (stageMap φ α S T hv) (stageMap_point φ α S T hv hα)
def stageMapValue : ControlledValues H N (StagePi G N S) :=
  value H N _ T (stageMapHom N φ α S T hv hα)

lemma stageMapValue_congrTarget (U : Shapes H)
    (hu : ∀ s : Face (stage G S), faceImage φ α s.1 ∈ stage H U) :
    stageMapValue N φ α S T hv hα = stageMapValue N φ α S U hu hα := by
  apply Quotient.sound
  refine ⟨T ∪ U,Finset.subset_union_left,Finset.subset_union_right,?_⟩
  apply MonoidHom.ext
  intro a
  induction a using Quotient.inductionOn with | h p =>
  apply congrArg Quotient.mk'
  apply Subtype.ext
  ext z
  rfl

lemma stageMapValue_eq_of_homotopy (ψ : G →* H) (β : ℕ → ℕ)
    (hw : ∀ s : Face (stage G S), faceImage ψ β s.1 ∈ stage H T) (hβ : β 0 = 0)
    (F : (stageMap φ α S T hv).Homotopy (stageMap ψ β S T hw))
    (hF : ∀ t, F (t,stagePoint G S) = stagePoint H T) :
    stageMapValue N φ α S T hv hα = stageMapValue N ψ β S T hw hβ := by
  apply congrArg (value H N _ T)
  ext a
  exact HomotopyFunctor.map_eq_of_homotopy _ _ _ _ F hF a

lemma image_stage_valid (hαi : Function.Injective α) (s : Face (stage G S)) :
    faceImage φ α s.1 ∈ stage H (imageShapes φ α (basedShapes G S)) :=
  orbitSpan_mono (Finset.subset_insert _ _) (faceImage_controlled φ α hαi (basedShapes G S) s)

def mapValue (hαi : Function.Injective α) : ControlledValues H N (StagePi G N S) :=
  stageMapValue N φ α S _ (image_stage_valid φ α S hαi) hα

lemma mapValue_eq (hαi : Function.Injective α) :
    mapValue N φ α S hα hαi = stageMapValue N φ α S T hv hα :=
  stageMapValue_congrTarget N φ α S _ _ hα T hv
end

open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical Topology.Homotopy unitInterval
universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable (N : Type w) [DecidableEq N] [Nontrivial N]

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_10
variable (φ : G →* H) (S : Shapes G) (α β : ℕ → ℕ)
variable (hα : Function.Injective α) (hβ : Function.Injective β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
include hα hα0 in
lemma relayerStageLeftValid (s : Face (stage G S)) :
    faceImage φ α s.1 ∈ stage H (relayerTarget φ (basedShapes G S) α β) :=
  orbitSpan_mono (Finset.subset_insert _ _) (relayerLeftMapValid φ (basedShapes G S) α β hα hα0 s)
include hβ hβ0 in
lemma relayerStageRightValid (s : Face (stage G S)) :
    faceImage φ β s.1 ∈ stage H (relayerTarget φ (basedShapes G S) α β) :=
  orbitSpan_mono (Finset.subset_insert _ _) (relayerRightMapValid φ (basedShapes G S) α β hβ hβ0 s)

def relayerToStage : C(Simplicial.Space (orbitSpan (relayerTarget φ (basedShapes G S) α β)),
    Simplicial.Space (stage H (relayerTarget φ (basedShapes G S) α β))) :=
  ⟨inclusion _ _ (fun _ hs => orbitSpan_mono (Finset.subset_insert _ _) hs),continuous_inclusion _ _ _⟩

def relayerStageHomotopy :
    (stageMap φ α S _ (relayerStageLeftValid φ S α β hα hα0)).Homotopy
      (stageMap φ β S _ (relayerStageRightValid φ S α β hβ hβ0)) :=
  (ContinuousMap.Homotopy.refl (relayerToStage φ S α β)).comp
    (relayerHomotopy φ (basedShapes G S) α β hα hβ hα0 hβ0)

lemma relayerStageHomotopy_fixed (t : I) :
    relayerStageHomotopy φ S α β hα hβ hα0 hβ0 (t,stagePoint G S) =
      stagePoint H (relayerTarget φ (basedShapes G S) α β) := by
  change relayerToStage φ S α β (relayerHomotopy φ (basedShapes G S) α β hα hβ hα0 hβ0 (t,stagePoint G S)) = _
  rw [relayerHomotopy_fixed φ (basedShapes G S) α β hα hβ hα0 hβ0 (stagePoint G S) 1 rfl]
  exact stageMap_point φ α S _ (relayerStageLeftValid φ S α β hα hα0) hα0

lemma mapValue_relayer : mapValue N φ α S hα0 hα = mapValue N φ β S hβ0 hβ := by
  rw [mapValue_eq N φ α S _ (relayerStageLeftValid φ S α β hα hα0) hα0 hα,
    mapValue_eq N φ β S _ (relayerStageRightValid φ S α β hβ hβ0) hβ0 hβ]
  exact stageMapValue_eq_of_homotopy N φ α S _ _ hα0 φ β _ hβ0
    (relayerStageHomotopy φ S α β hα hβ hα0 hβ0) (relayerStageHomotopy_fixed φ S α β hα hβ hα0 hβ0)
end UniversalFInfinity.Milnor

namespace UniversalFInfinity.Simplicial

section
open Set Metric Topology BigOperators
open scoped Classical Topology.Homotopy
universe u v
variable {V : Type u} (K : PreAbstractSimplicialComplex V)
variable {N : Type v} [Nonempty N] {x : Space K}

lemma loop_finite_restriction (p : GenLoop N (Space K) x) :
    ∃ S : Finset V, ∃ y : Space (restrict K S),
      ∃ hy : restrictInclusion K S y = x,
      ∃ q : GenLoop N (Space (restrict K S)) y,
        HomotopyFunctor.loopMap (restrictInclusion K S) hy q = p := by
  obtain ⟨S,F,hF⟩ := compactMap_finiteRestriction K p.1
  let z : N → unitInterval := fun _ => 0
  have hz : z ∈ Cube.boundary N := ⟨Classical.arbitrary N,Or.inl rfl⟩
  have hy : restrictInclusion K S (F z) = x :=
    (ContinuousMap.congr_fun hF z).trans (GenLoop.boundary p z hz)
  let q : GenLoop N (Space (restrict K S)) (F z) := ⟨F,by
    intro t ht
    apply inclusion_injective (restrict K S) K (fun _ h => restrict_le K S h)
    exact (ContinuousMap.congr_fun hF t).trans ((GenLoop.boundary p t ht).trans hy.symm)⟩
  refine ⟨S,F z,hy,q,?_⟩
  apply Subtype.ext
  exact hF
end

section
open Set Metric Topology BigOperators
open scoped Classical
universe u v w
variable {V : Type u} {W : Type v} {U : Type w}

variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
variable (M : PreAbstractSimplicialComplex U)
variable (p : V × W → U) (hp : ∀ s : Face K, ∀ t : Face L, (s.1 ×ˢ t.1).image p ∈ M)

lemma continuous_pairMap_faces (s : Face K) (t : Face L) :
    Continuous (fun q : SimplexDisk.Simplex s.1 × SimplexDisk.Simplex t.1 =>
      pairMap K L M p hp (faceMap K s q.1) (faceMap L t q.2)) := by
  apply continuous_of_support_subset M _ ⟨(s.1 ×ˢ t.1).image p,hp s t⟩
  · intro q
    exact (pairMap_support K L M p hp _ _).trans
      (Finset.image_subset_image (Finset.product_subset_product (weight_support_subset _ _) (weight_support_subset _ _)))
  · intro b
    have he : (fun q : SimplexDisk.Simplex s.1 × SimplexDisk.Simplex t.1 =>
        (pairMap K L M p hp (faceMap K s q.1) (faceMap L t q.2)).1 b) =
        fun q => ∑ a : s.1, ∑ c : t.1, if p (a.1,c.1) = b then q.1.1 a * q.2.1 c else 0 := by
      funext q
      change ((tensor (weight s.1 q.1) (weight t.1 q.2)).mapDomain p) b = _
      rw [push_apply p _ (s.1 ×ˢ t.1) (by rw [tensor_support]; exact Finset.product_subset_product (weight_support_subset _ _) (weight_support_subset _ _)),Finset.sum_product]
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro c _
      simp only [tensor_apply,weight_apply]
    rw [he]
    apply continuous_finsetSum
    intro a _
    apply continuous_finsetSum
    intro c _
    split_ifs
    · exact (((continuous_apply a).comp continuous_subtype_val).comp continuous_fst).mul
        (((continuous_apply c).comp continuous_subtype_val).comp continuous_snd)
    · exact continuous_const

instance instCompactSpaceElemFinsuppRealSpaceOfFiniteFace [Finite (Face K)] : CompactSpace (Space K) := by
  have hc : IsCompact (⋃ s : Face K, Set.range (faceMap K s)) :=
    isCompact_iUnion (fun s => isCompact_range (continuous_faceMap K s))
  have he : (⋃ s : Face K, Set.range (faceMap K s)) = Set.univ := by
    ext x
    simp only [mem_iUnion,mem_univ,iff_true]
    exact ⟨⟨x.1.support,x.2.2.2⟩,coordinates K _ x (Finset.Subset.refl _),faceMap_coordinates K _ _ _⟩
  exact ⟨he ▸ hc⟩

lemma continuous_prod_faces_iff [Finite (Face K)] {Y : Type*} [TopologicalSpace Y]
    (f : Space K × Space L → Y) : Continuous f ↔
    ∀ s : Face K, ∀ t : Face L, Continuous (fun q : SimplexDisk.Simplex s.1 × SimplexDisk.Simplex t.1 =>
      f (faceMap K s q.1,faceMap L t q.2)) := by
  constructor
  · intro hf s t
    exact hf.comp (((continuous_faceMap K s).comp continuous_fst).prodMk ((continuous_faceMap L t).comp continuous_snd))
  · intro hf
    rw [continuous_prod_iff]
    intro t
    have hc : Continuous (fun q : SimplexDisk.Simplex t.1 × Space K => f (q.2,faceMap L t q.1)) := by
      rw [continuous_prod_iff]
      intro s
      exact (hf s t).comp continuous_swap
    exact hc.comp continuous_swap

lemma continuous_pairMap [Finite (Face K)] : Continuous (fun q : Space K × Space L => pairMap K L M p hp q.1 q.2) :=
  (continuous_prod_faces_iff K L _).mpr (continuous_pairMap_faces K L M p hp)

def pairMapC [Finite (Face K)] : C(Space K × Space L,Space M) :=
  ⟨fun q => pairMap K L M p hp q.1 q.2,continuous_pairMap K L M p hp⟩
end

section
open Set Metric Topology BigOperators
open scoped Classical unitInterval
universe u v
variable {V : Type u} {W : Type v}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
variable (f g : C(Space K,Space L)) (c : Face K → Face L)
variable (hf : ∀ s : Face K, ∀ x : Space K, x.1.support ⊆ s.1 → (f x).1.support ⊆ (c s).1)
variable (hg : ∀ s : Face K, ∀ x : Space K, x.1.support ⊆ s.1 → (g x).1.support ⊆ (c s).1)

def carrierBlend (t : I) (x : Space K) : Space L :=
  blend L (c ⟨x.1.support,x.2.2.2⟩) (f x) (g x)
    (hf _ x (Finset.Subset.refl _)) (hg _ x (Finset.Subset.refl _)) t

lemma continuous_carrierBlend : Continuous (fun p : I × Space K => carrierBlend K L f g c hf hg p.1 p.2) := by
  rw [continuous_prod_iff]
  intro s
  apply continuous_of_support_subset L _ (c s)
  · intro p
    exact (blend_support _ _ p.1).trans (Finset.union_subset
      (hf s _ (weight_support_subset _ _)) (hg s _ (weight_support_subset _ _)))
  · intro b
    change Continuous (fun p : I × SimplexDisk.Simplex s.1 =>
      (1-(p.1:ℝ)) * (f (faceMap K s p.2)).1 b + (p.1:ℝ) * (g (faceMap K s p.2)).1 b)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_eval L b).comp (f.continuous.comp ((continuous_faceMap K s).comp continuous_snd)))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((continuous_eval L b).comp (g.continuous.comp ((continuous_faceMap K s).comp continuous_snd))))

def carrierHomotopy : f.Homotopy g where
  toFun p := carrierBlend K L f g c hf hg p.1 p.2
  continuous_toFun := continuous_carrierBlend K L f g c hf hg
  map_zero_left _ := blend_zero L _ _ _ _ _
  map_one_left _ := blend_one L _ _ _ _ _

lemma carrierHomotopy_fixed (x : Space K) (h : f x = g x) (t : I) :
    carrierHomotopy K L f g c hf hg (t,x) = f x := by
  apply Subtype.ext
  change (1-(t:ℝ)) • (f x).1 + (t:ℝ) • (g x).1 = (f x).1
  rw [←h,←add_smul,sub_add_cancel,one_smul]
end

section
open Set Metric Topology BigOperators
open scoped Classical unitInterval
universe u v
variable {V : Type u} {W : Type v}

variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
variable (p : V × V → W) (hp : ∀ s t : Face K, (s.1 ×ˢ t.1).image p ∈ L)

variable [Finite (Face K)]
def productDiagonal : C(Space K,Space L) :=
  (pairMapC K K L p hp).comp ((ContinuousMap.id _).prodMk (ContinuousMap.id _))
def vertexDiagonal : C(Space K,Space L) := mapC K L (fun v => p (v,v)) (diagonal_face K L p hp)

lemma productDiagonal_carried (s : Face K) (x : Space K) (hx : x.1.support ⊆ s.1) :
    (productDiagonal K L p hp x).1.support ⊆ (diagonalCarrier K L p hp s).1 :=
  (pairMap_support K K L p hp x x).trans (Finset.image_subset_image (Finset.product_subset_product hx hx))
omit [Finite (Face K)] in
lemma vertexDiagonal_carried (s : Face K) (x : Space K) (hx : x.1.support ⊆ s.1) :
    (vertexDiagonal K L p hp x).1.support ⊆ (diagonalCarrier K L p hp s).1 := by
  apply (map_support K L (fun v => p (v,v)) (diagonal_face K L p hp) x).trans
  intro z hz
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨(v,v),Finset.mem_product.mpr ⟨hx hv,hx hv⟩,rfl⟩

def diagonalHomotopy : (productDiagonal K L p hp).Homotopy (vertexDiagonal K L p hp) :=
  carrierHomotopy K L _ _ (diagonalCarrier K L p hp)
    (productDiagonal_carried K L p hp) (vertexDiagonal_carried K L p hp)

lemma diagonalHomotopy_fixed (x : Space K) (v : V) (hx : x.1 = Finsupp.single v 1) (t : I) :
    diagonalHomotopy K L p hp (t,x) = vertexDiagonal K L p hp x := by
  have h : productDiagonal K L p hp x = vertexDiagonal K L p hp x := by
    apply Subtype.ext
    rw [show (productDiagonal K L p hp x).1 = Finsupp.single (p (v,v)) 1 from
      pairMap_pure K L p hp x x v v hx hx]
    change Finsupp.single (p (v,v)) 1 = x.1.mapDomain (fun v => p (v,v))
    rw [hx,Finsupp.mapDomain_single]
  exact (carrierHomotopy_fixed K L _ _ _ _ _ x h t).trans h
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

namespace UniversalFInfinity.HomotopyFunctor
open scoped Topology.Homotopy
lemma map_congr_maps {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f g : C(X,Y)) (hf : f x = y) (hg : g x = y) (h : f = g) (a : HomotopyGroup N X x) :
    map f hf a = map g hg a := by
  subst g
  rfl
end UniversalFInfinity.HomotopyFunctor

namespace UniversalFInfinity.Simplicial

section
open Set Metric Topology BigOperators
open scoped Classical Topology.Homotopy
universe u v w
variable {V : Type u} {W : Type v}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
variable (p : V × V → W) (hp : ∀ s t : Face K, (s.1 ×ˢ t.1).image p ∈ L)
variable (x : Space K) (v : V) (hx : x.1 = Finsupp.single v 1)

def leftAxis : C(Space K,Space L) := mapC K L (fun a => p (a,v)) (leftAxisFace K L p hp x v hx)
def rightAxis : C(Space K,Space L) := mapC K L (fun a => p (v,a)) (rightAxisFace K L p hp x v hx)

lemma leftAxis_point : leftAxis K L p hp x v hx x = vertexDiagonal K L p hp x := by
  apply Subtype.ext
  change x.1.mapDomain _ = x.1.mapDomain _
  rw [hx,Finsupp.mapDomain_single,Finsupp.mapDomain_single]
lemma rightAxis_point : rightAxis K L p hp x v hx x = vertexDiagonal K L p hp x := by
  apply Subtype.ext
  change x.1.mapDomain _ = x.1.mapDomain _
  rw [hx,Finsupp.mapDomain_single,Finsupp.mapDomain_single]

variable [Finite (Face K)]
lemma pairLeft_eq : (pairMapC K K L p hp).comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ x)) =
    leftAxis K L p hp x v hx := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change (tensor z.1 x.1).mapDomain p = z.1.mapDomain _
  rw [hx,tensor_single_right_push]
lemma pairRight_eq : (pairMapC K K L p hp).comp ((ContinuousMap.const _ x).prodMk (ContinuousMap.id _)) =
    rightAxis K L p hp x v hx := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change (tensor x.1 z.1).mapDomain p = z.1.mapDomain _
  rw [hx,tensor_single_left_push]

include hx in
lemma productDiagonal_point : productDiagonal K L p hp x = vertexDiagonal K L p hp x := by
  apply Subtype.ext
  rw [show (productDiagonal K L p hp x).1 = Finsupp.single (p (v,v)) 1 from pairMap_pure K L p hp x x v v hx hx]
  change Finsupp.single _ 1 = x.1.mapDomain _
  rw [hx,Finsupp.mapDomain_single]

variable {N : Type w} [DecidableEq N] [Nonempty N]
lemma finite_pair_additivity (a : HomotopyGroup N (Space K) x) :
    HomotopyFunctor.map (vertexDiagonal K L p hp) rfl a =
      HomotopyFunctor.map (leftAxis K L p hp x v hx) (leftAxis_point K L p hp x v hx) a *
      HomotopyFunctor.map (rightAxis K L p hp x v hx) (rightAxis_point K L p hp x v hx) a := by
  have hh := HomotopyFunctor.product_additivity (pairMapC K K L p hp)
    (productDiagonal_point K L p hp x v hx) a
  have hD := HomotopyFunctor.map_eq_of_homotopy (productDiagonal K L p hp) (vertexDiagonal K L p hp)
    (productDiagonal_point K L p hp x v hx) rfl (diagonalHomotopy K L p hp)
    (diagonalHomotopy_fixed K L p hp x v hx) a
  simp only [ContinuousMap.id_apply] at hh
  have hL := HomotopyFunctor.map_congr_maps ((pairMapC K K L p hp).comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ x))) _ (productDiagonal_point K L p hp x v hx) (leftAxis_point K L p hp x v hx)
    (pairLeft_eq K L p hp x v hx) a
  have hR := HomotopyFunctor.map_congr_maps ((pairMapC K K L p hp).comp ((ContinuousMap.const _ x).prodMk (ContinuousMap.id _))) _ (productDiagonal_point K L p hp x v hx) (rightAxis_point K L p hp x v hx)
    (pairRight_eq K L p hp x v hx) a
  exact hD.symm.trans (hh.trans (congrArg₂ (· * ·) hL hR))
end

section
open Set Metric Topology BigOperators
open scoped Classical Topology.Homotopy
universe u v w
variable {V : Type u} {W : Type v}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
variable (p : V × V → W) (hp : ∀ s t : Face K, (s.1 ×ˢ t.1).image p ∈ L)
variable (x : Space K) (v : V) (hx : x.1 = Finsupp.single v 1)
variable {N : Type w} [DecidableEq N] [Nonempty N]
lemma finite_pair_additivity_to [Finite (Face K)] (z : Space L)
    (hz : vertexDiagonal K L p hp x = z) (a : HomotopyGroup N (Space K) x) :
    HomotopyFunctor.map (vertexDiagonal K L p hp) hz a =
      HomotopyFunctor.map (leftAxis K L p hp x v hx) ((leftAxis_point K L p hp x v hx).trans hz) a *
      HomotopyFunctor.map (rightAxis K L p hp x v hx) ((rightAxis_point K L p hp x v hx).trans hz) a := by
  subst z
  exact finite_pair_additivity K L p hp x v hx a

lemma pair_additivity (a : HomotopyGroup N (Space K) x) :
    HomotopyFunctor.map (vertexDiagonal K L p hp) rfl a =
      HomotopyFunctor.map (leftAxis K L p hp x v hx) (leftAxis_point K L p hp x v hx) a *
      HomotopyFunctor.map (rightAxis K L p hp x v hx) (rightAxis_point K L p hp x v hx) a := by
  induction a using Quotient.inductionOn with | h q =>
  obtain ⟨R,y,hy,r,hr⟩ := loop_finite_restriction K q
  have hyr : y.1 = Finsupp.single v 1 := (congrArg (fun z : Space K => z.1) hy).trans hx
  let hpR : ∀ s t : Face (restrict K R), (s.1 ×ˢ t.1).image p ∈ L :=
    fun s t => hp ⟨s.1,s.2.1⟩ ⟨t.1,t.2.1⟩
  have hz : vertexDiagonal (restrict K R) L p hpR y = vertexDiagonal K L p hp x := by
    apply Subtype.ext
    exact congrArg (Finsupp.mapDomain (fun v => p (v,v))) (congrArg (fun z : Space K => z.1) hy)
  have hh := finite_pair_additivity_to (restrict K R) L p hpR y v hyr _ hz (Quotient.mk' r)
  subst q
  exact hh
end

open scoped Classical Topology.Homotopy
universe u v w
variable {V : Type u} {W : Type v}
lemma pair_additivity_to (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (p : V × V → W) (hp : ∀ s t : Face K, (s.1 ×ˢ t.1).image p ∈ L)
    (x : Space K) (v : V) (hx : x.1 = Finsupp.single v 1) {N : Type w} [DecidableEq N] [Nonempty N]
    (z : Space L) (hz : vertexDiagonal K L p hp x = z) (a : HomotopyGroup N (Space K) x) :
    HomotopyFunctor.map (vertexDiagonal K L p hp) hz a =
      HomotopyFunctor.map (leftAxis K L p hp x v hx) ((leftAxis_point K L p hp x v hx).trans hz) a *
      HomotopyFunctor.map (rightAxis K L p hp x v hx) ((rightAxis_point K L p hp x v hx).trans hz) a := by
  subst z
  exact pair_additivity K L p hp x v hx a
end UniversalFInfinity.Simplicial

namespace UniversalFInfinity.Milnor
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical Topology.Homotopy
universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable (N : Type w) [DecidableEq N] [Nontrivial N]

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_12
variable (φ ψ : G →* H) (hc : ∀ g h, Commute (φ g) (ψ h)) (S : Shapes G)

def addTarget : Shapes H := productShapes φ ψ (basedShapes G S) (basedShapes G S)
include hc in
lemma addValid (s t : Face (stage G S)) : (s.1 ×ˢ t.1).image (addVertex φ ψ) ∈ stage H (addTarget φ ψ S) :=
  orbitSpan_mono (Finset.subset_insert _ _) (pairFace_controlled φ ψ hc _ _ s t)

lemma addDiagValid (s : Face (stage G S)) :
    faceImage (commutingProduct φ ψ hc) diagLayer s.1 ∈ stage H (addTarget φ ψ S) :=
  diagonal_face _ _ (addVertex φ ψ) (addValid φ ψ hc S) s
include hc in
lemma addLeftValid (s : Face (stage G S)) :
    faceImage φ leftLayer s.1 ∈ stage H (addTarget φ ψ S) := by
  have hh := leftAxisFace _ _ (addVertex φ ψ) (addValid φ ψ hc S) (stagePoint G S) (0,1) rfl s
  change (s.1.image (fun a => (Nat.pair a.1 0,φ a.2))) ∈ stage H (addTarget φ ψ S)
  simpa only [addVertex,pairVertex,map_one,mul_one] using hh
include hc in
lemma addRightValid (s : Face (stage G S)) :
    faceImage ψ rightLayer s.1 ∈ stage H (addTarget φ ψ S) := by
  have hh := rightAxisFace _ _ (addVertex φ ψ) (addValid φ ψ hc S) (stagePoint G S) (0,1) rfl s
  change (s.1.image (fun a => (Nat.pair 0 a.1,ψ a.2))) ∈ stage H (addTarget φ ψ S)
  simpa only [addVertex,pairVertex,map_one,one_mul] using hh

lemma addLeftMap : leftAxis _ _ (addVertex φ ψ) (addValid φ ψ hc S) (stagePoint G S) (0,1) rfl =
    stageMap φ leftLayer S _ (addLeftValid φ ψ hc S) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change z.1.mapDomain _ = z.1.mapDomain _
  congr 1
  funext v
  exact Prod.ext rfl (by exact (congrArg (φ v.2 * ·) ψ.map_one).trans (mul_one _))
lemma addRightMap : rightAxis _ _ (addVertex φ ψ) (addValid φ ψ hc S) (stagePoint G S) (0,1) rfl =
    stageMap ψ rightLayer S _ (addRightValid φ ψ hc S) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change z.1.mapDomain _ = z.1.mapDomain _
  congr 1
  funext v
  exact Prod.ext rfl (by exact (congrArg (· * ψ v.2) φ.map_one).trans (one_mul _))

lemma addHom : stageMapHom N (commutingProduct φ ψ hc) diagLayer S _ (addDiagValid φ ψ hc S) rfl =
    stageMapHom N φ leftLayer S _ (addLeftValid φ ψ hc S) rfl *
      stageMapHom N ψ rightLayer S _ (addRightValid φ ψ hc S) rfl := by
  ext a
  have hh := pair_additivity_to (stage G S) (stage H (addTarget φ ψ S)) (addVertex φ ψ) (addValid φ ψ hc S)
    (stagePoint G S) (0,1) rfl (stagePoint H (addTarget φ ψ S))
    (stageMap_point (commutingProduct φ ψ hc) diagLayer S _ (addDiagValid φ ψ hc S) rfl) a
  have hL := HomotopyFunctor.map_congr_maps _ _
    ((leftAxis_point _ _ (addVertex φ ψ) (addValid φ ψ hc S) (stagePoint G S) (0,1) rfl).trans (stageMap_point (commutingProduct φ ψ hc) diagLayer S _ (addDiagValid φ ψ hc S) rfl))
    (stageMap_point φ leftLayer S _ (addLeftValid φ ψ hc S) rfl) (addLeftMap φ ψ hc S) a
  have hR := HomotopyFunctor.map_congr_maps _ _
    ((rightAxis_point _ _ (addVertex φ ψ) (addValid φ ψ hc S) (stagePoint G S) (0,1) rfl).trans (stageMap_point (commutingProduct φ ψ hc) diagLayer S _ (addDiagValid φ ψ hc S) rfl))
    (stageMap_point ψ rightLayer S _ (addRightValid φ ψ hc S) rfl) (addRightMap φ ψ hc S) a
  exact hh.trans (congrArg₂ (· * ·) hL hR)

theorem mapValue_product :
    mapValue N (commutingProduct φ ψ hc) id S rfl Function.injective_id =
      mapValue N φ id S rfl Function.injective_id * mapValue N ψ id S rfl Function.injective_id := by
  rw [mapValue_relayer N (commutingProduct φ ψ hc) S id diagLayer Function.injective_id diagLayer_injective rfl rfl,
    mapValue_relayer N φ S id leftLayer Function.injective_id leftLayer_injective rfl rfl,
    mapValue_relayer N ψ S id rightLayer Function.injective_id rightLayer_injective rfl rfl,
    mapValue_eq N (commutingProduct φ ψ hc) diagLayer S _ (addDiagValid φ ψ hc S) rfl diagLayer_injective,
    mapValue_eq N φ leftLayer S _ (addLeftValid φ ψ hc S) rfl leftLayer_injective,
    mapValue_eq N ψ rightLayer S _ (addRightValid φ ψ hc S) rfl rightLayer_injective]
  change value H N _ _ _ = value H N _ _ _ * value H N _ _ _
  rw [←value_mul,addHom N φ ψ hc S]
end UniversalFInfinity.Milnor

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.ControlledHomotopies
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
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial ConcreteEnvelopes
open scoped Classical Topology.Homotopy
variable {G H : Type} [Group G] [Group H]
variable (N : Type*) [DecidableEq N] [Nontrivial N]

local instance (priority := 2000) instDecidableEqProdNat_solutions_13_rbfe4b0_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
lemma diagramValue_one (k : Index → G →* H) (hk : IsDiagram k) (S : Shapes G) :
    mapValue N (k (.inl P₂.identity)) id S rfl Function.injective_id = 1 := by
  let z : Index → Additive (ControlledValues H N (StagePi G N S)) :=
    fun E => Additive.ofMul (mapValue N (k E) id S rfl Function.injective_id)
  have hc : z (.inl P₂.identity) = z (.inr P₃.identity) := by
    simp only [z,hk.common]
  have hs : ∀ t : triples, z t.val.2.2 = z t.val.1 + z t.val.2.1 := by
    intro t
    have he : k t.val.2.2 = commutingProduct (k t.val.1) (k t.val.2.1) (hk.commute t) := by
      ext g
      exact hk.sum t g
    change mapValue N (k t.val.2.2) id S rfl Function.injective_id = _
    rw [he]
    exact mapValue_product N (k t.val.1) (k t.val.2.1) (hk.commute t) S
  exact congrArg Additive.toMul (coprime_annihilation z hc hs)

theorem diagram_uniform_homotopy_killing (k : Index → G →* H) (hk : IsDiagram k) (S : Shapes G) :
    ∃ T : Shapes H, ∃ h : imageShapes (k (.inl P₂.identity)) id (basedShapes G S) ⊆ T,
      (stageHom H N _ T h).comp
        (stageMapHom N (k (.inl P₂.identity)) id S _
          (image_stage_valid (k (.inl P₂.identity)) id S Function.injective_id) rfl) = 1 := by
  exact (value_eq_one_iff H N (StagePi G N S) _ _).mp (diagramValue_one N k hk S)
end UniversalFInfinity.Milnor

end

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

lemma rim_contractible (n : ℕ) : ContractibleSpace (Cylinder.Rim n) := by
  let : ContractibleSpace (Disk n) := (convex_closedBall (0 : Fin n → ℝ) 1).contractibleSpace
    ⟨0,by simp⟩
  let : ContractibleSpace unitInterval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by simp⟩
  obtain ⟨p,⟨H⟩⟩ := id_nullhomotopic (unitInterval × Disk n)
  let inc : C(Cylinder.Rim n,unitInterval × Disk n) := ⟨Subtype.val,continuous_subtype_val⟩
  let K := (ContinuousMap.Homotopy.refl (Cylinder.retract n)).comp (H.compContinuousMap inc)
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨Cylinder.retract n p,⟨?_⟩⟩
  have he : (Cylinder.retract n).comp ((ContinuousMap.id _).comp inc) = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (Cylinder.retract_of_rim x)
  exact he ▸ K

variable (f : C(Sphere (n+1),Y)) (y : Y)
variable (K : (f.comp (rimSphere n)).Homotopy (ContinuousMap.const _ y))

def topExtension : C(unitInterval × Disk n,Y) :=
  Cylinder.extension (f.comp (top n)) (edgeTrace f y K) (edgeTrace_zero f y K)

lemma topExtension_zero (x : Disk n) : topExtension f y K (0,x) = f (top n x) :=
  Cylinder.extension_zero _ _ _ x
lemma topExtension_boundary (t : unitInterval) (s : Sphere n) :
    topExtension f y K (t,boundary n s) = K (t,rimSide n (s,1)) :=
  Cylinder.extension_boundary _ _ _ t s

def normalizedTop : C(Disk n,Y) := (topExtension f y K).comp
  ⟨fun x => (1,x),continuous_const.prodMk continuous_id⟩
lemma normalizedTop_boundary (s : Sphere n) : normalizedTop f y K (boundary n s) = y := by
  change topExtension f y K (1,boundary n s) = y
  rw [topExtension_boundary,ContinuousMap.Homotopy.apply_one,ContinuousMap.const_apply]

def topPaths : C(Disk n,C(unitInterval,Y)) :=
  ((topExtension f y K).comp ContinuousMap.prodSwap).curry

lemma spherePaths_compatible (s : Sphere n) :
    pathEndpoint (sidePaths f y K s) =
      (bottomPaths f y K (boundary n s),topPaths f y K (boundary n s)) := by
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    exact (topExtension_boundary f y K t s).symm

lemma spherePaths_compatible_map (s : Sphere n) :
    pathEndpoint (sidePaths f y K s) =
      ((bottomPaths f y K).prodMk (topPaths f y K)) (boundary n s) :=
  spherePaths_compatible f y K s

def spherePaths : C(Sphere (n+1),C(unitInterval,Y)) :=
  cylinderBoundaryMap (sidePaths f y K)
    ((bottomPaths f y K).prodMk (topPaths f y K)) (spherePaths_compatible_map f y K)

lemma spherePaths_zero (s : Sphere (n+1)) : spherePaths f y K s 0 = f s := by
  rcases sphere_split s with h | h | h
  · rw [spherePaths,cylinderBoundaryMap_face _ _ _ (some false) ⟨s,h⟩]
    change K (0,rimBottom n (diskTail (boundary (n+1) s))) = f s
    rw [ContinuousMap.Homotopy.apply_zero]
    change f (rimSphere n (rimBottom n (diskTail (boundary (n+1) s)))) = f s
    congr 1
    apply Subtype.ext
    have ht : diskTime (boundary (n+1) s) = 0 := faceTime_eq_zero s h
    exact (congrArg (fun t => (diskCons (diskTail (boundary (n+1) s)) t).1) ht).symm.trans
      (congrArg Subtype.val (cons_tail_time (boundary (n+1) s)))
  · rw [spherePaths,cylinderBoundaryMap_face _ _ _ (some true) ⟨s,h⟩]
    change topExtension f y K (0,diskTail (boundary (n+1) s)) = f s
    rw [topExtension_zero]
    congr 1
    apply Subtype.ext
    have ht : diskTime (boundary (n+1) s) = 1 := faceTime_eq_one s h
    exact (congrArg (fun t => (diskCons (diskTail (boundary (n+1) s)) t).1) ht).symm.trans
      (congrArg Subtype.val (cons_tail_time (boundary (n+1) s)))
  · rw [spherePaths,cylinderBoundaryMap_face _ _ _ none ⟨s,h⟩]
    change K (0,rimSide n (faceSphere ⟨s,h⟩,faceTime none ⟨s,h⟩)) = f s
    rw [ContinuousMap.Homotopy.apply_zero]
    change f (rimSphere n (rimSide n (faceSphere ⟨s,h⟩,faceTime none ⟨s,h⟩))) = f s
    apply congrArg f
    apply Subtype.ext
    change (diskCons (diskTail (boundary (n+1) s)) (diskTime (boundary (n+1) s))).1 = s.1
    exact congrArg Subtype.val (cons_tail_time (boundary (n+1) s))

def normalizedSphere : C(Sphere (n+1),Y) :=
  ⟨fun s => spherePaths f y K s 1,(continuous_eval_const 1).comp (spherePaths f y K).continuous⟩

def normalizeHomotopy : f.Homotopy (normalizedSphere f y K) where
  toFun p := spherePaths f y K p.2 p.1
  continuous_toFun := continuous_eval.comp (((spherePaths f y K).continuous.comp continuous_snd).prodMk continuous_fst)
  map_zero_left s := spherePaths_zero f y K s
  map_one_left _ := rfl

lemma normalizedSphere_rim (x : Cylinder.Rim n) : normalizedSphere f y K (rimSphere n x) = y := by
  rcases x.2 with hx | hx
  · have h : rimSphere n x ∈ cylinderFace n (some false) := by
      change (diskCons x.1.2 x.1.1).1 0 = -1
      simp only [hx,diskCons,Fin.cons_zero,Set.Icc.coe_zero,mul_zero,zero_sub]
    change spherePaths f y K (rimSphere n x) 1 = y
    rw [spherePaths,cylinderBoundaryMap_face _ _ _ (some false) ⟨_,h⟩]
    exact K.apply_one _
  · have h : rimSphere n x ∈ cylinderFace n none := by
      change (diskTail (diskCons x.1.2 x.1.1)).1 ∈ sphere 0 1
      rw [diskTail_cons]; exact hx
    change spherePaths f y K (rimSphere n x) 1 = y
    rw [spherePaths,cylinderBoundaryMap_face _ _ _ none ⟨_,h⟩]
    exact K.apply_one _

lemma normalizedSphere_top (x : Disk n) : normalizedSphere f y K (top n x) = normalizedTop f y K x := by
  have h : top n x ∈ cylinderFace n (some true) := by
    change (diskCons x 1).1 0 = 1
    norm_num [diskCons]
  change spherePaths f y K (top n x) 1 = _
  rw [spherePaths,cylinderBoundaryMap_face _ _ _ (some true) ⟨_,h⟩]
  change topExtension f y K (1,diskTail (diskCons x 1)) = _
  rw [diskTail_cons]
  rfl
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
variable {n : ℕ} {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]

def basedDiskLoop (g : C(Disk n,Y)) (y : Y) (hg : ∀ s, g (boundary n s) = y) : GenLoop (Fin n) Y y :=
  ⟨g.comp (DiskCube.fromCube n),by
    intro x hx
    exact hg ⟨_,DiskCube.from_boundary n x hx⟩⟩

end

open scoped Topology Topology.Homotopy
universe u v
end UniversalFInfinity.SphereCube

namespace UniversalFInfinity.SphereCube
open Set Metric Topology Cellular
open scoped Topology.Homotopy
universe u v w
variable {n : ℕ} {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma rim_nullhomotopy_of_joined (r : C(X,Y)) (y : Y)
    (hy : ∀ x, Joined (r x) y) (f : C(Sphere (n+1),X)) :
    Nonempty (((r.comp f).comp (rimSphere n)).Homotopy (ContinuousMap.const _ y)) := by
  let := rim_contractible n
  obtain ⟨p,⟨H⟩⟩ := id_nullhomotopic (Cylinder.Rim n)
  let F := (r.comp f).comp (rimSphere n)
  let K := (ContinuousMap.Homotopy.refl F).comp H
  let q : Path (F p) y := (hy (f (rimSphere n p))).somePath
  let L : (ContinuousMap.const (Cylinder.Rim n) (F p)).Homotopy (ContinuousMap.const _ y) :=
    { toFun := fun z => q z.1
      continuous_toFun := q.continuous.comp continuous_fst
      map_zero_left := fun _ => q.source
      map_one_left := fun _ => q.target }
  exact ⟨K.trans L⟩

lemma fills_of_rim_nullhomotopy (y : Y) (q : C(Y,Z))
    (hq : ∀ p : GenLoop (Fin n) Y y,
      Nonempty ((q.comp p.1).HomotopyRel (ContinuousMap.const _ (q y)) (Cube.boundary (Fin n))))
    (f : C(Sphere (n+1),Y))
    (K : (f.comp (rimSphere n)).Homotopy (ContinuousMap.const _ y)) :
    ∃ F : C(Disk (n+1),Z), ∀ x, F (boundary (n+1) x) = q (f x) := by
  let g := normalizedTop f y K
  let p := basedDiskLoop g y (normalizedTop_boundary f y K)
  obtain ⟨L⟩ := hq p
  let H : (q.comp g).Homotopy (ContinuousMap.const _ (q y)) :=
    { toFun := fun v => L (v.1,DiskCube.toCube n v.2)
      continuous_toFun := L.continuous.comp
        (continuous_fst.prodMk ((DiskCube.toCube n).continuous.comp continuous_snd))
      map_zero_left := by
        intro x
        change L (0,DiskCube.toCube n x) = _
        rw [L.apply_zero]
        change q (g (DiskCube.fromCube n (DiskCube.toCube n x))) = q (g x)
        rw [DiskCube.from_to]
      map_one_left := by intro x; exact L.apply_one _ }
  have hb : ∀ t s, H (t,boundary n s) = q y := by
    intro t s
    exact L.eq_snd t (DiskCube.to_boundary n s)
  let J := nullSphere (q.comp (normalizedSphere f y K)) (q.comp g) (q y)
    (fun x => congrArg q (normalizedSphere_rim f y K x))
    (fun x => congrArg q (normalizedSphere_top f y K x)) H hb
  let N := (ContinuousMap.Homotopy.refl q).comp (normalizeHomotopy f y K)
  let : Nonempty (SphereTopology.Sphere (n+1)) := SphereTopology.sphere_nonempty n
  obtain ⟨F,hF⟩ := SphereTopology.extends_of_nullhomotopic (N.trans J).symm
  exact ⟨F,fun x => ContinuousMap.congr_fun hF x⟩

lemma killsSpheres_of_connected_image [Nonempty (Fin n)] (r : C(X,Y)) (y : Y)
    (hy : ∀ x, Joined (r x) y) (q : C(Y,Z)) (z : Z) (hbase : q y = z)
    (hq : ∀ a : HomotopyGroup (Fin n) Y y, HomotopyFunctor.map q hbase a = 1) :
    KillsSpheres (q.comp r) (n+1) := by
  subst z
  intro f
  obtain ⟨K⟩ := rim_nullhomotopy_of_joined r y hy f
  apply fills_of_rim_nullhomotopy y q (fun p => ?_) (r.comp f) K
  have hh := hq (Quotient.mk' p)
  change Quotient.mk' (HomotopyFunctor.loopMap q rfl p) = Quotient.mk' GenLoop.const at hh
  exact Quotient.exact hh
end UniversalFInfinity.SphereCube

namespace UniversalFInfinity.Milnor

section
open Set Metric Topology Cellular UniversalFInfinity.Simplicial ConcreteEnvelopes
open scoped Topology.Homotopy
variable {G : Type} [Group G] [Group.IsFinitelyPresented G]
  [TopologicalSpace G] [DiscreteTopology G]

local instance (priority := 2000) instDecidableEqProdNat_solutions_14_rbfe4b0_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
lemma uniform_low_fp (S : Shapes G) :
    ∃ (T : Shapes G) (hST : S ⊆ T), ∀ n : ℕ, n = 1 ∨ n = 2 →
      KillsSpheres (stageIncl G S T hST) n := by
  obtain ⟨m,q,hq,R,hR,hker⟩ := Group.IsFinitelyPresented.out (G := G)
  let s : Fin m → G := fun i => q (FreeGroup.of i)
  have hs : FreeGroup.lift s = q := by
    apply FreeGroup.ext_hom
    intro i
    exact FreeGroup.lift_apply_of
  have hrel : ∀ r ∈ R, FreeGroup.lift s r = 1 := by
    intro r hr
    rw [hs]
    exact show r ∈ q.ker from hker.symm ▸ Subgroup.subset_normalClosure hr
  apply uniform_low_connectivity s R hrel hR
  · rwa [hs]
  · rw [hs]; exact hker.symm

lemma uniform_diagram_sphere_ghost (k : Index → G →* G) (hk : IsDiagram k)
    (S : Shapes G) (n : ℕ) :
    ∃ (T : Shapes G) (q : C(Stage G S,Stage G T)),
      Represents (k (.inl P₂.identity)) q ∧ KillsSpheres q n := by
  classical
  let f := k (.inl P₂.identity)
  obtain ⟨R,hSR,hR⟩ := uniform_low_fp S
  let e := stageIncl G S R hSR
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · let T := imageShapes f id (basedShapes G R)
    let a := stageMap f id R T (image_stage_valid f id R Function.injective_id)
    refine ⟨T,a.comp e,fun _ => rfl,?_⟩
    intro b
    let : Nonempty (Stage G T) := ⟨stagePoint G T⟩
    obtain ⟨d,hd⟩ := SphereTopology.fill_zero (a.comp (e.comp b))
    exact ⟨d,hd⟩
  obtain hn | hn := (lt_or_ge n 3)
  · let T := imageShapes f id (basedShapes G R)
    let a := stageMap f id R T (image_stage_valid f id R Function.injective_id)
    refine ⟨T,a.comp e,fun _ => rfl,?_⟩
    exact (hR n (by omega)).post a
  · let m := n-1
    have hm : n = m+1 := by omega
    have hm2 : 2 ≤ m := by omega
    let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (by omega)
    let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm2
    obtain ⟨T,hT,hzero⟩ := diagram_uniform_homotopy_killing (Fin m) k hk R
    let a := (stageIncl G _ T hT).comp
      (stageMap f id R _ (image_stage_valid f id R Function.injective_id))
    have ha : a (stagePoint G R) = stagePoint G T := by
      change stageIncl G _ T hT (stageMap f id R _ _ (stagePoint G R)) = _
      rw [stageMap_point f id R _ _ rfl]
      rfl
    have hz : ∀ z : HomotopyGroup (Fin m) (Stage G R) (stagePoint G R),
        HomotopyFunctor.map a ha z = 1 := by
      intro z
      have hz := DFunLike.congr_fun hzero z
      change HomotopyFunctor.map (stageIncl G _ T hT) rfl
        (HomotopyFunctor.map (stageMap f id R _ _) (stageMap_point f id R _ _ rfl) z) = 1 at hz
      rw [HomotopyFunctor.map_comp] at hz
      exact hz
    refine ⟨T,a.comp e,fun _ => rfl,?_⟩
    rw [hm]
    apply SphereCube.killsSpheres_of_connected_image e (stagePoint G R) ?_ a (stagePoint G T) ha hz
    intro x
    exact joined_of_killsSpheres_one e (hR 1 (Or.inl rfl)) x (stagePoint G S)
end
open Set Metric Topology Cellular UniversalFInfinity.Simplicial ConcreteEnvelopes
variable {G : Type} [Group G] [Group.IsFinitelyPresented G]
  [TopologicalSpace G] [DiscreteTopology G]

local instance (priority := 2000) instDecidableEqProdNat_solutions_15_rbfe4b0_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
def iterateHom {G : Type*} [Group G] (f : G →* G) : ℕ → G →* G
  | 0 => MonoidHom.id G
  | n+1 => f.comp (iterateHom f n)

variable (k : Index → G →* G) (hk : IsDiagram k)
def ghostShapes (S : Shapes G) : ℕ → Shapes G
  | 0 => S
  | n+1 => (uniform_diagram_sphere_ghost k hk (ghostShapes S n) (n+1)).choose

def ghostMap (S : Shapes G) (n : ℕ) :
    C(Stage G (ghostShapes k hk S n),Stage G (ghostShapes k hk S (n+1))) :=
  (uniform_diagram_sphere_ghost k hk (ghostShapes k hk S n) (n+1)).choose_spec.choose
end UniversalFInfinity.Milnor

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

namespace UniversalFInfinity.Milnor
open Set Topology
universe u v
variable {G : Type u} [Group G] {H : Type v} [Group H]
lemma map_smul (φ : G →* H) (g : G) (x : Space G) :
    map φ id Function.injective_id (g • x) = φ g • map φ id Function.injective_id x := by
  change map φ id Function.injective_id (map (g * ·) id Function.injective_id x) =
    map (φ g * ·) id Function.injective_id (map φ id Function.injective_id x)
  rw [map_comp,map_comp]
  have he : (φ ∘ (g * ·)) = ((φ g * ·) ∘ φ) := funext (map_mul φ g)
  rw [he]

def smulMap (g : G) : C(Space G,Space G) := ⟨(g • ·),continuous_const_smul g⟩
end UniversalFInfinity.Milnor

namespace UniversalFInfinity.TorusGeometry
open Set Topology AscendingTorus
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)

def transition (c : Coset f) : C(Milnor.Space U,Milnor.Space U) :=
  (Milnor.smulMap (cosetOffset f c)).comp (Milnor.map f id Function.injective_id)
lemma transition_apply (c : Coset f) (x : Milnor.Space U) :
    transition f c x = cosetOffset f c • Milnor.map f id Function.injective_id x := rfl

abbrev Space := GraphBundle.Space (next f) (fun _ => ContinuousMap.id (Milnor.Space U)) (transition f)
def vertex (c : Coset f) (x : Milnor.Space U) : Space f := GraphBundle.vertex _ _ _ c x

def coordinateAction (g : Torus f) (c : Coset f) : C(Milnor.Space U,Milnor.Space U) :=
  Milnor.smulMap (actionOffset f g c)
lemma coordinateAction_compatible (hf : Function.Injective f) (g : Torus f) (c : Coset f) (x : Milnor.Space U) :
    coordinateAction f g (next f c) (transition f c x) =
      transition f (g • c) (coordinateAction f g c x) := by
  change actionOffset f g (next f c) • (cosetOffset f c • Milnor.map f id Function.injective_id x) =
    cosetOffset f (g • c) • Milnor.map f id Function.injective_id (actionOffset f g c • x)
  calc
    _ = (actionOffset f g (next f c) * cosetOffset f c) •
        Milnor.map f id Function.injective_id x := (mul_smul _ _ _).symm
    _ = (cosetOffset f (g • c) * f (actionOffset f g c)) •
        Milnor.map f id Function.injective_id x :=
      congrArg (fun element : U => element • Milnor.map f id Function.injective_id x)
        (actionOffset_next f hf g c)
    _ = cosetOffset f (g • c) •
        (f (actionOffset f g c) • Milnor.map f id Function.injective_id x) := mul_smul _ _ _
    _ = _ := congrArg (cosetOffset f (g • c) • ·)
      (Milnor.map_smul f (actionOffset f g c) x).symm
lemma coordinateAction_one (hf : Function.Injective f) (c : Coset f) (x : Milnor.Space U) :
    coordinateAction f 1 c x = x := by
  change actionOffset f 1 c • x = x
  rw [actionOffset_one f hf,one_smul]
lemma coordinateAction_mul (hf : Function.Injective f) (g h : Torus f) (c : Coset f) (x : Milnor.Space U) :
    coordinateAction f (g*h) c x = coordinateAction f g (h • c) (coordinateAction f h c x) := by
  change actionOffset f (g*h) c • x = actionOffset f g (h • c) • (actionOffset f h c • x)
  rw [actionOffset_mul f hf,mul_smul]

@[instance_reducible]
def action (hf : Function.Injective f) : MulAction (Torus f) (Space f) :=
  GraphBundle.graphAction (next f) (transition f) (next_smul f) (coordinateAction f)
    (coordinateAction_compatible f hf) (coordinateAction_one f hf) (coordinateAction_mul f hf)

variable [Fact (Function.Injective f)]
local notation "hf" => (Fact.out : Function.Injective f)
local instance instMulActionTorusSpace : MulAction (Torus f) (Space f) := action f hf
end UniversalFInfinity.TorusGeometry

namespace UniversalFInfinity.TorusGeometry

section
open Set Topology Milnor UniversalFInfinity.Simplicial AscendingTorus
open scoped Classical unitInterval
universe u v
variable {U : Type u} [Group U] (f : Monoid.End U)

attribute [local instance] OAI.UniversalFInfinity.TorusGeometry.instDecidableEqProdNat_solutions
def vertexShapes (S : Shapes U) : Shapes U := S ∪ imageShapes f id (basedShapes U S)
lemma vertexShapes_left (S : Shapes U) : S ⊆ vertexShapes f S := Finset.subset_union_left
lemma vertexShapes_map (S : Shapes U) (s : Face (stage U S)) :
    faceImage f id s.1 ∈ stage U (vertexShapes f S) := by
  apply orbitSpan_mono (show imageShapes f id (basedShapes U S) ⊆ basedShapes U (vertexShapes f S) from
    fun x hx => Finset.mem_insert_of_mem (Finset.mem_union_right _ hx))
  exact faceImage_controlled f id Function.injective_id (basedShapes U S) s

def stageForward (S : Shapes U) : C(Milnor.Stage U S,Milnor.Stage U (vertexShapes f S)) :=
  mapC _ _ (Milnor.vertexMap f id) (vertexShapes_map f S)

def left (S : Shapes U) : C(Milnor.Stage U S,Milnor.Stage U (vertexShapes f S)) :=
  stageIncl U S (vertexShapes f S) (vertexShapes_left f S)
def right (S : Shapes U) (c : Coset f) : C(Milnor.Stage U S,Milnor.Stage U (vertexShapes f S)) :=
  (stageSmul U (vertexShapes f S) (cosetOffset f c)).comp (stageForward f S)
lemma left_full (S : Shapes U) (_c : Coset f) (x : Milnor.Stage U S) :
    stageFull U (vertexShapes f S) (left f S x) = (ContinuousMap.id (Milnor.Space U)) (stageFull U S x) := rfl
lemma right_full (S : Shapes U) (c : Coset f) (x : Milnor.Stage U S) :
    stageFull U (vertexShapes f S) (right f S c x) = transition f c (stageFull U S x) := rfl

abbrev Stage (S : Shapes U) := GraphBundle.Space (next f) (fun _ => left f S) (right f S)
def stageFull (S : Shapes U) : C(Stage f S,Space f) :=
  GraphBundle.inclusion (next f) (fun _ => left f S) (right f S)
    (fun _ => ContinuousMap.id _) (transition f) (Milnor.stageFull U (vertexShapes f S)) (Milnor.stageFull U S)
    (left_full f S) (right_full f S)
lemma stageFull_closedEmbedding (S : Shapes U) : IsClosedEmbedding (stageFull f S) :=
  GraphBundle.inclusion_closedEmbedding _ _ _ _ _ _ _ _ _
    (Milnor.stageFull_embedding U _) (Milnor.stageFull_embedding U _)
end

open Set Topology Milnor AscendingTorus
open scoped Classical unitInterval
universe u v
variable {U : Type u} [Group U] (f : Monoid.End U)
variable [Fact (Function.Injective f)]
local notation "hf" => (Fact.out : Function.Injective f)
local instance instMulActionTorusSpace_1 : MulAction (Torus f) (Space f) := action f hf

variable {X : Type v} [TopologicalSpace X] [MulAction (Torus f) X]

omit [MulAction (Torus f) X] [Fact (Function.Injective f)] in
def factorStage (a : C(X,Space f)) (S : Shapes U)
    (ha : Set.range a ⊆ Set.range (stageFull f S)) : C(X,Stage f S) where
  toFun x := (ha (Set.mem_range_self x)).choose
  continuous_toFun := (stageFull_closedEmbedding f S).isEmbedding.continuous_iff.mpr (by
    convert a.continuous using 1
    funext x
    exact (ha (Set.mem_range_self x)).choose_spec)
omit [MulAction (Torus f) X] [Fact (Function.Injective f)] in
lemma factorStage_spec (a : C(X,Space f)) (S : Shapes U)
    (ha : Set.range a ⊆ Set.range (stageFull f S)) (x : X) :
    stageFull f S (factorStage f a S ha x) = a x := (ha (Set.mem_range_self x)).choose_spec
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

lemma forward_eq (n : ℕ) (c : Coset f) (x : Milnor.Space U) :
    GraphBundle.forward (next f) (transition f) n c x =
      forwardOffset f n c • Milnor.map (iterateHom f n) id Function.injective_id x := by
  induction n with
  | zero =>
    change x = 1 • Milnor.map (id : U → U) id Function.injective_id x
    rw [one_smul,Milnor.map_id]
  | succ n ih =>
    change transition f ((next f)^[n] c) (GraphBundle.forward (next f) (transition f) n c x) = _
    rw [ih,transition_apply]
    refine (congrArg (cosetOffset f ((next f)^[n] c) • ·)
      (Milnor.map_smul f (forwardOffset f n c) _)).trans ?_
    rw [←mul_smul]
    change (cosetOffset f ((next f)^[n] c) * f (forwardOffset f n c)) •
      Milnor.map f id Function.injective_id (Milnor.map (iterateHom f n) id Function.injective_id x) = _
    rw [Milnor.map_comp]
    rfl

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

lemma left_full_eq (S : Shapes U) (x : Milnor.Stage U S) :
    Milnor.stageFull U (vertexShapes f S) (left f S x) = Milnor.stageFull U S x := rfl

variable (S T : Shapes U) (n : ℕ)
variable (q : C(Milnor.Stage U (vertexShapes f S),Milnor.Stage U T)) (z : Milnor.Stage U T)
variable (H : q.Homotopy (.const _ z))
variable (hq : ∀ x,Milnor.stageFull U T (q x) =
  Milnor.map (iterateHom f n) id Function.injective_id (Milnor.stageFull U _ x))

def firstH (c : Coset f) : C(I × Milnor.Stage U (vertexShapes f S),Milnor.Stage U T) :=
  (stageSmul U T (forwardOffset f n c)).comp H.toContinuousMap
include hq in
lemma firstH_zero (c : Coset f) (x : Milnor.Stage U (vertexShapes f S)) :
    Milnor.stageFull U T (firstH f S T n q z H c (0,x)) =
      GraphBundle.forward (next f) (transition f) n c (Milnor.stageFull U _ x) := by
  change Milnor.stageFull U T (forwardOffset f n c • H (0,x)) = _
  rw [H.apply_zero,Milnor.stageFull_smul,hq,forward_eq]

def squareLeft (c : Coset f) : C(I × Milnor.Stage U S,Milnor.Stage U (vertexShapes f T)) :=
  (right f T (idx f n c)).comp ((firstH f S T n q z H c).comp
    (.prodMap (.id I) (left f S)))
def squareRight (c : Coset f) : C(I × Milnor.Stage U S,Milnor.Stage U (vertexShapes f T)) :=
  (left f T).comp ((firstH f S T n q z H (next f c)).comp
    (.prodMap (.id I) (right f S c)))

variable (Z : Shapes U) (e : ℕ)
variable (r : C(Milnor.Stage U (vertexShapes f T),Milnor.Stage U Z)) (w : Milnor.Stage U Z)
variable (J : r.Homotopy (.const _ w))
variable (hr : ∀ x,Milnor.stageFull U Z (r x) =
  Milnor.map (iterateHom f e) id Function.injective_id (Milnor.stageFull U _ x))

def secondH (c : Coset f) : C(I × Milnor.Stage U (vertexShapes f S),Milnor.Stage U Z) :=
  (stageSmul U Z (forwardOffset f e (idx f n c))).comp
    (r.comp ((left f T).comp (firstH f S T n q z H c)))
include hr in
lemma secondH_full (c : Coset f) (t : I) (x : Milnor.Stage U (vertexShapes f S)) :
    Milnor.stageFull U Z (secondH f S T n q z H Z e r c (t,x)) =
      GraphBundle.forward (next f) (transition f) e (idx f n c)
        (Milnor.stageFull U T (firstH f S T n q z H c (t,x))) := by
  change Milnor.stageFull U Z (forwardOffset f e (idx f n c) • r (left f T (firstH f S T n q z H c (t,x)))) = _
  rw [Milnor.stageFull_smul,hr,left_full_eq,forward_eq]
include hq hr in
lemma secondH_start_natural (c : Coset f) (x : Milnor.Stage U S) :
    right f Z (idx f e (idx f n c)) (secondH f S T n q z H Z e r c (0,left f S x)) =
      left f Z (secondH f S T n q z H Z e r (next f c) (0,right f S c x)) := by
  apply (Milnor.stageFull_embedding U _).injective
  rw [right_full,left_full_eq,secondH_full _ _ _ _ _ _ _ _ _ _ hr,secondH_full _ _ _ _ _ _ _ _ _ _ hr,
    firstH_zero _ _ _ _ _ _ _ hq,firstH_zero _ _ _ _ _ _ _ hq,left_full_eq,right_full]
  rw [idx_next,GraphBundle.forward_natural,GraphBundle.forward_natural]

def finalLower (c : Coset f) : C(Milnor.Stage U Z,Stage f Z) :=
  (GraphBundle.vertexMap (next f) (fun _ => left f Z) (right f Z) (finalIndex f n e c)).comp (left f Z)
def finalUpper (c : Coset f) : C(Milnor.Stage U Z,Stage f Z) :=
  (GraphBundle.vertexMap (next f) (fun _ => left f Z) (right f Z) (next f (finalIndex f n e c))).comp
    (right f Z (finalIndex f n e c))
def finalHigh (c : Coset f) : C(Milnor.Stage U Z,Stage f Z) :=
  (GraphBundle.vertexMap (next f) (fun _ => left f Z) (right f Z) (next f (finalIndex f n e c))).comp (left f Z)

def finalPoint (c : Coset f) : Milnor.Stage U Z :=
  forwardOffset f e (idx f n c) • r (left f T (forwardOffset f n c • z))

def shifted_stage (hq : ∀ x,Milnor.stageFull U T (q x) =
    Milnor.map (iterateHom f n) id Function.injective_id (Milnor.stageFull U _ x))
    (hr : ∀ x,Milnor.stageFull U Z (r x) =
    Milnor.map (iterateHom f e) id Function.injective_id (Milnor.stageFull U _ x)) : C(Stage f S,Stage f Z) :=
  GraphBundle.lift (next f) (fun _ => left f S) (right f S)
    (fun c => (finalLower f n Z e c).comp ((secondH f S T n q z H Z e r c).comp
      ⟨fun x => (0,x),continuous_const.prodMk continuous_id⟩))
    (fun c => (GraphBundle.edgeMap (next f) (fun _ => left f Z) (right f Z) (finalIndex f n e c)).comp
      ⟨fun p => (p.1,secondH f S T n q z H Z e r c (0,left f S p.2)),
        continuous_fst.prodMk ((secondH f S T n q z H Z e r c).continuous.comp
          (continuous_const.prodMk ((left f S).continuous.comp continuous_snd)))⟩)
    (fun c x => GraphBundle.edge_zero _ _ _ _ _)
    (fun c x => by
      change GraphBundle.edge (next f) (fun _ => left f Z) (right f Z) (finalIndex f n e c) 1
        (secondH f S T n q z H Z e r c (0,left f S x)) = _
      rw [GraphBundle.edge_one]
      change GraphBundle.vertex _ _ _ (next f (finalIndex f n e c))
        (right f Z (finalIndex f n e c) (secondH f S T n q z H Z e r c (0,left f S x))) =
        GraphBundle.vertex _ _ _ (finalIndex f n e (next f c))
        (left f Z (secondH f S T n q z H Z e r (next f c) (0,right f S c x)))
      rw [finalIndex_next]
      exact congrArg (GraphBundle.vertex _ _ _ _) (secondH_start_natural f S T n q z H hq Z e r hr c x))
end

open Set Topology Milnor AscendingTorus
open scoped Classical unitInterval
universe u
end UniversalFInfinity.TorusGeometry

namespace UniversalFInfinity.TorusGeometry

section
open Set Topology Milnor AscendingTorus
open scoped Classical unitInterval
universe u v
variable {U : Type u} [Group U] (f : Monoid.End U)

attribute [local instance] OAI.UniversalFInfinity.TorusGeometry.instDecidableEqProdNat_solutions_2
lemma vertexShapes_mono {S T : Shapes U} (h : S ⊆ T) : vertexShapes f S ⊆ vertexShapes f T := by
  apply Finset.union_subset_union h
  exact Finset.image_subset_image (Finset.insert_subset_insert _ h)
lemma stage_range_mono {S T : Shapes U} (h : S ⊆ T) :
    Set.range (stageFull f S) ⊆ Set.range (stageFull f T) := by
  rintro _ ⟨x,rfl⟩
  change GraphBundle.Core (C := Coset f) (A := Milnor.Stage U (vertexShapes f S)) (B := Milnor.Stage U S) at x
  cases x with
  | inl x =>
    exact ⟨GraphBundle.vertex _ _ _ x.1 (stageIncl U _ _ (vertexShapes_mono f h) x.2),rfl⟩
  | inr x =>
    exact ⟨GraphBundle.interior _ _ _ x.1 x.2.1 (stageIncl U _ _ h x.2.2),rfl⟩

def stageInclusion (S T : Shapes U) (h : S ⊆ T) : C(Stage f S,Stage f T) :=
  factorStage f (stageFull f S) T (stage_range_mono f h)

variable {X : Type v} [TopologicalSpace X]
def homotopyFactor (S : Shapes U) (a b : C(X,Stage f S))
    (H : ((stageFull f S).comp a).Homotopy ((stageFull f S).comp b))
    (h : ∀ t x,H (t,x) ∈ Set.range (stageFull f S)) : a.Homotopy b where
  toContinuousMap := factorStage f H.toContinuousMap S (Set.range_subset_iff.mpr (fun x => h x.1 x.2))
  map_zero_left x := by
    apply (stageFull_closedEmbedding f S).injective
    exact (factorStage_spec f H.toContinuousMap S _ (0,x)).trans (H.apply_zero x)
  map_one_left x := by
    apply (stageFull_closedEmbedding f S).injective
    exact (factorStage_spec f H.toContinuousMap S _ (1,x)).trans (H.apply_one x)
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
def mixedHomotopy (φ ψ : G → H) :
    (map φ evenLayer evenLayer_injective).Homotopy (map ψ oddLayer oddLayer_injective) :=
  straightHomotopy (complex G) (complex H) _ _
    (map_face φ evenLayer evenLayer_injective) (map_face ψ oddLayer oddLayer_injective) (mixed_face φ ψ)

def bridge (φ ψ : G → H) :
    (map φ evenLayer evenLayer_injective).Homotopy (map ψ evenLayer evenLayer_injective) :=
  (mixedHomotopy φ φ).trans (mixedHomotopy ψ φ).symm

end UniversalFInfinity.Milnor

namespace UniversalFInfinity.TorusGeometry
open Set Topology AscendingTorus
open scoped Classical unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)

def lowerLabel (c : Coset f) (u : U) : Torus f := origin f c * of f u
def upperLabel (c : Coset f) (u : U) : Torus f := lowerLabel f (next f c) (cosetOffset f c * f u)

def vertexToMilnor (c : Coset f) : C(Milnor.Space U,Milnor.Space (Torus f)) :=
  Milnor.map (lowerLabel f c) Milnor.evenLayer Milnor.evenLayer_injective

def edgeToMilnor (c : Coset f) : C(I × Milnor.Space U,Milnor.Space (Torus f)) :=
  (Milnor.bridge (lowerLabel f c) (upperLabel f c)).toContinuousMap

lemma edgeToMilnor_zero (c : Coset f) (x : Milnor.Space U) :
    edgeToMilnor f c (0,x) = vertexToMilnor f c x :=
  (Milnor.bridge (lowerLabel f c) (upperLabel f c)).apply_zero x
lemma edgeToMilnor_one (c : Coset f) (x : Milnor.Space U) :
    edgeToMilnor f c (1,x) = vertexToMilnor f (next f c) (transition f c x) := by
  change Milnor.bridge _ _ (1,x) = _
  rw [ContinuousMap.Homotopy.apply_one]
  change Milnor.map (upperLabel f c) Milnor.evenLayer Milnor.evenLayer_injective x =
    Milnor.map (lowerLabel f (next f c)) Milnor.evenLayer Milnor.evenLayer_injective
      (Milnor.map (cosetOffset f c * ·) id Function.injective_id (Milnor.map f id Function.injective_id x))
  rw [Milnor.map_comp,Milnor.map_comp]
  rfl

def toMilnor : C(Space f,Milnor.Space (Torus f)) :=
  GraphBundle.lift (next f) (fun _ => .id _) (transition f) (vertexToMilnor f) (edgeToMilnor f)
    (edgeToMilnor_zero f) (edgeToMilnor_one f)

variable [Fact (Function.Injective f)]
local notation "hf" => (Fact.out : Function.Injective f)
local instance instMulActionTorusSpace_2 : MulAction (Torus f) (Space f) := action f hf
end UniversalFInfinity.TorusGeometry

namespace UniversalFInfinity.TorusGeometry
open Set Topology AscendingTorus
open scoped unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)
variable [Fact (Function.Injective f)]
local notation "hf" => (Fact.out : Function.Injective f)
local instance instMulActionTorusSpace_3 : MulAction (Torus f) (Space f) := action f hf

end UniversalFInfinity.TorusGeometry

namespace UniversalFInfinity.TorusGeometry

section
open Set Topology AscendingTorus Cellular
open scoped unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)
variable [hfi : Fact (Function.Injective f)]
local notation "hf" => (Fact.out : Function.Injective f)
local instance instMulActionTorusSpace_4 : MulAction (Torus f) (Space f) := action f hf
end

open Set Topology AscendingTorus ConcreteEnvelopes
end UniversalFInfinity.TorusGeometry

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

def tailLift {Y : Type v} [TopologicalSpace Y] (n : ℕ)
    (g : ∀ m, n ≤ m → C(X m,Y))
    (hg : ∀ i j (hi : n ≤ i) (hij : i ≤ j) x,
      g i hi x = g j (hi.trans hij) (f i j hij x)) : C(Space X f,Y) := by
  let G (m : ℕ) : C(X m,Y) :=
    ⟨fun x => g (max n m) (le_max_left _ _) (f m (max n m) (le_max_right _ _) x),
      (g _ _).continuous.comp (hf _ _ _).continuous⟩
  apply lift X f G
  intro i j hij x
  let k := max n j
  have hik : max n i ≤ k := max_le_max_left n hij
  change g (max n i) _ (f i (max n i) _ x) = g k _ (f j k _ (f i j hij x))
  rw [hg _ _ _ hik,DirectedSystem.map_map',DirectedSystem.map_map']

end UniversalFInfinity.TopologicalTower

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

variable [EquivariantSystem (G := G) X f]

instance instContinuousConstSMulSpace [∀ n, ContinuousConstSMul G (X n)] : ContinuousConstSMul G (Space X f) where
  continuous_const_smul g := (continuous_iff X f _).mpr (fun n =>
    (continuous_of X f n).comp (continuous_const_smul g))

end

section
open Set Topology
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
variable (hf : ∀ i j h, IsClosedEmbedding (f i j h))
variable (k : ℕ) (U : ∀ n, k ≤ n → Set (X n))
variable (hU : ∀ i j (hi : k ≤ i) (hij : i ≤ j), f i j hij ⁻¹' U j (hi.trans hij) = U i hi)

def tailSet : Set (Space X f) := ⋃ n, ⋃ hn : k ≤ n, of X f n '' U n hn

end

open Set Metric Topology
universe u v

end UniversalFInfinity.TopologicalTower

end

end OAI
end


