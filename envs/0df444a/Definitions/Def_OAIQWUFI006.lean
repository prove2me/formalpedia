-- Prove2me | Definitions.Def_OAIQWUFI006
-- name    : OAIQWUFI006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:52:03.807806+00:00
-- url     : https://prove2.me/theorems/f7e95c5a-dfcc-4cfb-95d3-c03615a015c9
-- title:
--   OpenAI universal F∞ group split: definitions bundle 7 of 9
-- statement:
--   Definitions bundle 7 of 9 of the split of OpenAI's proof that a single group of type $F_\infty$ contains every finitely presented group (OpenAI, *A universal group of type F∞*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0). It holds OpenAI's Lean definitions, structures and instances from the modules listed below, ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas those definitions use in their bodies: several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs.
--
--   It imports bundles 5 and 6 of this split (`OAIQWUFI004`, `OAIQWUFI005`).
--
--   Modules: `BrownConstruction.lean`, `Cayley.lean`, `CellularApproximation.lean`, `CellularAttachment.lean`, `CellularChains.lean`, `CellularFillings.lean`, `CellularLifting.lean`, `CompactCells.lean`, `ControlledCells.lean`, `ControlledHomotopies.lean`, `Cylinders.lean`, `FiniteEnvelopes.lean`, `GeneralPosition.lean`, `GraphActions.lean`, `GraphBundles.lean`, `HomotopyProducts.lean`, `Idempotents.lean`, `MatrixDiagrams.lean`, `Milnor.lean`, `MilnorControl.lean`, `MilnorProducts.lean`, `PathExtensions.lean`, `SimplexDisk.lean`, `Simplicial.lean`, `SphereHomotopies.lean`, `TopologicalTowers.lean`, `TorusBundles.lean`, `TorusSpheres.lean`, `TowerCoverings.lean`, `TreeGeometry.lean`, `UniversalPresentation.lean`.
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

namespace UniversalFInfinity.CountableOvergroup
open Monoid
variable {C : Type u} [Group C] (c : ℕ → C)

noncomputable def embed : C →* Overgroup c := HNNExtension.of.comp Coprod.inl

noncomputable def a : Overgroup c := HNNExtension.of (Coprod.inr FreeConjugates.a)
noncomputable def p : Overgroup c := HNNExtension.of (Coprod.inr FreeConjugates.p)

lemma associated_left (g : FreeGroup ℕ) : associated c ⟨left g,⟨g,rfl⟩⟩ =
    ⟨right c g,⟨g,rfl⟩⟩ := by
  change (MonoidHom.ofInjective (right_injective c))
    ((MonoidHom.ofInjective (left_injective (C := C))).symm
      ((MonoidHom.ofInjective (left_injective (C := C))) g)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

lemma generator_formula (i : ℕ) : embed c (c i) =
    t c * (a c ^ i * p c * (a c ^ i)⁻¹) * (t c)⁻¹ *
      (a c ^ i * p c * (a c ^ i)⁻¹)⁻¹ := by
  have h := HNNExtension.equiv_eq_conj (φ := associated c)
    (⟨left (FreeGroup.of i),⟨FreeGroup.of i,rfl⟩⟩ : (left (C := C)).range)
  rw [associated_left] at h
  change HNNExtension.of (right c (FreeGroup.of i)) = _ at h
  simp only [right_of,left_of,map_mul] at h
  have hw : (HNNExtension.of (Coprod.inr (FreeConjugates.word i)) : Overgroup c) =
      a c ^ i * p c * (a c ^ i)⁻¹ := by
    simp only [FreeConjugates.word,map_mul,map_inv,map_pow,a,p]
  rw [hw] at h
  change embed c (c i) * _ = t c * _ * (t c)⁻¹ at h
  rw [← h]
  group

end UniversalFInfinity.CountableOvergroup

end
end UniversalFinitelyPresentedProof

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.SimplexDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
namespace UniversalFInfinity.SimplexDisk
noncomputable section

lemma simplexTruncated_positive (n : ℕ) (x : SimplexDisk.Simplex (Fin (n+1))) :
    (simplexTruncated n x).1 ∈ Positive n ↔ ∀ i, 0 < x.1 i := by
  have h := x.2.2
  rw [Fin.sum_univ_succ] at h
  constructor
  · rintro ⟨hc,hs⟩ i
    refine Fin.cases ?_ (fun j => hc j) i
    change ∑ i : Fin n, x.1 i.succ < 1 at hs
    linarith
  · intro hc
    refine ⟨fun j => hc _,?_⟩
    change ∑ i : Fin n, x.1 i.succ < 1
    linarith [hc 0]

lemma simplexDisk_open (n : ℕ) (x : SimplexDisk.Simplex (Fin (n+1))) :
    (simplexDisk n x).1 ∈ ball 0 1 ↔ ∀ i, 0 < x.1 i := by
  rw [← simplexTruncated_positive]
  change ambient n (simplexTruncated n x).1 ∈ ball 0 1 ↔ _
  rw [← ambient_positive]
  exact (ambient n).injective.mem_set_image

end
end UniversalFInfinity.SimplexDisk

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

lemma quotient_surjective : Function.Surjective (quotient K) := by
  intro x
  exact ⟨⟨⟨x.1.support,x.2.2.2⟩,coordinates K x.1.support x (subset_refl _)⟩,
    faceMap_coordinates K ⟨x.1.support,x.2.2.2⟩ x (subset_refl _)⟩

end

section
open Set Metric Topology BigOperators
open scoped Classical
universe u v w
variable {V : Type u} {W : Type v} {T : Type w}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)

lemma continuous_of_support_subset [TopologicalSpace T] (f : T → Space K) (s : Face K)
    (hs : ∀ x, (f x).1.support ⊆ s.1) (hc : ∀ v, Continuous fun x => (f x).1 v) : Continuous f := by
  let c : T → SimplexDisk.Simplex s.1 := fun x => coordinates K s.1 (f x) (hs x)
  have hcc : Continuous c := (continuous_pi fun v : s.1 => hc v.1).subtype_mk _
  have he : f = (faceMap K s) ∘ c := by
    funext x
    exact (faceMap_coordinates K s (f x) (hs x)).symm
  rw [he]
  exact (continuous_faceMap K s).comp hcc

lemma continuous_map (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) : Continuous (map K L f hf) := by
  classical
  rw [continuous_iff]
  intro s
  apply continuous_of_support_subset L _ ⟨s.1.image f,hf s⟩
  · intro x
    exact (map_support K L f hf _).trans (Finset.image_subset_image (weight_support_subset _ _))
  · intro b
    have he : (fun x : SimplexDisk.Simplex s.1 => ((map K L f hf ∘ faceMap K s) x).1 b) =
        fun x => ∑ a : s.1, if f a.1 = b then x.1 a else 0 := by
      funext x
      change (Finsupp.mapDomain f (weight s.1 x)) b = _
      rw [push_apply f _ s.1 (weight_support_subset _ _) b,← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro a _
      rw [weight_apply]
    rw [he]
    apply continuous_finsetSum
    intro a _
    split_ifs
    · exact (continuous_apply a).comp continuous_subtype_val
    · exact continuous_const

def mapC (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) : C(Space K,Space L) :=
  ⟨map K L f hf,continuous_map K L f hf⟩

lemma quotient_quotientMap : IsQuotientMap (quotient K) :=
  ⟨⟨rfl⟩,quotient_surjective K⟩

lemma continuous_prod_iff [TopologicalSpace T] [LocallyCompactSpace T]
    {Y : Type*} [TopologicalSpace Y] (f : T × Space K → Y) :
    Continuous f ↔ ∀ s : Face K, Continuous (fun p : T × SimplexDisk.Simplex s.1 => f (p.1,faceMap K s p.2)) := by
  constructor
  · intro hf s
    exact hf.comp (continuous_fst.prodMk ((continuous_faceMap K s).comp continuous_snd))
  · intro hf
    apply (quotient_quotientMap K).continuous_lift_prod_right
    rw [continuous_def]
    intro O hO
    have hp : (fun p : T × (Σ s : Face K, SimplexDisk.Simplex s.1) => f (p.1,quotient K p.2)) ⁻¹' O =
      ⋃ s : Face K, (fun p : T × SimplexDisk.Simplex s.1 => (p.1,⟨s,p.2⟩)) ''
        ((fun p : T × SimplexDisk.Simplex s.1 => f (p.1,faceMap K s p.2)) ⁻¹' O) := by
      ext p
      simp only [mem_preimage,mem_iUnion,mem_image]
      constructor
      · intro h
        exact ⟨p.2.1,⟨p.1,p.2.2⟩,h,rfl⟩
      · rintro ⟨s,p,h,rfl⟩
        exact h
    rw [hp]
    apply isOpen_iUnion
    intro s
    exact (IsOpenMap.id.prodMap isOpenMap_sigmaMk) _ ((hf s).isOpen_preimage O hO)

end

section
open Set Metric Topology BigOperators
open scoped Classical unitInterval
universe u v
variable {V : Type u} {W : Type v}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)

variable (f g : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) (hg : ∀ s : Face K, s.1.image g ∈ L)
variable (hfg : ∀ s : Face K, s.1.image f ∪ s.1.image g ∈ L)

lemma continuous_straight : Continuous (fun p : I × Space K => straight K L f g hf hg hfg p.1 p.2) := by
  rw [continuous_prod_iff]
  intro s
  apply continuous_of_support_subset L _ ⟨s.1.image f ∪ s.1.image g,hfg s⟩
  · intro p
    exact (blend_support _ _ p.1).trans (Finset.union_subset_union
      ((map_support K L f hf _).trans (Finset.image_subset_image (weight_support_subset _ _)))
      ((map_support K L g hg _).trans (Finset.image_subset_image (weight_support_subset _ _))))
  · intro b
    change Continuous (fun p : I × SimplexDisk.Simplex s.1 =>
      (1-(p.1:ℝ)) * (map K L f hf (faceMap K s p.2)).1 b +
        (p.1:ℝ) * (map K L g hg (faceMap K s p.2)).1 b)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_eval L b).comp ((continuous_map K L f hf).comp ((continuous_faceMap K s).comp continuous_snd)))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((continuous_eval L b).comp ((continuous_map K L g hg).comp ((continuous_faceMap K s).comp continuous_snd))))

def straightHomotopy : (mapC K L f hf).Homotopy (mapC K L g hg) where
  toFun p := straight K L f g hf hg hfg p.1 p.2
  continuous_toFun := continuous_straight K L f g hf hg hfg
  map_zero_left _ := blend_zero L _ _ _ _ _
  map_one_left _ := blend_one L _ _ _ _ _

end
open Set Metric Topology BigOperators
open scoped Classical
universe u
variable {V : Type u} (K L : PreAbstractSimplicialComplex V) (hKL : ∀ s ∈ K, s ∈ L)

lemma inclusion_isClosedMap : IsClosedMap (inclusion K L hKL) := by
  intro A hA
  rw [isClosed_iff]
  intro s
  let T : Set (Face K) := {t | t.1 ⊆ s.1}
  have hT : T.Finite := by
    have hf := s.1.powerset.finite_toSet.preimage (Subtype.val_injective : Function.Injective (Subtype.val : Face K → Finset V)).injOn
    convert hf using 1
    ext t
    simp only [T,mem_ofPred_eq,mem_preimage,Finset.mem_coe,Finset.mem_powerset]
  have hc : IsClosed (⋃ t ∈ T, inclusion K L hKL '' (A ∩ Set.range (faceMap K t))) := by
    apply hT.isClosed_biUnion
    intro t _
    exact (((isCompact_range (continuous_faceMap K t)).inter_left hA).image
      (continuous_inclusion K L hKL)).isClosed
  have he : inclusion K L hKL '' A ∩ Set.range (faceMap L s) =
      ⋃ t ∈ T, inclusion K L hKL '' (A ∩ Set.range (faceMap K t)) := by
    ext x
    simp only [mem_inter_iff,mem_image,mem_iUnion]
    constructor
    · rintro ⟨⟨y,hy,rfl⟩,hs⟩
      rw [range_faceMap] at hs
      let t : Face K := ⟨y.1.support,y.2.2.2⟩
      refine ⟨t,hs,y,⟨hy,?_⟩,rfl⟩
      rw [range_faceMap]
      exact Finset.Subset.refl _
    · rintro ⟨t,ht,y,⟨hy,hyt⟩,rfl⟩
      refine ⟨⟨y,hy,rfl⟩,?_⟩
      rw [range_faceMap] at hyt ⊢
      exact hyt.trans (show t.1 ⊆ s.1 from ht)
  rw [←he] at hc
  have hp := hc.preimage (continuous_faceMap L s)
  simpa only [preimage_inter,preimage_range,inter_univ] using hp

lemma inclusion_closedEmbedding : IsClosedEmbedding (inclusion K L hKL) :=
  .of_continuous_injective_isClosedMap (continuous_inclusion K L hKL)
    (inclusion_injective K L hKL) (inclusion_isClosedMap K L hKL)
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

def map (φ : G → H) (ρ : ℕ → ℕ) (hρ : Function.Injective ρ) : C(Space G,Space H) :=
  Simplicial.mapC (complex G) (complex H) (fun v => (ρ v.1,φ v.2)) (map_face φ ρ hρ)

lemma map_comp {J : Type*} (φ : G → H) (ψ : H → J)
    (ρ τ : ℕ → ℕ) (hρ : Function.Injective ρ) (hτ : Function.Injective τ) (x : Space G) :
    map ψ τ hτ (map φ ρ hρ x) = map (ψ ∘ φ) (τ ∘ ρ) (hτ.comp hρ) x :=
by
  apply Subtype.ext
  exact Finsupp.mapDomain_comp.symm

end UniversalFInfinity.Milnor

namespace UniversalFInfinity.Simplicial
open Set Metric Topology BigOperators
universe u
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

lemma faceDisk_open {n : ℕ} (s : Cell K n) (x : SimplexDisk.Simplex s.1.1) :
    (faceDisk K s x).1 ∈ ball 0 1 ↔ (faceMap K s.1 x).1.support = s.1.1 := by
  rw [support_eq_iff]
  exact (SimplexDisk.simplexDisk_open n _).trans (SimplexDisk.reindex_positive _ _)

lemma characteristic_bijOn {n : ℕ} (s : Cell K n) :
    Set.BijOn (characteristic K s) (ball 0 1) {x | x.1.support = s.1.1} := by
  constructor
  · intro x hx
    let d : closedBall (0 : Fin n → ℝ) 1 := ⟨x,ball_subset_closedBall hx⟩
    rw [show characteristic K s x = diskMap K s d from characteristic_disk K s d]
    exact (faceDisk_open K s ((faceDisk K s).symm d)).mp (by simpa using hx)
  constructor
  · intro x hx y hy hxy
    have hxy' : diskMap K s ⟨x,ball_subset_closedBall hx⟩ = diskMap K s ⟨y,ball_subset_closedBall hy⟩ := by
      simpa only [← characteristic_disk] using hxy
    exact congrArg Subtype.val (diskMap_injective K s hxy')
  · intro x hx
    let z := coordinates K s.1.1 x (by rw [hx])
    let d := faceDisk K s z
    have hd : d.1 ∈ ball 0 1 := (faceDisk_open K s z).mpr (by rwa [faceMap_coordinates])
    exact ⟨d.1,hd,(characteristic_disk K s d).trans (by
      change faceMap K s.1 ((faceDisk K s).symm (faceDisk K s z)) = x
      rw [Homeomorph.symm_apply_apply]
      exact faceMap_coordinates K s.1 x _)⟩

def characteristicPE {n : ℕ} (s : Cell K n) : PartialEquiv (Fin n → ℝ) (Space K) :=
  (characteristic_bijOn K s).toPartialEquiv _ _ _

lemma characteristicPE_open {n : ℕ} (s : Cell K n) :
    characteristicPE K s '' ball 0 1 = {x | x.1.support = s.1.1} :=
  (characteristic_bijOn K s).image_eq

lemma characteristicPE_closed {n : ℕ} (s : Cell K n) :
    characteristicPE K s '' closedBall 0 1 = Set.range (faceMap K s.1) := by
  rw [← diskMap_range]
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨⟨z,hz⟩,(characteristic_disk K s ⟨z,hz⟩).symm⟩
  · rintro ⟨z,rfl⟩
    exact ⟨z.1,z.2,characteristic_disk K s z⟩

lemma characteristicPE_continuous {n : ℕ} (s : Cell K n) :
    ContinuousOn (characteristicPE K s) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (closedBall (0:Fin n→ℝ) 1).domRestrict (characteristicPE K s) = diskMap K s := by
    funext x
    exact characteristic_disk K s x
  rw [he]
  exact (diskMap K s).continuous

lemma characteristicPE_continuous_symm {n : ℕ} (s : Cell K n) :
    ContinuousOn (characteristicPE K s).symm (characteristicPE K s).target := by
  let e := characteristicPE K s
  have he : IsEmbedding (e.source.domRestrict e) := by
    let inc : ball (0:Fin n→ℝ) 1 → closedBall (0:Fin n→ℝ) 1 := fun x => ⟨x.1,ball_subset_closedBall x.2⟩
    have hi : IsEmbedding inc := IsEmbedding.subtypeVal.codRestrict _ (fun x => ball_subset_closedBall x.2)
    have heq : e.source.domRestrict e = (diskMap K s) ∘ inc := by
      funext x
      exact characteristic_disk K s (inc x)
    rw [heq]
    exact ((diskMap K s).continuous.isClosedEmbedding (diskMap_injective K s)).isEmbedding.comp hi
  let H : e.source ≃ₜ e.target := e.toEquiv.toHomeomorphOfIsInducing
    (he.isInducing.codRestrict (fun x => e.map_source x.2))
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp H.symm.continuous

lemma support_lt_of_sphere {n : ℕ} (s : Cell K n) (x : Fin n → ℝ) (hx : x ∈ sphere 0 1) :
    (characteristicPE K s x).1.support.card < s.1.1.card := by
  have hd := characteristic_disk K s ⟨x,sphere_subset_closedBall hx⟩
  have hs : (characteristicPE K s x).1.support ⊆ s.1.1 := by
    rw [show characteristicPE K s x = diskMap K s ⟨x,sphere_subset_closedBall hx⟩ from hd]
    exact weight_support_subset _ _
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hs,?_⟩
  intro he
  have ho : x ∈ ball (0:Fin n→ℝ) 1 := by
    have hh := (faceDisk_open K s ((faceDisk K s).symm ⟨x,sphere_subset_closedBall hx⟩)).mpr (by
      change (characteristic K s x).1.support = s.1.1 at he
      rwa [hd] at he)
    simpa only [Homeomorph.apply_symm_apply] using hh
  exact sphere_disjoint_ball.notMem_of_mem_left hx ho

lemma subcells_finite (s : Face K) (n : ℕ) : Set.Finite {c : Cell K n | c.1.1 ⊆ s.1} := by
  classical
  have hinj : Function.Injective (fun c : Cell K n => c.1.1) := Subtype.val_injective.comp Subtype.val_injective
  have hfin := (s.1.powerset.finite_toSet).preimage hinj.injOn
  convert hfin using 1
  ext c
  simp only [mem_ofPred_eq,mem_preimage,Finset.mem_coe,Finset.mem_powerset]

noncomputable def subcells (s : Face K) (n : ℕ) : Finset (Cell K n) := (subcells_finite K s n).toFinset

lemma characteristic_boundary {n : ℕ} (s : Cell K n) :
    MapsTo (characteristicPE K s) (sphere 0 1)
      (⋃ (m < n) (j ∈ subcells K s.1 m), characteristicPE K j '' closedBall 0 1) := by
  intro x hx
  let y := characteristicPE K s x
  let t : Face K := ⟨y.1.support,y.2.2.2⟩
  let m := y.1.support.card-1
  let c : Cell K m := cellOfFace K t
  have hpos : 0 < y.1.support.card := Finset.card_pos.mpr (support_nonempty y.2.2.1)
  have hlt : y.1.support.card < s.1.1.card := support_lt_of_sphere K s x hx
  have hmn : m < n := by dsimp [m]; rw [s.2] at hlt; omega
  have hcs : c ∈ subcells K s.1 m := by
    rw [subcells,Set.Finite.mem_toFinset]
    change y.1.support ⊆ s.1.1
    rw [show y = diskMap K s ⟨x,sphere_subset_closedBall hx⟩ from characteristic_disk K s ⟨x,sphere_subset_closedBall hx⟩]
    exact weight_support_subset _ _
  refine mem_iUnion.mpr ⟨m,mem_iUnion.mpr ⟨hmn,mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hcs,?_⟩⟩⟩⟩
  rw [characteristicPE_closed,range_faceMap]
  exact Finset.Subset.refl _

instance cwComplex : Topology.CWComplex (Set.univ : Set (Space K)) where
  cell := Cell K
  map _ := characteristicPE K
  source_eq _ _ := rfl
  continuousOn _ := characteristicPE_continuous K
  continuousOn_symm _ := characteristicPE_continuous_symm K
  pairwiseDisjoint' := by
    intro a _ b _ hab
    change Disjoint (characteristicPE K a.2 '' ball 0 1) (characteristicPE K b.2 '' ball 0 1)
    rw [characteristicPE_open,characteristicPE_open]
    apply Set.disjoint_left.mpr
    intro x hx hy
    have he : a.2.1.1 = b.2.1.1 := hx.symm.trans hy
    have hn : a.1 = b.1 := by have hc := congrArg Finset.card he; rw [a.2.2,b.2.2] at hc; omega
    apply hab
    rcases a with ⟨n,a⟩
    rcases b with ⟨m,b⟩
    dsimp at hn
    subst m
    exact congrArg (Sigma.mk n) (Subtype.ext (Subtype.ext he))
  mapsTo' _ s := ⟨subcells K s.1,characteristic_boundary K s⟩
  closed' A _ hA := by
    rw [isClosed_iff]
    intro s
    have hc := hA _ (cellOfFace K s)
    rw [characteristicPE_closed] at hc
    have hp := hc.preimage (continuous_faceMap K s)
    have he : (faceMap K s) ⁻¹' (A ∩ Set.range (faceMap K (cellOfFace K s).1)) = (faceMap K s) ⁻¹' A := by
      ext z; simp only [mem_preimage,mem_inter_iff]; exact and_iff_left (mem_range_self z)
    rwa [he] at hp
  union' := by
    apply Set.Subset.antisymm (subset_univ _)
    intro x _
    let s : Face K := ⟨x.1.support,x.2.2.2⟩
    refine mem_iUnion.mpr ⟨s.1.card-1,mem_iUnion.mpr ⟨cellOfFace K s,?_⟩⟩
    rw [characteristicPE_closed,range_faceMap]
    exact Finset.Subset.refl _
end UniversalFInfinity.Simplicial

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CompactCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators

open Set Metric Topology

namespace UniversalFInfinity.Simplicial
open Set Metric Topology BigOperators
open scoped Classical
universe u
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

lemma compact_bounded_vertices {A : Set (Space K)} (hA : IsCompact A) :
    ∃ S : Finset V, ∀ x ∈ A, x.1.support ⊆ S := by
  let T := {p : Σ n, Topology.RelCWComplex.cell (Set.univ : Set (Space K)) n |
    (A ∩ CWComplex.openCell p.1 p.2).Nonempty}
  have hT : T.Finite := Cellular.compact_finitely_many_cells hA
  let S := hT.toFinset.biUnion (fun p => p.2.1.1)
  refine ⟨S,?_⟩
  intro x hx
  let s : Face K := ⟨x.1.support,x.2.2.2⟩
  let c := cellOfFace K s
  have hc : (⟨s.1.card-1,c⟩ : Σ n, Topology.RelCWComplex.cell (Set.univ : Set (Space K)) n) ∈ hT.toFinset := by
    rw [hT.mem_toFinset]
    refine ⟨x,hx,?_⟩
    change x ∈ characteristicPE K c '' ball 0 1
    rw [characteristicPE_open]
    rfl
  exact Finset.subset_biUnion_of_mem (fun p => p.2.1.1) hc

end UniversalFInfinity.Simplicial

open Set Metric Topology

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

lemma continuousOn_iff_characteristic {Y : Type v} [TopologicalSpace Y] (f : X → Y) :
    ContinuousOn f C ↔ ∀ n (i : RelCWComplex.cell C n),
      Continuous (f ∘ characteristic n i) := by
  constructor
  · intro hf n i
    exact hf.comp_continuous (characteristic n i).continuous
      (fun x => CWComplex.closedCell_subset_complex n i ⟨x.1,x.2,rfl⟩)
  · intro hf
    rw [continuousOn_iff_continuous_domRestrict, continuous_iff_isClosed]
    intro S hS
    have hclosed : IsClosed (C ∩ f ⁻¹' S) := by
      apply (CWComplex.closed C _ inter_subset_left).2
      intro n i
      have hpre : IsClosed ((f ∘ characteristic n i) ⁻¹' S) :=
        hS.preimage (hf n i)
      have hcompact := hpre.isCompact.image (characteristic n i).continuous
      convert hcompact.isClosed using 1
      ext x
      constructor
      · rintro ⟨⟨hxC,hxS⟩, y,hy,rfl⟩
        exact ⟨⟨y,hy⟩,hxS,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨⟨CWComplex.closedCell_subset_complex n i ⟨y.1,y.2,rfl⟩,hy⟩,
          y.1,y.2,rfl⟩
    convert hclosed.preimage continuous_subtype_val using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, and_iff_right x.2, Set.domRestrict_apply]

section Attach
variable {E : Type v} [TopologicalSpace E] {n : ℕ}

lemma attachValue_old (a : X → E) (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    {x : X} (hx : x ∈ Skeleton C n) : attachValue a e x = a x := by
  classical
  simp only [attachValue, ite_eq_left hx]

lemma attachValue_interior (a : X → E) (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (i : RelCWComplex.cell C n) (y : Disk n) (hy : y.1 ∈ ball 0 1) :
    attachValue a e (characteristic n i y) = e i y := by
  classical
  have hx : characteristic n i y ∈ CWComplex.openCell n i := ⟨y.1,hy,rfl⟩
  have h : ∃ j : RelCWComplex.cell C n,
      characteristic n i y ∈ CWComplex.openCell n j := ⟨i,hx⟩
  rw [attachValue,ite_eq_right (openCell_not_skeleton n i hx),dite_eq_left h]
  have hi : h.choose = i := by
    by_contra hne
    have hd := CWComplex.disjoint_openCell_of_ne (C := C) (i := h.choose) (j := i)
      (fun hEq => hne (sigma_mk_injective hEq))
    exact Set.disjoint_left.mp hd h.choose_spec hx
  have hz := h.choose_spec.choose_spec.1
  have hmap : RelCWComplex.map n i h.choose_spec.choose = characteristic n i y := by
    calc
      RelCWComplex.map n i h.choose_spec.choose =
          RelCWComplex.map n h.choose h.choose_spec.choose :=
        congrArg (fun k => RelCWComplex.map n k h.choose_spec.choose) hi.symm
      _ = _ := h.choose_spec.choose_spec.2
  have hcoord : h.choose_spec.choose = y.1 :=
    (RelCWComplex.map n i).injOn
      (by simpa only [RelCWComplex.source_eq] using hz)
      (by simpa only [RelCWComplex.source_eq] using hy) hmap
  exact (congrArg (fun k => e k ⟨h.choose_spec.choose,ball_subset_closedBall hz⟩) hi).trans
    (congrArg (e i) (Subtype.ext hcoord))

lemma attachValue_characteristic (a : X → E)
    (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (he : ∀ i (x : Sphere n), e i (boundary n x) =
      a (characteristic n i (boundary n x)))
    (i : RelCWComplex.cell C n) (y : Disk n) :
    attachValue a e (characteristic n i y) = e i y := by
  by_cases hy : y.1 ∈ ball 0 1
  · exact attachValue_interior a e i y hy
  · have hs : y.1 ∈ sphere 0 1 := le_antisymm y.2 (le_of_not_gt hy)
    have hx : characteristic n i y ∈ Skeleton C n := sphere_mem_skeleton n i ⟨y,hs⟩
    rw [attachValue_old a e hx]
    exact (he i ⟨y,hs⟩).symm

lemma attachValue_continuous (a : X → E) (ha : ContinuousOn a (Skeleton C n))
    (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (he : ∀ i (x : Sphere n), e i (boundary n x) =
      a (characteristic n i (boundary n x))) :
    ContinuousOn (attachValue a e) (Skeleton C (n+1)) := by
  apply (continuousOn_iff_characteristic (C := Skeleton C (n+1)) _).2
  intro m j
  change Continuous (fun x : Disk m => attachValue a e (characteristic m j.1 x))
  have hm : m < n+1 := by
    have h : (m : ℕ∞) < ((n+1 : ℕ) : ℕ∞) := by
      simpa only [RelCWComplex.skeletonLT_I,Set.mem_ofPred_eq] using j.2
    exact_mod_cast h
  rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | hm
  · have hEq : (fun x : Disk m => attachValue a e (characteristic m j.1 x)) =
        (fun x : Disk m => a (characteristic m j.1 x)) := by
      funext x
      exact attachValue_old a e (characteristic_mem_skeleton hm j.1 x)
    rw [hEq]
    exact ha.comp_continuous (characteristic m j.1).continuous
      (characteristic_mem_skeleton hm j.1)
  · subst m
    have hEq : (fun x : Disk n => attachValue a e (characteristic n j.1 x)) = e j.1 := by
      funext x
      exact attachValue_characteristic a e he j.1 x
    rw [hEq]
    exact (e j.1).continuous

end Attach

namespace PartialLift
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
variable {p : C(E,B)} {f : C(X,B)} {n : ℕ}

def onSphere (a : PartialLift (C := C) p f n) (i : RelCWComplex.cell C n) :
    C(Sphere n,E) :=
  ⟨fun x => a.val (characteristic n i (boundary n x)),
    a.continuousOn.comp_continuous
      ((characteristic n i).continuous.comp (continuous_boundary n))
      (sphere_mem_skeleton n i)⟩

lemma exists_cell_extension (a : PartialLift (C := C) p f n) (hp : DiskRLP p)
    (i : RelCWComplex.cell C n) :
    ∃ e : C(Disk n,E),
      (∀ x, e (boundary n x) = a.val (characteristic n i (boundary n x))) ∧
      ∀ x, p (e x) = f (characteristic n i x) := by
  apply hp n (a.onSphere i) (f.comp (characteristic n i))
  intro x
  exact a.fac _ (sphere_mem_skeleton n i x)

noncomputable def next (a : PartialLift (C := C) p f n) (hp : DiskRLP p) :
    PartialLift (C := C) p f (n+1) := by
  choose e hb hf using fun i => a.exists_cell_extension hp i
  refine ⟨attachValue a.val e,attachValue_continuous a.val a.continuousOn e hb,?_⟩
  intro x hx
  have hdecomp : Skeleton C (n+1) = Skeleton C n ∪
      ⋃ i : RelCWComplex.cell C n, CWComplex.closedCell n i := by
    simpa only [Skeleton,Nat.cast_add,Nat.cast_one] using
      (CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ (C := C) n).symm
  rw [hdecomp] at hx
  rcases hx with hx | hx
  · rw [attachValue_old a.val e hx]
    exact a.fac x hx
  · obtain ⟨i,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
    rw [show RelCWComplex.map n i y = characteristic n i ⟨y,hy⟩ from rfl,
      attachValue_characteristic a.val e hb]
    exact hf i ⟨y,hy⟩

end PartialLift

section Lift
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B] [Nonempty E]
variable {p : C(E,B)} (hp : DiskRLP p) (f : C(X,B))

noncomputable def stages : ∀ n, PartialLift (C := C) p f n
  | 0 => PartialLift.zero
  | n+1 => (stages n).next hp

noncomputable def liftValue (x : X) : E := by
  classical
  exact if hx : x ∈ C then (stages (C := C) hp f (exists_skeleton (C := C) hx).choose).val x
    else Classical.choice ‹Nonempty E›

end Lift

noncomputable section

variable {Y : Type u} [TopologicalSpace Y]

theorem pathEndpoint_RLP (hY : SphereFillable Y) : DiskRLP (@pathEndpoint Y _) := by
  intro n a b h
  obtain ⟨F,hF⟩ := hY (n+1) (cylinderBoundaryMap a b h)
  let e : C(Disk n,C(unitInterval,Y)) :=
    (F.comp ⟨fun q : Disk n × unitInterval => diskCons q.1 q.2,continuous_diskCons⟩).curry
  refine ⟨e,?_,?_⟩
  · intro x
    apply ContinuousMap.ext
    intro t
    let s : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
    have hs : s ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) t)).1 ∈ sphere 0 1
      rw [diskTail_cons]
      exact x.2
    change F (diskCons (boundary n x) t) = a x t
    rw [show diskCons (boundary n x) t = boundary (n+1) s from rfl,hF,
      cylinderBoundaryMap_face a b h none ⟨s,hs⟩]
    change a (faceSphere ⟨s,hs⟩) (diskTime (diskCons (boundary n x) t)) = a x t
    rw [diskTime_cons]
    congr 1
  · intro x
    apply Prod.ext
    · let s : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some false) := by
        change (diskCons x 0).1 0 = -1
        norm_num [diskCons]
      change F (diskCons x 0) = (b x).1
      rw [show diskCons x 0 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some false) ⟨s,hs⟩]
      change (b (diskTail (diskCons x 0))).1 = (b x).1
      rw [diskTail_cons]
    · let s : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some true) := by
        change (diskCons x 1).1 0 = 1
        norm_num [diskCons]
      change F (diskCons x 1) = (b x).2
      rw [show diskCons x 1 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some true) ⟨s,hs⟩]
      change (b (diskTail (diskCons x 1))).2 = (b x).2
      rw [diskTail_cons]

end
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

local instance (priority := 2000) instDecidableEqProdNat_solutions_r7f5f75_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
def boundedContraction (N : ℕ) (g : G) :
    (boundedInclusion (G := G) N).Homotopy (ContinuousMap.const _ (vertex (N,g))) := by
  let H := Simplicial.straightHomotopy (bounded G N) (complex G) id (fun _ => (N,g))
    (bounded_id_face N) (bounded_const_face N g) (bounded_contiguous N g)
  exact H.cast (ContinuousMap.ext (fun x => bounded_map_id N x))
    (ContinuousMap.ext (fun x => map_const_vertex (bounded G N) (N,g) (bounded_const_face N g) x))

lemma compactMap_bounded {A : Type v} [TopologicalSpace A] [CompactSpace A] (f : C(A,Space G)) :
    ∃ N : ℕ, ∃ F : C(A,Simplicial.Space (bounded G N)), (boundedInclusion N).comp F = f := by
  obtain ⟨S,hS⟩ := Simplicial.compact_bounded_vertices (complex G) (isCompact_range f.continuous)
  let N := S.sup Prod.fst + 1
  have hN (a : A) (v : ℕ × G) (hv : v ∈ (f a).1.support) : v.1 < N := by
    exact Nat.lt_succ_of_le (Finset.le_sup (f := Prod.fst) (hS (f a) (mem_range_self a) hv))
  let F : A → Simplicial.Space (bounded G N) := fun a =>
    ⟨(f a).1,(f a).2.1,(f a).2.2.1,(f a).2.2.2,hN a⟩
  have hc : Continuous F :=
    (Simplicial.inclusion_closedEmbedding (bounded G N) (complex G)
      (fun _ h => bounded_le G N h)).isEmbedding.continuous_iff.mpr f.continuous
  exact ⟨N,⟨F,hc⟩,rfl⟩

lemma compactMap_nullhomotopic {A : Type v} [TopologicalSpace A] [CompactSpace A]
    (g : G) (f : C(A,Space G)) : ∃ y, Nonempty (f.Homotopy (ContinuousMap.const _ y)) := by
  obtain ⟨N,F,hF⟩ := compactMap_bounded f
  exact ⟨vertex (N,g),⟨((boundedContraction N g).compContinuousMap F).cast hF rfl⟩⟩

lemma sphereFillable (g : G) : Cellular.SphereFillable (Space G) := by
  intro n f
  cases n with
  | zero =>
    refine ⟨ContinuousMap.const _ (vertex (0,g)),?_⟩
    intro x
    have hx : False := by
      have he := x.2
      simp only [Metric.mem_sphere,Subsingleton.elim x.1 0,dist_self] at he
      exact zero_ne_one he
    exact hx.elim
  | succ n =>
    let := SphereTopology.sphere_nonempty n
    obtain ⟨y,⟨H⟩⟩ := compactMap_nullhomotopic g f
    obtain ⟨F,hF⟩ := SphereTopology.extends_of_nullhomotopic H.symm
    exact ⟨F,fun x => ContinuousMap.congr_fun hF x⟩

end

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical
universe u v
variable {G : Type u} [Group G]

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_1
lemma orbitSpan_finite_representatives (S : Finset (Finset (ℕ × G))) :
    ∃ T : Finset (Finset (ℕ × G)), ∀ t ∈ orbitSpan S, ∃ s ∈ T, ∃ g : G, t = translate g s := by
  refine ⟨S.biUnion Finset.powerset,?_⟩
  intro t ht
  obtain ⟨g,s,hs,hts⟩ := ht.2
  have hh : translate g⁻¹ t ⊆ s := by
    have hh := translate_mono g⁻¹ hts
    simpa only [translate_mul,inv_mul_cancel,translate_one] using hh
  refine ⟨translate g⁻¹ t,Finset.mem_biUnion.mpr ⟨s,hs,Finset.mem_powerset.mpr hh⟩,g,?_⟩
  rw [translate_mul,mul_inv_cancel,translate_one]

end
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v
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

def loopMap (f : C(X,Y)) (hf : f x = y) (p : GenLoop N X x) : GenLoop N Y y :=
  ⟨f.comp p.1,fun t ht => by change f (p t) = y; rw [GenLoop.boundary p t ht,hf]⟩

lemma loopMap_homotopic (f : C(X,Y)) (hf : f x = y) {p q : GenLoop N X x}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (loopMap f hf p) (loopMap f hf q) :=
  h.comp_continuousMap f

def map (f : C(X,Y)) (hf : f x = y) : HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (loopMap f hf) (fun _ _ h => loopMap_homotopic f hf h)

@[simp] lemma map_mk (f : C(X,Y)) (hf : f x = y) (p : GenLoop N X x) :
    map f hf (Quotient.mk' p) = Quotient.mk' (loopMap f hf p) := rfl

lemma loopMap_const (f : C(X,Y)) (hf : f x = y) :
    loopMap (N := N) f hf GenLoop.const = GenLoop.const := by
  ext t
  exact hf

lemma loopMap_transAt [DecidableEq N] (i : N) (f : C(X,Y)) (hf : f x = y)
    (p q : GenLoop N X x) :
    loopMap f hf (GenLoop.transAt i p q) = GenLoop.transAt i (loopMap f hf p) (loopMap f hf q) := by
  ext t
  change f (if (t i : ℝ) ≤ 1/2 then p _ else q _) =
    if (t i : ℝ) ≤ 1/2 then f (p _) else f (q _)
  split <;> rfl

lemma map_comp {Z : Type*} [TopologicalSpace Z] {z : Z}
    (f : C(X,Y)) (hf : f x = y) (g : C(Y,Z)) (hg : g y = z)
    (a : HomotopyGroup N X x) :
    map g hg (map f hf a) = map (g.comp f) (by change g (f x) = z; rw [hf,hg]) a := by
  induction a using Quotient.inductionOn with | h p =>
  rfl

end
open scoped Topology Topology.Homotopy
universe u v w
end UniversalFInfinity.HomotopyFunctor
namespace UniversalFInfinity.Milnor

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u
variable {G : Type u} [Group G]

local instance (priority := 2000) instDecidableEqProdNat_solutions_5_r7f5f75_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
instance instMulActionElemFinsuppProdNatRealSpace : MulAction G (Space G) where
  smul g x := map (g * ·) id Function.injective_id x
  one_smul x := by
    change map (1 * ·) id Function.injective_id x = x
    apply Subtype.ext
    change x.1.mapDomain (fun v => (v.1,1*v.2)) = x.1
    rw [show (fun v : ℕ × G => (v.1,1*v.2)) = id from funext (fun v => Prod.ext rfl (one_mul v.2))]
    exact Finsupp.mapDomain_id
  mul_smul g h x := by
    change map ((g*h) * ·) id Function.injective_id x = map (g * ·) id Function.injective_id (map (h * ·) id Function.injective_id x)
    rw [map_comp]
    have he : (fun a => (g*h)*a) = ((g * ·) ∘ (h * ·)) := funext (mul_assoc g h)
    rw [he]
    rfl

instance instContinuousConstSMulElemFinsuppProdNatRealSpace : ContinuousConstSMul G (Space G) where
  continuous_const_smul g := (map (g * ·) id Function.injective_id).continuous

end
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical
universe u v
variable (G : Type u) [Group G]
attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_6
lemma stageFull_embedding (S : Shapes G) : IsClosedEmbedding (stageFull G S) :=
  inclusion_closedEmbedding _ _ (fun _ h => orbitSpan_le _ h)

def stageSmul (S : Shapes G) (g : G) : C(Stage G S,Stage G S) :=
  Simplicial.mapC _ _ (fun v => (v.1,g*v.2)) (stage_translate G S g)

instance stageAction (S : Shapes G) : MulAction G (Stage G S) where
  smul g x := stageSmul G S g x
  one_smul x := by
    apply Subtype.ext
    change x.1.mapDomain (fun v => (v.1,1*v.2)) = x.1
    rw [show (fun v : ℕ × G => (v.1,1*v.2)) = id from funext (fun v => Prod.ext rfl (one_mul v.2))]
    exact Finsupp.mapDomain_id
  mul_smul g h x := by
    apply Subtype.ext
    change x.1.mapDomain (fun v => (v.1,(g*h)*v.2)) =
      (x.1.mapDomain (fun v => (v.1,h*v.2))).mapDomain (fun v => (v.1,g*v.2))
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext v
    exact Prod.ext rfl (mul_assoc _ _ _)

instance stageContinuousAction (S : Shapes G) : ContinuousConstSMul G (Stage G S) where
  continuous_const_smul g := (stageSmul G S g).continuous

lemma stageFull_smul (S : Shapes G) (g : G) (x : Stage G S) :
    stageFull G S (g • x) = g • stageFull G S x := rfl
lemma stageIncl_smul (S T : Shapes G) (h : S ⊆ T) (g : G) (x : Stage G S) :
    stageIncl G S T h (g • x) = g • stageIncl G S T h x := rfl

lemma compact_controlled {K : Set (Space G)} (hK : IsCompact K) :
    ∃ S : Shapes G, K ⊆ Set.range (stageFull G S) := by
  obtain ⟨V,hV⟩ := Simplicial.compact_bounded_vertices (complex G) hK
  refine ⟨V.powerset,?_⟩
  intro x hx
  have hm : x.1.support ∈ stage G V.powerset := by
    apply orbitSpan_contains (basedShapes G V.powerset) x.2.2.2
    exact ⟨x.1.support,Finset.mem_insert_of_mem (Finset.mem_powerset.mpr (hV x hx)),Finset.Subset.refl _⟩
  exact ⟨⟨x.1,x.2.1,x.2.2.1,hm⟩,rfl⟩

lemma compact_orbit_controlled {K : Set (Space G)} (hK : IsCompact K) :
    ∃ S : Shapes G, ∀ g : G, (g • ·) '' K ⊆ Set.range (stageFull G S) := by
  obtain ⟨S,hS⟩ := compact_controlled G hK
  refine ⟨S,?_⟩
  intro g y hy
  obtain ⟨x,hx,rfl⟩ := hy
  obtain ⟨z,rfl⟩ := hS hx
  exact ⟨g • z,stageFull_smul G S g z⟩

variable {X : Type v} [TopologicalSpace X] [MulAction G X]

def factorStage (f : C(X,Space G)) (S : Shapes G)
    (hf : Set.range f ⊆ Set.range (stageFull G S)) : C(X,Stage G S) where
  toFun x := (hf (Set.mem_range_self x)).choose
  continuous_toFun := (stageFull_embedding G S).isEmbedding.continuous_iff.mpr (by
    convert f.continuous using 1
    funext x
    exact (hf (Set.mem_range_self x)).choose_spec)
omit [MulAction G X] in
lemma factorStage_spec (f : C(X,Space G)) (S : Shapes G)
    (hf : Set.range f ⊆ Set.range (stageFull G S)) (x : X) :
    stageFull G S (factorStage G f S hf x) = f x := (hf (Set.mem_range_self x)).choose_spec
end UniversalFInfinity.Milnor

open Set Metric Topology

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CellularAttachment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Cellular
universe u
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
variable {C : Set X} [CWComplex C] {f : X → Y} (hf : IsClosedEmbedding f)

variable [T2Space X]

@[instance_reducible]
def transportCW : CWComplex (f '' C) where
  cell := RelCWComplex.cell C
  map := transportedMap hf
  source_eq := transportedMap_source hf
  continuousOn := transportedMap_continuousOn hf
  continuousOn_symm := transportedMap_continuousOn_symm hf
  pairwiseDisjoint' := by
    intro p _ q _ hpq
    change Disjoint (transportedMap hf p.1 p.2 '' ball 0 1)
      (transportedMap hf q.1 q.2 '' ball 0 1)
    rw [transportedMap_image,transportedMap_image]
    exact (CWComplex.disjoint_openCell_of_ne hpq).image hf.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
  mapsTo' := by
    intro n i
    obtain ⟨I,hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell n i
    refine ⟨I,?_⟩
    intro x hx
    have h := hI (show RelCWComplex.map n i x ∈ CWComplex.cellFrontier n i from ⟨x,hx,rfl⟩)
    simp only [Set.mem_iUnion] at h
    obtain ⟨m,hm,j,hj,hx⟩ := h
    refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hm,Set.mem_iUnion.mpr
      ⟨j,Set.mem_iUnion.mpr ⟨hj,?_⟩⟩⟩⟩
    rw [transportedMap_image]
    exact ⟨_,hx,rfl⟩
  closed' := by
    intro A hA hclosed
    have hpre : IsClosed (f ⁻¹' A) := by
      apply (CWComplex.closed C (f ⁻¹' A) ?_).mpr
      · intro n i
        have h := (hclosed n i).preimage hf.continuous
        rw [transportedMap_image,Set.preimage_inter,
          Set.preimage_image_eq _ hf.injective] at h
        exact h
      · intro x hx
        obtain ⟨y,hy,hyx⟩ := hA hx
        exact hf.injective hyx ▸ hy
    have h := hf.isClosedMap _ hpre
    rwa [Set.image_preimage_eq_of_subset (hA.trans (Set.image_subset_range f C))] at h
  union' := by
    simp only [transportedMap_image,← Set.image_iUnion]
    change f '' (⋃ n, ⋃ i, CWComplex.closedCell n i) = f '' C
    rw [CWComplex.union]

end UniversalFInfinity.Cellular

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

namespace UniversalFInfinity.Cayley
open Set Metric Topology Attachment
universe u

lemma sphere_one_cases (x : Sphere 1) : x.1 0 = -1 ∨ x.1 0 = 1 := by
  have hn : ‖x.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using x.2
  have hc : x.1 = fun _ => x.1 0 := funext (fun i => congrArg x.1 (Subsingleton.elim i 0))
  rw [hc,pi_norm_const,Real.norm_eq_abs] at hn
  exact ((abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hn).symm

instance instFiniteElemForallFinOfNatNatRealSphere : Finite (Sphere 1) := by
  have he : {r : ℝ | r = -1 ∨ r = 1} = {-1,1} := by ext r; simp
  have hS : Set.Finite {r : ℝ | r = -1 ∨ r = 1} := he.symm ▸ ((Set.finite_singleton (1 : ℝ)).insert (-1))
  let : Finite {r : ℝ // r = -1 ∨ r = 1} := hS.to_subtype
  apply Finite.of_injective (fun x : Sphere 1 => (⟨x.1 0,sphere_one_cases x⟩ :
    {r : ℝ // r = -1 ∨ r = 1}))
  intro x y h
  apply Subtype.ext
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa only [hi] using congrArg Subtype.val h

instance instDiscreteTopologyElemForallFinOfNatNatRealSphere : DiscreteTopology (Sphere 1) := inferInstance

def minus : Sphere 1 := ⟨fun _ => -1,by norm_num [mem_sphere,dist_pi_def]⟩
def plus : Sphere 1 := ⟨fun _ => 1,by norm_num [mem_sphere,dist_pi_def]⟩

variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)

def attaching (i : S) : C(Sphere 1,G) :=
  ⟨fun x => if x.1 0 = -1 then 1 else s i,continuous_of_discreteTopology⟩

abbrev Graph := Space (equivariantFamily (G := G) (attaching s))

instance instNonemptyGraph : Nonempty (Graph s) := ⟨base _ 1⟩

def vertex (g : G) : Graph s := base _ g

instance instT2SpaceGraph : T2Space (Graph s) :=
  t2Space _ ((realSeparated_of_tychonoff (Y := G)))

lemma cell_minus (g : G) (i : S) :
    cell (equivariantFamily (G := G) (attaching s)) (g,i) (boundary 1 minus) = vertex s g := by
  refine (cell_boundary (equivariantFamily (G := G) (attaching s)) (g,i) minus).trans ?_
  change base _ (g * attaching s i minus) = vertex s g
  simp only [attaching,ContinuousMap.coe_mk,minus,ite_true,mul_one]
  rfl

lemma cell_plus (g : G) (i : S) :
    cell (equivariantFamily (G := G) (attaching s)) (g,i) (boundary 1 plus) = vertex s (g*s i) := by
  refine (cell_boundary (equivariantFamily (G := G) (attaching s)) (g,i) plus).trans ?_
  change base _ (g * attaching s i plus) = vertex s (g * s i)
  norm_num only [attaching,ContinuousMap.coe_mk,plus,ite_false]
  rfl

lemma cell_joined (g : G) (i : S) : Joined (vertex s g) (vertex s (g*s i)) := by
  have h : Joined (boundary 1 minus) (boundary 1 plus) := PathConnectedSpace.joined _ _
  have hh := h.map (cell (equivariantFamily (G := G) (attaching s)) (g,i)).continuous
  simpa only [cell_minus,cell_plus] using hh

lemma vertex_smul (g h : G) : g • vertex s h = vertex s (g*h) := rfl

lemma vertices_joined (hs : Subgroup.closure (Set.range s) = ⊤) (g : G) :
    Joined (vertex s 1) (vertex s g) := by
  let K : Subgroup G :=
    { carrier := {g | Joined (vertex s 1) (vertex s g)}
      one_mem' := Joined.refl _
      mul_mem' := by
        intro g h hg hh
        have hh' := hh.map (continuous_const_smul g : Continuous (fun x : Graph s => g • x))
        rw [vertex_smul,vertex_smul,mul_one] at hh'
        exact hg.trans hh'
      inv_mem' := by
        intro g hg
        have hh := hg.symm.map (continuous_const_smul g⁻¹ : Continuous (fun x : Graph s => g⁻¹ • x))
        change Joined (vertex s 1) (vertex s g⁻¹)
        simpa only [vertex_smul,mul_one,inv_mul_cancel] using hh }
  have hK : Subgroup.closure (Set.range s) ≤ K := (Subgroup.closure_le K).2 (by
    rintro _ ⟨i,rfl⟩
    change Joined (vertex s 1) (vertex s (s i))
    simpa only [one_mul] using cell_joined s 1 i)
  rw [hs] at hK
  exact hK (Subgroup.mem_top g)

lemma graph_pathConnected (hs : Subgroup.closure (Set.range s) = ⊤) : PathConnectedSpace (Graph s) := by
  have hj : ∀ x : Graph s, Joined (vertex s 1) x := by
    intro x
    cases x with
    | inl g => exact vertices_joined s hs g
    | inr p =>
      have h : Joined (boundary 1 minus) (interior 1 p.2) := PathConnectedSpace.joined _ _
      have hh := h.map (cell (equivariantFamily (G := G) (attaching s)) p.1).continuous
      rw [cell_interior] at hh
      have hp : cell (equivariantFamily (G := G) (attaching s)) p.1 (boundary 1 minus) = vertex s p.1.1 :=
        cell_minus s p.1.1 p.1.2
      rw [hp] at hh
      exact (vertices_joined s hs p.1.1).trans hh
  exact ⟨inferInstance,fun x y => (hj x).symm.trans (hj y)⟩

end UniversalFInfinity.Cayley

namespace UniversalFInfinity.PathSquares
open Set
open scoped unitInterval
variable {X : Type*} [TopologicalSpace X] {x a b : X}

theorem edgeSquare (p : Path x a) (q : Path x b) (e : Path a b)
    (h : (p.trans e).Homotopic q) :
    ∃ H : e.toContinuousMap.Homotopy (.const _ x),
      (∀ t, H (t,0) = pauseReverse p t) ∧ (∀ t, H (t,1) = pauseReverse q t) := by
  obtain ⟨A⟩ := turn p q e h
  refine ⟨A.toHomotopy.trans (spanContract p q),?_,?_⟩
  · intro t
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · change (t:ℝ) ≤ 1/2 at ht
      change A (_,0) = ((Path.refl a).trans p.symm) t
      rw [Path.trans_apply,dite_eq_left ht]
      exact A.source _
    · change ¬(t:ℝ) ≤ 1/2 at ht
      change spanContract p q (_,0) = ((Path.refl a).trans p.symm) t
      rw [Path.trans_apply,dite_eq_right ht,spanContract_source]
  · intro t
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · change (t:ℝ) ≤ 1/2 at ht
      change A (_,1) = ((Path.refl b).trans q.symm) t
      rw [Path.trans_apply,dite_eq_left ht]
      exact A.target _
    · change ¬(t:ℝ) ≤ 1/2 at ht
      change spanContract p q (_,1) = ((Path.refl b).trans q.symm) t
      rw [Path.trans_apply,dite_eq_right ht,spanContract_target]
end UniversalFInfinity.PathSquares
namespace UniversalFInfinity.Cayley
open Set Metric Topology Attachment
open scoped unitInterval
universe u v

def edgeParam (t : I) : Disk 1 := ⟨fun _ => 2*(t:ℝ)-1,by
  rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs,abs_le]
  constructor <;> linarith [t.2.1,t.2.2]⟩
lemma continuous_edgeParam : Continuous edgeParam := by unfold edgeParam; fun_prop

def edgeTime (d : Disk 1) : I := ⟨(d.1 0+1)/2,by
  have hh : |d.1 0| ≤ 1 := by
    have := d.2
    rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg zero_le_one] at this
    exact this 0
  rw [abs_le] at hh
  constructor <;> linarith⟩
lemma continuous_edgeTime : Continuous edgeTime := by
  apply Continuous.subtype_mk
  exact (((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2
lemma edgeParam_time (d : Disk 1) : edgeParam (edgeTime d) = d := by
  apply Subtype.ext
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  dsimp [edgeParam,edgeTime]
  ring
lemma edgeTime_param (t : I) : edgeTime (edgeParam t) = t := by
  apply Subtype.ext
  dsimp [edgeTime,edgeParam]
  ring
lemma edgeParam_zero : edgeParam 0 = boundary 1 minus := by
  apply Subtype.ext
  funext i
  norm_num [edgeParam,minus,boundary]
lemma edgeParam_one : edgeParam 1 = boundary 1 plus := by
  apply Subtype.ext
  funext i
  norm_num [edgeParam,plus,boundary]
lemma edgeTime_minus : edgeTime (boundary 1 minus) = 0 := by
  rw [←edgeParam_zero,edgeTime_param]
lemma edgeTime_plus : edgeTime (boundary 1 plus) = 1 := by
  rw [←edgeParam_one,edgeTime_param]
lemma sphere_one_eq (t : Sphere 1) : t = minus ∨ t = plus := by
  obtain h|h := sphere_one_cases t
  · left; apply Subtype.ext; funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; exact h
  · right; apply Subtype.ext; funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; exact h

variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)

def edge (g : G) (i : S) : Path (vertex s g) (vertex s (g*s i)) where
  toFun t := cell (equivariantFamily (G := G) (attaching s)) (g,i) (edgeParam t)
  continuous_toFun := (cell _ _).continuous.comp continuous_edgeParam
  source' := by rw [edgeParam_zero,cell_minus]
  target' := by rw [edgeParam_one,cell_plus]

variable {Y : Type v} [TopologicalSpace Y] (f : C(Graph s,Y)) (y : Y)
variable (p : ∀ g, Path y (f (vertex s g)))
variable (hp : ∀ g i, ((p g).trans ((edge s g i).map f.continuous)).Homotopic (p (g*s i)))

def edgeSquare (g : G) (i : S) : ((edge s g i).map f.continuous).toContinuousMap.Homotopy (.const _ y) :=
  (PathSquares.edgeSquare (p g) (p (g*s i)) ((edge s g i).map f.continuous) (hp g i)).choose
lemma edgeSquare_source (g : G) (i : S) (t : I) :
    edgeSquare s f y p hp g i (t,0) = PathSquares.pauseReverse (p g) t :=
  (PathSquares.edgeSquare (p g) (p (g*s i)) ((edge s g i).map f.continuous) (hp g i)).choose_spec.1 t
lemma edgeSquare_target (g : G) (i : S) (t : I) :
    edgeSquare s f y p hp g i (t,1) = PathSquares.pauseReverse (p (g*s i)) t :=
  (PathSquares.edgeSquare (p g) (p (g*s i)) ((edge s g i).map f.continuous) (hp g i)).choose_spec.2 t

def edgePaths (i : FreeIndex G S) : C(Disk 1,C(I,Y)) :=
  ContinuousMap.curry ⟨fun z => edgeSquare s f y p hp i.1 i.2 (z.2,edgeTime z.1),
    (edgeSquare s f y p hp i.1 i.2).continuous.comp
      (continuous_snd.prodMk (continuous_edgeTime.comp continuous_fst))⟩
def vertexPaths : C(G,C(I,Y)) := ⟨fun g => PathSquares.pauseReverse (p g),continuous_of_discreteTopology⟩
lemma edgePaths_boundary (i : FreeIndex G S) (t : Sphere 1) :
    edgePaths s f y p hp i (boundary 1 t) =
      vertexPaths s f y p (equivariantFamily (G := G) (attaching s) i t) := by
  obtain rfl|rfl := sphere_one_eq t
  · apply ContinuousMap.ext; intro z
    change edgeSquare s f y p hp i.1 i.2 (z,edgeTime (boundary 1 minus)) = _
    rw [edgeTime_minus,edgeSquare_source]
    simp only [vertexPaths,equivariantFamily,attaching,ContinuousMap.coe_mk,minus,ite_true,smul_eq_mul,mul_one]
  · apply ContinuousMap.ext; intro z
    change edgeSquare s f y p hp i.1 i.2 (z,edgeTime (boundary 1 plus)) = _
    rw [edgeTime_plus,edgeSquare_target]
    norm_num [vertexPaths,equivariantFamily,attaching,plus]

def graphPaths : C(Graph s,C(I,Y)) :=
  lift _ (vertexPaths s f y p) (edgePaths s f y p hp) (edgePaths_boundary s f y p hp)

lemma graphPaths_zero (z : Graph s) : graphPaths s f y p hp z 0 = f z := by
  cases z with
  | inl g =>
    change PathSquares.pauseReverse (p g) 0 = _
    exact Path.source _
  | inr z =>
    change edgeSquare s f y p hp z.1.1 z.1.2 (0,edgeTime (interior 1 z.2)) = _
    rw [ContinuousMap.Homotopy.apply_zero]
    change f (cell _ z.1 (edgeParam (edgeTime (interior 1 z.2)))) = f _
    rw [edgeParam_time,cell_interior]
lemma graphPaths_one (z : Graph s) : graphPaths s f y p hp z 1 = y := by
  cases z with
  | inl g =>
    change PathSquares.pauseReverse (p g) 1 = y
    exact Path.target _
  | inr z =>
    change edgeSquare s f y p hp z.1.1 z.1.2 (1,edgeTime (interior 1 z.2)) = y
    exact ContinuousMap.Homotopy.apply_one _ _

def graphNullhomotopy : f.Homotopy (.const _ y) where
  toFun z := graphPaths s f y p hp z.2 z.1
  continuous_toFun := (graphPaths s f y p hp).uncurry.continuous.comp continuous_swap
  map_zero_left := graphPaths_zero s f y p hp
  map_one_left := graphPaths_one s f y p hp
end UniversalFInfinity.Cayley
open Set Metric Topology

namespace UniversalFInfinity.Cellular
open Set Metric Topology
variable {Y : Type*} [TopologicalSpace Y]

theorem cylinderFill {n : ℕ} (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))
    (h : ∀ x, pathEndpoint (a x) = b (boundary n x))
    (F : C(Disk (n+1),Y)) (hF : ∀ x, F (boundary (n+1) x) = cylinderBoundaryMap a b h x) :
    ∃ e : C(Disk n,C(unitInterval,Y)),
      (∀ x, e (boundary n x) = a x) ∧ (∀ x, pathEndpoint (e x) = b x) := by
  let e : C(Disk n,C(unitInterval,Y)) :=
    (F.comp ⟨fun q : Disk n × unitInterval => diskCons q.1 q.2,continuous_diskCons⟩).curry
  refine ⟨e,?_,?_⟩
  · intro x
    apply ContinuousMap.ext
    intro t
    let s : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
    have hs : s ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) t)).1 ∈ sphere 0 1
      rw [diskTail_cons]
      exact x.2
    change F (diskCons (boundary n x) t) = a x t
    rw [show diskCons (boundary n x) t = boundary (n+1) s from rfl,hF,
      cylinderBoundaryMap_face a b h none ⟨s,hs⟩]
    change a (faceSphere ⟨s,hs⟩) (diskTime (diskCons (boundary n x) t)) = a x t
    rw [diskTime_cons]
    congr 1
  · intro x
    apply Prod.ext
    · let s : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some false) := by
        change (diskCons x 0).1 0 = -1
        norm_num [diskCons]
      change F (diskCons x 0) = (b x).1
      rw [show diskCons x 0 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some false) ⟨s,hs⟩]
      change (b (diskTail (diskCons x 0))).1 = (b x).1
      rw [diskTail_cons]
    · let s : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some true) := by
        change (diskCons x 1).1 0 = 1
        norm_num [diskCons]
      change F (diskCons x 1) = (b x).2
      rw [show diskCons x 1 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some true) ⟨s,hs⟩]
      change (b (diskTail (diskCons x 1))).2 = (b x).2
      rw [diskTail_cons]

end UniversalFInfinity.Cellular
namespace UniversalFInfinity.LoopSphere
open Set Metric Topology Cellular
open scoped unitInterval
universe u v
variable {X : Type u} [TopologicalSpace X] {x : X}

def ends (p : Path x x) : C(Disk 1,X × X) :=
  ⟨fun d => (p (Cayley.edgeTime d),x),
    (p.continuous.comp Cayley.continuous_edgeTime).prodMk continuous_const⟩
lemma ends_sides (p : Path x x) (z : Sphere 1) :
    pathEndpoint (sides (x := x) z) = ends p (boundary 1 z) := by
  obtain rfl|rfl := Cayley.sphere_one_eq z
  · change (x,x) = (p (Cayley.edgeTime (Attachment.boundary 1 Cayley.minus)),x)
    rw [Cayley.edgeTime_minus,p.source]
  · change (x,x) = (p (Cayley.edgeTime (Attachment.boundary 1 Cayley.plus)),x)
    rw [Cayley.edgeTime_plus,p.target]

def map (p : Path x x) : C(Sphere 2,X) := cylinderBoundaryMap sides (ends p) (ends_sides p)

theorem homotopic_of_fill (p : Path x x) (F : C(Disk 2,X))
    (hF : ∀ z, F (boundary 2 z) = map p z) : p.Homotopic (Path.refl x) := by
  obtain ⟨e,he,hep⟩ := cylinderFill sides (ends p) (ends_sides p) F hF
  refine ⟨{
    toFun := fun z => e (Cayley.edgeParam z.2) z.1
    continuous_toFun := e.uncurry.continuous.comp
      ((Cayley.continuous_edgeParam.comp continuous_snd).prodMk continuous_fst)
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    have h := congrArg Prod.fst (hep (Cayley.edgeParam t))
    change e (Cayley.edgeParam t) 0 = p t
    change e (Cayley.edgeParam t) 0 = p (Cayley.edgeTime (Cayley.edgeParam t)) at h
    simpa only [Cayley.edgeTime_param] using h
  · intro t
    exact congrArg Prod.snd (hep (Cayley.edgeParam t))
  · intro t q hq
    obtain rfl|hq := hq
    · change e (Cayley.edgeParam 0) t = p 0
      rw [Cayley.edgeParam_zero,p.source]
      exact ContinuousMap.congr_fun (he Cayley.minus) t
    · obtain rfl := Set.mem_singleton_iff.mp hq
      change e (Cayley.edgeParam 1) t = p 1
      rw [Cayley.edgeParam_one,p.target]
      exact ContinuousMap.congr_fun (he Cayley.plus) t

variable {Y : Type v} [TopologicalSpace Y]
lemma natural (p : Path x x) (f : C(X,Y)) : map (p.map f.continuous) = f.comp (map p) := by
  apply ContinuousMap.ext; intro z
  have hz : z ∈ ⋃ i, cylinderFace 1 i := by rw [cylinderFace_cover]; trivial
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
  change cylinderBoundaryMap sides (ends (p.map f.continuous)) (ends_sides _) z =
    f (cylinderBoundaryMap sides (ends p) (ends_sides p) z)
  rw [cylinderBoundaryMap_face _ _ _ i ⟨z,hi⟩,cylinderBoundaryMap_face _ _ _ i ⟨z,hi⟩]
  cases i with
  | none => rfl
  | some b => cases b <;> rfl

lemma homotopic_map_of_fill (p : Path x x) (f : C(X,Y)) (F : C(Disk 2,Y))
    (hF : ∀ z, F (boundary 2 z) = f (map p z)) :
    (p.map f.continuous).Homotopic (Path.refl (f x)) := by
  apply homotopic_of_fill _ F
  intro z
  rw [natural]
  exact hF z
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

namespace Equal
lemma ofEq {p q : Path.Homotopic.Quotient x y} (h : p = q) : Equal p q := ⟨rfl,rfl,heq_of_eq h⟩
lemma map {Y : Type*} [TopologicalSpace Y] {x' y' : X}
    {p : Path.Homotopic.Quotient x y} {q : Path.Homotopic.Quotient x' y'}
    (h : Equal p q) (f : C(X,Y)) : Equal (p.map f) (q.map f) := by
  rcases h with ⟨hx,hy,hp⟩
  subst x'; subst y'
  cases eq_of_heq hp
  exact .refl _
end Equal
lemma cast_equal {x' y' : X} (p : Path.Homotopic.Quotient x y) (hx : x' = x) (hy : y' = y) :
    Equal (p.cast hx hy) p := ⟨hx,hy,Path.Homotopic.Quotient.cast_heq hx hy⟩
lemma refl_equal {x y : X} (h : x = y) :
    Equal (Path.Homotopic.Quotient.refl x) (Path.Homotopic.Quotient.refl y) := by
  subst y
  exact .refl _

end Q

variable {G : Type v} [Group G] [MulAction G X] [ContinuousConstSMul G X]

lemma map_one_equal {x y : X} (p : Path.Homotopic.Quotient x y) :
    Q.Equal (p.map (smulMap (1 : G))) p := by
  refine ⟨one_smul G x,one_smul G y,?_⟩
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact Path.Homotopic.hpath_hext (fun t => one_smul G (p t))

lemma map_mul_equal {x y : X} (p : Path.Homotopic.Quotient x y) (g h : G) :
    Q.Equal ((p.map (smulMap h)).map (smulMap g)) (p.map (smulMap (g*h))) := by
  refine ⟨(mul_smul g h x).symm,(mul_smul g h y).symm,?_⟩
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact Path.Homotopic.hpath_hext (fun t => (mul_smul g h (p t)).symm)

variable (G) (x₀ : X)
variable {G x₀}

instance instOneExtension : One (Extension G x₀) :=
  ⟨⟨1,(Path.Homotopic.Quotient.refl x₀).cast rfl (one_smul G x₀)⟩⟩
instance instMulExtension : Mul (Extension G x₀) :=
  ⟨fun a b => ⟨a.1*b.1,(a.2.trans (b.2.map (smulMap a.1))).cast rfl (mul_smul ..)⟩⟩
instance instInvExtension : Inv (Extension G x₀) :=
  ⟨fun a => ⟨a.1⁻¹,((a.2.map (smulMap a.1⁻¹)).symm).cast (inv_smul_smul a.1 x₀).symm rfl⟩⟩

lemma mul_path_equal (a b : Extension G x₀) :
    Q.Equal (a*b).2 (a.2.trans (b.2.map (smulMap a.1))) :=
  Q.cast_equal _ _ _

omit [ContinuousConstSMul G X] in
lemma one_path_equal : Q.Equal (1 : Extension G x₀).2 (Path.Homotopic.Quotient.refl x₀) := by
  change Q.Equal ((Path.Homotopic.Quotient.refl x₀).cast rfl (one_smul G x₀)) _
  exact Q.cast_equal _ _ _

lemma mul_assoc (a b c : Extension G x₀) : a*b*c = a*(b*c) := by
  apply ext (_root_.mul_assoc _ _ _)
  apply Q.Equal.path
  apply Q.Equal.trans (mul_path_equal (a*b) c)
  apply Q.Equal.trans (Q.Equal.comp (mul_path_equal a b) (map_mul_equal c.2 a.1 b.1).symm)
  apply Q.Equal.trans (Q.Equal.ofEq (Path.Homotopic.Quotient.trans_assoc _ _ _))
  apply Q.Equal.trans ?_ (mul_path_equal a (b*c)).symm
  apply Q.Equal.comp (Q.Equal.refl _)
  apply Q.Equal.trans ?_ ((mul_path_equal b c).map (smulMap a.1)).symm
  exact Q.Equal.ofEq (Q.map_trans _ _ _).symm

lemma one_mul (a : Extension G x₀) : 1*a = a := by
  apply ext (_root_.one_mul _)
  apply Q.Equal.path
  exact (mul_path_equal 1 a).trans
    ((Q.Equal.comp one_path_equal (map_one_equal a.2)).trans
      (Q.Equal.ofEq (Path.Homotopic.Quotient.refl_trans a.2)))

lemma mul_one (a : Extension G x₀) : a*1 = a := by
  apply ext (_root_.mul_one _)
  apply Q.Equal.path
  apply Q.Equal.trans (mul_path_equal a 1)
  apply Q.Equal.trans (Q.Equal.comp (Q.Equal.refl _) (one_path_equal.map (smulMap a.1)))
  rw [Q.map_refl]
  exact Q.Equal.ofEq (Path.Homotopic.Quotient.trans_refl a.2)

lemma inv_mul_cancel (a : Extension G x₀) : a⁻¹*a = 1 := by
  apply ext (_root_.inv_mul_cancel _)
  apply Q.Equal.path
  apply Q.Equal.trans (mul_path_equal a⁻¹ a)
  have hi : Q.Equal (a⁻¹).2 (a.2.map (smulMap a.1⁻¹)).symm := Q.cast_equal _ _ _
  exact (Q.Equal.comp hi (Q.Equal.refl _)).trans
    ((Q.Equal.ofEq (Path.Homotopic.Quotient.symm_trans _)).trans
      ((Q.refl_equal (inv_smul_smul a.1 x₀)).trans one_path_equal.symm))

instance instGroupExtension : Group (Extension G x₀) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := inv_mul_cancel

def projection : Extension G x₀ →* G where
  toFun := Sigma.fst
  map_one' := rfl
  map_mul' _ _ := rfl

end
open Path.Homotopic
universe u v w
variable {G : Type u} [Group G]
variable {X : Type v} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable {Y : Type w} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
variable (f : C(X,Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

include hf in
lemma natural_smul_equal {x y : X} (p : Path.Homotopic.Quotient x y) (g : G) :
    Q.Equal ((p.map (smulMap g)).map f) ((p.map f).map (smulMap g)) := by
  refine ⟨hf g x,hf g y,?_⟩
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact Path.Homotopic.hpath_hext (fun t => hf g (p t))

variable (x₀ : X)
def mapFun (a : Extension G x₀) : Extension G (f x₀) :=
  ⟨a.1,(a.2.map f).cast rfl (hf a.1 x₀).symm⟩
omit [ContinuousConstSMul G X] [ContinuousConstSMul G Y] in
lemma mapFun_equal (a : Extension G x₀) :
    Q.Equal (mapFun f hf x₀ a).2 (a.2.map f) := Q.cast_equal _ _ _
omit [ContinuousConstSMul G X] [ContinuousConstSMul G Y] in
lemma mapFun_one : mapFun f hf x₀ 1 = 1 := by
  apply ext rfl
  apply Q.Equal.path
  apply (mapFun_equal f hf x₀ 1).trans
  apply (one_path_equal.map f).trans
  rw [Q.map_refl]
  exact one_path_equal.symm
lemma mapFun_mul (a b : Extension G x₀) : mapFun f hf x₀ (a*b) = mapFun f hf x₀ a * mapFun f hf x₀ b := by
  apply ext (a := mapFun f hf x₀ (a*b)) (b := mapFun f hf x₀ a * mapFun f hf x₀ b) (by rfl)
  apply Q.Equal.path
  apply (mapFun_equal f hf x₀ (a*b)).trans
  apply ((mul_path_equal a b).map f).trans
  apply (Q.Equal.ofEq (Q.map_trans _ _ _)).trans
  apply Q.Equal.trans ?_ (mul_path_equal (mapFun f hf x₀ a) (mapFun f hf x₀ b)).symm
  exact Q.Equal.comp (mapFun_equal f hf x₀ a).symm
    ((natural_smul_equal f hf b.2 a.1).trans
      ((mapFun_equal f hf x₀ b).map (smulMap a.1)).symm)

def map : Extension G x₀ →* Extension G (f x₀) where
  toFun := mapFun f hf x₀
  map_one' := mapFun_one f hf x₀
  map_mul' := mapFun_mul f hf x₀

end UniversalFInfinity.PathExtension
namespace UniversalFInfinity.Cayley

section
open Set Metric Topology Attachment PathExtension
open scoped unitInterval
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)

lemma smul_vertex (g h : G) : g • vertex s h = vertex s (g*h) := rfl

def pathGenerator (i : S) : PathExtension.Extension G (vertex s 1) :=
  ⟨s i,Path.Homotopic.Quotient.mk ((edge s 1 i).cast rfl (by
    rw [smul_vertex]; simp only [_root_.mul_one,_root_.one_mul]))⟩
def wordLift : FreeGroup S →* PathExtension.Extension G (vertex s 1) :=
  FreeGroup.lift (pathGenerator s)
lemma projection_wordLift : PathExtension.projection.comp (wordLift s) = FreeGroup.lift s := by
  ext i
  simp only [MonoidHom.comp_apply,wordLift,FreeGroup.lift_apply_of]
  rfl
lemma wordLift_fst (w : FreeGroup S) : (wordLift s w).1 = FreeGroup.lift s w :=
  DFunLike.congr_fun (projection_wordLift s) w

variable (rels : Set (FreeGroup S)) (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
def relatorClass (r : rels) : Path.Homotopic.Quotient (vertex s 1) (vertex s 1) :=
  (wordLift s r.1).2.cast rfl (by rw [wordLift_fst,hrel r.1 r.2,one_smul])
def relatorLoop (r : rels) : Path (vertex s 1) (vertex s 1) :=
  (Path.Homotopic.Quotient.mk_surjective (relatorClass s rels hrel r)).choose
lemma relatorLoop_eq (r : rels) : Path.Homotopic.Quotient.mk (relatorLoop s rels hrel r) =
    relatorClass s rels hrel r :=
  (Path.Homotopic.Quotient.mk_surjective (relatorClass s rels hrel r)).choose_spec
lemma relatorLoop_equal (r : rels) :
    PathExtension.Q.Equal (Path.Homotopic.Quotient.mk (relatorLoop s rels hrel r))
      (wordLift s r.1).2 :=
  (PathExtension.Q.Equal.ofEq (relatorLoop_eq s rels hrel r)).trans (PathExtension.Q.cast_equal _ _ _)

def relatorAttaching (r : rels) : C(Sphere 2,Graph s) := LoopSphere.map (relatorLoop s rels hrel r)
abbrev PresentationCover := Space (equivariantFamily (G := G) (relatorAttaching s rels hrel))
def presentationBase : C(Graph s,PresentationCover s rels hrel) := ⟨base _,continuous_base _⟩
lemma presentationBase_smul (g : G) (x : Graph s) :
    presentationBase s rels hrel (g • x) = g • presentationBase s rels hrel x := rfl

def coverWordLift : FreeGroup S →* PathExtension.Extension G (presentationBase s rels hrel (vertex s 1)) :=
  (PathExtension.map (presentationBase s rels hrel) (presentationBase_smul s rels hrel) (vertex s 1)).comp
    (wordLift s)

lemma mapped_relator_homotopic (r : rels) :
    ((relatorLoop s rels hrel r).map (presentationBase s rels hrel).continuous).Homotopic
      (Path.refl (presentationBase s rels hrel (vertex s 1))) := by
  apply LoopSphere.homotopic_map_of_fill _ _ (cell _ ((1:G),r))
  intro z
  change cell (equivariantFamily (G := G) (relatorAttaching s rels hrel)) ((1:G),r)
    (Attachment.boundary 2 z) = _
  refine (cell_boundary (equivariantFamily (G := G) (relatorAttaching s rels hrel))
    (1,r) z).trans ?_
  change base _ ((1 : G) • relatorAttaching s rels hrel r z) = _
  rw [one_smul]
  rfl

lemma coverWordLift_relator (r : rels) : coverWordLift s rels hrel r.1 = 1 := by
  apply PathExtension.ext (a := coverWordLift s rels hrel r.1) (b := 1)
    ((wordLift_fst s r.1).trans (hrel r.1 r.2))
  apply PathExtension.Q.Equal.path
  apply (PathExtension.mapFun_equal (presentationBase s rels hrel)
    (presentationBase_smul s rels hrel) (vertex s 1) (wordLift s r.1)).trans
  apply ((relatorLoop_equal s rels hrel r).map (presentationBase s rels hrel)).symm.trans
  apply (PathExtension.Q.Equal.ofEq (Quotient.sound (mapped_relator_homotopic s rels hrel r))).trans
  exact PathExtension.one_path_equal.symm

lemma coverWordLift_ker (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) :
    (FreeGroup.lift s).ker ≤ (coverWordLift s rels hrel).ker := by
  rw [hker]
  apply Subgroup.normalClosure_le_normal
  intro r hr
  exact coverWordLift_relator s rels hrel ⟨r,hr⟩

def presentationSection (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) :
    G →* PathExtension.Extension G (presentationBase s rels hrel (vertex s 1)) :=
  (FreeGroup.lift s).liftOfSurjective hs ⟨coverWordLift s rels hrel,coverWordLift_ker s rels hrel hker⟩
lemma presentationSection_lift (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) (w : FreeGroup S) :
    presentationSection s rels hrel hs hker (FreeGroup.lift s w) = coverWordLift s rels hrel w :=
  MonoidHom.liftOfRightInverse_comp_apply ..
lemma presentationSection_fst (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) (g : G) :
    (presentationSection s rels hrel hs hker g).1 = g := by
  obtain ⟨w,rfl⟩ := hs g
  rw [presentationSection_lift]
  exact wordLift_fst s w
end
section
open Set Metric Topology Attachment PathExtension
open scoped unitInterval
universe u v
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)
variable {Y : Type v} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
variable (f : C(Graph s,Y)) (hf : ∀ (g : G) x, f (g • x) = g • f x)
include hf in
omit [ContinuousConstSMul G Y] in
lemma vertex_action (g : G) : f (vertex s g) = g • f (vertex s 1) := by
  rw [← hf,smul_vertex,_root_.mul_one]

lemma pathGenerator_equal (i : S) : Q.Equal (pathGenerator s i).2 (Path.Homotopic.Quotient.mk (edge s 1 i)) := by
  refine ⟨rfl,?_,?_⟩
  · rw [smul_vertex]; simp only [_root_.one_mul,_root_.mul_one]; rfl
  · exact Path.Homotopic.hpath_hext (fun _ => rfl)

include hf in
lemma edge_smul_equal (g : G) (i : S) :
    Q.Equal (((Path.Homotopic.Quotient.mk (edge s 1 i)).map f).map (smulMap g))
      (Path.Homotopic.Quotient.mk ((edge s g i).map f.continuous)) := by
  refine ⟨(vertex_action s f hf g).symm,?_,?_⟩
  · change g • f (vertex s (1*s i)) = f (vertex s (g*s i))
    rw [←hf,smul_vertex,_root_.one_mul]
  · apply Path.Homotopic.hpath_hext
    intro t
    change g • f (cell _ ((1:G),i) (edgeParam t)) = f (cell _ (g,i) (edgeParam t))
    refine (hf g _).symm.trans (congrArg f ?_)
    refine (smul_cell _ (equivariantFamily_smul (attaching s)) g (1,i) _).trans ?_
    exact congrArg (fun first : G => cell _ (first,i) (edgeParam t)) (_root_.mul_one g)

variable (τ : G →* PathExtension.Extension G (f (vertex s 1)))
variable (hτ : ∀ g, (τ g).1 = g)
def coherentClass (g : G) : Path.Homotopic.Quotient (f (vertex s 1)) (f (vertex s g)) :=
  (τ g).2.cast rfl (by rw [hτ]; exact vertex_action s f hf g)
def coherentPath (g : G) : Path (f (vertex s 1)) (f (vertex s g)) :=
  (Path.Homotopic.Quotient.mk_surjective (coherentClass s f hf τ hτ g)).choose
lemma coherentPath_equal (g : G) : Q.Equal (Path.Homotopic.Quotient.mk (coherentPath s f hf τ hτ g)) (τ g).2 :=
  (Q.Equal.ofEq (Path.Homotopic.Quotient.mk_surjective (coherentClass s f hf τ hτ g)).choose_spec).trans
    (Q.cast_equal _ _ _)

variable (hgen : ∀ i, Q.Equal (τ (s i)).2 (Path.Homotopic.Quotient.mk ((edge s 1 i).map f.continuous)))
include hgen in
lemma coherentPath_edge (g : G) (i : S) :
    ((coherentPath s f hf τ hτ g).trans ((edge s g i).map f.continuous)).Homotopic
      (coherentPath s f hf τ hτ (g*s i)) := by
  apply Path.Homotopic.Quotient.exact
  change (Path.Homotopic.Quotient.mk (coherentPath s f hf τ hτ g)).trans
    (Path.Homotopic.Quotient.mk ((edge s g i).map f.continuous)) = _
  apply eq_of_heq
  apply Q.Equal.path
  have he : Q.Equal ((τ (s i)).2.map (smulMap (τ g).1))
      (Path.Homotopic.Quotient.mk ((edge s g i).map f.continuous)) := by
    apply ((hgen i).map (smulMap (τ g).1)).trans
    rw [hτ]
    exact edge_smul_equal s f hf g i
  apply (Q.Equal.comp (coherentPath_equal s f hf τ hτ g) he.symm).trans
  apply (mul_path_equal (τ g) (τ (s i))).symm.trans
  have hm : Q.Equal (τ g * τ (s i)).2 (τ (g*s i)).2 := by
    rw [←τ.map_mul]
    exact .refl _
  exact hm.trans (coherentPath_equal s f hf τ hτ (g*s i)).symm

def nullhomotopyOfSection : f.Homotopy (.const _ (f (vertex s 1))) :=
  graphNullhomotopy s f (f (vertex s 1)) (coherentPath s f hf τ hτ)
    (coherentPath_edge s f hf τ hτ hgen)
end
open PathExtension Attachment
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G) (rels : Set (FreeGroup S))
variable (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
variable (hs : Function.Surjective (FreeGroup.lift s))
variable (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels)
lemma presentationSection_generator (i : S) :
    Q.Equal (presentationSection s rels hrel hs hker (s i)).2
      (Path.Homotopic.Quotient.mk ((edge s 1 i).map (presentationBase s rels hrel).continuous)) := by
  have hh : presentationSection s rels hrel hs hker (s i) =
      PathExtension.map (presentationBase s rels hrel) (presentationBase_smul s rels hrel) (vertex s 1)
        (pathGenerator s i) := by
    simpa only [FreeGroup.lift_apply_of,coverWordLift,MonoidHom.comp_apply,wordLift]
      using presentationSection_lift s rels hrel hs hker (FreeGroup.of i)
  rw [hh]
  exact (PathExtension.mapFun_equal (presentationBase s rels hrel) (presentationBase_smul s rels hrel) (vertex s 1) (pathGenerator s i)).trans
    ((pathGenerator_equal s i).map (presentationBase s rels hrel))

def presentationGraphNullhomotopy :
    (presentationBase s rels hrel).Homotopy
      (.const _ (presentationBase s rels hrel (vertex s 1))) :=
  nullhomotopyOfSection s (presentationBase s rels hrel) (presentationBase_smul s rels hrel)
    (presentationSection s rels hrel hs hker) (presentationSection_fst s rels hrel hs hker)
    (presentationSection_generator s rels hrel hs hker)
end UniversalFInfinity.Cayley

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

namespace UniversalFInfinity.Cayley
open Set Metric Topology Attachment
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G) (rels : Set (FreeGroup S))
variable (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
variable (hs : Function.Surjective (FreeGroup.lift s))
variable (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels)

instance presentationCoverT2 : T2Space (PresentationCover s rels hrel) :=
  t2Space _ (realSeparated _ (realSeparated_of_tychonoff (Y := G)))

include hs in
lemma presentationCover_pathConnected : PathConnectedSpace (PresentationCover s rels hrel) := by
  have hgen : Subgroup.closure (Set.range s) = ⊤ := by
    rw [←FreeGroup.range_lift_eq_closure,MonoidHom.range_eq_top]
    exact hs
  let := graph_pathConnected s hgen
  let := SphereTopology.sphere_nonempty 1
  exact Attachment.pathConnectedSpace _

include hs hker in
lemma presentationCover_sphereFill (b : C(Sphere 2,PresentationCover s rels hrel)) : SphereTopology.Extends b := by
  let := SphereTopology.sphere_nonempty 1
  have hdim : dimH (Set.univ : Set (Sphere 2)) < 2 :=
    (GeneralPosition.dimH_cube_boundary_subtype_le 1).trans_lt (by norm_num)
  obtain ⟨g,H,_⟩ := exists_deformation_into_base _ b hdim
  apply SphereTopology.extends_of_homotopy H
  exact SphereTopology.extends_of_nullhomotopic
    (((presentationGraphNullhomotopy s rels hrel hs hker).compContinuousMap g).symm)

end UniversalFInfinity.Cayley

namespace UniversalFInfinity
universe u v
variable {G : Type u} [Group G] {A : Type v} [MulAction G A]

variable (hfree : ∀ (g : G) (a : A), g • a = a → g = 1)

include hfree in
lemma orbitCoordinates_bijective : Function.Bijective (fun p : G × Orbits (G := G) (A := A) => p.1 • p.2.out) := by
  constructor
  · rintro ⟨g,q⟩ ⟨h,r⟩ he
    have hqr : q = r := by
      have hh := congrArg (fun a : A => (Quotient.mk'' a : Orbits (G := G))) he
      simpa only [orbit_mk_smul,Quotient.out_eq'] using hh
    subst r
    change g • q.out = h • q.out at he
    have hh : (h⁻¹*g) • q.out = q.out := by rw [mul_smul,he,inv_smul_smul]
    have hh := hfree (h⁻¹*g) q.out hh
    have hgh : g = h := (inv_mul_eq_one.mp hh).symm
    exact Prod.ext hgh rfl
  · intro a
    obtain ⟨g,hg⟩ := orbit_out_translate (G := G) a
    exact ⟨(g,Quotient.mk'' a),hg.symm⟩

def orbitCoordinates : (G × Orbits (G := G) (A := A)) ≃ A :=
  Equiv.ofBijective _ (orbitCoordinates_bijective hfree)

end UniversalFInfinity

open Set Metric Topology

namespace UniversalFInfinity.Milnor
open Set Metric Topology UniversalFInfinity.Simplicial
universe u
variable (G : Type u) [Group G]

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_7
lemma vertexTranslate_injective (g : G) : Function.Injective (fun v : ℕ × G => (v.1,g*v.2)) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  change (i,g*a) = (j,g*b) at h
  apply Prod.ext
  · simpa only using congrArg (fun v : ℕ × G => v.1) h
  · exact mul_left_cancel (congrArg Prod.snd h)

lemma translate_card (g : G) (s : Finset (ℕ × G)) : (translate g s).card = s.card :=
  Finset.card_image_of_injective _ (vertexTranslate_injective G g)

abbrev StageCell (S : Shapes G) (n : ℕ) := Simplicial.Cell (stage G S) n

def cellTranslate (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) : StageCell G S n :=
  ⟨⟨translate g c.1.1,orbitSpan_invariant _ g c.1.2⟩,by rw [translate_card]; exact c.2⟩

instance cellAction (S : Shapes G) (n : ℕ) : MulAction G (StageCell G S n) where
  smul := cellTranslate G S n
  one_smul c := by apply Subtype.ext; apply Subtype.ext; exact translate_one _
  mul_smul g h c := by apply Subtype.ext; apply Subtype.ext; exact (translate_mul _ _ _).symm

lemma cell_smul_val (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) :
    (g • c).1.1 = translate g c.1.1 := rfl

lemma cellAction_free (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n)
    (h : g • c = c) : g = 1 := by
  have he : translate g c.1.1 = c.1.1 := congrArg (fun c : StageCell G S n => c.1.1) h
  obtain ⟨v,hv⟩ := c.1.2.1.1
  have ht : (v.1,g*v.2) ∈ c.1.1 := he ▸ Finset.mem_image.mpr ⟨v,hv,rfl⟩
  have heq := c.1.2.1.2 ht hv rfl
  have hg : g * v.2 = v.2 := congrArg Prod.snd heq
  exact mul_right_cancel (hg.trans (one_mul _).symm)

abbrev CellOrbits (S : Shapes G) (n : ℕ) := Orbits (G := G) (A := StageCell G S n)

def cellCoordinates (S : Shapes G) (n : ℕ) : (G × CellOrbits G S n) ≃ StageCell G S n :=
  orbitCoordinates (cellAction_free G S n)

instance cellOrbits_finite (S : Shapes G) (n : ℕ) : Finite (CellOrbits G S n) := by
  classical
  obtain ⟨T,hT⟩ := orbitSpan_finite_representatives (basedShapes G S)
  let R : Set (StageCell G S n) := {c | c.1.1 ∈ T}
  have hinj : Function.Injective (fun c : StageCell G S n => c.1.1) := by
    intro c d h; exact Subtype.ext (Subtype.ext h)
  have hR : R.Finite := T.finite_toSet.preimage hinj.injOn
  let := hR.fintype
  apply Finite.of_surjective (fun c : R => (Quotient.mk'' c.1 : CellOrbits G S n))
  intro q
  obtain ⟨s,hs,g,hg⟩ := hT q.out.1.1 q.out.1.2
  let c : StageCell G S n := g⁻¹ • q.out
  have hc : c ∈ R := by
    change translate g⁻¹ q.out.1.1 ∈ T
    rw [hg,translate_mul,inv_mul_cancel,translate_one]
    exact hs
  refine ⟨⟨c,hc⟩,?_⟩
  exact (orbit_mk_smul g⁻¹ q.out).trans (Quotient.out_eq' _)

lemma stage_smul_support (S : Shapes G) (g : G) (x : Stage G S) :
    (g • x).1.support = translate g x.1.support :=
  Finsupp.mapDomain_support_of_injective (vertexTranslate_injective G g) _

lemma stage_openCell (S : Shapes G) (n : ℕ) (c : StageCell G S n) :
    RelCWComplex.openCell (C := (univ : Set (Stage G S))) n c = {x : Stage G S | x.1.support = c.1.1} :=
  Simplicial.characteristicPE_open _ _

lemma stage_closedCell (S : Shapes G) (n : ℕ) (c : StageCell G S n) :
    RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n c = {x : Stage G S | x.1.support ⊆ c.1.1} := by
  change Simplicial.characteristicPE _ c '' closedBall 0 1 = _
  rw [Simplicial.characteristicPE_closed,Simplicial.range_faceMap]

lemma stage_openCell_smul (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) :
    (fun x : Stage G S => g • x) '' RelCWComplex.openCell (C := (univ : Set (Stage G S))) n c = RelCWComplex.openCell (C := (univ : Set (Stage G S))) n (g • c) := by
  rw [stage_openCell,stage_openCell]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (g • y).1.support = (g • c).1.1
    rw [stage_smul_support,cell_smul_val,hy]
  · intro hx
    refine ⟨g⁻¹ • x,?_,smul_inv_smul _ _⟩
    change (g⁻¹ • x).1.support = c.1.1
    change x.1.support = translate g c.1.1 at hx
    rw [stage_smul_support,hx,translate_mul,inv_mul_cancel,translate_one]

lemma stage_closedCell_smul (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) :
    (fun x : Stage G S => g • x) '' RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n c = RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n (g • c) := by
  rw [stage_closedCell,stage_closedCell]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (g • y).1.support ⊆ (g • c).1.1
    rw [stage_smul_support,cell_smul_val]
    exact translate_mono _ hy
  · intro hx
    refine ⟨g⁻¹ • x,?_,smul_inv_smul _ _⟩
    change (g⁻¹ • x).1.support ⊆ c.1.1
    rw [stage_smul_support]
    have h := translate_mono g⁻¹ hx
    simpa only [cell_smul_val,translate_mul,inv_mul_cancel,translate_one] using h

@[instance_reducible]
def stageEquivariantCW (S : Shapes G) : CWComplex (univ : Set (Stage G S)) :=
  Cellular.actionCW (cellCoordinates G S)
    (fun n g i => by
      change (fun x : Stage G S => g • x) '' RelCWComplex.openCell (C := (univ : Set (Stage G S))) n ((1:G) • i.out) = RelCWComplex.openCell (C := (univ : Set (Stage G S))) n (g • i.out)
      rw [one_smul]
      exact stage_openCell_smul G S n g i.out)
    (fun n g i => by
      change (fun x : Stage G S => g • x) '' RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n ((1:G) • i.out) = RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n (g • i.out)
      rw [one_smul]
      exact stage_closedCell_smul G S n g i.out)

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
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)

variable {E : Type u} [TopologicalSpace E] [MulAction G E] [ContinuousConstSMul G E]

lemma exists_equivariant_skeleton_extension (n : ℕ)
    (b : C(Skeleton (univ : Set X) n,E))
    (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ n g x) = g • b x)
    (hfill : ∀ a : C(Sphere n,E), ∃ d : C(Disk n,E), ∀ x, d (boundary n x) = a x) :
    ∃ e : C(Skeleton (univ : Set X) (n+1),E),
      (∀ x, e (skeletonBase n x) = b x) ∧
      ∀ (g : G) x, e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
  let a (i : ι n) := b.comp (skeletonBoundary n (σ n (1,i)))
  choose d hd using fun i => hfill (a i)
  let D (j : RelCWComplex.cell (univ : Set X) n) : C(Disk n,E) :=
    ⟨fun x => ((σ n).symm j).1 • d ((σ n).symm j).2 x,
      (continuous_const_smul _).comp (d _).continuous⟩
  have hD (j : RelCWComplex.cell (univ : Set X) n) (x : Sphere n) :
      D j (boundary n x) = b (skeletonBoundary n j x) := by
    obtain ⟨⟨g,i⟩,rfl⟩ := (σ n).surjective j
    change ((σ n).symm (σ n (g,i))).1 • d ((σ n).symm (σ n (g,i))).2 (boundary n x) = _
    rw [Equiv.symm_apply_apply,hd]
    change g • b (skeletonBoundary n (σ n (1,i)) x) = _
    rw [←hb]
    congr 1
    apply Subtype.ext
    exact (hσ n g 1 i x.1).symm.trans (by rw [mul_one]; rfl)
  let f := Attachment.lift (skeletonBoundary (C := (univ : Set X)) n) b D hD
  let e : C(Skeleton (univ : Set X) (n+1),E) := f.comp ⟨(skeletonHomeomorph n).symm,(skeletonHomeomorph n).symm.continuous⟩
  have he_base (x : Skeleton (univ : Set X) n) : e (skeletonBase n x) = b x := by
    change f ((skeletonHomeomorph n).symm (skeletonBase n x)) = _
    rw [←skeletonAssembly_base]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.base _ x))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  have he_cell (j : RelCWComplex.cell (univ : Set X) n) (x : Disk n) :
      e (skeletonCell n j x) = D j x := by
    change f ((skeletonHomeomorph n).symm (skeletonCell n j x)) = _
    rw [←skeletonAssembly_cell]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.cell _ j x))) = _
    rw [Homeomorph.symm_apply_apply]
    exact Attachment.lift_cell _ _ _ _ _ _
  refine ⟨e,he_base,?_⟩
  intro g x
  obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
  cases y with
  | inl x =>
    change e (skeletonTranslate σ hσ (n+1) g (skeletonBase n x)) = g • e (skeletonBase n x)
    rw [skeletonTranslate_base,he_base,he_base,hb]
  | inr p =>
    obtain ⟨⟨h,i⟩,hj⟩ := (σ n).surjective p.1
    have heq : skeletonAssembly n (Sum.inr p) = skeletonCell n p.1 (Attachment.interior n p.2) := by
      exact skeletonAssembly_interior n p.1 p.2
    rw [heq,←hj,skeletonTranslate_cell,he_cell,he_cell]
    change ((σ n).symm (σ n (g*h,i))).1 • d ((σ n).symm (σ n (g*h,i))).2 _ =
      g • (((σ n).symm (σ n (h,i))).1 • d ((σ n).symm (σ n (h,i))).2 _)
    simp only [Equiv.symm_apply_apply,mul_smul]
end

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G B]

lemma exists_equivariant_skeleton_lift (n : ℕ) (p : C(E,B))
    (hp : ∀ (g : G) e, p (g • e) = g • p e) (hRLP : DiskRLP p)
    (F : C(Skeleton (univ : Set X) (n+1),B))
    (hF : ∀ (g : G) x, F (skeletonTranslate σ hσ (n+1) g x) = g • F x)
    (b : C(Skeleton (univ : Set X) n,E))
    (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ n g x) = g • b x)
    (hbF : ∀ x, p (b x) = F (skeletonBase n x)) :
    ∃ e : C(Skeleton (univ : Set X) (n+1),E),
      (∀ x, e (skeletonBase n x) = b x) ∧ (∀ x, p (e x) = F x) ∧
      ∀ (g : G) x, e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
  let a (i : ι n) := b.comp (skeletonBoundary n (σ n (1,i)))
  let c (i : ι n) := F.comp (skeletonCell n (σ n (1,i)))
  have hsq (i : ι n) (x : Sphere n) : p (a i x) = c i (boundary n x) := by
    change p (b (skeletonBoundary n (σ n (1,i)) x)) = F (skeletonCell n (σ n (1,i)) (boundary n x))
    rw [hbF]
    rfl
  choose d hd hf using fun i => hRLP n (a i) (c i) (hsq i)
  let D (j : RelCWComplex.cell (univ : Set X) n) : C(Disk n,E) :=
    ⟨fun x => ((σ n).symm j).1 • d ((σ n).symm j).2 x,
      (continuous_const_smul _).comp (d _).continuous⟩
  have hD (j : RelCWComplex.cell (univ : Set X) n) (x : Sphere n) :
      D j (boundary n x) = b (skeletonBoundary n j x) := by
    obtain ⟨⟨g,i⟩,rfl⟩ := (σ n).surjective j
    change ((σ n).symm (σ n (g,i))).1 • d ((σ n).symm (σ n (g,i))).2 (boundary n x) = _
    rw [Equiv.symm_apply_apply,hd]
    change g • b (skeletonBoundary n (σ n (1,i)) x) = _
    rw [←hb]
    congr 1
    apply Subtype.ext
    exact (hσ n g 1 i x.1).symm.trans (by rw [mul_one]; rfl)
  let f := Attachment.lift (skeletonBoundary (C := (univ : Set X)) n) b D hD
  let e : C(Skeleton (univ : Set X) (n+1),E) := f.comp ⟨(skeletonHomeomorph n).symm,(skeletonHomeomorph n).symm.continuous⟩
  have he_base (x : Skeleton (univ : Set X) n) : e (skeletonBase n x) = b x := by
    change f ((skeletonHomeomorph n).symm (skeletonBase n x)) = _
    rw [←skeletonAssembly_base]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.base _ x))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  have he_cell (j : RelCWComplex.cell (univ : Set X) n) (x : Disk n) :
      e (skeletonCell n j x) = D j x := by
    change f ((skeletonHomeomorph n).symm (skeletonCell n j x)) = _
    rw [←skeletonAssembly_cell]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.cell _ j x))) = _
    rw [Homeomorph.symm_apply_apply]
    exact Attachment.lift_cell _ _ _ _ _ _
  have he (g : G) (x : Skeleton (univ : Set X) (n+1)) :
      e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
    obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
    cases y with
    | inl x =>
      change e (skeletonTranslate σ hσ (n+1) g (skeletonBase n x)) = g • e (skeletonBase n x)
      rw [skeletonTranslate_base,he_base,he_base,hb]
    | inr q =>
      obtain ⟨⟨h,i⟩,hj⟩ := (σ n).surjective q.1
      have heq : skeletonAssembly n (Sum.inr q) = skeletonCell n q.1 (Attachment.interior n q.2) :=
        skeletonAssembly_interior n q.1 q.2
      rw [heq,←hj,skeletonTranslate_cell,he_cell,he_cell]
      change ((σ n).symm (σ n (g*h,i))).1 • d ((σ n).symm (σ n (g*h,i))).2 _ =
        g • (((σ n).symm (σ n (h,i))).1 • d ((σ n).symm (σ n (h,i))).2 _)
      simp only [Equiv.symm_apply_apply,mul_smul]
  refine ⟨e,he_base,?_,he⟩
  intro x
  obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
  cases y with
  | inl x =>
    change p (e (skeletonBase n x)) = F (skeletonBase n x)
    rw [he_base,hbF]
  | inr q =>
    rw [skeletonAssembly_interior,he_cell]
    obtain ⟨⟨g,i⟩,hj⟩ := (σ n).surjective q.1
    rw [←hj]
    change p (((σ n).symm (σ n (g,i))).1 • d ((σ n).symm (σ n (g,i))).2 _) = _
    rw [Equiv.symm_apply_apply,hp,hf]
    change g • F (skeletonCell n (σ n (1,i)) _) = _
    rw [←hF,skeletonTranslate_cell,mul_one]
end

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G B]

lemma exists_equivariant_lift_on_skeleton (d : ℕ) (p : C(E,B))
    (hp : ∀ (g : G) e, p (g • e) = g • p e) (hRLP : DiskRLP p)
    (F : C(Skeleton (univ : Set X) d,B))
    (hF : ∀ (g : G) x, F (skeletonTranslate σ hσ d g x) = g • F x) :
    ∃ e : C(Skeleton (univ : Set X) d,E), (∀ x, p (e x) = F x) ∧
      ∀ (g : G) x, e (skeletonTranslate σ hσ d g x) = g • e x := by
  induction d with
  | zero =>
    let := isEmpty_skeleton_zero (X := X)
    exact ⟨⟨isEmptyElim,continuous_of_discreteTopology⟩,fun x => isEmptyElim x,fun _ x => isEmptyElim x⟩
  | succ d ih =>
    obtain ⟨b,hbF,hb⟩ := ih (F.comp (skeletonBase d)) (fun g x => by
      change F (skeletonBase d (skeletonTranslate σ hσ d g x)) = g • F (skeletonBase d x)
      rw [←skeletonTranslate_base,hF])
    obtain ⟨e,_,heF,he⟩ := exists_equivariant_skeleton_lift σ hσ d p hp hRLP F hF b hb hbF
    exact ⟨e,heF,he⟩

lemma exists_equivariant_map_on_skeleton (d : ℕ)
    (hfill : ∀ n < d, ∀ a : C(Sphere n,E), ∃ e : C(Disk n,E), ∀ x, e (boundary n x) = a x) :
    ∃ e : C(Skeleton (univ : Set X) d,E),
      ∀ (g : G) x, e (skeletonTranslate σ hσ d g x) = g • e x := by
  induction d with
  | zero =>
    let := isEmpty_skeleton_zero (X := X)
    exact ⟨⟨isEmptyElim,continuous_of_discreteTopology⟩,fun _ x => isEmptyElim x⟩
  | succ d ih =>
    obtain ⟨b,hb⟩ := ih (fun n hn => hfill n (Nat.lt_succ_of_lt hn))
    obtain ⟨e,_,he⟩ := exists_equivariant_skeleton_extension σ hσ d b hb (hfill d (Nat.lt_succ_self d))
    exact ⟨e,he⟩

variable {Y : Type u} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
lemma exists_equivariant_homotopy_on_skeleton (d : ℕ) (hY : SphereFillable Y)
    (a b : C(Skeleton (univ : Set X) d,Y))
    (ha : ∀ (g : G) x, a (skeletonTranslate σ hσ d g x) = g • a x)
    (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ d g x) = g • b x) :
    ∃ H : a.Homotopy b, ∀ (g : G) t x,
      H (t,skeletonTranslate σ hσ d g x) = g • H (t,x) := by
  let F : C(Skeleton (univ : Set X) d,Y × Y) := a.prodMk b
  have hF (g : G) x : F (skeletonTranslate σ hσ d g x) = g • F x := by
    exact Prod.ext (ha g x) (hb g x)
  obtain ⟨e,heF,he⟩ := exists_equivariant_lift_on_skeleton σ hσ d pathEndpoint
    (fun _ _ => rfl) (pathEndpoint_RLP hY) F hF
  let H : a.Homotopy b :=
    { toFun := fun z => e z.2 z.1
      continuous_toFun := e.continuous.comp continuous_snd |>.eval continuous_fst
      map_zero_left := fun x => congrArg Prod.fst (heF x)
      map_one_left := fun x => congrArg Prod.snd (heF x) }
  refine ⟨H,?_⟩
  intro g t x
  exact ContinuousMap.congr_fun (he g x) t

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

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_9
variable (φ : G →* H) (α : ℕ → ℕ) (S : Shapes G) (T : Shapes H)
variable (hv : ∀ s : Face (stage G S), faceImage φ α s.1 ∈ stage H T)

def stageMap : C(Simplicial.Space (stage G S), Simplicial.Space (stage H T)) :=
  mapC _ _ (vertexMap φ α) hv

end

open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical Topology.Homotopy unitInterval
universe u v w
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

namespace FiniteEnvelope

variable {I X : Type*}

variable (r : Set (FreeGroup X)) (S : Set (I × I)) (T : Set (I × I × I))

variable {r S T}

variable {G : Type*} [Group G]
variable (h : I → PresentedGroup r →* G)
variable (hsame : ∀ s : S, h s.val.1 = h s.val.2)
variable (hcomm : ∀ t : T, ∀ u v, Commute (h t.val.1 u) (h t.val.2.1 v))
variable (hsum : ∀ t : T, ∀ u, h t.val.2.2 u = h t.val.1 u * h t.val.2.1 u)

include hsame hcomm hsum

lemma model_satisfies_relations : ∀ w ∈ relators r S T,
    FreeGroup.lift (fun ix : I × X => h ix.1 (.of ix.2)) w = 1 := by
  have hc (i : I) :
      (FreeGroup.lift (fun ix : I × X => h ix.1 (.of ix.2))).comp
        (FreeGroup.map fun x => (i, x)) = (h i).comp (PresentedGroup.mk r) := by
    apply FreeGroup.ext_hom
    intro x
    simp only [MonoidHom.comp_apply, FreeGroup.map.of, FreeGroup.lift_apply_of]
    rfl
  rintro _ ⟨idx, rfl⟩
  rcases idx with ⟨i, w⟩ | ⟨s, x⟩ | ⟨t, x, y⟩ | ⟨t, x⟩
  · change ((FreeGroup.lift _).comp (FreeGroup.map fun x => (i, x))) w.val = 1
    rw [hc]
    simp only [MonoidHom.comp_apply, PresentedGroup.one_of_mem w.property, map_one]
  · simp only [relationWord, map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [hsame s, mul_inv_cancel]
  · simp only [relationWord, map_mul, map_inv, FreeGroup.lift_apply_of]
    exact mul_inv_eq_one.mpr (hcomm t (.of x) (.of y)).eq
  · simp only [relationWord, map_mul, map_inv, FreeGroup.lift_apply_of]
    exact mul_inv_eq_one.mpr (hsum t (.of x))

def modelMap : Envelope r S T →* G :=
  PresentedGroup.toGroup (model_satisfies_relations h hsame hcomm hsum)

@[simp]
lemma modelMap_copy (i : I) : (modelMap h hsame hcomm hsum).comp (copy r S T i) = h i := by
  apply PresentedGroup.ext
  intro x
  simp only [MonoidHom.comp_apply, copy_of, modelMap, PresentedGroup.toGroup.of]

end FiniteEnvelope

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

lemma rank_one_difference (z : Matrix (Fin 3) (Fin 3) K → T)
    (hz : OrthogonallyAdditive z) (u l v m : Fin 3 → K)
    (hlu : l ⬝ᵥ u = 1) (hlv : l ⬝ᵥ v = 0)
    (hmu : m ⬝ᵥ u = 0) (hmv : m ⬝ᵥ v = 1) :
    z (vecMulVec (u + v) l) - z (vecMulVec u l) =
      z (vecMulVec v m) - z (vecMulVec v (m - l)) := by
  have hmlv : (m - l) ⬝ᵥ v = 1 := by simp [sub_dotProduct, hmv, hlv]
  have hluv : l ⬝ᵥ (u + v) = 1 := by simp [dotProduct_add, hlu, hlv]
  have hmluv : (m - l) ⬝ᵥ (u + v) = 0 := by
    simp [sub_dotProduct, dotProduct_add, hmu, hmv, hlu, hlv]
  have h₁ := hz (vecMulVec u l) (vecMulVec v m)
    (rank_one_idempotent u l hlu) (rank_one_idempotent v m hmv)
    (rank_one_mul_zero u l v m hlv) (rank_one_mul_zero v m u l hmu)
  have h₂ := hz (vecMulVec (u + v) l) (vecMulVec v (m - l))
    (rank_one_idempotent (u + v) l hluv) (rank_one_idempotent v (m - l) hmlv)
    (rank_one_mul_zero (u + v) l v (m - l) hlv)
    (rank_one_mul_zero v (m - l) (u + v) l hmluv)
  have heq : vecMulVec u l + vecMulVec v m =
      vecMulVec (u + v) l + vecMulVec v (m - l) := by
    ext i j
    simp only [Matrix.add_apply, vecMulVec_apply, Pi.add_apply, Pi.sub_apply]
    ring
  rw [heq, h₂] at h₁
  apply sub_eq_sub_iff_add_eq_add.mpr
  exact h₁.trans (add_comm _ _)

lemma increment_independent (z : Matrix (Fin 3) (Fin 3) K → T)
    (hz : OrthogonallyAdditive z) (s t : K) :
    z (vecMulVec (along s (t + 1)) (row s)) - z (vecMulVec (along s t) (row s)) =
      z (vecMulVec (along s 1) (row s)) - z (vecMulVec (along s 0) (row s)) := by
  have hd (r : K) :
      z (vecMulVec (along s (r + 1)) (row s)) - z (vecMulVec (along s r) (row s)) =
        z (vecMulVec ((anchor : Fin 3 → K) + direction s) (row s)) -
          z (vecMulVec (anchor : Fin 3 → K) (row s)) := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := frame_identities s r
    rw [← along_step]
    exact (rank_one_difference z hz _ _ _ _ h₁ h₂ h₃ h₄).trans
      (rank_one_difference z hz _ _ _ _ h₅ h₂ h₆ h₄).symm
  exact (hd t).trans (by simpa using (hd 0).symm)

theorem prime_multiple_step (z : Matrix (Fin 3) (Fin 3) K → T)
    (hz : OrthogonallyAdditive z) (p : ℕ) [CharP K p] (s : K) :
    p • z (vecMulVec (along s 1) (row s)) =
      p • z (vecMulVec (along s 0) (row s)) := by
  let F (n : ℕ) := z (vecMulVec (along s (n : K)) (row s))
  let d := F 1 - F 0
  have hstep (n : ℕ) : F (n + 1) - F n = d := by
    simpa only [F, d, Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
      increment_independent z hz s (n : K)
  have hF (n : ℕ) : F n = F 0 + n • d := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hstep n
      rw [ih, succ_nsmul] at *
      exact (sub_eq_iff_eq_add.mp h).trans (by abel)
  have hp : F p = F 0 := by simp only [F, CharP.cast_eq_zero, Nat.cast_zero]
  have hpd : p • d = 0 := by
    have h := (hF p).symm.trans hp
    simpa only [add_eq_left] using h
  have h := sub_eq_zero.mp (show p • F 1 - p • F 0 = 0 by
    simpa only [d, nsmul_sub] using hpd)
  simpa only [F, Nat.cast_one, Nat.cast_zero] using h

theorem diagonal_zero_one (z : Matrix (Fin 3) (Fin 3) K → T)
    (hz : OrthogonallyAdditive z) (p : ℕ) [CharP K p] :
    p • z (diagonalUnit 0) = p • z (diagonalUnit 1) := by
  have hleft := prime_multiple_step (fun E => z E.transpose) hz.transpose p 0
  have hmid := prime_multiple_step z hz p 1
  let q := (Matrix.reindexRingEquiv K (Equiv.swap (0 : Fin 3) 1)).toRingHom
  have hright := prime_multiple_step (fun E => z (q E).transpose)
    (hz.transpose.comp q) p 0
  have e0 : along (0 : K) 0 = basisVector 0 := by
    ext i; fin_cases i <;> simp [along, basisVector]
  have r0 : row (0 : K) = basisVector 0 := by
    ext i; fin_cases i <;> simp [row, basisVector]
  have e1 : along (1 : K) 1 = basisVector 1 := by
    ext i; fin_cases i <;> simp [along, basisVector]
  have m0 : along (1 : K) 0 = basisVector 0 := by
    ext i; fin_cases i <;> simp [along, basisVector]
  have r1 : along (0 : K) 1 = row (1 : K) := by
    ext i; fin_cases i <;> simp [along, row]
  have q0 : q (vecMulVec (along 0 0) (row 0)) = diagonalUnit 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [q, Matrix.reindex, Matrix.submatrix, along, row,
        diagonalUnit, basisVector, Pi.single_apply, vecMulVec, Equiv.swap_apply_def]
  have q1 : (q (vecMulVec (along 0 1) (row 0))).transpose =
      vecMulVec (basisVector 1) (row 1) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [q, Matrix.reindex, Matrix.submatrix, along, row,
        basisVector, Pi.single_apply, vecMulVec, Equiv.swap_apply_def]
  rw [transpose_vecMulVec, transpose_vecMulVec, e0, r0, r1] at hleft
  rw [e1, m0] at hmid
  rw [q0, q1, diagonalUnit, transpose_vecMulVec] at hright
  exact hleft.symm.trans (hmid.symm.trans hright)

lemma reindex_diagonalUnit (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    reindexRingEquiv K e (diagonalUnit i) = diagonalUnit (e i) := by
  have hb (x : Fin 3) : basisVector i (e.symm x) = (basisVector (e i) x : K) := by
    by_cases hx : x = e i
    · subst x; simp [basisVector]
    · have hx' : e.symm x ≠ i := fun h => hx (by simpa using congrArg e h)
      simp [basisVector, hx, hx']
  ext x y
  change basisVector i (e.symm x) * basisVector i (e.symm y) =
    (basisVector (e i) x : K) * basisVector (e i) y
  rw [hb, hb]

theorem diagonal_equality (z : Matrix (Fin 3) (Fin 3) K → T)
    (hz : OrthogonallyAdditive z) (p : ℕ) [CharP K p] (i j : Fin 3) :
    p • z (diagonalUnit i) = p • z (diagonalUnit j) := by
  have h01 := diagonal_zero_one z hz p
  let e := Equiv.swap (1 : Fin 3) 2
  let q := (reindexRingEquiv K e).toRingHom
  have h02 := diagonal_zero_one (fun E => z (q E)) (hz.comp q) p
  have hq (i : Fin 3) : q (diagonalUnit i) = diagonalUnit (e i) :=
    reindex_diagonalUnit e i
  simp only [hq] at h02
  have he0 : e 0 = 0 := by decide
  have he1 : e 1 = 2 := by decide
  rw [he0, he1] at h02
  have h0 (i : Fin 3) : p • z (diagonalUnit 0) = p • z (diagonalUnit i) := by
    fin_cases i
    · rfl
    · exact h01
    · exact h02
  exact (h0 i).symm.trans (h0 j)

lemma diagonalUnit_orthogonal {i j : Fin 3} (hij : i ≠ j) :
    (diagonalUnit i : Matrix (Fin 3) (Fin 3) K) * diagonalUnit j = 0 := by
  apply rank_one_mul_zero
  simp [basisVector, dotProduct, Pi.single_apply, Ne.symm hij]

end MatrixDiagram

namespace PrefixAlgebra

variable (K : Type*) [CommRing K]

lemma delete_prefix (i j : Bool) :
    delete K i * prefixOp K j = if i = j then 1 else 0 := by
  apply Finsupp.lhom_ext
  intro s a
  simp only [Module.End.mul_apply, prefix_single, delete_single,
    Stream'.head_cons, Stream'.tail_cons]
  by_cases h : i = j
  · subst j; simp
  · simp [h, Ne.symm h]

lemma right_left (i j : Bool) : right K i * left K j = if i = j then 1 else 0 := by
  apply Subtype.ext
  simpa only [Subalgebra.coe_mul, left, right, Subalgebra.coe_one, Subalgebra.coe_zero,
    apply_ite] using delete_prefix K i j

lemma partition : left K false * right K false + left K true * right K true = 1 := by
  apply Subtype.ext
  exact prefix_partition K

lemma cancel_initial (b c : Bool) (v w : List Bool) :
    rightWord K (b :: v) * leftWord K (c :: w) =
      if b = c then rightWord K v * leftWord K w else 0 := by
  simp only [rightWord, leftWord]
  rw [mul_assoc, ← mul_assoc (right K b), right_left]
  by_cases h : b = c <;> simp [h]

@[simp] lemma word_cancel (w : List Bool) : rightWord K w * leftWord K w = 1 := by
  induction w with
  | nil => simp
  | cons b w ih => rw [cancel_initial, ite_eq_left rfl, ih]

lemma word_orthogonality (a i j : Fin 3) :
    rightWord K (words a i) * leftWord K (words a j) = if i = j then 1 else 0 := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [words, cancel_initial]

noncomputable def projection (w : List Bool) : algebra K := leftWord K w * rightWord K w

lemma projection_split (w : List Bool) :
    projection K w = projection K (w ++ [false]) + projection K (w ++ [true]) := by
  have hl (w v : List Bool) : leftWord K (w ++ v) = leftWord K w * leftWord K v := by
    induction w with
    | nil => simp [leftWord]
    | cons b w ih => simp only [List.cons_append, leftWord, ih, mul_assoc]
  have hr (w v : List Bool) : rightWord K (w ++ v) = rightWord K v * rightWord K w := by
    induction w with
    | nil => simp [rightWord]
    | cons b w ih => simp only [List.cons_append, rightWord, ih, mul_assoc]
  simp only [projection, hl, hr, leftWord, rightWord, mul_one, one_mul]
  calc
    _ = leftWord K w * (left K false * right K false + left K true * right K true) * rightWord K w := by
      rw [partition, mul_one]
    _ = _ := by noncomm_ring

end PrefixAlgebra

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

noncomputable instance algebraRing : Ring (algebra K) :=
  @Subalgebra.toRing K (Operators K) _ _ _ (algebra K)

noncomputable def corner (a : Fin 3) : Matrix (Fin 3) (Fin 3) K →ₙₐ[K] algebra K :=
  MatrixCorners.hom (fun i => leftWord K (words a i))
    (fun i => rightWord K (words a i)) (word_orthogonality K a)

def carrier : Set (algebra K) :=
  {E | E = 1 ∨ ∃ a M, IsIdempotentElem M ∧ E = corner K a M}

lemma carrier_finite [Finite K] : (carrier K).Finite := by
  classical
  apply ((Set.finite_singleton (1 : algebra K)).union
    (Set.finite_range (fun x : Fin 3 × Matrix (Fin 3) (Fin 3) K => corner K x.1 x.2))).subset
  rintro E (rfl | ⟨a, M, _, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨(a,M), rfl⟩

lemma one_mem : (1 : algebra K) ∈ carrier K := Or.inl rfl

lemma corner_mem (a : Fin 3) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : IsIdempotentElem M) : corner K a M ∈ carrier K :=
  Or.inr ⟨a, M, hM, rfl⟩

lemma carrier_idempotent (E : algebra K) (hE : E ∈ carrier K) : IsIdempotentElem E := by
  rcases hE with rfl | ⟨a, M, hM, rfl⟩
  · exact IsIdempotentElem.one
  · change corner K a M * corner K a M = corner K a M
    rw [← map_mul, hM.eq]

lemma corner_diagonal (a i : Fin 3) :
    corner K a (MatrixDiagram.diagonalUnit i) = projection K (words a i) := by
  rw [diagonalUnit_eq_diagonal]
  exact MatrixCorners.map_diagonal (K := K)
    (fun i => leftWord K (words a i)) (fun i => rightWord K (words a i))
    (word_orthogonality K a) i

lemma projection_mem (a i : Fin 3) : projection K (words a i) ∈ carrier K := by
  rw [← corner_diagonal]
  exact corner_mem K a _ (MatrixDiagram.diagonalUnit_idempotent i)

lemma projection_first_sum :
    projection K (words 0 0) + projection K (words 0 1) + projection K (words 0 2) = 1 := by
  change projection K [false,false] + projection K [false,true] + projection K [true] = 1
  have h := projection_split K [false]
  have h' := projection_split K []
  simp only [List.cons_append, List.nil_append] at h h'
  rw [← h, ← h']
  simp [projection]

lemma projection_mul_zero (v w : List Bool)
    (h : rightWord K v * leftWord K w = 0) : projection K v * projection K w = 0 := by
  simp only [projection]
  rw [mul_assoc, ← mul_assoc (rightWord K v), h, zero_mul, mul_zero]

lemma projection_orthogonal (a : Fin 3) {i j : Fin 3} (hij : i ≠ j) :
    projection K (words a i) * projection K (words a j) = 0 :=
  projection_mul_zero K _ _ (by rw [word_orthogonality, ite_eq_right hij])

variable {T : Type*} [AddCommGroup T]

def AdditiveOnDiagram (z : algebra K → T) : Prop :=
  ∀ E P, E ∈ carrier K → P ∈ carrier K → E + P ∈ carrier K →
    E * P = 0 → P * E = 0 → z (E + P) = z E + z P

lemma restrict_additive (z : algebra K → T) (hz : AdditiveOnDiagram K z) (a : Fin 3) :
    MatrixDiagram.OrthogonallyAdditive (fun M => z (corner K a M)) := by
  intro E P hE hP hEP hPE
  have hsum := corner_mem K a (E + P) (sum_idempotent hE hP hEP hPE)
  rw [map_add] at hsum
  change z (corner K a (E + P)) = z (corner K a E) + z (corner K a P)
  rw [map_add]
  apply hz _ _ (corner_mem K a E hE) (corner_mem K a P hP) hsum
  · rw [← map_mul, hEP, map_zero]
  · rw [← map_mul, hPE, map_zero]

lemma projection_multiples (z : algebra K → T) (hz : AdditiveOnDiagram K z)
    (p : ℕ) [CharP K p] (a i j : Fin 3) :
    p • z (projection K (words a i)) = p • z (projection K (words a j)) := by
  simpa only [corner_diagonal] using
    MatrixDiagram.diagonal_equality (fun M => z (corner K a M))
      (restrict_additive K z hz a) p i j

lemma first_projection_zero (z : algebra K → T) (hz : AdditiveOnDiagram K z)
    (p : ℕ) [CharP K p] : p • z (projection K [false,false]) = 0 := by
  let A := projection K [false,false]
  let B := projection K [false,true]
  let A₀ := projection K [false,false,false]
  let A₁ := projection K [false,false,true]
  have hA : A ∈ carrier K := projection_mem K 0 0
  have hA₀ : A₀ ∈ carrier K := projection_mem K 1 0
  have hA₁ : A₁ ∈ carrier K := projection_mem K 2 0
  have hAB : p • z A = p • z B := projection_multiples K z hz p 0 0 1
  have hA₀B : p • z A₀ = p • z B := projection_multiples K z hz p 1 0 1
  have hA₁B : p • z A₁ = p • z B := projection_multiples K z hz p 2 0 1
  have hsplit : A = A₀ + A₁ := projection_split K [false,false]
  have horth₀₁ : A₀ * A₁ = 0 := by
    apply projection_mul_zero
    simp only [cancel_initial, Bool.false_eq_true, ite_false, ite_true]
  have horth₁₀ : A₁ * A₀ = 0 := by
    apply projection_mul_zero
    simp only [cancel_initial, Bool.true_eq_false, ite_false, ite_true]
  have hsum := hz A₀ A₁ hA₀ hA₁ (hsplit ▸ hA) horth₀₁ horth₁₀
  rw [← hsplit] at hsum
  have hq : p • z A = p • z A + p • z A := calc
    p • z A = p • z A₀ + p • z A₁ := by rw [hsum, nsmul_add]
    _ = _ := by rw [hA₀B, hA₁B, ← hAB]
  apply add_left_cancel (a := p • z A)
  exact hq.symm.trans (add_zero _).symm

lemma first_two_mem : projection K (words 0 0) + projection K (words 0 1) ∈ carrier K := by
  have hd := corner_mem K 0
    ((MatrixDiagram.diagonalUnit 0 : Matrix (Fin 3) (Fin 3) K) + MatrixDiagram.diagonalUnit 1)
    (sum_idempotent (MatrixDiagram.diagonalUnit_idempotent 0)
      (MatrixDiagram.diagonalUnit_idempotent 1)
      (MatrixDiagram.diagonalUnit_orthogonal (by decide : (0 : Fin 3) ≠ 1))
      (MatrixDiagram.diagonalUnit_orthogonal (by decide : (1 : Fin 3) ≠ 0)))
  simpa only [map_add, corner_diagonal] using hd

lemma identity_additive_decomposition (z : algebra K → T) (hz : AdditiveOnDiagram K z) :
    z 1 = z (projection K (words 0 0)) + z (projection K (words 0 1)) +
      z (projection K (words 0 2)) := by
  let A := projection K (words 0 0)
  let B := projection K (words 0 1)
  let C := projection K (words 0 2)
  have hA : A ∈ carrier K := projection_mem K 0 0
  have hB : B ∈ carrier K := projection_mem K 0 1
  have hC : C ∈ carrier K := projection_mem K 0 2
  have hABorth : A * B = 0 := projection_orthogonal K 0 (by decide : (0 : Fin 3) ≠ 1)
  have hBAorth : B * A = 0 := projection_orthogonal K 0 (by decide : (1 : Fin 3) ≠ 0)
  have hACorth : A * C = 0 := projection_orthogonal K 0 (by decide : (0 : Fin 3) ≠ 2)
  have hBCorth : B * C = 0 := projection_orthogonal K 0 (by decide : (1 : Fin 3) ≠ 2)
  have hCAorth : C * A = 0 := projection_orthogonal K 0 (by decide : (2 : Fin 3) ≠ 0)
  have hCBorth : C * B = 0 := projection_orthogonal K 0 (by decide : (2 : Fin 3) ≠ 1)
  have hABmem : A + B ∈ carrier K := first_two_mem K
  have hone : A + B + C = 1 := projection_first_sum K
  have hzAB := hz A B hA hB hABmem hABorth hBAorth
  have hzI := hz (A + B) C hABmem hC (hone.symm ▸ one_mem K)
    (by rw [add_mul, hACorth, hBCorth, add_zero])
    (by rw [mul_add, hCAorth, hCBorth, add_zero])
  rw [hone, hzAB] at hzI
  exact hzI

theorem annihilates_identity (z : algebra K → T) (hz : AdditiveOnDiagram K z)
    (p : ℕ) [CharP K p] : p • z 1 = 0 := by
  rw [identity_additive_decomposition K z hz, nsmul_add, nsmul_add,
    ← projection_multiples K z hz p 0 0 1, ← projection_multiples K z hz p 0 0 2]
  have h : p • z (projection K (words 0 0)) = 0 := first_projection_zero K z hz p
  rw [h, add_zero, add_zero]

theorem annihilates_identity_subtype (z : carrier K → T)
    (hz : ∀ E P : carrier K, ∀ hsum : E.val + P.val ∈ carrier K,
      E.val * P.val = 0 → P.val * E.val = 0 →
        z ⟨E.val + P.val, hsum⟩ = z E + z P)
    (p : ℕ) [CharP K p] : p • z ⟨1, one_mem K⟩ = 0 := by
  classical
  let z' : algebra K → T := fun E => if h : E ∈ carrier K then z ⟨E,h⟩ else 0
  have hz' : AdditiveOnDiagram K z' := by
    intro E P hE hP hsum hEP hPE
    simpa only [z', dite_eq_left hE, dite_eq_left hP, dite_eq_left hsum] using
      hz ⟨E,hE⟩ ⟨P,hP⟩ hsum hEP hPE
  simpa only [z', dite_eq_left (one_mem K)] using annihilates_identity K z' hz' p

end IdempotentSystems

namespace ConcreteEnvelopes

open PrefixAlgebra IdempotentSystems

noncomputable def system (K : Type) [Field K] [Finite K] :
    FiniteIdempotentSystem (algebra K) where
  carrier := IdempotentSystems.carrier K
  finite := carrier_finite K
  one_mem := one_mem K
  idempotent := fun E h => carrier_idempotent K E h

noncomputable abbrev P₂ := system (ZMod 2)
noncomputable abbrev P₃ := system (ZMod 3)
abbrev Index := TwoEnvelope.Index P₂ P₃
abbrev triples := TwoEnvelope.triples P₂ P₃

structure IsDiagram {V W : Type} [Group V] [Group W] (k : Index → V →* W) : Prop where
  common : k (.inl P₂.identity) = k (.inr P₃.identity)
  commute : ∀ t : triples, ∀ u v, Commute (k t.val.1 u) (k t.val.2.1 v)
  sum : ∀ t : triples, ∀ u, k t.val.2.2 u = k t.val.1 u * k t.val.2.1 u

theorem coprime_annihilation {T : Type*} [AddCommGroup T]
    (z : Index → T)
    (hc : z (.inl P₂.identity) = z (.inr P₃.identity))
    (hs : ∀ t : triples, z t.val.2.2 = z t.val.1 + z t.val.2.1) :
    z (.inl P₂.identity) = 0 := by
  have h₂ : 2 • z (.inl P₂.identity) = 0 := by
    apply annihilates_identity_subtype (ZMod 2)
      (fun E => z (.inl E))
    intro E F hsum hEF hFE
    exact hs ⟨(.inl E, .inl F, .inl ⟨E.val + F.val, hsum⟩),
      ⟨hEF, hFE, rfl⟩⟩
  have h₃ : 3 • z (.inr P₃.identity) = 0 := by
    apply annihilates_identity_subtype (ZMod 3)
      (fun E => z (.inr E))
    intro E F hsum hEF hFE
    exact hs ⟨(.inr E, .inr F, .inr ⟨E.val + F.val, hsum⟩),
      ⟨hEF, hFE, rfl⟩⟩
  rw [← hc] at h₃
  have hx : (3 : ℕ) • z (.inl P₂.identity) = 2 • z (.inl P₂.identity) +
      z (.inl P₂.identity) := by exact succ_nsmul _ 2
  rw [hx, h₂, zero_add] at h₃
  exact h₃

end ConcreteEnvelopes
end UniversalFInfinity

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

namespace UniversalFInfinity.Cellular
open Set Metric Topology
universe u v w
variable {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]

def KillsSpheres (q : C(Y,Z)) (n : ℕ) : Prop :=
  ∀ a : C(Sphere n,Y), ∃ F : C(Disk n,Z), ∀ x, F (boundary n x) = q (a x)

lemma cylinder_filling_after {n : ℕ} (q : C(Y,Z)) (hq : KillsSpheres q (n+1))
    (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))
    (h : ∀ x, pathEndpoint (a x) = b (boundary n x)) :
    ∃ e : C(Disk n,C(unitInterval,Z)),
      (∀ x t, e (boundary n x) t = q (a x t)) ∧
      ∀ x, pathEndpoint (e x) = (q (b x).1,q (b x).2) := by
  obtain ⟨F,hF⟩ := hq (cylinderBoundaryMap a b h)
  let e : C(Disk n,C(unitInterval,Z)) :=
    (F.comp ⟨fun p : Disk n × unitInterval => diskCons p.1 p.2,continuous_diskCons⟩).curry
  refine ⟨e,?_,?_⟩
  · intro x t
    let s : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
    have hs : s ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) t)).1 ∈ sphere 0 1
      rw [diskTail_cons]
      exact x.2
    change F (diskCons (boundary n x) t) = q (a x t)
    rw [show diskCons (boundary n x) t = boundary (n+1) s from rfl,hF,
      cylinderBoundaryMap_face a b h none ⟨s,hs⟩]
    change q (a (faceSphere ⟨s,hs⟩) (diskTime (diskCons (boundary n x) t))) = q (a x t)
    rw [diskTime_cons]
    congr 2
  · intro x
    apply Prod.ext
    · let s : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some false) := by
        change (diskCons x 0).1 0 = -1
        norm_num [diskCons]
      change F (diskCons x 0) = q (b x).1
      rw [show diskCons x 0 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some false) ⟨s,hs⟩]
      change q (b (diskTail (diskCons x 0))).1 = q (b x).1
      rw [diskTail_cons]
    · let s : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some true) := by
        change (diskCons x 1).1 0 = 1
        norm_num [diskCons]
      change F (diskCons x 1) = q (b x).2
      rw [show diskCons x 1 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some true) ⟨s,hs⟩]
      change q (b (diskTail (diskCons x 1))).2 = q (b x).2
      rw [diskTail_cons]

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

namespace PartialHomotopy
variable {f g : C(X,Y)} {n : ℕ}

def onSphere (a : PartialHomotopy (C := C) f g n) (i : RelCWComplex.cell C n) :
    C(Sphere n,C(unitInterval,Y)) :=
  ⟨fun x => a.val (characteristic n i (boundary n x)),
    a.continuousOn.comp_continuous ((characteristic n i).continuous.comp (continuous_boundary n))
      (sphere_mem_skeleton n i)⟩

def endpoints (i : RelCWComplex.cell C n) : C(Disk n,Y × Y) :=
  ⟨fun x => (f (characteristic n i x),g (characteristic n i x)),
    (f.continuous.comp (characteristic n i).continuous).prodMk
      (g.continuous.comp (characteristic n i).continuous)⟩

lemma endpoints_compatible (a : PartialHomotopy (C := C) f g n)
    (i : RelCWComplex.cell C n) (x : Sphere n) :
    pathEndpoint (a.onSphere i x) = endpoints (f := f) (g := g) i (boundary n x) :=
  Prod.ext (a.zero _ (sphere_mem_skeleton n i x)) (a.one _ (sphere_mem_skeleton n i x))

lemma cell_extension_after (a : PartialHomotopy (C := C) f g n)
    (q : C(Y,Z)) (hq : KillsSpheres q (n+1)) (i : RelCWComplex.cell C n) :
    ∃ e : C(Disk n,C(unitInterval,Z)),
      (∀ x, e (boundary n x) = q.comp (a.val (characteristic n i (boundary n x)))) ∧
      (∀ x, e x 0 = q (f (characteristic n i x))) ∧
      (∀ x, e x 1 = q (g (characteristic n i x))) := by
  obtain ⟨e,he,hp⟩ := cylinder_filling_after q hq (a.onSphere i) (endpoints i)
    (a.endpoints_compatible i)
  exact ⟨e,fun x => ContinuousMap.ext (he x),fun x => congrArg Prod.fst (hp x),
    fun x => congrArg Prod.snd (hp x)⟩

def next (a : PartialHomotopy (C := C) f g n)
    (q : C(Y,Z)) (hq : KillsSpheres q (n+1)) :
    PartialHomotopy (C := C) (q.comp f) (q.comp g) (n+1) := by
  let e := fun i => (a.cell_extension_after q hq i).choose
  have hb : ∀ i x, e i (boundary n x) =
      q.comp (a.val (characteristic n i (boundary n x))) :=
    fun i => (a.cell_extension_after q hq i).choose_spec.1
  have hz := fun i => (a.cell_extension_after q hq i).choose_spec.2.1
  have ho := fun i => (a.cell_extension_after q hq i).choose_spec.2.2
  let v : X → C(unitInterval,Z) := fun x => q.comp (a.val x)
  have hv : ContinuousOn v (Skeleton C n) :=
    (ContinuousMap.continuous_postcomp q).comp_continuousOn a.continuousOn
  refine ⟨attachValue v e,attachValue_continuous v hv e hb,?_,?_⟩
  all_goals
    intro x hx
    have heq : Skeleton C (n+1) = Skeleton C n ∪
        ⋃ i : RelCWComplex.cell C n, CWComplex.closedCell n i := by
      simpa only [Skeleton,Nat.cast_add,Nat.cast_one] using
        (CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ (C := C) n).symm
    rw [heq] at hx
    rcases hx with hx | hx
    · rw [attachValue_old v e hx]
      first
      | exact congrArg q (a.zero x hx)
      | exact congrArg q (a.one x hx)
    · obtain ⟨i,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
      rw [show RelCWComplex.map n i y = characteristic n i ⟨y,hy⟩ from rfl,
        attachValue_characteristic v e hb]
      first | exact hz i ⟨y,hy⟩ | exact ho i ⟨y,hy⟩

def start (f g : C(X,Y)) : PartialHomotopy (C := C) f g 0 where
  val := fun x => ContinuousMap.const _ (f x)
  continuousOn := by
    rw [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty]
    exact continuousOn_empty _
  zero := by intro x _; rfl
  one := by
    intro x hx
    simp only [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty,Set.mem_empty_iff_false] at hx

def toHomotopy [CWComplex (Set.univ : Set X)] (a : PartialHomotopy (C := (Set.univ : Set X)) f g n)
    (hdim : Skeleton (Set.univ : Set X) n = Set.univ) : f.Homotopy g where
  toFun p := a.val p.2 p.1
  continuous_toFun := by
    have hv : Continuous a.val := by
      have hh := a.continuousOn
      rw [hdim] at hh
      exact continuousOn_univ.mp hh
    exact continuous_eval.comp ((hv.comp continuous_snd).prodMk continuous_fst)
  map_zero_left x := a.zero x (hdim.symm ▸ Set.mem_univ x)
  map_one_left x := a.one x (hdim.symm ▸ Set.mem_univ x)

end PartialHomotopy
end UniversalFInfinity.Cellular

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

namespace UniversalFInfinity.Cylinder

section

variable {n : ℕ}

lemma retract_mem_rim (p : unitInterval × Disk n) :
    (⟨2-factor p*(2-(p.1:ℝ)),retract_time_mem p⟩ : unitInterval) = 0 ∨
      factor p • p.2.1 ∈ sphere (0 : Fin n → ℝ) 1 := by
  rcases le_total (2*‖p.2.1‖) (2-(p.1:ℝ)) with h | h
  · left
    apply Subtype.ext
    have hd : denominator p = 2-(p.1:ℝ) := max_eq_left h
    have heq := factor_mul_denominator p
    rw [hd] at heq
    simpa only [Set.Icc.coe_zero,sub_eq_zero] using heq.symm
  · right
    simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg (factor_nonneg p)]
    have hd : denominator p = 2*‖p.2.1‖ := max_eq_right h
    have heq := factor_mul_denominator p
    rw [hd] at heq
    nlinarith

lemma continuous_denominator : Continuous (@denominator n) :=
  (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).max
    (continuous_const.mul ((continuous_subtype_val.comp continuous_snd).norm))
lemma continuous_factor : Continuous (@factor n) :=
  continuous_const.div continuous_denominator (fun p => ne_of_gt (denominator_pos p))

def retract (n : ℕ) : C(unitInterval × Disk n,Rim n) := by
  have htime : Continuous (fun p : unitInterval × Disk n =>
      (⟨2-factor p*(2-(p.1:ℝ)),retract_time_mem p⟩ : unitInterval)) :=
    (continuous_const.sub (continuous_factor.mul
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)))).subtype_mk _
  have hdisk : Continuous (fun p : unitInterval × Disk n =>
      (⟨factor p • p.2.1,retract_disk_mem p⟩ : Disk n)) :=
    (continuous_factor.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  exact ⟨fun p => ⟨(⟨_,retract_time_mem p⟩,⟨_,retract_disk_mem p⟩),retract_mem_rim p⟩,
    (htime.prodMk hdisk).subtype_mk _⟩

lemma retract_of_rim (p : Rim n) : (retract n p.1).1 = p.1 := by
  have hd : denominator p.1 = 2 := by
    rcases p.2 with ht | hx
    · have hx' : ‖p.1.2.1‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using p.1.2.2
      simp only [denominator,ht,Set.Icc.coe_zero,sub_zero]
      exact max_eq_left (by linarith)
    · have hx' : ‖p.1.2.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hx
      simp only [denominator,hx',mul_one]
      exact max_eq_right (by linarith [p.1.1.2.1])
  have hf : factor p.1 = 1 := by simp [factor,hd]
  apply Prod.ext
  · apply Subtype.ext
    change 2-factor p.1*(2-(p.1.1:ℝ)) = (p.1.1:ℝ)
    rw [hf,one_mul]
    ring
  · apply Subtype.ext
    change factor p.1 • p.1.2.1 = p.1.2.1
    rw [hf,one_smul]

end

open Set Metric Topology
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y]

lemma face_closed (n : ℕ) (i : Bool) : IsClosed (face n i) := by
  cases i
  · exact isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  · exact isClosed_sphere.preimage ((continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val)

def faceValue (F : C(Disk n,Y)) (H : C(unitInterval × Sphere n,Y)) : ∀ i : Bool, C(face n i,Y)
  | false => ⟨fun p => F p.1.1.2,F.continuous.comp ((continuous_snd.comp continuous_subtype_val).comp continuous_subtype_val)⟩
  | true => ⟨fun p => H (p.1.1.1,⟨p.1.1.2.1,p.2⟩),H.continuous.comp
      (((continuous_fst.comp continuous_subtype_val).comp continuous_subtype_val).prodMk
        (((continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val).comp continuous_subtype_val |>.subtype_mk _))⟩

variable (F : C(Disk n,Y)) (H : C(unitInterval × Sphere n,Y))
variable (h : ∀ x : Sphere n, H (0,x) = F ⟨x.1,sphere_subset_closedBall x.2⟩)
include h in
lemma faceValue_compatible (i j : Bool) (p : Rim n) (hi : p ∈ face n i) (hj : p ∈ face n j) :
    faceValue F H i ⟨p,hi⟩ = faceValue F H j ⟨p,hj⟩ := by
  have hcross (h0 : p.1.1 = 0) (hs : p.1.2.1 ∈ sphere 0 1) :
      F p.1.2 = H (p.1.1,⟨p.1.2.1,hs⟩) := by
    rw [h0,h]
  cases i <;> cases j
  · rfl
  · exact hcross hi hj
  · exact (hcross hj hi).symm
  · rfl

def rimMap : C(Rim n,Y) :=
  ⟨Set.liftCover (face n) (fun i => faceValue F H i) (faceValue_compatible F H h) (face_cover n),
    continuous_finite_closed_paste _ _ _ _ (face_closed n)⟩
lemma rimMap_face (i : Bool) (p : face n i) : rimMap F H h p.1 = faceValue F H i p := by
  exact Set.liftCover_coe (S := face n) (f := fun i => faceValue F H i)
    (hf := faceValue_compatible F H h) (hS := face_cover n) p

def extension : C(unitInterval × Disk n,Y) := (rimMap F H h).comp (retract n)

lemma extension_zero (x : Disk n) : extension F H h (0,x) = F x := by
  let p : Rim n := ⟨(0,x),Or.inl rfl⟩
  have heq : retract n (0,x) = p := Subtype.ext (retract_of_rim p)
  change rimMap F H h (retract n (0,x)) = F x
  rw [heq]
  exact rimMap_face F H h false ⟨p,rfl⟩

lemma extension_boundary (t : unitInterval) (x : Sphere n) :
    extension F H h (t,⟨x.1,sphere_subset_closedBall x.2⟩) = H (t,x) := by
  let p : Rim n := ⟨(t,⟨x.1,sphere_subset_closedBall x.2⟩),Or.inr x.2⟩
  have heq : retract n p.1 = p := Subtype.ext (retract_of_rim p)
  change rimMap F H h (retract n p.1) = H (t,x)
  rw [heq]
  exact rimMap_face F H h true ⟨p,x.2⟩

end UniversalFInfinity.Cylinder

namespace UniversalFInfinity.DiskCube

def fromCube (n : ℕ) : C((Fin n → unitInterval),Disk n) := by
  refine ⟨fun x => ⟨fun i => 2*(x i:ℝ)-1,?_⟩,?_⟩
  · simp only [mem_closedBall,dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith [(x i).2.1,(x i).2.2]
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))).sub continuous_const

lemma from_to (n : ℕ) (x : Disk n) : fromCube n (toCube n x) = x := by
  apply Subtype.ext
  funext i
  change 2*((x.1 i+1)/2)-1 = x.1 i
  ring

lemma from_boundary (n : ℕ) (x : Fin n → unitInterval) (hx : x ∈ Cube.boundary (Fin n)) :
    (fromCube n x).1 ∈ sphere 0 1 := by
  obtain ⟨i,hi | hi⟩ := hx
  all_goals
    simp only [mem_sphere,dist_zero_right]
    apply le_antisymm
    · simpa only [mem_closedBall,dist_zero_right] using (fromCube n x).2
    · have h := norm_le_pi_norm (fromCube n x).1 i
      change ‖2*(x i:ℝ)-1‖ ≤ _ at h
      norm_num [hi] at h ⊢
      exact h

lemma to_boundary (n : ℕ) (x : Sphere n) :
    toCube n ⟨x.1,sphere_subset_closedBall x.2⟩ ∈ Cube.boundary (Fin n) := by
  have hx : ‖x.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using x.2
  have hi : ∃ i, 1 ≤ ‖x.1 i‖ := by
    by_contra! hh
    have := (pi_norm_lt_iff (by norm_num : (0:ℝ)<1)).mpr hh
    linarith
  obtain ⟨i,hi⟩ := hi
  have heq : |x.1 i| = 1 := le_antisymm ((norm_le_pi_norm x.1 i).trans_eq hx) hi
  refine ⟨i,?_⟩
  rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp heq with h | h
  · right
    apply Subtype.ext
    change (x.1 i+1)/2 = 1
    rw [h]; norm_num
  · left
    apply Subtype.ext
    change (x.1 i+1)/2 = 0
    rw [h]; norm_num

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

variable (f g : C(X,Y 0)) (hq : ∀ i,KillsSpheres (q i) (i+1))

def towerPartialHomotopy : ∀ i,PartialHomotopy (C := (Set.univ : Set X))
    (towerComposite Y q f i) (towerComposite Y q g i) i
  | 0 => PartialHomotopy.start f g
  | i+1 => (towerPartialHomotopy i).next (q i) (hq i)

def towerHomotopy (d : ℕ) (hd : Skeleton (Set.univ : Set X) d = Set.univ) :
    (towerComposite Y q f d).Homotopy (towerComposite Y q g d) :=
  (towerPartialHomotopy Y q f g hq d).toHomotopy hd

end UniversalFInfinity.Cellular

namespace UniversalFInfinity.Cellular
open Set Metric Topology
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
lemma KillsSpheres.post {q : C(X,Y)} {n : ℕ} (hq : KillsSpheres q n) (r : C(Y,Z)) :
    KillsSpheres (r.comp q) n := by
  intro a
  obtain ⟨d,hd⟩ := hq a
  exact ⟨r.comp d,fun x => congrArg r (hd x)⟩
lemma joined_of_killsSpheres_one (q : C(X,Y)) (hq : KillsSpheres q 1) (x y : X) :
    Joined (q x) (q y) := by
  classical
  let a : C(Sphere 1,X) := ⟨fun s => if s = Cayley.minus then x else y,continuous_of_discreteTopology⟩
  obtain ⟨d,hd⟩ := hq a
  have hm : a Cayley.minus = x := ite_eq_left rfl
  have hp : a Cayley.plus = y := by
    apply ite_eq_right
    intro h
    have := congrArg (fun z : Sphere 1 => z.1 0) h
    norm_num [Cayley.plus,Cayley.minus] at this
  have hh := (PathConnectedSpace.joined (boundary 1 Cayley.minus) (boundary 1 Cayley.plus)).map d.continuous
  rw [hd,hd,hm,hp] at hh
  exact hh
end UniversalFInfinity.Cellular
namespace UniversalFInfinity.Milnor

section
open Set Metric Topology Cellular UniversalFInfinity.Simplicial ConcreteEnvelopes
open scoped Topology.Homotopy
variable {G : Type} [Group G] [Group.IsFinitelyPresented G]
  [TopologicalSpace G] [DiscreteTopology G]

local instance (priority := 2000) instDecidableEqProdNat_solutions_14_r7f5f75_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
def Represents {S T : Shapes G} (f : G →* G) (q : C(Stage G S,Stage G T)) : Prop :=
  ∀ x, (q x).1 = x.1.mapDomain (vertexMap f id)

end
open Set Metric Topology Cellular UniversalFInfinity.Simplicial ConcreteEnvelopes
variable {G : Type} [Group G] [Group.IsFinitelyPresented G]
  [TopologicalSpace G] [DiscreteTopology G]

local instance (priority := 2000) instDecidableEqProdNat_solutions_15_r7f5f75_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
omit [Group.IsFinitelyPresented G] [TopologicalSpace G] [DiscreteTopology G] in
lemma Represents.id (S : Shapes G) : Represents (MonoidHom.id G) (ContinuousMap.id (Stage G S)) := by
  intro x
  change x.1 = x.1.mapDomain _root_.id
  exact (Finsupp.mapDomain_id).symm

end UniversalFInfinity.Milnor

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

lemma edge_zero (c : C) (x : B) : edge τ L R c 0 x = vertex τ L R c (L c x) := by simp [edge]
lemma edge_one (c : C) (x : B) : edge τ L R c 1 x = vertex τ L R (τ c) (R c x) := by simp [edge]

variable [TopologicalSpace C] [DiscreteTopology C]

omit [DiscreteTopology C] in
lemma continuous_quotient : Continuous (quotient τ L R) := continuous_coinduced_rng
omit [DiscreteTopology C] in
lemma continuous_vertex : Continuous (fun z : C × A => vertex τ L R z.1 z.2) :=
  (continuous_quotient τ L R).comp continuous_inl
omit [DiscreteTopology C] in
lemma continuous_edge : Continuous (fun z : C × (I × B) => edge τ L R z.1 z.2.1 z.2.2) :=
  (continuous_quotient τ L R).comp continuous_inr

def vertexMap (c : C) : C(A,Space τ L R) :=
  ⟨vertex τ L R c,(continuous_vertex τ L R).comp (continuous_const.prodMk continuous_id)⟩
def edgeMap (c : C) : C(I × B,Space τ L R) :=
  ⟨fun z => edge τ L R c z.1 z.2,(continuous_edge τ L R).comp (continuous_const.prodMk continuous_id)⟩

lemma continuous_iff {Y : Type z} [TopologicalSpace Y] (f : Space τ L R → Y) :
    Continuous f ↔ (∀ c,Continuous (fun x => f (vertex τ L R c x))) ∧
      ∀ c,Continuous (fun z : I × B => f (edge τ L R c z.1 z.2)) := by
  change Continuous[TopologicalSpace.coinduced (quotient τ L R) inferInstance,_] f ↔ _
  rw [continuous_coinduced_dom,continuous_sum_dom]
  exact and_congr continuous_prod_of_discrete_left continuous_prod_of_discrete_left

lemma isClosed_iff (S : Set (Space τ L R)) :
    IsClosed S ↔ (∀ c,IsClosed ((vertex τ L R c) ⁻¹' S)) ∧
      ∀ c,IsClosed ((fun z : I × B => edge τ L R c z.1 z.2) ⁻¹' S) := by
  change @IsClosed _ (TopologicalSpace.coinduced (quotient τ L R) inferInstance) S ↔ _
  rw [isClosed_coinduced,isClosed_sum_iff]
  constructor
  · rintro ⟨hv,he⟩
    exact ⟨fun c => hv.preimage (continuous_const.prodMk continuous_id),
      fun c => he.preimage (continuous_const.prodMk continuous_id)⟩
  · rintro ⟨hv,he⟩
    exact ⟨closed_of_slices hv,closed_of_slices he⟩

variable {Y : Type z} [TopologicalSpace Y]
variable (v : C → C(A,Y)) (e : C → C(I × B,Y))
variable (he0 : ∀ c x,e c (0,x) = v c (L c x))
variable (he1 : ∀ c x,e c (1,x) = v (τ c) (R c x))

def liftFun : Space τ L R → Y :=
  Sum.elim (fun z => v z.1 z.2) (fun z => e z.1 (⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩,z.2.2))
omit [TopologicalSpace C] [DiscreteTopology C] in
include he0 he1 in
lemma liftFun_edge (c : C) (t : I) (x : B) : liftFun τ L R v e (edge τ L R c t x) = e c (t,x) := by
  classical
  unfold edge
  split_ifs with h0 h1
  · subst t; exact (he0 c x).symm
  · subst t; exact (he1 c x).symm
  · rfl

def lift : C(Space τ L R,Y) :=
  ⟨liftFun τ L R v e,(continuous_iff τ L R _).mpr
    ⟨fun c => (v c).continuous,fun c => by
      have h : (fun z : I × B => liftFun τ L R v e (edge τ L R c z.1 z.2)) = e c := by
        funext z; exact liftFun_edge τ L R v e he0 he1 c z.1 z.2
      rw [h]; exact (e c).continuous⟩⟩
lemma lift_edge (c : C) (z : I × B) : lift τ L R v e he0 he1 (edge τ L R c z.1 z.2) = e c z :=
  liftFun_edge τ L R v e he0 he1 c z.1 z.2
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

namespace UniversalFInfinity.GraphBundle

open Set Topology
open scoped unitInterval
universe u v w z
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))
variable {Y : Type z} [TopologicalSpace Y]

variable (f g : C(Space τ L R,Y))
variable (V : ∀ c,(f.comp (vertexMap τ L R c)).Homotopy (g.comp (vertexMap τ L R c)))
variable (E : ∀ c,(f.comp (edgeMap τ L R c)).Homotopy (g.comp (edgeMap τ L R c)))
variable (hE0 : ∀ c t x,E c (t,(0,x)) = V c (t,L c x))
variable (hE1 : ∀ c t x,E c (t,(1,x)) = V (τ c) (t,R c x))

def homotopyPaths : C(Space τ L R,C(I,Y)) :=
  lift τ L R (fun c => ContinuousMap.curry ((V c).toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩))
    (fun c => ContinuousMap.curry ((E c).toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩)) (by
      intro c x; apply ContinuousMap.ext; intro t; exact hE0 c t x) (by
      intro c x; apply ContinuousMap.ext; intro t; exact hE1 c t x)

def homotopy : f.Homotopy g where
  toFun z := homotopyPaths τ L R f g V E hE0 hE1 z.2 z.1
  continuous_toFun := (homotopyPaths τ L R f g V E hE0 hE1).uncurry.continuous.comp continuous_swap
  map_zero_left z := by
    change Core (C := C) (A := A) (B := B) at z
    cases z with
    | inl z => exact (V z.1).apply_zero z.2
    | inr z =>
      have he := (E z.1).apply_zero (⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩,z.2.2)
      change E z.1 (0,(⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩,z.2.2)) = f (edge τ L R z.1 ⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩ z.2.2) at he
      rw [edge_inner] at he
      exact he
  map_one_left z := by
    change Core (C := C) (A := A) (B := B) at z
    cases z with
    | inl z => exact (V z.1).apply_one z.2
    | inr z =>
      have he := (E z.1).apply_one (⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩,z.2.2)
      change E z.1 (1,(⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩,z.2.2)) = g (edge τ L R z.1 ⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩ z.2.2) at he
      rw [edge_inner] at he
      exact he
end UniversalFInfinity.GraphBundle

namespace UniversalFInfinity.GraphBundle

section
open Set Topology
open scoped unitInterval
universe u v w
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))

def edgePath (c : C) (x : B) : Path (vertex τ L R c (L c x)) (vertex τ L R (τ c) (R c x)) where
  toFun t := edge τ L R c t x
  continuous_toFun := (edgeMap τ L R c).continuous.comp (continuous_id.prodMk continuous_const)
  source' := edge_zero τ L R c x
  target' := edge_one τ L R c x

omit [DiscreteTopology C] in
lemma edgePath_continuous (c : C) : Continuous (fun z : B × I => edgePath τ L R c z.1 z.2) :=
  (edgeMap τ L R c).continuous.comp continuous_swap

def pausedEdge (c : C) (x : B) := (edgePath τ L R c x).trans (Path.refl _)
omit [DiscreteTopology C] in
lemma pausedEdge_continuous (c : C) : Continuous (fun z : B × I => pausedEdge τ L R c z.1 z.2) :=
  Path.trans_continuous_family (edgePath τ L R c) (edgePath_continuous τ L R c)
    (fun x => Path.refl (vertex τ L R (τ c) (R c x)))
    ((vertexMap τ L R (τ c)).continuous.comp ((R c).continuous.comp continuous_fst))

def pause : C(Space τ L R,Space τ L R) :=
  lift τ L R (vertexMap τ L R)
    (fun c => ⟨fun z => pausedEdge τ L R c z.2 z.1,(pausedEdge_continuous τ L R c).comp continuous_swap⟩)
    (fun c x => (pausedEdge τ L R c x).source)
    (fun c x => (pausedEdge τ L R c x).target)
lemma pause_edge (c : C) (z : I × B) : pause τ L R (edge τ L R c z.1 z.2) = pausedEdge τ L R c z.2 z.1 :=
  lift_edge τ L R _ _ _ _ c z

def pauseVertexHomotopy (c : C) :
    ((pause τ L R).comp (vertexMap τ L R c)).Homotopy ((ContinuousMap.id _).comp (vertexMap τ L R c)) :=
  ContinuousMap.Homotopy.refl (vertexMap τ L R c)

omit [DiscreteTopology C] in
lemma pauseEdgeHomotopy_continuous (c : C) :
    Continuous (fun z : I × (I × B) =>
      Path.Homotopy.transRefl (edgePath τ L R c z.2.2) (z.1,z.2.1)) := by
  change Continuous (fun z : I × (I × B) =>
    edge τ L R c (PathFamilies.unpause (z.1,z.2.1)) z.2.2)
  exact (edgeMap τ L R c).continuous.comp
    ((PathFamilies.unpause.continuous.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
      continuous_snd.snd)

def pauseEdgeHomotopy (c : C) :
    ((pause τ L R).comp (edgeMap τ L R c)).Homotopy ((ContinuousMap.id _).comp (edgeMap τ L R c)) where
  toFun z := Path.Homotopy.transRefl (edgePath τ L R c z.2.2) (z.1,z.2.1)
  continuous_toFun := pauseEdgeHomotopy_continuous τ L R c
  map_zero_left z := by
    change Path.Homotopy.transRefl (edgePath τ L R c z.2) (0,z.1) = pause τ L R (edge τ L R c z.1 z.2)
    rw [pause_edge]
    exact (Path.Homotopy.transRefl (edgePath τ L R c z.2)).apply_zero z.1
  map_one_left z := (Path.Homotopy.transRefl (edgePath τ L R c z.2)).apply_one z.1

def pauseHomotopy : (pause τ L R).Homotopy (ContinuousMap.id _) :=
  homotopy τ L R (pause τ L R) (ContinuousMap.id _) (pauseVertexHomotopy τ L R)
    (pauseEdgeHomotopy τ L R) (fun c t x => (Path.Homotopy.transRefl (edgePath τ L R c x)).source t)
    (fun c t x => (Path.Homotopy.transRefl (edgePath τ L R c x)).target t)
end

section
open Set Topology
open scoped unitInterval
universe u v w z
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {D : Type v} [TopologicalSpace D] [DiscreteTopology D]
variable {A : Type w} [TopologicalSpace A] {B : Type z} [TopologicalSpace B]
variable (τ : C → C) (F : C → C(A,A)) (ν : D → D) (K : D → C(B,B))
variable (sig : C → D) (hsig : ∀ c,sig (τ c) = ν (sig c)) (a : C → C(A,B))
variable (ha : ∀ c x,a (τ c) (F c x) = K (sig c) (a c x))

def homogeneousMap : C(Space τ (fun _ => .id A) F,Space ν (fun _ => .id B) K) :=
  lift τ (fun _ => .id A) F
    (fun c => (vertexMap ν (fun _ => .id B) K (sig c)).comp (a c))
    (fun c => (edgeMap ν (fun _ => .id B) K (sig c)).comp
      ⟨fun z => (z.1,a c z.2), continuous_fst.prodMk ((a c).continuous.comp continuous_snd)⟩)
    (fun c x => edge_zero ν _ K (sig c) (a c x))
    (fun c x => by change edge ν _ K (sig c) 1 (a c x) = vertex ν _ K (sig (τ c)) (a (τ c) (F c x)); rw [edge_one,hsig,ha])
omit [DiscreteTopology D] in
lemma homogeneousMap_edge (c : C) (t : I) (x : A) :
    homogeneousMap τ F ν K sig hsig a ha (edge τ (fun _ => .id A) F c t x) =
      edge ν (fun _ => .id B) K (sig c) t (a c x) := lift_edge τ _ F _ _ _ _ c (t,x)
end

open Set Topology
open scoped unitInterval
universe u v w
variable {G : Type u} [Group G]
variable {C : Type v} [TopologicalSpace C] [DiscreteTopology C] [MulAction G C]
variable {A : Type w} [TopologicalSpace A]
variable (τ : C → C) (F : C → C(A,A)) (hτ : ∀ (g : G) c,τ (g • c) = g • τ c)
variable (a : G → C → C(A,A))
variable (ha : ∀ (g : G) c x,a g (τ c) (F c x) = F (g • c) (a g c x))
variable (a_one : ∀ c x,a 1 c x = x)
variable (a_mul : ∀ (g h : G) c x,a (g*h) c x = a g (h • c) (a h c x))

def actionMap (g : G) : C(Space τ (fun _ => .id A) F,Space τ (fun _ => .id A) F) :=
  homogeneousMap τ F τ F (g • ·) (fun c => (hτ g c).symm) (a g) (ha g)
lemma actionMap_vertex (g : G) (c : C) (x : A) :
    actionMap τ F hτ a ha g (vertex τ (fun _ => .id A) F c x) =
      vertex τ (fun _ => .id A) F (g • c) (a g c x) := rfl
lemma actionMap_edge (g : G) (c : C) (t : I) (x : A) :
    actionMap τ F hτ a ha g (edge τ (fun _ => .id A) F c t x) =
      edge τ (fun _ => .id A) F (g • c) t (a g c x) :=
  homogeneousMap_edge τ F τ F _ _ _ _ c t x

@[instance_reducible]
def graphAction : MulAction G (Space τ (fun _ => .id A) F) where
  smul g x := actionMap τ F hτ a ha g x
  one_smul x := by
    have he : actionMap τ F hτ a ha 1 = ContinuousMap.id _ := by
      apply hom_ext τ (fun _ => .id A) F
      · intro c y; rw [actionMap_vertex,one_smul,a_one]; rfl
      · intro c z; rw [actionMap_edge,one_smul,a_one]; rfl
    exact ContinuousMap.congr_fun he x
  mul_smul g h x := by
    have he : actionMap τ F hτ a ha (g*h) = (actionMap τ F hτ a ha g).comp (actionMap τ F hτ a ha h) := by
      apply hom_ext τ (fun _ => .id A) F
      · intro c y; simp only [ContinuousMap.comp_apply,actionMap_vertex,mul_smul,a_mul]
      · intro c z; simp only [ContinuousMap.comp_apply,actionMap_edge,mul_smul,a_mul]
    exact ContinuousMap.congr_fun he x

end UniversalFInfinity.GraphBundle

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

namespace UniversalFInfinity.GraphBundle

section
open Set Topology
open scoped unitInterval
universe u v w z r
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable {A' : Type z} [TopologicalSpace A'] {B' : Type r} [TopologicalSpace B']
variable (τ : C → C) (L R : C → C(B,A)) (L' R' : C → C(B',A'))
variable (i : C(A,A')) (j : C(B,B'))
variable (hL : ∀ c x,i (L c x) = L' c (j x)) (hR : ∀ c x,i (R c x) = R' c (j x))

def inclusionFun : Space τ L R → Space τ L' R' :=
  Sum.map (Prod.map id i) (Prod.map id (Prod.map id j))
omit [TopologicalSpace C] [DiscreteTopology C] in
lemma inclusionFun_vertex (c : C) (x : A) :
    inclusionFun τ L R L' R' i j (vertex τ L R c x) = vertex τ L' R' c (i x) := rfl
include hL hR in
omit [TopologicalSpace C] [DiscreteTopology C] in
lemma inclusionFun_edge (c : C) (t : I) (x : B) :
    inclusionFun τ L R L' R' i j (edge τ L R c t x) = edge τ L' R' c t (j x) := by
  classical
  by_cases h0 : t = 0
  · subst t; rw [edge_zero,edge_zero,inclusionFun_vertex,hL]
  by_cases h1 : t = 1
  · subst t; rw [edge_one,edge_one,inclusionFun_vertex,hR]
  let s : Inner := ⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
    lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩
  change inclusionFun τ L R L' R' i j (edge τ L R c ⟨s.1,s.2.1.le,s.2.2.le⟩ x) =
    edge τ L' R' c ⟨s.1,s.2.1.le,s.2.2.le⟩ (j x)
  rw [edge_inner,edge_inner]; rfl

def inclusion : C(Space τ L R,Space τ L' R') :=
  ⟨inclusionFun τ L R L' R' i j,(continuous_iff τ L R _).mpr ⟨fun c =>
    (vertexMap τ L' R' c).continuous.comp i.continuous,fun c => by
      have he : (fun p : I × B => inclusionFun τ L R L' R' i j (edge τ L R c p.1 p.2)) =
          (fun p : I × B => edge τ L' R' c p.1 (j p.2)) := funext (fun p => inclusionFun_edge τ L R L' R' i j hL hR c p.1 p.2)
      rw [he]
      exact (edgeMap τ L' R' c).continuous.comp (continuous_fst.prodMk (j.continuous.comp continuous_snd))⟩⟩
lemma inclusion_edge (c : C) (t : I) (x : B) :
    inclusion τ L R L' R' i j hL hR (edge τ L R c t x) = edge τ L' R' c t (j x) :=
  inclusionFun_edge τ L R L' R' i j hL hR c t x

lemma inclusion_injective (hi : Function.Injective i) (hj : Function.Injective j) :
    Function.Injective (inclusion τ L R L' R' i j hL hR) :=
  Sum.map_injective.mpr ⟨Function.injective_id.prodMap hi,Function.injective_id.prodMap (Function.injective_id.prodMap hj)⟩

lemma inclusion_vertex_preimage (S : Set (Space τ L R)) (c : C) :
    (vertex τ L' R' c) ⁻¹' (inclusion τ L R L' R' i j hL hR '' S) =
      i '' ((vertex τ L R c) ⁻¹' S) := by
  ext x
  constructor
  · rintro ⟨a,ha,he⟩
    change Core (C := C) (A := A) (B := B) at a
    cases a with
    | inl a =>
      have hh : (a.1,i a.2) = (c,x) := Sum.inl.inj he
      obtain rfl := congrArg Prod.fst hh
      exact ⟨a.2,ha,congrArg Prod.snd hh⟩
    | inr a => cases he
  · rintro ⟨y,hy,rfl⟩; exact ⟨vertex τ L R c y,hy,rfl⟩

lemma inclusion_edge_preimage (S : Set (Space τ L R)) (c : C) :
    (fun p : I × B' => edge τ L' R' c p.1 p.2) ⁻¹' (inclusion τ L R L' R' i j hL hR '' S) =
      ({0} ×ˢ ((L' c) ⁻¹' (i '' ((vertex τ L R c) ⁻¹' S)))) ∪
      ({1} ×ˢ ((R' c) ⁻¹' (i '' ((vertex τ L R (τ c)) ⁻¹' S)))) ∪
      (Prod.map id j '' ((fun p : I × B => edge τ L R c p.1 p.2) ⁻¹' S)) := by
  classical
  ext ⟨t,x⟩
  constructor
  · intro h
    by_cases h0 : t = 0
    · subst t; apply Or.inl; apply Or.inl; refine ⟨rfl,?_⟩
      rw [Set.mem_preimage,edge_zero] at h
      exact (Set.ext_iff.mp (inclusion_vertex_preimage τ L R L' R' i j hL hR S c) _).mp h
    by_cases h1 : t = 1
    · subst t; apply Or.inl; apply Or.inr; refine ⟨rfl,?_⟩
      rw [Set.mem_preimage,edge_one] at h
      exact (Set.ext_iff.mp (inclusion_vertex_preimage τ L R L' R' i j hL hR S (τ c)) _).mp h
    let s : Inner := ⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
      lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩
    change edge τ L' R' c ⟨s.1,s.2.1.le,s.2.2.le⟩ x ∈ inclusion τ L R L' R' i j hL hR '' S at h
    rw [edge_inner] at h
    obtain ⟨a,ha,he⟩ := h
    change Core (C := C) (A := A) (B := B) at a
    cases a with
    | inl a => cases he
    | inr a =>
      have hh : (a.1,(a.2.1,j a.2.2)) = (c,(s,x)) := Sum.inr.inj he
      have hc : a.1 = c := congrArg Prod.fst hh
      have ht : a.2.1 = s := congrArg (fun p : C × (Inner × B') => p.2.1) hh
      have hx : j a.2.2 = x := congrArg (fun p : C × (Inner × B') => p.2.2) hh
      apply Or.inr
      refine ⟨(t,a.2.2),?_,Prod.ext rfl hx⟩
      change edge τ L R c ⟨s.1,s.2.1.le,s.2.2.le⟩ a.2.2 ∈ S
      rw [edge_inner,←hc,←ht]
      exact ha
  · rintro (h|h)
    · rcases h with h|h
      · have ht : t = 0 := h.1; subst t
        rw [Set.mem_preimage,edge_zero]
        exact (Set.ext_iff.mp (inclusion_vertex_preimage τ L R L' R' i j hL hR S c) _).mpr h.2
      · have ht : t = 1 := h.1; subst t
        rw [Set.mem_preimage,edge_one]
        exact (Set.ext_iff.mp (inclusion_vertex_preimage τ L R L' R' i j hL hR S (τ c)) _).mpr h.2
    · obtain ⟨⟨r,y⟩,hy,he⟩ := h
      have ht : r = t := congrArg Prod.fst he
      have hx : j y = x := congrArg Prod.snd he
      subst t; subst x
      exact ⟨edge τ L R c r y,hy,inclusion_edge τ L R L' R' i j hL hR c r y⟩

lemma inclusion_closedEmbedding (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j) :
    IsClosedEmbedding (inclusion τ L R L' R' i j hL hR) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap (inclusion τ L R L' R' i j hL hR).continuous
    (inclusion_injective τ L R L' R' i j hL hR hi.injective hj.injective)
  intro S hS
  obtain ⟨hv,he⟩ := (isClosed_iff τ L R S).mp hS
  apply (isClosed_iff τ L' R' _).mpr
  constructor
  · intro c; rw [inclusion_vertex_preimage]; exact hi.isClosedMap _ (hv c)
  · intro c; rw [inclusion_edge_preimage]
    exact ((isClosed_singleton.prod ((hi.isClosedMap _ (hv c)).preimage (L' c).continuous)).union
      (isClosed_singleton.prod ((hi.isClosedMap _ (hv (τ c))).preimage (R' c).continuous))).union
      ((IsClosedEmbedding.prodMap IsClosedEmbedding.id hj).isClosedMap _ (he c))
end

open Set Topology
open scoped unitInterval
universe u v w
end UniversalFInfinity.GraphBundle

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

namespace UniversalFInfinity.PathFamilies
open scoped unitInterval
universe u v
variable {Y : Type u} [TopologicalSpace Y] {X : Type v} [TopologicalSpace X]
variable {x y z : Y}

def diagonalSquare (p : Path x y) (q : Path y z) : C(I × I,Y) :=
  ⟨fun s => (p.trans q).extend (((s.1:ℝ)+(s.2:ℝ))/2),
    (p.trans q).continuous_extend.comp (by fun_prop)⟩

lemma diagonalSquare_zero_left (p : Path x y) (q : Path y z) (s : I) :
    diagonalSquare p q (0,s) = p s := by
  change (p.trans q).extend (((0:ℝ)+(s:ℝ))/2) = p s
  rw [Path.extend_trans_of_le_half p q (by have := s.2.2; linarith)]
  rw [show 2*(((0:ℝ)+(s:ℝ))/2) = (s:ℝ) by ring]
  exact p.extend_apply s.2
lemma diagonalSquare_one_left (p : Path x y) (q : Path y z) (s : I) :
    diagonalSquare p q (1,s) = q s := by
  change (p.trans q).extend (((1:ℝ)+(s:ℝ))/2) = q s
  rw [Path.extend_trans_of_half_le p q (by have := s.2.1; linarith)]
  rw [show 2*(((1:ℝ)+(s:ℝ))/2)-1 = (s:ℝ) by ring]
  exact q.extend_apply s.2
lemma diagonalSquare_symm (p : Path x y) (q : Path y z) (t s : I) :
    diagonalSquare p q (t,s) = diagonalSquare p q (s,t) := by
  change (p.trans q).extend _ = (p.trans q).extend _
  rw [add_comm (t:ℝ) (s:ℝ)]
lemma diagonalSquare_zero_right (p : Path x y) (q : Path y z) (t : I) :
    diagonalSquare p q (t,0) = p t := by
  rw [diagonalSquare_symm,diagonalSquare_zero_left]
lemma diagonalSquare_one_right (p : Path x y) (q : Path y z) (t : I) :
    diagonalSquare p q (t,1) = q t := by
  rw [diagonalSquare_symm,diagonalSquare_one_left]

lemma diagonalSquare_continuous {a b c : X → Y}
    (p : ∀ x,Path (a x) (b x)) (q : ∀ x,Path (b x) (c x))
    (hp : Continuous (fun z : X × I => p z.1 z.2))
    (hq : Continuous (fun z : X × I => q z.1 z.2)) :
    Continuous (fun z : X × (I × I) => diagonalSquare (p z.1) (q z.1) z.2) := by
  exact (Path.continuous_uncurry_extend_of_continuous_family
    (fun x => (p x).trans (q x)) (Path.trans_continuous_family p hp q hq)).comp
      (continuous_fst.prodMk (by fun_prop))
lemma diagonalSquare_continuous_params {a b c : X → Y}
    (p : ∀ x,Path (a x) (b x)) (q : ∀ x,Path (b x) (c x))
    (hp : Continuous (fun z : X × I => p z.1 z.2))
    (hq : Continuous (fun z : X × I => q z.1 z.2)) :
    Continuous (fun z : I × (I × X) => diagonalSquare (p z.2.2) (q z.2.2) (z.1,z.2.1)) := by
  have hc : Continuous (fun z : I × (I × X) => (z.2.2,(z.1,z.2.1))) :=
    continuous_snd.snd.prodMk (continuous_fst.prodMk continuous_snd.fst)
  exact (diagonalSquare_continuous p q hp hq).comp hc
end UniversalFInfinity.PathFamilies

namespace UniversalFInfinity.GraphBundle

section
open Set Topology
open scoped unitInterval
universe u v
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A]
variable (τ : C → C) (F : C → C(A,A))

abbrev Homogeneous := Space τ (fun _ => ContinuousMap.id A) F

def shift : C(Homogeneous τ F,Homogeneous τ F) :=
  lift τ (fun _ => .id A) F
    (fun c => (vertexMap τ (fun _ => .id A) F (τ c)).comp (F c))
    (fun c => (edgeMap τ (fun _ => .id A) F (τ c)).comp
      ⟨fun z => (z.1,F c z.2),continuous_fst.prodMk ((F c).continuous.comp continuous_snd)⟩)
    (fun c x => edge_zero τ _ F (τ c) (F c x))
    (fun c x => edge_one τ _ F (τ c) (F c x))
lemma shift_edge (c : C) (t : I) (x : A) :
    shift τ F (edge τ (fun _ => .id A) F c t x) = edge τ (fun _ => .id A) F (τ c) t (F c x) :=
  lift_edge τ _ F _ _ _ _ c (t,x)

def shiftVertexHomotopy (c : C) :
    ((ContinuousMap.id _).comp (vertexMap τ (fun _ => .id A) F c)).Homotopy
      ((shift τ F).comp (vertexMap τ (fun _ => .id A) F c)) where
  toFun z := edge τ (fun _ => .id A) F c z.1 z.2
  continuous_toFun := (edgeMap τ (fun _ => .id A) F c).continuous
  map_zero_left x := edge_zero τ _ F c x
  map_one_left x := edge_one τ _ F c x

omit [DiscreteTopology C] in
lemma shiftEdge_continuous (c : C) :
    Continuous (fun z : I × (I × A) =>
      PathFamilies.diagonalSquare (edgePath τ (fun _ => .id A) F c z.2.2)
        (edgePath τ (fun _ => .id A) F (τ c) (F c z.2.2)) (z.1,z.2.1)) := by
  let p : ∀ x : A, Path (vertex τ (fun _ => .id A) F c x)
      (vertex τ (fun _ => .id A) F (τ c) (F c x)) := edgePath τ (fun _ => .id A) F c
  let q : ∀ x : A, Path (vertex τ (fun _ => .id A) F (τ c) (F c x))
      (vertex τ (fun _ => .id A) F (τ (τ c)) (F (τ c) (F c x))) :=
    fun x => edgePath τ (fun _ => .id A) F (τ c) (F c x)
  have hp : Continuous (fun z : A × I => p z.1 z.2) :=
    (edgeMap τ (fun _ => .id A) F c).continuous.comp continuous_swap
  have hq : Continuous (fun z : A × I => q z.1 z.2) :=
    (edgeMap τ (fun _ => .id A) F (τ c)).continuous.comp
      (continuous_snd.prodMk ((F c).continuous.comp continuous_fst))
  exact PathFamilies.diagonalSquare_continuous_params p q hp hq

def shiftEdgeHomotopy (c : C) :
    ((ContinuousMap.id _).comp (edgeMap τ (fun _ => .id A) F c)).Homotopy
      ((shift τ F).comp (edgeMap τ (fun _ => .id A) F c)) where
  toFun z := PathFamilies.diagonalSquare (edgePath τ (fun _ => .id A) F c z.2.2)
    (edgePath τ (fun _ => .id A) F (τ c) (F c z.2.2)) (z.1,z.2.1)
  continuous_toFun := shiftEdge_continuous τ F c
  map_zero_left z := PathFamilies.diagonalSquare_zero_left _ _ z.1
  map_one_left z := (PathFamilies.diagonalSquare_one_left _ _ z.1).trans (shift_edge τ F c z.1 z.2).symm

def shiftHomotopy : (ContinuousMap.id (Homogeneous τ F)).Homotopy (shift τ F) :=
  homotopy τ (fun _ => .id A) F _ _ (shiftVertexHomotopy τ F) (shiftEdgeHomotopy τ F)
    (fun _ t _ => PathFamilies.diagonalSquare_zero_right _ _ t)
    (fun _ t _ => PathFamilies.diagonalSquare_one_right _ _ t)

def shiftIterate : ℕ → C(Homogeneous τ F,Homogeneous τ F)
  | 0 => .id _
  | n+1 => (shift τ F).comp (shiftIterate n)
def shiftIterateHomotopy : ∀ n,(ContinuousMap.id _).Homotopy (shiftIterate τ F n)
  | 0 => .refl _
  | n+1 => (shiftIterateHomotopy n).trans ((shiftHomotopy τ F).compContinuousMap (shiftIterate τ F n))
end

open Set Topology
open scoped unitInterval
universe u v
end UniversalFInfinity.GraphBundle

namespace UniversalFInfinity.DirectedGraph
open Set Metric Topology Attachment
open scoped unitInterval
universe u v
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C] (τ : C → C)

def attaching (c : C) : C(Sphere 1,C) :=
  ⟨fun x => if x.1 0 = -1 then c else τ c,continuous_of_discreteTopology⟩
abbrev Graph := Space (attaching τ)
def vertex (c : C) : Graph τ := base _ c

instance instT2SpaceGraph : T2Space (Graph τ) := t2Space _ (realSeparated_of_tychonoff (Y := C))

omit [DiscreteTopology C] in
lemma cell_minus (c : C) : cell (attaching τ) c (boundary 1 Cayley.minus) = vertex τ c := by
  rw [cell_boundary]; simp only [attaching,Cayley.minus,ContinuousMap.coe_mk,ite_true]; rfl
omit [DiscreteTopology C] in
lemma cell_plus (c : C) : cell (attaching τ) c (boundary 1 Cayley.plus) = vertex τ (τ c) := by
  rw [cell_boundary]; norm_num [attaching,Cayley.plus,vertex]

def edge (c : C) : Path (vertex τ c) (vertex τ (τ c)) where
  toFun t := cell (attaching τ) c (Cayley.edgeParam t)
  continuous_toFun := (cell _ c).continuous.comp Cayley.continuous_edgeParam
  source' := by rw [Cayley.edgeParam_zero,cell_minus]
  target' := by rw [Cayley.edgeParam_one,cell_plus]

variable {Y : Type v} [TopologicalSpace Y] (f : C(Graph τ,Y)) (y : Y)
variable (p : ∀ c,Path y (f (vertex τ c)))
variable (hp : ∀ c,((p c).trans ((edge τ c).map f.continuous)).Homotopic (p (τ c)))

def edgeSquare (c : C) : ((edge τ c).map f.continuous).toContinuousMap.Homotopy (.const _ y) :=
  (PathSquares.edgeSquare (p c) (p (τ c)) ((edge τ c).map f.continuous) (hp c)).choose
omit [DiscreteTopology C] in
lemma edgeSquare_source (c : C) (t : I) : edgeSquare τ f y p hp c (t,0) = PathSquares.pauseReverse (p c) t :=
  (PathSquares.edgeSquare (p c) (p (τ c)) ((edge τ c).map f.continuous) (hp c)).choose_spec.1 t
omit [DiscreteTopology C] in
lemma edgeSquare_target (c : C) (t : I) : edgeSquare τ f y p hp c (t,1) = PathSquares.pauseReverse (p (τ c)) t :=
  (PathSquares.edgeSquare (p c) (p (τ c)) ((edge τ c).map f.continuous) (hp c)).choose_spec.2 t

def edgePaths (c : C) : C(Disk 1,C(I,Y)) :=
  ContinuousMap.curry ⟨fun z => edgeSquare τ f y p hp c (z.2,Cayley.edgeTime z.1),
    (edgeSquare τ f y p hp c).continuous.comp
      (continuous_snd.prodMk (Cayley.continuous_edgeTime.comp continuous_fst))⟩
def vertexPaths : C(C,C(I,Y)) := ⟨fun c => PathSquares.pauseReverse (p c),continuous_of_discreteTopology⟩
lemma edgePaths_boundary (c : C) (t : Sphere 1) :
    edgePaths τ f y p hp c (boundary 1 t) = vertexPaths τ f y p (attaching τ c t) := by
  obtain rfl|rfl := Cayley.sphere_one_eq t
  · apply ContinuousMap.ext; intro z
    change edgeSquare τ f y p hp c (z,Cayley.edgeTime (boundary 1 Cayley.minus)) = _
    rw [Cayley.edgeTime_minus,edgeSquare_source]
    simp only [vertexPaths,attaching,ContinuousMap.coe_mk,Cayley.minus,ite_true]
  · apply ContinuousMap.ext; intro z
    change edgeSquare τ f y p hp c (z,Cayley.edgeTime (boundary 1 Cayley.plus)) = _
    rw [Cayley.edgeTime_plus,edgeSquare_target]
    norm_num [vertexPaths,attaching,Cayley.plus]

def graphPaths : C(Graph τ,C(I,Y)) :=
  lift _ (vertexPaths τ f y p) (edgePaths τ f y p hp) (edgePaths_boundary τ f y p hp)
lemma graphPaths_zero (z : Graph τ) : graphPaths τ f y p hp z 0 = f z := by
  cases z with
  | inl c => exact Path.source _
  | inr z =>
    change edgeSquare τ f y p hp z.1 (0,Cayley.edgeTime (interior 1 z.2)) = _
    rw [ContinuousMap.Homotopy.apply_zero]
    change f (cell _ z.1 (Cayley.edgeParam (Cayley.edgeTime (interior 1 z.2)))) = f _
    rw [Cayley.edgeParam_time,cell_interior]
lemma graphPaths_one (z : Graph τ) : graphPaths τ f y p hp z 1 = y := by
  cases z with
  | inl c => exact Path.target _
  | inr z =>
    change edgeSquare τ f y p hp z.1 (1,Cayley.edgeTime (interior 1 z.2)) = y
    exact ContinuousMap.Homotopy.apply_one _ _

def graphNullhomotopy : f.Homotopy (.const _ y) where
  toFun z := graphPaths τ f y p hp z.2 z.1
  continuous_toFun := (graphPaths τ f y p hp).uncurry.continuous.comp continuous_swap
  map_zero_left := graphPaths_zero τ f y p hp
  map_one_left := graphPaths_one τ f y p hp

end UniversalFInfinity.DirectedGraph

namespace UniversalFInfinity.DirectedTree
universe u v
variable {C : Type u} {G : Type v} [Group G]
variable (τ : C → C) (h : C → ℤ) (hτ : ∀ c, h (τ c) = h c + 1)

variable (w : C → G)
def rayProduct (c : C) : ℕ → G
  | 0 => 1
  | n+1 => rayProduct c n * w (τ^[n] c)

variable (hc : ∀ c d, ∃ p q : ℕ, τ^[p] c = τ^[q] d) (root : C)
def potential (c : C) : G :=
  let p := (hc root c).choose
  let q := (hc root c).choose_spec.choose
  rayProduct τ w root p * (rayProduct τ w c q)⁻¹

end UniversalFInfinity.DirectedTree

namespace UniversalFInfinity.DirectedGraph
open Set Topology Attachment
open scoped unitInterval
universe u
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C] (τ : C → C)
variable (h : C → ℤ) (hτ : ∀ c, h (τ c) = h c + 1)
variable (hc : ∀ c d, ∃ p q : ℕ, τ^[p] c = τ^[q] d) (root : C)

omit [DiscreteTopology C] in
lemma ray_joined (c : C) (n : ℕ) : Joined (vertex τ c) (vertex τ (τ^[n] c)) := by
  induction n with
  | zero => exact Joined.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans ⟨edge τ (τ^[n] c)⟩

include hc in
omit [DiscreteTopology C] in
lemma vertex_joined (c : C) : Joined (vertex τ root) (vertex τ c) := by
  obtain ⟨p,q,he⟩ := hc root c
  have hd : Joined (vertex τ c) (vertex τ (τ^[p] root)) := by
    rw [he]; exact ray_joined τ c q
  exact (ray_joined τ root p).trans hd.symm

def initialPath (c : C) : Path (vertex τ root) (vertex τ c) :=
  (vertex_joined τ hc root c).somePath

def initialClass (c : C) : Path.Homotopic.Quotient (vertex τ root) (vertex τ c) :=
  Path.Homotopic.Quotient.mk (initialPath τ hc root c)

def edgeClass (c : C) : Path.Homotopic.Quotient (vertex τ c) (vertex τ (τ c)) :=
  Path.Homotopic.Quotient.mk (edge τ c)

def edgeWeight (c : C) : (FundamentalGroup (Graph τ) (vertex τ root))ᵐᵒᵖ :=
  MulOpposite.op (((initialClass τ hc root c).trans (edgeClass τ c)).trans
    (initialClass τ hc root (τ c)).symm)

def treeClass (c : C) : Path.Homotopic.Quotient (vertex τ root) (vertex τ c) :=
  (MulOpposite.unop (DirectedTree.potential τ (edgeWeight τ hc root) hc root c)).trans
    (initialClass τ hc root c)

def treePath (c : C) : Path (vertex τ root) (vertex τ c) :=
  (Path.Homotopic.Quotient.mk_surjective (treeClass τ hc root c)).choose

end UniversalFInfinity.DirectedGraph

namespace UniversalFInfinity.GraphBundle

section
open Set Topology
open scoped unitInterval
universe u v w z
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))
variable {Y : Type z} [TopologicalSpace Y]

def treeProjection : C(Space τ L R,DirectedGraph.Graph τ) :=
  lift τ L R (fun c => .const _ (DirectedGraph.vertex τ c))
    (fun c => (DirectedGraph.edge τ c).toContinuousMap.comp (.fst))
    (fun c _ => (DirectedGraph.edge τ c).source)
    (fun c _ => (DirectedGraph.edge τ c).target)

omit [DiscreteTopology C] in
lemma pathMap_boundary (y : C → Y) (p : ∀ c,Path (y c) (y (τ c))) (c : C)
    (x : Attachment.Sphere 1) :
    p c (Cayley.edgeTime (Attachment.boundary 1 x)) = y (DirectedGraph.attaching τ c x) := by
  obtain rfl|rfl := Cayley.sphere_one_eq x
  · rw [Cayley.edgeTime_minus,Path.source]
    simp only [DirectedGraph.attaching,Cayley.minus,ContinuousMap.coe_mk,ite_true]
  · rw [Cayley.edgeTime_plus,Path.target]
    norm_num [DirectedGraph.attaching,Cayley.plus]

def treePathMap (y : C → Y) (p : ∀ c,Path (y c) (y (τ c))) : C(DirectedGraph.Graph τ,Y) :=
  Attachment.lift _ ⟨y,continuous_of_discreteTopology⟩
    (fun c => (p c).toContinuousMap.comp ⟨Cayley.edgeTime,Cayley.continuous_edgeTime⟩)
    (pathMap_boundary τ y p)
end

open Set Topology
open scoped unitInterval
universe u v w z r
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))
variable {Y : Type z} [TopologicalSpace Y] {Z : Type r} [TopologicalSpace Z]
variable (f : C(Space τ L R,Y)) (y : C → Y)
variable (V : ∀ c,(f.comp (vertexMap τ L R c)).Homotopy (.const _ (y c)))
variable (a b : C → C(Z,Y)) (e : ∀ c z,Path (a c z) (b c z))
variable (he : ∀ c,Continuous (fun p : Z × I => e c p.1 p.2))
variable (H : C → C(I × B,Z))
variable (Q : C → C(B,C(I,C(I,Y))))
variable (hleft : ∀ c t x,a c (H c (t,x)) = V c (t,L c x))
variable (qleft : ∀ c x t,Q c x t 0 = b c (H c (t,x)))
variable (qright : ∀ c x t,Q c x t 1 = V (τ c) (t,R c x))

def connectorPath (c : C) (p : I × B) :
    Path (b c (H c p)) (V (τ c) (p.1,R c p.2)) where
  toFun s := Q c p.2 p.1 s
  continuous_toFun := (Q c p.2 p.1).continuous
  source' := qleft c p.2 p.1
  target' := qright c p.2 p.1

omit [DiscreteTopology C] in
lemma connectorPath_continuous (c : C) : Continuous (fun p : (I × B) × I =>
    connectorPath τ L R f y V b H Q qleft qright c p.1 p.2) := by
  change Continuous (fun p : (I × B) × I => Q c p.1.2 p.1.1 p.2)
  exact (Q c).uncurry.uncurry.continuous.comp
    ((continuous_fst.snd.prodMk continuous_fst.fst).prodMk continuous_snd)

def gluedPath (c : C) (p : I × B) : Path (a c (H c p)) (V (τ c) (p.1,R c p.2)) :=
  (e c (H c p)).trans (connectorPath τ L R f y V b H Q qleft qright c p)

include he in
omit [DiscreteTopology C] in
lemma gluedPath_continuous (c : C) : Continuous (fun p : (I × B) × I =>
    gluedPath τ L R f y V a b e H Q qleft qright c p.1 p.2) := by
  exact Path.trans_continuous_family (fun z : I × B => e c (H c z))
    ((he c).comp (((H c).continuous.comp continuous_fst).prodMk continuous_snd))
    (connectorPath τ L R f y V b H Q qleft qright c)
    (connectorPath_continuous τ L R f y V b H Q qleft qright c)

variable (e0 : ∀ c x s,e c (H c (0,x)) s = f (edge τ L R c s x))
variable (q0 : ∀ c x s,Q c x 0 s = f (vertex τ L R (τ c) (R c x)))
variable (p : ∀ c,Path (y c) (y (τ c)))
variable (e1 : ∀ c x s,gluedPath τ L R f y V a b e H Q qleft qright c (1,x) s = p c s)

include e0 q0 in
lemma gluedPath_zero (c : C) (x : B) (s : I) :
    gluedPath τ L R f y V a b e H Q qleft qright c (0,x) s =
      f (pause τ L R (edge τ L R c s x)) := by
  rw [pause_edge τ L R c (s,x)]
  change ((e c (H c (0,x))).trans (connectorPath τ L R f y V b H Q qleft qright c (0,x))) s =
    f ((edgePath τ L R c x).trans (Path.refl _) s)
  rw [Path.trans_apply,Path.trans_apply]
  split_ifs with hs
  · exact e0 c x _
  · exact q0 c x _

def collapsed : C(Space τ L R,Y) :=
  lift τ L R (fun c => .const _ (y c))
    (fun c => (p c).toContinuousMap.comp .fst)
    (fun c _ => (p c).source) (fun c _ => (p c).target)

lemma collapsed_edge (c : C) (s : I) (x : B) :
    collapsed τ L R y p (edge τ L R c s x) = p c s :=
  lift_edge τ L R _ _ _ _ c (s,x)

def gluedEdgeHomotopy (c : C) :
    ((f.comp (pause τ L R)).comp (edgeMap τ L R c)).Homotopy
      ((collapsed τ L R y p).comp (edgeMap τ L R c)) where
  toFun z := gluedPath τ L R f y V a b e H Q qleft qright c (z.1,z.2.2) z.2.1
  continuous_toFun := (gluedPath_continuous τ L R f y V a b e he H Q qleft qright c).comp
    ((continuous_fst.prodMk continuous_snd.snd).prodMk continuous_snd.fst)
  map_zero_left z := gluedPath_zero τ L R f y V a b e H Q qleft qright e0 q0 c z.2 z.1
  map_one_left z := (e1 c z.2 z.1).trans (collapsed_edge τ L R y p c z.1 z.2).symm

def gluedVertexHomotopy (c : C) :
    ((f.comp (pause τ L R)).comp (vertexMap τ L R c)).Homotopy
      ((collapsed τ L R y p).comp (vertexMap τ L R c)) := V c

def coherentHomotopy : (f.comp (pause τ L R)).Homotopy (collapsed τ L R y p) :=
  homotopy τ L R _ _ (gluedVertexHomotopy τ L R f y V p)
    (gluedEdgeHomotopy τ L R f y V a b e he H Q qleft qright e0 q0 p e1)
    (fun c t x => ((gluedPath τ L R f y V a b e H Q qleft qright c (t,x)).source).trans (hleft c t x))
    (fun c t x => (gluedPath τ L R f y V a b e H Q qleft qright c (t,x)).target)

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

section
open Set Metric Topology
open scoped unitInterval
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

structure SquareBoundary (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] where
  b : C(X,C(I,Y) × C(I,Y))
  c : C(X,C(I,Y) × C(I,Y))
  zero : ∀ x, pathEndpoint ((b x).1) = ((c x).1 0,(c x).2 0)
  one : ∀ x, pathEndpoint ((b x).2) = ((c x).1 1,(c x).2 1)

end

open Set Metric Topology
open scoped unitInterval
universe u v
end UniversalFInfinity.Cellular

namespace UniversalFInfinity.Cellular

section
open Set Topology
open scoped unitInterval
universe u v
variable {B : Type u} [TopologicalSpace B] {Y : Type v} [TopologicalSpace Y] {n : ℕ}
variable (a : C(B,C(Sphere n,C(I,Y)))) (b : C(B,C(Disk n,Y × Y)))
variable (h : ∀ v x,pathEndpoint (a v x) = b v (boundary n x))

def familyCylinderFace (i : Option Bool) : Set (B × Sphere (n+1)) :=
  Prod.snd ⁻¹' cylinderFace n i

def familyFaceMap (i : Option Bool) : C(familyCylinderFace (B := B) (n := n) i,Y) := by
  let π : C(familyCylinderFace (B := B) (n := n) i,B) := ⟨fun p => p.1.1,continuous_fst.comp continuous_subtype_val⟩
  let ρ : C(familyCylinderFace (B := B) (n := n) i,cylinderFace n i) :=
    ⟨fun p => ⟨p.1.2,p.2⟩,(continuous_snd.comp continuous_subtype_val).subtype_mk _⟩
  cases i with
  | none => exact ⟨fun p => a (π p) (faceSphere (ρ p)) (faceTime none (ρ p)),
      continuous_eval.comp ((continuous_eval.comp ((a.continuous.comp π.continuous).prodMk
        (faceSphere.continuous.comp ρ.continuous))).prodMk ((faceTime none).continuous.comp ρ.continuous))⟩
  | some c =>
    cases c
    · exact ⟨fun p => (b (π p) (faceTail (some false) (ρ p))).1,
        continuous_fst.comp (continuous_eval.comp ((b.continuous.comp π.continuous).prodMk
          ((faceTail (some false)).continuous.comp ρ.continuous)))⟩
    · exact ⟨fun p => (b (π p) (faceTail (some true) (ρ p))).2,
        continuous_snd.comp (continuous_eval.comp ((b.continuous.comp π.continuous).prodMk
          ((faceTail (some true)).continuous.comp ρ.continuous)))⟩
end

open Set Topology
open scoped unitInterval
universe u v w
variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
  {Z : Type w} [TopologicalSpace Z]
variable (a b : C(I × X,Y)) (A B : Y)
variable (h0 : ∀ x,a (0,x) = b (0,x)) (ha : ∀ x,a (1,x) = A) (hb : ∀ x,b (1,x) = B)

def connectorTop (x : X) : Path A B :=
  (contractionPath a A ha x).symm.trans ((contractionPath b B hb x).cast (h0 x) rfl)

def connectorSquare (x0 : X) : SquareBoundary X Y where
  b := (ContinuousMap.curry ((a.comp ⟨fun x => (0,x),continuous_const.prodMk continuous_id⟩).comp .fst)).prodMk
    (.const _ (connectorTop a b A B h0 ha hb x0).toContinuousMap)
  c := (ContinuousMap.curry (a.comp ⟨Prod.swap,continuous_swap⟩)).prodMk
    (ContinuousMap.curry (b.comp ⟨Prod.swap,continuous_swap⟩))
  zero x := Prod.ext rfl (h0 x)
  one x := Prod.ext ((connectorTop a b A B h0 ha hb x0).source.trans (ha x).symm)
    ((connectorTop a b A B h0 ha hb x0).target.trans (hb x).symm)

end UniversalFInfinity.Cellular

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

namespace UniversalFInfinity.GraphBundle
open Set Topology Cellular
open scoped unitInterval
universe u v
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A]
variable (τ : C → C) (F : C → C(A,A)) (z : A)
variable (H : (ContinuousMap.id A).Homotopy (.const _ z))

def contractionSquare (c : C) : SquareBoundary A A where
  b := (ContinuousMap.curry ((F c).comp .fst)).prodMk
    (.const _ ⟨fun t => H (t,F c z),H.continuous.comp (continuous_id.prodMk continuous_const)⟩)
  c := (ContinuousMap.curry ⟨fun p : A × I => F c (H (p.2,p.1)),
      (F c).continuous.comp (H.continuous.comp continuous_swap)⟩).prodMk
    (ContinuousMap.curry ⟨fun p : A × I => H (p.2,F c p.1),
      H.continuous.comp (continuous_snd.prodMk ((F c).continuous.comp continuous_fst))⟩)
  zero x := by
    apply Prod.ext <;> change F c x = _
    · exact congrArg (F c) (H.apply_zero x).symm
    · exact (H.apply_zero (F c x)).symm
  one x := by
    apply Prod.ext
    · change H (0,F c z) = F c (H (1,x))
      rw [H.apply_zero,H.apply_one]; rfl
    · change H (1,F c z) = H (1,F c x)
      rw [H.apply_one,H.apply_one]; rfl

end UniversalFInfinity.GraphBundle

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

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G B]

lemma exists_equivariant_skeleton_lift_cells_pred (n : ℕ) (p : C(E,B))
    (hp : ∀ (g : G) e, p (g • e) = g • p e)
    (P : E → Prop) (hP : ∀ (g : G) x,P x → P (g • x))
    (F : C(Skeleton (univ : Set X) (n+1),B))
    (hF : ∀ (g : G) x, F (skeletonTranslate σ hσ (n+1) g x) = g • F x)
    (b : C(Skeleton (univ : Set X) n,E))
    (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ n g x) = g • b x)
    (hbP : ∀ x,P (b x))
    (hfill : ∀ i : ι n, ∃ d : C(Disk n,E),
      (∀ x,d (boundary n x) = b (skeletonBoundary n (σ n (1,i)) x)) ∧
      (∀ x,p (d x) = F (skeletonCell n (σ n (1,i)) x)) ∧ ∀ x,P (d x))
    (hbF : ∀ x, p (b x) = F (skeletonBase n x)) :
    ∃ e : C(Skeleton (univ : Set X) (n+1),E),
      (∀ x, e (skeletonBase n x) = b x) ∧ (∀ x, p (e x) = F x) ∧
      (∀ (g : G) x, e (skeletonTranslate σ hσ (n+1) g x) = g • e x) ∧ ∀ x,P (e x) := by
  choose d hd hf hdP using hfill
  let D (j : RelCWComplex.cell (univ : Set X) n) : C(Disk n,E) :=
    ⟨fun x => ((σ n).symm j).1 • d ((σ n).symm j).2 x,
      (continuous_const_smul _).comp (d _).continuous⟩
  have hD (j : RelCWComplex.cell (univ : Set X) n) (x : Sphere n) :
      D j (boundary n x) = b (skeletonBoundary n j x) := by
    obtain ⟨⟨g,i⟩,rfl⟩ := (σ n).surjective j
    change ((σ n).symm (σ n (g,i))).1 • d ((σ n).symm (σ n (g,i))).2 (boundary n x) = _
    rw [Equiv.symm_apply_apply,hd]
    change g • b (skeletonBoundary n (σ n (1,i)) x) = _
    rw [←hb]
    congr 1
    apply Subtype.ext
    exact (hσ n g 1 i x.1).symm.trans (by rw [mul_one]; rfl)
  let f := Attachment.lift (skeletonBoundary (C := (univ : Set X)) n) b D hD
  let e : C(Skeleton (univ : Set X) (n+1),E) := f.comp ⟨(skeletonHomeomorph n).symm,(skeletonHomeomorph n).symm.continuous⟩
  have he_base (x : Skeleton (univ : Set X) n) : e (skeletonBase n x) = b x := by
    change f ((skeletonHomeomorph n).symm (skeletonBase n x)) = _
    rw [←skeletonAssembly_base]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.base _ x))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  have he_cell (j : RelCWComplex.cell (univ : Set X) n) (x : Disk n) :
      e (skeletonCell n j x) = D j x := by
    change f ((skeletonHomeomorph n).symm (skeletonCell n j x)) = _
    rw [←skeletonAssembly_cell]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.cell _ j x))) = _
    rw [Homeomorph.symm_apply_apply]
    exact Attachment.lift_cell _ _ _ _ _ _
  have he (g : G) (x : Skeleton (univ : Set X) (n+1)) :
      e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
    obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
    cases y with
    | inl x =>
      change e (skeletonTranslate σ hσ (n+1) g (skeletonBase n x)) = g • e (skeletonBase n x)
      rw [skeletonTranslate_base,he_base,he_base,hb]
    | inr q =>
      obtain ⟨⟨h,i⟩,hj⟩ := (σ n).surjective q.1
      have heq : skeletonAssembly n (Sum.inr q) = skeletonCell n q.1 (Attachment.interior n q.2) :=
        skeletonAssembly_interior n q.1 q.2
      rw [heq,←hj,skeletonTranslate_cell,he_cell,he_cell]
      change ((σ n).symm (σ n (g*h,i))).1 • d ((σ n).symm (σ n (g*h,i))).2 _ =
        g • (((σ n).symm (σ n (h,i))).1 • d ((σ n).symm (σ n (h,i))).2 _)
      simp only [Equiv.symm_apply_apply,mul_smul]
  refine ⟨e,he_base,?_,he,?_⟩
  · intro x
    obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
    cases y with
    | inl x =>
      change p (e (skeletonBase n x)) = F (skeletonBase n x)
      rw [he_base,hbF]
    | inr q =>
      rw [skeletonAssembly_interior,he_cell]
      obtain ⟨⟨g,i⟩,hj⟩ := (σ n).surjective q.1
      rw [←hj]
      change p (((σ n).symm (σ n (g,i))).1 • d ((σ n).symm (σ n (g,i))).2 _) = _
      rw [Equiv.symm_apply_apply,hp,hf]
      change g • F (skeletonCell n (σ n (1,i)) _) = _
      rw [←hF,skeletonTranslate_cell,mul_one]
  · intro x
    obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
    cases y with
    | inl x =>
      change P (e (skeletonBase n x))
      rw [he_base]
      exact hbP x
    | inr q =>
      rw [skeletonAssembly_interior,he_cell]
      exact hP _ _ (hdP _ _)

end

open Set Metric Topology
universe u
variable {Y : Type u} [TopologicalSpace Y]

def pausePaths : C(C(unitInterval,Y),C(unitInterval,Y)) :=
  ContinuousMap.curry (((pathEvaluation (Y := Y)).trans (ContinuousMap.Homotopy.refl pathOne)).toContinuousMap.comp
    ⟨Prod.swap,continuous_swap⟩)

lemma pausePaths_zero (p : C(unitInterval,Y)) : pausePaths p 0 = p 0 :=
  ((pathEvaluation (Y := Y)).trans (ContinuousMap.Homotopy.refl pathOne)).apply_zero p
lemma pausePaths_one (p : C(unitInterval,Y)) : pausePaths p 1 = p 1 :=
  ((pathEvaluation (Y := Y)).trans (ContinuousMap.Homotopy.refl pathOne)).apply_one p

lemma pausePaths_smul {G : Type*} [Group G] [MulAction G Y] [ContinuousConstSMul G Y]
    (g : G) (p : C(unitInterval,Y)) : pausePaths (g • p) = g • pausePaths p := by
  apply ContinuousMap.ext; intro t
  change ((pathEvaluation (Y := Y)).trans (ContinuousMap.Homotopy.refl pathOne)) (t,g • p) =
    g • (((pathEvaluation (Y := Y)).trans (ContinuousMap.Homotopy.refl pathOne)) (t,p))
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> rfl

variable [T2Space Y] [CWComplex (univ : Set Y)]
omit [TopologicalSpace Y] [T2Space Y] [CWComplex (univ : Set Y)] in
lemma dimH_disk_le (m : ℕ) : dimH (Set.univ : Set (Disk m)) ≤ m := by
  rw [← isometry_subtype_coe.dimH_image]
  have hm := dimH_mono (Set.subset_univ (closedBall (0 : Fin m → ℝ) 1))
  simpa only [Set.image_univ,Subtype.range_coe_subtype,Set.ofPred_mem_eq,Real.dimH_univ_pi_fin] using hm

lemma disk_homotopy_into_skeleton {n d : ℕ} (hnd : n < d)
    (f : C(Disk n,Y)) (H : C(Sphere n,C(unitInterval,Y)))
    (h0 : ∀ x,H x 0 = f (boundary n x))
    (h1 : ∀ x,H x 1 ∈ Skeleton (univ : Set Y) d) :
    ∃ e : C(Disk n,C(unitInterval,Y)),
      (∀ x,e (boundary n x) = pausePaths (H x)) ∧
      (∀ x,e x 0 = f x) ∧ ∀ x,e x 1 ∈ Skeleton (univ : Set Y) d := by
  let B : C(unitInterval × Sphere n,Y) :=
    H.uncurry.comp ⟨Prod.swap,continuous_swap⟩
  let E := Cylinder.extension f B h0
  let f₁ : C(Disk n,Y) := E.comp ⟨fun x => (1,x),continuous_const.prodMk continuous_id⟩
  have hs (x : Sphere n) : f₁ (boundary n x) = H x 1 :=
    Cylinder.extension_boundary f B h0 1 x
  obtain ⟨g,J,hJ⟩ := exists_cellular_approximation_bundle d f₁ (fun _ => Set.mem_univ _)
    ((dimH_disk_le n).trans_lt (by exact_mod_cast hnd))
  let K : f.Homotopy f₁ :=
    { toContinuousMap := E
      map_zero_left := Cylinder.extension_zero f B h0
      map_one_left := fun _ => rfl }
  let L := K.trans J
  let e := ContinuousMap.curry (L.toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩)
  refine ⟨e,?_,fun x => L.apply_zero x,fun x => ?_⟩
  · intro x
    apply ContinuousMap.ext; intro t
    change (K.trans J) (t,boundary n x) =
      ((pathEvaluation (Y := Y)).trans (ContinuousMap.Homotopy.refl pathOne)) (t,H x)
    simp only [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact Cylinder.extension_boundary f B h0 _ x
    · exact (hJ _ _ (hs x ▸ h1 x)).trans (hs x)
  · change L (1,x) ∈ _
    rw [ContinuousMap.Homotopy.apply_one]
    exact (g x).2
end UniversalFInfinity.Cellular

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CellularFillings
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

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X Y : Type u}
  [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
  [MulAction G X] [ContinuousConstSMul G X]
  [TopologicalSpace Y] [T2Space Y] [CWComplex (univ : Set Y)]
  [MulAction G Y] [ContinuousConstSMul G Y]
variable {ι κ : ℕ → Type u}
variable (a : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
  (ha : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
    RelCWComplex.map n (a n (g*h,i)) x = g • RelCWComplex.map n (a n (h,i)) x)
variable (b : ∀ n, (G × κ n) ≃ RelCWComplex.cell (univ : Set Y) n)
  (hb : ∀ n (g h : G) (i : κ n) (x : Fin n → ℝ),
    RelCWComplex.map n (b n (g*h,i)) x = g • RelCWComplex.map n (b n (h,i)) x)

include hb in

theorem exists_equivariant_cellular_homotopy (d n : ℕ) (hnd : n ≤ d)
    (f : C(Skeleton (univ : Set X) n,Y))
    (hf : ∀ (g : G) x, f (skeletonTranslate a ha n g x) = g • f x) :
    ∃ e : C(Skeleton (univ : Set X) n,C(unitInterval,Y)),
      (∀ (g : G) x, e (skeletonTranslate a ha n g x) = g • e x) ∧
      (∀ x,e x 0 = f x) ∧ ∀ x,e x 1 ∈ Skeleton (univ : Set Y) d := by
  induction n with
  | zero =>
    have : IsEmpty (Skeleton (univ : Set X) 0) := by
      refine ⟨fun x => ?_⟩
      have hx := x.2
      change x.1 ∈ (CWComplex.skeletonLT (univ : Set X) 0 : Set X) at hx
      rw [CWComplex.skeletonLT_zero_eq_empty] at hx
      exact hx
    exact ⟨⟨isEmptyElim,continuous_of_discreteTopology⟩,fun _ x => isEmptyElim x,
      fun x => isEmptyElim x,fun x => isEmptyElim x⟩
  | succ n ih =>
    obtain ⟨H,hH,hH0,hH1⟩ := ih (Nat.le_of_succ_le hnd) (f.comp (skeletonBase n)) (fun g x => by
      change f (skeletonBase n (skeletonTranslate a ha n g x)) = g • f (skeletonBase n x)
      rw [←skeletonTranslate_base,hf])
    let H' := pausePaths.comp H
    have hH' (g : G) x : H' (skeletonTranslate a ha n g x) = g • H' x := by
      change pausePaths (H (skeletonTranslate a ha n g x)) = g • pausePaths (H x)
      rw [hH,pausePaths_smul]
    have hH'0 (x) : pathZero (H' x) = f (skeletonBase n x) := by
      exact (pausePaths_zero (H x)).trans (hH0 x)
    have hH'1 (x) : pathOne (H' x) ∈ Skeleton (univ : Set Y) d := by
      change pausePaths (H x) 1 ∈ _
      rw [pausePaths_one]
      exact hH1 x
    have hfill (i : ι n) : ∃ D : C(Disk n,C(unitInterval,Y)),
        (∀ x,D (boundary n x) = H' (skeletonBoundary n (a n (1,i)) x)) ∧
        (∀ x,pathZero (D x) = f (skeletonCell n (a n (1,i)) x)) ∧
        ∀ x,pathOne (D x) ∈ Skeleton (univ : Set Y) d := by
      apply disk_homotopy_into_skeleton (Nat.lt_of_succ_le hnd)
        (f.comp (skeletonCell n (a n (1,i)))) (H.comp (skeletonBoundary n (a n (1,i))))
      · intro x
        exact hH0 (skeletonBoundary n (a n (1,i)) x)
      · intro x
        exact hH1 _
    obtain ⟨e,_,he0,he,he1⟩ := exists_equivariant_skeleton_lift_cells_pred a ha n
      pathZero (fun _ _ => rfl) (fun p => pathOne p ∈ Skeleton (univ : Set Y) d)
      (fun g p hp => skeleton_smul_mem b hb d g hp) f hf H' hH' hH'1 hfill hH'0
    exact ⟨e,he,he0,he1⟩
end

section
open Set Metric Topology
universe u

lemma pathEndpoint_lift_at {Y : Type*} [TopologicalSpace Y] (n : ℕ)
    (hfill : ∀ a : C(Sphere (n+1),Y), ∃ e : C(Disk (n+1),Y), ∀ x,e (boundary (n+1) x) = a x)
    (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))
    (h : ∀ x,pathEndpoint (a x) = b (boundary n x)) :
    ∃ e : C(Disk n,C(unitInterval,Y)),
      (∀ x,e (boundary n x) = a x) ∧ ∀ x,pathEndpoint (e x) = b x := by
  obtain ⟨F,hF⟩ := hfill (cylinderBoundaryMap a b h)
  obtain ⟨e,he,hp⟩ := cylinder_filling_from_disk (.id Y) a b h F hF
  exact ⟨e,fun x => ContinuousMap.ext (he x),hp⟩

variable {G : Type u} [Group G] {X Y : Type u}
  [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
  [MulAction G X] [ContinuousConstSMul G X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
variable {ι : ℕ → Type u}
variable (κ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
  (hκ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
    RelCWComplex.map n (κ n (g*h,i)) x = g • RelCWComplex.map n (κ n (h,i)) x)

lemma equivariant_low_homotopy (d : ℕ) (hfill : LowFillable Y d)
    (a b : C(Skeleton (univ : Set X) d,Y))
    (ha : ∀ (g : G) x,a (skeletonTranslate κ hκ d g x) = g • a x)
    (hb : ∀ (g : G) x,b (skeletonTranslate κ hκ d g x) = g • b x) :
    ∃ H : C(Skeleton (univ : Set X) d,C(unitInterval,Y)),
      (∀ x,pathEndpoint (H x) = (a x,b x)) ∧
      ∀ (g : G) x,H (skeletonTranslate κ hκ d g x) = g • H x := by
  induction d with
  | zero =>
    let := isEmpty_skeleton_zero (X := X)
    exact ⟨⟨isEmptyElim,continuous_of_discreteTopology⟩,fun x => isEmptyElim x,fun _ x => isEmptyElim x⟩
  | succ d ih =>
    obtain ⟨H,hH,hHe⟩ := ih (fun n hn => hfill n (hn.trans (Nat.le_succ d)))
      (a.comp (skeletonBase d)) (b.comp (skeletonBase d))
      (fun g x => by change a (skeletonBase d (skeletonTranslate κ hκ d g x)) = g • a (skeletonBase d x); rw [←skeletonTranslate_base,ha])
      (fun g x => by change b (skeletonBase d (skeletonTranslate κ hκ d g x)) = g • b (skeletonBase d x); rw [←skeletonTranslate_base,hb])
    obtain ⟨e,_,he,hee⟩ := exists_equivariant_skeleton_lift_cells κ hκ d pathEndpoint
      (fun _ _ => rfl) (a.prodMk b) (fun g x => Prod.ext (ha g x) (hb g x)) H hHe
      (fun i => pathEndpoint_lift_at d (hfill (d+1) le_rfl)
        (H.comp (skeletonBoundary d (κ d (1,i))))
        ((a.prodMk b).comp (skeletonCell d (κ d (1,i))))
        (fun x => hH (skeletonBoundary d (κ d (1,i)) x))) hH
    exact ⟨e,he,hee⟩
end

open Set Metric Topology
universe u v w
end UniversalFInfinity.Cellular

namespace UniversalFInfinity.Cellular

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G]
local instance (priority := 2000) instDecidableEqProdNat_solutions_r7f5f75_2 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq _
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
  [MulAction G X] [ContinuousConstSMul G X]
variable {ι : ℕ → Type u} [∀ m,Finite (ι m)]
variable (α : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
  (hα : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
    RelCWComplex.map n (α n (g*h,i)) x = g • RelCWComplex.map n (α n (h,i)) x)

lemma controlled_map_on_skeleton (d : ℕ) (e : C(Skeleton (univ : Set X) d,Milnor.Space G))
    (he : ∀ (g : G) x,e (skeletonTranslate α hα d g x) = g • e x) :
    ∃ S : Milnor.Shapes G, Set.range e ⊆ Set.range (Milnor.stageFull G S) := by
  obtain ⟨K,hK,hcov⟩ := skeleton_compact_representatives α hα d
  obtain ⟨S,hS⟩ := Milnor.compact_orbit_controlled G (hK.image e.continuous)
  refine ⟨S,?_⟩
  rintro _ ⟨x,rfl⟩
  obtain ⟨g,y,hy,rfl⟩ := hcov x
  rw [he]
  exact hS g ⟨e y,⟨y,hy,rfl⟩,rfl⟩

lemma exists_brown_data
    (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)
    (n : ℕ) (hfill : LowFillable X n) :
    ∃ T : Milnor.Shapes G,
    letI cw := Milnor.stageEquivariantCW G T
    let β : ∀ m, (G × Milnor.CellOrbits G T m) ≃ cw.cell m := fun _ => Equiv.refl _
    let hβ : ∀ m (g h : G) (i : Milnor.CellOrbits G T m) (x : Fin m → ℝ),
      cw.map m (β m (g*h,i)) x = g • cw.map m (β m (h,i)) x := fun _ g h _ _ => mul_smul g h _
    ∃ (q : C(Skeleton (univ : Set X) (n+1),Skeleton (univ : Set (Milnor.Stage G T)) (n+1)))
      (r : C(Skeleton (univ : Set (Milnor.Stage G T)) (n+1),X))
      (H : C(Skeleton (univ : Set X) n,C(unitInterval,X))),
      ((skeletonInclusion (n+1)).comp q).Nullhomotopic ∧
      (∀ (g : G) x,q (skeletonTranslate α hα (n+1) g x) = skeletonTranslate β hβ (n+1) g (q x)) ∧
      (∀ (g : G) x,r (skeletonTranslate β hβ (n+1) g x) = g • r x) ∧
      (∀ x,pathEndpoint (H x) = ((skeletonBase n x).1,r (q (skeletonBase n x)))) ∧
      ∀ (g : G) x,H (skeletonTranslate α hα n g x) = g • H x := by
  obtain ⟨e,he⟩ := exists_equivariant_map_on_skeleton α hα (n+1)
    (fun m _ => Milnor.sphereFillable (1:G) m)
  obtain ⟨S,hS⟩ := controlled_map_on_skeleton α hα (n+1) e he
  let eS := Milnor.factorStage G e S hS
  have heS (g : G) x : eS (skeletonTranslate α hα (n+1) g x) = g • eS x := by
    apply (Milnor.stageFull_embedding G S).injective
    rw [Milnor.factorStage_spec,Milnor.stageFull_smul,Milnor.factorStage_spec,he]
  obtain ⟨T,hST,z,⟨K⟩⟩ := hunif S
  let : CWComplex (univ : Set (Milnor.Stage G T)) := Milnor.stageEquivariantCW G T
  let β : ∀ m, (G × Milnor.CellOrbits G T m) ≃ RelCWComplex.cell (univ : Set (Milnor.Stage G T)) m :=
    fun _ => Equiv.refl _
  have hβ : ∀ m (g h : G) (i : Milnor.CellOrbits G T m) (x : Fin m → ℝ),
      RelCWComplex.map m (β m (g*h,i)) x = g • RelCWComplex.map m (β m (h,i)) x :=
    fun _ g h _ _ => mul_smul g h _
  let f := (Milnor.stageIncl G S T hST).comp eS
  have hf (g : G) x : f (skeletonTranslate α hα (n+1) g x) = g • f x := by
    change Milnor.stageIncl G S T hST (eS _) = _
    rw [heS,Milnor.stageIncl_smul]
    rfl
  obtain ⟨J,hJe,hJ0,hJ1⟩ := exists_equivariant_cellular_homotopy α hα β hβ (n+1) (n+1) le_rfl f hf
  let q : C(Skeleton (univ : Set X) (n+1),Skeleton (univ : Set (Milnor.Stage G T)) (n+1)) :=
    ⟨fun x => ⟨J x 1,hJ1 x⟩,(J.continuous.eval_const _).subtype_mk _⟩
  have hq (g : G) x : q (skeletonTranslate α hα (n+1) g x) = skeletonTranslate β hβ (n+1) g (q x) := by
    apply Subtype.ext
    exact ContinuousMap.congr_fun (hJe g x) 1
  let J' : f.Homotopy ((skeletonInclusion (n+1)).comp q) :=
    { toFun := fun z => J z.2 z.1
      continuous_toFun := (J.continuous.comp continuous_snd).eval continuous_fst
      map_zero_left := hJ0
      map_one_left := fun _ => rfl }
  have hqnull : ((skeletonInclusion (n+1)).comp q).Nullhomotopic :=
    ⟨z,⟨J'.symm.trans (K.compContinuousMap eS)⟩⟩
  obtain ⟨r,hr⟩ := exists_equivariant_map_on_skeleton β hβ (n+1)
    (fun m hm => hfill m (Nat.le_of_lt_succ hm))
  let a := skeletonInclusion (C := (univ : Set X)) n
  let b := r.comp (q.comp (skeletonBase n))
  have ha (g : G) x : a (skeletonTranslate α hα n g x) = g • a x := rfl
  have hb (g : G) x : b (skeletonTranslate α hα n g x) = g • b x := by
    change r (q (skeletonBase n (skeletonTranslate α hα n g x))) = _
    rw [←skeletonTranslate_base,hq,hr]
    rfl
  obtain ⟨H,hH,hHe⟩ := equivariant_low_homotopy α hα n hfill a b ha hb
  exact ⟨T,q,r,H,hqnull,hq,hr,hH,hHe⟩
end

open Set Metric Topology
universe u
variable {G : Type u} [Group G]
local instance (priority := 2000) instDecidableEqProdNat_solutions_1_r7f5f75_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq _
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
  [MulAction G X] [ContinuousConstSMul G X] [Nonempty X]
variable {ι : ℕ → Type u} [∀ m,Finite (ι m)]
variable (α : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
  (hα : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
    RelCWComplex.map n (α n (g*h,i)) x = g • RelCWComplex.map n (α n (h,i)) x)

omit [MulAction G X] [ContinuousConstSMul G X] [Nonempty X] in
lemma skeleton_eq_univ_of_dimension (n : ℕ)
    (hdim : ∀ m (_ : RelCWComplex.cell (univ : Set X) m),m ≤ n) :
    Skeleton (univ : Set X) (n+1) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ (univ : Set X) := trivial
  rw [←CWComplex.union (C := (univ : Set X))] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨m,i,y,hy,rfl⟩ := hx
  exact characteristic_mem_skeleton (Nat.lt_succ_of_le (hdim m i)) i ⟨y,hy⟩

include hα in
lemma exists_finite_brown_attachment
    (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)
    (n : ℕ) (hfill : LowFillable X n)
    (hdim : ∀ m (_ : RelCWComplex.cell (univ : Set X) m),m ≤ n)
    (hsep : Attachment.RealSeparated X) :
    ∃ (I : Type u) (_ : Finite I) (a : I → C(Sphere (n+1),X)),
      LowFillable (Attachment.Space (Attachment.equivariantFamily (G := G) a)) (n+1) := by
  obtain ⟨T,q,r,H,hqnull,hq,hr,hH,hHe⟩ := exists_brown_data α hα hunif n hfill
  let cw := Milnor.stageEquivariantCW G T
  let β : ∀ m,(G × Milnor.CellOrbits G T m) ≃ cw.cell m := fun _ => Equiv.refl _
  have hβ : ∀ m (g h : G) (i : Milnor.CellOrbits G T m) (x : Fin m → ℝ),
      cw.map m (β m (g*h,i)) x = g • cw.map m (β m (h,i)) x := fun _ g h _ _ => mul_smul g h _
  let a := brownObstructions α β n q r H hH
  let := Attachment.t2Space (Attachment.equivariantFamily (G := G) a) hsep
  exact ⟨_,inferInstance,a,brown_lowFillable α hα β hβ n q r H hH
    (skeleton_eq_univ_of_dimension n hdim) hqnull hq hr hHe⟩
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

def of (n : ℕ) (x : X n) : Space X f := ⟦⟨n,x⟩⟧

instance instTopologicalSpaceSpace : TopologicalSpace (Space X f) :=
  TopologicalSpace.coinduced (fun x : Σ n, X n => of X f x.1 x.2) inferInstance

lemma of_compat (i j : ℕ) (h : i ≤ j) (x : X i) :
    of X f j (f i j h x) = of X f i x := DirectLimit.mk_apply i j x h

lemma continuous_iff {Y : Type v} [TopologicalSpace Y] (g : Space X f → Y) :
    Continuous g ↔ ∀ n, Continuous (g ∘ of X f n) := by
  rw [continuous_coinduced_dom,continuous_sigma_iff]
  rfl

lemma continuous_of (n : ℕ) : Continuous (of X f n) := by
  have h : Continuous (fun x : Σ n, X n => of X f x.1 x.2) := continuous_coinduced_rng
  exact h.comp continuous_sigmaMk

lemma isClosed_iff (A : Set (Space X f)) :
    IsClosed A ↔ ∀ n, IsClosed (of X f n ⁻¹' A) := by
  rw [isClosed_coinduced]
  exact isClosed_sigma_iff

variable (hf : ∀ i j h, IsClosedEmbedding (f i j h))

include hf in
lemma of_injective (n : ℕ) : Function.Injective (of X f n) :=
  DirectLimit.mk_injective f (fun i j h => (hf i j h).injective) n

include hf in
lemma preimage_of_image_le (i j : ℕ) (h : i ≤ j) (A : Set (X i)) :
    of X f j ⁻¹' (of X f i '' A) = f i j h '' A := by
  ext y
  constructor
  · rintro ⟨x,hx,hxy⟩
    refine ⟨x,hx,?_⟩
    apply of_injective X f hf j
    exact (of_compat X f i j h x).trans hxy
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,hx,(of_compat X f i j h x).symm⟩

include hf in
lemma preimage_of_image_ge (i j : ℕ) (h : j ≤ i) (A : Set (X i)) :
    of X f j ⁻¹' (of X f i '' A) = f j i h ⁻¹' A := by
  ext y
  constructor
  · rintro ⟨x,hx,hxy⟩
    have he : x = f j i h y := of_injective X f hf i
      (hxy.trans (of_compat X f j i h y).symm)
    change f j i h y ∈ A
    rw [← he]
    exact hx
  · intro hA
    exact ⟨f j i h y,hA,of_compat X f j i h y⟩

include hf in
lemma of_closedEmbedding (n : ℕ) : IsClosedEmbedding (of X f n) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_of X f n) (of_injective X f hf n)
  intro A hA
  rw [isClosed_iff]
  intro m
  rcases le_total n m with h | h
  · rw [preimage_of_image_le X f hf n m h]
    exact (hf n m h).isClosedMap _ hA
  · rw [preimage_of_image_ge X f hf n m h]
    exact hA.preimage (hf m n h).continuous

def lift {Y : Type v} [TopologicalSpace Y] (g : ∀ n, C(X n,Y))
    (hg : ∀ i j h x, g i x = g j (f i j h x)) : C(Space X f,Y) :=
  ⟨DirectLimit.lift f (fun n => g n) hg,
    (continuous_iff X f _).mpr (fun n => (g n).continuous)⟩

@[simp] lemma lift_of {Y : Type v} [TopologicalSpace Y] (g : ∀ n, C(X n,Y))
    (hg : ∀ i j h x, g i x = g j (f i j h x)) (n : ℕ) (x : X n) :
    lift X f g hg (of X f n x) = g n x := rfl

end UniversalFInfinity.TopologicalTower

namespace UniversalFInfinity.CellularTower
open Set Metric Topology
universe u
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
variable [∀ n, Nonempty (X n)]
variable [∀ n, CWComplex (Set.univ : Set (X n))]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
variable (hf : ∀ i j h, IsClosedEmbedding (f i j h))

structure CellSystem where
  index : ℕ → Type u
  cell : ∀ n m, m ≤ n → index m → RelCWComplex.cell (Set.univ : Set (X n)) m
  injective : ∀ n m h, Function.Injective (cell n m h)
  exhaustive : ∀ n m (j : RelCWComplex.cell (Set.univ : Set (X n)) m),
    ∃ (h : m ≤ n) (i : index m), cell n m h i = j
  compatibility : ∀ n k (h : n ≤ k) (m : ℕ) (hm : m ≤ n) (i : index m) (x : Fin m → ℝ),
    f n k h (RelCWComplex.map m (cell n m hm i) x) =
      RelCWComplex.map m (cell k m (hm.trans h) i) x

variable (D : CellSystem X f)

abbrev Limit := TopologicalTower.Space X f
abbrev stage (n : ℕ) := TopologicalTower.of X f n

def map (m : ℕ) (i : D.index m) : PartialEquiv (Fin m → ℝ) (Limit X f) :=
  Cellular.transportedMap (TopologicalTower.of_closedEmbedding X f hf m)
    m (D.cell m m le_rfl i)

lemma map_eq_stage (n m : ℕ) (hm : m ≤ n) (i : D.index m) (x : Fin m → ℝ) :
    map X f hf D m i x = stage X f n (RelCWComplex.map m (D.cell n m hm i) x) := by
  change stage X f m (RelCWComplex.map m (D.cell m m le_rfl i) x) = _
  unfold stage
  rw [← TopologicalTower.of_compat X f m n hm,D.compatibility]

lemma map_image (n m : ℕ) (hm : m ≤ n) (i : D.index m) (S : Set (Fin m → ℝ)) :
    map X f hf D m i '' S = stage X f n '' (RelCWComplex.map m (D.cell n m hm i) '' S) := by
  rw [← Set.image_comp]
  congr 1
  funext x
  exact map_eq_stage X f hf D n m hm i x

def globalIndex (n m : ℕ) (j : RelCWComplex.cell (Set.univ : Set (X n)) m) : D.index m :=
  (D.exhaustive n m j).choose_spec.choose

omit [∀ n, Nonempty (X n)] [DirectedSystem X (f · · ·)] in
lemma globalIndex_spec (n m : ℕ) (j : RelCWComplex.cell (Set.univ : Set (X n)) m) :
    D.cell n m (D.exhaustive n m j).choose (globalIndex X f D n m j) = j :=
  (D.exhaustive n m j).choose_spec.choose_spec

lemma old_image (n m : ℕ) (j : RelCWComplex.cell (Set.univ : Set (X n)) m)
    (S : Set (Fin m → ℝ)) :
    stage X f n '' (RelCWComplex.map m j '' S) =
      map X f hf D m (globalIndex X f D n m j) '' S := by
  rw [map_image X f hf D n m (D.exhaustive n m j).choose,globalIndex_spec]

variable [∀ n, T2Space (X n)]

@[instance_reducible]
def cwComplex : CWComplex (Set.univ : Set (Limit X f)) where
  cell := D.index
  map := map X f hf D
  source_eq := fun m i => Cellular.transportedMap_source _ _ _
  continuousOn := fun m i => Cellular.transportedMap_continuousOn _ _ _
  continuousOn_symm := fun m i => Cellular.transportedMap_continuousOn_symm _ _ _
  pairwiseDisjoint' := by
    rintro ⟨m,i⟩ _ ⟨k,j⟩ _ hne
    change Disjoint (map X f hf D m i '' ball 0 1) (map X f hf D k j '' ball 0 1)
    rw [map_image X f hf D (max m k) m (le_max_left _ _),
      map_image X f hf D (max m k) k (le_max_right _ _)]
    apply (CWComplex.disjoint_openCell_of_ne ?_).image
      (TopologicalTower.of_injective X f hf (max m k)).injOn (Set.subset_univ _) (Set.subset_univ _)
    intro heq
    have hmk := congrArg Sigma.fst heq
    change m = k at hmk
    subst k
    have hij : D.cell (max m m) m (le_max_left _ _) i =
        D.cell (max m m) m (le_max_right _ _) j := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    have : i = j := D.injective _ _ _ hij
    exact hne (by subst j; rfl)
  mapsTo' := by
    classical
    intro m i
    obtain ⟨I,hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell m (D.cell m m le_rfl i)
    refine ⟨fun k => (I k).image (globalIndex X f D m k),?_⟩
    intro x hx
    have h := hI (show RelCWComplex.map m (D.cell m m le_rfl i) x ∈
      CWComplex.cellFrontier m (D.cell m m le_rfl i) from ⟨x,hx,rfl⟩)
    simp only [Set.mem_iUnion] at h
    obtain ⟨k,hkm,j,hj,hx'⟩ := h
    refine Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hkm,Set.mem_iUnion.mpr
      ⟨globalIndex X f D m k j,Set.mem_iUnion.mpr
        ⟨Finset.mem_image.mpr ⟨j,hj,rfl⟩,?_⟩⟩⟩⟩
    rw [← old_image X f hf D m k j]
    exact ⟨_,hx',rfl⟩
  closed' := by
    intro A _ hA
    rw [TopologicalTower.isClosed_iff]
    intro n
    apply (CWComplex.closed Set.univ (stage X f n ⁻¹' A) (Set.subset_univ _)).mpr
    intro m j
    have h := (hA m (globalIndex X f D n m j)).preimage (TopologicalTower.continuous_of X f n)
    rw [← old_image X f hf D n m j,Set.preimage_inter,
      Set.preimage_image_eq _ (TopologicalTower.of_injective X f hf n)] at h
    exact h
  union' := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨n,x,rfl⟩ := DirectLimit.exists_eq_mk f z
    have hx : x ∈ (Set.univ : Set (X n)) := Set.mem_univ _
    rw [← CWComplex.union (C := (Set.univ : Set (X n)))] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨m,j,hx⟩ := hx
    refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨globalIndex X f D n m j,?_⟩⟩
    rw [← old_image X f hf D n m j]
    exact ⟨x,hx,rfl⟩

end UniversalFInfinity.CellularTower

namespace UniversalFInfinity.Sequential
open Set Topology
universe u
variable (X : ℕ → Type u) [∀ n,TopologicalSpace (X n)]
variable (step : ∀ n,C(X n,X (n+1)))

lemma map_succ (i j : ℕ) (h : i ≤ j) :
    map X step i (j+1) (h.trans (Nat.le_succ j)) = (step j).comp (map X step i j h) := by
  simp only [map,Nat.leRecOn_succ h]
@[simp] lemma map_step (i : ℕ) : map X step i (i+1) (Nat.le_succ i) = step i := by
  rw [map_succ X step i i le_rfl,map_self,ContinuousMap.comp_id]

instance instDirectedSystemNatCoeContinuousMapMap : DirectedSystem X (map X step · · ·) where
  map_self {i} x := by simp only [map_self,ContinuousMap.id_apply]
  map_map {k j i} hij hjk x := by
    induction k,hjk using Nat.le_induction with
    | base => simp only [map_self,ContinuousMap.id_apply]
    | succ k hk ih =>
      rw [map_succ X step j k hk,map_succ X step i k (hij.trans hk)]
      change step k (map X step j k hk (map X step i j hij x)) = step k (map X step i k (hij.trans hk) x)
      rw [ih]

lemma map_closedEmbedding (hs : ∀ n,IsClosedEmbedding (step n)) (i j : ℕ) (h : i ≤ j) :
    IsClosedEmbedding (map X step i j h) := by
  induction j,h using Nat.le_induction with
  | base => simpa only [map_self,ContinuousMap.coe_id] using IsClosedEmbedding.id
  | succ j h ih => rw [map_succ X step i j h]; exact (hs j).comp ih

variable [∀ n,CWComplex (univ : Set (X n))]

variable (D : CellSteps X step)
lemma cellMap_succ (i j : ℕ) (h : i ≤ j) (m : ℕ) :
    cellMap X step D i (j+1) (h.trans (Nat.le_succ j)) m = D.cell j m ∘ cellMap X step D i j h m := by
  simp only [cellMap,Nat.leRecOn_succ h]
lemma cellMap_injective (i j : ℕ) (h : i ≤ j) (m : ℕ) :
    Function.Injective (cellMap X step D i j h m) := by
  induction j,h using Nat.le_induction with
  | base => rw [cellMap_self]; exact Function.injective_id
  | succ j h ih => rw [cellMap_succ X step D i j h]; exact (D.injective j m).comp ih
lemma cellMap_comp (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (m : ℕ) (c) :
    cellMap X step D j k hjk m (cellMap X step D i j hij m c) =
      cellMap X step D i k (hij.trans hjk) m c := by
  induction k,hjk using Nat.le_induction with
  | base => rw [cellMap_self]; rfl
  | succ k hk ih =>
    rw [cellMap_succ X step D j k hk,cellMap_succ X step D i k (hij.trans hk)]
    exact congrArg (D.cell k m) ih
lemma cellMap_compat (i j : ℕ) (h : i ≤ j) (m : ℕ) (c) (x : Fin m → ℝ) :
    map X step i j h (RelCWComplex.map m c x) = RelCWComplex.map m (cellMap X step D i j h m c) x := by
  induction j,h using Nat.le_induction with
  | base => rw [map_self,cellMap_self]; rfl
  | succ j h ih =>
    rw [map_succ X step i j h,cellMap_succ X step D i j h]
    change step j (map X step i j h (RelCWComplex.map m c x)) = _
    rw [ih,D.compatibility]

lemma cellMap_exhaustive (n m : ℕ) (c : RelCWComplex.cell (univ : Set (X n)) m) :
    ∃ (h : m ≤ n) (i : RelCWComplex.cell (univ : Set (X m)) m),cellMap X step D m n h m i = c := by
  induction n with
  | zero =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero (D.dim 0 m c)
    subst m
    exact ⟨le_rfl,c,by rw [cellMap_self]; rfl⟩
  | succ n ih =>
    by_cases hm : m = n+1
    · subst m
      exact ⟨le_rfl,c,by rw [cellMap_self]; rfl⟩
    · obtain ⟨j,rfl⟩ := D.exhaustive n m hm c
      obtain ⟨h,i,hi⟩ := ih j
      refine ⟨h.trans (Nat.le_succ n),i,?_⟩
      rw [cellMap_succ X step D m n h]
      exact congrArg (D.cell n m) hi

variable [∀ n,Nonempty (X n)]
def cellSystem : CellularTower.CellSystem X (map X step) where
  index m := RelCWComplex.cell (univ : Set (X m)) m
  cell n m h := cellMap X step D m n h m
  injective n m h := cellMap_injective X step D m n h m
  exhaustive := cellMap_exhaustive X step D
  compatibility n k h m hm i x := by
    rw [cellMap_compat X step D n k h,cellMap_comp X step D m n k hm h]
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

variable [EquivariantSystem (G := G) X f]

instance limitMulAction : MulAction G (Space X f) where
  smul g := DirectLimit.lift f (fun n x => of X f n (g • x)) (fun i j h x => by
    rw [← EquivariantSystem.map_smul i j h g x,of_compat])
  one_smul z := by
    obtain ⟨n,x,rfl⟩ := DirectLimit.exists_eq_mk f z
    change of X f n ((1:G) • x) = of X f n x
    rw [one_smul]
  mul_smul g h z := by
    obtain ⟨n,x,rfl⟩ := DirectLimit.exists_eq_mk f z
    change of X f n ((g*h) • x) = of X f n (g • h • x)
    rw [mul_smul]

@[simp] lemma smul_of (g : G) (n : ℕ) (x : X n) :
    g • of X f n x = of X f n (g • x) := rfl

end

section
open Set Topology
universe u v w
variable {G : Type w} [Group G]
variable (E : ℕ → Type u) [∀ n, TopologicalSpace (E n)] [∀ n, MulAction G (E n)]
variable (e : ∀ i j, i ≤ j → C(E i,E j)) [DirectedSystem E (e · · ·)]
variable [EquivariantSystem (G := G) E e] [∀ n, ContinuousConstSMul G (E n)]
variable (X : ℕ → Type v) [∀ n, TopologicalSpace (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
variable (p : ∀ n, C(E n,X n))
variable (hp : ∀ i j h x, p j (e i j h x) = f i j h (p i x))

def limitMap : C(Space E e,Space X f) :=
  ⟨DirectLimit.lift e (fun n x => of X f n (p n x)) (fun i j h x => by
    rw [hp,of_compat]), (continuous_iff E e _).mpr (fun n =>
      (continuous_of X f n).comp (p n).continuous)⟩

@[simp] lemma limitMap_of (n : ℕ) (x : E n) :
    limitMap E e X f p hp (of E e n x) = of X f n (p n x) := rfl

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
open Set Metric Topology Cellular Attachment
universe u
variable (G : Type u) [Group G]

attribute [instance] Stage.topE Stage.topB Stage.nonemptyE Stage.nonemptyB
  Stage.cwE Stage.cwB Stage.action Stage.continuousAction Stage.orbitFinite Stage.finiteB

instance instT2SpaceB {n : ℕ} (S : Stage G n) : T2Space S.B := S.sepB.t2Space

variable {G}

instance instFiniteZeroOrbits (m : ℕ) : Finite (ZeroOrbits.{u} m) := by cases m <;> dsimp [ZeroOrbits] <;> infer_instance

section Zero
variable [TopologicalSpace G] [DiscreteTopology G]
def zeroEquiv (m : ℕ) : (G × ZeroOrbits.{u} m) ≃ RelCWComplex.cell (univ : Set G) m := by
  cases m with
  | zero =>
    exact { toFun := fun p => ⟨p.1,trivial⟩
            invFun := fun p => (p.1,PUnit.unit)
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  | succ m =>
    change (G × PEmpty.{u+1}) ≃ PEmpty
    exact Equiv.equivOfIsEmpty _ _
lemma zeroEquiv_map (m : ℕ) (g h : G) (i : ZeroOrbits.{u} m) (x : Fin m → ℝ) :
    RelCWComplex.map m (zeroEquiv m (g*h,i)) x = g • RelCWComplex.map m (zeroEquiv m (h,i)) x := by
  cases m with
  | zero => rfl
  | succ m => exact i.elim

def zeroStage : Stage G 0 where
  E := G
  B := PUnit.{u+1}
  topE := inferInstance
  topB := inferInstance
  nonemptyE := inferInstance
  nonemptyB := inferInstance
  sepE := realSeparated_of_tychonoff
  sepB := realSeparated_of_tychonoff
  cwE := inferInstance
  cwB := inferInstance
  action := inferInstance
  continuousAction := inferInstance
  orbits := ZeroOrbits
  orbitFinite := inferInstance
  equiv := zeroEquiv
  equiv_map := zeroEquiv_map
  dimE := discrete_dim
  dimB := discrete_dim
  finiteB m := by
    cases m with
    | zero =>
      change Finite (univ : Set PUnit.{u+1})
      infer_instance
    | succ m =>
      change Finite PEmpty
      infer_instance
  fill m hm a := by
    have hm : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    obtain ⟨e,he⟩ := SphereTopology.fill_zero a
    exact ⟨e,he⟩
  p := pointCover
  covering := pointCover_quotient
end Zero

variable (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)
variable {n : ℕ} (S : Stage G n)

def nextIndex : Type u := (exists_finite_brown_attachment S.equiv S.equiv_map hunif n S.fill S.dimE S.sepE).choose
instance instFiniteNextIndex : Finite (nextIndex hunif S) :=
  (exists_finite_brown_attachment S.equiv S.equiv_map hunif n S.fill S.dimE S.sepE).choose_spec.choose

def attaching : nextIndex hunif S → C(Cellular.Sphere (n+1),S.E) :=
  (exists_finite_brown_attachment S.equiv S.equiv_map hunif n S.fill S.dimE S.sepE).choose_spec.choose_spec.choose
lemma attaching_fill : LowFillable (Space (equivariantFamily (G := G) (attaching hunif S))) (n+1) :=
  (exists_finite_brown_attachment S.equiv S.equiv_map hunif n S.fill S.dimE S.sepE).choose_spec.choose_spec.choose_spec

def downstairs (i : nextIndex hunif S) : C(Cellular.Sphere (n+1),S.B) := S.p.comp (attaching hunif S i)

instance nextE_nonempty : Nonempty (Space (equivariantFamily (G := G) (attaching hunif S))) :=
  ⟨base _ (Classical.choice S.nonemptyE)⟩
instance nextB_nonempty : Nonempty (Space (downstairs hunif S)) := ⟨base _ (Classical.choice S.nonemptyB)⟩
instance nextE_t2 : T2Space (Space (equivariantFamily (G := G) (attaching hunif S))) :=
  (realSeparated _ S.sepE).t2Space
instance nextB_t2 : T2Space (Space (downstairs hunif S)) := (realSeparated _ S.sepB).t2Space

def nextStage : Stage G (n+1) where
  E := Space (equivariantFamily (G := G) (attaching hunif S))
  B := Space (downstairs hunif S)
  topE := inferInstance
  topB := inferInstance
  nonemptyE := inferInstance
  nonemptyB := inferInstance
  sepE := realSeparated _ S.sepE
  sepB := realSeparated _ S.sepB
  cwE := equivariantLayerCW S.equiv S.equiv_map (attaching hunif S) (fun m i => Nat.lt_succ_of_le (S.dimE m i))
  cwB := layerCW (downstairs hunif S) (fun m i => Nat.lt_succ_of_le (S.dimB m i))
  action := inferInstance
  continuousAction := inferInstance
  orbits := LayerOrbits (ι := S.orbits) (I := nextIndex hunif S) (n := n+1)
  orbitFinite m := by dsimp [LayerOrbits]; infer_instance
  equiv _ := Equiv.refl _
  equiv_map := equivariantLayerCW_smul S.equiv S.equiv_map (attaching hunif S) _
  dimE m i := Nat.le_of_lt_succ (equivariantLayerCW_dims S.equiv S.equiv_map (attaching hunif S) _ m i)
  dimB m i := Nat.le_of_lt_succ (layerCW_dimensions (downstairs hunif S) _ m i)
  finiteB := layerCW_finite_cells (downstairs hunif S) S.finiteB _
  fill := attaching_fill hunif S
  p := coverMap (attaching hunif S) S.p S.covering (downstairs hunif S) (fun _ _ => rfl)
  covering := coverMap_isQuotientCovering _ _ _ _ _
end

section
open Set Metric Topology Cellular Attachment
universe u
variable {G : Type u} [Group G]
variable (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)
variable {n : ℕ} (S : Stage G n)

def nextInE : C(S.E,(nextStage hunif S).E) := ⟨base _,continuous_base _⟩
def nextInB : C(S.B,(nextStage hunif S).B) := ⟨base _,continuous_base _⟩
lemma nextInE_closed : IsClosedEmbedding (nextInE hunif S) := base_closedEmbedding _
lemma nextInB_closed : IsClosedEmbedding (nextInB hunif S) := base_closedEmbedding _
lemma nextInE_smul (g : G) (x : S.E) : nextInE hunif S (g • x) = g • nextInE hunif S x := rfl
lemma next_square (x : S.E) :
    (nextStage hunif S).p (nextInE hunif S x) = nextInB hunif S (S.p x) := rfl

def nextCellE (m : ℕ) : S.cwE.cell m → (nextStage hunif S).cwE.cell m :=
  layerOld S.equiv S.equiv_map (attaching hunif S) _ m
lemma nextCellE_injective (m : ℕ) : Function.Injective (nextCellE hunif S m) :=
  layerOld_injective _ _ _ _ m
lemma nextCellE_exhaustive (m : ℕ) (hm : m ≠ n+1) (i : (nextStage hunif S).cwE.cell m) :
    ∃ j,nextCellE hunif S m j = i := layerOld_exhaustive _ _ _ _ m hm i
lemma nextCellE_map (m : ℕ) (i : S.cwE.cell m) (x : Fin m → ℝ) :
    nextInE hunif S (S.cwE.map m i x) = (nextStage hunif S).cwE.map m (nextCellE hunif S m i) x :=
  (layerOld_map _ _ _ _ m i x).symm

def nextCellB (m : ℕ) : S.cwB.cell m → (nextStage hunif S).cwB.cell m := Sum.inl
lemma nextCellB_injective (m : ℕ) : Function.Injective (nextCellB hunif S m) := Sum.inl_injective
lemma nextCellB_exhaustive (m : ℕ) (hm : m ≠ n+1) (i : (nextStage hunif S).cwB.cell m) :
    ∃ j,nextCellB hunif S m j = i := by
  cases i with
  | inl i => exact ⟨i,rfl⟩
  | inr i => exact (hm i.down.1.down).elim
lemma nextCellB_map (m : ℕ) (i : S.cwB.cell m) (x : Fin m → ℝ) :
    nextInB hunif S (S.cwB.map m i x) = (nextStage hunif S).cwB.map m (nextCellB hunif S m i) x := rfl

end

open Set Metric Topology Cellular Attachment
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)

def stages : (n : ℕ) → Stage G n
  | 0 => zeroStage
  | n+1 => nextStage hunif (stages n)
abbrev E (n : ℕ) := (stages hunif n).E
abbrev B (n : ℕ) := (stages hunif n).B

def eStep (n : ℕ) : C(E hunif n,E hunif (n+1)) := nextInE hunif (stages hunif n)
def bStep (n : ℕ) : C(B hunif n,B hunif (n+1)) := nextInB hunif (stages hunif n)
abbrev eMap := Sequential.map (E hunif) (eStep hunif)
abbrev bMap := Sequential.map (B hunif) (bStep hunif)
lemma eMap_closed : ∀ i j h,IsClosedEmbedding (eMap hunif i j h) :=
  Sequential.map_closedEmbedding _ _ (fun n => nextInE_closed hunif (stages hunif n))
lemma bMap_closed : ∀ i j h,IsClosedEmbedding (bMap hunif i j h) :=
  Sequential.map_closedEmbedding _ _ (fun n => nextInB_closed hunif (stages hunif n))

instance instEquivariantSystemEEMap : TopologicalTower.EquivariantSystem (G := G) (E hunif) (eMap hunif) where
  map_smul i j h g x := by
    induction j,h using Nat.le_induction with
    | base => simp only [eMap,Sequential.map_self,ContinuousMap.id_apply]
    | succ j h ih =>
      simp only [eMap,Sequential.map_succ _ _ i j h,ContinuousMap.comp_apply]
      change eStep hunif j (eMap hunif i j h (g • x)) = g • eStep hunif j (eMap hunif i j h x)
      rw [ih]
      exact nextInE_smul hunif (stages hunif j) g _

def eCells : Sequential.CellSteps (E hunif) (eStep hunif) where
  cell n := nextCellE hunif (stages hunif n)
  injective n := nextCellE_injective hunif (stages hunif n)
  dim n := (stages hunif n).dimE
  exhaustive n := nextCellE_exhaustive hunif (stages hunif n)
  compatibility n := nextCellE_map hunif (stages hunif n)
def bCells : Sequential.CellSteps (B hunif) (bStep hunif) where
  cell n := nextCellB hunif (stages hunif n)
  injective n := nextCellB_injective hunif (stages hunif n)
  dim n := (stages hunif n).dimB
  exhaustive n := nextCellB_exhaustive hunif (stages hunif n)
  compatibility n := nextCellB_map hunif (stages hunif n)

abbrev Total := TopologicalTower.Space (E hunif) (eMap hunif)
abbrev Base := TopologicalTower.Space (B hunif) (bMap hunif)
instance instNonemptyTotal : Nonempty (Total hunif) := ⟨TopologicalTower.of (E hunif) (eMap hunif) 0 (1:G)⟩
instance instNonemptyBase : Nonempty (Base hunif) := ⟨TopologicalTower.of (B hunif) (bMap hunif) 0 PUnit.unit⟩

instance totalCW : CWComplex (univ : Set (Total hunif)) :=
  CellularTower.cwComplex _ _ (eMap_closed hunif) (Sequential.cellSystem _ _ (eCells hunif))
instance baseCW : CWComplex (univ : Set (Base hunif)) :=
  CellularTower.cwComplex _ _ (bMap_closed hunif) (Sequential.cellSystem _ _ (bCells hunif))

def pStage (n : ℕ) : C(E hunif n,B hunif n) := (stages hunif n).p
lemma p_compat (i j : ℕ) (h : i ≤ j) (x : E hunif i) :
    pStage hunif j (eMap hunif i j h x) = bMap hunif i j h (pStage hunif i x) := by
  induction j,h using Nat.le_induction with
  | base => simp only [eMap,bMap,Sequential.map_self,ContinuousMap.id_apply]
  | succ j h ih =>
    simp only [eMap,bMap,Sequential.map_succ _ _ i j h,ContinuousMap.comp_apply]
    change pStage hunif (j+1) (eStep hunif j (eMap hunif i j h x)) = bStep hunif j (bMap hunif i j h (pStage hunif i x))
    exact (next_square hunif (stages hunif j) _).trans (congrArg (bStep hunif j) ih)

def pLimit : C(Total hunif,Base hunif) :=
  TopologicalTower.limitMap _ _ _ _ (pStage hunif) (p_compat hunif)
end UniversalFInfinity.Brown

end

end OAI
end


