-- Prove2me | Definitions.Def_CompactnessAndDegeneracy
-- name    : CompactnessAndDegeneracy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-19T10:54:31.198+00:00
-- url     : https://prove2.me/theorems/dad1d6b2-480a-439d-9c05-0158bc2c1e9d
-- title:
--   CompactnessAndDegeneracy
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
set_option autoImplicit true
namespace CompactnessConjecture
noncomputable section Foundations
open Filter Finset SimpleGraph
open scoped Topology
structure FiniteGraph where
  order : ℕ
  graph : SimpleGraph (Fin order)
def FamilyFree (family : Finset FiniteGraph) {n : ℕ}
    (host : SimpleGraph (Fin n)) : Prop :=
  ∀ forbidden ∈ family, forbidden.graph.Free host
noncomputable def familyExtremal (family : Finset FiniteGraph)
    (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (FamilyFree family)).sup
    (fun host : SimpleGraph (Fin n) => host.edgeFinset.card)
def IsCyclicFamily (family : Finset FiniteGraph) : Prop :=
  ∀ forbidden ∈ family, ¬ forbidden.graph.IsAcyclic
def IsCompactFamily (family : Finset FiniteGraph) : Prop :=
  ∃ forbidden ∈ family, ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      (SimpleGraph.extremalNumber n forbidden.graph : ℝ) ≤
        C * (familyExtremal family n : ℝ)
def CompactnessConjectureStatement : Prop :=
  ∀ family : Finset FiniteGraph,
    family.Nonempty → IsCyclicFamily family → IsCompactFamily family
theorem FamilyFree.member {family : Finset FiniteGraph}
    {forbidden : FiniteGraph} (hmem : forbidden ∈ family)
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree family host) : forbidden.graph.Free host :=
  hfree forbidden hmem
end Foundations
noncomputable section DensityReduction
open Finset SimpleGraph
open scoped Classical
def booleanCut {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) : SimpleGraph V :=
  G ⊓ (⊤ : SimpleGraph Bool).comap color
@[simp]
lemma booleanCut_adj {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) (u v : V) :
    (booleanCut G color).Adj u v ↔ G.Adj u v ∧ color u ≠ color v :=
  Iff.rfl
instance booleanCutDecidableRel {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] (color : V → Bool) :
    DecidableRel (booleanCut G color).Adj :=
  inferInstanceAs
    (DecidableRel fun u v => G.Adj u v ∧ color u ≠ color v)
def flipBooleanColor {V : Type*} [DecidableEq V]
    (color : V → Bool) (v : V) : V → Bool :=
  Function.update color v (! color v)
@[simp]
lemma flipBooleanColor_self {V : Type*} [DecidableEq V]
    (color : V → Bool) (v : V) :
    flipBooleanColor color v v = ! color v := by
  simp [flipBooleanColor]
noncomputable def sharpPruningPotential {V : Type*} [Fintype V]
    (originalEdges : ℕ) (H : SimpleGraph V) : ℕ :=
  2 * Fintype.card V * Nat.card H.edgeSet +
    originalEdges * (Fintype.card V - Nat.card H.support)
noncomputable def sharpPruningScore {V : Type*} [Fintype V]
    (originalEdges : ℕ) (H : SimpleGraph V) : ℕ :=
  2 * sharpPruningPotential originalEdges H +
    (if 0 < Nat.card H.edgeSet then 1 else 0)
end DensityReduction
noncomputable section Patterns
open SimpleGraph
abbrev SubdivisionVertex (k : ℕ) :=
  (Fin 3 ⊕ Fin k) ⊕ (Fin 3 × Fin k)
def subdivisionRelation (k : ℕ) :
    SubdivisionVertex k → SubdivisionVertex k → Prop
  | .inl (.inl base), .inr (otherBase, _) => base = otherBase
  | .inl (.inr center), .inr (_, otherCenter) => center = otherCenter
  | _, _ => False
def SubdivisionGraph (k : ℕ) : SimpleGraph (SubdivisionVertex k) :=
  SimpleGraph.fromRel (subdivisionRelation k)
def subdivisionColor (k : ℕ) : SubdivisionVertex k → Bool
  | .inl _ => false
  | .inr _ => true
abbrev thetaGraph : SimpleGraph (SubdivisionVertex 2) :=
  SubdivisionGraph 2
abbrev gammaGraph : SimpleGraph (SubdivisionVertex 3) :=
  SubdivisionGraph 3
end Patterns
noncomputable section Quotients
open Finset SimpleGraph
abbrev JVertex :=
  (Fin 4 ⊕ (Fin 2 × Fin 2)) ⊕
    ((Fin 2 × (Fin 3 × Fin 2)) ⊕ Unit)
def jBase (copy : Fin 2) (base : Fin 3) : Fin 4 :=
  if base = 0 then
    if copy = 0 then 0 else 1
  else if base = 1 then 2 else 3
def jTemplateRelation : JVertex → JVertex → Prop
  | .inl (.inl base), .inr (.inl (copy, (i, _))) =>
      base = jBase copy i
  | .inl (.inr (copy, center)), .inr (.inl (copy', (_, center'))) =>
      copy = copy' ∧ center = center'
  | .inl (.inl base), .inr (.inr _) =>
      base = 0 ∨ base = 1
  | _, _ => False
def jTemplate : SimpleGraph JVertex :=
  SimpleGraph.fromRel jTemplateRelation
def jColor : JVertex → Bool
  | .inl _ => false
  | .inr _ => true
def InJCopy (copy : Fin 2) : JVertex → Prop
  | .inl (.inl base) => ∃ i : Fin 3, base = jBase copy i
  | .inl (.inr (copy', _)) => copy = copy'
  | .inr (.inl (copy', _)) => copy = copy'
  | .inr (.inr _) => False
abbrev KVertex := Fin 2 × SubdivisionVertex 3
def kSpecifiedCenter : SubdivisionVertex 3 :=
  .inl (.inr 0)
def kTemplateRelation (u v : KVertex) : Prop :=
  (u.1 = v.1 ∧ subdivisionRelation 3 u.2 v.2) ∨
    (u.1 = 0 ∧ v.1 = 1 ∧
      u.2 = kSpecifiedCenter ∧ v.2 = kSpecifiedCenter)
def kTemplate : SimpleGraph KVertex :=
  SimpleGraph.fromRel kTemplateRelation
def kColor (v : KVertex) : Bool :=
  if v.1 = 0 then subdivisionColor 3 v.2
  else !(subdivisionColor 3 v.2)
def ColorRespecting {α : Type*}
    (color : α → Bool) (f : α → α) : Prop :=
  ∀ u v, f u = f v → color u = color v
def JAdmissible (f : JVertex → JVertex) : Prop :=
  ColorRespecting jColor f ∧
    Function.Injective
      (fun base : Fin 4 => f (.inl (.inl base))) ∧
    ∀ copy : Fin 2, Set.InjOn f {v | InJCopy copy v}
def KAdmissible (f : KVertex → KVertex) : Prop :=
  ColorRespecting kColor f ∧
    ∀ copy : Fin 2,
      Set.InjOn f {v : KVertex | v.1 = copy}
def quotientRelation {α : Type*}
    (graph : SimpleGraph α) (f : α → α)
    (u v : Set.range f) : Prop :=
  ∃ x y : α, f x = (u : α) ∧ f y = (v : α) ∧ graph.Adj x y
def quotientGraph {α : Type*}
    (graph : SimpleGraph α) (f : α → α) :
    SimpleGraph (Set.range f) :=
  SimpleGraph.fromRel (quotientRelation graph f)
noncomputable def encodeFiniteGraph {α : Type*} [Fintype α]
    (graph : SimpleGraph α) : FiniteGraph :=
  ⟨Fintype.card α,
    graph.map (Fintype.equivFin α).toEmbedding⟩
noncomputable def jQuotients : Finset FiniteGraph :=
  (Set.finite_range
    (fun f : {f : JVertex → JVertex // JAdmissible f} =>
      encodeFiniteGraph
        (quotientGraph jTemplate (f : JVertex → JVertex)))).toFinset
noncomputable def kQuotients : Finset FiniteGraph :=
  (Set.finite_range
    (fun f : {f : KVertex → KVertex // KAdmissible f} =>
      encodeFiniteGraph
        (quotientGraph kTemplate (f : KVertex → KVertex)))).toFinset
def finiteCycle (n : ℕ) : FiniteGraph :=
  ⟨n, SimpleGraph.cycleGraph n⟩
noncomputable def proposedFamily : Finset FiniteGraph := by
  classical
  exact {finiteCycle 4, finiteCycle 6} ∪ jQuotients ∪ kQuotients
end Quotients
noncomputable section Geometry
open SimpleGraph
section SymplecticGeometry
variable (K : Type*) [Field K]
abbrev SymplecticVector := Fin 4 → K
def standardSymplecticForm
    (u v : SymplecticVector K) : K :=
  u 0 * v 1 - u 1 * v 0 +
    (u 2 * v 3 - u 3 * v 2)
theorem standardSymplecticForm_self
    (u : SymplecticVector K) :
    standardSymplecticForm K u u = 0 := by
  unfold standardSymplecticForm
  ring
lemma standardSymplecticForm_swap
    (u v : SymplecticVector K) :
    standardSymplecticForm K u v =
      -standardSymplecticForm K v u := by
  unfold standardSymplecticForm
  ring
lemma standardSymplecticForm_add_left
    (u v w : SymplecticVector K) :
    standardSymplecticForm K (u + v) w =
      standardSymplecticForm K u w + standardSymplecticForm K v w := by
  simp only [standardSymplecticForm, Pi.add_apply]
  ring
lemma standardSymplecticForm_add_right
    (u v w : SymplecticVector K) :
    standardSymplecticForm K u (v + w) =
      standardSymplecticForm K u v + standardSymplecticForm K u w := by
  simp only [standardSymplecticForm, Pi.add_apply]
  ring
lemma standardSymplecticForm_smul_left
    (a : K) (u v : SymplecticVector K) :
    standardSymplecticForm K (a • u) v =
      a * standardSymplecticForm K u v := by
  simp only [standardSymplecticForm, Pi.smul_apply, smul_eq_mul]
  ring
lemma standardSymplecticForm_smul_right
    (a : K) (u v : SymplecticVector K) :
    standardSymplecticForm K u (a • v) =
      a * standardSymplecticForm K u v := by
  simp only [standardSymplecticForm, Pi.smul_apply, smul_eq_mul]
  ring
theorem standardSymplecticForm_nondegenerate_left
    (u : SymplecticVector K)
    (h : ∀ v : SymplecticVector K,
      standardSymplecticForm K u v = 0) : u = 0 := by
  funext i
  fin_cases i
  · simpa [standardSymplecticForm] using h ![0, 1, 0, 0]
  · simpa [standardSymplecticForm] using h ![1, 0, 0, 0]
  · simpa [standardSymplecticForm] using h ![0, 0, 0, 1]
  · simpa [standardSymplecticForm] using h ![0, 0, 1, 0]
theorem standardSymplecticForm_nondegenerate_right
    (u : SymplecticVector K)
    (h : ∀ v : SymplecticVector K,
      standardSymplecticForm K v u = 0) : u = 0 := by
  apply standardSymplecticForm_nondegenerate_left K u
  intro v
  rw [standardSymplecticForm_swap, h v, neg_zero]
def standardSymplecticBilin :
    LinearMap.BilinForm K (SymplecticVector K) :=
  LinearMap.mk₂ K (standardSymplecticForm K)
    (standardSymplecticForm_add_left K)
    (fun a u v => by
      simpa [smul_eq_mul] using standardSymplecticForm_smul_left K a u v)
    (standardSymplecticForm_add_right K)
    (fun a u v => by
      simpa [smul_eq_mul] using standardSymplecticForm_smul_right K a u v)
theorem standardSymplecticBilin_nondegenerate :
    (standardSymplecticBilin K).Nondegenerate := by
  constructor
  · intro u hu
    exact standardSymplecticForm_nondegenerate_left K u hu
  · intro u hu
    exact standardSymplecticForm_nondegenerate_right K u hu
abbrev SymplecticPoint :=
  {P : Submodule K (SymplecticVector K) //
    Module.finrank K P = 1}
abbrev SymplecticLine :=
  {L : Submodule K (SymplecticVector K) //
    Module.finrank K L = 2 ∧
      ∀ u ∈ L, ∀ v ∈ L, standardSymplecticForm K u v = 0}
abbrev SymplecticPointOrthogonal (p : SymplecticPoint K) :=
  (standardSymplecticBilin K).orthogonal p.1
lemma symplecticPoint_le_orthogonal (p : SymplecticPoint K) :
    p.1 ≤ SymplecticPointOrthogonal K p := by
  intro x hx
  change ∀ y ∈ p.1, standardSymplecticForm K y x = 0
  intro y hy
  by_cases hx0 : x = 0
  · simp [hx0, standardSymplecticForm]
  · have hxsub : (⟨x, hx⟩ : p.1) ≠ 0 := by
      intro h
      apply hx0
      simpa using congrArg Subtype.val h
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
      p.2 hxsub (⟨y, hy⟩ : p.1)
    have hav : a • x = y := congrArg Subtype.val ha
    rw [← hav, standardSymplecticForm_smul_left,
      standardSymplecticForm_self, mul_zero]
abbrev SymplecticPointRadical (p : SymplecticPoint K) :
    Submodule K (SymplecticPointOrthogonal K p) :=
  Submodule.comap (SymplecticPointOrthogonal K p).subtype p.1
lemma symplecticPointRadical_finrank
    (p : SymplecticPoint K) :
    Module.finrank K (SymplecticPointRadical K p) = 1 := by
  exact (Submodule.comapSubtypeEquivOfLe
    (symplecticPoint_le_orthogonal K p)).finrank_eq.trans p.2
abbrev SymplecticPointQuotient (p : SymplecticPoint K) :=
  (SymplecticPointOrthogonal K p) ⧸ (SymplecticPointRadical K p)
lemma quotient_map_finrank
    {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W]
    (R S : Submodule K W) (hRS : R ≤ S) :
    Module.finrank K (Submodule.map R.mkQ S) +
      Module.finrank K R = Module.finrank K S := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (R.mkQ.domRestrict S)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe hRS).finrank_eq] at h
  exact h
lemma symplecticLine_le_pointOrthogonal
    {p : SymplecticPoint K} {L : SymplecticLine K}
    (hpL : p.1 ≤ L.1) : L.1 ≤ SymplecticPointOrthogonal K p := by
  intro x hx
  change ∀ y ∈ p.1, standardSymplecticForm K y x = 0
  intro y hy
  exact L.2.2 y (hpL hy) x hx
lemma symplectic_two_plane_isotropic
    {p : SymplecticPoint K}
    {S : Submodule K (SymplecticVector K)}
    (hdim : Module.finrank K S = 2)
    (hpS : p.1 ≤ S)
    (hSorth : S ≤ SymplecticPointOrthogonal K p) :
    ∀ u ∈ S, ∀ v ∈ S, standardSymplecticForm K u v = 0 := by
  intro u hu v hv
  by_cases huP : u ∈ p.1
  · exact hSorth hv u huP
  · have hle : p.1 ⊔ K ∙ u ≤ S := by
      apply sup_le hpS
      exact (Submodule.span_le).mpr (by simpa using hu)
    have hspan : p.1 ⊔ K ∙ u = S :=
      Submodule.eq_of_le_of_finrank_eq hle (by
        rw [Submodule.finrank_sup_span_singleton huP, p.2, hdim])
    have hvspan : v ∈ p.1 ⊔ K ∙ u := hspan.symm ▸ hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hvspan
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have horth : standardSymplecticForm K a u = 0 :=
      hSorth hu a ha
    have hreverse : standardSymplecticForm K u a = 0 := by
      rw [standardSymplecticForm_swap, horth, neg_zero]
    rw [standardSymplecticForm_add_right,
      standardSymplecticForm_smul_right,
      standardSymplecticForm_self,
      hreverse, mul_zero, add_zero]
abbrev SymplecticLinesOnPoint (p : SymplecticPoint K) :=
  {L : SymplecticLine K // p.1 ≤ L.1}
abbrev SymplecticLineInPointOrthogonal
    (p : SymplecticPoint K) (L : SymplecticLine K) :
    Submodule K (SymplecticPointOrthogonal K p) :=
  Submodule.comap (SymplecticPointOrthogonal K p).subtype L.1
lemma symplecticLineInPointOrthogonal_finrank
    {p : SymplecticPoint K} {L : SymplecticLine K}
    (hpL : p.1 ≤ L.1) :
    Module.finrank K (SymplecticLineInPointOrthogonal K p L) = 2 := by
  exact (Submodule.comapSubtypeEquivOfLe
    (symplecticLine_le_pointOrthogonal K hpL)).finrank_eq.trans L.2.1
lemma symplecticPointRadical_le_lineInPointOrthogonal
    {p : SymplecticPoint K} {L : SymplecticLine K}
    (hpL : p.1 ≤ L.1) :
    SymplecticPointRadical K p ≤
      SymplecticLineInPointOrthogonal K p L :=
  Submodule.comap_mono hpL
noncomputable def symplecticLinesOnPointEquivSubmodule
    (p : SymplecticPoint K) :
    SymplecticLinesOnPoint K p ≃
      {S : Submodule K (SymplecticPointQuotient K p) //
        Module.finrank K S = 1} where
  toFun L :=
    ⟨Submodule.map (SymplecticPointRadical K p).mkQ
       (SymplecticLineInPointOrthogonal K p L.1), by
       change Module.finrank K
         (Submodule.map (SymplecticPointRadical K p).mkQ
           (SymplecticLineInPointOrthogonal K p L.1)) = 1
       have h := quotient_map_finrank K
         (SymplecticPointRadical K p)
         (SymplecticLineInPointOrthogonal K p L.1)
         (symplecticPointRadical_le_lineInPointOrthogonal K L.2)
       rw [symplecticPointRadical_finrank K p,
         symplecticLineInPointOrthogonal_finrank K L.2] at h
       omega⟩
  invFun Q := by
    let T : Submodule K (SymplecticPointOrthogonal K p) :=
      Submodule.comap (SymplecticPointRadical K p).mkQ Q.1
    have hrad : SymplecticPointRadical K p ≤ T :=
      Submodule.le_comap_mkQ (SymplecticPointRadical K p) Q.1
    have hmap :
        Submodule.map (SymplecticPointRadical K p).mkQ T = Q.1 := by
      apply Submodule.map_comap_eq_self
      rw [Submodule.range_mkQ]
      exact le_top
    have hdimT : Module.finrank K T = 2 := by
      have h := quotient_map_finrank K
        (SymplecticPointRadical K p) T hrad
      rw [hmap, Q.2, symplecticPointRadical_finrank K p] at h
      omega
    let S : Submodule K (SymplecticVector K) :=
      Submodule.map (SymplecticPointOrthogonal K p).subtype T
    have hdimS : Module.finrank K S = 2 := by
      exact (Submodule.finrank_map_subtype_eq
        (SymplecticPointOrthogonal K p) T).trans hdimT
    have hSorth : S ≤ SymplecticPointOrthogonal K p := by
      intro x hx
      rcases hx with ⟨y, _, rfl⟩
      exact y.2
    have hpS : p.1 ≤ S := by
      intro x hx
      have hxorth : x ∈ SymplecticPointOrthogonal K p :=
        symplecticPoint_le_orthogonal K p hx
      have hxrad :
          (⟨x, hxorth⟩ : SymplecticPointOrthogonal K p) ∈
            SymplecticPointRadical K p := hx
      exact ⟨⟨x, hxorth⟩, hrad hxrad, rfl⟩
    exact ⟨⟨S, hdimS,
      symplectic_two_plane_isotropic K hdimS hpS hSorth⟩, hpS⟩
  left_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    change Submodule.map (SymplecticPointOrthogonal K p).subtype
      (Submodule.comap (SymplecticPointRadical K p).mkQ
        (Submodule.map (SymplecticPointRadical K p).mkQ
          (SymplecticLineInPointOrthogonal K p L.1))) = L.1.1
    rw [Submodule.comap_map_mkQ,
      sup_eq_right.mpr
        (symplecticPointRadical_le_lineInPointOrthogonal K L.2)]
    change Submodule.map (SymplecticPointOrthogonal K p).subtype
      (Submodule.comap (SymplecticPointOrthogonal K p).subtype
        L.1.1) = L.1.1
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr
      (symplecticLine_le_pointOrthogonal K L.2)
  right_inv Q := by
    apply Subtype.ext
    change Submodule.map (SymplecticPointRadical K p).mkQ
      (Submodule.comap (SymplecticPointOrthogonal K p).subtype
        (Submodule.map (SymplecticPointOrthogonal K p).subtype
          (Submodule.comap (SymplecticPointRadical K p).mkQ
            Q.1))) = Q.1
    rw [Submodule.comap_map_eq,
      LinearMap.ker_eq_bot.mpr
        (SymplecticPointOrthogonal K p).subtype_injective,
      sup_bot_eq]
    apply Submodule.map_comap_eq_self
    rw [Submodule.range_mkQ]
    exact le_top
noncomputable def symplecticLinesOnPointEquiv
    (p : SymplecticPoint K) :
    SymplecticLinesOnPoint K p ≃
      Projectivization K (SymplecticPointQuotient K p) :=
  (symplecticLinesOnPointEquivSubmodule K p).trans
    (Projectivization.equivSubmodule K
      (SymplecticPointQuotient K p)).symm
abbrev SymplecticPointsOnLine (L : SymplecticLine K) :=
  {p : SymplecticPoint K // p.1 ≤ L.1}
noncomputable def symplecticPointsOnLineEquivSubmodule
    (L : SymplecticLine K) :
    SymplecticPointsOnLine K L ≃
      {S : Submodule K L.1 // Module.finrank K S = 1} where
  toFun p :=
    ⟨Submodule.comap L.1.subtype p.1.1,
      (Submodule.comapSubtypeEquivOfLe p.2).finrank_eq.trans p.1.2⟩
  invFun S :=
    ⟨⟨Submodule.map L.1.subtype S.1,
       (Submodule.finrank_map_subtype_eq L.1 S.1).trans S.2⟩,
      by
        intro x hx
        rcases hx with ⟨y, _, rfl⟩
        exact y.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    change Submodule.map L.1.subtype
      (Submodule.comap L.1.subtype p.1.1) = p.1.1
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr p.2
  right_inv S := by
    apply Subtype.ext
    change Submodule.comap L.1.subtype
      (Submodule.map L.1.subtype S.1) = S.1
    rw [Submodule.comap_map_eq,
      LinearMap.ker_eq_bot.mpr L.1.subtype_injective, sup_bot_eq]
noncomputable def symplecticPointsOnLineEquiv
    (L : SymplecticLine K) :
    SymplecticPointsOnLine K L ≃ Projectivization K L.1 :=
  (symplecticPointsOnLineEquivSubmodule K L).trans
    (Projectivization.equivSubmodule K L.1).symm
abbrev QuadrangleVertex :=
  SymplecticPoint K ⊕ SymplecticLine K
def quadrangleIncidence :
    QuadrangleVertex K → QuadrangleVertex K → Prop
  | .inl point, .inr line => (point.1 : Submodule K _) ≤ line.1
  | _, _ => False
def symplecticQuadrangle : SimpleGraph (QuadrangleVertex K) :=
  SimpleGraph.fromRel (quadrangleIncidence K)
theorem symplecticQuadrangle_incidence_adj
    (p : SymplecticPoint K) (L : SymplecticLine K) :
    (symplecticQuadrangle K).Adj (.inl p) (.inr L) ↔ p.1 ≤ L.1 := by
  simp [symplecticQuadrangle, SimpleGraph.fromRel_adj, quadrangleIncidence]
abbrev SymplecticIncidence :=
  {x : SymplecticPoint K × SymplecticLine K // x.1.1 ≤ x.2.1}
def symplecticIncidenceEquivSigmaPoints :
    SymplecticIncidence K ≃
      (Σ p : SymplecticPoint K, SymplecticLinesOnPoint K p) where
  toFun i := ⟨i.1.1, ⟨i.1.2, i.2⟩⟩
  invFun s := ⟨(s.1, s.2.1), s.2.2⟩
  left_inv i := by
    rcases i with ⟨⟨p, L⟩, h⟩
    rfl
  right_inv s := by
    rcases s with ⟨p, ⟨L, h⟩⟩
    rfl
def symplecticIncidenceEquivSigmaLines :
    SymplecticIncidence K ≃
      (Σ L : SymplecticLine K, SymplecticPointsOnLine K L) where
  toFun i := ⟨i.1.2, ⟨i.1.1, i.2⟩⟩
  invFun s := ⟨(s.2.1, s.1), s.2.2⟩
  left_inv i := by
    rcases i with ⟨⟨p, L⟩, h⟩
    rfl
  right_inv s := by
    rcases s with ⟨L, ⟨p, h⟩⟩
    rfl
def symplecticIncidenceToEdge :
    SymplecticIncidence K → (symplecticQuadrangle K).edgeSet :=
  fun i =>
    ⟨s(Sum.inl i.1.1, Sum.inr i.1.2),
      (symplecticQuadrangle_incidence_adj K i.1.1 i.1.2).mpr i.2⟩
lemma symplecticIncidenceToEdge_injective :
    Function.Injective (symplecticIncidenceToEdge K) := by
  intro i j h
  have hedges := congrArg Subtype.val h
  change s(Sum.inl i.1.1, Sum.inr i.1.2) =
    s(Sum.inl j.1.1, Sum.inr j.1.2) at hedges
  rcases Sym2.eq_iff.mp hedges with ⟨hp, hL⟩ | ⟨hbad, _⟩
  · apply Subtype.ext
    apply Prod.ext
    · exact Sum.inl_injective hp
    · exact Sum.inr_injective hL
  · cases hbad
lemma symplecticIncidenceToEdge_surjective :
    Function.Surjective (symplecticIncidenceToEdge K) := by
  intro e
  obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective e.1
  change s(u, v) = e.1 at huv
  have hadj : (symplecticQuadrangle K).Adj u v := by
    apply (symplecticQuadrangle K).mem_edgeSet.mp
    rw [huv]
    exact e.2
  rcases u with p | L <;> rcases v with q | M
  · simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at hadj
  · refine ⟨⟨(p, M),
        (symplecticQuadrangle_incidence_adj K p M).mp hadj⟩, ?_⟩
    apply Subtype.ext
    exact huv
  · refine ⟨⟨(q, L),
        (symplecticQuadrangle_incidence_adj K q L).mp hadj.symm⟩, ?_⟩
    apply Subtype.ext
    exact Sym2.eq_swap.trans huv
  · simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at hadj
noncomputable def symplecticIncidenceEquivEdge :
    SymplecticIncidence K ≃ (symplecticQuadrangle K).edgeSet :=
  Equiv.ofBijective (symplecticIncidenceToEdge K)
    ⟨symplecticIncidenceToEdge_injective K,
      symplecticIncidenceToEdge_surjective K⟩
end SymplecticGeometry
section NumericalParameters
def quadrangleVertexCount (q : ℕ) : ℕ :=
  2 * (q + 1) * (q ^ 2 + 1)
def quadrangleEdgeCount (q : ℕ) : ℕ :=
  (q + 1) ^ 2 * (q ^ 2 + 1)
end NumericalParameters
end Geometry
noncomputable section Cyclicity
open Finset SimpleGraph
def thetaCycleVertex : Fin 8 → SubdivisionVertex 2 :=
  ![.inl (.inl 0),
    .inr (0, 0),
    .inl (.inr 0),
    .inr (1, 0),
    .inl (.inl 1),
    .inr (1, 1),
    .inl (.inr 1),
    .inr (0, 1)]
def thetaCycleCopy :
    SimpleGraph.Copy (SimpleGraph.cycleGraph 8) thetaGraph := by
  refine ⟨⟨thetaCycleVertex, ?_⟩, ?_⟩
  · intro u v hadj
    fin_cases u <;> fin_cases v <;>
      simp_all [thetaCycleVertex, SubdivisionGraph,
        subdivisionRelation, SimpleGraph.cycleGraph]
    all_goals
      exact (of_decide_eq_false rfl) hadj
  · decide
def jThetaVertex (copy : Fin 2) : SubdivisionVertex 2 → JVertex
  | .inl (.inl base) => .inl (.inl (jBase copy base))
  | .inl (.inr center) => .inl (.inr (copy, center))
  | .inr (base, center) => .inr (.inl (copy, (base, center)))
def jThetaCopy (copy : Fin 2) :
    SimpleGraph.Copy thetaGraph jTemplate := by
  refine ⟨⟨jThetaVertex copy, ?_⟩, ?_⟩
  · intro u v hadj
    rcases (SimpleGraph.fromRel_adj
      (subdivisionRelation 2) u v).mp hadj with
      ⟨hne, hforward | hbackward⟩
    · apply (SimpleGraph.fromRel_adj
        jTemplateRelation (jThetaVertex copy u)
        (jThetaVertex copy v)).mpr
      constructor
      · intro heq
        have hinj : Function.Injective (jThetaVertex copy) := by
          fin_cases copy <;> decide
        exact hne (hinj heq)
      · left
        rcases u with (u | u) | u <;>
          rcases v with (v | v) | v <;>
          simp_all [subdivisionRelation, jTemplateRelation, jThetaVertex]
    · apply (SimpleGraph.fromRel_adj
        jTemplateRelation (jThetaVertex copy u)
        (jThetaVertex copy v)).mpr
      constructor
      · intro heq
        have hinj : Function.Injective (jThetaVertex copy) := by
          fin_cases copy <;> decide
        exact hne (hinj heq)
      · right
        rcases u with (u | u) | u <;>
          rcases v with (v | v) | v <;>
          simp_all [subdivisionRelation, jTemplateRelation, jThetaVertex]
  · fin_cases copy <;> decide
lemma jThetaVertex_mem (copy : Fin 2)
    (v : SubdivisionVertex 2) :
    InJCopy copy (jThetaVertex copy v) := by
  rcases v with (base | center) | pair
  · exact ⟨base, rfl⟩
  · simp [InJCopy, jThetaVertex]
  · simp [InJCopy, jThetaVertex]
def gammaCycleVertex : Fin 8 → SubdivisionVertex 3 :=
  ![.inl (.inl 0),
    .inr (0, 0),
    .inl (.inr 0),
    .inr (1, 0),
    .inl (.inl 1),
    .inr (1, 1),
    .inl (.inr 1),
    .inr (0, 1)]
def gammaCycleCopy :
    SimpleGraph.Copy (SimpleGraph.cycleGraph 8) gammaGraph := by
  refine ⟨⟨gammaCycleVertex, ?_⟩, ?_⟩
  · intro u v hadj
    fin_cases u <;> fin_cases v <;>
      simp_all [gammaCycleVertex, SubdivisionGraph,
        subdivisionRelation, SimpleGraph.cycleGraph]
    all_goals
      exact (of_decide_eq_false rfl) hadj
  · decide
def kGammaVertex (copy : Fin 2)
    (v : SubdivisionVertex 3) : KVertex := (copy, v)
def kGammaCopy (copy : Fin 2) :
    SimpleGraph.Copy gammaGraph kTemplate := by
  refine ⟨⟨kGammaVertex copy, ?_⟩, ?_⟩
  · intro u v hadj
    rcases (SimpleGraph.fromRel_adj
      (subdivisionRelation 3) u v).mp hadj with
      ⟨hne, hforward | hbackward⟩
    · apply (SimpleGraph.fromRel_adj
        kTemplateRelation (kGammaVertex copy u)
        (kGammaVertex copy v)).mpr
      constructor
      · intro heq
        exact hne (congrArg Prod.snd heq)
      · left
        exact Or.inl ⟨rfl, hforward⟩
    · apply (SimpleGraph.fromRel_adj
        kTemplateRelation (kGammaVertex copy u)
        (kGammaVertex copy v)).mpr
      constructor
      · intro heq
        exact hne (congrArg Prod.snd heq)
      · right
        exact Or.inl ⟨rfl, hbackward⟩
  · intro u v h
    exact congrArg Prod.snd h
def copyToQuotient {α β : Type*}
    (source : SimpleGraph β) (target : SimpleGraph α)
    (f : α → α) (copy : SimpleGraph.Copy source target)
    (hinj : Function.Injective (fun v : β => f (copy v))) :
    SimpleGraph.Copy source (quotientGraph target f) := by
  refine ⟨⟨fun v => ⟨f (copy v), ⟨copy v, rfl⟩⟩, ?_⟩, ?_⟩
  · intro u v hadj
    apply (SimpleGraph.fromRel_adj
      (quotientRelation target f) _ _).mpr
    constructor
    · intro heq
      exact hadj.ne (hinj (congrArg Subtype.val heq))
    · left
      exact ⟨copy u, copy v, rfl, rfl, copy.toHom.map_rel hadj⟩
  · intro u v heq
    exact hinj (congrArg Subtype.val heq)
end Cyclicity
noncomputable section CharacteristicAvoidance
open SimpleGraph
section PointClass
variable (K : Type*) [Field K]
def SymplecticPointRelated (p q : SymplecticPoint K) : Prop :=
  p ≠ q ∧ ∃ L : SymplecticLine K, p.1 ≤ L.1 ∧ q.1 ≤ L.1
def colorRespectingQuotientProjectionHom
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (f : V → V) (hf : ColorRespecting color f) :
    graph →g quotientGraph graph f := by
  refine ⟨fun v => ⟨f v, v, rfl⟩, ?_⟩
  intro u v hadj
  apply (SimpleGraph.fromRel_adj
    (quotientRelation graph f)
    (⟨f u, u, rfl⟩ : Set.range f)
    (⟨f v, v, rfl⟩ : Set.range f)).mpr
  constructor
  · intro heq
    exact hproper hadj
      (hf u v (congrArg Subtype.val heq))
  · left
    exact ⟨u, v, rfl, rfl, hadj⟩
lemma jTemplate_adj_color_ne
    {u v : JVertex} (h : jTemplate.Adj u v) :
    jColor u ≠ jColor v := by
  rcases u with (u | u) | (u | u) <;>
    rcases v with (v | v) | (v | v) <;>
    simp_all [jTemplate, SimpleGraph.fromRel_adj,
      jTemplateRelation, jColor]
lemma kTemplate_adj_color_ne
    {u v : KVertex} (h : kTemplate.Adj u v) :
    kColor u ≠ kColor v := by
  rcases u with ⟨u, (u | u) | u⟩ <;>
    rcases v with ⟨v, (v | v) | v⟩ <;>
    fin_cases u <;> fin_cases v <;>
    simp_all [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, kColor, subdivisionColor,
      subdivisionRelation, kSpecifiedCenter]
  all_goals aesop
def jQuotientProjectionHom
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    jTemplate →g quotientGraph jTemplate f :=
  colorRespectingQuotientProjectionHom jTemplate jColor
    (fun _ _ h => jTemplate_adj_color_ne h) f hf.1
def kQuotientProjectionHom
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    kTemplate →g quotientGraph kTemplate f :=
  colorRespectingQuotientProjectionHom kTemplate kColor
    (fun _ _ h => kTemplate_adj_color_ne h) f hf.1
def jThetaHomCopy
    {V : Type*} {host : SimpleGraph V}
    (hom : jTemplate →g host)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (copy : Fin 2) :
    SimpleGraph.Copy thetaGraph host := by
  refine ⟨hom.comp (jThetaCopy copy).toHom, ?_⟩
  intro u v huv
  change hom (jThetaVertex copy u) =
    hom (jThetaVertex copy v) at huv
  apply (jThetaCopy copy).injective
  exact hcopies copy (jThetaVertex_mem copy u)
    (jThetaVertex_mem copy v) huv
def kGammaHomCopy
    {V : Type*} {host : SimpleGraph V}
    (hom : kTemplate →g host)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = copy})
    (copy : Fin 2) :
    SimpleGraph.Copy gammaGraph host := by
  refine ⟨hom.comp (kGammaCopy copy).toHom, ?_⟩
  intro u v huv
  change hom (kGammaVertex copy u) =
    hom (kGammaVertex copy v) at huv
  apply (kGammaCopy copy).injective
  exact hcopies copy (show (kGammaVertex copy u).1 = copy from rfl)
    (show (kGammaVertex copy v).1 = copy from rfl) huv
end PointClass
end CharacteristicAvoidance
noncomputable section SubdivisionLineExtraction
open SimpleGraph
variable (K : Type*) [Field K]
end SubdivisionLineExtraction
noncomputable section Padding
open SimpleGraph
def GraphHasNoIsolated {V : Type*} (graph : SimpleGraph V) : Prop :=
  ∀ u : V, ∃ v : V, graph.Adj u v
end Padding
noncomputable section LocalGeometry
open SimpleGraph
theorem common_neighbor_unique_of_four_cycle_free
    {V : Type*} {G : SimpleGraph V}
    (hfree : (SimpleGraph.cycleGraph 4).Free G)
    {u v x y : V} (huv : u ≠ v)
    (hux : G.Adj u x) (hvx : G.Adj v x)
    (huy : G.Adj u y) (hvy : G.Adj v y) : x = y := by
  by_contra hxy
  apply hfree
  let f : Fin 4 → V := ![u, x, v, y]
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, SimpleGraph.cycleGraph]
    all_goals
      first
      | exact hux.symm
      | exact hvx.symm
      | exact huy.symm
      | exact hvy.symm
      | exact False.elim ((of_decide_eq_false rfl) hij)
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, hux.ne, hux.symm.ne, hvx.ne, hvx.symm.ne,
        huy.ne, huy.symm.ne, hvy.ne, hvy.symm.ne]
def CommonNeighborRelated {V : Type*} (G : SimpleGraph V)
    (u v : V) : Prop :=
  u ≠ v ∧ ∃ w : V, G.Adj u w ∧ G.Adj v w
lemma commonNeighborRelated_symm
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : CommonNeighborRelated G u v) :
    CommonNeighborRelated G v u := by
  obtain ⟨hne, w, huw, hvw⟩ := h
  exact ⟨hne.symm, w, hvw, huw⟩
lemma bipartite_coloring_eq_of_common_neighbor
    {V : Type*} {G : SimpleGraph V}
    (color : G.Coloring (Fin 2)) {u v w : V}
    (huw : G.Adj u w) (hvw : G.Adj v w) :
    color u = color v := by
  have hu := color.valid huw
  have hv := color.valid hvw
  apply Fin.ext
  omega
theorem common_neighbors_triangle_eq_of_cycle_free
    {V : Type*} {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u v w a b c : V}
    (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (hua : G.Adj u a) (hva : G.Adj v a)
    (hvb : G.Adj v b) (hwb : G.Adj w b)
    (hwc : G.Adj w c) (huc : G.Adj u c) :
    a = b ∧ b = c := by
  by_cases hab : a = b
  · subst b
    refine ⟨rfl, ?_⟩
    exact common_neighbor_unique_of_four_cycle_free hfour huw
      hua hwb huc hwc
  by_cases hbc : b = c
  · subst c
    have hac : a = b :=
      common_neighbor_unique_of_four_cycle_free hfour huv
        hua hva huc hvb
    exact (hab hac).elim
  by_cases hac : a = c
  · subst c
    have hab' : a = b :=
      common_neighbor_unique_of_four_cycle_free hfour hvw
        hva hwc hvb hwb
    exact (hab hab').elim
  obtain ⟨color⟩ := hbip
  have hcolor_uv : color u = color v :=
    bipartite_coloring_eq_of_common_neighbor color hua hva
  have hcolor_vw : color v = color w :=
    bipartite_coloring_eq_of_common_neighbor color hvb hwb
  have hub : u ≠ b := by
    intro h
    subst b
    exact color.valid hvb hcolor_uv.symm
  have hvc : v ≠ c := by
    intro h
    subst c
    exact color.valid huc hcolor_uv
  have hwa : w ≠ a := by
    intro h
    subst a
    exact color.valid hva hcolor_vw
  exfalso
  apply hsix
  let f : Fin 6 → V := ![u, a, v, b, w, c]
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, SimpleGraph.cycleGraph]
    all_goals
      first
      | exact hua
      | exact hua.symm
      | exact hva
      | exact hva.symm
      | exact hvb
      | exact hvb.symm
      | exact hwb
      | exact hwb.symm
      | exact hwc
      | exact hwc.symm
      | exact huc
      | exact huc.symm
      | exact False.elim ((of_decide_eq_false rfl) hij)
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, huv, huv.symm, hvw, hvw.symm, huw, huw.symm,
        hab, Ne.symm hab, hbc, Ne.symm hbc, hac, Ne.symm hac,
        hua.ne, hua.symm.ne, hva.ne, hva.symm.ne,
        hvb.ne, hvb.symm.ne, hwb.ne, hwb.symm.ne,
        hwc.ne, hwc.symm.ne, huc.ne, huc.symm.ne,
        hub, hub.symm, hvc, hvc.symm, hwa, hwa.symm] at hij ⊢
theorem common_second_neighbors_pairwise_unrelated
    {V : Type*} {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u v x y : V} (huv : u ≠ v)
    (hunrelated : ¬ CommonNeighborRelated G u v)
    (hxu : CommonNeighborRelated G x u)
    (hxv : CommonNeighborRelated G x v)
    (hyu : CommonNeighborRelated G y u)
    (hyv : CommonNeighborRelated G y v) :
    ¬ CommonNeighborRelated G x y := by
  rintro ⟨hxy, b, hxb, hyb⟩
  obtain ⟨hxu_ne, a, hxa, hua⟩ := hxu
  obtain ⟨hxv_ne, d, hxd, hvd⟩ := hxv
  obtain ⟨hyu_ne, c, hyc, huc⟩ := hyu
  obtain ⟨hyv_ne, e, hye, hve⟩ := hyv
  have habc : a = c ∧ c = b :=
    common_neighbors_triangle_eq_of_cycle_free hbip hfour hsix
      hxu_ne (Ne.symm hyu_ne) hxy
      hxa hua huc hyc hyb hxb
  have hdeb : d = e ∧ e = b :=
    common_neighbors_triangle_eq_of_cycle_free hbip hfour hsix
      hxv_ne (Ne.symm hyv_ne) hxy
      hxd hvd hve hye hyb hxb
  apply hunrelated
  refine ⟨huv, b, ?_, ?_⟩
  · rwa [habc.1.trans habc.2] at hua
  · rwa [hdeb.1.trans hdeb.2] at hvd
section FourPathCounting
variable {V : Type*} [Fintype V] [DecidableEq V]
abbrev NonbacktrackingNeighbor (G : SimpleGraph V)
    (previous current : V) :=
  {next : V // G.Adj current next ∧ next ≠ previous}
abbrev NonbacktrackingFourPath (G : SimpleGraph V) (u : V) :=
  Σ a : G.neighborSet u,
    Σ w : NonbacktrackingNeighbor G u (a : V),
      Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
        NonbacktrackingNeighbor G (w : V) (b : V)
def nonbacktrackingFourPathPair
    (G : SimpleGraph V) {u : V}
    (path : NonbacktrackingFourPath G u) : V × V :=
  (path.2.2.2.1, path.2.1.1)
omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPath_endpoint_ne
    (G : SimpleGraph V)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    {u : V} (path : NonbacktrackingFourPath G u) :
    u ≠ (nonbacktrackingFourPathPair G path).1 := by
  rcases path with ⟨a, w, b, v⟩
  change u ≠ (v : V)
  intro huv
  have hub : G.Adj u (b : V) := by
    simpa only [huv] using v.property.1.symm
  have hab : (a : V) = (b : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      w.property.2.symm a.property w.property.1.symm
      hub b.property.1
  exact b.property.2 hab.symm
omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPath_endpoint_unrelated
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} (path : NonbacktrackingFourPath G u) :
    ¬ CommonNeighborRelated G u
      (nonbacktrackingFourPathPair G path).1 := by
  rcases path with ⟨a, w, b, v⟩
  change ¬ CommonNeighborRelated G u (v : V)
  rintro ⟨_, c, huc, hvc⟩
  have huv : u ≠ (v : V) :=
    nonbacktrackingFourPath_endpoint_ne G hfour
      ⟨a, w, b, v⟩
  have hab := common_neighbors_triangle_eq_of_cycle_free
    hbip hfour hsix w.property.2.symm
    v.property.2.symm huv
    a.property w.property.1.symm
    b.property.1 v.property.1.symm hvc huc
  exact b.property.2 hab.1.symm
abbrev FourPathEndpointWitness (G : SimpleGraph V) (u : V) :=
  {pair : V × V //
    u ≠ pair.1 ∧
      ¬ CommonNeighborRelated G u pair.1 ∧
      CommonNeighborRelated G u pair.2 ∧
      CommonNeighborRelated G pair.1 pair.2}
noncomputable instance fourPathEndpointWitnessFintype
    (G : SimpleGraph V) (u : V) :
    Fintype (FourPathEndpointWitness G u) :=
  Fintype.ofFinite _
def nonbacktrackingFourPathWitness
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} (path : NonbacktrackingFourPath G u) :
    FourPathEndpointWitness G u := by
  refine ⟨nonbacktrackingFourPathPair G path,
    nonbacktrackingFourPath_endpoint_ne G hfour path,
    nonbacktrackingFourPath_endpoint_unrelated G hbip hfour hsix path,
    ?_, ?_⟩
  · refine ⟨path.2.1.property.2.symm, path.1,
      path.1.property, path.2.1.property.1.symm⟩
  · refine ⟨path.2.2.2.property.2, path.2.2.1,
      path.2.2.2.property.1.symm,
      path.2.2.1.property.1⟩
abbrev UnrelatedFourPathEndpoint (G : SimpleGraph V) (u : V) :=
  {v : V // u ≠ v ∧ ¬ CommonNeighborRelated G u v}
abbrev CommonSecondNeighbor (G : SimpleGraph V) (u v : V) :=
  {w : V //
    CommonNeighborRelated G u w ∧ CommonNeighborRelated G v w}
noncomputable instance unrelatedFourPathEndpointFintype
    (G : SimpleGraph V) (u : V) :
    Fintype (UnrelatedFourPathEndpoint G u) :=
  Fintype.ofFinite _
noncomputable instance commonSecondNeighborFintype
    (G : SimpleGraph V) (u v : V) :
    Fintype (CommonSecondNeighbor G u v) :=
  Fintype.ofFinite _
def fourPathEndpointWitnessEquiv
    (G : SimpleGraph V) (u : V) :
    FourPathEndpointWitness G u ≃
      Σ v : UnrelatedFourPathEndpoint G u,
        CommonSecondNeighbor G u (v : V) where
  toFun pair :=
    ⟨⟨pair.1.1, pair.2.1, pair.2.2.1⟩,
      ⟨pair.1.2, pair.2.2.2.1, pair.2.2.2.2⟩⟩
  invFun pair :=
    ⟨((pair.1 : V), (pair.2 : V)),
      pair.1.2.1, pair.1.2.2,
      pair.2.2.1, pair.2.2.2⟩
  left_inv pair := Subtype.ext rfl
  right_inv pair := by
    rcases pair with ⟨v, w⟩
    rfl
def CommonNeighborIndependent (G : SimpleGraph V)
    (vertices : Finset V) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ vertices → y ∈ vertices → x ≠ y →
    ¬ CommonNeighborRelated G x y
end FourPathCounting
end LocalGeometry
noncomputable section BreadthFirstCounting
open SimpleGraph
section BreadthFirstPaths
variable {V : Type*} [Fintype V] [DecidableEq V]
abbrev NonbacktrackingThreePath (G : SimpleGraph V) (u : V) :=
  Σ a : G.neighborSet u,
    Σ w : NonbacktrackingNeighbor G u (a : V),
      NonbacktrackingNeighbor G (a : V) (w : V)
def nonbacktrackingThreePathEndpoint
    (G : SimpleGraph V) {u : V}
    (path : NonbacktrackingThreePath G u) : V :=
  path.2.2.1
end BreadthFirstPaths
end BreadthFirstCounting
noncomputable section SubdivisionCounting
open SimpleGraph
section SubdivisionCopies
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}
def subdivisionVertexImage
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V) : SubdivisionVertex k → V
  | .inl (.inl i) => base i
  | .inl (.inr j) => center j
  | .inr (i, j) => pair i j
lemma subdivisionPairVertex_injective
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j)) :
    Function.Injective
      (fun ij : Fin 3 × Fin k => pair ij.1 ij.2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ hpair
  have hi : i = i' := by
    by_contra hne
    apply hbase_unrelated hne
    refine ⟨fun h => hne (hbase h), pair i j,
      hpair_base i j, ?_⟩
    exact Eq.mp
      (congrArg (G.Adj (base i')) hpair.symm)
      (hpair_base i' j')
  subst i'
  have hj : j = j' := by
    by_contra hne
    apply hcenter_unrelated hne
    refine ⟨fun h => hne (hcenter h), pair i j,
      hpair_center i j, ?_⟩
    exact Eq.mp
      (congrArg (G.Adj (center j')) hpair.symm)
      (hpair_center i j')
  exact Prod.ext rfl hj
lemma subdivisionPairVertex_ne_base
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j))
    (i : Fin 3) (j : Fin k) (other : Fin 3) :
    pair i j ≠ base other := by
  obtain ⟨color⟩ := hbip
  have hfirst : color (base i) = color (center j) :=
    bipartite_coloring_eq_of_common_neighbor color
      (hpair_base i j) (hpair_center i j)
  have hother : color (base other) = color (center j) :=
    bipartite_coloring_eq_of_common_neighbor color
      (hpair_base other j) (hpair_center other j)
  intro heq
  apply color.valid (hpair_base i j)
  exact hfirst.trans
    (hother.symm.trans (congrArg color heq).symm)
lemma subdivisionPairVertex_ne_center
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j))
    (i : Fin 3) (j other : Fin k) :
    pair i j ≠ center other := by
  obtain ⟨color⟩ := hbip
  have hother : color (base i) = color (center other) :=
    bipartite_coloring_eq_of_common_neighbor color
      (hpair_base i other) (hpair_center i other)
  intro heq
  apply color.valid (hpair_base i j)
  exact hother.trans (congrArg color heq).symm
lemma subdivisionVertexImage_injective
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_center : ∀ i j, base i ≠ center j)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j)) :
    Function.Injective (subdivisionVertexImage base center pair) := by
  intro u v huv
  rcases u with (i | j) | ⟨i, j⟩ <;>
    rcases v with (i' | j') | ⟨i', j'⟩
  · change base i = base i' at huv
    exact congrArg (fun a : Fin 3 =>
      (Sum.inl (Sum.inl a) : SubdivisionVertex k)) (hbase huv)
  · change base i = center j' at huv
    exact False.elim (hbase_center i j' huv)
  · change base i = pair i' j' at huv
    exact False.elim
      (subdivisionPairVertex_ne_base hbip base center pair
        hpair_base hpair_center i' j' i huv.symm)
  · change center j = base i' at huv
    exact False.elim (hbase_center i' j huv.symm)
  · change center j = center j' at huv
    exact congrArg (fun a : Fin k =>
      (Sum.inl (Sum.inr a) : SubdivisionVertex k)) (hcenter huv)
  · change center j = pair i' j' at huv
    exact False.elim
      (subdivisionPairVertex_ne_center hbip base center pair
        hpair_base hpair_center i' j' j huv.symm)
  · change pair i j = base i' at huv
    exact False.elim
      (subdivisionPairVertex_ne_base hbip base center pair
        hpair_base hpair_center i j i' huv)
  · change pair i j = center j' at huv
    exact False.elim
      (subdivisionPairVertex_ne_center hbip base center pair
        hpair_base hpair_center i j j' huv)
  · change pair i j = pair i' j' at huv
    have heq : (i, j) = (i', j') :=
      subdivisionPairVertex_injective base center pair
        hbase hcenter hbase_unrelated hcenter_unrelated
        hpair_base hpair_center huv
    exact congrArg
      (fun ij : Fin 3 × Fin k =>
        (Sum.inr ij : SubdivisionVertex k)) heq
lemma subdivisionVertexImage_map_relation
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j))
    {u v : SubdivisionVertex k}
    (hadj : (SubdivisionGraph k).Adj u v) :
    G.Adj (subdivisionVertexImage base center pair u)
      (subdivisionVertexImage base center pair v) := by
  rcases u with (i | j) | ⟨i, j⟩ <;>
    rcases v with (i' | j') | ⟨i', j'⟩ <;>
    simp_all [SubdivisionGraph, SimpleGraph.fromRel_adj,
      subdivisionRelation, subdivisionVertexImage]
  all_goals
    first
    | exact (hpair_base _ _).symm
    | exact (hpair_center _ _).symm
def subdivisionCopyOfCommonNeighbors
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_center : ∀ i j, base i ≠ center j)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j)) :
    SimpleGraph.Copy (SubdivisionGraph k) G := by
  refine ⟨⟨subdivisionVertexImage base center pair, ?_⟩, ?_⟩
  · intro u v huv
    exact subdivisionVertexImage_map_relation base center pair
      hpair_base hpair_center huv
  · exact subdivisionVertexImage_injective hbip base center pair
      hbase hcenter hbase_center hbase_unrelated
      hcenter_unrelated hpair_base hpair_center
noncomputable def subdivisionCopyOfRelatedCenters
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j)) :
    SimpleGraph.Copy (SubdivisionGraph k) G := by
  classical
  let pair : Fin 3 → Fin k → V :=
    fun i j => Classical.choose (hrelated i j).2
  have hpair_base (i : Fin 3) (j : Fin k) :
      G.Adj (base i) (pair i j) :=
    (Classical.choose_spec (hrelated i j).2).1
  have hpair_center (i : Fin 3) (j : Fin k) :
      G.Adj (center j) (pair i j) :=
    (Classical.choose_spec (hrelated i j).2).2
  exact subdivisionCopyOfCommonNeighbors hbip base center pair
    hbase hcenter (fun i j => (hrelated i j).1)
    hbase_unrelated hcenter_unrelated hpair_base hpair_center
noncomputable def subdivisionCopyOfGirthEightCenters
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V) (center : Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j)) :
    SimpleGraph.Copy (SubdivisionGraph k) G := by
  have hbase01 : base 0 ≠ base 1 := by
    intro heq
    exact (by decide : (0 : Fin 3) ≠ 1) (hbase heq)
  have hcenter_unrelated :
      ∀ ⦃i j : Fin k⦄, i ≠ j →
        ¬ CommonNeighborRelated G (center i) (center j) := by
    intro i j hij
    exact common_second_neighbors_pairwise_unrelated
      hbip hfour hsix hbase01
      (hbase_unrelated (by decide : (0 : Fin 3) ≠ 1))
      (commonNeighborRelated_symm (hrelated 0 i))
      (commonNeighborRelated_symm (hrelated 1 i))
      (commonNeighborRelated_symm (hrelated 0 j))
      (commonNeighborRelated_symm (hrelated 1 j))
  exact subdivisionCopyOfRelatedCenters hbip base center
    hbase hcenter hbase_unrelated hcenter_unrelated hrelated
end SubdivisionCopies
end SubdivisionCounting
noncomputable section QuotientWitnesses
open SimpleGraph
noncomputable def fiberRepresentative
    {α β : Type*} (g : α → β) (b : Set.range g) : α :=
  Classical.choose b.property
lemma fiberRepresentative_spec
    {α β : Type*} (g : α → β) (b : Set.range g) :
    g (fiberRepresentative g b) = b.1 :=
  Classical.choose_spec b.property
noncomputable def kernelNormalForm
    {α β : Type*} (g : α → β) (x : α) : α :=
  fiberRepresentative g ⟨g x, ⟨x, rfl⟩⟩
lemma kernelNormalForm_spec
    {α β : Type*} (g : α → β) (x : α) :
    g (kernelNormalForm g x) = g x :=
  fiberRepresentative_spec g ⟨g x, ⟨x, rfl⟩⟩
lemma kernelNormalForm_eq_iff
    {α β : Type*} (g : α → β) (x y : α) :
    kernelNormalForm g x = kernelNormalForm g y ↔ g x = g y := by
  constructor
  · intro h
    calc
      g x = g (kernelNormalForm g x) :=
        (kernelNormalForm_spec g x).symm
      _ = g (kernelNormalForm g y) := congrArg g h
      _ = g y := kernelNormalForm_spec g y
  · intro h
    unfold kernelNormalForm
    congr 1
    exact Subtype.ext h
lemma kernelNormalForm_idempotent
    {α β : Type*} (g : α → β) (x : α) :
    kernelNormalForm g (kernelNormalForm g x) =
      kernelNormalForm g x := by
  apply (kernelNormalForm_eq_iff g _ _).mpr
  exact kernelNormalForm_spec g x
lemma kernelNormalForm_fixed
    {α β : Type*} (g : α → β)
    (u : Set.range (kernelNormalForm g)) :
    kernelNormalForm g u.1 = u.1 := by
  obtain ⟨x, hx⟩ := u.property
  rw [← hx]
  exact kernelNormalForm_idempotent g x
noncomputable def kernelQuotientCopy
    {α β : Type*} (source : SimpleGraph α)
    (target : SimpleGraph β) (hom : source →g target) :
    SimpleGraph.Copy
      (quotientGraph source (kernelNormalForm hom)) target := by
  refine ⟨⟨fun u => hom u.1, ?_⟩, ?_⟩
  · intro u v hadj
    rcases (SimpleGraph.fromRel_adj
      (quotientRelation source (kernelNormalForm hom))
        u v).mp hadj with ⟨_, hforward | hbackward⟩
    · obtain ⟨x, y, hx, hy, hxy⟩ := hforward
      have hu : hom u.1 = hom x := by
        calc
          hom u.1 = hom (kernelNormalForm hom x) :=
            congrArg hom hx.symm
          _ = hom x := kernelNormalForm_spec hom x
      have hv : hom v.1 = hom y := by
        calc
          hom v.1 = hom (kernelNormalForm hom y) :=
            congrArg hom hy.symm
          _ = hom y := kernelNormalForm_spec hom y
      change target.Adj (hom u.1) (hom v.1)
      rw [hu, hv]
      exact hom.map_rel hxy
    · obtain ⟨x, y, hx, hy, hxy⟩ := hbackward
      have hv : hom v.1 = hom x := by
        calc
          hom v.1 = hom (kernelNormalForm hom x) :=
            congrArg hom hx.symm
          _ = hom x := kernelNormalForm_spec hom x
      have hu : hom u.1 = hom y := by
        calc
          hom u.1 = hom (kernelNormalForm hom y) :=
            congrArg hom hy.symm
          _ = hom y := kernelNormalForm_spec hom y
      change target.Adj (hom u.1) (hom v.1)
      rw [hu, hv]
      exact (hom.map_rel hxy).symm
  · intro u v huv
    apply Subtype.ext
    have h := (kernelNormalForm_eq_iff hom u.1 v.1).mpr huv
    rwa [kernelNormalForm_fixed hom u,
      kernelNormalForm_fixed hom v] at h
noncomputable def encodeFiniteGraphCopy
    {α β : Type*} [Fintype α]
    (source : SimpleGraph α) (target : SimpleGraph β)
    (copy : SimpleGraph.Copy source target) :
    SimpleGraph.Copy (encodeFiniteGraph source).graph target := by
  exact copy.comp
    (SimpleGraph.Iso.map (Fintype.equivFin α) source).symm.toCopy
end QuotientWitnesses
section CommutativeRing
variable {K : Type*} [CommRing K]
def symmetricQuadratic (a b c x y : K) : K :=
  a * x ^ 2 + (2 : K) * b * x * y + c * y ^ 2
def symmetricDet (a b c : K) : K := a * c - b ^ 2
end CommutativeRing
section CharacteristicTwo
variable {K : Type*} [Field K] [CharP K 2]
end CharacteristicTwo
section Field
variable {K : Type*} [Field K]
def symmetricQuadraticEvaluationMatrix
    (x₀ y₀ x₁ y₁ x₂ y₂ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![x₀ ^ 2, (2 : K) * x₀ * y₀, y₀ ^ 2;
     x₁ ^ 2, (2 : K) * x₁ * y₁, y₁ ^ 2;
     x₂ ^ 2, (2 : K) * x₂ * y₂, y₂ ^ 2]
end Field
noncomputable section Separation
open Filter Finset SimpleGraph
open scoped Topology
def extremalScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((4 : ℝ) / 3)
def FamilyLittleO (family : Finset FiniteGraph) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      (familyExtremal family n : ℝ) ≤ ε * extremalScale n
def UniformMemberLower (family : Finset FiniteGraph) (c : ℝ) : Prop :=
  ∀ forbidden ∈ family,
    ∀ᶠ n : ℕ in atTop,
      c * extremalScale n ≤
        (SimpleGraph.extremalNumber n forbidden.graph : ℝ)
structure SeparationCertificate (family : Finset FiniteGraph) where
  lowerConstant : ℝ
  lowerConstant_pos : 0 < lowerConstant
  family_littleO : FamilyLittleO family
  member_lower : UniformMemberLower family lowerConstant
noncomputable def manuscriptLowerConstant : ℝ :=
  (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
    (27 : ℝ) ^ (-((4 : ℝ) / 3))
end Separation
noncomputable section Supersaturation
open Finset SimpleGraph
section FiniteHeavyFibers
def fourPathHeavyThreshold (N p : ℕ) : ℝ :=
  (p : ℝ) / (2 * (N : ℝ))
def finiteHeavyFiberMass {α : Type*} [Fintype α]
    (weight : α → ℕ) (N p : ℕ) : ℝ :=
  ∑ x : α,
    if fourPathHeavyThreshold N p ≤ (weight x : ℝ)
    then (weight x : ℝ) else 0
end FiniteHeavyFibers
section ActualFourPathFibers
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V] in
lemma common_second_neighbor_pairwise_unrelated
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u v : V}
    (huv : u ≠ v)
    (hunrelated : ¬ CommonNeighborRelated G u v)
    (x y : CommonSecondNeighbor G u v) :
    ¬ CommonNeighborRelated G (x : V) (y : V) := by
  exact common_second_neighbors_pairwise_unrelated
    hbip hfour hsix huv hunrelated
    (commonNeighborRelated_symm x.property.1)
    (commonNeighborRelated_symm x.property.2)
    (commonNeighborRelated_symm y.property.1)
    (commonNeighborRelated_symm y.property.2)
end ActualFourPathFibers
section ActualThetaExtensions
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def thetaBaseExtensions
    (G : SimpleGraph V) (y z : V) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    ∃ witness : SimpleGraph.Copy thetaGraph G,
      witness (.inl (.inl (0 : Fin 3))) = x ∧
      witness (.inl (.inl (1 : Fin 3))) = y ∧
      witness (.inl (.inl (2 : Fin 3))) = z
lemma mem_thetaBaseExtensions
    (G : SimpleGraph V) (x y z : V) :
    x ∈ thetaBaseExtensions G y z ↔
      ∃ witness : SimpleGraph.Copy thetaGraph G,
        witness (.inl (.inl (0 : Fin 3))) = x ∧
        witness (.inl (.inl (1 : Fin 3))) = y ∧
        witness (.inl (.inl (2 : Fin 3))) = z := by
  classical
  simp [thetaBaseExtensions]
def gluedJBase {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G) : Fin 4 → V :=
  ![copies 0 (.inl (.inl (0 : Fin 3))),
    copies 1 (.inl (.inl (0 : Fin 3))),
    copies 0 (.inl (.inl (1 : Fin 3))),
    copies 0 (.inl (.inl (2 : Fin 3)))]
def gluedJVertex {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V) : JVertex → V
  | .inl (.inl base) => gluedJBase copies base
  | .inl (.inr (copy, center)) =>
      copies copy (.inl (.inr center))
  | .inr (.inl (copy, (base, center))) =>
      copies copy (.inr (base, center))
  | .inr (.inr _) => joining
omit [Fintype V] [DecidableEq V] in
lemma gluedJBase_jBase
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (copy : Fin 2) (base : Fin 3) :
    gluedJBase copies (jBase copy base) =
      copies copy (.inl (.inl base)) := by
  fin_cases copy <;> fin_cases base <;>
    simp [gluedJBase, jBase, hfirst, hsecond]
lemma theta_base_pair_adj (base : Fin 3) (center : Fin 2) :
    thetaGraph.Adj
      (.inl (.inl base)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]
lemma theta_center_pair_adj (base : Fin 3) (center : Fin 2) :
    thetaGraph.Adj
      (.inl (.inr center)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]
omit [Fintype V] [DecidableEq V] in
lemma gluedJVertex_map_relation
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining)
    {source target : JVertex}
    (hedge : jTemplateRelation source target) :
    G.Adj
      (gluedJVertex copies joining source)
      (gluedJVertex copies joining target) := by
  rcases source with (base | center) | (pair | star)
  · rcases target with (targetBase | targetCenter) | (targetPair | targetStar)
    · exact False.elim hedge
    · exact False.elim hedge
    · rcases targetPair with ⟨copy, base', center'⟩
      change base = jBase copy base' at hedge
      subst base
      change G.Adj
        (gluedJBase copies (jBase copy base'))
        (copies copy (.inr (base', center')))
      rw [gluedJBase_jBase copies hfirst hsecond copy base']
      exact (copies copy).toHom.map_rel
        (theta_base_pair_adj base' center')
    · change base = 0 ∨ base = 1 at hedge
      rcases hedge with hbase | hbase
      · subst base
        simpa [gluedJVertex, gluedJBase] using hjoinFirst
      · subst base
        simpa [gluedJVertex, gluedJBase] using hjoinSecond
  · rcases center with ⟨copy, center⟩
    rcases target with (targetBase | targetCenter) | (targetPair | targetStar)
    · exact False.elim hedge
    · exact False.elim hedge
    · rcases targetPair with ⟨copy', base, center'⟩
      change copy = copy' ∧ center = center' at hedge
      obtain ⟨hcopy, hcenter⟩ := hedge
      subst copy'
      subst center'
      exact (copies copy).toHom.map_rel
        (theta_center_pair_adj base center)
    · exact False.elim hedge
  · exact False.elim hedge
  · exact False.elim hedge
def gluedJHom
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining) :
    jTemplate →g G where
  toFun := gluedJVertex copies joining
  map_rel' := by
    intro source target hedge
    rcases (SimpleGraph.fromRel_adj
      jTemplateRelation source target).mp hedge with
      ⟨_, hforward | hbackward⟩
    · exact gluedJVertex_map_relation copies joining hfirst hsecond
        hjoinFirst hjoinSecond hforward
    · exact (gluedJVertex_map_relation copies joining
        hfirst hsecond hjoinFirst hjoinSecond hbackward).symm
end ActualThetaExtensions
section ActualCommonCenterTriples
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def tripleCommonCenters
    (G : SimpleGraph V) (base : Fin 3 → V) : Finset V := by
  classical
  exact Finset.univ.filter fun center =>
    ∀ i : Fin 3, CommonNeighborRelated G (base i) center
omit [DecidableEq V] in
lemma mem_tripleCommonCenters
    (G : SimpleGraph V) (base : Fin 3 → V) (center : V) :
    center ∈ tripleCommonCenters G base ↔
      ∀ i : Fin 3, CommonNeighborRelated G (base i) center := by
  classical
  simp [tripleCommonCenters]
lemma mem_thetaBaseExtensions_of_girthEightCenters
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V) (center : Fin 2 → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j)) :
    base 0 ∈ thetaBaseExtensions G (base 1) (base 2) := by
  refine (mem_thetaBaseExtensions G _ _ _).mpr ?_
  let witness := subdivisionCopyOfGirthEightCenters
    hbip hfour hsix base center hbase hcenter hbase_unrelated hrelated
  refine ⟨witness, ?_, ?_, ?_⟩
  all_goals rfl
lemma mem_thetaBaseExtensions_of_two_common_centers
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V)
    (hbase : Function.Injective base)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenters : 2 ≤ (tripleCommonCenters G base).card) :
    base 0 ∈ thetaBaseExtensions G (base 1) (base 2) := by
  classical
  have hcard : 1 < (tripleCommonCenters G base).card := by omega
  obtain ⟨first, hfirst, second, hsecond, hdistinct⟩ :=
    Finset.one_lt_card.mp hcard
  let center : Fin 2 → V := ![first, second]
  have hcenter : Function.Injective center := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [center]
  have hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j) := by
    intro i j
    fin_cases j
    · exact (mem_tripleCommonCenters G base first).mp hfirst i
    · exact (mem_tripleCommonCenters G base second).mp hsecond i
  exact mem_thetaBaseExtensions_of_girthEightCenters
    hbip hfour hsix base center hbase hcenter hbase_unrelated hrelated
end ActualCommonCenterTriples
section CubicBinomialSupersaturation
end CubicBinomialSupersaturation
section ActualTripleSupersaturation
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def commonSecondNeighborTripleMass
    (G : SimpleGraph V) (u : V) : ℕ :=
  ∑ v : UnrelatedFourPathEndpoint G u,
    (Fintype.card (CommonSecondNeighbor G u (v : V))).choose 3
end ActualTripleSupersaturation
section OrderedThetaTripleCounting
noncomputable def orderedThetaTripleCount
    {n : ℕ} (host : SimpleGraph (Fin n)) : ℕ :=
  ∑ y : Fin n, ∑ z : Fin n, (thetaBaseExtensions host y z).card
end OrderedThetaTripleCounting
section ActualGammaAndKForcing
variable {V : Type*} [Fintype V] [DecidableEq V]
def GammaGood (G : SimpleGraph V) (u : V) : Prop :=
  ∃ witness : SimpleGraph.Copy gammaGraph G,
    witness kSpecifiedCenter = u
def gluedKVertex {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (vertex : KVertex) : V :=
  copies vertex.1 vertex.2
lemma subdivisionRelation_adj
    {k : ℕ} {source target : SubdivisionVertex k}
    (hedge : subdivisionRelation k source target) :
    (SubdivisionGraph k).Adj source target := by
  rcases source with (base | center) | pair <;>
    rcases target with (targetBase | targetCenter) | targetPair <;>
    simp_all [SubdivisionGraph, SimpleGraph.fromRel_adj,
      subdivisionRelation]
omit [Fintype V] [DecidableEq V] in
lemma gluedKVertex_map_relation
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter))
    {source target : KVertex}
    (hedge : kTemplateRelation source target) :
    G.Adj (gluedKVertex copies source)
      (gluedKVertex copies target) := by
  rcases hedge with hcopy | hjoin
  · obtain ⟨hindex, hsubdivision⟩ := hcopy
    rcases source with ⟨index, vertex⟩
    rcases target with ⟨index', vertex'⟩
    change index = index' at hindex
    subst index'
    exact (copies index).toHom.map_rel
      (subdivisionRelation_adj hsubdivision)
  · obtain ⟨hsource, htarget, hvertex, hvertex'⟩ := hjoin
    rcases source with ⟨index, vertex⟩
    rcases target with ⟨index', vertex'⟩
    change index = 0 at hsource
    change index' = 1 at htarget
    subst index
    subst index'
    change vertex = kSpecifiedCenter at hvertex
    change vertex' = kSpecifiedCenter at hvertex'
    subst vertex
    subst vertex'
    exact hjoining
def gluedKHom
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter)) :
    kTemplate →g G where
  toFun := gluedKVertex copies
  map_rel' := by
    intro source target hedge
    rcases (SimpleGraph.fromRel_adj
      kTemplateRelation source target).mp hedge with
      ⟨_, hforward | hbackward⟩
    · exact gluedKVertex_map_relation copies hjoining hforward
    · exact (gluedKVertex_map_relation
        copies hjoining hbackward).symm
end ActualGammaAndKForcing
section ActualBadVertexEdgeCounting
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def gammaBadVertices (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ¬ GammaGood G v
end ActualBadVertexEdgeCounting
end Supersaturation
noncomputable section BadVertexCounting
open Finset SimpleGraph
noncomputable def finiteBadFiberMass
    {α β : Type*} [Fintype α] [Fintype β]
    (fibers : α → Finset β) (good : β → Prop) : ℕ := by
  classical
  exact ∑ index : α,
    ((fibers index).filter fun vertex => ¬ good vertex).card
section ActualIndependentTriples
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def commonCenterFinset
    (G : SimpleGraph V) (base : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun center =>
    ∀ vertex ∈ base, CommonNeighborRelated G vertex center
lemma mem_commonCenterFinset
    (G : SimpleGraph V) (base : Finset V) (center : V) :
    center ∈ commonCenterFinset G base ↔
      ∀ vertex ∈ base, CommonNeighborRelated G vertex center := by
  classical
  simp [commonCenterFinset]
def IsIndependentThetaTriple
    (G : SimpleGraph V) (base : Finset V) : Prop :=
  base.card = 3 ∧
    (base : Set V).Pairwise
      (fun first second => ¬ CommonNeighborRelated G first second) ∧
    2 ≤ (commonCenterFinset G base).card
abbrev IndependentThetaTriple (G : SimpleGraph V) :=
  {base : Finset V // IsIndependentThetaTriple G base}
noncomputable instance independentThetaTripleFintype
    (G : SimpleGraph V) : Fintype (IndependentThetaTriple G) :=
  Fintype.ofFinite _
abbrev OrderedThetaWitness (G : SimpleGraph V) :=
  Σ first : V, Σ second : V,
    {third : V // third ∈ thetaBaseExtensions G first second}
noncomputable def independentThetaTripleBase
    (G : SimpleGraph V) (triple : IndependentThetaTriple G) :
    Fin 3 → V :=
  fun index =>
    ((Finset.equivFinOfCardEq triple.property.1).symm index : triple.val)
lemma independentThetaTripleBase_injective
    (G : SimpleGraph V) (triple : IndependentThetaTriple G) :
    Function.Injective (independentThetaTripleBase G triple) := by
  intro first second heq
  apply (Finset.equivFinOfCardEq triple.property.1).symm.injective
  exact Subtype.ext heq
lemma independentThetaTripleBase_mem
    (G : SimpleGraph V) (triple : IndependentThetaTriple G)
    (index : Fin 3) :
    independentThetaTripleBase G triple index ∈ triple.val :=
  ((Finset.equivFinOfCardEq triple.property.1).symm index).property
lemma independentThetaTripleBase_surjective
    (G : SimpleGraph V) (triple : IndependentThetaTriple G)
    {vertex : V} (hvertex : vertex ∈ triple.val) :
    ∃ index : Fin 3,
      independentThetaTripleBase G triple index = vertex := by
  let member : triple.val := ⟨vertex, hvertex⟩
  refine ⟨Finset.equivFinOfCardEq triple.property.1 member, ?_⟩
  change (((Finset.equivFinOfCardEq triple.property.1).symm
    (Finset.equivFinOfCardEq triple.property.1 member) : triple.val) : V) =
      vertex
  simp [member]
lemma commonCenterFinset_eq_tripleCommonCenters
    (G : SimpleGraph V) (triple : IndependentThetaTriple G) :
    commonCenterFinset G triple.val =
      tripleCommonCenters G (independentThetaTripleBase G triple) := by
  classical
  ext center
  rw [mem_commonCenterFinset, mem_tripleCommonCenters]
  constructor
  · intro hcenter index
    exact hcenter _ (independentThetaTripleBase_mem G triple index)
  · intro hcenter vertex hvertex
    obtain ⟨index, rfl⟩ :=
      independentThetaTripleBase_surjective G triple hvertex
    exact hcenter index
lemma independentThetaTripleBase_unrelated
    (G : SimpleGraph V) (triple : IndependentThetaTriple G)
    ⦃first second : Fin 3⦄ (hne : first ≠ second) :
    ¬ CommonNeighborRelated G
      (independentThetaTripleBase G triple first)
      (independentThetaTripleBase G triple second) := by
  apply triple.property.2.1
    (independentThetaTripleBase_mem G triple first)
    (independentThetaTripleBase_mem G triple second)
  exact fun heq =>
    hne (independentThetaTripleBase_injective G triple heq)
noncomputable def independentThetaTripleOrderedWitness
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (triple : IndependentThetaTriple G) : OrderedThetaWitness G := by
  refine ⟨independentThetaTripleBase G triple 1,
    independentThetaTripleBase G triple 2,
    ⟨independentThetaTripleBase G triple 0, ?_⟩⟩
  apply mem_thetaBaseExtensions_of_two_common_centers
    hbip hfour hsix (independentThetaTripleBase G triple)
    (independentThetaTripleBase_injective G triple)
    (independentThetaTripleBase_unrelated G triple)
  rw [← commonCenterFinset_eq_tripleCommonCenters]
  exact triple.property.2.2
end ActualIndependentTriples
end BadVertexCounting
noncomputable section TripleMassIncidence
open Finset SimpleGraph
section TripleIncidence
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def commonSecondNeighborFinset
    (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    CommonNeighborRelated G u x ∧ CommonNeighborRelated G v x
omit [DecidableEq V] in
lemma mem_commonSecondNeighborFinset
    (G : SimpleGraph V) (u v x : V) :
    x ∈ commonSecondNeighborFinset G u v ↔
      CommonNeighborRelated G u x ∧ CommonNeighborRelated G v x := by
  classical
  simp [commonSecondNeighborFinset]
abbrev BadFourPathTripleWitness (G : SimpleGraph V) :=
  Σ center : {u : V // ¬ GammaGood G u},
    Σ endpoint : UnrelatedFourPathEndpoint G (center : V),
      {base : Finset V //
        base ∈ (commonSecondNeighborFinset G
          (center : V) (endpoint : V)).powersetCard 3}
abbrev BadIndependentTripleWitness (G : SimpleGraph V) :=
  Σ triple : IndependentThetaTriple G,
    {center : V // center ∈ commonCenterFinset G triple.val ∧
      ¬ GammaGood G center}
noncomputable instance badFourPathTripleWitnessFintype
    (G : SimpleGraph V) : Fintype (BadFourPathTripleWitness G) := by
  classical
  infer_instance
noncomputable instance badIndependentTripleWitnessFintype
    (G : SimpleGraph V) : Fintype (BadIndependentTripleWitness G) := by
  classical
  infer_instance
noncomputable def fourPathTripleToIndependentThetaTriple
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (u : V)
    (endpoint : UnrelatedFourPathEndpoint G u)
    (base : {T : Finset V //
      T ∈ (commonSecondNeighborFinset G u
        (endpoint : V)).powersetCard 3}) :
    IndependentThetaTriple G := by
  have hsubset :
      base.val ⊆ commonSecondNeighborFinset G u (endpoint : V) :=
    (Finset.mem_powersetCard.mp base.property).1
  refine ⟨base.val, ?_, ?_, ?_⟩
  · exact (Finset.mem_powersetCard.mp base.property).2
  · intro x hx y hy hne
    have hx' := (mem_commonSecondNeighborFinset
      G u (endpoint : V) x).mp (hsubset hx)
    have hy' := (mem_commonSecondNeighborFinset
      G u (endpoint : V) y).mp (hsubset hy)
    exact common_second_neighbor_pairwise_unrelated
      G hbip hfour hsix endpoint.property.1 endpoint.property.2
      (⟨x, hx'⟩ : CommonSecondNeighbor G u (endpoint : V))
      (⟨y, hy'⟩ : CommonSecondNeighbor G u (endpoint : V))
  · have hu : u ∈ commonCenterFinset G base.val := by
      apply (mem_commonCenterFinset G base.val u).mpr
      intro x hx
      exact commonNeighborRelated_symm
        ((mem_commonSecondNeighborFinset
          G u (endpoint : V) x).mp (hsubset hx)).1
    have hv : (endpoint : V) ∈ commonCenterFinset G base.val := by
      apply (mem_commonCenterFinset G base.val (endpoint : V)).mpr
      intro x hx
      exact commonNeighborRelated_symm
        ((mem_commonSecondNeighborFinset
          G u (endpoint : V) x).mp (hsubset hx)).2
    have hcard : 1 < (commonCenterFinset G base.val).card :=
      Finset.one_lt_card.mpr
        ⟨u, hu, (endpoint : V), hv, endpoint.property.1⟩
    omega
lemma fourPathTripleToIndependentThetaTriple_center_mem
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (u : V)
    (endpoint : UnrelatedFourPathEndpoint G u)
    (base : {T : Finset V //
      T ∈ (commonSecondNeighborFinset G u
        (endpoint : V)).powersetCard 3}) :
    u ∈ commonCenterFinset G
      (fourPathTripleToIndependentThetaTriple
        G hbip hfour hsix u endpoint base).val := by
  change u ∈ commonCenterFinset G base.val
  apply (mem_commonCenterFinset G base.val u).mpr
  intro x hx
  have hsubset := (Finset.mem_powersetCard.mp base.property).1
  exact commonNeighborRelated_symm
    ((mem_commonSecondNeighborFinset
      G u (endpoint : V) x).mp (hsubset hx)).1
noncomputable def badFourPathTripleToBadIndependentTriple
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    BadFourPathTripleWitness G → BadIndependentTripleWitness G := by
  rintro ⟨center, endpoint, base⟩
  refine ⟨fourPathTripleToIndependentThetaTriple
    G hbip hfour hsix center endpoint base, ?_⟩
  refine ⟨center, ?_, center.property⟩
  exact fourPathTripleToIndependentThetaTriple_center_mem
    G hbip hfour hsix center endpoint base
end TripleIncidence
end TripleMassIncidence
noncomputable section QuantitativeBadVertexBound
open Finset SimpleGraph
end QuantitativeBadVertexBound
noncomputable section LineCoordinates
variable (K : Type*) [Field K]
def symplecticHorizontalVector (x y : K) : SymplecticVector K :=
  ![x, 0, y, 0]
def symplecticAnnihilatorVector (x y : K) : SymplecticVector K :=
  ![0, -y, 0, x]
def symmetricGraphVector (a b c x y : K) : SymplecticVector K :=
  ![x, a * x + b * y, y, b * x + c * y]
lemma symmetricGraphVector_orthogonal
    (a b c x y x' y' : K) :
    standardSymplecticForm K
      (symmetricGraphVector K a b c x y)
      (symmetricGraphVector K a b c x' y') = 0 := by
  simp [standardSymplecticForm, symmetricGraphVector]
  ring
def coordinateCenterLinearMap (x y : K) :
    (Fin 2 → K) →ₗ[K] SymplecticVector K where
  toFun h :=
    h 0 • symplecticHorizontalVector K x y +
      h 1 • symplecticAnnihilatorVector K x y
  map_add' u v := by
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalVector, symplecticAnnihilatorVector,
        Pi.add_apply, smul_eq_mul] <;> ring
  map_smul' r u := by
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalVector, symplecticAnnihilatorVector,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
lemma coordinateCenterLinearMap_injective
    {x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    Function.Injective (coordinateCenterLinearMap K x y) := by
  intro u v huv
  have hzero := congrFun huv 0
  have hone := congrFun huv 1
  have htwo := congrFun huv 2
  have hthree := congrFun huv 3
  simp [coordinateCenterLinearMap, symplecticHorizontalVector,
    symplecticAnnihilatorVector, smul_eq_mul]
    at hzero hone htwo hthree
  funext i
  fin_cases i
  · rcases hxy with hx | hy
    · exact hzero.resolve_right hx
    · exact htwo.resolve_right hy
  · rcases hxy with hx | hy
    · exact hthree.resolve_right hx
    · exact hone.resolve_right hy
def coordinateCenterLine (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0) :
    SymplecticLine K :=
  ⟨LinearMap.range (coordinateCenterLinearMap K x y), by
    constructor
    · rw [LinearMap.finrank_range_of_inj
        (coordinateCenterLinearMap_injective K hxy)]
      simp
    · intro u hu v hv
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      simp [coordinateCenterLinearMap, standardSymplecticForm,
        symplecticHorizontalVector, symplecticAnnihilatorVector,
        smul_eq_mul]
      ring⟩
def symmetricGraphLinearMap (a b c : K) :
    (Fin 2 → K) →ₗ[K] SymplecticVector K where
  toFun h := symmetricGraphVector K a b c (h 0) (h 1)
  map_add' u v := by
    funext i
    fin_cases i <;>
      simp [symmetricGraphVector, Pi.add_apply] <;> ring
  map_smul' r u := by
    funext i
    fin_cases i <;>
      simp [symmetricGraphVector, Pi.smul_apply, smul_eq_mul] <;> ring
lemma symmetricGraphLinearMap_injective
    (a b c : K) :
    Function.Injective (symmetricGraphLinearMap K a b c) := by
  intro u v huv
  funext i
  fin_cases i
  · simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      congrFun huv 0
  · simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      congrFun huv 2
def symmetricGraphLine (a b c : K) : SymplecticLine K :=
  ⟨LinearMap.range (symmetricGraphLinearMap K a b c), by
    constructor
    · rw [LinearMap.finrank_range_of_inj
        (symmetricGraphLinearMap_injective K a b c)]
      simp
    · intro u hu v hv
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      exact symmetricGraphVector_orthogonal K a b c
        (u' 0) (u' 1) (v' 0) (v' 1)⟩
lemma projectiveDirection_nonzero_left
    {x y x' y' : K}
    (hdet : x * y' - x' * y ≠ 0) :
    x ≠ 0 ∨ y ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hx, hy⟩ := h
  apply hdet
  simp [hx, hy]
lemma projectiveDirection_nonzero_right
    {x y x' y' : K}
    (hdet : x * y' - x' * y ≠ 0) :
    x' ≠ 0 ∨ y' ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hx, hy⟩ := h
  apply hdet
  simp [hx, hy]
section CharacteristicTwo
variable [CharP K 2] [Finite K]
end CharacteristicTwo
end LineCoordinates
noncomputable section ArbitraryLineNormalization
open SimpleGraph
variable (K : Type*) [Field K]
abbrev SymplecticAutomorphism :=
  (standardSymplecticBilin K).IsometryEquiv
    (standardSymplecticBilin K)
lemma symplecticAutomorphism_form
    (e : SymplecticAutomorphism K)
    (u v : SymplecticVector K) :
    standardSymplecticForm K (e u) (e v) =
      standardSymplecticForm K u v := by
  change
    standardSymplecticBilin K (e u) (e v) =
      standardSymplecticBilin K u v
  exact e.map_app' u v
def symplecticAutomorphismPoint
    (e : SymplecticAutomorphism K)
    (p : SymplecticPoint K) : SymplecticPoint K :=
  ⟨p.1.map e.toLinearEquiv.toLinearMap,
    (e.toLinearEquiv.finrank_map_eq p.1).trans p.2⟩
def symplecticAutomorphismLine
    (e : SymplecticAutomorphism K)
    (L : SymplecticLine K) : SymplecticLine K := by
  refine ⟨L.1.map e.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · exact (e.toLinearEquiv.finrank_map_eq L.1).trans L.2.1
  · intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := (Submodule.mem_map.mp hu)
    obtain ⟨v', hv', rfl⟩ := (Submodule.mem_map.mp hv)
    change standardSymplecticForm K (e u') (e v') = 0
    exact (symplecticAutomorphism_form K e u' v').trans
      (L.2.2 u' hu' v' hv')
lemma symplecticAutomorphism_isotropic_iff
    (e : SymplecticAutomorphism K)
    (S : Submodule K (SymplecticVector K)) :
    (∀ u ∈ S.map e.toLinearEquiv.toLinearMap,
      ∀ v ∈ S.map e.toLinearEquiv.toLinearMap,
        standardSymplecticForm K u v = 0) ↔
      (∀ u ∈ S, ∀ v ∈ S,
        standardSymplecticForm K u v = 0) := by
  constructor
  · intro h u hu v hv
    have hmap := h (e u) (Submodule.mem_map_of_mem hu)
      (e v) (Submodule.mem_map_of_mem hv)
    exact (symplecticAutomorphism_form K e u v).symm.trans hmap
  · intro h u hu v hv
    obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨v', hv', rfl⟩ := Submodule.mem_map.mp hv
    exact (symplecticAutomorphism_form K e u' v').trans
      (h u' hu' v' hv')
def symplecticAutomorphismLineEquiv
    (e : SymplecticAutomorphism K) :
    SymplecticLine K ≃ SymplecticLine K :=
  (Submodule.orderIsoMapComap e.toLinearEquiv).toEquiv.subtypeEquiv
    (fun S => by
      change
        (Module.finrank K S = 2 ∧
          ∀ u ∈ S, ∀ v ∈ S,
            standardSymplecticForm K u v = 0) ↔
        (Module.finrank K
            (S.map e.toLinearEquiv.toLinearMap) = 2 ∧
          ∀ u ∈ S.map e.toLinearEquiv.toLinearMap,
            ∀ v ∈ S.map e.toLinearEquiv.toLinearMap,
              standardSymplecticForm K u v = 0)
      rw [e.toLinearEquiv.finrank_map_eq,
        symplecticAutomorphism_isotropic_iff K e S])
@[simp]
lemma symplecticAutomorphismLineEquiv_apply
    (e : SymplecticAutomorphism K)
    (L : SymplecticLine K) :
    symplecticAutomorphismLineEquiv K e L =
      symplecticAutomorphismLine K e L := by
  apply Subtype.ext
  rfl
lemma symplecticLine_orthogonal_eq
    (L : SymplecticLine K) :
    (standardSymplecticBilin K).orthogonal L.1 = L.1 := by
  have hle :
      L.1 ≤ (standardSymplecticBilin K).orthogonal L.1 := by
    intro u hu
    change ∀ v ∈ L.1, standardSymplecticForm K v u = 0
    intro v hv
    exact L.2.2 v hv u hu
  have hdim :
      Module.finrank K
        ((standardSymplecticBilin K).orthogonal L.1) = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal
      (standardSymplecticBilin_nondegenerate K), L.2.1]
    simp [SymplecticVector]
  exact (Submodule.eq_of_le_of_finrank_eq hle
    (L.2.1.trans hdim.symm)).symm
lemma symplecticLine_isCompl_of_disjoint
    {L M : SymplecticLine K}
    (hLM : Disjoint L.1 M.1) : IsCompl L.1 M.1 := by
  apply (Submodule.isCompl_iff_disjoint L.1 M.1 ?_).mpr hLM
  simp [SymplecticVector, L.2.1, M.2.1]
def symplecticLinePairing
    (L M : SymplecticLine K) :
    M.1 →ₗ[K] Module.Dual K L.1 where
  toFun y :=
    { toFun := fun x =>
        standardSymplecticForm K
          (x : SymplecticVector K) (y : SymplecticVector K)
      map_add' := by
        intro x x'
        simpa using standardSymplecticForm_add_left K
          (x : SymplecticVector K)
          (x' : SymplecticVector K)
          (y : SymplecticVector K)
      map_smul' := by
        intro c x
        simpa [smul_eq_mul] using
          standardSymplecticForm_smul_left K c
            (x : SymplecticVector K)
            (y : SymplecticVector K) }
  map_add' := by
    intro y y'
    apply LinearMap.ext
    intro x
    simpa using standardSymplecticForm_add_right K
      (x : SymplecticVector K)
      (y : SymplecticVector K)
      (y' : SymplecticVector K)
  map_smul' := by
    intro c y
    apply LinearMap.ext
    intro x
    simpa [smul_eq_mul] using
      standardSymplecticForm_smul_right K c
        (x : SymplecticVector K)
        (y : SymplecticVector K)
lemma symplecticLinePairing_injective
    {L M : SymplecticLine K}
    (hLM : Disjoint L.1 M.1) :
    Function.Injective (symplecticLinePairing K L M) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro y hy
    have hpair : symplecticLinePairing K L M y = 0 := by
      exact LinearMap.mem_ker.mp hy
    have hyorth :
        (y : SymplecticVector K) ∈
          (standardSymplecticBilin K).orthogonal L.1 := by
      change
        ∀ x ∈ L.1,
          standardSymplecticForm K x
            (y : SymplecticVector K) = 0
      intro x hx
      have hz := DFunLike.congr_fun hpair (⟨x, hx⟩ : L.1)
      simpa [symplecticLinePairing] using hz
    have hyL : (y : SymplecticVector K) ∈ L.1 := by
      rw [symplecticLine_orthogonal_eq K L] at hyorth
      exact hyorth
    have hyzero : (y : SymplecticVector K) = 0 := by
      have hbot :
          (y : SymplecticVector K) ∈
            (⊥ : Submodule K (SymplecticVector K)) :=
        hLM.le_bot ⟨hyL, y.2⟩
      simpa using hbot
    have hyzero' : y = 0 := by
      apply Subtype.ext
      simpa using hyzero
    exact (Submodule.mem_bot K).2 hyzero'
  · exact bot_le
lemma symplecticLinePairing_finrank
    (L M : SymplecticLine K) :
    Module.finrank K M.1 =
      Module.finrank K (Module.Dual K L.1) := by
  rw [Subspace.dual_finrank_eq, L.2.1, M.2.1]
def symplecticLinePairingEquiv
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    M.1 ≃ₗ[K] Module.Dual K L.1 :=
  (symplecticLinePairing K L M).linearEquivOfInjective
    (symplecticLinePairing_injective K hLM)
    (symplecticLinePairing_finrank K L M)
def symplecticLineBasis
    (L : SymplecticLine K) : Module.Basis (Fin 2) K L.1 :=
  Module.finBasisOfFinrankEq K L.1 L.2.1
def symplecticLineDualCoordinates
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    M.1 ≃ₗ[K] (Fin 2 → K) :=
  (symplecticLinePairingEquiv K L M hLM).trans
    (symplecticLineBasis K L).dualBasis.equivFun
@[simp]
lemma symplecticLineDualCoordinates_apply
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (y : M.1) (i : Fin 2) :
    symplecticLineDualCoordinates K L M hLM y i =
      standardSymplecticForm K
        ((symplecticLineBasis K L i : L.1) : SymplecticVector K)
        (y : SymplecticVector K) := by
  change
    (symplecticLineBasis K L).dualBasis.equivFun
        (symplecticLinePairingEquiv K L M hLM y) i = _
  rw [Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr]
  rfl
def symplecticCoordinateInterleave :
    ((Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] SymplecticVector K where
  toFun x := ![x.1 0, x.2 0, x.1 1, x.2 1]
  invFun x := (![x 0, x 2], ![x 1, x 3])
  left_inv := by
    intro x
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
    · funext i
      fin_cases i <;> simp
  right_inv := by
    intro x
    funext i
    fin_cases i <;> simp
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp
  map_smul' := by
    intro c x
    funext i
    fin_cases i <;> simp [smul_eq_mul]
def symplecticLineCoordinateEquiv
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    SymplecticVector K ≃ₗ[K] SymplecticVector K :=
  ((L.1.prodEquivOfIsCompl M.1
      (symplecticLine_isCompl_of_disjoint K hLM)).symm.trans
      ((symplecticLineBasis K L).equivFun.prodCongr
        (symplecticLineDualCoordinates K L M hLM))).trans
      (symplecticCoordinateInterleave K)
lemma symplecticLinePairing_coordinate_expansion
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (x : L.1) (y : M.1) :
    standardSymplecticForm K
        (x : SymplecticVector K) (y : SymplecticVector K) =
      (symplecticLineBasis K L).equivFun x 0 *
          symplecticLineDualCoordinates K L M hLM y 0 +
        (symplecticLineBasis K L).equivFun x 1 *
          symplecticLineDualCoordinates K L M hLM y 1 := by
  let b := symplecticLineBasis K L
  have hsum :
      (∑ i : Fin 2, b.equivFun x i • b i) = x :=
    b.sum_equivFun x
  calc
    standardSymplecticForm K
        (x : SymplecticVector K) (y : SymplecticVector K) =
        symplecticLinePairing K L M y x := rfl
    _ = symplecticLinePairing K L M y
          (∑ i : Fin 2, b.equivFun x i • b i) :=
      congrArg (symplecticLinePairing K L M y) hsum.symm
    _ = ∑ i : Fin 2,
          b.equivFun x i *
            standardSymplecticForm K
              ((b i : L.1) : SymplecticVector K)
              (y : SymplecticVector K) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      simp [smul_eq_mul, symplecticLinePairing]
    _ = (symplecticLineBasis K L).equivFun x 0 *
          symplecticLineDualCoordinates K L M hLM y 0 +
        (symplecticLineBasis K L).equivFun x 1 *
          symplecticLineDualCoordinates K L M hLM y 1 := by
      simp [Fin.sum_univ_two, b,
        symplecticLineDualCoordinates_apply]
lemma symplecticLineCoordinateEquiv_apply_add
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (x : L.1) (y : M.1) :
    symplecticLineCoordinateEquiv K L M hLM
        ((x : SymplecticVector K) + (y : SymplecticVector K)) =
      ![(symplecticLineBasis K L).equivFun x 0,
        symplecticLineDualCoordinates K L M hLM y 0,
        (symplecticLineBasis K L).equivFun x 1,
        symplecticLineDualCoordinates K L M hLM y 1] := by
  let hcompl := symplecticLine_isCompl_of_disjoint K hLM
  have hsplit :
      (L.1.prodEquivOfIsCompl M.1 hcompl).symm
        ((x : SymplecticVector K) +
          (y : SymplecticVector K)) = (x, y) := by
    apply (L.1.prodEquivOfIsCompl M.1 hcompl).symm_apply_eq.mpr
    rfl
  change
    symplecticCoordinateInterleave K
      (((symplecticLineBasis K L).equivFun.prodCongr
        (symplecticLineDualCoordinates K L M hLM))
        ((L.1.prodEquivOfIsCompl M.1 hcompl).symm
          ((x : SymplecticVector K) +
            (y : SymplecticVector K)))) = _
  rw [hsplit]
  rfl
lemma symplecticLineCoordinateEquiv_form
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (u v : SymplecticVector K) :
    standardSymplecticForm K
        (symplecticLineCoordinateEquiv K L M hLM u)
        (symplecticLineCoordinateEquiv K L M hLM v) =
      standardSymplecticForm K u v := by
  let hcompl := symplecticLine_isCompl_of_disjoint K hLM
  obtain ⟨⟨x, y⟩, hu⟩ :=
    (L.1.prodEquivOfIsCompl M.1 hcompl).surjective u
  obtain ⟨⟨x', y'⟩, hv⟩ :=
    (L.1.prodEquivOfIsCompl M.1 hcompl).surjective v
  rw [← hu, ← hv]
  change
    standardSymplecticForm K
        (symplecticLineCoordinateEquiv K L M hLM
          ((x : SymplecticVector K) + (y : SymplecticVector K)))
        (symplecticLineCoordinateEquiv K L M hLM
          ((x' : SymplecticVector K) + (y' : SymplecticVector K))) =
      standardSymplecticForm K
        ((x : SymplecticVector K) + (y : SymplecticVector K))
        ((x' : SymplecticVector K) + (y' : SymplecticVector K))
  calc
    standardSymplecticForm K
        (symplecticLineCoordinateEquiv K L M hLM
          ((x : SymplecticVector K) + (y : SymplecticVector K)))
        (symplecticLineCoordinateEquiv K L M hLM
          ((x' : SymplecticVector K) + (y' : SymplecticVector K))) =
      (symplecticLineBasis K L).equivFun x 0 *
          symplecticLineDualCoordinates K L M hLM y' 0 -
        symplecticLineDualCoordinates K L M hLM y 0 *
          (symplecticLineBasis K L).equivFun x' 0 +
        ((symplecticLineBasis K L).equivFun x 1 *
          symplecticLineDualCoordinates K L M hLM y' 1 -
        symplecticLineDualCoordinates K L M hLM y 1 *
          (symplecticLineBasis K L).equivFun x' 1) := by
        simp [symplecticLineCoordinateEquiv_apply_add,
          standardSymplecticForm]
    _ = standardSymplecticForm K
          (x : SymplecticVector K) (y' : SymplecticVector K) -
        standardSymplecticForm K
          (x' : SymplecticVector K) (y : SymplecticVector K) := by
        rw [symplecticLinePairing_coordinate_expansion K L M hLM x y',
          symplecticLinePairing_coordinate_expansion K L M hLM x' y]
        ring
    _ = standardSymplecticForm K
        ((x : SymplecticVector K) + (y : SymplecticVector K))
        ((x' : SymplecticVector K) + (y' : SymplecticVector K)) := by
        have hxx :
            standardSymplecticForm K
              (x : SymplecticVector K)
              (x' : SymplecticVector K) = 0 :=
          L.2.2 x x.2 x' x'.2
        have hyy :
            standardSymplecticForm K
              (y : SymplecticVector K)
              (y' : SymplecticVector K) = 0 :=
          M.2.2 y y.2 y' y'.2
        rw [standardSymplecticForm_add_left,
          standardSymplecticForm_add_right,
          standardSymplecticForm_add_right,
          hxx, hyy,
          standardSymplecticForm_swap K
            (y : SymplecticVector K)
            (x' : SymplecticVector K)]
        ring
def symplecticLineNormalizer
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    SymplecticAutomorphism K :=
  { symplecticLineCoordinateEquiv K L M hLM with
    map_app' := by
      intro u v
      change
        standardSymplecticForm K
            (symplecticLineCoordinateEquiv K L M hLM u)
            (symplecticLineCoordinateEquiv K L M hLM v) =
          standardSymplecticForm K u v
      exact symplecticLineCoordinateEquiv_form K L M hLM u v }
def symplecticVerticalLinearMap :
    (Fin 2 → K) →ₗ[K] SymplecticVector K where
  toFun y := ![0, y 0, 0, y 1]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c y := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]
lemma symplecticVerticalLinearMap_injective :
    Function.Injective (symplecticVerticalLinearMap K) := by
  intro u v huv
  funext i
  fin_cases i
  · simpa [symplecticVerticalLinearMap] using congrFun huv 1
  · simpa [symplecticVerticalLinearMap] using congrFun huv 3
def symplecticVerticalLine : SymplecticLine K :=
  ⟨LinearMap.range (symplecticVerticalLinearMap K), by
    constructor
    · rw [LinearMap.finrank_range_of_inj
        (symplecticVerticalLinearMap_injective K)]
      simp
    · intro u hu v hv
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      simp [symplecticVerticalLinearMap,
        standardSymplecticForm]⟩
def symplecticHorizontalProjection :
    SymplecticVector K →ₗ[K] (Fin 2 → K) where
  toFun v := ![v 0, v 2]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c v := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]
def symplecticVerticalProjection :
    SymplecticVector K →ₗ[K] (Fin 2 → K) where
  toFun v := ![v 1, v 3]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c v := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]
lemma symplecticHorizontalProjection_ker :
    LinearMap.ker (symplecticHorizontalProjection K) =
      (symplecticVerticalLine K).1 := by
  apply le_antisymm
  · intro v hv
    have hzero := LinearMap.mem_ker.mp hv
    have hfirst := congrFun hzero 0
    have hthird := congrFun hzero 1
    simp [symplecticHorizontalProjection] at hfirst hthird
    change v ∈ LinearMap.range (symplecticVerticalLinearMap K)
    refine ⟨![v 1, v 3], ?_⟩
    funext i
    fin_cases i <;>
      simp [symplecticVerticalLinearMap, hfirst, hthird]
  · intro v hv
    change v ∈ LinearMap.range (symplecticVerticalLinearMap K) at hv
    obtain ⟨y, rfl⟩ := hv
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalProjection,
        symplecticVerticalLinearMap]
lemma symplecticLineHorizontalProjection_injective
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    Function.Injective
      ((symplecticHorizontalProjection K).comp L.1.subtype) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro x hx
    have hproj := LinearMap.mem_ker.mp hx
    change
      symplecticHorizontalProjection K
          (x : SymplecticVector K) = 0 at hproj
    have hxvertical :
        (x : SymplecticVector K) ∈
          (symplecticVerticalLine K).1 := by
      rw [← symplecticHorizontalProjection_ker K]
      exact LinearMap.mem_ker.mpr hproj
    have hxzero : (x : SymplecticVector K) = 0 := by
      have hbot :
          (x : SymplecticVector K) ∈
            (⊥ : Submodule K (SymplecticVector K)) :=
        hvertical.le_bot ⟨x.2, hxvertical⟩
      simpa using hbot
    have hxsub : x = 0 := by
      apply Subtype.ext
      simpa using hxzero
    exact (Submodule.mem_bot K).2 hxsub
  · exact bot_le
def symplecticLineHorizontalProjectionEquiv
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    L.1 ≃ₗ[K] (Fin 2 → K) :=
  ((symplecticHorizontalProjection K).comp L.1.subtype).linearEquivOfInjective
      (symplecticLineHorizontalProjection_injective K L hvertical)
      (by simp [L.2.1])
def symplecticLineGraphMap
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
  (symplecticVerticalProjection K).comp
    (L.1.subtype.comp
      (symplecticLineHorizontalProjectionEquiv K L hvertical).symm.toLinearMap)
end ArbitraryLineNormalization
noncomputable section JQuotientAvoidanceReduction
open SimpleGraph
end JQuotientAvoidanceReduction
noncomputable section JTemplateLineAvoidanceReduction
open SimpleGraph
variable (K : Type*) [Field K]
def CharTwoLinePairAvoidance : Prop :=
  ∀ (Y Z X X' : SymplecticLine K),
    Disjoint Y.1 Z.1 →
    Disjoint X.1 Y.1 →
    Disjoint X.1 Z.1 →
    Disjoint X'.1 Y.1 →
    Disjoint X'.1 Z.1 →
    X ≠ X' →
    ∀ (C C' : Fin 2 → SymplecticLine K),
      Function.Injective C →
      Function.Injective C' →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Y.1 ∧ p.1 ≤ (C i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Z.1 ∧ p.1 ≤ (C i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ X.1 ∧ p.1 ≤ (C i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Y.1 ∧ p.1 ≤ (C' i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Z.1 ∧ p.1 ≤ (C' i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ X'.1 ∧ p.1 ≤ (C' i).1) →
      Disjoint X.1 X'.1
end JTemplateLineAvoidanceReduction
noncomputable section CharacteristicTwoLineAvoidance
open SimpleGraph
variable (K : Type*) [Field K] [CharP K 2] [Finite K]
end CharacteristicTwoLineAvoidance
noncomputable section UpperBoundReduction
open Filter Finset SimpleGraph
open scoped Classical Topology
end UpperBoundReduction
noncomputable section AsymptoticExtraction
open Filter Finset SimpleGraph
open scoped Classical Topology
noncomputable def compactnessDegreePowerConstant : ℝ :=
  (48 : ℝ) ^ (4 : ℕ) + 1769472 + 1
noncomputable def compactnessHostPowerConstant : ℝ :=
  (2 : ℝ) ^ (16 : ℕ) * compactnessDegreePowerConstant
end AsymptoticExtraction
noncomputable section CycleBounds
open Filter Finset SimpleGraph
open scoped Topology
end CycleBounds
noncomputable section Counterexample
open SimpleGraph
end Counterexample
noncomputable section Connectedness
open Finset SimpleGraph
end Connectedness
noncomputable section Bipartiteness
open Finset SimpleGraph
end Bipartiteness
noncomputable section FamilyExtremal
open Finset SimpleGraph
end FamilyExtremal
noncomputable section MainTheorem
open Finset SimpleGraph
open scoped Classical
noncomputable def compactnessSharpHostPowerConstant : ℝ :=
  compactnessHostPowerConstant
end MainTheorem
end CompactnessConjecture
namespace TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
section BinaryEntropy
noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2
noncomputable def binaryEntropy (x : ℝ) : ℝ :=
  Real.binEntropy x / Real.log 2
noncomputable def tau : ℝ := (Real.sqrt 3 - 1) / 2
noncomputable def kappa : ℝ := 3 / 2 - (3 / 4) * logTwo 3
noncomputable def certifiedWindowWidth : ℝ :=
  logTwo ((97 + 56 * Real.sqrt 3) / 192) / 4
theorem twelve_sevenths_lt_sqrt_three : (12 : ℝ) / 7 < Real.sqrt 3 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  nlinarith
theorem log_two_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)
@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy]
@[simp] theorem binaryEntropy_one_sub (x : ℝ) :
    binaryEntropy (1 - x) = binaryEntropy x := by
  simp [binaryEntropy]
@[fun_prop] theorem binaryEntropy_continuous : Continuous binaryEntropy := by
  exact Real.binEntropy_continuous.div_const _
noncomputable def binaryPinskerGap (q : ℝ) : ℝ :=
  Real.log 2 - Real.binEntropy q - (2 * q - 1) ^ 2 / 2
noncomputable def binaryPinskerGapDeriv (q : ℝ) : ℝ :=
  Real.log q - Real.log (1 - q) - 2 * (2 * q - 1)
noncomputable def binaryPinskerGapDerivTwo (q : ℝ) : ℝ :=
  q⁻¹ + (1 - q)⁻¹ - 4
@[simp] theorem binaryPinskerGap_half :
    binaryPinskerGap ((2 : ℝ)⁻¹) = 0 := by
  unfold binaryPinskerGap
  rw [Real.binEntropy_two_inv]
  norm_num
@[simp] theorem binaryPinskerGapDeriv_half :
    binaryPinskerGapDeriv ((2 : ℝ)⁻¹) = 0 := by
  unfold binaryPinskerGapDeriv
  norm_num
noncomputable def entropyTangentSigma : ℝ :=
  4 / (3 * Real.sqrt 2)
noncomputable def entropyTangentRho : ℝ :=
  Real.sqrt 2 / Real.sqrt 3
noncomputable def entropyTangentZeroCoefficient (q : ℝ) : ℝ :=
  Real.sqrt 2 * (3 - 2 * q) / 4
noncomputable def entropyTangentOneCoefficient (q : ℝ) : ℝ :=
  Real.sqrt 2 * (1 + 2 * q) / 4
noncomputable def binaryConditionalLogPotential (q zeroAmplitude oneAmplitude : ℝ) : ℝ :=
  Real.binEntropy q / 2 +
    (1 - q) ^ 2 * Real.log (zeroAmplitude + oneAmplitude / 3) +
    q ^ 2 * Real.log (zeroAmplitude / 3 + oneAmplitude) +
    2 * q * (1 - q) *
      Real.log ((zeroAmplitude + oneAmplitude) / Real.sqrt 3)
def binaryCoinMass (q : ℝ) (outcome : Bool) : ℝ :=
  if outcome then q else 1 - q
def independentBinaryPairMass (q : ℝ) (left right : Bool) : ℝ :=
  binaryCoinMass q left * binaryCoinMass q right
structure BinaryPairKernel where
  parentProbability : ℝ
  parentProbability_nonneg : 0 ≤ parentProbability
  parentProbability_le_one : parentProbability ≤ 1
  childProbability : Bool → Bool → ℝ
  childProbability_nonneg : ∀ left right, 0 ≤ childProbability left right
  childProbability_le_one : ∀ left right, childProbability left right ≤ 1
namespace BinaryPairKernel
noncomputable def childMarginal (kernel : BinaryPairKernel) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      kernel.childProbability left right
noncomputable def conditionalEntropy (kernel : BinaryPairKernel) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      binaryEntropy (kernel.childProbability left right)
def bitDisagreementProbability (parent : Bool) (childProbability : ℝ) : ℝ :=
  if parent then 1 - childProbability else childProbability
noncomputable def averageDisagreement (kernel : BinaryPairKernel) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      ((bitDisagreementProbability left
          (kernel.childProbability left right) +
        bitDisagreementProbability right
          (kernel.childProbability left right)) / 2)
noncomputable def smoothed (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) : BinaryPairKernel where
  parentProbability := kernel.parentProbability
  parentProbability_nonneg := kernel.parentProbability_nonneg
  parentProbability_le_one := kernel.parentProbability_le_one
  childProbability left right :=
    (1 - mixing) * kernel.childProbability left right + mixing / 2
  childProbability_nonneg := by
    intro left right
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hmixing_one)
        (kernel.childProbability_nonneg left right))
      (div_nonneg hmixing_zero (by norm_num))
  childProbability_le_one := by
    intro left right
    have hproduct := mul_le_mul_of_nonneg_left
      (kernel.childProbability_le_one left right)
      (sub_nonneg.mpr hmixing_one)
    nlinarith
noncomputable def smoothedConditionalEntropy
    (kernel : BinaryPairKernel) (mixing : ℝ) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      binaryEntropy
        ((1 - mixing) * kernel.childProbability left right + mixing / 2)
end BinaryPairKernel
def empiricalBinaryOutcomeCount
    (parentCount oneCount : ℕ) (outcome : Bool) : ℝ :=
  if outcome then (oneCount : ℝ)
  else (parentCount : ℝ) - (oneCount : ℝ)
noncomputable def withoutReplacementBinaryPairMass
    (parentCount oneCount : ℕ) (left right : Bool) : ℝ :=
  empiricalBinaryOutcomeCount parentCount oneCount left *
      (empiricalBinaryOutcomeCount parentCount oneCount right -
        if left = right then 1 else 0) /
    ((parentCount : ℝ) * ((parentCount : ℝ) - 1))
noncomputable def withoutReplacementBinaryPairExpectation
    (parentCount oneCount : ℕ) (f : Bool → Bool → ℝ) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    withoutReplacementBinaryPairMass parentCount oneCount left right *
      f left right
noncomputable def empiricalChildMarginal
    (parentCount oneCount : ℕ) (kernel : BinaryPairKernel) : ℝ :=
  withoutReplacementBinaryPairExpectation parentCount oneCount
    kernel.childProbability
noncomputable def empiricalConditionalEntropy
    (parentCount oneCount : ℕ) (kernel : BinaryPairKernel) : ℝ :=
  withoutReplacementBinaryPairExpectation parentCount oneCount
    (fun left right => binaryEntropy (kernel.childProbability left right))
noncomputable def empiricalAverageDisagreement
    (parentCount oneCount : ℕ) (kernel : BinaryPairKernel) : ℝ :=
  withoutReplacementBinaryPairExpectation parentCount oneCount
    (fun left right =>
      (BinaryPairKernel.bitDisagreementProbability left
          (kernel.childProbability left right) +
        BinaryPairKernel.bitDisagreementProbability right
          (kernel.childProbability left right)) / 2)
noncomputable def binomialProbabilityMass
    (trialCount successCount : ℕ) (probability : ℝ) : ℝ :=
  (trialCount.choose successCount : ℝ) *
    probability ^ successCount *
    (1 - probability) ^ (trialCount - successCount)
theorem certificate_ratio_one_lt :
    (1 : ℝ) < (97 + 56 * Real.sqrt 3) / 192 := by
  have h := twelve_sevenths_lt_sqrt_three
  nlinarith
theorem certifiedWindowWidth_pos : 0 < certifiedWindowWidth := by
  unfold certifiedWindowWidth logTwo
  exact div_pos
    (div_pos (Real.log_pos certificate_ratio_one_lt)
      log_two_pos)
    (by norm_num)
theorem tau_pos : 0 < tau := by
  unfold tau
  nlinarith [twelve_sevenths_lt_sqrt_three]
theorem sqrt_three_pos : 0 < Real.sqrt (3 : ℝ) := by
  positivity
theorem tau_complement : 1 - tau = Real.sqrt 3 * tau := by
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  unfold tau
  nlinarith
theorem tau_reciprocal_identity :
    1 + 1 / Real.sqrt 3 = (1 - tau)⁻¹ := by
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  rw [tau_complement]
  field_simp [sqrt_three_pos.ne', tau_pos.ne']
  unfold tau
  nlinarith
theorem log_three_eq_twice_log_sqrt_three :
    Real.log (3 : ℝ) = 2 * Real.log (Real.sqrt 3) := by
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  calc
    Real.log (3 : ℝ) = Real.log ((Real.sqrt 3) ^ 2) := by rw [hsqrt_sq]
    _ = 2 * Real.log (Real.sqrt 3) := by
      rw [Real.log_pow]
      ring
theorem entropy_tau_identity :
    2 * binaryEntropy tau - tau * logTwo 3 =
      2 * logTwo (1 + 1 / Real.sqrt 3) := by
  have hlog_complement :
      Real.log (1 - tau) = Real.log (Real.sqrt 3) + Real.log tau := by
    rw [tau_complement, Real.log_mul sqrt_three_pos.ne' tau_pos.ne']
  unfold binaryEntropy logTwo Real.binEntropy
  rw [Real.log_inv, Real.log_inv, tau_reciprocal_identity, Real.log_inv,
    hlog_complement, log_three_eq_twice_log_sqrt_three]
  ring
theorem certificate_ratio_identity :
    (1 + 1 / Real.sqrt 3) ^ (8 : ℕ) * 27 / 1024 =
      (97 + 56 * Real.sqrt 3) / 192 := by
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by positivity)
  have hz : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  field_simp [hz]
  ring_nf at hs ⊢
  linear_combination
    (-1728 - 13824 * Real.sqrt 3
      - 48960 * Real.sqrt 3 ^ 2
      - 101376 * Real.sqrt 3 ^ 3
      - 137280 * Real.sqrt 3 ^ 4
      - 130560 * Real.sqrt 3 ^ 5
      - 94144 * Real.sqrt 3 ^ 6
      - 57344 * Real.sqrt 3 ^ 7) * hs
theorem log_certificate_ratio_identity :
    Real.log ((97 + 56 * Real.sqrt 3) / 192) =
      8 * Real.log (1 + 1 / Real.sqrt 3) +
        3 * Real.log 3 - 10 * Real.log 2 := by
  have hu : 0 < (1 : ℝ) + 1 / Real.sqrt 3 := by
    positivity
  have hlog27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    calc
      Real.log (27 : ℝ) = Real.log ((3 : ℝ) ^ (3 : ℕ)) := by norm_num
      _ = 3 * Real.log 3 := by rw [Real.log_pow]; norm_num
  have hlog1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    calc
      Real.log (1024 : ℝ) = Real.log ((2 : ℝ) ^ (10 : ℕ)) := by norm_num
      _ = 10 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [← certificate_ratio_identity,
    Real.log_div (by positivity) (by norm_num),
    Real.log_mul (by positivity) (by norm_num),
    Real.log_pow, hlog27, hlog1024]
  ring
noncomputable def entropyLowerEndpoint : ℝ := kappa + tau * logTwo 3
noncomputable def entropyUpperEndpoint : ℝ := 2 * binaryEntropy tau - 1
noncomputable def midpointBeta : ℝ :=
  (entropyLowerEndpoint + entropyUpperEndpoint) / 2
theorem entropyWindow_eq_certifiedWindowWidth :
    entropyUpperEndpoint - entropyLowerEndpoint = certifiedWindowWidth := by
  have hentropy := entropy_tau_identity
  have hlog := log_certificate_ratio_identity
  unfold logTwo at hentropy
  have hlog_argument :
      (Real.sqrt 3 + 1) / Real.sqrt 3 =
        1 + 1 / Real.sqrt 3 := by
    field_simp [sqrt_three_pos.ne']
  unfold entropyUpperEndpoint entropyLowerEndpoint kappa
    certifiedWindowWidth logTwo
  field_simp [log_two_pos.ne'] at hentropy ⊢
  rw [hlog_argument] at hentropy
  ring_nf at hentropy hlog ⊢
  linarith
theorem entropyWindow_pos : entropyLowerEndpoint < entropyUpperEndpoint := by
  have h := certifiedWindowWidth_pos
  rw [← entropyWindow_eq_certifiedWindowWidth] at h
  linarith
theorem midpointBeta_gt_lower
    (hwindow : entropyLowerEndpoint < entropyUpperEndpoint) :
    entropyLowerEndpoint < midpointBeta := by
  unfold midpointBeta
  linarith
theorem midpointBeta_gt_lower_unconditional :
    entropyLowerEndpoint < midpointBeta :=
  midpointBeta_gt_lower entropyWindow_pos
theorem logTwo_three_pos : 0 < logTwo 3 := by
  unfold logTwo
  exact div_pos (Real.log_pos (by norm_num)) log_two_pos
theorem logTwo_three_lt_two : logTwo 3 < 2 := by
  have hlog : Real.log (3 : ℝ) < Real.log 4 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  unfold logTwo
  apply (div_lt_iff₀ log_two_pos).mpr
  nlinarith [hlog]
theorem kappa_pos : 0 < kappa := by
  unfold kappa
  nlinarith [logTwo_three_lt_two]
theorem entropyLowerEndpoint_pos : 0 < entropyLowerEndpoint := by
  unfold entropyLowerEndpoint
  positivity [kappa_pos, tau_pos, logTwo_three_pos]
theorem midpointBeta_pos : 0 < midpointBeta :=
  entropyLowerEndpoint_pos.trans midpointBeta_gt_lower_unconditional
noncomputable def entropySlack : ℝ := certifiedWindowWidth / 8
noncomputable def exponentGain : ℝ :=
  certifiedWindowWidth / (8 * (1 - midpointBeta))
noncomputable def empiricalEntropyError (layerSize : ℕ) : ℝ :=
  (1 + logTwo 3) / (layerSize : ℝ) +
    binaryEntropy (1 / (layerSize : ℝ)) / 2
end BinaryEntropy
section ForbiddenGraph
noncomputable def neighborsWithin {V : Type*} (G : SimpleGraph V)
    (s : Finset V) (v : V) : Finset V := by
  classical
  exact s.filter (G.Adj v)
def IsDegenerate {V : Type*} (r : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty →
    ∃ v ∈ s, (neighborsWithin G s v).card ≤ r
abbrev IsTwoDegenerate {V : Type*} (G : SimpleGraph V) : Prop :=
  IsDegenerate 2 G
def DegeneracyConjectureStatement : Prop :=
  ∀ (r q : ℕ) (H : SimpleGraph (Fin q)),
    0 < r → H.IsBipartite → IsDegenerate r H →
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ => (SimpleGraph.extremalNumber n H : ℝ))
        (fun n : ℕ => (n : ℝ) ^ (((2 : ℕ) : ℝ) - 1 / (r : ℝ)))
structure ParentSystem (V : Type*) where
  level : V → ℕ
  parents : V → Finset V
  parent_level : ∀ ⦃v u : V⦄, u ∈ parents v → level u + 1 = level v
  parent_card : ∀ v : V, (parents v).card ≤ 2
namespace ParentSystem
def graph {V : Type*} (P : ParentSystem V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v u => u ∈ P.parents v)
end ParentSystem
def PairLayer (baseSize : ℕ) : ℕ → Type
  | 0 => Fin baseSize
  | i + 1 => {parents : Finset (PairLayer baseSize i) // parents.card = 2}
noncomputable instance pairLayerFintype (baseSize i : ℕ) :
    Fintype (PairLayer baseSize i) := by
  classical
  induction i with
  | zero =>
      change Fintype (Fin baseSize)
      infer_instance
  | succ i ih =>
      letI := ih
      change Fintype
        {parents : Finset (PairLayer baseSize i) // parents.card = 2}
      infer_instance
theorem pairLayer_card_zero (baseSize : ℕ) :
    Fintype.card (PairLayer baseSize 0) = baseSize := by
  change Fintype.card (Fin baseSize) = baseSize
  simp
theorem pairLayer_card_succ (baseSize i : ℕ) :
    Fintype.card (PairLayer baseSize (i + 1)) =
      (Fintype.card (PairLayer baseSize i)).choose 2 := by
  classical
  let layerPairs : Finset (Finset (PairLayer baseSize i)) :=
    (Finset.univ : Finset (PairLayer baseSize i)).powersetCard 2
  let equivalence : PairLayer baseSize (i + 1) ≃ layerPairs :=
    { toFun := fun p =>
        ⟨p.val, by
          apply Finset.mem_powersetCard.mpr
          exact ⟨Finset.subset_univ _, p.property⟩⟩
      invFun := fun p => ⟨p.val, (Finset.mem_powersetCard.mp p.property).2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  calc
    Fintype.card (PairLayer baseSize (i + 1)) = Fintype.card layerPairs :=
      Fintype.card_congr equivalence
    _ = layerPairs.card := Fintype.card_coe layerPairs
    _ = (Fintype.card (PairLayer baseSize i)).choose 2 := by
      simp [layerPairs]
theorem le_choose_two_of_four {size : ℕ} (hsize : 4 ≤ size) :
    size ≤ size.choose 2 := by
  have hreal : (4 : ℝ) ≤ (size : ℝ) := by
    exact_mod_cast hsize
  have hchoose :
      (size.choose 2 : ℝ) =
        (size : ℝ) * ((size : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ size
  have hbound : (size : ℝ) ≤ (size.choose 2 : ℝ) := by
    rw [hchoose]
    nlinarith [sq_nonneg ((size : ℝ) - 2)]
  exact_mod_cast hbound
theorem pairLayer_card_ge_base
    (baseSize i : ℕ) (hbase : 4 ≤ baseSize) :
    baseSize ≤ Fintype.card (PairLayer baseSize i) := by
  induction i with
  | zero =>
      rw [pairLayer_card_zero]
  | succ i ih =>
      rw [pairLayer_card_succ]
      exact ih.trans
        (le_choose_two_of_four (hbase.trans ih))
noncomputable def pairLayerFinEquiv (baseSize layer : ℕ) :
    PairLayer baseSize layer ≃
      Fin (Fintype.card (PairLayer baseSize layer)) :=
  Fintype.equivFin (PairLayer baseSize layer)
noncomputable def pairLayerPairEquiv (baseSize layer : ℕ) :
    PairLayer (Fintype.card (PairLayer baseSize layer)) 1 ≃
      PairLayer baseSize (layer + 1) := by
  classical
  change
    {parents : Finset
      (Fin (Fintype.card (PairLayer baseSize layer))) //
        parents.card = 2} ≃
      {parents : Finset (PairLayer baseSize layer) //
        parents.card = 2}
  exact
    (pairLayerFinEquiv baseSize layer).symm.finsetCongr.subtypeEquiv
      (fun parents => by
        simp [Equiv.finsetCongr_apply])
abbrev PairVertex (baseSize depth : ℕ) :=
  Σ i : Fin (depth + 1), PairLayer baseSize i.val
def pairLayerEmbedding (baseSize depth i : ℕ) (hi : i < depth + 1) :
    PairLayer baseSize i ↪ PairVertex baseSize depth where
  toFun v := ⟨⟨i, hi⟩, v⟩
  inj' := by
    intro v w heq
    cases heq
    rfl
noncomputable def pairParents (baseSize depth : ℕ) :
    PairVertex baseSize depth → Finset (PairVertex baseSize depth)
  | ⟨⟨0, _⟩, _⟩ => ∅
  | ⟨⟨i + 1, hi⟩, v⟩ =>
      v.val.map (pairLayerEmbedding baseSize depth i (by omega))
noncomputable def pairParentSystem (baseSize depth : ℕ) :
    ParentSystem (PairVertex baseSize depth) where
  level v := v.1.val
  parents := pairParents baseSize depth
  parent_level := by
    classical
    rintro ⟨⟨i, hi⟩, v⟩ ⟨⟨j, hj⟩, u⟩ hparent
    cases i with
    | zero =>
        simp [pairParents] at hparent
    | succ i =>
        change {parents : Finset (PairLayer baseSize i) // parents.card = 2} at v
        simp only [pairParents, Finset.mem_map] at hparent
        obtain ⟨w, _, hw⟩ := hparent
        have hlevels := congrArg
          (fun z : PairVertex baseSize depth => z.1.val) hw
        change i = j at hlevels
        change j + 1 = i + 1
        omega
  parent_card := by
    classical
    rintro ⟨⟨i, hi⟩, v⟩
    cases i with
    | zero =>
        simp [pairParents]
    | succ i =>
        change {parents : Finset (PairLayer baseSize i) // parents.card = 2} at v
        simp [pairParents, v.property]
def pairBaseVertex (baseSize depth : ℕ) (a : Fin baseSize) :
    PairVertex baseSize depth :=
  pairLayerEmbedding baseSize depth 0 (by omega) a
noncomputable def pairGraphOverFin (baseSize depth : ℕ) :
    SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) :=
  (pairParentSystem baseSize depth).graph.overFin rfl
noncomputable def pairGraphOverFinIso (baseSize depth : ℕ) :
    (pairParentSystem baseSize depth).graph ≃g
      pairGraphOverFin baseSize depth :=
  (pairParentSystem baseSize depth).graph.overFinIso rfl
end ForbiddenGraph
section HammingProfiles
abbrev HammingWord (dimension : ℕ) := Fin dimension → Bool
noncomputable def booleanWordOnes {ι : Type*} [Fintype ι]
    (word : ι → Bool) : Finset ι := by
  classical
  exact Finset.univ.filter (fun index => word index = true)
noncomputable def booleanWordsOfWeight (ι : Type*) [Fintype ι]
    (weight : ℕ) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter
    (fun word => (booleanWordOnes word).card = weight)
noncomputable def booleanWordsOfWeightEquiv
    (ι : Type*) [Fintype ι] (weight : ℕ) :
    ↥(booleanWordsOfWeight ι weight) ≃
      ↥((Finset.univ : Finset ι).powersetCard weight) := by
  classical
  refine
    { toFun := fun word => ⟨booleanWordOnes word.val, ?_⟩
      invFun := fun support =>
        ⟨fun index => decide (index ∈ support.val), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    have hword :
        word.val ∈
          (Finset.univ.filter
            (fun candidate : ι → Bool =>
              (booleanWordOnes candidate).card = weight)) := by
      simpa only [booleanWordsOfWeight] using word.property
    exact (Finset.mem_filter.mp hword).2
  · have hsupport :=
      (Finset.mem_powersetCard.mp support.property).2
    have hones :
        booleanWordOnes
          (fun index : ι => decide (index ∈ support.val)) = support.val := by
      ext index
      simp [booleanWordOnes]
    simp only [booleanWordsOfWeight, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hones]
    exact hsupport
  · intro word
    apply Subtype.ext
    funext index
    cases hbit : word.val index <;>
      simp [booleanWordOnes, hbit]
  · intro support
    apply Subtype.ext
    ext index
    simp [booleanWordOnes]
abbrev ClassificationFiber
    {ι γ : Type*} (classify : ι → γ) (group : γ) :=
  {index : ι // classify index = group}
noncomputable def classificationGroup
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) : Finset ι :=
  Finset.univ.filter (fun index => classify index = group)
noncomputable def classifiedWordOnes
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) (word : ι → Bool) : Finset ι :=
  (classificationGroup classify group).filter
    (fun index => word index = true)
noncomputable def classifiedWordSupportEquiv
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) (word : ι → Bool) :
    ↥(booleanWordOnes
        (fun index : ClassificationFiber classify group => word index.val)) ≃
      ↥(classifiedWordOnes classify group word) := by
  classical
  refine
    { toFun := fun index => ⟨index.val.val, ?_⟩
      invFun := fun index => ⟨⟨index.val, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hbit : word index.val.val = true := by
      have hmembership :
          index.val ∈
            (Finset.univ.filter
              (fun candidate : ClassificationFiber classify group =>
                word candidate.val = true)) := by
        simpa only [booleanWordOnes] using index.property
      exact (Finset.mem_filter.mp hmembership).2
    simp [classifiedWordOnes, classificationGroup,
      index.val.property, hbit]
  · have hmembership :
        index.val ∈
          (classificationGroup classify group).filter
            (fun candidate => word candidate = true) := by
      simpa only [classifiedWordOnes] using index.property
    have hgroup := (Finset.mem_filter.mp hmembership).1
    exact (Finset.mem_filter.mp hgroup).2
  · have hmembership :
        index.val ∈
          (classificationGroup classify group).filter
            (fun candidate => word candidate = true) := by
      simpa only [classifiedWordOnes] using index.property
    have hbit := (Finset.mem_filter.mp hmembership).2
    simp [booleanWordOnes, hbit]
  · intro index
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro index
    apply Subtype.ext
    rfl
theorem classifiedWordOnes_card
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) (word : ι → Bool) :
    (classifiedWordOnes classify group word).card =
      (booleanWordOnes
        (fun index : ClassificationFiber classify group => word index.val)).card := by
  calc
    (classifiedWordOnes classify group word).card =
        Fintype.card ↥(classifiedWordOnes classify group word) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        ↥(booleanWordOnes
          (fun index : ClassificationFiber classify group => word index.val)) :=
      Fintype.card_congr
        (classifiedWordSupportEquiv classify group word).symm
    _ = (booleanWordOnes
          (fun index : ClassificationFiber classify group => word index.val)).card :=
      Fintype.card_coe _
noncomputable def classifiedBooleanWords
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter
    (fun word => ∀ group,
      (classifiedWordOnes classify group word).card = counts group)
noncomputable def classifiedBooleanWordsEquiv
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) :
    ↥(classifiedBooleanWords classify counts) ≃
      (∀ group : γ,
        ↥(booleanWordsOfWeight
          (ClassificationFiber classify group) (counts group))) := by
  classical
  refine
    { toFun := fun word group =>
        ⟨fun index => word.val index.val, ?_⟩
      invFun := fun pieces =>
        ⟨fun index => (pieces (classify index)).val ⟨index, rfl⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership :
        word.val ∈
          (Finset.univ.filter
            (fun candidate : ι → Bool =>
              ∀ group,
                (classifiedWordOnes classify group candidate).card =
                  counts group)) := by
      simpa only [classifiedBooleanWords] using word.property
    have hprofile := (Finset.mem_filter.mp hmembership).2 group
    simp only [booleanWordsOfWeight, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (classifiedWordOnes_card classify group word.val).symm.trans
      hprofile
  · simp only [classifiedBooleanWords, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro group
    rw [classifiedWordOnes_card]
    have hrestriction :
        (fun index : ClassificationFiber classify group =>
          (pieces (classify index.val)).val
            ⟨index.val, rfl⟩) =
          (pieces group).val := by
      funext index
      rcases index with ⟨index, hindex⟩
      cases hindex
      rfl
    rw [hrestriction]
    have hmembership := (pieces group).property
    unfold booleanWordsOfWeight at hmembership
    exact (Finset.mem_filter.mp hmembership).2
  · intro word
    apply Subtype.ext
    funext index
    rfl
  · intro pieces
    funext group
    apply Subtype.ext
    funext index
    rcases index with ⟨index, hindex⟩
    cases hindex
    rfl
abbrev PairBitType := Fin 3
abbrev PairTypeCountProfile (parentCount dimension : ℕ) :=
  PairBitType → Fin dimension → Fin (parentCount.choose 2 + 1)
noncomputable def pairCoordinateBitType
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1) : PairBitType := by
  classical
  exact
    if ∀ parent ∈ pair.val, parents parent coordinate = false then 0
    else if ∀ parent ∈ pair.val, parents parent coordinate = true then 1
    else 2
noncomputable def pairTypeGroup
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) : Finset (PairLayer parentCount 1) := by
  classical
  exact Finset.univ.filter
    (fun pair => pairCoordinateBitType parents coordinate pair = bitType)
noncomputable def pairCoordinateClassification
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension) :
    PairLayer parentCount 1 × Fin dimension → PairBitType × Fin dimension :=
  fun index =>
    (pairCoordinateBitType parents index.2 index.1, index.2)
noncomputable def pairCoordinateClassificationFiberEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (bitType : PairBitType) (coordinate : Fin dimension) :
    ClassificationFiber
        (pairCoordinateClassification parents) (bitType, coordinate) ≃
      ↥(pairTypeGroup parents coordinate bitType) := by
  classical
  refine
    { toFun := fun index => ⟨index.val.1, ?_⟩
      invFun := fun pair => ⟨(pair.val, coordinate), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have htype := congrArg Prod.fst index.property
    have hcoordinate : index.val.2 = coordinate := by
      simpa [pairCoordinateClassification] using
        congrArg Prod.snd index.property
    simp only [pairTypeGroup, Finset.mem_filter,
      Finset.mem_univ, true_and]
    simpa [pairCoordinateClassification, hcoordinate] using htype
  · have hmembership :
        pair.val ∈
          (Finset.univ.filter
            (fun candidate : PairLayer parentCount 1 =>
              pairCoordinateBitType parents coordinate candidate = bitType)) := by
      simpa only [pairTypeGroup] using pair.property
    have htype := (Finset.mem_filter.mp hmembership).2
    change
      (pairCoordinateBitType parents coordinate pair.val, coordinate) =
        (bitType, coordinate)
    exact Prod.ext htype rfl
  · intro index
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hcoordinate := congrArg Prod.snd index.property
      simpa [pairCoordinateClassification] using hcoordinate.symm
  · intro pair
    apply Subtype.ext
    rfl
theorem pairTypeGroup_card_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    (pairTypeGroup parents coordinate bitType).card ≤
      parentCount.choose 2 := by
  classical
  calc
    (pairTypeGroup parents coordinate bitType).card ≤
      (Finset.univ : Finset (PairLayer parentCount 1)).card := by
        unfold pairTypeGroup
        exact Finset.card_filter_le _ _
    _ = parentCount.choose 2 := by
      rw [Finset.card_univ, pairLayer_card_succ parentCount 0,
        pairLayer_card_zero]
noncomputable def pairTypeGroupChildOnes
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) : Finset (PairLayer parentCount 1) := by
  classical
  exact (pairTypeGroup parents coordinate bitType).filter
    (fun pair => children pair coordinate = true)
theorem pairTypeGroupChildOnes_card_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    (pairTypeGroupChildOnes parents children coordinate bitType).card ≤
      (pairTypeGroup parents coordinate bitType).card := by
  classical
  unfold pairTypeGroupChildOnes
  exact Finset.card_filter_le _ _
def flattenPairChildArray
    {parentCount dimension : ℕ}
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    PairLayer parentCount 1 × Fin dimension → Bool :=
  fun index => children index.1 index.2
theorem pairChildClassificationOnes_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (bitType : PairBitType) (coordinate : Fin dimension) :
    (classifiedWordOnes
      (pairCoordinateClassification parents) (bitType, coordinate)
      (flattenPairChildArray children)).card =
        (pairTypeGroupChildOnes parents children coordinate bitType).card := by
  classical
  apply Finset.card_bij (fun index _ => index.1)
  · intro index hindex
    have hclassified :
        index ∈
          (classificationGroup (pairCoordinateClassification parents)
            (bitType, coordinate)).filter
              (fun candidate =>
                flattenPairChildArray children candidate = true) := by
      simpa only [classifiedWordOnes] using hindex
    have hparts := Finset.mem_filter.mp hclassified
    have hgroup := (Finset.mem_filter.mp hparts.1).2
    have htype := congrArg Prod.fst hgroup
    have hcoordinate := congrArg Prod.snd hgroup
    have hcoord : index.2 = coordinate := by
      simpa [pairCoordinateClassification] using hcoordinate
    simp only [pairTypeGroupChildOnes, Finset.mem_filter]
    constructor
    · simp only [pairTypeGroup, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simpa [pairCoordinateClassification, hcoord] using htype
    · simpa [flattenPairChildArray, hcoord] using hparts.2
  · intro first hfirst second hsecond hequal
    apply Prod.ext
    · exact hequal
    · have hfirst_group :=
        (Finset.mem_filter.mp hfirst).1
      have hsecond_group :=
        (Finset.mem_filter.mp hsecond).1
      have hfirst_class :=
        (Finset.mem_filter.mp hfirst_group).2
      have hsecond_class :=
        (Finset.mem_filter.mp hsecond_group).2
      have hfirst_coordinate := congrArg Prod.snd hfirst_class
      have hsecond_coordinate := congrArg Prod.snd hsecond_class
      simpa [pairCoordinateClassification] using
        hfirst_coordinate.trans hsecond_coordinate.symm
  · intro pair hpair
    refine ⟨(pair, coordinate), ?_, rfl⟩
    have hpair_parts := Finset.mem_filter.mp hpair
    have hpair_type := (Finset.mem_filter.mp hpair_parts.1).2
    change
      (pair, coordinate) ∈
        (classificationGroup (pairCoordinateClassification parents)
          (bitType, coordinate)).filter
            (fun index => flattenPairChildArray children index = true)
    apply Finset.mem_filter.mpr
    constructor
    · unfold classificationGroup
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact Prod.ext hpair_type rfl
    · exact hpair_parts.2
noncomputable def pairChildCountProfile
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    PairTypeCountProfile parentCount dimension := by
  intro bitType coordinate
  refine ⟨(pairTypeGroupChildOnes parents children coordinate bitType).card, ?_⟩
  have hones := pairTypeGroupChildOnes_card_le
    parents children coordinate bitType
  have hgroup := pairTypeGroup_card_le parents coordinate bitType
  omega
noncomputable def pairChildArraysOfProfile
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : PairTypeCountProfile parentCount dimension) :
    Finset (PairLayer parentCount 1 → HammingWord dimension) := by
  classical
  exact Finset.univ.filter
    (fun children => pairChildCountProfile parents children = profile)
noncomputable def pairChildArraysOfProfileEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : PairTypeCountProfile parentCount dimension) :
    ↥(pairChildArraysOfProfile parents profile) ≃
      ↥(classifiedBooleanWords
        (pairCoordinateClassification parents)
        (fun index : PairBitType × Fin dimension =>
          (profile index.1 index.2).val)) := by
  classical
  refine
    { toFun := fun children =>
        ⟨flattenPairChildArray children.val, ?_⟩
      invFun := fun word =>
        ⟨fun pair coordinate => word.val (pair, coordinate), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership := children.property
    unfold pairChildArraysOfProfile at hmembership
    have hprofile := (Finset.mem_filter.mp hmembership).2
    simp only [classifiedBooleanWords, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rintro ⟨bitType, coordinate⟩
    rw [pairChildClassificationOnes_card]
    have hcount := congrArg
      (fun candidate : PairTypeCountProfile parentCount dimension =>
        (candidate bitType coordinate).val) hprofile
    simpa [pairChildCountProfile] using hcount
  · simp only [pairChildArraysOfProfile, Finset.mem_filter,
      Finset.mem_univ, true_and]
    funext bitType
    funext coordinate
    apply Fin.ext
    change
      (pairTypeGroupChildOnes parents
        (fun pair coordinate => word.val (pair, coordinate))
        coordinate bitType).card = (profile bitType coordinate).val
    have hmembership := word.property
    unfold classifiedBooleanWords at hmembership
    have hprofile :=
      (Finset.mem_filter.mp hmembership).2 (bitType, coordinate)
    rw [← pairChildClassificationOnes_card]
    have hflatten :
        flattenPairChildArray
          (fun pair coordinate => word.val (pair, coordinate)) =
            word.val := by
      funext index
      rcases index with ⟨pair, coordinate⟩
      rfl
    rw [hflatten]
    exact hprofile
  · intro children
    apply Subtype.ext
    funext pair
    funext coordinate
    rfl
  · intro word
    apply Subtype.ext
    funext index
    rcases index with ⟨pair, coordinate⟩
    rfl
noncomputable def pairCoordinateConditionalEntropy
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : ℝ :=
  ∑ bitType : PairBitType,
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      binaryEntropy
        (((pairTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
          ((pairTypeGroup parents coordinate bitType).card : ℝ))
noncomputable def pairChildArrayEntropy
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    pairCoordinateConditionalEntropy parents children coordinate) /
      (dimension : ℝ)
noncomputable def pairParentCoordinateOneCount
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) : ℕ :=
  (booleanWordOnes (fun parent => parents parent coordinate)).card
theorem pairParentCoordinateOneCount_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    pairParentCoordinateOneCount parents coordinate ≤ parentCount := by
  classical
  unfold pairParentCoordinateOneCount booleanWordOnes
  calc
    (Finset.univ.filter
      (fun parent : Fin parentCount =>
        parents parent coordinate = true)).card ≤
        (Finset.univ : Finset (Fin parentCount)).card :=
      Finset.card_filter_le _ _
    _ = parentCount := by simp
noncomputable def pairParentCoordinateSupport
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (outcome : Bool) : Finset (Fin parentCount) := by
  classical
  exact Finset.univ.filter
    (fun parent => parents parent coordinate = outcome)
theorem pairCoordinateBitType_homogeneous_iff
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1)
    (outcome : Bool) :
    pairCoordinateBitType parents coordinate pair =
        (if outcome then (1 : PairBitType) else 0) ↔
      ∀ parent ∈ pair.val, parents parent coordinate = outcome := by
  classical
  obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp pair.property
  cases outcome <;> cases ha : parents a coordinate <;>
    cases hb : parents b coordinate <;>
    simp_all [pairCoordinateBitType]
noncomputable def pairTypeGroupHomogeneousEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (outcome : Bool) :
    ↥(pairTypeGroup parents coordinate
      (if outcome then (1 : PairBitType) else 0)) ≃
      ↥((pairParentCoordinateSupport parents coordinate outcome).powersetCard 2) := by
  classical
  refine
    { toFun := fun pair => ⟨pair.val.val, ?_⟩
      invFun := fun support =>
        ⟨⟨support.val, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership := pair.property
    unfold pairTypeGroup at hmembership
    have htype := (Finset.mem_filter.mp hmembership).2
    have hhomogeneous :=
      (pairCoordinateBitType_homogeneous_iff
        parents coordinate pair.val outcome).mp htype
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, pair.val.property⟩
    intro parent hparent
    unfold pairParentCoordinateSupport
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hhomogeneous parent hparent⟩
  · exact (Finset.mem_powersetCard.mp support.property).2
  · unfold pairTypeGroup
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (pairCoordinateBitType_homogeneous_iff
      parents coordinate
      ⟨support.val, (Finset.mem_powersetCard.mp support.property).2⟩
      outcome).mpr
    intro parent hparent
    have hsubset :=
      (Finset.mem_powersetCard.mp support.property).1
    have hsupport := hsubset hparent
    unfold pairParentCoordinateSupport at hsupport
    exact (Finset.mem_filter.mp hsupport).2
  · intro pair
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro support
    apply Subtype.ext
    rfl
def pairBitTypeOfOutcomes (left right : Bool) : PairBitType :=
  if left = false ∧ right = false then 0
  else if left = true ∧ right = true then 1
  else 2
noncomputable def pairCoordinateKernel
    {parentCount dimension : ℕ}
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : BinaryPairKernel where
  parentProbability :=
    (pairParentCoordinateOneCount parents coordinate : ℝ) /
      (parentCount : ℝ)
  parentProbability_nonneg := by
    positivity
  parentProbability_le_one := by
    have hpositive : 0 < (parentCount : ℝ) := by
      exact_mod_cast hparents
    apply (div_le_one hpositive).mpr
    exact_mod_cast pairParentCoordinateOneCount_le parents coordinate
  childProbability left right :=
    ((pairTypeGroupChildOnes parents children coordinate
      (pairBitTypeOfOutcomes left right)).card : ℝ) /
        ((pairTypeGroup parents coordinate
          (pairBitTypeOfOutcomes left right)).card : ℝ)
  childProbability_nonneg := by
    intro left right
    positivity
  childProbability_le_one := by
    intro left right
    let bitType := pairBitTypeOfOutcomes left right
    have hle := pairTypeGroupChildOnes_card_le
      parents children coordinate bitType
    by_cases hzero : (pairTypeGroup parents coordinate bitType).card = 0
    · simp [bitType, hzero]
    · have hpositive :
          0 < ((pairTypeGroup parents coordinate bitType).card : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      apply (div_le_one hpositive).mpr
      exact_mod_cast hle
noncomputable def pairChildCoordinateOneCount
    {parentCount dimension : ℕ}
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : ℕ :=
  (booleanWordOnes (fun pair => children pair coordinate)).card
noncomputable def pairCoordinatePairMismatchCount
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1) : ℕ := by
  classical
  exact (pair.val.filter
    (fun parent =>
      parents parent coordinate ≠ children pair coordinate)).card
noncomputable def pairParentArrayEntropyPotential
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      ((pairParentCoordinateOneCount parents coordinate : ℝ) /
        (parentCount : ℝ))) /
      (dimension : ℝ)
noncomputable def pairChildArrayEntropyPotential
    {parentCount dimension : ℕ}
    (children : PairLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      ((pairChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose 2 : ℝ))) /
      (dimension : ℝ)
noncomputable def pairChildArrayAverageDisagreement
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    empiricalAverageDisagreement parentCount
      (pairParentCoordinateOneCount parents coordinate)
      (pairCoordinateKernel (by omega) parents children coordinate)) /
    (dimension : ℝ)
noncomputable def badPairChildArrays
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (threshold : ℝ) :
    Finset (PairLayer parentCount 1 → HammingWord dimension) := by
  classical
  exact Finset.univ.filter
    (fun children => pairChildArrayEntropy parents children ≤ threshold)
end HammingProfiles
section SamplingAndHammingBalls
noncomputable def hammingRetentionProbability (dimension : ℕ) : ℝ :=
  Real.exp (-(midpointBeta * (dimension : ℝ) * Real.log 2))
theorem hammingRetentionProbability_pos (dimension : ℕ) :
    0 < hammingRetentionProbability dimension := by
  unfold hammingRetentionProbability
  exact Real.exp_pos _
theorem hammingRetentionProbability_le_one (dimension : ℕ) :
    hammingRetentionProbability dimension ≤ 1 := by
  unfold hammingRetentionProbability
  apply Real.exp_le_one_iff.mpr
  have hproduct :
      0 ≤ midpointBeta * (dimension : ℝ) * Real.log 2 :=
    mul_nonneg
      (mul_nonneg midpointBeta_pos.le (Nat.cast_nonneg dimension))
      log_two_pos.le
  linarith
noncomputable def hammingRetentionParameter (dimension : ℕ) : unitInterval :=
  ⟨hammingRetentionProbability dimension,
    hammingRetentionProbability_pos dimension |>.le,
    hammingRetentionProbability_le_one dimension⟩
noncomputable def hammingRetentionMeasure (dimension : ℕ) :
    MeasureTheory.Measure (Set (Bool × HammingWord dimension)) :=
  ProbabilityTheory.setBernoulli Set.univ
    (hammingRetentionParameter dimension)
noncomputable def hammingExpectedRetainedVertexCount
    (dimension : ℕ) : ℝ :=
  ∑ vertex : Bool × HammingWord dimension,
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        vertex ∈ retained}
noncomputable def hammingExpectedRetainedVertexSquare
    (dimension : ℕ) : ℝ :=
  ∑ first : Bool × HammingWord dimension,
    ∑ second : Bool × HammingWord dimension,
      (hammingRetentionMeasure dimension).real
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained ∧ second ∈ retained}
noncomputable def hammingRetainedVertexCount
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) : ℝ := by
  classical
  exact ∑ vertex : Bool × HammingWord dimension,
    if vertex ∈ retained then 1 else 0
noncomputable def pairChildVertexFinset
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    Finset (Bool × HammingWord dimension) := by
  classical
  exact (Finset.univ : Finset (PairLayer parentCount 1)).image
    (fun pair => (side, children pair))
def pairChildRetentionEvent
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    Set (Set (Bool × HammingWord dimension)) :=
  {retained | ∀ pair, (side, children pair) ∈ retained}
noncomputable def badPairChildRetentionEvent
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (side : Bool)
    (threshold : ℝ) : Set (Set (Bool × HammingWord dimension)) := by
  classical
  exact
    ⋃ children ∈
        (badPairChildArrays parents threshold).filter Function.Injective,
      pairChildRetentionEvent side children
noncomputable def badPairLayerRetentionEvent
    (parentCount dimension : ℕ)
    (side : Bool)
    (threshold : ℝ) : Set (Set (Bool × HammingWord dimension)) :=
  ⋃ parents : Fin parentCount → HammingWord dimension,
    badPairChildRetentionEvent parents side threshold
noncomputable def badPairLayersRetentionEvent
    {depth : ℕ}
    (layerSizes : Fin depth → ℕ)
    (dimension : ℕ) : Set (Set (Bool × HammingWord dimension)) :=
  ⋃ side : Bool, ⋃ layer : Fin depth,
    badPairLayerRetentionEvent (layerSizes layer) dimension side
      (midpointBeta - entropySlack)
noncomputable def hammingDifferenceSet {dimension : ℕ}
    (u v : HammingWord dimension) : Finset (Fin dimension) := by
  classical
  exact Finset.univ.filter (fun coordinate => u coordinate ≠ v coordinate)
noncomputable def hammingFlip {dimension : ℕ}
    (u : HammingWord dimension) (coordinates : Finset (Fin dimension)) :
    HammingWord dimension := by
  classical
  exact fun coordinate =>
    if coordinate ∈ coordinates then !(u coordinate) else u coordinate
theorem hammingDifferenceSet_flip {dimension : ℕ}
    (u : HammingWord dimension) (coordinates : Finset (Fin dimension)) :
    hammingDifferenceSet u (hammingFlip u coordinates) = coordinates := by
  classical
  ext coordinate
  by_cases hcoordinate : coordinate ∈ coordinates
  · simp [hammingDifferenceSet, hammingFlip, hcoordinate]
  · simp [hammingDifferenceSet, hammingFlip, hcoordinate]
theorem hammingFlip_differenceSet {dimension : ℕ}
    (u v : HammingWord dimension) :
    hammingFlip u (hammingDifferenceSet u v) = v := by
  classical
  funext coordinate
  cases hu : u coordinate <;> cases hv : v coordinate <;>
    simp [hammingFlip, hammingDifferenceSet, hu, hv]
noncomputable def hammingBall (dimension radius : ℕ)
    (u : HammingWord dimension) : Finset (HammingWord dimension) := by
  classical
  exact Finset.univ.filter (fun v => hammingDist u v ≤ radius)
noncomputable def boundedDifferenceSets (dimension radius : ℕ) :
    Finset (Finset (Fin dimension)) := by
  classical
  exact ((Finset.univ : Finset (Fin dimension)).powerset).filter
    (fun coordinates => coordinates.card ≤ radius)
noncomputable def hammingBallEquiv (dimension radius : ℕ)
    (u : HammingWord dimension) :
    ↥(hammingBall dimension radius u) ≃
      ↥(boundedDifferenceSets dimension radius) := by
  classical
  refine
    { toFun := fun v => ⟨hammingDifferenceSet u v.val, ?_⟩
      invFun := fun coordinates =>
        ⟨hammingFlip u coordinates.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hball : hammingDist u v.val ≤ radius := by
      have hmembership : v.val ∈
          (Finset.univ.filter
            (fun w : HammingWord dimension => hammingDist u w ≤ radius)) := by
        simpa only [hammingBall] using v.property
      exact (Finset.mem_filter.mp hmembership).2
    simp only [boundedDifferenceSets, Finset.mem_filter,
      Finset.mem_powerset]
    refine ⟨Finset.subset_univ _, ?_⟩
    simpa [hammingDist, hammingDifferenceSet] using hball
  · have hcoordinates : coordinates.val.card ≤ radius := by
      have hmembership : coordinates.val ∈
          (((Finset.univ : Finset (Fin dimension)).powerset).filter
            (fun S => S.card ≤ radius)) := by
        simpa only [boundedDifferenceSets] using coordinates.property
      exact (Finset.mem_filter.mp hmembership).2
    simp only [hammingBall, Finset.mem_filter, Finset.mem_univ, true_and]
    change (hammingDifferenceSet u
      (hammingFlip u coordinates.val)).card ≤ radius
    simpa [hammingDifferenceSet_flip] using hcoordinates
  · intro v
    apply Subtype.ext
    exact hammingFlip_differenceSet u v.val
  · intro coordinates
    apply Subtype.ext
    exact hammingDifferenceSet_flip u coordinates.val
end SamplingAndHammingBalls
attribute [local instance] Classical.propDecidable
section HammingHostAndExclusion
def hammingHost (dimension radius : ℕ) :
    SimpleGraph (Bool × HammingWord dimension) :=
  SimpleGraph.fromRel
    (fun x y => x.1 ≠ y.1 ∧ hammingDist x.2 y.2 ≤ radius)
noncomputable def hammingExpectedRetainedEdgeCount
    (dimension radius : ℕ) : ℝ :=
  ∑ left : HammingWord dimension,
    ∑ right : HammingWord dimension,
      if hammingDist left right ≤ radius then
        (hammingRetentionMeasure dimension).real
          {retained : Set (Bool × HammingWord dimension) |
            (false, left) ∈ retained ∧ (true, right) ∈ retained}
      else 0
noncomputable def hammingExpectedRetainedEdgeSquare
    (dimension radius : ℕ) : ℝ :=
  ∑ firstLeft : HammingWord dimension,
    ∑ firstRight : HammingWord dimension,
      ∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            (hammingRetentionMeasure dimension).real
              {retained : Set (Bool × HammingWord dimension) |
                (false, firstLeft) ∈ retained ∧
                (true, firstRight) ∈ retained ∧
                (false, secondLeft) ∈ retained ∧
                (true, secondRight) ∈ retained}
          else 0
noncomputable def retainedHammingWordEdges
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    Finset (HammingWord dimension × HammingWord dimension) := by
  classical
  exact Finset.univ.filter (fun edge =>
    hammingDist edge.1 edge.2 ≤ radius ∧
      (false, edge.1) ∈ retained ∧ (true, edge.2) ∈ retained)
noncomputable def hammingRetainedEdgeCount
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) : ℝ := by
  classical
  exact
    ∑ left : HammingWord dimension,
      ∑ right : HammingWord dimension,
        if hammingDist left right ≤ radius ∧
            (false, left) ∈ retained ∧ (true, right) ∈ retained
        then 1 else 0
def retainedHammingHost (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) : SimpleGraph retained :=
  (hammingHost dimension radius).induce retained
noncomputable def pairGraphCopyParentWords
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    Fin (Fintype.card (PairLayer baseSize layer.val)) →
      HammingWord dimension :=
  fun parent =>
    (copy
      (pairLayerEmbedding baseSize depth layer.val (by omega)
        ((pairLayerFinEquiv baseSize layer.val).symm parent))).val.2
noncomputable def pairGraphCopyChildWords
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1 →
      HammingWord dimension :=
  fun pair =>
    (copy
      (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        ((pairLayerPairEquiv baseSize layer.val) pair))).val.2
noncomputable def pairGraphCopyChildSide
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (reference :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1) : Bool :=
  (copy
    (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
      ((pairLayerPairEquiv baseSize layer.val) reference))).val.1
noncomputable def pairGraphCopyLayerPotential
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin (depth + 1)) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      (((booleanWordOnes
        (fun vertex : PairLayer baseSize layer.val =>
          (copy
            (pairLayerEmbedding baseSize depth layer.val layer.isLt
              vertex)).val.2 coordinate)).card : ℝ) /
        (Fintype.card (PairLayer baseSize layer.val) : ℝ))) /
    (dimension : ℝ)
end HammingHostAndExclusion
section MainTheorem
noncomputable def manuscriptHammingRadius (dimension : ℕ) : ℕ :=
  ⌊tau * (dimension : ℝ)⌋₊
noncomputable def sampledHammingEdgeEntropyRate : ℝ :=
  (1 - 2 * midpointBeta) * Real.log 2 + Real.binEntropy tau
noncomputable def manuscriptSamplingFailureBound
    (depth dimension : ℕ) : ℝ :=
  (((2 * depth : ℕ) : ℝ)) *
      Real.exp (-(dimension : ℝ) * Real.log 2) +
    4 / hammingExpectedRetainedVertexCount dimension +
    (4 / hammingExpectedRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) +
      8 / (hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ)))
noncomputable def manuscriptSamplingFailureEvent
    {depth : ℕ}
    (layerSizes : Fin depth → ℕ)
    (dimension : ℕ) : Set (Set (Bool × HammingWord dimension)) :=
  (badPairLayersRetentionEvent layerSizes dimension ∪
    {retained : Set (Bool × HammingWord dimension) |
      3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) ≤
        hammingRetainedVertexCount dimension retained}) ∪
    {retained : Set (Bool × HammingWord dimension) |
      hammingRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) retained <
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2}
noncomputable def manuscriptVertexCount (dimension : ℕ) : ℕ :=
  ⌈3 * hammingRetentionProbability dimension *
    ((2 ^ dimension : ℕ) : ℝ)⌉₊
noncomputable def manuscriptExtremalPower : ℝ :=
  (3 : ℝ) / 2 + exponentGain
noncomputable def manuscriptEntropyGap : ℝ :=
  certifiedWindowWidth * Real.log 2 / 16
end MainTheorem
end TwoDegenerateGraphs


