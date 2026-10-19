-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
-- name    : OAI_GroupTheory_Hyperbolic_Presentation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:35:58.726562+00:00
-- url     : https://prove2.me/theorems/5ae3c208-4ff0-4c60-9c8a-53c81022961e
-- title:
--   The triangle presentation built from marked-line data
-- statement:
--   The group presentation and link structures of the construction.
--
--   1. **Reduced walks and local injectivity.** A walk is reduced if it never returns to the vertex two steps back; a graph homomorphism is locally injective if it is injective on the neighbours of each vertex.
--   2. **Shift schemes.** Given labels $I$, points $P$ with incidence sets $\mathrm{inc}(z)\subseteq I$, and block indices $B$, a shift scheme assigns to each block $b$ a size $\ge r$, a label set inside $\mathrm{inc}(\mathrm{point}(b))$ with coordinates in $\mathbb Z/\mathrm{size}(b)$, and a point; a label lies in at most one block over each point. Its link is the bipartite graph between triples $(i,u,v)\in I\times[r]^2$ and pairs $(b,u,j)$, where $(i,u,v)$ is attached to $(b,u,j)$ iff $i$ is in block $b$ and $j=\mathrm{coord}_b(i)+v$. Projecting to labels and points is a graph homomorphism to the incidence graph.
--   3. **Block presentation.** For a family of Cartesian blocks $b\mapsto(\text{labels},\ c=(c_1,c_2))$, with a base block and a base index, the generators are $x_{i,u,v}$, $l_{b,u,j}$ with $j\in\mathbb Z/s_b$, and $r_{b,v,k}$ with $k\in\mathbb Z/t_b$. The relators are the triangle words together with $l_{\text{base},\text{base},0}$ and $r_{\text{base},\text{base},0}$, so in the presented group
--   $$
--   x_{i,u,v}=l_{b,u,\,c_1(i)+v}^{-1}\;r_{b,v,\,c_2(i)+u}
--   $$
--   for $i$ in block $b$. The generators generate, so their multiplicative Cayley graph is connected.
--   4. **From marked-line data.** For a non-exceptional point $z$ the incidence set $I(z)$ has at least $4r^2$ labels, and a chosen two-block partition splits it into blocks indexed by $(z,\text{bool})$. This yields the block presentation, the rectangular nontriviality condition for its $x$-generators, the two shift schemes at the vertices $V$ and $W$ (first coordinate, resp. second coordinate with $u,v$ exchanged), and the swap of the incidence graph's two sides.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Presentation.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Presentation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

namespace OAI

namespace Release075

/-- Internal reduction of an edge walk; no condition is imposed at the closing seam. -/
def ReducedWalk {V : Type*} {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : Prop :=
  ∀ n, n + 2 ≤ p.length → p.getVert n ≠ p.getVert (n + 2)

/-- A locally injective graph homomorphism preserves internal reduction. -/
def LocallyInjective {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) : Prop :=
  ∀ a b c, G.Adj a b → G.Adj a c → f b = f c → b = c

/-- Data of either of the two small-angle links. At V use the first block coordinate;
at W use the second and swap u,v. The membership and uniqueness fields are exactly
the partition of I(z) into blocks, not geometric conclusions. -/
structure ShiftScheme (I P B : Type*) (r : ℕ) (inc : P → Finset I) where
  size : B → ℕ
  size_ge : ∀ b, r ≤ size b
  labels : B → Finset I
  coord : ∀ b, {i // i ∈ labels b} → ZMod (size b)
  point : B → P
  incident : ∀ b i, i ∈ labels b → i ∈ inc (point b)
  unique : ∀ b c i, point b = point c → i ∈ labels b → i ∈ labels c → b = c

namespace ShiftScheme
variable {I P B : Type*} {r : ℕ} {inc : P → Finset I} (d : ShiftScheme I P B r inc)

abbrev XDirection := I × Fin r × Fin r
abbrev LDirection := Σ b : B, Fin r × ZMod (d.size b)

def attached (x : XDirection (I := I) (r := r)) (l : d.LDirection) : Prop :=
  ∃ hi : x.1 ∈ d.labels l.1,
    x.2.1 = l.2.1 ∧ l.2.2 = d.coord l.1 ⟨x.1,hi⟩ + (x.2.2.val : ZMod (d.size l.1))

def link : SimpleGraph ((XDirection (I := I) (r := r)) ⊕ d.LDirection) :=
  relationGraph d.attached

def projection : d.link →g relationGraph (fun i z => i ∈ inc z) where
  toFun := Sum.map (fun x => x.1) (fun l => d.point l.1)
  map_rel' := by
    intro x y h
    cases x with
    | inl x => cases y with
      | inl y => exact h.elim
      | inr l => obtain ⟨hi,_,_⟩ := h; exact d.incident l.1 x.1 hi
    | inr l => cases y with
      | inr m => exact h.elim
      | inl x => obtain ⟨hi,_,_⟩ := h; exact d.incident l.1 x.1 hi

end ShiftScheme

end Release075

namespace Release075

/-- Pick one block and one leaf index for the two edges in the spanning tree. -/
structure BlockPresentation (I B : Type*) (r : ℕ) where
  block : B → CartesianBlock I r
  baseBlock : B
  baseIndex : Fin r

namespace BlockPresentation
variable {I B : Type*} {r : ℕ} (d : BlockPresentation I B r)

abbrev XEdge := I × Fin r × Fin r
abbrev LEdge := Σ b : B, Fin r × ZMod (d.block b).s
abbrev REdge := Σ b : B, Fin r × ZMod (d.block b).t
abbrev Edge := XEdge (I := I) (r := r) ⊕ (d.LEdge ⊕ d.REdge)

/-- The orientation of a face is `L x R⁻¹`, not a permuted product. -/
def triangleWord (b : B) (i : (d.block b).labels) (u v : Fin r) : FreeGroup d.Edge :=
  FreeGroup.of (.inr (.inl ⟨b,u,((d.block b).coordinates i).1 + (v.val : ZMod (d.block b).s)⟩)) *
  FreeGroup.of (.inl (i.val,u,v)) *
  (FreeGroup.of (.inr (.inr ⟨b,v,((d.block b).coordinates i).2 + (u.val : ZMod (d.block b).t)⟩)))⁻¹

def treeL : d.Edge := .inr (.inl ⟨d.baseBlock,d.baseIndex,0⟩)
def treeR : d.Edge := .inr (.inr ⟨d.baseBlock,d.baseIndex,0⟩)

def relators : Set (FreeGroup d.Edge) :=
  {w | (∃ b i u v, w = d.triangleWord b i u v) ∨
    w = FreeGroup.of d.treeL ∨ w = FreeGroup.of d.treeR}

abbrev GroupType := PresentedGroup d.relators

def edge (e : d.Edge) : d.GroupType := PresentedGroup.of e

def x (i : I) (u v : Fin r) : d.GroupType := d.edge (.inl (i,u,v))
def l (b : B) (u : Fin r) (j : ZMod (d.block b).s) : d.GroupType :=
  d.edge (.inr (.inl ⟨b,u,j⟩))
def rr (b : B) (v : Fin r) (k : ZMod (d.block b).t) : d.GroupType :=
  d.edge (.inr (.inr ⟨b,v,k⟩))

/-- The triangle faces impose precisely the factorization used by the rank proof. -/
theorem triangle_relation (b : B) (i : (d.block b).labels) (u v : Fin r) :
    d.x i u v = (d.l b u (((d.block b).coordinates i).1 + (v.val : ZMod (d.block b).s)))⁻¹ *
      d.rr b v (((d.block b).coordinates i).2 + (u.val : ZMod (d.block b).t)) := by
  have h := PresentedGroup.one_of_mem (rels := d.relators)
    (show d.triangleWord b i u v ∈ d.relators from Or.inl ⟨b,i,u,v,rfl⟩)
  apply (eq_inv_mul_iff_mul_eq).mpr
  exact mul_inv_eq_one.mp (by simpa only [triangleWord,map_mul,map_inv,
    edge,x,l,rr,PresentedGroup.of] using h)

theorem treeL_eq_one : d.edge d.treeL = 1 :=
  PresentedGroup.one_of_mem (Or.inr (Or.inl rfl))

theorem treeR_eq_one : d.edge d.treeR = 1 :=
  PresentedGroup.one_of_mem (Or.inr (Or.inr rfl))

theorem edge_closure : Subgroup.closure (Set.range d.edge) = ⊤ :=
  PresentedGroup.closure_range_of d.relators

end BlockPresentation

/-- Left translation is an automorphism of the right-generator Cayley graph. -/
def cayleyLeft {G : Type*} [Group G] (S : Set G) (a : G) :
    SimpleGraph.mulCayley S →g SimpleGraph.mulCayley S where
  toFun := (a * ·)
  map_rel' := by
    intro x y h
    exact (SimpleGraph.mulCayley_adj_mul_iff_right).mpr h

theorem cayley_reachable_mul_left {G : Type*} [Group G] (S : Set G) (a : G)
    {b c : G} (h : (SimpleGraph.mulCayley S).Reachable b c) :
    (SimpleGraph.mulCayley S).Reachable (a*b) (a*c) := h.map (cayleyLeft S a)

/-- The connected Cayley graph is derived from generation, not included as data. -/
theorem cayley_connected_of_closure {G : Type*} [Group G] (S : Set G)
    (hS : Subgroup.closure S = ⊤) : (SimpleGraph.mulCayley S).Connected := by
  classical
  have hreach (g : G) : (SimpleGraph.mulCayley S).Reachable 1 g := by
    have hg : g ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top _
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      by_cases h : 1 = g
      · subst g; exact SimpleGraph.Reachable.refl _
      · exact (SimpleGraph.mulCayley_adj' S 1 g |>.mpr
          ⟨h,g,hg,Or.inl (one_mul g)⟩).reachable
    | one => exact SimpleGraph.Reachable.refl _
    | mul a b _ _ ha hb =>
      exact ha.trans (by simpa using cayley_reachable_mul_left S a hb)
    | inv a _ ha =>
      have hh := cayley_reachable_mul_left S a⁻¹ ha
      simpa using hh.symm
  exact ⟨fun a b => (hreach a).symm.trans (hreach b)⟩

namespace BlockPresentation
variable {I B : Type*} {r : ℕ} (d : BlockPresentation I B r)

instance [Fintype I] [Fintype B] : Fintype d.Edge := by
  unfold Edge LEdge REdge
  infer_instance

theorem cayley_connected : (SimpleGraph.mulCayley (Set.range d.edge)).Connected :=
  cayley_connected_of_closure _ d.edge_closure

end BlockPresentation
end Release075

namespace Release075
noncomputable section
open scoped BigOperators
local instance instDecidableEq_oAI (α : Type*) : DecidableEq α := Classical.decEq α

/-- The two formalizations of puncturing remove exactly parameter zero / the
line's own mark. Other marked points are retained in both. -/
theorem mem_puncturedLine_iff_incidence {T K : Type*} [Fintype T] [Field K] [Fintype K]
    (a z : T → K) (d : Projectivization K (T → K)) :
    z ∈ puncturedLine a d.rep ↔ PuncturedIncidence a z d := by
  classical
  simp only [puncturedLine,Finset.mem_image,Finset.mem_erase,Finset.mem_univ,and_true]
  constructor
  · rintro ⟨t,ht,rfl⟩
    refine ⟨?_,t,?_⟩
    · intro h
      have hh : affineLineMap a d.rep t = affineLineMap a d.rep 0 := by
        rw [show affineLineMap a d.rep 0 = a by ext t; simp [affineLineMap]]
        exact h
      exact ht (affineLineMap_injective a d.rep d.rep_nonzero hh)
    · rfl
  · rintro ⟨hz,t,ht⟩
    refine ⟨t,?_,ht⟩
    intro he
    subst t
    simp only [zero_smul,add_zero] at ht
    exact hz ht.symm

/-- A chosen two-block partition. The fields contain only finite combinatorial
partition data, no geometric or group-theoretic conclusion. -/
structure TwoBlockPartition (I : Type*) (r : ℕ) (A : Finset I) where
  zero : CartesianBlock I r
  one : CartesianBlock I r
  disjoint : Disjoint zero.labels one.labels
  cover : zero.labels ∪ one.labels = A

namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

def incidences (z : Fin 20 → ZMod q) : Finset d.Label :=
  lineIncidence d.mark (fun i => (d.direction i).rep) z

theorem mem_incidences (z : Fin 20 → ZMod q) (i : d.Label) :
    i ∈ d.incidences z ↔ PuncturedIncidence (d.mark i) z (d.direction i) := by
  classical
  simp only [incidences,lineIncidence,Finset.mem_filter,Finset.mem_univ,true_and]
  exact mem_puncturedLine_iff_incidence _ _ _

theorem incidences_card_ge (z : Fin 20 → ZMod q) (hz : z ∉ d.exceptional) :
    4*r^2 ≤ (d.incidences z).card := by
  convert d.degree z hz using 1
  congr 1
  ext i
  simp only [d.mem_incidences,Finset.mem_filter,Finset.mem_univ,true_and]

abbrev Regular := {z : Fin 20 → ZMod q // z ∉ d.exceptional}
abbrev BlockIndex := d.Regular × Bool

instance : Fintype d.Regular := Fintype.ofFinite _

noncomputable def partition (hr : 0 < r) (z : d.Regular) :
    TwoBlockPartition d.Label r (d.incidences z) := by
  classical
  have hn : Nonempty (TwoBlockPartition d.Label r (d.incidences z)) := by
    obtain ⟨b₀,b₁,hd,hu⟩ := exists_two_cartesian_blocks r hr (d.incidences z)
      (d.incidences_card_ge z z.property)
    exact ⟨⟨b₀,b₁,hd,hu⟩⟩
  exact Classical.choice hn

noncomputable def block (hr : 0 < r) (b : d.BlockIndex) : CartesianBlock d.Label r :=
  if b.2 then (d.partition hr b.1).one else (d.partition hr b.1).zero

theorem block_incident (hr : 0 < r) (b : d.BlockIndex) (i : d.Label)
    (hi : i ∈ (d.block hr b).labels) : i ∈ d.incidences b.1 := by
  rw [← (d.partition hr b.1).cover]
  rcases b with ⟨z,e⟩
  cases e with
  | false => exact Finset.mem_union_left _ hi
  | true => exact Finset.mem_union_right _ hi

theorem block_unique (hr : 0 < r) (b c : d.BlockIndex) (i : d.Label)
    (hz : b.1.val = c.1.val) (hi : i ∈ (d.block hr b).labels)
    (hi' : i ∈ (d.block hr c).labels) : b = c := by
  rcases b with ⟨z,e⟩
  rcases c with ⟨w,f⟩
  have hw : z = w := Subtype.ext hz
  subst w
  cases e <;> cases f
  · rfl
  · exact ((Finset.disjoint_left.mp (d.partition hr z).disjoint) hi hi').elim
  · exact ((Finset.disjoint_left.mp (d.partition hr z).disjoint) hi' hi).elim
  · rfl

/-- The presentation is fixed from the finite data, before any quotient or
putative separation homomorphism is considered. -/
noncomputable def presentation (hr : 0 < r) : BlockPresentation d.Label d.BlockIndex r where
  block := d.block hr
  baseBlock := (⟨d.exists_regular.choose,d.exists_regular.choose_spec⟩,false)
  baseIndex := ⟨0,hr⟩

def RectangularNontriviality (hr : 0 < r) : Prop :=
  ∀ i, RectanglesSurvive ((d.presentation hr).x i)

/-- Small-angle link at V. -/
noncomputable def vShift (hr : 0 < r) :
    ShiftScheme d.Label (Fin 20 → ZMod q) d.BlockIndex r d.incidences where
  size b := (d.block hr b).s
  size_ge b := (d.block hr b).hs
  labels b := (d.block hr b).labels
  coord b i := ((d.block hr b).coordinates i).1
  point b := b.1
  incident := d.block_incident hr
  unique := d.block_unique hr

/-- Small-angle link at W, with u,v interchanged. -/
noncomputable def wShift (hr : 0 < r) :
    ShiftScheme d.Label (Fin 20 → ZMod q) d.BlockIndex r d.incidences where
  size b := (d.block hr b).t
  size_ge b := (d.block hr b).ht
  labels b := (d.block hr b).labels
  coord b i := ((d.block hr b).coordinates i).2
  point b := b.1
  incident := d.block_incident hr
  unique := d.block_unique hr

/-- Switch the two incidence-graph parts without altering any incidence. -/
def swapIncidence : relationGraph (fun i z => i ∈ d.incidences z) →g
    relationGraph (fun z i => PuncturedIncidence (d.mark i) z (d.direction i)) where
  toFun := Sum.swap
  map_rel' := by
    intro x y h
    cases x with
    | inl i => cases y with
      | inl j => exact h.elim
      | inr z => exact (d.mem_incidences z i).mp h
    | inr z => cases y with
      | inr w => exact h.elim
      | inl i => exact (d.mem_incidences z i).mp h

end MarkedLineData

end
end Release075

end OAI


