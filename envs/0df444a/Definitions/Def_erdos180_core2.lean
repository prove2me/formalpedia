-- Prove2me | Definitions.Def_erdos180_core2
-- name    : erdos180_core2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-04T01:56:20.725729+00:00
-- url     : https://prove2.me/theorems/fd402095-eeef-4de5-a337-1f0e518c1a0d
-- title:
--   Common-neighbour geometry, non-backtracking four-paths, and the separation constants
-- statement:
--   Part two of the definition bundle. It sets up the counting apparatus of §3 of the source
--   and the constants that express the separation between the two bounds of Theorem 1.1.
--
--   **Common-neighbour geometry.** For a bipartite graph $B$ with no $C_4$ and no $C_6$ and a bipartition class $S$, the auxiliary *common-neighbour graph* $R_S$ joins $u \ne v$ in $S$ whenever $N_B(u) \cap N_B(v) \ne \emptyset$; one writes $u \sim v$ for adjacency in $R_S$. For an $R_S$-independent triple $T$, $L(T)$ is its set of common centres and $r(T) = |L(T)|$ (§3 of the source). `CommonNeighborRelated` is the relation
--   $\sim$, and the accompanying facts record Lemma 3.1(1): a related pair has a unique common
--   neighbour (two would close a $C_4$), and three pairwise related vertices share one common
--   neighbour (otherwise a $C_6$ appears).
--
--   **Non-backtracking walks.** `NonbacktrackingNeighbor`, `NonbacktrackingThreePath` and
--   `NonbacktrackingFourPath` formalise the walks $u,a,w,b,v$ counted in Lemma 3.2. In a graph of
--   girth at least eight such a walk always ends at a vertex $v \ne u$ with $v \not\sim u$, and the
--   walks correspond bijectively to pairs $(v,w)$ with $w \in Z_{uv} = \{w : w \sim u,\ w \sim v\}$,
--   which is what turns a degree bound into the estimate $\sum_v |Z_{uv}| \ge d(d-1)^3$.
--   `subdivisionCopyOfCommonNeighbors`, `subdivisionCopyOfRelatedCenters` and
--   `subdivisionCopyOfGirthEightCenters` build the copies of $S_k$ that Lemma 3.1(2) extracts from
--   an independent triple with $r(T) \ge k$.
--
--   **Separation constants.** `FamilyLittleO` says $\mathrm{ex}(n,\mathcal{F}) = o(n^{4/3})$,
--   `UniformMemberLower` says every member satisfies $\mathrm{ex}(n,F) \ge c\,n^{4/3}$ eventually,
--   and `SeparationCertificate` bundles the two with the positivity of the constant —
--   together they contradict compactness. `manuscriptLowerConstant` is the explicit $c$ coming from
--   the quadrangle construction, `extremalScale` the normalising factor $n^{4/3}$, and
--   `fourPathHeavyThreshold` the threshold separating heavy from light four-path fibres in the
--   supersaturation argument. `kernelNormalForm` provides canonical representatives for the
--   quotient maps, and `symmetricQuadratic`, `symmetricDet` the quadratic form used for the
--   characteristic-two analysis of line pairs.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L2417-L4516

import Definitions.Def_erdos180_core1
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Erdos180

noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

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

end

noncomputable section
open SimpleGraph

def GraphHasNoIsolated {V : Type*} (graph : SimpleGraph V) : Prop :=
  ∀ u : V, ∃ v : V, graph.Adj u v

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

end

noncomputable section
open SimpleGraph
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

abbrev NonbacktrackingThreePath (G : SimpleGraph V) (u : V) :=
  Σ a : G.neighborSet u,
    Σ w : NonbacktrackingNeighbor G u (a : V),
      NonbacktrackingNeighbor G (a : V) (w : V)

def nonbacktrackingThreePathEndpoint
    (G : SimpleGraph V) {u : V}
    (path : NonbacktrackingThreePath G u) : V :=
  path.2.2.1

end

noncomputable section
open SimpleGraph
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

end

noncomputable section
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

end

section
variable {K : Type*} [CommRing K]

def symmetricQuadratic (a b c x y : K) : K :=
  a * x ^ 2 + (2 : K) * b * x * y + c * y ^ 2

def symmetricDet (a b c : K) : K := a * c - b ^ 2

end

section
variable {K : Type*} [Field K]

def symmetricQuadraticEvaluationMatrix
    (x₀ y₀ x₁ y₁ x₂ y₂ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![x₀ ^ 2, (2 : K) * x₀ * y₀, y₀ ^ 2;
     x₁ ^ 2, (2 : K) * x₁ * y₁, y₁ ^ 2;
     x₂ ^ 2, (2 : K) * x₂ * y₂, y₂ ^ 2]

end

noncomputable section
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

end

noncomputable section
open Finset SimpleGraph

def fourPathHeavyThreshold (N p : ℕ) : ℝ :=
  (p : ℝ) / (2 * (N : ℝ))

def finiteHeavyFiberMass {α : Type*} [Fintype α]
    (weight : α → ℕ) (N p : ℕ) : ℝ :=
  ∑ x : α,
    if fourPathHeavyThreshold N p ≤ (weight x : ℝ)
    then (weight x : ℝ) else 0

end

noncomputable section
open Finset SimpleGraph
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

end

end Erdos180


