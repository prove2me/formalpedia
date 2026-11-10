-- Prove2me | Definitions.Def_AcycTesting_NearLinear_Forests
-- name    : AcycTesting_NearLinear_Forests
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:35:43.453003+00:00
-- url     : https://prove2.me/theorems/6401da94-cca6-4b2c-a40a-736681c46289
-- title:
--   Proper coloured forests, embedding counts Emb_G(F), the periodic cover G◦, activities a_I(G) and signed partition functions Φ_J(w)
-- statement:
--   A *coloured directed graph* $F$ on a finite vertex set $U$ is a finite set of edges $u\xrightarrow{a}w$ with colours $a\in[32]$. It is *proper* if no vertex has two outgoing edges of one colour or two incoming edges of one colour. It is a *coloured forest* if its underlying undirected multigraph is a weak forest (no loops, no opposite or repeated occurrences on a pair, no longer cycles). Its weak components, their sizes and weak diameters refer to the underlying undirected graph. $c$ is the number of components.
--
--   For a core $G$ with maps $P_a$ on $V$, $\mathrm{Emb}_G(F)$ is the number of injective maps $f:U\to V$ that preserve the direction and the colour of every edge, $f(w)=P_a(f(u))$ for each edge $u\xrightarrow{a}w$ (the maps need not be induced).
--
--   **Periodic cover (5.2).** For a core $\rho_1,\dots,\rho_{32}$ on $X$ and $W\ge1$, $G^\circ$ is the core on $\mathbb Z/W\mathbb Z\times X$ with $P_a(i,x)=(i+1,\rho_a(x))$. The layer translation is $(i,x)\mapsto(i+1,x)$. $\mathrm{Emb}_{G^\circ,\mathrm{avoid}}(F)$ counts the injective embeddings of $F$ into $G^\circ$ whose images avoid layer $W$, i.e. residue $0$.
--
--   **Activities (6.1)–(6.2).** Fix a root $r_C$ in each component $C$ of $F$. For $x\in V$, the image of $C$ with root image $x$ is the set of values on $C$ of the maps that send $r_C$ to $x$ and follow $P_a$ along every colour-$a$ edge of $C$; for a tree component in a permutation core, its restriction to that component exists and is unique. For root images $x=(x_C)_C$ chosen independently and uniformly from $V$, $O_{CD}$ indicates that the images of $C$ and $D$ intersect. For a set $I$ of at least two components the *activity* is
--   $$a_I(G)=\mathbb E\sum_{\Gamma\ \text{connected},\ V(\Gamma)=I}\ \prod_{CD\in E(\Gamma)}(-O_{CD}),$$
--   the sum ranging over the connected graphs $\Gamma$ with vertex set exactly $I$ (edges are pairs of distinct elements of $I$).
--
--   **Signed partition functions (§6.3).** For reals $w_I$ indexed by $I\subseteq[c]$ with $|I|\ge2$ and for $J\subseteq[c]$,
--   $$\Phi_J(w)=\sum_{\mathcal C}\prod_{I\in\mathcal C}w_I,$$
--   where $\mathcal C$ ranges over all collections of pairwise disjoint subsets of $J$ of size at least two; $\Phi_\emptyset(w)=1$.
--
--   **Formalization Note.** Components are indexed by Mathlib's `ConnectedComponent` type of the underlying simple graph (`fromRel`), not by $[c]$. Weak distance is `SimpleGraph.dist`. A component of size at most $S$ is compared as a real number with $S$. $[c]$ in $\Phi$ is `Fin c`; the weights `w I` with $|I|<2$ are never used.
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), pp. 18–19 (PDF 21–22), §5.1, (5.2), Lemma 5.4; pp. 24–26 (PDF 27–29), §6.1, (6.1)–(6.2), §6.3

import Mathlib
import Definitions.Def_AcycTesting_NearLinear_PermCores

namespace AcycTesting.NearLinear

/-! ### Coloured directed graphs, proper coloured forests and embeddings -/

/-- A directed edge-coloured graph on a vertex type `U`: a finite set of edges
`(tail, colour, head)` with colours in `[32]` (`Fin 32`). -/
abbrev ColGraph (U : Type*) := Finset (U × Fin 32 × U)

/-- The occurrences of a coloured graph and their (tail, head). -/
def colEnds {U : Type*} (F : ColGraph U) : F → U × U := fun e => (e.1.1, e.1.2.2)

/-- Proper: no vertex has two outgoing edges of one colour or two incoming edges of one
colour. -/
def IsProperCol {U : Type*} (F : ColGraph U) : Prop :=
  (∀ u a w w', (u, a, w) ∈ F → (u, a, w') ∈ F → w = w') ∧
    (∀ u u' a w, (u, a, w) ∈ F → (u', a, w) ∈ F → u = u')

/-- A coloured forest: a weak forest (its underlying undirected multigraph has no cycle). -/
def IsColForest {U : Type*} (F : ColGraph U) : Prop := IsWeakForest (colEnds F)

/-- The underlying undirected simple graph of a coloured graph (weak adjacency). -/
def weakGraph {U : Type*} (F : ColGraph U) : SimpleGraph U :=
  SimpleGraph.fromRel (fun u w => ∃ a, (u, a, w) ∈ F)

/-- The weak components of `F`. -/
abbrev Comp {U : Type*} (F : ColGraph U) := (weakGraph F).ConnectedComponent

/-- The number `c` of weak components of `F`. -/
noncomputable def numComponents {U : Type*} (F : ColGraph U) : ℕ := Nat.card (Comp F)

/-- Every weak component of `F` has at most `S` vertices and weak diameter at most `Λ`. -/
def ComponentsBounded {U : Type*} (F : ColGraph U) (S : ℝ) (Λ : ℕ) : Prop :=
  ∀ u : U, (Nat.card {w : U // (weakGraph F).Reachable u w} : ℝ) ≤ S ∧
    ∀ w : U, (weakGraph F).Reachable u w → (weakGraph F).dist u w ≤ Λ

/-- `f : U → V` preserves the direction and the colour of every edge of `F`:
`f(head) = P a (f(tail))` for every colour-`a` edge. -/
def PreservesEdges {U V : Type*} (P : CoreMaps V) (F : ColGraph U) (f : U → V) : Prop :=
  ∀ e ∈ F, f e.2.2 = P e.2.1 (f e.1)

/-- `Emb_G(F)`: the number of injective maps `V(F) → V` that preserve the direction and the
colour of every edge (not necessarily induced). -/
noncomputable def Emb {U V : Type*} (P : CoreMaps V) (F : ColGraph U) : ℕ :=
  Nat.card {f : U → V // Function.Injective f ∧ PreservesEdges P F f}

/-! ### The periodic cover (5.2) -/

/-- The maps of the periodic cover `G◦` on `ℤ/Wℤ × V(G_base)`: `P a (i, x) = (i + 1, ρ a x)`. -/
def coverMaps {X : Type*} (ρ : CoreMaps X) (W : ℕ) : CoreMaps (ZMod W × X) :=
  fun a y => (y.1 + 1, ρ a y.2)

/-- The layer translation `(i, x) ↦ (i + 1, x)`. -/
def layerShift {X : Type*} (W : ℕ) : ZMod W × X → ZMod W × X := fun y => (y.1 + 1, y.2)

/-- `Emb_{G◦,avoid}(F)`: injective embeddings of `F` into `G◦` whose images avoid layer `W`,
i.e. residue `0`. -/
noncomputable def EmbAvoid {U X : Type*} (ρ : CoreMaps X) (W : ℕ) (F : ColGraph U) : ℕ :=
  Nat.card {f : U → ZMod W × X //
    Function.Injective f ∧ PreservesEdges (coverMaps ρ W) F f ∧ ∀ u, (f u).1 ≠ 0}

/-! ### Independent roots, overlaps and activities (6.1)–(6.2) -/

/-- The image of the component `C` of `F` when its root `r C` is mapped to `x`: the values on
`C` of the maps that follow `P a` along every colour-`a` edge of `C` and send `r C` to `x`. -/
def compImage {U V : Type*} (P : CoreMaps V) (F : ColGraph U) (r : Comp F → U) (C : Comp F)
    (x : V) : Set V :=
  {y | ∃ f : U → V,
    (∀ e ∈ F, (weakGraph F).connectedComponentMk e.1 = C → f e.2.2 = P e.2.1 (f e.1)) ∧
      f (r C) = x ∧ ∃ u, (weakGraph F).connectedComponentMk u = C ∧ f u = y}

/-- The overlap indicator `O_{CD}` for root images `x`. -/
noncomputable def overlapInd {U V : Type*} (P : CoreMaps V) (F : ColGraph U) (r : Comp F → U)
    (x : Comp F → V) (C D : Comp F) : ℝ := by
  classical
  exact if (compImage P F r C (x C) ∩ compImage P F r D (x D)).Nonempty then 1 else 0

/-- The overlap indicator on unordered pairs. -/
noncomputable def overlapSym {U V : Type*} (P : CoreMaps V) (F : ColGraph U) (r : Comp F → U)
    (x : Comp F → V) : Sym2 (Comp F) → ℝ :=
  Sym2.lift ⟨overlapInd P F r x, fun C D => by
    unfold overlapInd
    rw [Set.inter_comm]⟩

/-- The edge sets `E` of connected graphs `Γ` with vertex set exactly `I`: edges are pairs of
distinct elements of `I`, and every two elements of `I` are joined by a path in `E`. -/
noncomputable def connectedEdgeSets {ι : Type*} [DecidableEq ι] (I : Finset ι) :
    Finset (Finset (Sym2 ι)) := by
  classical
  exact (I.sym2.powerset).filter (fun E => (∀ e ∈ E, ¬ e.IsDiag) ∧
    ∀ i ∈ I, ∀ j ∈ I, Relation.ReflTransGen (fun a b => s(a, b) ∈ E) i j)

/-- The activity (6.2): `a_I(G) = E ∑_{Γ connected, V(Γ) = I} ∏_{ij ∈ E(Γ)} (-O_ij)`, the
root images `x_C` being independent and uniform on `V`. -/
noncomputable def activity {U V : Type*} [Fintype U] [Fintype V] (P : CoreMaps V)
    (F : ColGraph U) (r : Comp F → U) (I : Finset (Comp F)) : ℝ := by
  classical
  haveI : Fintype (Comp F) := Fintype.ofFinite _
  exact expU (fun x : Comp F → V =>
    ∑ E ∈ connectedEdgeSets I, ∏ e ∈ E, (-(overlapSym P F r x e)))

/-! ### Signed partition functions (§6.3) -/

/-- `Φ_J(w) = ∑_C ∏_{I ∈ C} w_I` over collections `C` of pairwise disjoint subsets of `J` of
size at least two (`Φ_∅(w) = 1`). The weights `w I` with `|I| < 2` are never used. -/
noncomputable def signedPartition {c : ℕ} (w : Finset (Fin c) → ℝ) (J : Finset (Fin c)) : ℝ := by
  classical
  exact ∑ C ∈ (J.powerset.powerset).filter (fun C => (∀ I ∈ C, 2 ≤ I.card) ∧
      (C : Set (Finset (Fin c))).PairwiseDisjoint id), ∏ I ∈ C, w I

end AcycTesting.NearLinear


