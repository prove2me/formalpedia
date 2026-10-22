-- Prove2me | Definitions.Def_SidB_hyper
-- name    : SidB_hyper
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T18:07:54.468559+00:00
-- url     : https://prove2.me/theorems/952f26bf-c343-41a2-a7c9-fcef712c537d
-- title:
--   The hypergraph layer: downset graphs, weighted densities, and the chain hypergraphs
-- statement:
--   The hypergraph layer of the SidB mission, carrying the weighted-homomorphism machinery of Section 3 of the paper. downsetGraph m r is the (m,r)-downset graph, the membership bigraph between Fin m and the nonempty subsets of Fin m of cardinality at most r; incGraph m r is the (m,r)-incidence graph on the r-subsets. Graphon.downsetDens g m r alpha is the alpha-weighted homomorphism density t_H^alpha(W) = E_x prod_S rho(x_S) ^ alpha_{|S|}; Graphon.incDens g m r w is the single-weight density on the r-subsets; weightedEdgeCount m r alpha is the weighted edge count e_alpha(H) = sum_k C(m,k) k alpha_k. RGraph r is an r-uniform hypergraph: a vertex type with an edge predicate on (r+1)-tuples. HV m is the chain-vertex type - the point marker, the anchor point, the common r-subset F, the chain subset, and the copy index - with the accessors isPoint, pt, big, sub, and cp; finSub and finEq are the Boolean membership-test encodings of containment and equality of finsets. hAlphaEdge m r beta e is the edge predicate of the chain hypergraph H_alpha: e 0 is the anchor point, the chain vertices e (k+1) carry subsets of cardinality k+1 with copy indices below beta (k+1), all contained in the common r-subset carried by the last vertex, the anchor point lies in the first chain subset, and the chain subsets are nested; hAlpha m r beta is H_alpha and gAlpha r beta the [r]-chain core G_alpha, both abbrevs so that the Fintype instance of the vertex type resolves. qOf r beta is the paper's weight vector q_k = beta_{k+1} / (beta * k! * (r-k-1)!) with beta the product of the beta_k; qAH m r beta is the exponent q_{alpha,H} = e_alpha(H) / C(m,r); rDens g R q is the homomorphism density t_R(W_alpha) = E_x prod_{edges e} prod_{k < r} W(x_{e_0}, x_{e_{k+1}}) ^ q_k.
--
--   **Formalization Note** The finset containment and equality tests inside the chain edge predicate are encoded as Boolean list-membership tests (finSub, finEq); the chain hypergraphs are abbrevs so that instance resolution for the vertex type is transparent; and the copy structures U_k(F) of the paper are recorded through their cardinality data (the copy index below beta (k+1)) rather than as explicit disjoint unions.
-- source:
--   D. Conlon, J. Lee, Sidorenko's conjecture for blow-ups, Discrete Anal. 2021:2 (2021), Section 3 (the chain hypergraphs H_alpha and G_alpha, the weight vector q, and the weighted densities) and Section 4 (the exponent q_alpha,H of Lemma 3.4).

import Mathlib
import Definitions.Def_SidB_graph

/-!
# The hypergraph layer: downset graphs, weighted densities, and the chain hypergraphs

The hypergraph layer of the SidB mission, carrying the weighted-homomorphism
machinery of Section 3 of Conlon and Lee, "Sidorenko's Conjecture for
Blow-ups" (Discrete Anal. 2021:2): the (m,r)-downset and (m,r)-incidence
graphs; the alpha-weighted homomorphism density of a downset graph and the
weighted edge count e_alpha(H); the r-uniform hypergraph interface; the
chain hypergraphs H_alpha and G_alpha of the paper's proof of Theorem 3.1,
with their chain-vertex type, their edge predicates, and their densities
under the weight vector q; and the exponent q_alpha,H.
-/

namespace SidB

/-- The (m,r)-downset graph: the membership bigraph between Fin m and the
nonempty subsets of Fin m of cardinality at most r. -/
def downsetGraph (m r : ℕ) : Bigraph (Fin m) {s : Finset (Fin m) // 0 < s.card ∧ s.card ≤ r} where
  adj a s := decide (a ∈ s.1)

/-- The (m,r)-incidence graph: the membership bigraph between Fin m and
the r-subsets of Fin m. -/
def incGraph (m r : ℕ) : Bigraph (Fin m) {s : Finset (Fin m) // s.card = r} where
  adj a s := decide (a ∈ s.1)

/-- The alpha-weighted homomorphism density of the (m,r)-downset graph:
t_H^alpha(W) = E_{x} prod_{S} rho(x_S) ^ alpha_{|S|}, over the nonempty
subsets S of cardinality at most r. -/
noncomputable def Graphon.downsetDens (g : Graphon) (m r : ℕ) (α : ℕ → ℝ) : ℝ :=
  g.EX (Fin m) (fun x =>
    ∏ s : {s : Finset (Fin m) // 0 < s.card ∧ s.card ≤ r}, g.rho s.1 x ^ α s.1.card)

/-- The homomorphism density of the (m,r)-incidence graph with the single
weight w on each r-subset. -/
noncomputable def Graphon.incDens (g : Graphon) (m r : ℕ) (w : ℝ) : ℝ :=
  g.EX (Fin m) (fun x => ∏ s : {s : Finset (Fin m) // s.card = r}, g.rho s.1 x ^ w)

/-- The weighted edge count e_alpha(H) of the (m,r)-downset graph under the
symmetric weight vector alpha: the sum over k of C(m,k) * k * alpha_k. -/
def weightedEdgeCount (m r : ℕ) (α : ℕ → ℕ) : ℝ :=
  ∑ k ∈ Finset.range r, (m.choose (k + 1) : ℝ) * ((k : ℝ) + 1) * (α (k + 1) : ℝ)

/-- An r-uniform directed hypergraph: a vertex type together with an edge
predicate on (r+1)-tuples of vertices. -/
structure RGraph (r : ℕ) where
  vert : Type
  edge : (Fin (r + 1) → vert) → Bool

/-- The largest of the copy numbers beta_1, ..., beta_r. -/
def betaMax (r : ℕ) (β : ℕ → ℕ) : ℕ :=
  (List.finRange r).foldl (fun acc k => max acc (β (k.val + 1))) 0

/-- The vertex type of the chain hypergraph: a point marker (distinguishing
the V_0 coordinates from the chain coordinates), the anchor point of
Fin m, the common r-subset F, the chain subset, and the copy index. The
copy index lives in the finite range Fin (betaMax r beta + 1): an edge
only involves copy indices below their copy numbers, which are at most
betaMax r beta, and the + 1 keeps point vertices alive even when every
copy number is zero. -/
abbrev HV (m r : ℕ) (β : ℕ → ℕ) : Type :=
  Bool × Fin m × Finset (Fin m) × Finset (Fin m) × Fin (betaMax r β + 1)

/-- The point marker of a chain vertex. -/
def HV.isPoint {m r : ℕ} {β : ℕ → ℕ} (v : HV m r β) : Bool := v.1

/-- The anchor point of a chain vertex. -/
def HV.pt {m r : ℕ} {β : ℕ → ℕ} (v : HV m r β) : Fin m := v.2.1

/-- The common r-subset F of a chain vertex. -/
def HV.big {m r : ℕ} {β : ℕ → ℕ} (v : HV m r β) : Finset (Fin m) := v.2.2.1

/-- The chain subset of a chain vertex. -/
def HV.sub {m r : ℕ} {β : ℕ → ℕ} (v : HV m r β) : Finset (Fin m) := v.2.2.2.1

/-- The copy index of a chain vertex. -/
def HV.cp {m r : ℕ} {β : ℕ → ℕ} (v : HV m r β) : Fin (betaMax r β + 1) := v.2.2.2.2

/-- The Boolean containment test: every element of the first finset lies in
the second, by list membership tests. -/
noncomputable def finSub {A : Type} [DecidableEq A] (s t : Finset A) : Bool :=
  s.toList.all (fun a => decide (a ∈ t))

/-- The Boolean equality test for finsets, by mutual containment. -/
noncomputable def finEq {A : Type} [DecidableEq A] (s t : Finset A) : Bool :=
  finSub s t && finSub t s

/-- The edge predicate of the chain hypergraph H_alpha: an (r+1)-tuple e is
an edge when e 0 is the anchor point; for each k below r the vertex e (k+1)
is a chain vertex that is not a point, whose chain subset has cardinality
k+1, whose copy index is below beta (k+1), whose chain subset is contained
in its common subset, whose common subset has cardinality r and equals the
common subset carried by the last vertex, and, for the first chain vertex,
whose chain subset contains the anchor point; and the chain subsets are
nested, an earlier one contained in a later one. -/
noncomputable def hAlphaEdge (m r : ℕ) (β : ℕ → ℕ) (e : Fin (r + 1) → HV m r β) : Bool :=
  (e ⟨0, Nat.zero_lt_succ r⟩).isPoint &&
  ((List.finRange r).all (fun k =>
    let v := e ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
    (!v.isPoint) &&
    (v.sub.card = k.val + 1) &&
    decide ((v.cp : ℕ) < β (k.val + 1)) &&
    finSub v.sub v.big &&
    (v.big.card = r) &&
    finEq v.big (e ⟨r, Nat.lt_succ_self r⟩).big &&
    ((k.val ≠ 0) || decide ((e ⟨0, Nat.zero_lt_succ r⟩).pt ∈ v.sub)) &&
    ((List.finRange r).all (fun j =>
      (k.val < j.val) ||
      finSub (e ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).sub v.sub))))

/-- The r-uniform chain hypergraph H_alpha on the chain vertices HV m r
beta. An abbrev, so that the Fintype instance of its vertex type
resolves. -/
noncomputable abbrev hAlpha (m r : ℕ) (β : ℕ → ℕ) : RGraph r :=
  ⟨HV m r β, hAlphaEdge m r β⟩

/-- The [r]-chain core hypergraph G_alpha: the chain hypergraph with
m = r, whose edges are the [r]-chains. -/
noncomputable abbrev gAlpha (r : ℕ) (β : ℕ → ℕ) : RGraph r :=
  hAlpha r r β

/-- The chain vertices form a finite type: the vertex type HV m r beta is
a product of finite types, so the homomorphism density of the chain
hypergraph is defined. The instance is declared on the projected vertex
type because the structure projection does not reduce at instance-search
transparency. -/
instance hAlphaFintype (m r : ℕ) (β : ℕ → ℕ) : Fintype (hAlpha m r β).vert :=
  inferInstanceAs (Fintype (HV m r β))

/-- The chain core hypergraph inherits the same finiteness. -/
instance gAlphaFintype (r : ℕ) (β : ℕ → ℕ) : Fintype (gAlpha r β).vert :=
  inferInstanceAs (Fintype (HV r r β))

/-- The weight vector q of the paper: with beta the product of the beta_k,
the weight at the chain coordinate k+1 is beta_{k+1} divided by
beta * k! * (r-k-1)!. -/
noncomputable def qOf (r : ℕ) (β : ℕ → ℕ) : Fin r → ℝ :=
  fun k =>
    (β (k.val + 1) : ℝ) / (∏ i ∈ Finset.range r, (β (i + 1) : ℝ)) *
      (Nat.factorial k.val : ℝ) * (Nat.factorial (r - k.val - 1) : ℝ)

/-- The exponent q_alpha,H = e_alpha(H) / C(m,r) of Lemma 3.4. -/
noncomputable def qAH (m r : ℕ) (β : ℕ → ℕ) : ℝ :=
  (∑ k ∈ Finset.range r,
    (m.choose (k + 1) : ℝ) * ((k : ℝ) + 1) *
      ((β (k + 1) : ℝ) * ((m - (k + 1)).choose (r - (k + 1)) : ℝ)))
    / (m.choose r : ℝ)

/-- The homomorphism density of the r-uniform hypergraph R under the weight
vector q on the chain coordinates of each edge:
t_R(W_alpha) = E_x prod_{edges e} prod_{k < r} W(x_{e_0}, x_{e_{k+1}}) ^ q_k. -/
noncomputable def rDens (g : Graphon) {r : ℕ} (R : RGraph r) [Fintype R.vert] (q : Fin r → ℝ) : ℝ :=
  g.EX R.vert (fun x =>
    ∏ e : (Fin (r + 1) → R.vert),
      cond (R.edge e)
        (∏ k : Fin r, (g.W (x (e ⟨0, Nat.zero_lt_succ r⟩))
          (x (e ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩))) ^ q k) 1)

end SidB


