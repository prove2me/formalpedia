-- Prove2me | Definitions.Def_HypergraphUnreliability_FPRAS_Instance
-- name    : HypergraphUnreliability_FPRAS_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:36.937162+00:00
-- url     : https://prove2.me/theorems/4f2612a5-2b5b-4016-ba94-186873508fac
-- title:
--   Explicit inputs of Theorems 1.1 and 1.2 and Lemma 2.1, with their encodings and resource sizes
-- statement:
--   An **explicit input** of Theorem 1.1 lists the vertices $0,\dots,n-1$, then the labeled edges, each with its incidence list and written failure probability $p_e\in[0,1]$, then written $\varepsilon,\delta\in(0,1)$. Parallel edges are separate list entries, so multiplicities are explicit. Repeated incidences and empty or singleton edges may occur in the input.
--
--   The **target** is $u_H(p)$ of the hypergraph with these labels. The **resource size** is
--   $$s=|\mathrm{enc}(x)|+\lceil\varepsilon^{-1}\rceil+1+\lceil\log_2(1/\delta)\rceil .$$
--   The encoding length contains $n$, every incidence and label, and both binary numbers of every rational parameter. It contains no derived quantity.
--
--   The same layer defines the explicit hypergraph input of Lemma 2.1, the common-probability input of Theorem 1.2, and the inputs of Lemmas 7.1, 9.2 and 9.3.
--
--   **Formalization Note** Empty and singleton labels cross no set and contribute a factor summing to one, so they do not change $u_H(p)$, and the discarding of §1.1 is a step of the algorithm rather than a restriction on inputs.
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), §1.1, p. 2; Theorem 1.1, p. 2; Theorem 1.2, p. 2

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Hypergraph
import Definitions.Def_HypergraphUnreliability_FPRAS_Machine

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

/-- One labeled input edge: its explicit (possibly repeating) incidence list and its written failure
probability. -/
structure RawEdge (n : ℕ) where
  verts : List (Fin n)
  fail : Frac

/-- An explicit input of Theorem 1.1 (§1.1, p. 2): `n` listed vertices, an explicit list of labeled
edges with rational failure probabilities, and the rational parameters `ε, δ`. Parallel edges are
separate list entries. Repeated incidences and empty or singleton edges are allowed in the input. -/
structure RawInstance where
  n : ℕ
  edges : List (RawEdge n)
  ε : Frac
  δ : Frac

namespace RawInstance

/-- Well-formedness: all denominators positive, `p_e ∈ [0,1]`, and `ε, δ ∈ (0,1)`. -/
structure Valid (x : RawInstance) : Prop where
  fail_den : ∀ e ∈ x.edges, 0 < e.fail.den
  fail_le : ∀ e ∈ x.edges, e.fail.num ≤ e.fail.den
  ε_den : 0 < x.ε.den
  ε_pos : 0 < x.ε.num
  ε_lt : x.ε.num < x.ε.den
  δ_den : 0 < x.δ.den
  δ_pos : 0 < x.δ.num
  δ_lt : x.δ.num < x.δ.den

/-- The input hypergraph with labels `Fin (x.edges.length)`; repeated incidences collapse. -/
def hypergraph (x : RawInstance) : LabeledHypergraph x.n (Fin x.edges.length) where
  inc e := (x.edges.get e).verts.toFinset

/-- The failure probabilities, as real numbers. -/
def failProb (x : RawInstance) (e : Fin x.edges.length) : ℝ :=
  (((x.edges.get e).fail.val : ℚ) : ℝ)

/-- The target `u_H(p)`. Empty and singleton labels cross no set, and each contributes a factor
summing to one, so discarding them (§1.1) does not change this number. -/
def target (x : RawInstance) : ℝ :=
  x.hypergraph.unreliability x.failProb

/-- The explicit binary encoding: the vertex list `0, …, n-1` written out (so that its length is at
least `n`), then the edge list with every incidence and both numbers of every probability, then
`ε` and `δ`. Multiplicities are represented by the explicit edge list. No probability, cut or other
derived quantity is encoded. -/
def encode (x : RawInstance) : List Bool :=
  listCode natCode (List.range x.n) ++
    listCode (fun e : RawEdge x.n =>
      listCode (fun v : Fin x.n => natCode v.val) e.verts ++ fracCode e.fail) x.edges ++
    fracCode x.ε ++ fracCode x.δ

/-- The resource parameter of Theorem 1.1: the total encoded length (which contains all probability
encodings), `⌈ε⁻¹⌉`, and `1 + ⌈log₂(1/δ)⌉`. -/
def resourceSize (x : RawInstance) : ℕ :=
  x.encode.length + ⌈((x.ε.val : ℚ) : ℝ)⁻¹⌉₊ + (1 + ⌈Real.logb 2 (((x.δ.val : ℚ) : ℝ)⁻¹)⌉₊)

end RawInstance

/-- An explicit hypergraph without probabilities, the input of Lemma 2.1. -/
structure RawHypergraph where
  n : ℕ
  edges : List (List (Fin n))

namespace RawHypergraph

/-- The hypergraph with labels `Fin (x.edges.length)`. Empty and singleton labels cross nothing and
contribute `0` to every cut. -/
def hypergraph (x : RawHypergraph) : LabeledHypergraph x.n (Fin x.edges.length) where
  inc e := (x.edges.get e).toFinset

/-- The explicit encoding: the vertex list, then the edge list with every incidence. -/
def encode (x : RawHypergraph) : List Bool :=
  listCode natCode (List.range x.n) ++
    listCode (listCode (fun v : Fin x.n => natCode v.val)) x.edges

end RawHypergraph

/-- An explicit input of the common-probability algorithm (Theorem 1.2, p. 2). -/
structure CommonInstance where
  graph : RawHypergraph
  p : Frac
  ε : Frac
  δ : Frac

namespace CommonInstance

/-- Well-formedness: all denominators positive, `p ∈ [0,1]`, `ε, δ ∈ (0,1)`. -/
structure Valid (x : CommonInstance) : Prop where
  p_den : 0 < x.p.den
  p_le : x.p.num ≤ x.p.den
  ε_den : 0 < x.ε.den
  ε_pos : 0 < x.ε.num
  ε_lt : x.ε.num < x.ε.den
  δ_den : 0 < x.δ.den
  δ_pos : 0 < x.δ.num
  δ_lt : x.δ.num < x.δ.den

/-- The explicit encoding. -/
def encode (x : CommonInstance) : List Bool :=
  x.graph.encode ++ fracCode x.p ++ fracCode x.ε ++ fracCode x.δ

/-- The resource parameter of Theorem 1.2: the explicit input length, `⌈ε⁻¹⌉` and
`1 + ⌈log₂(1/δ)⌉`. -/
def resourceSize (x : CommonInstance) : ℕ :=
  x.encode.length + ⌈((x.ε.val : ℚ) : ℝ)⁻¹⌉₊ + (1 + ⌈Real.logb 2 (((x.δ.val : ℚ) : ℝ)⁻¹)⌉₊)

end CommonInstance

/-- The input of Lemma 7.1: `p = A/B` written with integers `A, B`, and the tolerance `η`. -/
structure LogInput where
  A : ℕ
  B : ℕ
  η : Frac

/-- The encoding of a `LogInput`. -/
def LogInput.encode (x : LogInput) : List Bool :=
  natCode x.A ++ natCode x.B ++ fracCode x.η

/-- The input of Lemma 9.2: an explicit hypergraph with a written rate on each label. -/
structure RatedHypergraph where
  n : ℕ
  edges : List (List (Fin n) × Frac)

namespace RatedHypergraph

/-- The hypergraph with labels `Fin (x.edges.length)`. -/
def hypergraph (x : RatedHypergraph) : LabeledHypergraph x.n (Fin x.edges.length) where
  inc e := (x.edges.get e).1.toFinset

/-- The rates. -/
def rate (x : RatedHypergraph) (e : Fin x.edges.length) : ℚ := (x.edges.get e).2.val

/-- The explicit encoding: the vertex list, then every incidence and every written rate. -/
def encode (x : RatedHypergraph) : List Bool :=
  listCode natCode (List.range x.n) ++
    listCode (fun e : List (Fin x.n) × Frac =>
      listCode (fun v : Fin x.n => natCode v.val) e.1 ++ fracCode e.2) x.edges

/-- The domain of Lemma 9.2 (§§9.1–9.2, p. 13): the connected quotient, `n ≥ 2`, with positive dyadic
rates over one common denominator `2^a`. -/
def InDomain (x : RatedHypergraph) : Prop :=
  x.hypergraph.Standing ∧ (∀ e ∈ x.edges, 0 < e.2.num) ∧ ∃ a : ℕ, ∀ e ∈ x.edges, e.2.den = 2 ^ a

end RatedHypergraph

/-- The input of Lemma 9.3: `Λ`, the numerical bound `R`, and `ε`. -/
structure ExpInput where
  Λ : Frac
  R : Frac
  ε : Frac

/-- The encoding of an `ExpInput`. -/
def ExpInput.encode (x : ExpInput) : List Bool :=
  fracCode x.Λ ++ fracCode x.R ++ fracCode x.ε

/-- The domain of Lemma 9.3: rational `Λ ∈ [0, R]`, `ε ∈ (0, 1)`. -/
def ExpInput.InDomain (x : ExpInput) : Prop :=
  0 < x.Λ.den ∧ 0 < x.R.den ∧ 0 < x.ε.den ∧ x.Λ.val ≤ x.R.val ∧ 0 < x.ε.num ∧ x.ε.num < x.ε.den

end HypergraphUnreliability.FPRAS


