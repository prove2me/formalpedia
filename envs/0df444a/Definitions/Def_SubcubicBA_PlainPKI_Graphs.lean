-- Prove2me | Definitions.Def_SubcubicBA_PlainPKI_Graphs
-- name    : SubcubicBA_PlainPKI_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:42:14.985209+00:00
-- url     : https://prove2.me/theorems/078d932c-db7b-4077-b7ee-ddafc31c5e89
-- title:
--   Dispersers, bipartite Ramanujan graphs, fault-tolerant expanders and explicit graph families
-- statement:
--   Graph notions used by the protocol.
--
--   1. **Dispersers (Definition 7).** A directed graph on $\{0,\dots,n-1\}$ is given by out-neighbourhoods $N(u)$, with $N(S)=\bigcup_{u\in S}N(u)$. It is an $(a,b)$-disperser if every $S$ with $|S|\ge a$ has $|N(S)|\ge b$. A bipartite graph with left side of size $n$ and right side of size $m$ is a bipartite $(a,b)$-disperser if every left set $S$ with $|S|\ge a$ has $|N(S)|\ge b$. The thresholds are real numbers.
--   2. **Bipartite Ramanujan graphs.** A $D$-regular bipartite multigraph with $n$ vertices per side is given by its biadjacency multiplicity matrix $N$ (all row and column sums $D$). It is Ramanujan if its second largest singular value is at most $2\sqrt{D-1}$; equivalently, all eigenvalues of $N^{\mathsf T}N$, listed with multiplicity, except one are at most $4(D-1)$.
--   3. **Fault tolerance (Theorem 2).** A graph $G$ on $n$ vertices is $(\alpha,\beta,d)$-fault-tolerant if for every $C$ with $|C|\le\alpha n$ there is $S$ disjoint from $C$ with $|S|\ge n-\beta|C|$ such that $G[S]$ is connected and any two vertices of $S$ are at distance at most $d$ in $G[S]$.
--   4. **Explicit families.** A graph is explicit if it can be constructed deterministically in polynomial time (p. 37). A family is given by one function $f$ from the parameters (in unary) to the adjacency bit matrix, computed by a Turing machine in polynomial time (Mathlib's `Turing.TM2ComputableInPolyTime`). `nbhdOfBits` reads out-neighbourhoods from the matrix, and `graphOfBits` reads the simple graph of a symmetric, loopless matrix.
--
--   These notions state Theorems 2, 11, 12 and Lemmas 7 and 20.
--
--   **Formalization Note** The trivial singular value $D$ is exempted once only, so a disconnected regular graph, where $D^2$ is a repeated eigenvalue of $N^{\mathsf T}N$, is not Ramanujan unless $D^2\le4(D-1)$.
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), §5 Definition 7 (p. 10); App. A (pp. 37–40)

import Mathlib

set_option autoImplicit false

namespace SubcubicBA.PlainPKI

/-! # Graph notions of §5 (Definition 7) and Appendix A

Directed graphs on `Fin n` are given by out-neighbourhoods `N : Fin n → Finset (Fin n)`
(`N u = {v : u → v ∈ E}`, self-loops allowed); `N_G(S) = ⋃_{u ∈ S} N(u)` (p. 10).
"Explicit" means constructed deterministically in polynomial time (p. 37): the whole family is
one function computed by a Turing machine in time polynomial in the input length, with the
parameters given in unary and the graph output as its adjacency bit matrix. -/

/-- Definition 7 (directed): `N` is an `(a, b)`-disperser if every `S` with `|S| ≥ a` has
`|N(S)| ≥ b` (real thresholds). -/
def IsDisperser {n : ℕ} (N : Fin n → Finset (Fin n)) (a b : ℝ) : Prop :=
  ∀ S : Finset (Fin n), a ≤ (S.card : ℝ) → b ≤ ((S.biUnion N).card : ℝ)

/-- Definition 7 (bipartite, left side `Fin n`, right side `Fin m`). -/
def IsBipDisperser {n m : ℕ} (N : Fin n → Finset (Fin m)) (a b : ℝ) : Prop :=
  ∀ S : Finset (Fin n), a ≤ (S.card : ℝ) → b ≤ ((S.biUnion N).card : ℝ)

/-- Unary encoding of one parameter. -/
def unary1 (n : ℕ) : List Bool := List.replicate n true

/-- Unary encoding of two parameters, `1^n 0 1^m`. -/
def unary2 (p : ℕ × ℕ) : List Bool := List.replicate p.1 true ++ false :: List.replicate p.2 true

/-- A family `f` of bit strings is explicit: computed by a Turing machine in polynomial time. -/
def PolyTimeFamily {α : Type} (enc : α → List Bool) (f : α → List Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime enc (id : List Bool → List Bool) f)

/-- Entry `(u, v)` of an `rows × cols` row-major bit matrix (missing bits read `false`). -/
def bitAt (bits : List Bool) (cols u v : ℕ) : Bool := bits.getD (u * cols + v) false

/-- The out-neighbourhoods of the `n × m` bit matrix `bits`. -/
def nbhdOfBits (bits : List Bool) (n m : ℕ) (u : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun v : Fin m => bitAt bits m u.val v.val = true

/-- The simple graph on `Fin n` whose adjacency is the symmetric, loopless part of the bit
matrix: `u ~ v` iff `u ≠ v` and both entries `(u,v)`, `(v,u)` are set. -/
def graphOfBits (bits : List Bool) (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v : Fin n =>
    bitAt bits n u.val v.val = true ∧ bitAt bits n v.val u.val = true

/-- The bit matrix is a valid adjacency matrix of a simple graph on `Fin n`: length `n²`,
symmetric, zero diagonal. -/
def IsSimpleAdjBits (bits : List Bool) (n : ℕ) : Prop :=
  bits.length = n * n ∧ (∀ u v : ℕ, u < n → v < n → bitAt bits n u v = bitAt bits n v u) ∧
    ∀ u : ℕ, u < n → bitAt bits n u u = false

/-- The degree-`D` regular bipartite multigraph with biadjacency (multiplicity) matrix `N`
(`n` vertices per side, every row and column sum `D`) is Ramanujan: the second largest singular
value of `N` is at most `2√(D-1)`. Equivalently, the eigenvalues of `Nᵀ N` (the squared singular
values, listed with multiplicity) are all `≤ 4(D-1)` except for one of them (the trivial value
`D²`). The trivial value is exempted once only, so a disconnected graph (where `D²` repeats)
fails unless `D² ≤ 4(D-1)`. -/
def IsRamanujanBip (D n : ℕ) (N : Fin n → Fin n → ℕ) : Prop :=
  (∀ u, ∑ v, N u v = D) ∧ (∀ v, ∑ u, N u v = D) ∧
    ∃ h : (((Matrix.of fun u v => (N u v : ℝ)) : Matrix (Fin n) (Fin n) ℝ).transpose *
        (Matrix.of fun u v => (N u v : ℝ))).IsHermitian,
      ∃ i₀ : Fin n, ∀ i : Fin n, i ≠ i₀ → h.eigenvalues i ≤ 4 * ((D : ℝ) - 1)

/-- The fault-tolerant expander property of Theorem 2 (p. 5, p. 39) for one graph: for every
`C` with `|C| ≤ α n` there is `S` disjoint from `C` with `|S| ≥ n - β|C|` such that `G[S]` is
connected and every two vertices of `S` are at distance at most `d` in `G[S]`. -/
def FaultTolerant {n : ℕ} (G : SimpleGraph (Fin n)) (α β d : ℝ) : Prop :=
  ∀ C : Finset (Fin n), (C.card : ℝ) ≤ α * n →
    ∃ S : Finset (Fin n), Disjoint S C ∧ (n : ℝ) - β * C.card ≤ (S.card : ℝ) ∧
      (G.induce (S : Set (Fin n))).Connected ∧
      ∀ u v : (S : Set (Fin n)), ((G.induce (S : Set (Fin n))).dist u v : ℝ) ≤ d

end SubcubicBA.PlainPKI


