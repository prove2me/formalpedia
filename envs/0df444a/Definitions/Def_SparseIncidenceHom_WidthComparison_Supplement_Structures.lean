-- Prove2me | Definitions.Def_SparseIncidenceHom_WidthComparison_Supplement_Structures
-- name    : SparseIncidenceHom_WidthComparison_Supplement_Structures
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:13:01.261534+00:00
-- url     : https://prove2.me/theorems/79402b5e-ddf1-4361-9fe1-11e5fbdbc84b
-- title:
--   Finite relational structures as explicit tuple lists, homomorphisms, the hypergraph $H_A$, encodings and cores
-- statement:
--   A **finite relational structure** $A$ is given by explicit data: a finite signature $\tau$, listed as the arities $r_1,\dots,r_s\in\mathbb N$ of its relation symbols (arity $0$ is allowed); a finite domain $V(A)=\{0,\dots,n-1\}$; and, for each relation symbol $R_i$, an explicit list of tuples forming $R_i^A\subseteq V(A)^{r_i}$. The structure is **well formed** when there is one table per symbol and every tuple has the right arity and entries in the domain.
--
--   A map $h$ is a **homomorphism** $h:A\to B$ when $A$ and $B$ have the same signature, $h$ maps $V(A)$ into $V(B)$, and
--   $$(a_1,\dots,a_{r_i})\in R_i^A\ \Longrightarrow\ (h(a_1),\dots,h(a_{r_i}))\in R_i^B$$
--   for every $i$; $A\to B$ means that a homomorphism exists. $A$ and $B$ are **isomorphic** when there are mutually inverse homomorphisms between them.
--
--   The hypergraph $H_A$ has one vertex for each domain element occurring in some tuple, and for each tuple with at least one entry the hyperedge formed by its entries; tuples inducing the same set give one hyperedge. It is a finite hypergraph with no empty edges in which every vertex lies in an edge; it may be empty or disconnected.
--
--   A structure is encoded as a binary string by listing its signature, its domain size and its tuple lists in a self-delimiting code (unary numbers, each list entry preceded by $1$ and the list closed by $0$); $\|A\|$ is the length of this string.
--
--   An **endomorphism** of $A$ is a homomorphism $A\to A$. A **core map** is an endomorphism $h$ whose image $h(V(A))$ has minimum cardinality among all endomorphisms; the endomorphic image $h(A)$ has the relations $h(R_i^A)$, and $\operatorname{core}(A)$ is (up to isomorphism) $h(A)$ for a core map $h$.
--
--   These objects state the homomorphism problems $\mathrm{Hom}(\mathcal H)$ and $\mathrm{Hom}(\mathcal A)$ and the core-width conditions of Section 4.
--
--   **Formalization Note** A structure is the triple (arity list, domain size, list of tuple lists) of natural numbers, so that classes of structures are sets of a `Primcodable` type and recursive enumerability has its standard meaning. Maps are functions $\mathbb N\to\mathbb N$, of which only the values on the domain matter. The image structure keeps the declared domain size of $A$; only its hypergraph $H_{h(A)}$ is used, which depends only on the relations, and the minimality of the image is measured separately by `imageCard`.
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), p. 3 (Hom(H) and footnote 1), p. 7 (Section 2.1: relational structures, homomorphisms, H_A, encoding length), p. 16 (Section 4.2: endomorphisms, cores)

import Mathlib
import Definitions.Def_SparseIncidenceHom_WidthComparison_Hypergraphs

namespace SparseIncidenceHom.WidthComparison.Supplement

open SparseIncidenceHom.WidthComparison

/-- Section 2.1, p. 7. A finite relational structure as explicit data: the list of arities of the
relation symbols (the signature τ), the domain size `n` (domain `{0, …, n-1}`), and for every
relation symbol its explicit list of tuples. Arities are arbitrary natural numbers. -/
abbrev RelStr : Type := List ℕ × ℕ × List (List (List ℕ))

namespace RelStr

/-- The signature: the arity of relation symbol `i` is the `i`-th entry. -/
def arities (A : RelStr) : List ℕ := A.1

/-- The domain is `{0, …, size - 1}`. -/
def size (A : RelStr) : ℕ := A.2.1

/-- The relation tables, one list of tuples per relation symbol. -/
def rels (A : RelStr) : List (List (List ℕ)) := A.2.2

/-- The table of relation symbol `i` (empty for an index outside the signature). -/
def table (A : RelStr) (i : ℕ) : List (List ℕ) := A.rels.getD i []

/-- One table per relation symbol, every tuple of the right arity with entries in the domain. -/
def WellFormed (A : RelStr) : Prop :=
  A.rels.length = A.arities.length ∧
  ∀ i < A.arities.length, ∀ t ∈ A.table i, t.length = A.arities.getD i 0 ∧ ∀ a ∈ t, a < A.size

/-- `h` (on the domain of `A`) is a homomorphism `A → B`: same signature, domain into domain,
and every tuple of every relation of `A` is mapped to a tuple of the same relation of `B`. -/
def IsHomMap (A B : RelStr) (h : ℕ → ℕ) : Prop :=
  A.arities = B.arities ∧ (∀ a < A.size, h a < B.size) ∧
  ∀ i < A.arities.length, ∀ t ∈ A.table i, t.map h ∈ B.table i

/-- `A → B`: some homomorphism exists. -/
def HomTo (A B : RelStr) : Prop := ∃ h : ℕ → ℕ, IsHomMap A B h

/-- Isomorphism: mutually inverse homomorphisms on the domains. -/
def Isomorphic (A B : RelStr) : Prop :=
  ∃ σ τ : ℕ → ℕ, IsHomMap A B σ ∧ IsHomMap B A τ ∧
    (∀ a < A.size, τ (σ a) = a) ∧ (∀ b < B.size, σ (τ b) = b)

/-- The domain elements occurring in some tuple: the vertices of `H_A`. -/
abbrev Vtx (A : RelStr) : Type := {a : ℕ // a ∈ A.rels.flatten.flatten}

noncomputable instance vtxFintype (A : RelStr) : Fintype (Vtx A) :=
  Fintype.ofFinite _

/-- The hypergraph `H_A` (p. 7): one vertex per domain element occurring in a tuple, and for each
tuple with at least one entry the hyperedge of its entries; tuples inducing the same set give one
hyperedge (edges form a set). -/
def hypergraph (A : RelStr) : FiniteHypergraph (Vtx A) where
  graph := {
    vertexSet := Set.univ
    edgeSet := {S | ∃ r ∈ A.rels, ∃ t ∈ r, t ≠ [] ∧ S = {v : Vtx A | v.val ∈ t}}
    subset_vertexSet_of_mem_edgeSet' := fun _ _ => Set.subset_univ _ }
  all_vertices := rfl
  edge_nonempty := by
    rintro S ⟨r, hr, t, ht, hne, rfl⟩
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil t hne
    exact ⟨⟨a, List.mem_flatten.2 ⟨t, List.mem_flatten.2 ⟨r, hr, ht⟩, ha⟩⟩, ha⟩
  covered := by
    rintro ⟨a, ha⟩
    obtain ⟨t, ht, hat⟩ := List.mem_flatten.1 ha
    obtain ⟨r, hr, htr⟩ := List.mem_flatten.1 ht
    exact ⟨{v : Vtx A | v.val ∈ t}, ⟨r, hr, t, htr, List.ne_nil_of_mem hat, rfl⟩, hat⟩

/-- Self-delimiting unary code of a natural number. -/
def encNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- Self-delimiting code of a list: each entry is preceded by `1`, the list ends with `0`. -/
def encList {α : Type} (f : α → List Bool) : List α → List Bool
  | [] => [false]
  | a :: l => true :: (f a ++ encList f l)

/-- The binary encoding of a structure as explicit lists: signature, domain size, tuple lists. -/
def encode (A : RelStr) : List Bool :=
  encList encNat A.arities ++ encNat A.size ++ encList (encList (encList encNat)) A.rels

/-- The encoding length `‖A‖`. -/
def norm (A : RelStr) : ℕ := (encode A).length

/-- The number of domain elements in the image of `h`. -/
def imageCard (A : RelStr) (h : ℕ → ℕ) : ℕ := ((Finset.range A.size).image h).card

/-- `h` is an endomorphism of `A` whose image has minimum domain cardinality among all
endomorphisms (p. 16). -/
def IsCoreMap (A : RelStr) (h : ℕ → ℕ) : Prop :=
  IsHomMap A A h ∧ ∀ g : ℕ → ℕ, IsHomMap A A g → imageCard A h ≤ imageCard A g

/-- The endomorphic image `h(A)`: its relations are the images of the relations of `A`. Only its
hypergraph `H_{h(A)}` is used, which depends only on the relations. -/
def image (A : RelStr) (h : ℕ → ℕ) : RelStr :=
  (A.arities, A.size, A.rels.map (List.map (List.map h)))

end RelStr

end SparseIncidenceHom.WidthComparison.Supplement


