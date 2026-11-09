-- Prove2me | Definitions.Def_AMPLowDeg_RankOne_Graph
-- name    : AMPLowDeg_RankOne_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:59:47.875199+00:00
-- url     : https://prove2.me/theorems/b421819a-be06-4314-9d03-bef5c42fef50
-- title:
--   Multi-indices as rooted multigraphs: degree, $V(\alpha)$, excess, $\mathcal T$, $\mathcal J$, rooted cores, $\mathrm{Aut}$, tagged occurrences
-- statement:
--   A multi-index $\alpha\in\mathbb N_0^{\mathcal E_n}$ is read as a multigraph on $[n]$ in which the edge or self-loop $e=(i,j)$ occurs $\alpha_e$ times.
--
--   1. $|\alpha|=\sum_e\alpha_e$ (each copy, loops included, counts once), $\alpha!=\prod_e\alpha_e!$, and $\{\alpha:|\alpha|\le D\}$ is a finite set.
--   2. The degree of $i$ counts each edge copy at $i$ once and each loop copy at $i$ twice. $V(\alpha)=\bigcup_{\alpha_{ij}>0}\{i,j\}$.
--   3. $\alpha$ is **connected** when any two vertices of $V(\alpha)$ are joined by a path of edges of $\alpha$. The **excess** is $\tau(\alpha)=|\alpha|-|V(\alpha)|+1$.
--   4. $\mathcal T$ is the set of nonempty connected $\alpha$ with $|\alpha|=|V(\alpha)|-1$ (trees); $\mathcal J$ the set of nonempty connected $\alpha$ with $\tau(\alpha)\ge1$.
--   5. A **rooted core** with root $1$ is a connected $\gamma$ with $1\in V(\gamma)$ (so the root has degree $\ge1$) in which every non-root vertex has degree $\ge2$. $\mathrm{Aut}(\gamma)$ is the number of vertex automorphisms of $\gamma$ fixing the root and preserving all edge and loop multiplicities; the labelled copies of $\gamma$ with root $1$ are its images under root-fixing relabellings of $[n]$.
--   6. **Tagged occurrences.** Label every edge copy of $\gamma$; each copy has two endpoint occurrences (distinct even for a loop), and there is one extra occurrence of $\theta_1$. $\mathcal I_i$ is the set of occurrences at vertex $i$, so $|\mathcal I_i|=\deg_\gamma(i)+\mathbf 1\{i=1\}$. For partitions $\pi_i\in\Pi(\mathcal I_i)$, the associated multigraph has the blocks as vertices, each edge copy joining the blocks of its two endpoint occurrences, and the block of the extra $\theta_1$ as root; $\pi=(\pi_i)$ is **connected** when this multigraph is connected.
--
--   These notions organize the graph expansion of $\sum_\alpha\mathbb E[A_\alpha(\theta)^2]/(n^{|\alpha|}\alpha!)$ in §§2, 4–6.
--
--   **Formalization Note** Vertices are `Fin n`; the root is a parameter (the theorems use vertex `⟨0, hn⟩`, the paper's vertex $1$). A family $(\pi_i)$ is represented by one partition of all tags whose blocks each lie inside a single $\mathcal I_i$; connectivity is reachability of every tag from the extra $\theta_1$ by moves inside a block or across an edge copy, which is connectivity of the block multigraph. `numCopies` counts the distinct relabellings of $\gamma$ by permutations fixing the root.
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 6 (multi-indices, |α|, α!), p. 8 (multigraph reading, V(α), τ(α), 𝒯, 𝒥), p. 14 (rooted core, Aut), p. 17 (tagged occurrences ℐ_i, connected partition families); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model

open Classical

namespace AMPLowDeg.RankOne

/-! Multi-indices `α ∈ ℕ₀^{ℰₙ}` (p. 6) and their reading as multigraphs on the vertex set `Fin n`
(p. 8): the edge or self-loop `e = (i, j)` occurs `α e` times. -/

/-- `|α| = Σ_e α_e`, the number of edge copies (each loop copy counts once). -/
def absIdx {n : ℕ} (α : Edge n → ℕ) : ℕ := ∑ e, α e

/-- `α! = Π_e α_e!` (edge multiplicities only, loops included). -/
def factIdx {n : ℕ} (α : Edge n → ℕ) : ℕ := ∏ e, (α e).factorial

/-- The finite set `{α ∈ ℕ₀^{ℰₙ} : |α| ≤ D}`. -/
noncomputable def multiIdx (n D : ℕ) : Finset (Edge n → ℕ) :=
  (Fintype.piFinset fun _ : Edge n => Finset.range (D + 1)).filter (fun α => absIdx α ≤ D)

/-- The number of endpoints of `e` equal to `i` (2 for a self-loop at `i`). -/
def incid {n : ℕ} (e : Edge n) (i : Fin n) : ℕ :=
  (if e.1.1 = i then 1 else 0) + (if e.1.2 = i then 1 else 0)

/-- The degree of vertex `i` in `α`: each edge copy at `i` contributes one, each loop copy two. -/
def deg {n : ℕ} (α : Edge n → ℕ) (i : Fin n) : ℕ := ∑ e, α e * incid e i

/-- The vertex set `V(α) = ⋃_{(i,j) : α_{ij} > 0} {i, j}` (p. 8), i.e. the vertices of positive
degree. -/
noncomputable def vertexSet {n : ℕ} (α : Edge n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ e, 0 < α e ∧ (e.1.1 = i ∨ e.1.2 = i))

/-- `i` and `j` are joined by an edge (or are the same vertex carrying a loop) of positive
multiplicity in `α`. -/
def adj {n : ℕ} (α : Edge n → ℕ) (i j : Fin n) : Prop :=
  ∃ e, 0 < α e ∧ ((e.1.1 = i ∧ e.1.2 = j) ∨ (e.1.1 = j ∧ e.1.2 = i))

/-- `α` is connected: any two vertices of `V(α)` are joined by a path of edges of `α`. -/
def IsConnected {n : ℕ} (α : Edge n → ℕ) : Prop :=
  ∀ i ∈ vertexSet α, ∀ j ∈ vertexSet α, Relation.ReflTransGen (adj α) i j

/-- The excess `τ(α) = |α| − |V(α)| + 1` (p. 8), an integer. -/
noncomputable def excess {n : ℕ} (α : Edge n → ℕ) : ℤ :=
  (absIdx α : ℤ) - ((vertexSet α).card : ℤ) + 1

/-- `α ∈ 𝒯`: `α` is nonempty, connected and `|α| = |V(α)| − 1` (Lemma 2.4). -/
def InTrees {n : ℕ} (α : Edge n → ℕ) : Prop :=
  α ≠ 0 ∧ IsConnected α ∧ absIdx α + 1 = (vertexSet α).card

/-- `α ∈ 𝒥`: `α` is nonempty, connected and `τ(α) ≥ 1` (Lemma 2.5(2)). -/
def InJ {n : ℕ} (α : Edge n → ℕ) : Prop :=
  α ≠ 0 ∧ IsConnected α ∧ 1 ≤ excess α

/-- `γ` is a rooted core with root `r` (p. 14): it is connected, the root is a vertex (so it has
degree at least one), and every nonroot vertex has degree at least two. -/
def IsRootedCore {n : ℕ} (r : Fin n) (γ : Edge n → ℕ) : Prop :=
  IsConnected γ ∧ r ∈ vertexSet γ ∧ ∀ i ∈ vertexSet γ, i ≠ r → 2 ≤ deg γ i

/-- Relabelling of the vertices by a permutation `σ`: vertex `i` of `γ` becomes `σ i`. -/
def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (γ : Edge n → ℕ) : Edge n → ℕ :=
  fun e => γ (mkEdge (σ.symm e.1.1) (σ.symm e.1.2))

/-- `Aut(γ)`: the number of vertex automorphisms of `γ` (bijections of `V(γ)`, extended by the
identity off `V(γ)`) that fix the root `r` and preserve all edge multiplicities, loop multiplicities
included (Lemma 6.1). -/
noncomputable def rootedAut {n : ℕ} (r : Fin n) (γ : Edge n → ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    σ r = r ∧ relabel σ γ = γ ∧ ∀ i ∉ vertexSet γ, σ i = i)).card

/-- The number of distinct labelled copies of `γ` on the vertex set `Fin n` with the same root `r`,
i.e. the size of the rooted isomorphism class of `γ` among multigraphs on `Fin n`. -/
noncomputable def numCopies {n : ℕ} (r : Fin n) (γ : Edge n → ℕ) : ℕ :=
  ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ r = r)).image (fun σ => relabel σ γ)).card

/-- Tagged occurrences for a multigraph `γ` (p. 17): `none` is the additional occurrence of `θ₁`
(the root variable); `some ⟨e, k, b⟩` is endpoint `b` (`false` = first, `true` = second
coordinate of `e`) of the `k`-th copy of the edge `e`. Both endpoints of a loop copy are distinct
tags. -/
abbrev Tag {n : ℕ} (γ : Edge n → ℕ) := Option (Σ e : Edge n, Fin (γ e) × Bool)

/-- The vertex `i(o)` of a tagged occurrence `o`. -/
def tagVertex {n : ℕ} (r : Fin n) {γ : Edge n → ℕ} : Tag γ → Fin n
  | none => r
  | some ⟨e, _, false⟩ => e.1.1
  | some ⟨e, _, true⟩ => e.1.2

/-- The tagged occurrence set `ℐᵢ` of vertex `i`. -/
noncomputable def tagSet {n : ℕ} (r : Fin n) (γ : Edge n → ℕ) (i : Fin n) : Finset (Tag γ) :=
  Finset.univ.filter (fun o => tagVertex r o = i)

/-- The edge copy an occurrence belongs to (`none` for the root occurrence). -/
def tagCopy {n : ℕ} {γ : Edge n → ℕ} : Tag γ → Option (Σ e : Edge n, Fin (γ e))
  | none => none
  | some ⟨e, k, _⟩ => some ⟨e, k⟩

/-- A partition of all tags is a family `π = (πᵢ)_{i ∈ V(γ)}` with `πᵢ ∈ Π(ℐᵢ)` exactly when each
block lies inside a single `ℐᵢ`; then `πᵢ` is the set of blocks contained in `ℐᵢ`. -/
def IsVertexHomog {n : ℕ} (r : Fin n) {γ : Edge n → ℕ}
    (P : Finpartition (Finset.univ : Finset (Tag γ))) : Prop :=
  ∀ A ∈ P.parts, ∀ o ∈ A, ∀ o' ∈ A, tagVertex r o = tagVertex r o'

/-- `π` is connected (p. 17): in the multigraph whose vertices are the blocks, where each edge copy of
`γ` joins the blocks of its two endpoint tags and the block of the root occurrence is the root,
every block is reachable from the root block. Equivalently, every tag is reachable from the root
occurrence by moves inside a block or across an edge copy. -/
def IsPartConnected {n : ℕ} {γ : Edge n → ℕ}
    (P : Finpartition (Finset.univ : Finset (Tag γ))) : Prop :=
  ∀ o : Tag γ, Relation.ReflTransGen
    (fun a b => (∃ A ∈ P.parts, a ∈ A ∧ b ∈ A) ∨
      (∃ c : Σ e : Edge n, Fin (γ e), tagCopy a = some c ∧ tagCopy b = some c)) none o

end AMPLowDeg.RankOne


