-- Prove2me | Definitions.Def_CircStability_Main_Attachment
-- name    : CircStability_Main_Attachment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:20.394097+00:00
-- url     : https://prove2.me/theorems/70772f55-f968-43ba-b323-6cf95138f727
-- title:
--   §2.1, p. 6 — components of G − C, (x, R, y)-paths, N_C(R), strong and maximum strong attachments
-- statement:
--   This module defines the attachment notions of §2.1 of Ma and Ning. Let $C$ be a cycle of $G$.
--
--   1. **Component of $G-C$.** A nonempty vertex set $R$, disjoint from $V(C)$, inducing a connected subgraph, such that every neighbour of a vertex of $R$ lies in $R$ or on $C$.
--   2. **$(x,R,y)$-path.** An $(x,y)$-path all of whose internal vertices lie in $R$.
--   3. **$N_C(R)$.** The set of vertices of $C$ having at least one neighbour in $R$.
--   4. **Strong attachment** (p. 6). A set $M=\{x_1,\dots,x_s\}$ of vertices lying on $C$ in this cyclic order is a strong attachment of $R$ to $C$ if for every ordered pair $x_i,x_{i+1}$ (with $x_{s+1}=x_1$) there are $y_i,y_{i+1}\in R$ such that $x_iy_i$ and $x_{i+1}y_{i+1}$ are independent edges (edges with distinct endpoints).
--   5. **Maximum strong attachment.** A strong attachment of largest cardinality.
--
--   Strong attachments measure how a component of $G-C$ can be routed through when one builds cycles longer than $C$; they enter the clique-number bound of Lemma 2.5.
--
--   **Formalization Note.** The vertices of $C$ are listed as $C_0,C_1,\dots,C_{c-1}$ along the walk. Two vertices $C_i$ and $C_{(i+d)\bmod c}$ of $M$ ($0<d<c$) are consecutive when no $C_{(i+e)\bmod c}$ with $0<e<d$ lies in $M$. A one-element set is excluded explicitly, since the page's condition for $s=1$ asks for independent edges $x_1y_1$, $x_1y_1'$, which cannot exist; the empty set satisfies the condition vacuously.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 6 (§2.1, notation N_H(A), (x, H, y)-path, independent edges, strong attachment)

import Mathlib
import Definitions.Def_CircStability_Main_Setting
import Definitions.Def_CircStability_Bondy_Setting

namespace CircStability.Main

open Finset SimpleGraph

/-- `p` is an `(x, R, y)`-path (§2.1, p. 6): an `(x, y)`-path all of whose internal vertices lie
in `R`. -/
def IsThroughPath {n : ℕ} {G : SimpleGraph (Fin n)} {x y : Fin n} (R : Finset (Fin n))
    (p : G.Walk x y) : Prop :=
  p.IsPath ∧ ∀ v ∈ p.support, v ≠ x → v ≠ y → v ∈ R

open Classical in
/-- `N_S(R)`: the vertices of `S` with at least one neighbour in `R`. -/
noncomputable def attachSet {n : ℕ} (G : SimpleGraph (Fin n)) (S R : Finset (Fin n)) :
    Finset (Fin n) :=
  S.filter (fun x => ∃ y ∈ R, G.Adj x y)

/-- `M` is a strong attachment of `R` to the cycle `C` (§2.1, p. 6). The vertices of `C` are
`C.getVert i`, `i < |C|`. `M ⊆ V(C)`, `M` is not a single vertex, and for every two vertices
`x = C.getVert i`, `x' = C.getVert (i + d mod |C|)` of `M` that are consecutive in the cyclic order
(no vertex of `M` strictly between them going forward along `C`) there are distinct `y, y' ∈ R`
with `x ~ y` and `x' ~ y'`, i.e. two independent edges `xy`, `x'y'`. -/
def IsStrongAttachment {n : ℕ} (G : SimpleGraph (Fin n)) {u : Fin n} (C : G.Walk u u)
    (R M : Finset (Fin n)) : Prop :=
  M ⊆ C.support.toFinset ∧ #M ≠ 1 ∧
    ∀ i d : ℕ, i < C.length → 0 < d → d < C.length →
      C.getVert i ∈ M → C.getVert ((i + d) % C.length) ∈ M →
      (∀ e : ℕ, 0 < e → e < d → C.getVert ((i + e) % C.length) ∉ M) →
      ∃ y ∈ R, ∃ y' ∈ R, y ≠ y' ∧ G.Adj (C.getVert i) y ∧
        G.Adj (C.getVert ((i + d) % C.length)) y'

/-- A maximum strong attachment: a strong attachment of largest cardinality. -/
def IsMaxStrongAttachment {n : ℕ} (G : SimpleGraph (Fin n)) {u : Fin n} (C : G.Walk u u)
    (R T : Finset (Fin n)) : Prop :=
  IsStrongAttachment G C R T ∧ ∀ M, IsStrongAttachment G C R M → #M ≤ #T

end CircStability.Main


