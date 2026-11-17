-- Prove2me | Definitions.Def_QLocalCert_Supplement_SYM
-- name    : QLocalCert_Supplement_SYM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:39:19.732737+00:00
-- url     : https://prove2.me/theorems/9a9ef9b0-e359-4e21-a4a5-84a6915b47b1
-- title:
--   Graph symmetry $\mathrm{SYM}$ and bounded-radius symmetry $\mathrm{SYM}_D$
-- statement:
--   A graph $G$ on the vertex set $\{0,\dots,n-1\}$ belongs to $\mathrm{SYM}$ (graph symmetry) if it admits a **nontrivial automorphism**: a permutation $\varphi$ of the vertices that preserves adjacency in both directions ($u\sim v \iff \varphi(u)\sim\varphi(v)$) and is not the identity, i.e. moves at least one vertex.
--
--   For a known integer $D$, $G$ belongs to $\mathrm{SYM}_D$ if, in addition, its **radius** is at most $D$:
--   $$
--   \mathrm{rad}(G)=\min_{u}\ \max_{v}\ \mathrm{dist}_G(u,v)\le D .
--   $$
--
--   These are the graph properties certified by the quantum protocol of Theorem 2 and Corollary 3 and bounded from below for classical multi-round protocols by Theorem 4. As graph properties they are evaluated on the connected communication graph of a network instance.
--
--   **Formalization Note** The radius is Mathlib's `SimpleGraph.radius`, valued in $\mathbb N\cup\{\infty\}$ (infinite only for disconnected or empty graphs, which are never instances). "Nontrivial" is written as "some vertex $v$ has $\varphi(v)\ne v$". The paper's $D\ge 1$ is imposed in the theorems that use $\mathrm{SYM}_D$.
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), §1.1, p.5 (SYM, SYM_D); §5, p.44 (SYM_D := {G ∈ SYM : rad(G) ≤ D})

import Mathlib

set_option autoImplicit false

namespace QLocalCert.Supplement

/-- **SYM** (graph symmetry): the graph `G` admits a nontrivial automorphism, "an adjacency-preserving
permutation of the vertices other than the identity".

B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), §1.1, p.5, and §5, p.44 ("Let SYM be the
class of connected graphs having such an automorphism").

**Formalization Note.** A predicate on graphs on `Fin n`, for use with `DQMA1.Correct` and
`DMA.Correct`, whose instances are connected (connectedness is part of `QLocalCert.Instance`).
"Nontrivial" is written as "moves some vertex", which is the same as `φ ≠ id`. -/
def SYM {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ φ : G ≃g G, ∃ v : Fin n, φ v ≠ v

/-- **SYM_D** (bounded-radius graph symmetry): `G` has radius at most `D` and a nontrivial
automorphism.

Source: as `SYM`, §1.1, p.5 ("For a known integer D ≥ 1, let SYM_D denote the class of graphs of
radius at most D that admit a nontrivial automorphism") and §5, p.44
(`SYM_D := {G ∈ SYM : rad(G) ≤ D}`).

**Formalization Note.** `rad(G)` is Mathlib's `SimpleGraph.radius` (`ℕ∞`-valued: the minimum over
vertices of the eccentricity, the maximum graph distance from the vertex; it is `⊤` only for a
disconnected or empty graph, which never occurs for an instance). `D : ℕ` is a parameter known to
the nodes (fixed with the protocol); the paper's `D ≥ 1` is imposed where `SYM_D` is used. -/
def SYMD {n : ℕ} (D : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  G.radius ≤ (D : ℕ∞) ∧ SYM G

end QLocalCert.Supplement


