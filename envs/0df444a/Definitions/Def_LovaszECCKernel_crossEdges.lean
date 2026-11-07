-- Prove2me | Definitions.Def_LovaszECCKernel_crossEdges
-- name    : LovaszECCKernel_crossEdges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:55:05.942106+00:00
-- url     : https://prove2.me/theorems/f2cc6cb1-d975-4e7f-851f-dd2b6e89f515
-- title:
--   Edges and non-edges between two vertex sets, $|E_G(X,Y)|$ and $|\overline E_G(X,Y)|$
-- statement:
--   For disjoint sets of vertices $X,Y\subseteq V(G)$,
--   $$E_G(X,Y)=\{xy\in E(G): x\in X,\ y\in Y\}$$
--   is the set of **edges between** $X$ and $Y$, and $\overline E_G(X,Y)=E_{\overline G}(X,Y)$ the set of **non-edges between** them. The two numbers $|E_G(X,Y)|$ and $|\overline E_G(X,Y)|$ appear in Lemma 1 (non-edges between cliques of a deletion sequence) and Lemma 4 (edges between the two largest parts).
--
--   **Formalization Note** Counted as ordered pairs $(x,y)\in X\times Y$ with $xy\in E(G)$, resp. $x\ne y$ and $xy\notin E(G)$; for disjoint $X,Y$ these are the numbers of edges, resp. non-edges, between them.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), §2, p.15 (= PDF p.15)

import Mathlib

set_option autoImplicit false

namespace LovaszECCKernel

open Classical in
/-- The number `|E_G(X, Y)|` of **edges between** two disjoint vertex sets (Fomin, Golovach,
Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic Extensions of the Lovász
and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript sha256 a9d53ab8…), §2, p.15
(= PDF p.15)): "For two disjoint sets of vertices X, Y ⊆ V(G), we write E_G(X, Y) to denote the set
of edges between X and Y, that is, E_G(X, Y) = {xy ∈ E(G) | x ∈ X and y ∈ Y}."

**Formalization Note** Counted as pairs `(x, y) ∈ X × Y` with `xy ∈ E(G)`; for disjoint `X, Y` each
such edge is counted once. Every use in the mission has `X, Y` disjoint. -/
noncomputable def crossEdges {V : Type*} (G : SimpleGraph V) (X Y : Finset V) : ℕ :=
  ((X ×ˢ Y).filter (fun p => G.Adj p.1 p.2)).card

open Classical in
/-- The number `|E̅_G(X, Y)|` of **non-edges between** two disjoint vertex sets (Fomin et al., STOC
2027 submission (manuscript sha256 a9d53ab8…), §2, p.15 (= PDF p.15)): "We also define
E̅_G(X, Y) = E_{G̅}(X, Y), that is, this is the set of non-edges between X and Y."

**Formalization Note** Counted as pairs `(x, y) ∈ X × Y` with `x ≠ y` and `xy ∉ E(G)`; for disjoint
`X, Y` the condition `x ≠ y` is automatic and each non-edge is counted once. -/
noncomputable def crossNonEdges {V : Type*} (G : SimpleGraph V) (X Y : Finset V) : ℕ :=
  ((X ×ˢ Y).filter (fun p => p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2)).card

end LovaszECCKernel


