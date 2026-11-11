-- Prove2me | Definitions.Def_PlanarDFVSKernel_PDFVSInstance
-- name    : PlanarDFVSKernel_PDFVSInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:35:13.495704+00:00
-- url     : https://prove2.me/theorems/3e3c8d63-a316-4732-a767-5769df962b3c
-- title:
--   Instances $(D,k)$ of (Planar) Directed Feedback Vertex Set and their binary encoding
-- statement:
--   An **instance** $(D,k)$ consists of a finite digraph $D$ with vertex set $\{0,\dots,n-1\}$ and arc identities $\{0,\dots,m-1\}$ (each arc has a tail and a head; loops, repeated arcs and opposite arcs are allowed) and a budget $k\in\mathbb N$.
--
--   Its **encoding** is the bit string formed by $n$ in unary (the explicit vertex list), then $m$, the tail and head of every arc in order (the explicit arc list), and $k$, each in self-delimiting binary. This is the paper's convention: "We measure the encoding size using explicit vertex and arc lists and a binary parameter."
--
--   **Formalization Note** The digraph is the published carrier `PlanarDFVS.SingleExp.Graph n m`; planarity is the published property `Planar`. The encoding is injective, so polynomial time with respect to it is polynomial time in $n+m\log n+\log k$.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §1, p.1 (PDF 2) and §3, p.8 (PDF 9)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs
import Definitions.Def_PlanarDFVSKernel_binNat

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **An instance `(D, k)` of (Planar) Directed Feedback Vertex Set** (Sheng, Xiao, *A Polynomial
Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256
75cfca8f…), §1, p.1 (PDF 2)): "Input. A finite digraph D and a nonnegative integer k."

`n` is the number of vertices (vertex set `Fin n`), `m` the number of arcs (arc identities
`Fin m`), `G` the digraph (tail and head maps; loops, repeated arcs and opposite arcs allowed, as on
p.6 (PDF 7)), and `k` the deletion budget.

**Formalization Note** The digraph is the published multigraph carrier
`PlanarDFVS.SingleExp.Graph n m`. The instance is a plain structure; planarity is a property of
`G` (`PlanarDFVS.SingleExp.Planar`), not part of the data. -/
structure PDFVSInstance where
  /-- number of vertices -/
  n : ℕ
  /-- number of arcs -/
  m : ℕ
  /-- the digraph -/
  G : Graph n m
  /-- the budget -/
  k : ℕ

/-- **Encoding of an instance as a bit string** (Sheng, Xiao, arXiv:2609.23669 (held version,
sha256 75cfca8f…), §3, p.8 (PDF 9): "We measure the encoding size using explicit vertex and arc
lists and a binary parameter.").

The string is: `n` in unary (`n` copies of `true`, then `false`: the explicit vertex list), the
number of arcs `m` in self-delimiting binary (`binNat`), then for each arc `e = 0, …, m − 1` its
tail and its head in self-delimiting binary (the explicit arc list), and finally `k` in
self-delimiting binary.

**Formalization Note** The encoding is injective (decoding reads `n`, then `m`, then `2m`
numbers, then `k`). The parameter is binary, so polynomial time in the length of this string is
polynomial time in `n + m log n + log k`, the paper's encoding size. -/
def encInst (I : PDFVSInstance) : List Bool :=
  List.replicate I.n true ++ false ::
    (binNat I.m ++
      ((List.finRange I.m).flatMap fun e => binNat (I.G.tail e : ℕ) ++ binNat (I.G.head e : ℕ)) ++
      binNat I.k)

end PlanarDFVSKernel


