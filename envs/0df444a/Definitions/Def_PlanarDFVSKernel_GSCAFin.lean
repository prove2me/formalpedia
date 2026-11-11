-- Prove2me | Definitions.Def_PlanarDFVSKernel_GSCAFin
-- name    : PlanarDFVSKernel_GSCAFin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:36:49.699902+00:00
-- url     : https://prove2.me/theorems/47488736-8439-4dc3-9637-2eaefdf7649a
-- title:
--   GSCA instances as machine inputs
-- statement:
--   A GSCA instance on the vertex set $\{0,\dots,N-1\}$, encoded by $N$ in unary, then the base arcs, the groups (each as the increasing list of its arc codes $uN+v$) and $k$, all numbers in self-delimiting binary. The encoding is injective.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 6.2, p.27 (PDF 28)

import Mathlib
import Definitions.Def_PlanarDFVSKernel_GSCA
import Definitions.Def_PlanarDFVSKernel_binNat

set_option autoImplicit false

namespace PlanarDFVSKernel

/-- **A GSCA instance on the vertex set `{0, …, N − 1}`**, the form in which GSCA instances are
machine inputs (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*,
arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 6.2, p.27 (PDF 28)). -/
structure GSCAFin where
  /-- the number of vertices -/
  N : ℕ
  /-- the instance on `Fin N` -/
  inst : GSCA (Fin N)

/-- The number `uN + v` of an arc `u → v` on `Fin N`; injective on `Fin N × Fin N`. -/
def arcCode {N : ℕ} (a : Fin N × Fin N) : ℕ := (a.1 : ℕ) * N + (a.2 : ℕ)

/-- **Encoding of a GSCA instance** with explicit vertex, arc and group lists and a binary
parameter (as for PDFVS, ibid., §3, p.8 (PDF 9)): `N` in unary, then the number of base arcs and
each base arc's endpoints, then the number of groups and, for each group, its number of arcs and the
codes `arcCode` of its arcs in increasing order, then `k`; all numbers after `N` in self-delimiting
binary.

**Formalization Note** A group is a set; listing its arcs in increasing code order makes the
encoding a function of the set. The encoding is injective, and its length is
`O(N + (|A(H)| + entries + #groups) log N + log k)`. -/
def encGSCA (I : GSCAFin) : List Bool :=
  List.replicate I.N true ++ false ::
    (binNat I.inst.base.length ++
      (I.inst.base.flatMap fun a => binNat (a.1 : ℕ) ++ binNat (a.2 : ℕ)) ++
      binNat I.inst.groups.length ++
      (I.inst.groups.flatMap fun g =>
        binNat g.card ++ ((g.image arcCode).sort (· ≤ ·)).flatMap binNat) ++
      binNat I.inst.k)

end PlanarDFVSKernel


