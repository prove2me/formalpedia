-- Prove2me | Definitions.Def_ZeroExtensionGap_Supplement_Code
-- name    : ZeroExtensionGap_Supplement_Code
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:23:12.1185+00:00
-- url     : https://prove2.me/theorems/20a01ecb-f6ff-4396-b755-4e36005da74b
-- title:
--   Encoded 0-Extension inputs with rational data, their instance, and their binary code
-- statement:
--   A **code** of a 0-Extension input is finite data: a number of vertices $m$ (the vertex set is $\{0,\dots,m-1\}$), a list of edges $(u,v,w_{u,v})$ with rational weights, a list of terminals, a list of values $(a,b,D(a,b))$ of the terminal metric on ordered pairs, with rational values, and a rational threshold $\tau$.
--
--   A code describes the 0-Extension instance $I=(G,w,T,D)$ in which
--
--   1. $G$ has an edge $\{u,v\}$ ($u\ne v$) exactly when some listed edge has these endpoints, and $w_{\{u,v\}}$ is the sum of the listed weights of its copies;
--   2. $T$ is the set of listed terminals;
--   3. $D(a,b)$ is the value of the first listed entry for the ordered pair $(a,b)$, and $0$ if there is none.
--
--   The **binary string** of a code writes $m$ in unary, then the number of edges and each edge (two endpoints and a weight), then the number of terminals and each terminal, then the number of metric entries and each entry, then $\tau$. Natural numbers are written in self-delimiting binary and rationals as a signed binary numerator followed by a binary denominator.
--
--   These are the inputs of the promise problem behind Theorem 2: the string length is at least $m$ and at least the bit length of every number in the input, so polynomial time in the string length is polynomial time in the size of the instance.
--
--   **Formalization Note.** Parallel edges are merged by adding weights and loops are dropped, which changes no retraction cost (loops cost $D(x,x)=0$). A malformed code (a missing or duplicated pair, a negative weight) still describes an instance, which then fails validity; every valid instance with rational data on $m$ vertices is described by some code. The binary codes of naturals and rationals are the published `QAlgorithms_ClassicalBinaryEncoding` and `QAlgorithms_ClassicalRationalEncoding`; the instance type and its validity are the base mission's `ZeroExtensionGap_Instance`.
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), §1, p.1 (PDF p.3) (instances) and Theorem 2, p.3 (PDF p.5) (the inputs of the hardness statement)

import Mathlib
import Definitions.Def_ZeroExtensionGap_Instance
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

set_option autoImplicit false

namespace ZeroExtensionGap.Supplement

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

/-- An encoded 0-Extension input with rational data together with a threshold, the input of the
promise problem behind Theorem 2 of Chen, Zhu, *Almost Tight Hardness of Approximation for
0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), §1, p.1 (PDF p.3) and §1.1, p.3
(PDF p.5).
* `m` is the number of vertices; the vertex set is `Fin m`.
* `edges` lists the edges `(u, v, w_{u,v})` with a rational weight each.
* `terms` lists the terminals.
* `dist` lists values `(a, b, D(a,b))` of the terminal function on ordered pairs.
* `τ` is the rational threshold of the decision version.
**Formalization Note.** Theorem 2 is a complexity statement, so the input is finite data: rational
weights and distances, as is standard for weighted problems. The code carries only input data, never
`OPT` or a solution. A code with a malformed part (a missing or a duplicated pair in `dist`, a
negative weight) still maps to an `Instance`, which may then fail `Instance.IsValid`; the promise
problem only accepts valid instances. -/
structure Code : Type where
  /-- The number of vertices; the vertex set is `Fin m`. -/
  m : ℕ
  /-- The edge list: endpoints and a rational weight. -/
  edges : List (Fin m × Fin m × ℚ)
  /-- The terminal list. -/
  terms : List (Fin m)
  /-- Values of the terminal metric on ordered pairs of terminals. -/
  dist : List (Fin m × Fin m × ℚ)
  /-- The threshold of the decision version. -/
  τ : ℚ

namespace Code

/-- The 0-Extension instance `I = (G, w, T, D)` on `Fin m` described by a code (§1, p.1, PDF p.3).
* `G` has an edge `{u, v}` (`u ≠ v`) iff some listed edge has these endpoints.
* `w {u,v}` is the sum of the listed weights of all copies of `{u,v}`.
* `T` is the set of listed terminals.
* `D(a, b)` is the value of the first entry of `dist` for the ordered pair `(a, b)`, and `0` when there is none.
**Formalization Note.** The page's graph may have parallel edges and loops. Parallel copies are
merged by adding their weights, and loops are dropped (they cost `D(x,x) = 0`); the base
`Instance` documents that neither changes `OPT`. A missing pair `(a, b)` with `a ≠ b` gives
`D(a,b) = 0`, so the instance is invalid; every valid instance with rational data on `Fin m` is the
image of some code. -/
noncomputable def toInstance (c : Code) : Instance (Fin c.m) where
  G := SimpleGraph.fromEdgeSet {e | ∃ x ∈ c.edges, s(x.1, x.2.1) = e}
  w := fun e => ((c.edges.filter (fun x => decide (s(x.1, x.2.1) = e))).map
    (fun x => (x.2.2 : ℝ))).sum
  T := c.terms.toFinset
  D := fun a b => (((c.dist.find? (fun x => decide (x.1 = a.1 ∧ x.2.1 = b.1))).map
    (fun x => (x.2.2 : ℝ))).getD 0)

/-- The binary string of a code. The number of vertices in unary (`encNat`, the explicit graph lists
its vertices); then the number of edges and each edge as endpoint, endpoint, weight; the number of
terminals and each terminal; the number of `dist` entries and each as terminal, terminal, value;
finally the threshold. Indices and counts use the self-delimiting binary code `encBin`, rationals
`encRat` (sign and binary numerator, binary denominator), from the published
`QAlgorithms_ClassicalBinaryEncoding` / `QAlgorithms_ClassicalRationalEncoding`.
**Formalization Note.** The length of the string is at least `m` and at least the number of bits of
every number of the input, so a polynomial in the string length is a polynomial in the bit size of
the instance. Every field is written with a self-delimiting code, so the string determines the
code. -/
def encode (c : Code) : Str :=
  encNat c.m ++
    encBin c.edges.length ++
    c.edges.flatMap (fun x => encBin x.1.val ++ encBin x.2.1.val ++ encRat x.2.2) ++
    encBin c.terms.length ++
    c.terms.flatMap (fun t => encBin t.val) ++
    encBin c.dist.length ++
    c.dist.flatMap (fun x => encBin x.1.val ++ encBin x.2.1.val ++ encRat x.2.2) ++
    encRat c.τ

end Code

end ZeroExtensionGap.Supplement


