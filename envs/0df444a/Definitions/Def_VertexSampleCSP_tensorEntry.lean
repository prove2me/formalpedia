-- Prove2me | Definitions.Def_VertexSampleCSP_tensorEntry
-- name    : VertexSampleCSP_tensorEntry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:38.316355+00:00
-- url     : https://prove2.me/theorems/c4856f38-431c-479d-8c9b-c2ed559c6d89
-- title:
--   The payoff tensor $T$, the multilinear form $T[w_1,\dots,w_r]$ and the polynomial $P(x)$
-- statement:
--   $T$ is the symmetric tensor of order $r$ on $\mathbb R^{V\times[q]}$ with entry $f_e(a)/r!$ at each of the $r!$ orderings of the coordinates $(i,a_i)$, $i\in e$, for every $r$-subset $e$ and every $a\in[q]^e$, and with all other entries zero. In particular an entry is zero whenever two of its coordinates belong to one variable. The multilinear form is
--
--   $$T[w_1,\dots,w_r]=\sum_{c\in(V\times[q])^r}T_c\prod_j w_j(c_j),$$
--
--   and $P(x)=T[x,\dots,x]$. If $x$ is the one-hot encoding of $\sigma$, then $P(x)=F_{\mathcal I}(\sigma)$.
--
--   **Formalization Note** The tensor is an entry function on `Fin r → V × Fin q`. An ordering of the coordinates is an injective tuple whose set of entries is the graph of $a$ on $e$.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A, "The encoding", p.13 (PDF p.15)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance

namespace VertexSampleCSP

open Classical in
/-- **The payoff tensor `T`.** Chang, *Optimal Vertex Sampling for Constraint Satisfaction Problems*,
STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A, "The encoding", p.13 (PDF p.15):
"Let T be the symmetric tensor of order r on ℝ^{V×[q]} with entry fe(a)/r! at each of the r!
orderings of the coordinates (i1, a_{i1}), . . . , (ir, a_{ir}), for every e = {i1, . . . , ir} and
a ∈ [q]^e, and with all other entries zero."

`tensorEntry I c` is the entry of `T` at the index tuple `c = (c_1, …, c_r)` of coordinates
`c_j ∈ V × [q]`. An ordering of the coordinates `(i, a_i)`, `i ∈ e`, is an injective tuple `c` whose
set of entries is `{(i, a_i) : i ∈ e}`; at such a `c` the entry is `f_e(a)/r!`, and every other entry
is `0`. At most one pair `(e, a)` matches a given `c` (the first components of `c` give `e`, the
second give `a`), so the double sum below has at most one nonzero term.

**Formalization Note.** The tensor is an entry function on `Fin r → V × Fin q`. -/
noncomputable def tensorEntry {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) (c : Fin r → V × Fin q) : ℝ :=
  ∑ e ∈ Finset.powersetCard r Finset.univ, ∑ a : (e → Fin q),
    if Function.Injective c ∧
        Finset.univ.image c = e.attach.image (fun i : e => ((i : V), a i))
    then I.f e a / (r.factorial : ℝ) else 0

/-- **The multilinear form `T[w_1, …, w_r]`.** Chang, STOC 2027 submission (manuscript sha256
1e0edd23…), Appendix A, "The encoding", p.13: `T[w_1, …, w_r] = Σ_c T_c Π_j w_j(c_j)`, the sum over
all index tuples `c ∈ (V × [q])^r`. -/
noncomputable def tensorMul {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) (w : Fin r → EuclideanSpace ℝ (V × Fin q)) : ℝ :=
  ∑ c : Fin r → V × Fin q, tensorEntry I c * ∏ j, w j (c j)

/-- **The polynomial `P(x) = T[x, …, x]`.** Chang, STOC 2027 submission (manuscript sha256
1e0edd23…), Appendix A, "The encoding", p.13: "Let P(x) = T[x, . . . , x]. If x is the one-hot
encoding of σ, then P(x) = FI(σ)." -/
noncomputable def poly {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) (x : EuclideanSpace ℝ (V × Fin q)) : ℝ :=
  tensorMul I (fun _ => x)

end VertexSampleCSP


