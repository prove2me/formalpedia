-- Prove2me | Definitions.Def_InfoLossLAR_WorstCase_FixedT
-- name    : InfoLossLAR_WorstCase_FixedT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:02:58.045283+00:00
-- url     : https://prove2.me/theorems/d754c790-957f-4075-b46d-2798eb3649e5
-- title:
--   The rounding matrix of Definition 6.3, its label, $H_0$, $c_T$, incidence loads and oriented trees
-- statement:
--   For an odd prime $q$ and $d\ge q$ (Definition 6.3), let $e_1,\dots,e_d$ be the standard basis of $\mathbb Z^d$ and
--   $$T=[\,e_1-e_2\mid\cdots\mid e_{d-1}-e_d\mid v_0\,],\qquad v_0=\sum_{j=1}^{q}e_j .$$
--   With the scalar quotient encoding $P=\mathbf 1^\top$ the label is $f_T(x)=\sum_{j=1}^d\lfloor (T[x]_q)_j/q\rfloor\bmod q\in\mathbb F_q$ and $\mathcal F_{T,0}=f_T^{-1}(0)$. The **zero-sum hyperplane** is $H_0=\{\bar w\in\mathbb F_q^d:\mathbf 1^\top\bar w=0\}$ and the **canonical endpoint pullback** is $c_T(\bar w)=T^{-1}[\bar w]_q\bmod q$ with $T^{-1}$ over $\mathbb Q$. For integer $(Q,\beta)$ and $x\in\mathbb Z^d$ the **vertex load** is $w=T(Qx+\beta)$ (Definition 6.1).
--
--   An **oriented tree** on the vertex set $\{1,\dots,d\}$ is a tree with each edge oriented from a tail to a head; its **signed incidence matrix** $D_{\mathscr T}$ has one column per edge, $+1$ at the tail and $-1$ at the head; $[D_{\mathscr T}\mid v]$ appends one column $v$.
--
--   **Formalization Note.** Indices are $0$-based. $c_T$ is defined on all of $\mathbb F_q^d$; on $H_0$ the vector $T^{-1}[\bar w]_q$ is integral and each entry is read through its numerator. Incidence-matrix columns are indexed by the edge set (and `edges ⊕ Unit` for the extended matrix).
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 19 (remark after Lemma 3.5), p. 26 §6.1 and Definition 6.1, p. 27 Definition 6.3, H_0 and c_T, p. 28 §6.3

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Rounding

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-!
# The rounding matrix of Definition 6.3, its zero fiber, and tree incidence matrices

Chen Qian, *Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices*,
arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 19 (the remark after Lemma 3.5: for
`ℓ = 1` and `P = 1ᵀ`, `f_T(x) = ∑_j ⌊(T[x]_q)_j / q⌋ mod q`), p. 26 (§6.1: signed incidence
matrices), p. 27 (Definition 6.3; `H_0`; the canonical endpoint pullback `c_T`), p. 28 (§6.3:
oriented spanning trees on `V = {1, …, d}`).

Indices are 0-based: the paper's vertex/coordinate `j ∈ {1, …, d}` is `j − 1 : Fin d`.
-/

/-- Definition 6.3 (p. 27): `T = [D_d | v_0] ∈ ℤ^{d×d}` with path columns
`D_d = [e_1 − e_2 | ⋯ | e_{d−1} − e_d]` and `v_0 = ∑_{j=1}^{q} e_j`. In 0-based indices, column
`j < d − 1` is `e_j − e_{j+1}` and the last column `d − 1` has a `1` in rows `0, …, q − 1`.
(The paper assumes `q` an odd prime and `d ≥ q`; these are hypotheses of every statement.) -/
def TDef63 (q d : ℕ) : Matrix (Fin d) (Fin d) ℤ :=
  fun i j =>
    if (j : ℕ) + 1 < d then
      (if i = j then 1 else if (i : ℕ) = (j : ℕ) + 1 then -1 else 0)
    else (if (i : ℕ) < q then 1 else 0)

/-- The encoded label of Definition 6.3 with the scalar quotient encoding `P = 1ᵀ` (p. 19 and
p. 27): `f_T(x) = ∑_{j=1}^{d} ⌊(T[x]_q)_j / q⌋ mod q ∈ 𝔽_q` for `x ∈ 𝔽_q^d`. -/
def fT63 (q d : ℕ) (x : Fin d → ZMod q) : ZMod q :=
  ((∑ j, AR q (TDef63 q d) (lift x) j : ℤ) : ZMod q)

/-- The zero fiber `F_{T,0} = {x ∈ 𝔽_q^d : f_T(x) = 0}` of the label of Definition 6.3. -/
def zeroFiber63 (q d : ℕ) : Set (Fin d → ZMod q) := {x | fT63 q d x = 0}

/-- The zero-sum hyperplane `H_0 = {w̄ ∈ 𝔽_q^d : 1ᵀw̄ = 0}` (p. 27). -/
def H0 (q d : ℕ) : Set (Fin d → ZMod q) := {w | ∑ i, w i = 0}

/-- `T^{-1}` over `ℚ` (Definition 6.3's `T` has `|det T| = q ≠ 0`). -/
noncomputable def TinvQ (q d : ℕ) : Matrix (Fin d) (Fin d) ℚ :=
  ((TDef63 q d).map (Int.cast : ℤ → ℚ))⁻¹

/-- The canonical endpoint pullback (p. 27): `c_T(w̄) = T^{-1}[w̄]_q mod q`, `T^{-1}` over `ℚ`.
For `w̄ ∈ H_0` the vector `T^{-1}[w̄]_q` is integral (the paper's remark), and each entry is read
as an integer through its numerator (for an integer this is the integer itself).
Applied to all of `𝔽_q^d`; statements restrict it to `H_0`. -/
noncomputable def cT (q d : ℕ) (w : Fin d → ZMod q) : Fin d → ZMod q :=
  fun i => (((TinvQ q d).mulVec (fun j => ((lift w j : ℤ) : ℚ)) i).num : ZMod q)

/-- Definition 6.1 (p. 26), for the matrix of Definition 6.3: the incidence representation of an
integer transport pair `(Q, β)` is `D_T = TQ`, `z_0 = Tβ`, and the vertex load at an integer
source representative `x ∈ ℤ^d` is `w = D_T x + z_0 = T(Qx + β)`. -/
def incidenceLoad (q d : ℕ) (Q : Matrix (Fin d) (Fin d) ℤ) (β : Fin d → ℤ) (x : Fin d → ℤ) :
    Fin d → ℤ :=
  (TDef63 q d).mulVec (Q.mulVec x + β)

/-- An oriented tree on the vertex set `Fin d` (§6.1, §6.3): a simple graph that is a tree,
with each edge `e = {u, v}` oriented from its tail to its head. -/
structure OrientedTree (d : ℕ) where
  /-- The underlying graph on the vertices `Fin d`. -/
  G : SimpleGraph (Fin d)
  /-- Adjacency is decidable (so the edge set is a finite type). -/
  dec : DecidableRel G.Adj
  /-- The graph is a tree (connected and acyclic). -/
  isTree : G.IsTree
  /-- The tail of each edge. -/
  tail : G.edgeSet → Fin d
  /-- The head of each edge. -/
  head : G.edgeSet → Fin d
  /-- Each edge is `{tail, head}`. -/
  orient : ∀ e : G.edgeSet, s(tail e, head e) = (e : Sym2 (Fin d))

instance {d : ℕ} (𝒯 : OrientedTree d) : DecidableRel 𝒯.G.Adj := 𝒯.dec

/-- The signed incidence matrix `D_𝒯` (§6.1, p. 26): one column per edge, `+1` at its tail,
`−1` at its head, `0` elsewhere. Columns are indexed by the edges. -/
def OrientedTree.incidence {d : ℕ} (𝒯 : OrientedTree d) : Matrix (Fin d) 𝒯.G.edgeSet ℤ :=
  fun v e => if v = 𝒯.tail e then 1 else if v = 𝒯.head e then -1 else 0

/-- The extended incidence matrix `[D_𝒯 | v]` (Lemma 6.7, Corollary 6.8): the edge columns
followed by one extra column `v`. Columns are indexed by `edges ⊕ Unit`. -/
def OrientedTree.extended {d : ℕ} (𝒯 : OrientedTree d) (v : Fin d → ℤ) :
    Matrix (Fin d) (𝒯.G.edgeSet ⊕ Unit) ℤ :=
  fun i c => Sum.elim (fun e => 𝒯.incidence i e) (fun _ => v i) c

end InfoLossLAR.WorstCase


