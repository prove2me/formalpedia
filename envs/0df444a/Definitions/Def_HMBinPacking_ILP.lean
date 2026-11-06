-- Prove2me | Definitions.Def_HMBinPacking_ILP
-- name    : HMBinPacking_ILP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:23.679686+00:00
-- url     : https://prove2.me/theorems/0493154d-2dda-4229-8d59-ae20a2ca8461
-- title:
--   The ILP of §2: $S$, $S_r$, $P_r$, $C_r$, $K$, $D=(d+1)d^d$
-- statement:
--   Fix an instance and write $s=(s_1,\dots,s_d)$, $a=(a_1,\dots,a_d)$. Residue indices $r$ range over $\{0,\dots,d-1\}^d$ (there are $d^d$ of them).
--
--   1. The **bin configurations** are $S:=\{x\in\mathbb Z^d_{\ge0}: s^\top x\le B\}$.
--   2. For each $r$, $S_r:=S\cap(r+d\mathbb Z^d)$ (configurations congruent to $r$ coordinatewise modulo $d$) and $P_r:=\mathrm{conv}(S_r)\subseteq\mathbb R^d$; $P_r=\emptyset$ when $S_r=\emptyset$.
--   3. The **cone** $C_r:=\{(0,0)\}\cup\{(np,n):p\in P_r,\ n\in\mathbb R_{>0}\}\subseteq\mathbb R^{d+1}$.
--   4. With $D:=(d+1)d^d$, the polytope $K\subseteq\mathbb R^D$ consists of the families $((z_r,n_r))_r$, $z_r\in\mathbb R^d$, $n_r\in\mathbb R$, with, for every $r$ and $1\le i\le d$,
--   $$
--   \sum_r z_r=a,\qquad \sum_r n_r=b,\qquad 0\le n_r\le b,\qquad 0\le z_{r,i}\le a_i,\qquad (z_r,n_r)\in C_r .
--   $$
--   5. An **integral point** of $K$ is a point of $K$ all of whose coordinates $z_{r,i}$, $n_r$ are integers; the ILP asks whether $K\cap\mathbb Z^D\neq\emptyset$.
--   6. The flat coordinates of $\mathbb R^D$: coordinate $(j,r)$ is $z_{r,j}$ for $j<d$ and $n_r$ for $j=d$, with residues and blocks numbered by explicit bijections.
--
--   Lemmas 1 and 4 show that the instance is feasible exactly when $K$ has an integral point; Lemma 8 separates over $K$.
--
--   **Formalization Note** A residue is a map `Fin d → Fin d`; all $d^d$ residues are kept, including those with $S_r=\emptyset$ (where $C_r=\{(0,0)\}$). A point of $K$ is a family over residues of pairs in $\mathbb R^d\times\mathbb R$ (`KSet`); `castPoint` casts an integer family, so an integral point is genuinely integral. `unflatten` reads a vector of $\mathbb R^D$ in block coordinates through the computable bijections `finFunctionFinEquiv` (residues) and `finProdFinEquiv` (blocks), and `KFlat` is $K$ in these coordinates.
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, §2, p.3 (S, P, S_r, P_r, C_r, D, K, count and cone constraints, K ∩ Z^D)

import Mathlib
import Definitions.Def_HMBinPacking_Instance
import Definitions.Def_HMBinPacking_Casts

namespace HMBinPacking

/-- **The bin configurations `S`.**
Koana, Kumabe, arXiv:2609.16923v2, §2, p.3: "Define the set S of bin configurations and its convex
hull P by S := {x ∈ Z^d_≥0 : s⊤x ≤ B}, P := conv(S)."

**Formalization Note.** `Z^d` is `Fin d → ℤ` with `d = I.d`; nonnegativity is coordinatewise. -/
def S (I : Instance) : Set (Fin I.d → ℤ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, (I.s i : ℤ) * x i ≤ I.B}

/-- **The residue class `S_r` of bin configurations.**
Koana, Kumabe, arXiv:2609.16923v2, §2, p.3: "For every r, let S_r consist of the bin configurations
congruent to r coordinatewise modulo d, and let P_r be the convex hull of S_r:
S_r := S ∩ (r + dZ^d), P_r := conv(S_r)." and "All residue indices r range over {0, . . . , d − 1}^d."

**Formalization Note.** A residue `r ∈ {0, …, d − 1}^d` is a map `Fin d → Fin d`; there are exactly
`d^d` of them, including those with `S_r = ∅`. The modulus is the number `d` of item sizes. -/
def Sr (I : Instance) (r : Fin I.d → Fin I.d) : Set (Fin I.d → ℤ) :=
  S I ∩ {x | ∃ y : Fin I.d → ℤ, x = (fun i => ((r i : ℕ) : ℤ)) + (I.d : ℤ) • y}

/-- **The polytope `P_r = conv(S_r)`.**
Koana, Kumabe, arXiv:2609.16923v2, §2, p.3: "P_r := conv(S_r)".

**Formalization Note.** The convex hull is taken in `ℝ^d = Fin d → ℝ` of the cast of `S_r`. It is
empty when `S_r` is. -/
def Pr (I : Instance) (r : Fin I.d → Fin I.d) : Set (Fin I.d → ℝ) :=
  convexHull ℝ (zCast '' Sr I r)

/-- **The cone `C_r`.**
Koana, Kumabe, arXiv:2609.16923v2, §2, p.3: "For every r, define the rational polyhedral cone
C_r ⊆ R^{d+1} by C_r := {(0, 0)} ∪ {(np, n) : p ∈ P_r, n ∈ R_>0}."

**Formalization Note.** `R^{d+1}` is `(Fin d → ℝ) × ℝ`, the pair `(z_r, n_r)`. When `P_r = ∅` the
cone is `{(0, 0)}`. -/
def Cr (I : Instance) (r : Fin I.d → Fin I.d) : Set ((Fin I.d → ℝ) × ℝ) :=
  {(0, 0)} ∪ {q | ∃ p ∈ Pr I r, ∃ n : ℝ, 0 < n ∧ q = (n • p, n)}

/-- **The polytope `K`.**
Koana, Kumabe, arXiv:2609.16923v2, §2, p.3: "Let K ⊆ R^D be the rational polytope defined by the
following constraints, imposed for every r and 1 ≤ i ≤ d: ∑_r z_r = a, ∑_r n_r = b, 0 ≤ n_r ≤ b,
0 ≤ z_{r,i} ≤ a_i, (z_r, n_r) ∈ C_r."

**Formalization Note.** A point of `K` is a family `w`, indexed by the `d^d` residues
`r : Fin d → Fin d`, of pairs `w r = (z_r, n_r) ∈ ℝ^d × ℝ`; this is `R^D` with `D = (d + 1)d^d`
(see `unflatten` for the flat coordinates). -/
def KSet (I : Instance) : Set ((Fin I.d → Fin I.d) → (Fin I.d → ℝ) × ℝ) :=
  {w | (∑ r, (w r).1 = fun i => (I.a i : ℝ)) ∧ ∑ r, (w r).2 = (I.b : ℝ) ∧
    (∀ r, 0 ≤ (w r).2 ∧ (w r).2 ≤ (I.b : ℝ)) ∧
    (∀ r i, 0 ≤ (w r).1 i ∧ (w r).1 i ≤ (I.a i : ℝ)) ∧
    ∀ r, w r ∈ Cr I r}

/-- **The real point of an integer family `((z_r, n_r))_r`.**
Koana, Kumabe, arXiv:2609.16923v2, §2, p.3: "Our ILP asks whether K ∩ Z^D is nonempty."

**Formalization Note.** An integral point of `K` is `castPoint I z ∈ KSet I` for an integer family
`z r = (z_r, n_r) ∈ ℤ^d × ℤ`; it is a genuine integer point, not a point of the relaxation. -/
def castPoint (I : Instance) (z : (Fin I.d → Fin I.d) → (Fin I.d → ℤ) × ℤ) :
    (Fin I.d → Fin I.d) → (Fin I.d → ℝ) × ℝ :=
  fun r => (zCast (z r).1, ((z r).2 : ℝ))

/-- **The number of ILP variables `D = (d + 1)d^d`.**
Koana, Kumabe, arXiv:2609.16923v2, §2, p.3: "Let D := (d + 1)d^d."

**Formalization Note.** `d = I.d`. -/
def D (I : Instance) : ℕ :=
  (I.d + 1) * I.d ^ I.d

/-- **The block coordinates of a flat vector in `R^D`.**
Koana, Kumabe, arXiv:2609.16923v2, §2, p.3: "Let K ⊆ R^D".

Flat coordinate `finProdFinEquiv (j, finFunctionFinEquiv r)` is `z_{r,j}` for `j < d` and `n_r` for
`j = d`.

**Formalization Note.** The residues are numbered by the explicit bijection
`finFunctionFinEquiv : (Fin d → Fin d) ≃ Fin (d^d)` (base-`d` digits) and the blocks by
`finProdFinEquiv : Fin (d + 1) × Fin (d^d) ≃ Fin ((d + 1)d^d)`. Both are computable, so a machine can
read and write flat vectors. `unflatten` is a linear bijection. -/
def unflatten (I : Instance) (y : Fin (D I) → ℝ) : (Fin I.d → Fin I.d) → (Fin I.d → ℝ) × ℝ :=
  fun r => (fun i => y (finProdFinEquiv (Fin.castSucc i, finFunctionFinEquiv r)),
    y (finProdFinEquiv (Fin.last I.d, finFunctionFinEquiv r)))

/-- **`K` in the flat coordinates of `R^D`.**
Koana, Kumabe, arXiv:2609.16923v2, §2, p.3 ("K ⊆ R^D") and Lemma 8, p.5.

**Formalization Note.** `KFlat I` is the preimage of `KSet I` under the bijection `unflatten I`. -/
def KFlat (I : Instance) : Set (Fin (D I) → ℝ) :=
  {y | unflatten I y ∈ KSet I}

end HMBinPacking


