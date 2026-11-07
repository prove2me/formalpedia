-- Prove2me | Definitions.Def_DynEdgeOrient_NodeQuantities
-- name    : DynEdgeOrient_NodeQuantities
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:41.983185+00:00
-- url     : https://prove2.me/theorems/e9f82622-336e-48a5-8b83-4cadb82f7e3e
-- title:
--   The sets $X,Y,A,B$, the quantities $\Gamma(I)$, $\psi(I)$, $\Psi(\ell)$ and the descendants $\mathrm{desc}(S,I)$
-- statement:
--   Let $(S,I=[i,k))$ be an internal node $(\ell,q)$, $\ell\ge1$, of the hierarchy of Lemma 4.9, with children $(S_1,[i,j))$ and $(S_2,[j,k))$. Its times are $i-1=q2^\ell$, $j-1=(2q+1)2^{\ell-1}$ and $k-1=(q+1)2^\ell$. Define
--
--   $$
--   X(I)=S\setminus(S_1\cup S_2),\quad Y(I)=S_1\cap S_2,\quad A(I)=S_1\setminus Y(I),\quad B(I)=S_2\setminus Y(I),
--   $$
--
--   and let $|E(A(I),B(I))|$ be the number of edges crossing $A(I)$ and $B(I)$, counted in $G_{i-1}$. Then
--
--   1. $\Gamma(I)=\alpha|X(I)|+\alpha|Y(I)|+|E(A(I),B(I))|$ (Definition 5.1);
--   2. $\psi(I)=2\alpha|S|-|E_{G_{i-1}}(S)|-|E_{G_{k-1}}(S)|$, defined for every node (p.16);
--   3. $\Psi(\ell)=\sum_{q<2^{K-\ell}}\psi(\ell,q)$, the sum of $\psi$ over level $\ell$;
--   4. $\mathrm{desc}(S,I)$ is the set of internal nodes $(\ell',q')$ below $(\ell,q)$, including $(\ell,q)$: $1\le\ell'\le\ell$ and $q2^{\ell-\ell'}\le q'<(q+1)2^{\ell-\ell'}$.
--
--   $\Gamma$ bounds the work at a node, and $\psi$ is the potential that bounds the hierarchy's total size.
--
--   **Formalization Note** The quantities are functions of $(\ell,q)$ and are meaningful only for $\ell\ge1$; every statement assumes it. $\Gamma$ is in $\mathbb N$ and $\psi,\Psi$ in $\mathbb Z$. Counting $|E(A,B)|$ in $G_{i-1}$ is harmless: by Remark 4.10 it is constant throughout $I$.
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), Definition 4.8, p.13; Remark 4.10, p.14; ψ and Ψ, p.16; Definition 5.1, p.18; desc(S, I) in Lemma 5.2, p.19

import Mathlib
import Definitions.Def_DynEdgeOrient_Hierarchy

namespace DynEdgeOrient

/-!
# The sets X, Y, A, B, the quantities Γ and ψ, and the internal descendants

S. Hiken, N. Wein, *Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n
Barrier*, STOC 2027 submission (manuscript sha256 626b4eee…), Definition 4.8, p.13; Remark 4.10,
p.14; ψ and Ψ, p.16; Definition 5.1, p.18; `desc(S, I)` in Lemma 5.2, p.19.

**Formalization Note.**
* All quantities are attached to an **internal** node `(ℓ, q)` of the hierarchy `hierS`
  (`1 ≤ ℓ`), whose children are `S₁ = hierS (ℓ−1) (2q)` and `S₂ = hierS (ℓ−1) (2q+1)`. At
  `ℓ = 0` the definitions return unused values; every statement assumes `1 ≤ ℓ`.
* Times of the node: `i − 1 = winLo ℓ q = q·2^ℓ`, `j − 1 = winMid ℓ q = (2q+1)·2^(ℓ−1)` (the end of
  the first child's window, the start of the second's), `k − 1 = winHi ℓ q = (q+1)·2^ℓ`.
* `X = S ∖ (S₁ ∪ S₂)`, `Y = S₁ ∩ S₂`, `A = S₁ ∖ Y`, `B = S₂ ∖ Y` (Definition 4.8).
* `crossAB` is `|E(A, B)|` evaluated at time `i − 1`. Remark 4.10 notes that it is constant on the
  window for a special hierarchy.
* `Gamma ℓ q = α|X| + α|Y| + |E(A, B)|` in `ℕ` (Definition 5.1).
* `psi ℓ q = 2α|S| − |E_{G_{i−1}}(S)| − |E_{G_{k−1}}(S)|` in `ℤ`, for every node (leaves too), and
  `Psi K ℓ = Σ_{q < 2^(K−ℓ)} psi ℓ q` is its sum over level `ℓ` (p.16).
* `desc ℓ q` is the set of internal descendants of `(ℓ, q)`, itself included: the pairs
  `(ℓ', q')` with `1 ≤ ℓ' ≤ ℓ` and `q·2^(ℓ−ℓ') ≤ q' < (q+1)·2^(ℓ−ℓ')`.
-/

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V]

/-- `j − 1`: the time where the first child's window ends and the second's begins. -/
def winMid (ℓ q : ℕ) : ℕ := (2 * q + 1) * 2 ^ (ℓ - 1)

/-- The first child `S₁` of the internal node `(ℓ, q)`. -/
def child₁ (ends : E → V × V) (G : ℕ → Finset E) (α ℓ q : ℕ) : Finset V :=
  hierS ends G α (ℓ - 1) (2 * q)

/-- The second child `S₂` of the internal node `(ℓ, q)`. -/
def child₂ (ends : E → V × V) (G : ℕ → Finset E) (α ℓ q : ℕ) : Finset V :=
  hierS ends G α (ℓ - 1) (2 * q + 1)

/-- `X(I) = S ∖ (S₁ ∪ S₂)` (Definition 4.8). -/
def Xset (ends : E → V × V) (G : ℕ → Finset E) (α ℓ q : ℕ) : Finset V :=
  hierS ends G α ℓ q \ (child₁ ends G α ℓ q ∪ child₂ ends G α ℓ q)

/-- `Y(I) = S₁ ∩ S₂` (Definition 4.8). -/
def Yset (ends : E → V × V) (G : ℕ → Finset E) (α ℓ q : ℕ) : Finset V :=
  child₁ ends G α ℓ q ∩ child₂ ends G α ℓ q

/-- `A(I) = S₁ ∖ Y(I)` (Definition 4.8). -/
def Aset (ends : E → V × V) (G : ℕ → Finset E) (α ℓ q : ℕ) : Finset V :=
  child₁ ends G α ℓ q \ Yset ends G α ℓ q

/-- `B(I) = S₂ ∖ Y(I)` (Definition 4.8). -/
def Bset (ends : E → V × V) (G : ℕ → Finset E) (α ℓ q : ℕ) : Finset V :=
  child₂ ends G α ℓ q \ Yset ends G α ℓ q

/-- `|E(A(I), B(I))|`, the edges crossing `A(I)` and `B(I)`, counted in `G_{i−1}`. -/
def crossAB (ends : E → V × V) (G : ℕ → Finset E) (α ℓ q : ℕ) : ℕ :=
  (edgesBetween ends (G (winLo ℓ q)) (Aset ends G α ℓ q) (Bset ends G α ℓ q)).card

/-- `Γ(I) = α|X(I)| + α|Y(I)| + |E(A(I), B(I))|` (Definition 5.1). -/
def Gamma (ends : E → V × V) (G : ℕ → Finset E) (α ℓ q : ℕ) : ℕ :=
  α * (Xset ends G α ℓ q).card + α * (Yset ends G α ℓ q).card + crossAB ends G α ℓ q

/-- `ψ(I) = 2α|S| − |E_{G_{i−1}}(S)| − |E_{G_{k−1}}(S)|`, in `ℤ` (p.16). -/
def psi (ends : E → V × V) (G : ℕ → Finset E) (α ℓ q : ℕ) : ℤ :=
  2 * (α : ℤ) * (hierS ends G α ℓ q).card
    - (edgesIn ends (G (winLo ℓ q)) (hierS ends G α ℓ q)).card
    - (edgesIn ends (G (winHi ℓ q)) (hierS ends G α ℓ q)).card

/-- `Ψ(ℓ) = Σ_{(S,I) ∈ V^ℓ(H)} ψ(I)` for the hierarchy with `2^K` leaves (p.16). -/
def Psi (ends : E → V × V) (G : ℕ → Finset E) (α K ℓ : ℕ) : ℤ :=
  ∑ q ∈ Finset.range (2 ^ (K - ℓ)), psi ends G α ℓ q

/-- `desc(S, I)`: the internal nodes `(ℓ', q')` below the node `(ℓ, q)`, including `(ℓ, q)`
itself (Lemma 5.2). -/
def desc (ℓ q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 ℓ ×ˢ Finset.range ((q + 1) * 2 ^ ℓ)).filter
    (fun p => q * 2 ^ (ℓ - p.1) ≤ p.2 ∧ p.2 < (q + 1) * 2 ^ (ℓ - p.1))

end DynEdgeOrient


