-- Prove2me | Definitions.Def_PctDistortion_blowupG
-- name    : PctDistortion_blowupG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:41:54.93313+00:00
-- url     : https://prove2.me/theorems/6be5bcd3-507c-4a69-bfd0-5c1ed97221c1
-- title:
--   The composed digraph $G=C[P,H,\dots,H]$ of §4 and its blocks
-- statement:
--   Fix a digraph $H=(V_H,E_H)$ and integers $s,r$, and let $\ell=sr+1$ and $C=\vec C^{\,r}_\ell$. Let $P=(c_0\to c^*)$ be the directed path on two candidates. The digraph
--   $$G=C[P,H,H,\dots,H]$$
--   is the composition in which node $0$ of $C$ is replaced by $P$ and every node $i\ne 0$ by a disjoint copy of $H$. Its $i$-th **block** $V_i$ is the copy substituted for node $i$, so $V_0=\{c_0,c^*\}$ and $|V_i|=|V_H|$ for $i\ne 0$.
--
--   For a mixed strategy $p$ on the nodes of $G$, $\pi(p)_i=\sum_{u\in V_i}p_u$ is its **projection** onto $C$ and $\phi(p)_{i,u}=p_u/\pi(p)_i$ its **conditional distribution** on $V_i$; $G[V_i]$ is the subdigraph induced on block $i$.
--
--   **Formalization Note** The node type is $\{0,1\}\sqcup(\{i\in\mathbb Z_\ell: i\ne 0\}\times V_H)$ with $c_0=0$, $c^*=1$ in the first summand; the block map sends a node to its node of $C$.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), §4.1, p.13; §4.2, p.13

import Mathlib
import Definitions.Def_PctDistortion_cyclePower

set_option autoImplicit false

namespace PctDistortion

/-- The node type of the composed digraph `G = C[P, H, …, H]` of §4.1 with `ℓ = s r + 1`:
block `0` is `Fin 2` (the path `P` on `c₀ = 0`, `c* = 1`), and block `i ≠ 0` is a copy
`{i} × V_H` of the node set of `H`. -/
abbrev BlowupVertex (VH : Type) (s r : ℕ) : Type :=
  Fin 2 ⊕ ({i : Fin (s * r + 1) // i ≠ 0} × VH)

/-- The block `i ∈ {0, …, ℓ − 1}` (a node of `C`) containing a node of `G`: `V_i` is the
`i`-th block. -/
def block {VH : Type} {s r : ℕ} : BlowupVertex VH s r → Fin (s * r + 1)
  | Sum.inl _ => 0
  | Sum.inr x => x.1.1

/-- The candidate `c₀`, the source of the path `P = (c₀ → c*)` in block `0`. -/
def c0 {VH : Type} {s r : ℕ} : BlowupVertex VH s r := Sum.inl 0

/-- The candidate `c*`, the head of the path `P = (c₀ → c*)` in block `0`. -/
def cStar {VH : Type} {s r : ℕ} : BlowupVertex VH s r := Sum.inl 1

/-- The **composed digraph `G = C[P, H, H, …, H]`** of §4.1, with `C = C⃗^r_ℓ` and
`ℓ = s r + 1`: node `0` of `C` is replaced by the path `P = (c₀ → c*)` and every node
`i ≠ 0` by a disjoint copy of `H`. Its arcs are the arc `(c₀, c*)`, the arcs of each copy of
`H` inside its block, and every `(u, v)` with `u ∈ V_i`, `v ∈ V_j` and `(i, j)` an arc of
`C`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §4.1, p.13: "Let P = (c0 → c∗) denote the directed path of length 2 on nodes/candidates c0,
c∗, and let G = C[P, H, H, . . . , H] be the composition in which node 0 of C is replaced with P,
and all nodes i ≠ 0 are replaced with disjoint copies of H." The composition is that of §2.2, p.9.

**Formalization Note.** The node type is `Fin 2 ⊕ ({i : Fin ℓ // i ≠ 0} × V_H)`
(`BlowupVertex`), and `block` is the block map. -/
def blowupG {VH : Type} (H : Digraph VH) (s r : ℕ) : Digraph (BlowupVertex VH s r) where
  Adj x y := (cyclePower (s * r + 1) r).Adj (block x) (block y) ∨ (x = c0 ∧ y = cStar) ∨
    ∃ (i : {i : Fin (s * r + 1) // i ≠ 0}) (u u' : VH),
      x = Sum.inr (i, u) ∧ y = Sum.inr (i, u') ∧ H.Adj u u'

/-- The **block projection** `π(p)_i = Σ_{u ∈ V_i} p_u` of a mixed strategy `p` on the nodes of
`G` onto the nodes of `C`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §4.2, p.13: "For a mixed strategy p ∈ ∆VG, we write π(p) ∈ ∆{0,...,ℓ−1} for the projection onto
C, i.e., π(p)_i = Σ_{u∈Vi} p_u." -/
def blockMass {VH : Type} [Fintype VH] {s r : ℕ} (p : BlowupVertex VH s r → ℝ)
    (i : Fin (s * r + 1)) : ℝ :=
  ∑ x, if block x = i then p x else 0

/-- The **conditional distribution** `ϕ(p)_i` on block `V_i`: `ϕ(p)_{i,u} = p_u / π(p)_i`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §4.2, p.13: "choose the specific node u ∈ Vi with conditional probabilities
ϕ(p)_{i,u} = p_u/π(p)_i. Let ϕ(p)_i = (ϕ(p)_{i,u})_{u∈Vi} be the induced distribution on Vi." -/
noncomputable def condDist {VH : Type} [Fintype VH] {s r : ℕ} (p : BlowupVertex VH s r → ℝ)
    (i : Fin (s * r + 1)) : {x : BlowupVertex VH s r // block x = i} → ℝ :=
  fun x => p x.1 / blockMass p i

/-- The **induced subdigraph `G[V_i]`** of a digraph on the nodes of `G` on block `V_i`. -/
def blockSub {VH : Type} {s r : ℕ} (G : Digraph (BlowupVertex VH s r)) (i : Fin (s * r + 1)) :
    Digraph {x : BlowupVertex VH s r // block x = i} where
  Adj x y := G.Adj x.1 y.1

end PctDistortion


