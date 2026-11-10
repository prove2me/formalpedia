-- Prove2me | Definitions.Def_EntrywiseLogGH_Dichotomy_DistanceRegular
-- name    : EntrywiseLogGH_Dichotomy_DistanceRegular
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:29:29.068285+00:00
-- url     : https://prove2.me/theorems/31aaa12c-5281-4725-9280-7897123ec0d9
-- title:
--   Distance-regular graphs, intersection numbers, Hamming, Shrikhande and Doob graphs (Definitions 2.7–2.10)
-- statement:
--   Let $\Gamma$ be a connected simple graph of diameter $D\ge1$ with path distance $d_\Gamma$. $\Gamma$ is **distance-regular** if for all $0\le i,j,k\le D$ the number
--   $$p^k_{ij}=|\{z\mid d_\Gamma(x,z)=i,\ d_\Gamma(z,y)=j\}|$$
--   is the same for all vertices $x,y$ with $d_\Gamma(x,y)=k$; these are its **intersection numbers**. Two graphs have the same intersection numbers when they have the same diameter $D$ and equal $p^k_{ij}$ for all $0\le i,j,k\le D$. The **Hamming graph** $H(D,Q)$ has vertex set $[Q]^D$, tuples adjacent when they differ in exactly one position. The **Shrikhande graph** has vertex set $\mathbb Z_4^2$, $x\sim y$ iff $y-x\in\{(1,0),(3,0),(0,1),(0,3),(1,1),(3,3)\}$. The **Doob graph** $I(p,q)$ is the Cartesian product of $p\ge1$ Shrikhande graphs and $q\ge0$ copies of $K_4$. By Egawa's theorem these are the only distance-regular graphs with the intersection numbers of a Hamming graph.
--
--   **Formalization Note.** Mathlib `SimpleGraph`, `SimpleGraph.dist`, `SimpleGraph.diam`; counts are `Nat.card` of subtypes. `hammingGraph D Q` is on `Fin D → Fin Q` with `hammingDist f g = 1`; `piBox G` is the Cartesian product of copies of `G` indexed by a type; `doobGraph p q := (piBox shrikhandeGraph).boxProd (piBox ⊤)` on `(Fin p → ZMod 4 × ZMod 4) × (Fin q → Fin 4)`; `IsDoobGraph G := ∃ p q, 1 ≤ p ∧ Nonempty (G ≃g doobGraph p q)`. Graphs given by a symmetric relation use `SimpleGraph.fromRel`, which only adds `x ≠ y`.
-- source:
--   Cai, Tang, Entrywise Logarithmic Matrix Algebra and Dichotomy of Planar Graph Homomorphisms, arXiv:2610.00828 (held copy, sha256 4fd56ea7…a7cd), p. 18, §2.4, Definitions 2.7–2.10

import Mathlib

set_option autoImplicit false

/-!
# Distance-regular graphs, Hamming, Shrikhande and Doob graphs (§2.4)

Cai, Tang, *Entrywise Logarithmic Matrix Algebra and Dichotomy of Planar Graph Homomorphisms*,
arXiv:2610.00828 (held copy, sha256 4fd56ea7…a7cd), §2.4, p. 18, Definitions 2.7–2.10.

"Definition 2.7. Let Γ be a connected simple graph of diameter D ≥ 1, and let d_Γ(x, y) denote the
length of a shortest path between vertices x, y. The graph is distance-regular if, for every
integer 0 ≤ i, j, k ≤ D and every pair of vertices x, y with d_Γ(x, y) = k, the number
p^k_ij := |{z ∈ V(Γ) | d_Γ(x, z) = i and d_Γ(z, y) = j}| is independent of x and y. These counts
p^k_ij are called intersection numbers.
Definition 2.8. For integers D ≥ 1 and Q ≥ 2, the Hamming graph H(D, Q) has vertex set [Q]^D; two
tuples are adjacent exactly when they differ in one position.
Definition 2.9. The Shrikhande graph has vertex set Z_4^2 and edges joining x, y ∈ Z_4^2 exactly
when y − x ∈ D, where D = {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}.
Definition 2.10. A Doob graph I(p, q) is a Cartesian product of p ≥ 1 Shrikhande graphs and q ≥ 0
copies of the complete graph K4."

Conventions. Graphs are Mathlib `SimpleGraph`s on finite vertex types; `SimpleGraph.dist` and
`SimpleGraph.diam` are the shortest-path distance and the diameter. "Γ has the same intersection
numbers as H" (§2.4) is `SameIntersectionNumbers Γ H`: equal diameters `D`, and
`p^k_ij(Γ) = p^k_ij(H)` for all `0 ≤ i, j, k ≤ D`. Graphs given by a symmetric relation are built
with `SimpleGraph.fromRel`, which only adds `x ≠ y` and symmetrises (no change for these
relations). The Cartesian product of copies of a graph is `piBox`: two tuples are adjacent when
they differ in exactly one coordinate, and are adjacent there.
-/

namespace EntrywiseLogGH.Dichotomy

/-- The count `|{z | d(x, z) = i ∧ d(z, y) = j}|` of Definition 2.7. -/
noncomputable def interCount {V : Type*} (G : SimpleGraph V) (x y : V) (i j : ℕ) : ℕ :=
  Nat.card {z : V // G.dist x z = i ∧ G.dist z y = j}

/-- **Distance-regular** graph (Definition 2.7, p. 18): connected, of diameter `D ≥ 1`, and for
all `0 ≤ i, j, k ≤ D` the count `p^k_ij(x, y)` is the same for all `x, y` at distance `k`. -/
def IsDistanceRegular {V : Type*} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ 1 ≤ G.diam ∧
    ∀ i j k : ℕ, i ≤ G.diam → j ≤ G.diam → k ≤ G.diam →
      ∀ x y x' y' : V, G.dist x y = k → G.dist x' y' = k →
        interCount G x y i j = interCount G x' y' i j

/-- `G` has the **same intersection numbers** as `H` (§2.4, p. 18): the same diameter `D`, and
`p^k_ij(G) = p^k_ij(H)` for all `0 ≤ i, j, k ≤ D`. -/
def SameIntersectionNumbers {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  G.diam = H.diam ∧
    ∀ i j k : ℕ, i ≤ G.diam → j ≤ G.diam → k ≤ G.diam →
      ∀ (x y : V) (x' y' : W), G.dist x y = k → H.dist x' y' = k →
        interCount G x y i j = interCount H x' y' i j

/-- The **Hamming graph** `H(D, Q)` (Definition 2.8, p. 18) on `[Q]^D = Fin D → Fin Q`: tuples
differing in exactly one position are adjacent. -/
def hammingGraph (D Q : ℕ) : SimpleGraph (Fin D → Fin Q) :=
  SimpleGraph.fromRel fun f g => hammingDist f g = 1

/-- The difference set `D` of the Shrikhande graph (Definition 2.9). -/
def shrikhandeDiffs : Finset (ZMod 4 × ZMod 4) :=
  {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}

/-- The **Shrikhande graph** (Definition 2.9, p. 18) on `ℤ_4²`: `x ~ y` iff `y − x ∈ D`. -/
def shrikhandeGraph : SimpleGraph (ZMod 4 × ZMod 4) :=
  SimpleGraph.fromRel fun x y => y - x ∈ shrikhandeDiffs

/-- The Cartesian product of `|ι|` copies of `G`: tuples differing in exactly one coordinate, in
which they are adjacent in `G`. -/
def piBox {ι V : Type*} (G : SimpleGraph V) : SimpleGraph (ι → V) :=
  SimpleGraph.fromRel fun f g => ∃ i, G.Adj (f i) (g i) ∧ ∀ j, j ≠ i → f j = g j

/-- The **Doob graph** `I(p, q)` (Definition 2.10, p. 18): the Cartesian product of `p`
Shrikhande graphs and `q` copies of `K₄`. -/
def doobGraph (p q : ℕ) : SimpleGraph ((Fin p → ZMod 4 × ZMod 4) × (Fin q → Fin 4)) :=
  (piBox shrikhandeGraph).boxProd (piBox (⊤ : SimpleGraph (Fin 4)))

/-- `G` is **isomorphic to a Doob graph** `I(p, q)` with `p ≥ 1`, `q ≥ 0`. -/
def IsDoobGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ p q : ℕ, 1 ≤ p ∧ Nonempty (G ≃g doobGraph p q)

end EntrywiseLogGH.Dichotomy


