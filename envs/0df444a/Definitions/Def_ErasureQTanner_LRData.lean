-- Prove2me | Definitions.Def_ErasureQTanner_LRData
-- name    : ErasureQTanner_LRData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:01.580001+00:00
-- url     : https://prove2.me/theorems/107336f6-f43b-409e-9fc0-eeb4b16e29f8
-- title:
--   The quadripartite Cayley square complex
-- statement:
--   The complex is defined with a finite group $G$ and two symmetric generating sets $A,B\subset G$ with $|A|=|B|=\Delta$. Its vertices are four copies $V_{00},V_{10},V_{11},V_{01}$ of $G$. Its **squares** are the quadruples
--   $$\{(g,00),(ag,10),(agb,11),(gb,01)\},\qquad g\in G,\ a\in A,\ b\in B,$$
--   so there are $N=|G|\Delta^2$ of them, and they index the qubits. The **local view** of a vertex is the set of squares containing it, identified with $A\times B$, with the same labels $(a,b)$ in the four views of a square: $(h,00)$ sees $(h,a,b)$, $(h,10)$ sees $(a^{-1}h,a,b)$, $(h,01)$ sees $(hb^{-1},a,b)$, and $(h,11)$ sees $(a^{-1}hb^{-1},a,b)$. This item also defines the Ramanujan condition on $\mathrm{Cay}(A,G)$, $\mathrm{Cay}(G,B)$.
--
--   **Formalization Note** $A,B$ are labelled by injections from `Fin Δ`, so that one local code on `Fin Δ` serves every member of a family. They may coincide. `enum` numbers the group for the machine layout and adds no condition. The paper defers "Ramanujan" to [LZ23], whose setting is non-bipartite, so $-\Delta$ is excluded as an eigenvalue. `QAlgorithms.qtPhi` is not reused: it has two codes, `Finset` coordinates and the labels 01, 10 swapped.
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), §4, pp.5–7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_TensorCode

set_option autoImplicit false

namespace ErasureQTanner

/-- The quadripartite Cayley square complex: Pfister, Sprumont, Zémor, STOC 2027 submission (manuscript sha256
bf7a84a5…), §4, p.5: "It is defined with a group `G` and two symmetric sets of generators `A ⊂ G` and `B ⊂ G`. Symmetry
here means that `A = A⁻¹` and `B = B⁻¹`. For simplicity we take `∆ := |A| = |B|`."

**Formalization Note.** `A`, `B` are labelled by injections `Fin Δ ↪ G`, so that one local code on `Fin Δ` serves every
member of a family (p.4: "fixed once and used with a sequence of square complexes"). The paper allows `A = B`, so they
need not be disjoint. No total no-conjugacy condition: the quadripartite version does not use it. `enum` numbers the
group, which fixes the machine's input layout; it adds no condition, since every finite group has one. -/
structure LRData (Δ : ℕ) where
  G : Type
  [group : Group G]
  [fintype : Fintype G]
  [decEq : DecidableEq G]
  enum : G ≃ Fin (Fintype.card G)
  A : Fin Δ ↪ G
  B : Fin Δ ↪ G
  A_symm : ∀ a, ∃ a', A a' = (A a)⁻¹
  B_symm : ∀ b, ∃ b', B b' = (B b)⁻¹
  A_gen : Subgroup.closure (Set.range A) = ⊤
  B_gen : Subgroup.closure (Set.range B) = ⊤

attribute [instance] LRData.group LRData.fintype LRData.decEq

/-- The four copies of `G` (p.5: "`V00, V10, V11, V01`"). -/
inductive VType where
  | v00 | v10 | v11 | v01
  deriving DecidableEq

namespace LRData

variable {Δ : ℕ} (Γ : LRData Δ)

/-- A square `{(g, 00), (ag, 10), (agb, 11), (gb, 01)}` (p.5) is the triple `(g, a, b)`. -/
abbrev Square := Γ.G × Fin Δ × Fin Δ

/-- `N = |G|∆²` (p.6). -/
def N : ℕ := Fintype.card Γ.G * Δ ^ 2

/-- The vertex of type `t` of the square `(g, a, b)` is `(vert t (g, a, b), t)` (p.5). -/
def vert (t : VType) (s : Γ.Square) : Γ.G :=
  match t with
  | .v00 => s.1
  | .v10 => Γ.A s.2.1 * s.1
  | .v11 => Γ.A s.2.1 * s.1 * Γ.B s.2.2
  | .v01 => s.1 * Γ.B s.2.2

/-- The local view `Q(v) ≃ A × B` of the vertex `(h, t)`: the square carrying the local index `(a, b)` (p.6, Figure 2: a
square is "indexed similarly, by `(a, b)` here, in the four local views"). -/
def view (t : VType) (h : Γ.G) (p : Fin Δ × Fin Δ) : Γ.Square :=
  match t with
  | .v00 => (h, p.1, p.2)
  | .v10 => ((Γ.A p.1)⁻¹ * h, p.1, p.2)
  | .v11 => ((Γ.A p.1)⁻¹ * h * (Γ.B p.2)⁻¹, p.1, p.2)
  | .v01 => (h * (Γ.B p.2)⁻¹, p.1, p.2)

/-- The word `w` on the local view of `(h, t)`, extended by zero to all squares. -/
def push (t : VType) (h : Γ.G) (w : Fin Δ × Fin Δ → ZMod 2) : Γ.Square → ZMod 2 :=
  fun s => if Γ.vert t s = h then w s.2 else 0

/-- The restriction of a vector on the squares to the local view of `(h, t)`. -/
def localVec {α : Type*} (t : VType) (h : Γ.G) (e : Γ.Square → α) : Fin Δ × Fin Δ → α :=
  fun p => e (Γ.view t h p)

/-- "The group `G` and the generating sets `A` and `B` … so that associated Cayley graphs `Cay(A, G)` and `Cay(G, B)` are
Ramanujan graphs" (§4, p.7).

**Formalization Note.** The paper says "Ramanujan" and defers to [LZ23], whose setting is non-bipartite, so `−∆` is
excluded as an eigenvalue of both graphs. `QAlgorithms.IsRamanujanAdj` includes Hermitian and connected, automatic for a
symmetric generating set. -/
def IsRamanujan : Prop :=
  let ML := QAlgorithms.leftCayleyAdj (Finset.univ.map Γ.A)
  let MR := QAlgorithms.rightCayleyAdj (Finset.univ.map Γ.B)
  QAlgorithms.IsRamanujanAdj ML Δ ∧ QAlgorithms.IsRamanujanAdj MR Δ ∧
    (∀ k, QAlgorithms.ascEigenvalues ML k ≠ -(Δ : ℝ)) ∧
    ∀ k, QAlgorithms.ascEigenvalues MR k ≠ -(Δ : ℝ)

end LRData

end ErasureQTanner


