-- Prove2me | Definitions.Def_WalledBrauer_SuperSchurWeyl_Weights
-- name    : WalledBrauer_SuperSchurWeyl_Weights
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:23.898873+00:00
-- url     : https://prove2.me/theorems/7f959c2b-a063-4eca-86eb-d65138d420fa
-- title:
--   The weight wt(_iσ_j) of (7.5), the maps Φ^{m,n}_{r+s} and Ψ^{m,n}_{r,s} of (7.11)–(7.12), and flip_{r,s} on diagrams (2.1)
-- statement:
--   This file defines the diagrammatic side of mixed Schur–Weyl duality. Let $I = \{1, \dots, m+n\}$ with parities $|i| = 0$ for $i \le m$ and $|i| = 1$ otherwise, and $N = r + s$.
--
--   **Diagrams.** A diagram on $N$ strands is a pairing of the $2N$ vertices $\{\text{top}, \text{bottom}\} \times \{1, \dots, N\}$ into $N$ strands. A permutation $\sigma \in \Sigma_N$ gives the *permutation diagram* in which the top vertex $a$ is joined to the bottom vertex $\sigma(a)$ (p. 6). The *walled Brauer diagrams* (p. 5) are the diagrams in which each vertical strand joins two vertices on the same side of a wall placed between positions $r$ and $r+1$, and each horizontal strand joins two vertices on opposite sides; they are the published `WalledBrauer.Blocks.WalledDiagram r s`, and they form a basis of the walled Brauer algebra $B_{r,s}(\delta)$.
--
--   **The weight (7.5).** For $\mathbf i, \mathbf j \in I^N$, colour the bottom vertices of $\sigma$ by $i_1, \dots, i_N$ and the top vertices by $j_1, \dots, j_N$. If some strand has ends of different colours, $\mathrm{wt}({}_{\mathbf i}\sigma_{\mathbf j}) = 0$. Otherwise each strand has a colour and
--
--   $$
--   \mathrm{wt}({}_{\mathbf i}\sigma_{\mathbf j}) = \prod_{c} (-1)^{|c|} \cdot \prod_{h} (-1)^{|h|},
--   $$
--
--   where the first product is over the pairs of distinct strands that cross, a crossing of strands of colours $k, l$ having parity $|k||l|$, and the second over the horizontal strands with both endpoints on the bottom edge, a strand of colour $k$ having parity $|k|$. Crossings are those of a reduced drawing: reading the boundary of the rectangle cyclically (bottom vertices left to right, then top vertices right to left), two strands cross exactly when their endpoints interleave. By Lemma 7.2 of the paper, the weight depends only on the pairing, so this choice of drawing is harmless.
--
--   **The maps.** A diagram $\sigma$ acts on the right on tensor space by $u_{\mathbf i} \cdot \sigma = \sum_{\mathbf j} \mathrm{wt}({}_{\mathbf i}\sigma_{\mathbf j})\, u_{\mathbf j}$ ((7.6), (7.7)); its matrix has entry $\mathrm{wt}({}_{\mathbf i}\sigma_{\mathbf j})$ in row $\mathbf j$, column $\mathbf i$. Extending linearly gives
--
--   $$
--   \Phi^{m,n}_{N} : \mathbb C\Sigma_N \to \operatorname{End}(V^{\otimes N}), \qquad \Psi^{m,n}_{r,s} : B_{r,s}(\delta) \to \operatorname{End}(V^{\otimes r} \otimes W^{\otimes s}),
--   $$
--
--   the linear maps underlying the algebra homomorphisms (7.11), (7.12). Here $\delta = m - n$.
--
--   **flip on diagrams (2.1).** $\mathrm{flip}_{r,s}(\sigma)$ is the walled Brauer diagram obtained from the permutation diagram of $\sigma \in \Sigma_{r+s}$ by adding a wall between the $r$-th and $(r+1)$-th vertices and flipping the part to the right of the wall in its horizontal axis: at every position $a > r$ the top and bottom vertices are exchanged.
--
--   **Formalization Note** Vertices are `Sum.inl a` (top vertex `a`) and `Sum.inr a` (bottom vertex `a`), 0-based, as in the published `WalledBrauer.Blocks.Node`; a diagram is a fixed-point-free involution of the vertices. Crossings are counted by interleaving of boundary positions (bottom `a ↦ a`, top `a ↦ 2N - 1 - a`), which absorbs Lemma 7.2. $\mathbb C\Sigma_N$ and $B_{r,s}(\delta)$ enter as vector spaces with their diagram bases, i.e. as `Equiv.Perm (Fin N) →₀ ℂ` and `WalledDiagram r s →₀ ℂ`; `Phi` and `Psi` are `Finsupp.linearCombination` of the diagram matrices `PhiDiag`, `PsiDiag`. `flipDiag` is conjugation of the permutation pairing by the vertex involution exchanging top and bottom at positions `≥ r`, packaged with `WalledDiagram.ofPairing`, whose fallback is never reached. `delta m n = (m : ℂ) - n`.
-- source:
--   Brundan and Stroppel, Gradings on walled Brauer algebras and Khovanov's arc algebra, arXiv:1107.0999v1, pp. 5–6 (walled Brauer diagrams, permutation diagrams, (2.1)), p. 50 ((7.5)), p. 51 ((7.6), (7.7)), p. 53 ((7.11), (7.12))

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_Algebra
import Definitions.Def_WalledBrauer_SuperSchurWeyl_TensorSpace

namespace WalledBrauer.SuperSchurWeyl

open WalledBrauer.Blocks

/-! Diagrams and the weight (7.5) (Brundan–Stroppel, arXiv:1107.0999v1, pp. 5–6, 50–53).
A diagram on `N` strands is a pairing of the nodes `Node N = Fin N ⊕ Fin N`, given as a
fixed-point-free involution `f` (as in `WalledBrauer.Blocks`): `Sum.inl a` is the top vertex
`a`, `Sum.inr a` the bottom vertex `a` (0-based, left to right). -/

/-- The colour of a node of the coloured diagram `_i σ _j` (p. 50): the bottom vertex `a` is
coloured `i a`, the top vertex `a` is coloured `j a`. -/
def nodeColour {m n N : ℕ} (i j : Fin N → Fin (m + n)) : Node N → Fin (m + n)
  | Sum.inl a => j a
  | Sum.inr a => i a

/-- The position of a node on the boundary of the rectangle, read cyclically: bottom vertex
`a ↦ a`, top vertex `a ↦ 2N - 1 - a`. Two strands cross (in a reduced drawing) iff their
endpoints interleave in this order. -/
def bpos {N : ℕ} : Node N → ℕ
  | Sum.inl a => 2 * N - 1 - a.val
  | Sum.inr a => a.val

/-- Whether a node is on the bottom edge. -/
def isBottom {N : ℕ} : Node N → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

/-- `_i f _j` is consistently coloured: both ends of every strand have the same colour. -/
def Consistent {m n N : ℕ} (f : Node N → Node N) (i j : Fin N → Fin (m + n)) : Prop :=
  ∀ x, nodeColour i j (f x) = nodeColour i j x

instance {m n N : ℕ} (f : Node N → Node N) (i j : Fin N → Fin (m + n)) :
    Decidable (Consistent f i j) :=
  inferInstanceAs (Decidable (∀ x, nodeColour i j (f x) = nodeColour i j x))

/-- The exponent of the weight (7.5): the sum of `|c||c'|` over the unordered pairs of distinct
strands that cross (strands `{x, f x}` and `{y, f y}`, each listed by its endpoint with the
smaller boundary position, cross iff `bpos x < bpos y < bpos (f x) < bpos (f y)`), plus the
sum of `|c|` over the horizontal strands with both endpoints on the bottom edge; `c, c'` are
the colours of the strands. -/
def wtExp (m : ℕ) {n N : ℕ} (f : Node N → Node N) (i j : Fin N → Fin (m + n)) : ℕ :=
  (∑ x : Node N, ∑ y : Node N,
      if bpos x < bpos (f x) ∧ bpos y < bpos (f y) ∧
          bpos x < bpos y ∧ bpos y < bpos (f x) ∧ bpos (f x) < bpos (f y)
      then par m (nodeColour i j x) * par m (nodeColour i j y) else 0) +
    ∑ x : Node N,
      if isBottom x ∧ isBottom (f x) ∧ bpos x < bpos (f x) then par m (nodeColour i j x) else 0

/-- The weight `wt(_i σ _j)` of (7.5): `(-1)^{wtExp}` if `_i σ _j` is consistently coloured,
`0` otherwise. -/
def wt (m n : ℕ) {N : ℕ} (f : Node N → Node N) (i j : Fin N → Fin (m + n)) : ℂ :=
  if Consistent f i j then sgn (wtExp m f i j) else 0

/-- The matrix of a diagram acting on the right on tensor space ((7.6), (7.7)):
`u_i · σ = ∑_j wt(_i σ _j) u_j`; column `i` (input), row `j` (output). -/
def diagMat (m n : ℕ) {N : ℕ} (f : Node N → Node N) : Op m n N :=
  Matrix.of fun j i => wt m n f i j

/-- The permutation diagram of `σ ∈ Σ_N` (p. 6): the top vertex `a` is joined to the bottom
vertex `σ a`. -/
def permPairing {N : ℕ} (σ : Equiv.Perm (Fin N)) : Node N → Node N
  | Sum.inl a => Sum.inr (σ a)
  | Sum.inr b => Sum.inl (σ.symm b)

/-- `Φ^{m,n}_N(σ)` for a permutation `σ` ((7.6), (7.11)): the operator `v_i ↦ v_i · σ` on
`V^{⊗ N}`. -/
def PhiDiag (m n : ℕ) {N : ℕ} (σ : Equiv.Perm (Fin N)) : Op m n N :=
  diagMat m n (permPairing σ)

/-- `Φ^{m,n}_N : ℂΣ_N → End(V^{⊗ N})` (7.11), the linear extension of `PhiDiag`; the group
algebra `ℂΣ_N` is, as a vector space, the space of finitely supported functions on `Σ_N`. -/
noncomputable def Phi (m n N : ℕ) : (Equiv.Perm (Fin N) →₀ ℂ) →ₗ[ℂ] Op m n N :=
  Finsupp.linearCombination ℂ (PhiDiag m n)

/-- `Ψ^{m,n}_{r,s}(σ)` for a walled Brauer diagram `σ` ((7.7), (7.12)): the operator
`v_{i^L} ⊗ w_{i^R} ↦ (v_{i^L} ⊗ w_{i^R}) · σ` on `V^{⊗ r} ⊗ W^{⊗ s}`. -/
def PsiDiag (m n : ℕ) {r s : ℕ} (σ : WalledDiagram r s) : Op m n (r + s) :=
  diagMat m n σ.1

/-- `Ψ^{m,n}_{r,s} : B_{r,s}(δ) → End(V^{⊗ r} ⊗ W^{⊗ s})` (7.12), the linear extension of
`PsiDiag`; the walled Brauer diagrams are a basis of `B_{r,s}(δ)` (p. 5), so `B_{r,s}(δ)` is,
as a vector space, the space of finitely supported functions on walled diagrams. -/
noncomputable def Psi (m n r s : ℕ) : (WalledDiagram r s →₀ ℂ) →ₗ[ℂ] Op m n (r + s) :=
  Finsupp.linearCombination ℂ (PsiDiag m n)

/-- `δ = m - n` (p. 48), as a complex number. -/
def delta (m n : ℕ) : ℂ := (m : ℂ) - n

/-- The involution of the nodes exchanging top and bottom at every position `a ≥ r`. -/
def flipNode {N : ℕ} (r : ℕ) : Node N → Node N
  | Sum.inl a => if a.val < r then Sum.inl a else Sum.inr a
  | Sum.inr a => if a.val < r then Sum.inr a else Sum.inl a

/-- `flip_{r,s} : Σ_{r+s} → {walled Brauer diagrams}` (2.1): add a wall between the vertices
`r` and `r + 1` and flip the part of the permutation diagram to the right of the wall in its
horizontal axis. On pairings it is conjugation by `flipNode r`. (The result is always a walled
Brauer diagram; the fallback of `WalledDiagram.ofPairing` is never used.) -/
noncomputable def flipDiag (r s : ℕ) (σ : Equiv.Perm (Fin (r + s))) : WalledDiagram r s :=
  WalledDiagram.ofPairing (flipNode r ∘ permPairing σ ∘ flipNode r)

end WalledBrauer.SuperSchurWeyl


