-- Prove2me | Definitions.Def_MultiLayerCake_LongKnives_Model
-- name    : MultiLayerCake_LongKnives_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:59.298967+00:00
-- url     : https://prove2.me/theorems/0fbfcd27-6d47-4337-8b3b-cf8dc0b6536d
-- title:
--   §2, §3.1–3.2, pp. 3–7 — multi-layered cake: pieces, multi-divisions, feasibility, long knives, choice functions, closed preferences; chessboard complex and the encoding A(x)
-- statement:
--   **The multi-layered cake (§2, pp. 3–4).** A *cake* is the unit interval $[0,1]$. A *piece* is a union of finitely many pairwise disjoint closed subintervals of $[0,1]$, and a *contiguous piece* is a single closed subinterval $[a,b]\subseteq[0,1]$ (zero length allowed). An $m$-layered cake consists of $m$ copies of $[0,1]$, the layers. A *layered piece* is a family $\mathcal L=(L_\ell)_{\ell\in[m]}$ of pieces, one per layer.
--
--   A *multi-division* into layered pieces $\mathcal A=(\mathcal A_j)_{j}$, indexed by a finite set of bundle names, is a family of layered pieces that covers every layer, $\bigcup_j \mathcal A_{j,\ell}=[0,1]$ for each $\ell$, and whose entries have disjoint interiors in each layer: two distinct entries meet in a layer in at most finitely many points. It is
--
--   1. *contiguous* if every $\mathcal A_{j,\ell}$ is a contiguous piece;
--   2. *feasible* if every $\mathcal A_j$ is *non-overlapping*: for distinct layers $\ell\neq\ell'$ the set $\mathcal A_{j,\ell}\cap\mathcal A_{j,\ell'}$ is empty or finite;
--   3. obtained with $q-1$ *long knives* (for $q$ bundles) if there are positions $0=t_0\le t_1\le\dots\le t_q=1$, the same in every layer, such that every $\mathcal A_{j,\ell}$ is one of the intervals $[t_k,t_{k+1}]$.
--
--   The pseudo-metric between layered pieces is
--   $$d(\mathcal L,\mathcal L')=\mu(\mathcal L\triangle\mathcal L')=\sum_{\ell\in[m]}\lambda\big(L_\ell\triangle L'_\ell\big),$$
--   with $\lambda$ the Lebesgue measure; a sequence of multi-divisions converges to $\mathcal A'$ if each of its entries converges to the corresponding entry of $\mathcal A'$ for $d$.
--
--   A *choice function* $c$ assigns to every multi-division $\mathcal A$ the set $c(\mathcal A)$ of preferred layered pieces; it is invariant under permuting the entries of $\mathcal A$, and it prefers at least one entry of $\mathcal A$. An agent has *closed preferences* if for every sequence $(\mathcal A^{(t)})_{t}$ of multi-divisions converging to a multi-division $\mathcal A^{(\infty)}$, $\mathcal A^{(t)}_j\in c(\mathcal A^{(t)})$ for all $t$ implies $\mathcal A^{(\infty)}_j\in c(\mathcal A^{(\infty)})$.
--
--   **The chessboard complex and the encoding (§3.1–3.2, pp. 6–7).** Let $G$ be a finite additive group of order $q$. The chessboard complex $\Delta_{2q-1,q}$ has ground set $[2q-1]\times G$ (rows $\times$ columns, the columns named by the elements of $G$), and its simplices are the "rook sets": no two distinct vertices share a row or a column. Its geometric realization $\|\Delta_{2q-1,q}\|$ is the set of points $x\in\mathbb R^{[2q-1]\times G}$ with $x\ge0$, $\sum_v x_v=1$, whose support is a rook set. The group acts by $g\cdot(r,j)=(r,g+j)$ on the chessboard and by $g'\cdot e_g=e_{g+g'}$ on the standard simplex $\Delta^G\subseteq\mathbb R^G$, both extended linearly.
--
--   A *procedure* $\mathfrak P$ assigns to every nonempty rook set $\sigma$ a $(q-1)$-dimensional simplex $\{(r_j,j):j\in G\}$ of $\Delta_{2q-1,q}$ (pairwise distinct rows $r_j$) containing $\sigma$, equivariantly: the simplex assigned to $g\cdot\sigma$ is $g$ applied to the simplex assigned to $\sigma$. Given $\mathfrak P$ and an injective map $h:[m]\to G$, a point $x\in\|\Delta_{2q-1,q}\|$ with support $\sigma$ and rows $r_j$ assigned by $\mathfrak P$ encodes the multi-division $\mathcal A(x)$: in every layer the pieces are laid out left to right by increasing row, the piece of column $j$ has length $x_{(r_j,j)}$, and in layer $\ell$ that piece belongs to the bundle $j+h(\ell)$. So $\mathcal A_g(x)$ has, in layer $\ell$, the interval of column $j=g-h(\ell)$:
--   $$\mathcal A_g(x)_\ell=\Big[\sum_{j':\,r_{j'}<r_j}x_{(r_{j'},j')},\ \sum_{j':\,r_{j'}\le r_j}x_{(r_{j'},j')}\Big].$$
--
--   These definitions are the model of Theorem 1 and the configuration space of its proof.
--
--   **Formalization Note.** A layered piece is `Fin m → Set ℝ`, a multi-division `ι → Fin m → Set ℝ` for a finite index type `ι` (`Fin q` in Theorem 1, the group `G` in the encoding). "Disjoint interiors" and "non-overlapping" are both encoded as finiteness of the intersection; for finite unions of closed intervals these coincide with the page's notions. The choice function's property "prefers at least one entry" (`exists_preferred`) is a reading of "returns the set of preferred layered pieces"; without it an agent preferring nothing would make Theorem 1 false. Both laws of a choice function are asked on multi-divisions only. `pdist` takes `toReal` of each layer's measure, harmless because pieces lie in $[0,1]$. The bijection $\eta:[q]\to G$ of the page is the identity: columns are indexed by $G$ directly. The procedure's laws are asked on nonempty rook sets only, which are exactly the supports of points of $\|\Delta_{2q-1,q}\|$ (the empty set is fixed by the whole group, so equivariance there would contradict injectivity). The encoding uses left endpoints computed from the rows instead of the permutation $\rho$ of the page; the two descriptions give the same intervals.
-- source:
--   Igarashi, Meunier, Envy-Free Division of Multi-Layered Cakes, arXiv:2106.02262v4, pp. 3–7, §2, §3.1, §3.2

import Mathlib

namespace MultiLayerCake.LongKnives

open MeasureTheory

/-- p. 3: a piece of cake — a union of finitely many pairwise disjoint closed subintervals of
`[0, 1]` (the empty union and degenerate intervals `[a, a]` are allowed). -/
def IsPiece (P : Set ℝ) : Prop :=
  ∃ (N : ℕ) (a b : Fin N → ℝ), (∀ k, 0 ≤ a k ∧ a k ≤ b k ∧ b k ≤ 1) ∧
    Pairwise (fun k k' => Disjoint (Set.Icc (a k) (b k)) (Set.Icc (a k') (b k'))) ∧
    P = ⋃ k, Set.Icc (a k) (b k)

/-- p. 3: a contiguous piece — a closed subinterval `[a, b]` of `[0, 1]` (zero length allowed). -/
def IsContiguousPiece (P : Set ℝ) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ P = Set.Icc a b

variable {m : ℕ} {ι : Type*} [Fintype ι]

/-- p. 4: `A` is a (complete) multi-division of the `m`-layered cake into the layered pieces
`A j`, `j : ι` (a layered piece is `Fin m → Set ℝ`, its `ℓ`-th entry being the piece in layer `ℓ`):
every entry is a piece, every layer `[0, 1]` is covered, and two distinct layered pieces have
disjoint interiors in each layer, i.e. meet there in finitely many points. -/
def IsMultiDivision (A : ι → Fin m → Set ℝ) : Prop :=
  (∀ j ℓ, IsPiece (A j ℓ)) ∧ (∀ ℓ, (⋃ j, A j ℓ) = Set.Icc 0 1) ∧
    ∀ ℓ, Pairwise fun j j' => (A j ℓ ∩ A j' ℓ).Finite

/-- p. 4: contiguous — every layered piece is contiguous in every layer. -/
def IsContiguous (A : ι → Fin m → Set ℝ) : Prop :=
  ∀ j ℓ, IsContiguousPiece (A j ℓ)

/-- pp. 3–4: feasible — every layered piece is non-overlapping: its pieces in two distinct layers
are empty or meet in finitely many points. -/
def IsFeasible (A : ι → Fin m → Set ℝ) : Prop :=
  ∀ j, Pairwise fun ℓ ℓ' => (A j ℓ ∩ A j ℓ').Finite

/-- p. 5: the multi-division into `q` layered pieces is obtained with `q − 1` long knives: there are
cut positions `0 = t₀ ≤ t₁ ≤ … ≤ t_q = 1`, the same in every layer, and every piece of every layer
is one of the `q` intervals `[t_k, t_{k+1}]`. -/
def ByLongKnives {q : ℕ} (A : Fin q → Fin m → Set ℝ) : Prop :=
  ∃ t : Fin (q + 1) → ℝ, Monotone t ∧ t 0 = 0 ∧ t (Fin.last q) = 1 ∧
    ∀ j ℓ, ∃ k : Fin q, A j ℓ = Set.Icc (t k.castSucc) (t k.succ)

/-- p. 4: the pseudo-metric `d(L, L′) = μ(L △ L′)` between layered pieces: the Lebesgue measure of
the symmetric difference in each layer, summed over the layers ("the length of a layered piece is
the sum of the lengths of its pieces in each layer", p. 3). Pieces lie in `[0, 1]`, so every
measure involved is finite and `toReal` loses nothing. -/
noncomputable def pdist (L L' : Fin m → Set ℝ) : ℝ :=
  ∑ ℓ, (volume (symmDiff (L ℓ) (L' ℓ))).toReal

/-- p. 4: a sequence of multi-divisions converges to `A'` if each of its layered pieces converges
to the corresponding layered piece of `A'` for the pseudo-metric `pdist`. -/
def Converges (A : ℕ → ι → Fin m → Set ℝ) (A' : ι → Fin m → Set ℝ) : Prop :=
  ∀ j, Filter.Tendsto (fun t => pdist (A t j) (A' j)) Filter.atTop (nhds 0)

/-- p. 4: a choice function `c` returns, for a multi-division, the set of preferred layered pieces.
It returns the same set over all permutations of the entries of the multi-division, and (reading of
"returns the set of preferred layered pieces") it prefers at least one entry of the
multi-division. -/
structure IsChoiceFunction (c : (ι → Fin m → Set ℝ) → Set (Fin m → Set ℝ)) : Prop where
  perm_invariant : ∀ A, IsMultiDivision A → ∀ ρ : Equiv.Perm ι, c (A ∘ ρ) = c A
  exists_preferred : ∀ A, IsMultiDivision A → ∃ j, A j ∈ c A

/-- p. 4: closed preferences — for every sequence `(A⁽ᵗ⁾)` of multi-divisions converging to a
multi-division `A⁽∞⁾`, if `A⁽ᵗ⁾_j ∈ c(A⁽ᵗ⁾)` for all `t` then `A⁽∞⁾_j ∈ c(A⁽∞⁾)`. -/
def ClosedPreferences (c : (ι → Fin m → Set ℝ) → Set (Fin m → Set ℝ)) : Prop :=
  ∀ (A : ℕ → ι → Fin m → Set ℝ) (A' : ι → Fin m → Set ℝ) (j : ι),
    (∀ t, IsMultiDivision (A t)) → IsMultiDivision A' → Converges A A' →
    (∀ t, A t j ∈ c (A t)) → A' j ∈ c A'

/-! ### §3.1–3.2: the chessboard complex and the encoding `A(x)` -/

variable (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- p. 6: the ground set `[2q − 1] × [q]` of the chessboard complex `Δ_{2q−1,q}`, with the `q`
columns indexed by the group `G` of order `q` itself (the bijection `η : [q] → G` is the identity). -/
abbrev V := Fin (2 * Fintype.card G - 1) × G

/-- p. 6: the geometric realization `‖Δ_{2q−1,q}‖` in `ℝ^{[2q−1]×G}`: the points of the standard
simplex on the ground set whose support is a simplex of the chessboard complex, i.e. contains no two
distinct vertices in the same row or in the same column. -/
def chessboard : Set (V G → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1 ∧
    ∀ v v', x v ≠ 0 → x v' ≠ 0 → v ≠ v' → v.1 ≠ v'.1 ∧ v.2 ≠ v'.2}

variable {G}

/-- p. 6: the action `φ_g(r, j) = (r, g + j)` of `G` on `Δ_{2q−1,q}`, extended linearly to
`ℝ^{[2q−1]×G}`: it sends the vertex `e_{(r,j)}` to `e_{(r,g+j)}`. -/
def actCB (g : G) (x : V G → ℝ) : V G → ℝ := fun v => x (v.1, v.2 - g)

/-- p. 6: the action `φ_{g′}(e_g) = e_{g+g′}` of `G` on the standard simplex `Δ^G ⊆ ℝ^G`,
extended linearly. -/
def actSimplex (g : G) (z : G → ℝ) : G → ℝ := fun h => z (h - g)

/-- `σ` is a simplex of the chessboard complex: no two distinct vertices share a row or a column. -/
def IsRookSet (σ : Finset (V G)) : Prop :=
  ∀ v ∈ σ, ∀ v' ∈ σ, v ≠ v' → v.1 ≠ v'.1 ∧ v.2 ≠ v'.2

/-- p. 7: the procedure `𝔓`. To every support `σ` (a nonempty simplex of `Δ_{2q−1,q}`) it assigns a
`(q − 1)`-dimensional simplex `{(P σ j, j) : j ∈ G}` of `Δ_{2q−1,q}` containing `σ` (one row per
column, the rows pairwise distinct), equivariantly: the simplex assigned to the shifted support
`g · σ` is the image by `φ_g` of the simplex assigned to `σ`. -/
structure Procedure (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] where
  P : Finset (V G) → G → Fin (2 * Fintype.card G - 1)
  injective : ∀ σ : Finset (V G), σ.Nonempty → IsRookSet σ → Function.Injective (P σ)
  contains : ∀ σ : Finset (V G), σ.Nonempty → IsRookSet σ → ∀ v ∈ σ, P σ v.2 = v.1
  equivariant : ∀ σ : Finset (V G), σ.Nonempty → IsRookSet σ → ∀ g : G,
    P (σ.image fun v => (v.1, v.2 + g)) = fun j => P σ (j - g)

/-- p. 7: the multi-division `A(x)` encoded by a point `x` of `‖Δ_{2q−1,q}‖`, for the procedure `𝔓`
and an injective map `h : [m] → G`. With `σ` the support of `x` and `r_j = 𝔓 σ j`, the pieces of
every layer are ordered by increasing row, the piece of column `j` has length `x_{(r_j, j)}`, and in
layer `ℓ` it gets the bundle-name `j + h(ℓ)`. So the layered piece `A_g(x)` has, in layer `ℓ`, the
interval of column `j = g − h(ℓ)`, whose left end is the total length of the columns of smaller
row. -/
noncomputable def encode (𝔓 : Procedure G) (h : Fin m → G) (x : V G → ℝ) :
    G → Fin m → Set ℝ := by
  classical
  exact fun g ℓ =>
    let σ : Finset (V G) := Finset.univ.filter (fun v => x v ≠ 0)
    let r : G → Fin (2 * Fintype.card G - 1) := 𝔓.P σ
    let len : G → ℝ := fun c => x (r c, c)
    let c := g - h ℓ
    Set.Icc (∑ c' ∈ Finset.univ.filter (fun c' => r c' < r c), len c')
      (∑ c' ∈ Finset.univ.filter (fun c' => r c' ≤ r c), len c')

end MultiLayerCake.LongKnives


