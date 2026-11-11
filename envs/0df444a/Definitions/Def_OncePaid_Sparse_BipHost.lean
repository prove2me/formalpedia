-- Prove2me | Definitions.Def_OncePaid_Sparse_BipHost
-- name    : OncePaid_Sparse_BipHost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T13:46:47.837289+00:00
-- url     : https://prove2.me/theorems/85cdb81e-76a0-48cd-9607-e57ee6350e53
-- title:
--   Bipartite hosts: perfect matchings, perfect-matching and edge-cover objectives, probes $p^M$, coupled prices, coefficient totals, $X_{U,V}(M)$, $B_H(\tau)$, regularity and singular values
-- statement:
--   A **bipartite host** $H=(V_L\cup V_R,E)$ is given by finite sets of rows $V_L$ and columns $V_R$ and an adjacency relation; $E$ is the set of pairs $ij$ with $i\in V_L$, $j\in V_R$ adjacent (so $H$ is simple). Prices are vectors $c\in\mathbb R^{E}$.
--
--   1. A **perfect matching** is a bijection $M:V_L\to V_R$ with $i\,M(i)\in E$ for all $i$; $\mathcal M(H)$ is the set of them.
--   2. The objective $f_H$ is either **minimum-weight perfect matching** $\min_{M\in\mathcal M(H)}\sum_i c_{iM(i)}$ or **full minimum-weight edge cover** $\mathrm{EC}_H(c)=\min\{\sum_{e\in F}c_e: F\subseteq E\text{ meets every vertex}\}$ (covers of any size), each $+\infty$ when the family is empty.
--   3. Tests: the all-$t$ table; the **probe** $p^M$ (price 3 on $M$, 4 elsewhere); the **subset test** for $A$ (price 4 on the matching edges in $A$ and off $M$, 3 on the rest of $M$); the **coupled prices** (3.2) $c_{ij}=3+\tfrac12(v_i-v_{M^{-1}(j)})$ for $v\in\{-1,1\}^{V_L}$.
--   4. For an affine form $P$ in the edge prices: row and column totals $r_i(P)=\sum_{j:ij\in E}\alpha_{ij}(P)$, $q_j(P)=\sum_{i:ij\in E}\alpha_{ij}(P)$; supports $U(P)=\{i:r_i(P)>0\}$, $V(P)=\{j:q_j(P)>0\}$; off-matching mass $O=\sum_{e\notin M}\alpha_e(P)$; matching deficit $\sum_{e\in M}(1-\alpha_e(P))_+$; and $\|D_M(P)\|_1=\sum_i|r_i(P)-q_{M(i)}(P)|$.
--   5. $X_{U,V}(M)=|M(U)\,\triangle\,V|$ for $U\subseteq V_L$, $V\subseteq V_R$, and the **cut count** (3.5), with $n=|V_L|$:
--
--   $$
--   B_H(\tau)=\max_{\substack{U\subseteq V_L,\ V\subseteq V_R\\ |U|=|V|\in[\lceil n/3\rceil,\lfloor 2n/3\rfloor]}}\big|\{M\in\mathcal M(H): X_{U,V}(M)\le\tau\}\big|.
--   $$
--
--   6. $H$ is **$d$-regular** if every vertex has exactly $d$ neighbours; $e(U,V)$ is the number of edges from $U$ to $V$ and $e(U^c,V^c)$ the number of edges between the complements.
--   7. With $B$ the biadjacency matrix ($(Bf)_i=\sum_{j:ij\in E}f_j$), **all nontrivial singular values are at most $\sigma$** means $\|Bf\|_2\le\sigma\|f\|_2$ for every $f\in\mathbb R^{V_R}$ with $\sum_j f_j=0$.
--
--   These are the graph-side objects of §3.2–3.3 and §4: the probes are the test inputs of the circuit lower bound, and $B_H$ is the combinatorial quantity that converts it into a count of addition gates.
--
--   **Formalization Note** Rows and columns are arbitrary finite types; an edge is a structure (row, column, adjacency proof). Objective values lie in `WithTop ℝ`. $B_H$ is the paper's quantity for $n>3$; for other $n$ the Lean maximum is over the (possibly empty) same range, with $\max\emptyset=0$. The singular-value condition is stated squared ($\|Bf\|^2\le\sigma^2\|f\|^2$); for a $d$-regular bipartite host the all-ones vector is a top singular vector of $B$ with singular value $d$ and its orthogonal complement is invariant under $B^{\mathsf T}B$, so the condition says exactly that every singular value other than this trivial one is at most $\sigma$ (for $\sigma\ge0$).
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), pp. 12–14, §3.2–3.3, Eqs. (3.2), (3.5); p. 20, §4; p. 36, App. A.3 (PDF pp. 14–16, 22, 38)

import Mathlib
import Definitions.Def_OncePaid_Sparse_Parse

namespace OncePaid.Sparse

/-!
# Bipartite hosts, perfect matchings, the two objectives, probes and cut counts

Chao, Li, Gao, Wang, *Once-Paid Subsequences and the Cost of Min-Plus Approximation*,
STOC 2027 submission (manuscript sha256 9dc21472…), pp. 12–14 §3.2–3.3 (Eqs. (3.2), (3.5)),
p. 20 §4 (biadjacency matrix), p. 36 App. A.3.

A bipartite host is given by finite vertex types `L = V_L` (rows) and `R = V_R` (columns) and an
adjacency relation `adj : L → R → Prop`; the graph is simple by construction (an edge is a pair
`(i, j)` with `adj i j`). The theorems assume `|L| = |R| = n`.

* `Edge adj`: the edge set `E(H)`; prices are vectors `c : Edge adj → ℝ`.
* Perfect matchings are bijections `M : L ≃ R` with `adj i (M i)` for every `i`; `M(H)` is the
  finset `perfectMatchings adj`.
* `objValue adj obj c` (`f_H`): minimum-weight perfect matching, or full minimum-weight edge cover
  (a set of edges meeting every vertex, of any size), with `min ∅ = +∞ = ⊤` in `WithTop ℝ`.
* Tests: `probe M = p^M` (3 on `M`, 4 elsewhere); `subsetTest M A` (4 on the matching edges in
  `A` and off `M`, 3 on the other matching edges); `coupledPrices M v` (Eq. (3.2):
  `c_ij = 3 + (v_i − v_{M⁻¹(j)})/2`); `uniformPrices t` (the all-`t` table).
* For an affine form `P` over the edge prices: row and column coefficient totals `r_i(P)`,
  `q_j(P)`, their supports `U(P)`, `V(P)`, the off-matching mass `Σ_{e ∉ M} α_e(P)`, the matching
  deficit `Σ_{e ∈ M} (1 − α_e(P))₊`, and `‖D_M(P)‖₁ = Σ_i |r_i(P) − q_{M(i)}(P)|`.
* `crossCount M U V = X_{U,V}(M) = |M(U) △ V|` and the cut count `B_H(τ)` of (3.5): the maximum,
  over `U ⊆ V_L`, `V ⊆ V_R` with `|U| = |V| ∈ [⌈n/3⌉, ⌊2n/3⌋]`, of the number of perfect
  matchings with `X_{U,V}(M) ≤ τ` (the paper defines it for `n > 3`; for other `n` the Lean value
  is still the maximum over that, possibly empty, range, with `max ∅ = 0`).
* `IsBiregular adj d`: every vertex has exactly `d` neighbours; `edgesBetween adj U V = e(U, V)`,
  `edgesOutside adj U V = e(Uᶜ, Vᶜ)`.
* `NontrivialSingularValuesLe adj σ`: every `f : V_R → ℝ` with `Σ_j f_j = 0` has
  `‖B f‖₂ ≤ σ ‖f‖₂` (stated squared), `B` the biadjacency matrix (one row per left vertex, entry
  one exactly at the edges). For a `d`-regular bipartite host, `𝟙` is a top singular vector of `B`
  and `𝟙^⊥` is invariant under `BᵀB`, so this says that all singular values other than the trivial
  one `d` are at most `σ`.
-/

section Host

variable {L R : Type}

/-- An edge `ij` of the bipartite host: a row `i`, a column `j`, and `adj i j`. -/
structure Edge (adj : L → R → Prop) where
  /-- the left endpoint (row) -/
  left : L
  /-- the right endpoint (column) -/
  right : R
  /-- the two endpoints are adjacent -/
  isAdj : adj left right

theorem Edge.ext_iff' {adj : L → R → Prop} (e f : Edge adj) :
    e = f ↔ e.left = f.left ∧ e.right = f.right := by
  cases e; cases f; simp

instance Edge.finite [Finite L] [Finite R] (adj : L → R → Prop) : Finite (Edge adj) :=
  Finite.of_injective (fun e : Edge adj => (e.left, e.right)) (by
    intro e f h
    simp only [Prod.mk.injEq] at h
    exact (Edge.ext_iff' e f).2 h)

noncomputable instance Edge.fintype [Finite L] [Finite R] (adj : L → R → Prop) :
    Fintype (Edge adj) := Fintype.ofFinite _

noncomputable instance Edge.decEq (adj : L → R → Prop) : DecidableEq (Edge adj) :=
  Classical.decEq _

/-- `M : L ≃ R` is a perfect matching of the host: every pair `i, M(i)` is an edge. -/
def IsPerfectMatching (adj : L → R → Prop) (M : L ≃ R) : Prop :=
  ∀ i, adj i (M i)

/-- The set `M(H)` of perfect matchings, as bijections `V_L → V_R`. -/
noncomputable def perfectMatchings [Fintype L] [Fintype R] (adj : L → R → Prop) :
    Finset (L ≃ R) := by
  classical
  exact Finset.univ.filter (fun M => IsPerfectMatching adj M)

/-- The edge `e` belongs to the matching `M` (`e = i M(i)`). -/
def InMatching {adj : L → R → Prop} (M : L ≃ R) (e : Edge adj) : Prop :=
  e.right = M e.left

/-- An edge set meeting every vertex on both sides (a full edge cover; any size). -/
def IsEdgeCover {adj : L → R → Prop} (F : Finset (Edge adj)) : Prop :=
  (∀ i : L, ∃ e ∈ F, e.left = i) ∧ (∀ j : R, ∃ e ∈ F, e.right = j)

/-- The two graph objectives of §3.2. -/
inductive Objective where
  /-- minimum-weight perfect matching -/
  | perfectMatching
  /-- full minimum-weight edge cover -/
  | edgeCover

/-- Minimum-weight perfect matching value, `+∞` if `H` has no perfect matching. -/
noncomputable def matchingValue [Fintype L] [Fintype R] (adj : L → R → Prop)
    (c : Edge adj → ℝ) : WithTop ℝ := by
  classical
  exact (perfectMatchings adj).inf
    (fun M => ((∑ e : Edge adj, if InMatching M e then c e else 0 : ℝ) : WithTop ℝ))

/-- Full minimum-weight edge-cover value `EC_H(c)` (minimum over all edge covers, of any size),
`+∞` if there is none. -/
noncomputable def edgeCoverValue [Fintype L] [Fintype R] (adj : L → R → Prop)
    (c : Edge adj → ℝ) : WithTop ℝ := by
  classical
  exact ((Finset.univ : Finset (Finset (Edge adj))).filter (fun F => IsEdgeCover F)).inf
    (fun F => ((∑ e ∈ F, c e : ℝ) : WithTop ℝ))

/-- The objective `f_H`. -/
noncomputable def objValue [Fintype L] [Fintype R] (adj : L → R → Prop) :
    Objective → (Edge adj → ℝ) → WithTop ℝ
  | Objective.perfectMatching => matchingValue adj
  | Objective.edgeCover => edgeCoverValue adj

/-- The all-`t` table. -/
def uniformPrices (adj : L → R → Prop) (t : ℝ) : Edge adj → ℝ := fun _ => t

/-- The matching probe `p^M`: price 3 on the edges of `M`, 4 elsewhere. -/
noncomputable def probe {adj : L → R → Prop} (M : L ≃ R) : Edge adj → ℝ := by
  classical
  exact fun e => if InMatching M e then 3 else 4

/-- The subset test: price 4 on the matching edges in `A` and on every edge off `M`, price 3 on
the remaining edges of `M`. -/
noncomputable def subsetTest {adj : L → R → Prop} (M : L ≃ R) (A : Set (Edge adj)) :
    Edge adj → ℝ := by
  classical
  exact fun e => if InMatching M e ∧ e ∉ A then 3 else 4

/-- The coupled prices (3.2): `c_ij = 3 + (v_i − v_{M⁻¹(j)})/2`. -/
noncomputable def coupledPrices {adj : L → R → Prop} (M : L ≃ R) (v : L → ℝ) :
    Edge adj → ℝ :=
  fun e => 3 + (v e.left - v (M.symm e.right)) / 2

/-- `v ∈ {−1, 1}^{V_L}`. -/
def IsSignVector (v : L → ℝ) : Prop := ∀ i, v i = 1 ∨ v i = -1

/-- Soundness of an affine form at every coupled test (3.2) for the objective `obj`. -/
def SoundAtCoupled [Fintype L] [Fintype R] (adj : L → R → Prop) (obj : Objective)
    (M : L ≃ R) (F : AffineForm (Edge adj)) : Prop :=
  ∀ v : L → ℝ, IsSignVector v →
    objValue adj obj (coupledPrices M v) ≤ ((F.eval (coupledPrices M v) : ℝ) : WithTop ℝ)

/-- Row total `r_i(P) = Σ_{j : ij ∈ E} α_ij(P)`. -/
noncomputable def rowTotal [Fintype L] [Fintype R] {adj : L → R → Prop}
    (P : AffineForm (Edge adj)) (i : L) : ℝ := by
  classical
  exact ∑ e : Edge adj, if e.left = i then P.coef e else 0

/-- Column total `q_j(P) = Σ_{i : ij ∈ E} α_ij(P)`. -/
noncomputable def colTotal [Fintype L] [Fintype R] {adj : L → R → Prop}
    (P : AffineForm (Edge adj)) (j : R) : ℝ := by
  classical
  exact ∑ e : Edge adj, if e.right = j then P.coef e else 0

/-- Row support `U(P) = {i : r_i(P) > 0}`. -/
noncomputable def rowSupport [Fintype L] [Fintype R] {adj : L → R → Prop}
    (P : AffineForm (Edge adj)) : Finset L := by
  classical
  exact Finset.univ.filter (fun i => 0 < rowTotal P i)

/-- Column support `V(P) = {j : q_j(P) > 0}`. -/
noncomputable def colSupport [Fintype L] [Fintype R] {adj : L → R → Prop}
    (P : AffineForm (Edge adj)) : Finset R := by
  classical
  exact Finset.univ.filter (fun j => 0 < colTotal P j)

/-- Off-matching coefficient mass `O = Σ_{e ∉ M} α_e(P)`. -/
noncomputable def offMass [Fintype L] [Fintype R] {adj : L → R → Prop} (M : L ≃ R)
    (P : AffineForm (Edge adj)) : ℝ := by
  classical
  exact ∑ e : Edge adj, if InMatching M e then 0 else P.coef e

/-- Matching deficit `Σ_{e ∈ M} (1 − α_e(P))₊`. -/
noncomputable def matchDeficit [Fintype L] [Fintype R] {adj : L → R → Prop} (M : L ≃ R)
    (P : AffineForm (Edge adj)) : ℝ := by
  classical
  exact ∑ e : Edge adj, if InMatching M e then max (1 - P.coef e) 0 else 0

/-- `‖D_M(F)‖₁ = Σ_i |r_i(F) − q_{M(i)}(F)|`. -/
noncomputable def imbalance [Fintype L] [Fintype R] {adj : L → R → Prop} (M : L ≃ R)
    (F : AffineForm (Edge adj)) : ℝ :=
  ∑ i : L, |rowTotal F i - colTotal F (M i)|

/-- `X_{U,V}(M) = |M(U) △ V|`. -/
noncomputable def crossCount (M : L ≃ R) (U : Finset L) (V : Finset R) : ℕ := by
  classical
  exact (symmDiff (U.map M.toEmbedding) V).card

/-- The cut count `B_H(τ)` of (3.5): the maximum over `U ⊆ V_L`, `V ⊆ V_R` with
`|U| = |V| ∈ [⌈n/3⌉, ⌊2n/3⌋]` (`n = |V_L|`) of `|{M ∈ M(H) : X_{U,V}(M) ≤ τ}|`. -/
noncomputable def cutCount [Fintype L] [Fintype R] (adj : L → R → Prop) (τ : ℝ) : ℕ := by
  classical
  exact (((Finset.univ : Finset (Finset L)) ×ˢ (Finset.univ : Finset (Finset R))).filter
      (fun UV => UV.1.card = UV.2.card ∧ (Fintype.card L + 2) / 3 ≤ UV.1.card ∧
        UV.1.card ≤ 2 * Fintype.card L / 3)).sup
    (fun UV => ((perfectMatchings adj).filter
      (fun M => ((crossCount M UV.1 UV.2 : ℕ) : ℝ) ≤ τ)).card)

/-- Every vertex on either side has exactly `d` neighbours. -/
def IsBiregular [Fintype L] [Fintype R] (adj : L → R → Prop) (d : ℕ) : Prop :=
  (∀ i : L, Nat.card {j : R // adj i j} = d) ∧ (∀ j : R, Nat.card {i : L // adj i j} = d)

/-- `e(U, V)`: the number of edges with left endpoint in `U` and right endpoint in `V`. -/
noncomputable def edgesBetween [Fintype L] [Fintype R] (adj : L → R → Prop)
    (U : Finset L) (V : Finset R) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : Edge adj => e.left ∈ U ∧ e.right ∈ V)).card

/-- `e(Uᶜ, Vᶜ)`: the number of edges with left endpoint outside `U` and right endpoint outside
`V`. -/
noncomputable def edgesOutside [Fintype L] [Fintype R] (adj : L → R → Prop)
    (U : Finset L) (V : Finset R) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : Edge adj => e.left ∉ U ∧ e.right ∉ V)).card

/-- The biadjacency matrix applied to `f : V_R → ℝ`: `(B f)_i = Σ_{j : ij ∈ E} f_j`. -/
noncomputable def biadjApply [Fintype R] (adj : L → R → Prop) (f : R → ℝ) (i : L) : ℝ := by
  classical
  exact ∑ j : R, if adj i j then f j else 0

/-- All nontrivial biadjacency singular values are at most `σ`: `‖B f‖₂² ≤ σ² ‖f‖₂²` for every
`f ⊥ 𝟙` on the right side. -/
def NontrivialSingularValuesLe [Fintype L] [Fintype R] (adj : L → R → Prop) (σ : ℝ) : Prop :=
  ∀ f : R → ℝ, ∑ j, f j = 0 → ∑ i : L, (biadjApply adj f i) ^ 2 ≤ σ ^ 2 * ∑ j : R, (f j) ^ 2

end Host

end OncePaid.Sparse


