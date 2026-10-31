-- Prove2me | Definitions.Def_ApproxNashSet_Model
-- name    : ApproxNashSet_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:05.496951+00:00
-- url     : https://prove2.me/theorems/c38d965e-8e80-4a84-b23f-5b1bbe669387
-- title:
--   Shared-constraint games, problem (3), (ε-)Pareto optimality, upper images, convex projections, the L1 norm and the slice modulus (§2–§4, pp.2–10)
-- statement:
--   This file sets up the objects of Feinstein, Hey and Rudloff's approximation of the Nash equilibrium set.
--
--   **Game.** There are finitely many players $i$. Player $i$ chooses $x_i\in X_i=\mathbb R^{n_i}$, a joint strategy is $x=(x_1,\dots,x_N)\in\prod_j X_j$, and $x_{-i}$ collects the strategies of the players $j\neq i$. Player $i$ has a cost $f_i:\prod_j X_j\to\mathbb R$, and $\mathbb X\subseteq\prod_j X_j$ is a shared constraint set.
--
--   **ε-approximate Nash equilibria** (Definition 2.2). For a real $\varepsilon$,
--   $$\varepsilon\,\mathrm{NE}(f,\mathbb X)=\{x^*\in\mathbb X:\ f_i(x^*)\le f_i(x_i,x^*_{-i})+\varepsilon\ \text{for every } i \text{ and every } x_i \text{ with } (x_i,x^*_{-i})\in\mathbb X\}.$$
--
--   **Problem (3).** For player $i$ the objective is $g_i(x)=(x_{-i},-x_{-i},f_i(x))\in\mathbb R^{m_i}$, $m_i=2\sum_{j\ne i}n_j+1$, ordered componentwise (cone $\mathbb R^{m_i}_+$), and $\bar c_i=(0,\dots,0,1)$.
--
--   **Pareto and ε-Pareto optimality** (Definitions 2.3–2.4). For $g:D\to\mathbb R^m$, $S\subseteq D$ and a direction $c$,
--   $$\operatorname{argMin}\{g(x)\mid x\in S\}=\{x^*\in S:(g(x^*)-(\mathbb R^m_+\setminus\{0\}))\cap g[S]=\emptyset\},$$
--   $$\varepsilon\operatorname{argMin}\{g(x)\mid x\in S\}=\{x^*\in S:(g(x^*)-\varepsilon c-(\mathbb R^m_+\setminus\{0\}))\cap g[S]=\emptyset\}.$$
--
--   **Upper image and inner approximation** (pp.7, 9): $P=g[S]+\mathbb R^m_+$ and, for a point set $G$, $P^{In}(G)=\operatorname{conv}g[G]+\mathbb R^m_+$. **Minimal elements** of a set $P$: the $y\in P$ with no $y'\in P$, $y'\le y$, $y'\ne y$. **Convex projection** (14): $\bar X(F)=\{x\in S:\exists y\in F,\ g(x)\le y\}$.
--
--   **L1 norm** (p.5): $\|x\|_1=\sum_j\sum_k|x_{jk}|$, the closed ball $B_r=\{b:\|b\|_1\le r\}$ (p.10), and a common L1-Lipschitz constant $L$ of the $f_i$ on $\mathbb X$: $|f_i(x)-f_i(y)|\le L\|x-y\|_1$ for all $i$ and $x,y\in\mathbb X$.
--
--   **Slice modulus** (not in the paper; used by the corrected Lemma 4.11 and Theorem 4.9). $\kappa$ is a slice modulus of $\mathbb X$ for player $i$ if for all $x,z\in\mathbb X$ there is $x'\in\mathbb X$ with $x'_{-i}=z_{-i}$ and
--   $$\|x'_i-x_i\|_1\le\kappa\sum_{j\ne i}\|x_j-z_j\|_1 .$$
--   $\kappa=0$ means $(x_i,z_{-i})\in\mathbb X$ for all $x,z\in\mathbb X$, i.e. $\mathbb X$ is a product of its projections (boxes, classical games).
--
--   **Formalization Note** Players form a finite type with decidable equality; $X_i$ is `Fin (n i) → ℝ`; $(x_i,x^*_{-i})$ is `Function.update`. The objective space is `(∏_{j≠i} ℝ^{n_j}) × (∏_{j≠i} ℝ^{n_j}) × ℝ` with Mathlib's componentwise order. ε-NE uses the universal form of Definition 2.2, not its displayed infimum form (a real infimum of an unbounded set is $0$ in Lean). The L1 norm is written out because Mathlib's norm on function types is the sup norm. The Nash equilibrium set itself (Definition 2.1) is the published `NashVecOpt.SharedConstraint.NE`.
-- source:
--   Feinstein–Hey–Rudloff, Approximating the set of Nash equilibria for convex games, arXiv:2310.04176v4, §2 (Definitions 2.2–2.4, pp.2–3), (3) p.4, Assumption 4.1 and the L1 Lipschitz bound p.5, Pᵢ p.7, P^In_i and (13)–(14) p.9, B_ε₂ p.10

import Mathlib

open scoped Pointwise

namespace ApproxNashSet

/-- **Joint strategy space** `∏ⱼ ℝ^{nⱼ}`.
Feinstein–Hey–Rudloff, *Approximating the set of Nash equilibria for convex games*,
arXiv:2310.04176v4, §2, p.2: "Each player i … considers strategies in the linear space
Xi = R^{ni}", and joint strategies `x ∈ ∏_{j=1}^N Xj`.

**Formalization Note.** The players form a finite type `ι` (the paper's `{1, …, N}`); player `j`'s
strategy space `ℝ^{nⱼ}` is `Fin (n j) → ℝ`. -/
abbrev Joint {ι : Type} (n : ι → ℕ) : Type := ∀ j, Fin (n j) → ℝ

/-- **The other players** `{j | j ≠ i}` (arXiv:2310.04176v4, §2, p.2, the index set of `x₋ᵢ`). -/
abbrev Others {ι : Type} (i : ι) : Type := {j : ι // j ≠ i}

/-- **Strategies of the other players** `∏_{j≠i} ℝ^{nⱼ}` (arXiv:2310.04176v4, §2, p.2). -/
abbrev OthersStrat {ι : Type} (n : ι → ℕ) (i : ι) : Type := ∀ j : Others i, Fin (n j.1) → ℝ

/-- **`x₋ᵢ`**, the strategies of all players other than `i` (arXiv:2310.04176v4, §2, p.2). -/
def minus {ι : Type} (n : ι → ℕ) (i : ι) (x : Joint n) : OthersStrat n i := fun j => x j.1

/-- **Objective space of problem (3)**, `ℝ^{mᵢ}` with `mᵢ = 2 ∑_{j≠i} nⱼ + 1`
(arXiv:2310.04176v4, (3), p.4).

**Formalization Note.** `ℝ^{mᵢ}` is `(∏_{j≠i} ℝ^{nⱼ}) × (∏_{j≠i} ℝ^{nⱼ}) × ℝ`; Mathlib's order on
products and on function types is componentwise, so `y ≤ y'` is exactly `y' − y ∈ ℝ^{mᵢ}₊`, the
natural ordering cone of (3). -/
abbrev Obj {ι : Type} (n : ι → ℕ) (i : ι) : Type := OthersStrat n i × OthersStrat n i × ℝ

/-- **The objective of problem (3)**: `gᵢ(x) = (x₋ᵢ, −x₋ᵢ, fᵢ(x))`.
arXiv:2310.04176v4, (3), p.4: "min{(x−i, −x−i, fi(x)) | x ∈ X}". -/
def g {ι : Type} (n : ι → ℕ) (f : ι → Joint n → ℝ) (i : ι) (x : Joint n) : Obj n i :=
  (minus n i x, -minus n i x, f i x)

/-- **The direction `c̄ᵢ = (0, …, 0, 1)⊤ ∈ ℝ^{mᵢ}₊ ∖ {0}`** (arXiv:2310.04176v4, p.3 and p.4). -/
def cbar {ι : Type} (n : ι → ℕ) (i : ι) : Obj n i := (0, 0, 1)

/-- **ε-approximate Nash equilibria** `ε NE(f, 𝕏)`.
arXiv:2310.04176v4, Definition 2.2, p.3: "The joint strategy x∗ ∈ X is called an ǫ-approximate Nash
equilibrium for the game if, for any player i it holds fi(xi, x∗−i) + ǫ ≥ fi(x∗) for any xi ∈ Xi
such that (xi, x∗−i) ∈ X."

**Formalization Note.** This is the universal form of the definition's first sentence, not the
displayed `inf` form (a real infimum of a set unbounded below would be `0` in Lean). It is defined
for every real `ε`; the paper takes `ε > 0`. `(xᵢ, x*₋ᵢ)` is `Function.update xs i xi`. -/
def epsNE {ι : Type} [DecidableEq ι] {n : ι → ℕ} (f : ι → Joint n → ℝ) (X : Set (Joint n))
    (ε : ℝ) : Set (Joint n) :=
  {xs | xs ∈ X ∧ ∀ (i : ι) (xi : Fin (n i) → ℝ), Function.update xs i xi ∈ X →
      f i xs ≤ f i (Function.update xs i xi) + ε}

/-- **Pareto optimal points** `argMin{g(x) | x ∈ X}` of a multi-objective problem (2).
arXiv:2310.04176v4, Definition 2.3, p.3: "An element x∗ ∈ X is called Pareto optimal for problem (2)
if (g(x∗) − R^m_+ \ {0}) ∩ g[X] = ∅."

**Formalization Note.** The ordering cone `ℝ^m₊` is `{d | 0 ≤ d}` for the partial order of `Z`
(componentwise on `Obj n i`). -/
def argMin {D Z : Type} [AddCommGroup Z] [PartialOrder Z] (g : D → Z) (S : Set D) : Set D :=
  {xs | xs ∈ S ∧ ((fun d => g xs - d) '' ({d : Z | 0 ≤ d} \ {0})) ∩ g '' S = ∅}

/-- **ε-Pareto optimal points with respect to a direction `c`**, `ε argMin{g(x) | x ∈ X}`.
arXiv:2310.04176v4, Definition 2.4, p.3: "Let c ∈ R^m_+ \ {0}. An element x∗ ∈ X is called ǫ-Pareto
optimal with respect to c for problem (2) if (g(x∗) − ǫc − R^m_+ \ {0}) ∩ g[X] = ∅."
The paper fixes `c = c̄` for the rest of the paper (p.3); the theorems instantiate `c := cbar n i`.

**Formalization Note.** Defined for every real `ε` and every `c`; with `ε = 0` it is `argMin`. -/
def epsArgMin {D Z : Type} [AddCommGroup Z] [Module ℝ Z] [PartialOrder Z] (g : D → Z)
    (S : Set D) (c : Z) (ε : ℝ) : Set D :=
  {xs | xs ∈ S ∧ ((fun d => g xs - ε • c - d) '' ({d : Z | 0 ≤ d} \ {0})) ∩ g '' S = ∅}

/-- **Upper image** `P = g[X] + ℝ^m₊`.
arXiv:2310.04176v4, p.7: "Pi := {(x−i, −x−i, fi(x)) | x ∈ X} + R^{mi}_+ the upper image of problem
(3)" (the closure of p.3 is not needed under the assumptions of §4, p.7). -/
def upperImage {D Z : Type} [AddCommGroup Z] [PartialOrder Z] (g : D → Z) (S : Set D) : Set Z :=
  g '' S + {d : Z | 0 ≤ d}

/-- **Polyhedral inner approximation generated by a point set `G`**:
`P^In(G) = conv{g(x) | x ∈ G} + ℝ^m₊`.
arXiv:2310.04176v4, p.9: "PIn_i := conv{(x−i, −x−i, fi(x)) | x ∈ X̄} + R^{mi}_+". -/
def PIn {D Z : Type} [AddCommGroup Z] [Module ℝ Z] [PartialOrder Z] (g : D → Z) (G : Set D) :
    Set Z :=
  convexHull ℝ (g '' G) + {d : Z | 0 ≤ d}

/-- **Minimal elements** of a set `P` in an ordered space: `y ∈ P` such that no `y' ∈ P` with
`y' ≤ y`, `y' ≠ y` exists. These are the Pareto optimal points of the linear problem
min{y | y ∈ PIn_i} (13), arXiv:2310.04176v4, p.9 ("the set of minimal elements of PIn_i").

**Formalization Note.** Minimal, not weakly minimal (Remark 3.4, p.5, explains why weak notions are
not meaningful here). -/
def MinSet {Z : Type} [PartialOrder Z] (P : Set Z) : Set Z :=
  {y | y ∈ P ∧ ∀ y' ∈ P, y' ≤ y → y' = y}

/-- **Convex projection** (14): `X̄(F) = {x ∈ X | ∃ y ∈ F : g(x) ≤ y}`.
arXiv:2310.04176v4, (14), p.9: "¯Xj_i := {x ∈ X | ∃y ∈ F j : (x−i, −x−i, fi(x)) ≤_{R^{mi}_+} y}". -/
def convProj {D Z : Type} [LE Z] (g : D → Z) (S : Set D) (F : Set Z) : Set D :=
  {x | x ∈ S ∧ ∃ y ∈ F, g x ≤ y}

/-- **The L1 norm** `‖x‖ = ∑ⱼ ∑ₖ |xⱼₖ|` on `∏ⱼ ℝ^{nⱼ}`.
arXiv:2310.04176v4, p.5: "where ∥·∥ is the L1 norm on ∏_{j=1}^N Xj".

**Formalization Note.** Written out; Mathlib's `‖·‖` on function types is the sup norm. -/
def l1 {ι : Type} [Fintype ι] {n : ι → ℕ} (x : Joint n) : ℝ := ∑ j, ∑ k, |x j k|

/-- **The closed L1 ball** `B_r = {b | ‖b‖₁ ≤ r}` around the origin.
arXiv:2310.04176v4, p.10: "Bε2 is a closed ε2-ball around the origin (in the L1 norm)". -/
def ballL1 {ι : Type} [Fintype ι] (n : ι → ℕ) (r : ℝ) : Set (Joint n) := {b | l1 b ≤ r}

/-- **Common L1-Lipschitz constant on `X`**: `|fᵢ(x) − fᵢ(y)| ≤ L ‖x − y‖₁` for every player `i`
and all `x, y ∈ X`.
arXiv:2310.04176v4, p.5: "we have for all i = 1, ..., N that |fi(x1) − fi(x2)| ≤ L ∥x1 − x2∥ for
x1, x2 ∈ X where ∥·∥ is the L1 norm". -/
def IsL1Lipschitz {ι : Type} [Fintype ι] {n : ι → ℕ} (f : ι → Joint n → ℝ) (X : Set (Joint n))
    (L : ℝ) : Prop :=
  ∀ i, ∀ x ∈ X, ∀ y ∈ X, |f i x - f i y| ≤ L * l1 (x - y)

/-- **Slice modulus of `X` for player `i`** (not in the paper; used by the corrected Lemma 4.11 and
Theorem 4.9). `κ` is a slice modulus for player `i` if for all `x, z ∈ X` there is `x' ∈ X` with
`x'₋ᵢ = z₋ᵢ` and `‖x'ᵢ − xᵢ‖₁ ≤ κ · ∑_{j≠i} ‖xⱼ − zⱼ‖₁`: the slice of `X` at `z₋ᵢ` contains a point
whose `i`-th block is close to `xᵢ`.

**Formalization Note.** `κ = 0` holds iff `(xᵢ, z₋ᵢ) ∈ X` for all `x, z ∈ X` (take `x' = (xᵢ, z₋ᵢ)`),
which is the property the printed proof of Lemma 4.11 (p.12) uses; it holds for product sets such as
boxes. -/
def IsSliceModulusAt {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (X : Set (Joint n))
    (κ : ℝ) (i : ι) : Prop :=
  ∀ x ∈ X, ∀ z ∈ X, ∃ x' ∈ X, (∀ j, j ≠ i → x' j = z j) ∧
    ∑ k, |x' i k - x i k| ≤ κ * ∑ j ∈ Finset.univ.erase i, ∑ k, |x j k - z j k|

/-- **Slice modulus of `X`**: `κ` is a slice modulus of `X` for every player (see
`IsSliceModulusAt`). -/
def IsSliceModulus {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (X : Set (Joint n))
    (κ : ℝ) : Prop :=
  ∀ i, IsSliceModulusAt X κ i

end ApproxNashSet


