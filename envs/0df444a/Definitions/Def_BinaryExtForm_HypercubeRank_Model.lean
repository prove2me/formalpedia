-- Prove2me | Definitions.Def_BinaryExtForm_HypercubeRank_Model
-- name    : BinaryExtForm_HypercubeRank_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:13:43.606875+00:00
-- url     : https://prove2.me/theorems/8432a450-830e-4e22-b2b3-26f047f1e3a2
-- title:
--   pp. 3–5, 9–10, 12–13 — lpr, binarization (1), natural, B^L(d), B(f), rk_B (Definition 4.7), hypercube binarization, α-edges, indicator vectors, f_B
-- statement:
--   This file fixes the vocabulary of Aprile, Conforti and Di Summa's study of the rank of binarizations.
--
--   **Polytopes and the lift-and-project rank (p. 3).** A *polytope* is the convex hull of finitely many points of $\mathbb R^n$. For a polytope $Q$ whose coordinates indexed by a set $H$ lie in $[0,1]$, and for $i \in H$, the one-step convexification is $Q_{x_i} = \operatorname{conv}(\{x \in Q : x_i = 0\} \cup \{x \in Q : x_i = 1\})$ (the published `SplitConvexify`). The *0/1 hull* is
--   $$\operatorname{conv}\{x \in Q : x_i \in \{0,1\}\ \forall i \in H\}.$$
--   The *lift-and-project rank* $\operatorname{lpr}(Q)$ with respect to $H$ is the least integer $k$ for which there are indices $i_1, \dots, i_k \in H$, repetitions allowed, with $((Q_{x_{i_1}})\dots)_{x_{i_k}}$ equal to the 0/1 hull.
--
--   **Binarizations (pp. 4–5).** Points $(x, y) \in \mathbb R \times \mathbb R^d$ are written with $x$ first. A polytope $B \subseteq \mathbb R \times [0,1]^d$ is a *binarization of $x$ in the range $\{0, \dots, k\}$*, for a positive integer $k$, if
--   $$\pi_x(\{(x,y) \in B : y \in \{0,1\}^d\}) = \{0, \dots, k\}. \tag{1}$$
--   $B$ is *natural* (Definition 2.5) if $x$ is an integer at every vertex $(x, y)$ of $B$; *integral* (Definition 2.6) if $B = \operatorname{conv}(B \cap (\mathbb Z \times \{0,1\}^d))$; *affine* (Definition 2.9) if $x = f(y)$ on $B$ for an affine $f : \mathbb R^d \to \mathbb R$. The *logarithmic binarization* is
--   $$B^L(d) = \Big\{(x, y) \in \mathbb R \times [0,1]^d : x = \sum_{i=1}^d 2^{i-1} y_i\Big\}.$$
--
--   **Slices and the rank of a binarization (pp. 9–10).** For a number $f$, $B(f) = \{(x,y) \in B : x = f\}$. Given $\alpha_1, \dots, \alpha_\ell$ and points $\bar x^j$ with $\alpha_j < \bar x^j < \alpha_j + 1$, Definition 4.7 sets
--   $$\operatorname{rk}_B(\alpha_1, \dots, \alpha_\ell) = \operatorname{lpr}\Big(\operatorname{conv}\Big(\bigcup_{j \in [\ell]} B(\bar x^j)\Big)\Big),$$
--   the lift-and-project rank taken with respect to $y_1, \dots, y_d$ only.
--
--   **Edges (p. 10).** Two vertices $u, v$ of a polytope are adjacent when the segment $[u,v]$ is a face of it (the published `Hirsch.Adj`); the skeleton $\operatorname{sk}(B)$ is the resulting graph. An edge $((x^u,y^u),(x^v,y^v))$ of $\operatorname{sk}(B)$ is an *$\alpha$-edge* if $x^u \le \alpha$ and $x^v \ge \alpha + 1$, or vice versa. Its *indicator vector* $t \in \{0,1\}^d$ has $t_k = 0$ if $y^u_k$ and $y^v_k$ are both $0$ or both $1$, and $t_k = 1$ otherwise.
--
--   **Hypercube binarizations and $f_B$ (pp. 12–13).** $B$ is a *$d$-hypercube binarization* if $\pi_y(V(B)) = \{0,1\}^d$ and $\pi_x(V(B)) = \{0, \dots, 2^d - 1\}$, where $V(B)$ is the vertex set. Its hypercube graph $G(B)$ has vertex set $V(B)$, two vertices being adjacent when their $y$-parts differ in exactly one component; such an edge has *type* $i$ when that component is $i$, i.e. when it lies in the cut $\delta(V^i_0)$, $V^i_0 = \{(x,y) \in V(B) : y_i = 0\}$. With $V_\alpha = \{(x,y) \in V(B) : x \le \alpha\}$,
--   $$f_B(\alpha_1, \dots, \alpha_\ell) = \Big|\Big\{i : \delta(V^i_0) \cap \bigcup_{j=1}^\ell \delta(V_{\alpha_j}) = \emptyset\Big\}\Big|.$$
--
--   These are the objects in which the paper's Theorem 2.1, Observations 2.2, 2.3, 4.8, Lemmas 4.3, 4.18, 4.20, 4.21, Corollaries 4.15, 4.19, 4.22 and Theorem 4.23 are stated.
--
--   **Formalization Note.** A point $(x,y)$ is `p : Fin (d+1) → ℝ` with $x$ = `p 0` and $y_i$ = `p i.succ`, so the paper's $y_1, \dots, y_d$ are `Fin d`-indexed from $0$ and the weight $2^{i-1}$ of $B^L(d)$ becomes `2 ^ (i : ℕ)`. `lpr Q H` is stated for an arbitrary set `H` of 0/1 coordinates rather than the first $h$ (the same notion up to relabelling coordinates); it is an `sInf` over list lengths, attained whenever Theorem 2.1 applies. `rk B xbar` takes the fractional points $\bar x^j$ as an argument; the $\alpha_j$ appear only in the hypotheses of the theorems that use it. `typeHit B α i` encodes $\delta(V^i_0) \cap \bigcup_j \delta(V_{\alpha_j}) \neq \emptyset$ through vertices of $B$: two vertices whose $y$-parts differ exactly in component $i$, one with $x \le \alpha_j$, the other with $x \ge \alpha_j + 1$; `fB` counts the components for which this fails. Both have the paper's meaning on hypercube binarizations, where every theorem uses them. In `IsHypercubeBinarization` the range $\{0,\dots,2^d-1\}$ is written $m + 1 \le 2^d$; the binarization range $k = 2^d - 1$ is forced by the two vertex conditions.
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, pp. 3–5, 9–10, 12–13: §2.1 p. 3 (Q_{x_i}, definition of lpr(Q)), §2.2 p. 4 Eq. (1), §2.3 p. 5 Definitions 2.5, 2.6, 2.9 and B^L(d), §4 p. 9 (B(f)), p. 10 (sk, α-edge, indicator vector, Definition 4.7), §4.2 p. 12 (d-hypercube binarization), §4.3 p. 13 (G(B), V_α, V^i_0, type, f_B)

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Hirsch_model

namespace BinaryExtForm.HypercubeRank

open Disjunctive.HigherDim

/-- A polytope: the convex hull of a finite set of points. -/
def IsPolytope {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ S : Finset (Fin n → ℝ), P = convexHull ℝ (S : Set (Fin n → ℝ))

/-- The 0/1 hull `conv{x ∈ Q : x_i ∈ {0, 1} ∀ i ∈ H}` of `Q` with respect to the coordinates
`H` (Aprile–Conforti–Di Summa, arXiv:2106.00354v1, p. 3). -/
def intHull {n : ℕ} (Q : Set (Fin n → ℝ)) (H : Finset (Fin n)) : Set (Fin n → ℝ) :=
  convexHull ℝ (Q ∩ ⋂ i ∈ H, ZeroOneSet i)

/-- The lift-and-project rank `lpr(Q)` with respect to the 0/1 coordinates `H` (p. 3): the least
number `k` of (not necessarily distinct) coordinates `i₁, …, i_k ∈ H` such that the iterated
convexification `((Q_{x_{i₁}}) …)_{x_{i_k}}` equals `conv{x ∈ Q : x_i ∈ {0,1} ∀ i ∈ H}`. -/
noncomputable def lpr {n : ℕ} (Q : Set (Fin n → ℝ)) (H : Finset (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ l : List (Fin n), (∀ i ∈ l, i ∈ H) ∧ l.length = k ∧
    IteratedSplit Q l = intHull Q H}

/-! Points `(x, y) ∈ ℝ × ℝ^d` are encoded as `p : Fin (d + 1) → ℝ` with `x = p 0` and
`y_i = p i.succ` (`i : Fin d`, 0-based). -/

/-- The `y`-coordinates `{1, …, d}` of `Fin (d + 1)`. -/
def yCoords (d : ℕ) : Finset (Fin (d + 1)) := Finset.univ.image Fin.succ

/-- The projection `π_y(x, y) = y`. -/
def yproj {d : ℕ} (p : Fin (d + 1) → ℝ) : Fin d → ℝ := fun i => p i.succ

/-- `y ∈ {0, 1}^d`. -/
def IsBinaryY {d : ℕ} (p : Fin (d + 1) → ℝ) : Prop := ∀ i : Fin d, p i.succ = 0 ∨ p i.succ = 1

/-- A binarization of `x` in the range `{0, …, k}` (p. 4, (1)): a polytope
`B ⊆ ℝ × [0, 1]^d`, `k` a positive integer, with `π_x({(x, y) ∈ B : y ∈ {0,1}^d}) = {0, …, k}`. -/
def IsBinarization (d k : ℕ) (B : Set (Fin (d + 1) → ℝ)) : Prop :=
  IsPolytope B ∧ 0 < k ∧ (∀ p ∈ B, ∀ i : Fin d, 0 ≤ p i.succ ∧ p i.succ ≤ 1) ∧
    (fun p => p 0) '' {p | p ∈ B ∧ IsBinaryY p} = {t : ℝ | ∃ m : ℕ, m ≤ k ∧ t = m}

/-- Definition 2.5 (p. 5): `x` is an integer at every vertex `(x, y)` of `B`. -/
def IsNatural {d : ℕ} (B : Set (Fin (d + 1) → ℝ)) : Prop :=
  ∀ p ∈ Set.extremePoints ℝ B, ∃ m : ℤ, p 0 = m

/-- Definition 2.6 (p. 5): `B = conv(B ∩ (ℤ × {0, 1}^d))`. -/
def IsIntegral {d : ℕ} (B : Set (Fin (d + 1) → ℝ)) : Prop :=
  B = convexHull ℝ {p | p ∈ B ∧ (∃ m : ℤ, p 0 = m) ∧ IsBinaryY p}

/-- Definition 2.9 (p. 5): `x = f(y)` on `B` for an affine `f : ℝ^d → ℝ`. -/
def IsAffineBin {d : ℕ} (B : Set (Fin (d + 1) → ℝ)) : Prop :=
  ∃ (a : Fin d → ℝ) (β : ℝ), ∀ p ∈ B, p 0 = ∑ i, a i * p i.succ + β

/-- The logarithmic binarization (p. 5):
`B^L(d) = {(x, y) ∈ ℝ × [0, 1]^d : x = ∑_{i=1}^d 2^{i-1} y_i}` (0-based: weight `2^i`). -/
def BL (d : ℕ) : Set (Fin (d + 1) → ℝ) :=
  {p | (∀ i : Fin d, 0 ≤ p i.succ ∧ p i.succ ≤ 1) ∧
    p 0 = ∑ i : Fin d, (2 : ℝ) ^ (i : ℕ) * p i.succ}

/-- The slice `B(f) = {(x, y) ∈ B : x = f}` (p. 9). -/
def slice {d : ℕ} (B : Set (Fin (d + 1) → ℝ)) (f : ℝ) : Set (Fin (d + 1) → ℝ) :=
  {p | p ∈ B ∧ p 0 = f}

/-- Definition 4.7 (p. 10), for chosen fractional points `xbar j ∈ (α_j, α_j + 1)`:
`rk_B(α₁, …, α_ℓ) = lpr(conv(⋃_{j ∈ [ℓ]} B(x̄^j)))`, the lpr taken with respect to
`y₁, …, y_d`. The `α_j` enter only through the hypotheses on `xbar` in each statement. -/
noncomputable def rk {d ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (xbar : Fin ℓ → ℝ) : ℕ :=
  lpr (convexHull ℝ (⋃ j, slice B (xbar j))) (yCoords d)

/-- A `d`-hypercube binarization (p. 12): a binarization (necessarily of the range
`{0, …, 2^d − 1}`) with `π_y(V(B)) = {0, 1}^d` and `π_x(V(B)) = {0, …, 2^d − 1}`. -/
def IsHypercubeBinarization (d : ℕ) (B : Set (Fin (d + 1) → ℝ)) : Prop :=
  IsBinarization d (2 ^ d - 1) B ∧
    yproj '' Set.extremePoints ℝ B = {y : Fin d → ℝ | ∀ i, y i = 0 ∨ y i = 1} ∧
    (fun p => p 0) '' Set.extremePoints ℝ B = {t : ℝ | ∃ m : ℕ, m + 1 ≤ 2 ^ d ∧ t = m}

/-- `(u, v)` is an `α`-edge of the skeleton `sk(B)` (p. 10): `[u, v]` is an edge of `B` and
`x^u ≤ α`, `x^v ≥ α + 1`, or vice versa. -/
def IsAlphaEdge {d : ℕ} (B : Set (Fin (d + 1) → ℝ)) (α : ℕ) (u v : Fin (d + 1) → ℝ) : Prop :=
  Hirsch.Adj B u v ∧ ((u 0 ≤ α ∧ (α : ℝ) + 1 ≤ v 0) ∨ (v 0 ≤ α ∧ (α : ℝ) + 1 ≤ u 0))

/-- The `i`-th entry of the indicator vector of the edge `(u, v)` is `1` (p. 10): it is `0`
exactly when `y^u_i` and `y^v_i` are both `0` or both `1`. -/
def indicator {d : ℕ} (u v : Fin (d + 1) → ℝ) (i : Fin d) : Prop :=
  ¬ ((u i.succ = 0 ∧ v i.succ = 0) ∨ (u i.succ = 1 ∧ v i.succ = 1))

/-- The `y`-parts of `u` and `v` differ in component `i` and in no other component; for vertices
of a hypercube binarization this says `{u, v}` is an edge of `G(B)` of type `i` (p. 13). -/
def DiffersOnlyAt {d : ℕ} (u v : Fin (d + 1) → ℝ) (i : Fin d) : Prop :=
  u i.succ ≠ v i.succ ∧ ∀ k : Fin d, k ≠ i → u k.succ = v k.succ

/-- `δ(V^i_0) ∩ ⋃_{j=1}^ℓ δ(V_{α_j}) ≠ ∅` in the hypercube graph `G(B)` (p. 13): some edge of
`G(B)` of type `i` has one end `u` with `x^u ≤ α_j` and the other end `v` with `x^v ≥ α_j + 1`. -/
def typeHit {d ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (α : Fin ℓ → ℕ) (i : Fin d) : Prop :=
  ∃ j, ∃ u ∈ Set.extremePoints ℝ B, ∃ v ∈ Set.extremePoints ℝ B,
    DiffersOnlyAt u v i ∧ u 0 ≤ α j ∧ (α j : ℝ) + 1 ≤ v 0

/-- `f_B(α₁, …, α_ℓ) = |{i : δ(V^i_0) ∩ ⋃_{j=1}^ℓ δ(V_{α_j}) = ∅}|` (p. 13). -/
noncomputable def fB {d ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (α : Fin ℓ → ℕ) : ℕ := by
  classical exact (Finset.univ.filter (fun i : Fin d => ¬ typeHit B α i)).card

end BinaryExtForm.HypercubeRank


