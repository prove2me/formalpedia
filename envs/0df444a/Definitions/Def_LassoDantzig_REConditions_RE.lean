-- Prove2me | Definitions.Def_LassoDantzig_REConditions_RE
-- name    : LassoDantzig_REConditions_RE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T10:01:22.962087+00:00
-- url     : https://prove2.me/theorems/6c1f82ac-52cb-4750-9633-8f281e77cf43
-- title:
--   Restricted eigenvalue assumptions RE$(s,c_0)$ and RE$(s,m,c_0)$ with a witness $\kappa$
-- statement:
--   Let $X\in\mathbb R^{n\times M}$ be a design matrix with columns $x_1,\dots,x_M\in\mathbb R^n$. For $\delta\in\mathbb R^M$ and $J\subseteq\{1,\dots,M\}$ write $\delta_J$ for the vector that agrees with $\delta$ on $J$ and vanishes off $J$, $|\delta_J|_1=\sum_{j\in J}|\delta_j|$, $|\delta_J|_2=(\sum_{j\in J}\delta_j^2)^{1/2}$, $J(\delta)=\{j:\delta_j\neq0\}$ and $\mathcal M(\delta)=|J(\delta)|$ (the sparsity of $\delta$). For $J_0\subseteq\{1,\dots,M\}$ and $c_0>0$ the **cone condition** (4.1) is
--
--   $$
--   |\delta_{J_0^c}|_1\le c_0\,|\delta_{J_0}|_1 .
--   $$
--
--   For an integer $s$ and a number $\kappa$, **RE$(s,c_0)$ with witness $\kappa$** means: for every $J_0$ with $|J_0|\le s$ and every $\delta\ne0$ satisfying (4.1),
--
--   $$
--   \kappa\,\sqrt n\,|\delta_{J_0}|_2\le |X\delta|_2 .
--   $$
--
--   Given $J_0$, a set $J_1$ is an admissible choice of "the $m$ largest in absolute value coordinates of $\delta$ outside of $J_0$" if $J_1\subseteq J_0^c$, $|J_1|=m$, and $|\delta_k|\le|\delta_j|$ for all $j\in J_1$, $k\in J_0^c\setminus J_1$. **RE$(s,m,c_0)$ with witness $\kappa$** means: for every $J_0$ with $|J_0|\le s$, every $\delta\neq0$ satisfying (4.1), and every admissible $J_1$, with $J_{01}=J_0\cup J_1$,
--
--   $$
--   \kappa\,\sqrt n\,|\delta_{J_{01}}|_2\le |X\delta|_2 .
--   $$
--
--   The paper's quantities $\kappa(s,c_0)$ and $\kappa(s,m,c_0)$ are the largest such witnesses, and Assumption RE$(s,c_0)$ (resp. RE$(s,m,c_0)$) of the paper is the statement that some $\kappa>0$ is a witness.
--
--   The file also defines the partition of $J_0^c$ into consecutive blocks $J_1,\dots,J_K$ of the $m$ largest remaining $|\delta_j|$ used in Appendix A (sizes $|J_k|=m$ for $k<K$, $|J_K|\le m$, blocks sorted by decreasing $|\delta_j|$), the column span of $X_J$ in $\mathbb R^n$, and the Euclidean norm $|P_J v|_2$ of the orthogonal projection of $v\in\mathbb R^n$ onto that span (the projector $P_{01}$ of Lemma 4.1 is $P_{J_{01}}$).
--
--   These are the conditions under which the paper proves all of its Lasso and Dantzig selector bounds.
--
--   **Formalization Note** RE is stated through a witness $\kappa$ instead of the minimum $\kappa(s,c_0)$: the minimum is attained (the normalized cone is compact), so it is itself a witness and every witness is at most it; this avoids the junk value of a real `sInf` over the empty set that arises for $J_0=\emptyset$. Under ties, all admissible $J_1$ are quantified over. The projector lives in $\mathbb R^n$ (the paper writes "$\mathbb R^M$", a slip: the columns of $X$ are in $\mathbb R^n$); it is Mathlib's `Submodule.starProjection` on `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 7, Assumptions RE(s, c0) and RE(s, m, c0); p. 9, Eq. (4.1) and Lemma 4.1 (projector P01); p. 19, Appendix A (block partition)

import Mathlib

namespace LassoDantzig.REConditions

/-- The restriction `δ_J` of a vector `δ ∈ ℝ^M` to an index set `J`: it agrees with `δ` on `J`
and vanishes off `J` (Bickel–Ritov–Tsybakov, p. 4). -/
def restrict {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : Fin M → ℝ :=
  fun j => if j ∈ J then δ j else 0

/-- `|δ_J|_1 = ∑_{j ∈ J} |δ_j|`. -/
noncomputable def l1On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  ∑ j ∈ J, |δ j|

/-- `|δ_J|_2 = (∑_{j ∈ J} δ_j²)^{1/2}`. -/
noncomputable def l2On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  Real.sqrt (∑ j ∈ J, δ j ^ 2)

/-- The Euclidean norm `|v|_2` of a vector `v ∈ ℝ^n`. -/
noncomputable def euclNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The support `J(x) = {j : x_j ≠ 0}` (p. 4). -/
noncomputable def supp {M : ℕ} (x : Fin M → ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun j => x j ≠ 0)

/-- The sparsity `𝓜(x) = |J(x)|`, the number of non-zero coordinates (p. 4). -/
noncomputable def sparsity {M : ℕ} (x : Fin M → ℝ) : ℕ :=
  (supp x).card

/-- The cone condition (4.1) (p. 9): `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1`. -/
def ConeCond {M : ℕ} (c0 : ℝ) (J0 : Finset (Fin M)) (δ : Fin M → ℝ) : Prop :=
  l1On δ J0ᶜ ≤ c0 * l1On δ J0

/-- `J1` is an admissible choice of "the set of the `m` largest in absolute value coordinates of
`δ` outside of `J0`" (p. 7): `J1 ⊆ J0ᶜ`, `|J1| = m`, and every coordinate of `δ` in
`J0ᶜ \ J1` is at most, in absolute value, every coordinate in `J1`. Under ties several sets
qualify; statements quantify over all of them. -/
def IsTopBlock {M : ℕ} (δ : Fin M → ℝ) (J0 J1 : Finset (Fin M)) (m : ℕ) : Prop :=
  J1 ⊆ J0ᶜ ∧ J1.card = m ∧ ∀ j ∈ J1, ∀ k ∈ J0ᶜ \ J1, |δ k| ≤ |δ j|

/-- Assumption RE(s, c₀) (p. 7) with witness `κ`: for every `J0` with `|J0| ≤ s` and every
`δ ≠ 0` satisfying the cone condition (4.1), `κ √n |δ_{J0}|_2 ≤ |Xδ|_2`.
The paper's `κ(s, c₀)` is the largest such `κ`; Assumption RE(s, c₀) is "`RE X s c0 κ` for
some `κ > 0`". -/
def RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    κ * Real.sqrt n * l2On δ J0 ≤ euclNorm (X.mulVec δ)

/-- Assumption RE(s, m, c₀) (p. 7) with witness `κ`: as `RE`, but with `|δ_{J01}|_2` in the
denominator, `J01 = J0 ∪ J1`, for every admissible `J1` (the `m` largest `|δ_j|` outside `J0`). -/
def REm {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s m : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    ∀ J1 : Finset (Fin M), IsTopBlock δ J0 J1 m →
      κ * Real.sqrt n * l2On δ (J0 ∪ J1) ≤ euclNorm (X.mulVec δ)

/-- The blocks `J 1, …, J K` form a partition of the index set `S`: pairwise disjoint, with union
`S`. (Blocks may be empty; `K ≥ 1`.) -/
def IsBlockPartition {M : ℕ} (S : Finset (Fin M)) (J : ℕ → Finset (Fin M)) (K : ℕ) : Prop :=
  1 ≤ K ∧
  (∀ k ∈ Finset.Icc 1 K, ∀ l ∈ Finset.Icc 1 K, k ≠ l → Disjoint (J k) (J l)) ∧
  (Finset.Icc 1 K).biUnion J = S

/-- The partition of `J0ᶜ` used in Appendix A (p. 19): `J0ᶜ = J 1 ∪ ⋯ ∪ J K`, `|J k| = m` for
`k = 1, …, K − 1`, `|J K| ≤ m`, and the blocks are sorted by decreasing absolute value of `δ`
(every coordinate in a later block is at most every coordinate in an earlier one), so that `J k`
is the set of the `m` largest `|δ_j|` outside `J 1 ∪ ⋯ ∪ J (k − 1)` for `k < K`, and `J K` is the
remaining set. -/
def IsShelling {M : ℕ} (δ : Fin M → ℝ) (J0 : Finset (Fin M)) (m : ℕ)
    (J : ℕ → Finset (Fin M)) (K : ℕ) : Prop :=
  IsBlockPartition J0ᶜ J K ∧
  (∀ k ∈ Finset.Ico 1 K, (J k).card = m) ∧
  (J K).card ≤ m ∧
  ∀ k ∈ Finset.Icc 1 K, ∀ l ∈ Finset.Icc 1 K, k < l → ∀ a ∈ J k, ∀ b ∈ J l, |δ b| ≤ |δ a|

/-- The linear span in `ℝⁿ` of the columns of `X` indexed by `J`, i.e. of the columns of `X_J`. -/
noncomputable def colSpan {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (J : Finset (Fin M)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ ((fun j => WithLp.toLp 2 (fun i => X i j)) '' (J : Set (Fin M)))

/-- `|P_J v|_2`: the Euclidean norm of the orthogonal projection of `v ∈ ℝⁿ` onto the span of
the columns of `X_J` (the projector `P01` of Lemma 4.1 is the case `J = J01`). -/
noncomputable def projNorm {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (J : Finset (Fin M))
    (v : Fin n → ℝ) : ℝ :=
  ‖(colSpan X J).starProjection (WithLp.toLp 2 v)‖

end LassoDantzig.REConditions


