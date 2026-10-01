-- Prove2me | Definitions.Def_CandesTao_Decoding_Norms
-- name    : CandesTao_Decoding_Norms
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-30T21:59:02.716785+00:00
-- url     : https://prove2.me/theorems/bece5bfc-4878-4a9a-aab1-9bfab86b6b4a
-- title:
--   Support, $\ell^1$ norm and Euclidean norm on $\mathbb{R}^m$
-- statement:
--   Three elementary notions used throughout the mission, for real vectors indexed by $\{1,\dots,m\}$.
--
--   1. A vector $c \in \mathbb{R}^m$ is **supported on** an index set $T \subseteq \{1,\dots,m\}$ when $c_j = 0$ for every $j \notin T$. This is how the paper's "real vector supported on a set $T$" and its coefficient vectors $(c_j)_{j \in T}$ are represented: a vector of full length $m$ whose coordinates outside $T$ vanish, so that $F_T c = \sum_{j \in T} c_j v_j$ is simply the matrix–vector product $Fc$.
--
--   2. The **$\ell^1$ norm** $\|c\|_{\ell^1} = \sum_{j=1}^m |c_j|$ (paper, Section 1.2).
--
--   3. The **Euclidean norm** $\|x\| = \big(\sum_i x_i^2\big)^{1/2}$, used both for coefficient vectors in $\mathbb{R}^m$ and for vectors in $\mathbb{R}^p$; the paper writes it $\|\cdot\|$ or $\|\cdot\|_H$.
--
--   These are the only norms that enter the restricted isometry constants of Definition 1.1 and the two $\ell^1$-minimization problems $(P_1)$ and $(P_1')$ of the mission.
--
--   **Formalization Note** Both norms are explicit finite sums rather than instances of Mathlib's normed-space structure on `EuclideanSpace`, so that every statement of the mission can be audited by hand against the paper.
-- source:
--   Candès--Tao 2005, Decoding by Linear Programming, IEEE Trans. Inform. Theory 51(12):4203-4215, doi:10.1109/TIT.2005.858979; arXiv:math/0502327v1 (https://arxiv.org/abs/math/0502327), pp. 2-5: support (Lemma 1.3, Theorem 1.4), l1 norm eq. (1.4), Euclidean norm eq. (1.7)-(1.8)

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Matrix.Mul

namespace CandesTao.Decoding

/-- A vector `c ∈ ℝ^m` is supported on the index set `T` when every coordinate outside `T`
is zero. -/
def SupportedOn {m : ℕ} (c : Fin m → ℝ) (T : Finset (Fin m)) : Prop :=
  ∀ j, j ∉ T → c j = 0

/-- The ℓ¹ norm `‖c‖_{ℓ¹} = ∑_j |c_j|`. -/
def l1Norm {m : ℕ} (c : Fin m → ℝ) : ℝ := ∑ j, |c j|

/-- The Euclidean (ℓ²) norm `‖x‖ = (∑_i x_i²)^{1/2}`. -/
noncomputable def l2Norm {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

end CandesTao.Decoding


