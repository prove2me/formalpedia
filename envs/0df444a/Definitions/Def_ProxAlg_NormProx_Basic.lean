-- Prove2me | Definitions.Def_ProxAlg_NormProx_Basic
-- name    : ProxAlg_NormProx_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:26.27111+00:00
-- url     : https://prove2.me/theorems/b01bd626-1989-47ab-ba17-5fe8f58c77db
-- title:
--   §1.2, p. 125; §2.5, p. 134 — a general norm on ℝⁿ, the dual norm ‖z‖∗ = sup{zᵀx | ‖x‖ ≤ 1}, the dual unit ball B, the indicator I_C
-- statement:
--   Throughout, $\mathbb R^n$ carries the Euclidean inner product $z^Tx$ and the Euclidean norm $\|\cdot\|_2$. This file fixes the objects of §6.5 of Parikh and Boyd.
--
--   1. A **general norm** $\|\cdot\|$ on $\mathbb R^n$ is a seminorm (nonnegative, absolutely homogeneous, subadditive) that vanishes only at $0$. It is a second norm on the space, in general different from $\|\cdot\|_2$.
--   2. The **dual norm** of $\|\cdot\|$ is
--   $$
--   \|z\|_*=\sup\{z^Tx\mid \|x\|\le 1\}.
--   $$
--   3. The **unit ball of the dual norm** is
--   $$
--   \mathcal B=\{x\mid \|x\|_*\le 1\}.
--   $$
--   4. The **indicator function** of a set $C\subseteq\mathbb R^n$ is $I_C(x)=0$ for $x\in C$ and $I_C(x)=+\infty$ for $x\notin C$.
--   5. The norm $f=\|\cdot\|$ is also regarded as a function $\mathbb R^n\to\mathbb R\cup\{+\infty\}$ that happens to take only finite values.
--
--   These are the objects in the statement that the proximal operator of a norm is $v-\lambda\Pi_{\mathcal B}(v/\lambda)$: the conjugate of a norm is $I_{\mathcal B}$, and the proximal operator of $I_{\mathcal B}$ is the Euclidean projection onto $\mathcal B$.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`. A general norm is a Mathlib `Seminorm ℝ (EuclideanSpace ℝ (Fin n))` `N` together with the structure `IsNorm N` (definiteness: `N x = 0 → x = 0`). The dual norm is computed in `EReal` as the supremum of the image set $\{z^Tx \mid N(x)\le 1\}$, so it is always the true supremum (no junk value); for a norm on $\mathbb R^n$ it is a finite real number. The indicator and the norm-as-function take values in `EReal`. Closed proper convex functions, the convex conjugate $f^*(y)=\sup_x(y^Tx-f(x))$, the proximal-point predicate and the projection predicate are imported from the published Moreau 1965 definitions `MoreauProx.Decomposition.ConvexDuality` and `MoreauProx.Decomposition.Cones`.
-- source:
--   Parikh & Boyd, Proximal Algorithms, Found. Trends Optim. 1(3) (2014), §1.2, p. 125 (indicator I_C); §2.5, p. 134 (dual norm and its unit ball B); §6.5, p. 187

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality
import Definitions.Def_MoreauProx_Decomposition_Cones

namespace ProxAlg.NormProx

open scoped InnerProductSpace

/-- A general norm `‖·‖` on `ℝⁿ` (Parikh–Boyd §2.5, p. 134; §6.5, p. 187): a seminorm `N` on
`EuclideanSpace ℝ (Fin n)` that vanishes only at `0`. It is unrelated to the Euclidean norm `‖·‖₂`
of the space, which stays the norm of the proximal objective (1.1). -/
structure IsNorm {n : ℕ} (N : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) : Prop where
  eq_zero_of_eq_zero : ∀ x, N x = 0 → x = 0

/-- The dual norm `‖z‖∗ = sup {zᵀx | ‖x‖ ≤ 1}` (Parikh–Boyd §2.5, p. 134), computed in `EReal`,
so the supremum is always the true one (it is a finite real number when `N` is a norm). -/
noncomputable def dualNorm {n : ℕ} (N : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) : EReal :=
  sSup ((fun x => ((⟪z, x⟫_ℝ : ℝ) : EReal)) '' {x | N x ≤ 1})

/-- The unit ball of the dual norm, `B = {x | ‖x‖∗ ≤ 1}` (Parikh–Boyd §2.5, p. 134). -/
def dualBall {n : ℕ} (N : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {z | dualNorm N z ≤ 1}

open Classical in
/-- The indicator function `I_C(x) = 0` for `x ∈ C`, `+∞` for `x ∉ C` (Parikh–Boyd §1.2,
p. 125), with values in `EReal`. -/
noncomputable def indicator {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) → EReal :=
  fun x => if x ∈ C then 0 else ⊤

/-- The norm `f = ‖·‖` viewed as a function `ℝⁿ → ℝ ∪ {+∞}` (it takes only finite values). -/
noncomputable def normFun {n : ℕ} (N : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) → EReal :=
  fun x => ((N x : ℝ) : EReal)

end ProxAlg.NormProx


