-- Prove2me | Definitions.Def_MixedVolFPRAS_Main_MixedVolume
-- name    : MixedVolFPRAS_Main_MixedVolume
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:29:43.568541+00:00
-- url     : https://prove2.me/theorems/7d8272c2-0160-4064-aaa1-8c4ebb06ddc5
-- title:
--   Mixed volume of n compact sets in ℝⁿ (inclusion–exclusion form, Eq. (3))
-- statement:
--   For compact convex $K_1,\dots,K_m\subseteq\mathbb{R}^n$, Minkowski's theorem says that $\mathrm{Vol}_n(t_1K_1+\dots+t_mK_m)$ is, for $t\in\mathbb{R}^m_{\ge0}$, a homogeneous polynomial of degree $n$ (Eq. (1)), $\sum_{i_1,\dots,i_n}V_n(K_{i_1},\dots,K_{i_n})\prod_j t_{i_j}$ with symmetric coefficients; the coefficient $V_n(K_1,\dots,K_n)$ is the **mixed volume**. This item defines it by the inclusion–exclusion formula Eq. (3):
--
--   $$V_n(K_1,\dots,K_n)=\frac{1}{n!}\sum_{\ell=1}^{n}(-1)^{n+\ell}\sum_{1\le i_1<\dots<i_\ell\le n}\mathrm{Vol}_n\big(K_{i_1}+\dots+K_{i_\ell}\big).$$
--
--   The right-hand side makes sense for every tuple of compact sets; on compact convex sets it equals the coefficient of Eq. (1) (with the paper's normalization, so $V_n(K,\dots,K)=\mathrm{Vol}_n(K)$; Gurvits's normalization differs by $n!$). It is also used for the flat sets $K\times\{0\}$ and the segment of §A.1.
--
--   For a tuple $C=(C_1,\dots,C_{n-2})$, $V_n(a,b,C)$ denotes $V_n(a,b,C_1,\dots,C_{n-2})$.
--
--   **Formalization Note.** `mixedVolume K` takes `K : Fin n → Set (E n)` and sums over the nonempty `S : Finset (Fin n)` with sign `(-1)^(n + |S|)` and `vol (minkowskiSum S K)`. Using Eq. (3) as the definition is an encoding of Eq. (1): the two agree on compact convex sets. At $n=0$ the sum is empty and the value is $0$; no item uses $n=0$. `tuple2 a b C : Fin n → Set (E n)` is $(a,b,C_1,\dots,C_{n-2})$ (index 0 is $a$, index 1 is $b$, index $k\ge2$ is $C_{k-1}$).
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 2, Eq. (1) and p. 10, Eq. (3)

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_ConvexGeometry

open scoped Pointwise

noncomputable section

namespace MixedVolFPRAS.Main

/-!
# The mixed volume `Vₙ(K₁, …, Kₙ)`

Chen, Liu, *An FPRAS for Mixed Volumes*, p. 2, Eq. (1), and p. 10, Eq. (3).

The mixed volume is defined by the inclusion–exclusion formula Eq. (3):
`Vₙ(K₁,…,Kₙ) = (1/n!) ∑_{∅ ≠ S ⊆ [n]} (−1)^{n+|S|} Volₙ(∑_{i∈S} Kᵢ)`.
It is defined for all compact sets; on compact convex sets it is the symmetric coefficient of
Minkowski's volume polynomial Eq. (1).

`tuple2 a b C` is the `n`-tuple `(a, b, C₁, …, C_{n−2})` (used for `Vₙ(K, L, C)`).
-/

/-- The mixed volume, by the inclusion–exclusion formula Eq. (3). -/
def mixedVolume {n : ℕ} (K : Fin n → Set (E n)) : ℝ :=
  (1 / (n.factorial : ℝ)) *
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))) with S.Nonempty,
      (-1 : ℝ) ^ (n + S.card) * vol (minkowskiSum S K)

/-- The `n`-tuple `(a, b, C₁, …, C_{n−2})`. -/
def tuple2 {n : ℕ} (a b : Set (E n)) (C : Fin (n - 2) → Set (E n)) : Fin n → Set (E n) :=
  fun i => if h0 : i.val = 0 then a else if h1 : i.val = 1 then b
    else C ⟨i.val - 2, by have := i.isLt; omega⟩

end MixedVolFPRAS.Main


