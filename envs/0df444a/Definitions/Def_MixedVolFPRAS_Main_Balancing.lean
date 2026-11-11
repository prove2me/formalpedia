-- Prove2me | Definitions.Def_MixedVolFPRAS_Main_Balancing
-- name    : MixedVolFPRAS_Main_Balancing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:31:08.817296+00:00
-- url     : https://prove2.me/theorems/26db365f-626c-4ef3-b812-7e1f38157902
-- title:
--   A-balanced tuples of convex bodies (Definition 5.1) and Z_β(t) (§5.1)
-- statement:
--   For a tuple $K=(K_1,\dots,K_n)$ of convex bodies in $\mathbb{R}^n$ write $(K_{-i},K_j)$ for $K$ with its $i$-th entry replaced by $K_j$. For $A\ge1$, $K$ is **$A$-balanced** (Definition 5.1) if
--
--   $$\frac{V_n(K_{-i},K_j)}{V_n(K)}\le A\qquad\forall i,j\in[n].$$
--
--   For $t\in\mathbb{R}^n_{\ge0}$ let $L(t)=t_1K_1+\dots+t_nK_n$ and
--
--   $$Z_\beta(t)=V_n\big(t_1K_1+\beta L(t),\dots,t_nK_n+\beta L(t)\big),$$
--
--   a polynomial in $\beta$ and $t$, homogeneous of degree $n$ in $t$, with $Z_0(t)=V_n(K_1,\dots,K_n)\prod_it_i$ (Eq. (15)).
--
--   **Formalization Note.** `IsBalanced A K` uses `Function.update K i (K j)` for $(K_{-i},K_j)$. `weightedSum t K` is $L(t)$ and `Zbeta K β t` is $Z_\beta(t)$, with pointwise dilation and Minkowski sum.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 23, §5.1 and p. 24, Definition 5.1

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_MixedVolume

open scoped Pointwise

noncomputable section

namespace MixedVolFPRAS.Main

/-!
# Balancedness (Definition 5.1) and `Z_β(t)` (§5.1)

Chen, Liu, *An FPRAS for Mixed Volumes*, pp. 23–24.

* `K = (K₁, …, Kₙ)` is `A`-balanced when `Vₙ(K_{−i}, K_j) / Vₙ(K) ≤ A` for all `i, j`, where
  `(K_{−i}, K_j)` is `K` with its `i`-th entry replaced by `K_j` (`Function.update K i (K j)`).
* `weightedSum t K = L(t) = t₁K₁ + ⋯ + tₙKₙ`.
* `Zbeta K β t = Z_β(t) = Vₙ(t₁K₁ + βL(t), …, tₙKₙ + βL(t))`.
-/

/-- Definition 5.1: `K` is `A`-balanced. -/
def IsBalanced {n : ℕ} (A : ℝ) (K : Fin n → Set (E n)) : Prop :=
  ∀ i j : Fin n, mixedVolume (Function.update K i (K j)) / mixedVolume K ≤ A

/-- `L(t) = t₁K₁ + ⋯ + tₙKₙ`. -/
def weightedSum {n : ℕ} (t : Fin n → ℝ) (K : Fin n → Set (E n)) : Set (E n) :=
  minkowskiSum Finset.univ (fun j => t j • K j)

/-- `Z_β(t) = Vₙ(t₁K₁ + βL(t), …, tₙKₙ + βL(t))`. -/
def Zbeta {n : ℕ} (K : Fin n → Set (E n)) (β : ℝ) (t : Fin n → ℝ) : ℝ :=
  mixedVolume (fun i => t i • K i + β • weightedSum t K)

end MixedVolFPRAS.Main


