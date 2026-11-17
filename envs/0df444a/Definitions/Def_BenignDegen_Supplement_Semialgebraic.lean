-- Prove2me | Definitions.Def_BenignDegen_Supplement_Semialgebraic
-- name    : BenignDegen_Supplement_Semialgebraic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:30:11.908574+00:00
-- url     : https://prove2.me/theorems/3c9926bf-f6b9-4b12-ad2a-517c1223d3b0
-- title:
--   Semialgebraic subsets of $\mathcal P_n$ and their dimension $\dim A$ (BCR Def. 2.8.1)
-- statement:
--   Identify the space $\mathcal P_n$ of square-free polynomials in $n$ Boolean variables with $\mathbb R^{2^n}$ through its coefficients $(f_T)_{T\subseteq[n]}$.
--
--   1. A subset $A\subseteq\mathcal P_n$ is **semialgebraic** if its coordinate image in $\mathbb R^{2^n}$ is a finite union of basic sets $\{v: p_1(v)=\dots=p_k(v)=0,\ g_1(v)<0,\dots,g_l(v)<0\}$ with real polynomials $p_i,g_j$.
--   2. The **dimension** of a set $A\subseteq\mathbb R^\sigma$ ($\sigma$ finite) is the Krull dimension of the coordinate ring of its Zariski closure,
--   $$
--   \dim A=\dim_{\mathrm{Krull}}\bigl(\mathbb R[X_\sigma]/I(A)\bigr),\qquad I(A)=\{p\in\mathbb R[X_\sigma]: p|_A=0\},
--   $$
--   with $\dim\emptyset=-\infty$.
--
--   These are the notions of Bochnak–Coste–Roy (*Real Algebraic Geometry*, Definition 2.8.1), which the paper cites for Theorem 6.2; for a semialgebraic set this dimension equals the maximal dimension of a cell in any cell decomposition.
--
--   **Formalization Note** Semialgebraicity reuses the published `NonconvexSplitting.ADMMKL.IsSemialgebraicSet` on $\mathrm{Fin}\,N\to\mathbb R$, transported along `Fintype.equivFin`; the choice of bijection is immaterial because semialgebraicity is invariant under coordinate permutations. The dimension uses Mathlib's `MvPolynomial.vanishingIdeal` and `ringKrullDim`, valued in $\mathrm{WithBot}\,\mathbb N_\infty$ with $\dim\emptyset=\bot$.
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, §6, Theorem 6.2, p.11 and Appendix G.2, p.32 (citing Bochnak–Coste–Roy, Real Algebraic Geometry, 1998, Def. 2.8.1, Props. 2.8.2, 2.8.13)

import Mathlib
import Definitions.Def_NonconvexSplitting_ADMMKL_Semialgebraic

namespace BenignDegen

namespace Supplement

noncomputable section

/-! # Semialgebraic subsets of the coefficient space `P_n` and their dimension

Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*,
arXiv:2610.20270v1, §6, p.11 (Theorem 6.2) and p.12 (Theorem 6.3); Appendix G.2, p.32, which
cites Bochnak–Coste–Roy, *Real Algebraic Geometry* (1998), Definition 2.8.1 and
Propositions 2.8.2, 2.8.13 for the dimension of a semialgebraic set.

**Formalization Note** A square-free polynomial `f ∈ P_n` is its coefficient function
`Finset (Fin n) → ℝ` (as in `BenignDegen.Boolean`). A subset of `P_n` is semialgebraic when its
image in `ℝ^{2ⁿ}` under a fixed coordinate bijection `Fin 2ⁿ ≃ Finset (Fin n)` is semialgebraic
in the sense of the published `NonconvexSplitting.ADMMKL.IsSemialgebraicSet` (finite unions of
basic sets `{p₁ = ⋯ = p_k = 0, g₁ < 0, …, g_l < 0}`, the definition of [BCR98]); this does not
depend on the bijection, since semialgebraicity is invariant under permutations of coordinates.
The dimension of `A ⊆ ℝ^σ` (`σ` finite) is BCR Definition 2.8.1: the Krull dimension of
`ℝ[X_σ]/I(A)`, `I(A)` the ideal of polynomials vanishing on `A`, valued in `WithBot ℕ∞`, so that
`dim ∅ = ⊥` (BCR's `−∞`). -/

/-- A subset of the coefficient space `P_n = (Finset (Fin n) → ℝ)` is **semialgebraic**: its
coordinate image in `ℝ^{2ⁿ}` is a finite union of basic semialgebraic sets ([BCR98]). -/
def IsSemialgebraicCoeff {n : ℕ} (A : Set (Finset (Fin n) → ℝ)) : Prop :=
  NonconvexSplitting.ADMMKL.IsSemialgebraicSet
    {v : Fin (Fintype.card (Finset (Fin n))) → ℝ |
      (fun T => v (Fintype.equivFin (Finset (Fin n)) T)) ∈ A}

/-- The **dimension** of a subset `A ⊆ ℝ^σ` ([BCR98, Definition 2.8.1]): the Krull dimension of
the ring `ℝ[X_σ]/I(A)`, where `I(A)` is the ideal of real polynomials vanishing on `A`. It is
`⊥` exactly when `A = ∅`. -/
def semialgDim {σ : Type} (A : Set (σ → ℝ)) : WithBot ℕ∞ :=
  ringKrullDim (MvPolynomial σ ℝ ⧸ MvPolynomial.vanishingIdeal ℝ A)

end

end Supplement

end BenignDegen


