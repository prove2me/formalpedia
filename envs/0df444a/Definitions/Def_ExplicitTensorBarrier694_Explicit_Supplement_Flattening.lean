-- Prove2me | Definitions.Def_ExplicitTensorBarrier694_Explicit_Supplement_Flattening
-- name    : ExplicitTensorBarrier694_Explicit_Supplement_Flattening
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:38:25.368958+00:00
-- url     : https://prove2.me/theorems/a58a53b7-f7ae-4ac9-bd69-e0a42713aaa2
-- title:
--   Linear flattenings: $\rho(L)$, potency $\mathrm{Pot}(L)$, optimal potency $\Pi(n)$, and Schatten norms
-- statement:
--   Let $n\ge0$ and let $F$ be a map from tensors $T\in(\mathbb C^n)^{\otimes3}$ to complex matrices (rows and columns indexed by finite sets). Following equation (1.2) of the source define
--
--   $$\rho(F)=\max_{x,y,z\in\mathbb C^n}\operatorname{rank}F(x\otimes y\otimes z),\qquad \mathrm{Pot}(F)=\frac{\max_T\operatorname{rank}F(T)}{\rho(F)}.$$
--
--   Both maxima exist: the rank sets are nonempty and bounded by the number of columns. A **linear flattening** is a nonzero $\mathbb C$-linear map $L:(\mathbb C^n)^{\otimes3}\to\mathrm{Mat}_{u,v}(\mathbb C)$ with arbitrary positive $u,v$; for it $\rho(L)\ge1$ because pure tensors span. The **optimal potency** is
--
--   $$\Pi(n)=\sup\{\mathrm{Pot}(L): u,v\ge1,\ L\neq0\text{ linear}\},$$
--
--   with no restriction on $u,v$. The module also defines $M(x,y,z)=\sum_{ijk}x_iy_jz_kM_{ijk}$ for a family of $r\times r$ matrices, the squared Schatten 2-norm $\|X\|_2^2=\sum_{a,b}|X_{ab}|^2=\operatorname{tr}(XX^\dagger)$ and the fourth power of the Schatten 4-norm $\|X\|_4^4=\operatorname{tr}((X^\dagger X)^2)=\sum_j\sigma_j(X)^4$.
--
--   These are the objects of Theorem 1.2 and its supporting Lemmas 4.1 and 4.2.
--
--   **Formalization Note** $\Pi(n)$ is an `EReal` supremum, so an unbounded potency set would give $+\infty$ and not a junk real value. $\rho$ and $\mathrm{Pot}$ are defined for maps into matrices over arbitrary finite index types, so the Koszul matrices of the published Koszul definition (indexed by exterior bases) use the same $\rho$ and $\mathrm{Pot}$; for the Koszul flattening $\rho$ coincides with the published `koszulRho`. The trace in $\|X\|_4^4$ is of a positive semidefinite matrix and its real part is taken.
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), equation (1.2) and the definition of Π(n), p.2; Schatten norms p.5; §4 pp.11–12 (PDF same); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Tensors

open scoped BigOperators Matrix

namespace ExplicitTensorBarrier694.Explicit.Supplement

open ExplicitTensorBarrier694.Explicit

/-- ρ(L), equation (1.2), p.2: the largest rank of `F (x ⊗ y ⊗ z)` over ALL pure tensors
(zero factors allowed). The set is nonempty and bounded by the number of columns, so the
natural-number supremum is an attained maximum. Defined for any map to matrices over
finite index types, so that Koszul matrices (indexed by exterior bases) are covered by
the same definition as `Mat_{u,v}`-valued flattenings. -/
noncomputable def flatRho {n : ℕ} {ι κ : Type*} [Fintype κ]
    (F : Tensor n n n → Matrix ι κ ℂ) : ℕ :=
  sSup {r : ℕ | ∃ x y z : Fin n → ℂ, (F (pure x y z)).rank = r}

/-- max_T rank F(T), equation (1.2), p.2, over ALL tensors T; an attained maximum
(nonempty, bounded by the number of columns). -/
noncomputable def flatMaxRank {n : ℕ} {ι κ : Type*} [Fintype κ]
    (F : Tensor n n n → Matrix ι κ ℂ) : ℕ :=
  sSup {r : ℕ | ∃ T : Tensor n n n, (F T).rank = r}

/-- Potency Pot(F) = (max_T rank F(T)) / ρ(F), equation (1.2), p.2. For a nonzero linear
flattening ρ ≥ 1 (pure tensors span), so the real division is genuine. -/
noncomputable def potency {n : ℕ} {ι κ : Type*} [Fintype κ]
    (F : Tensor n n n → Matrix ι κ ℂ) : ℝ :=
  (flatMaxRank F : ℝ) / (flatRho F : ℝ)

/-- Optimal potency Π(n), p.2: the supremum of Pot(L) over ALL nonzero ℂ-linear maps
L : (ℂⁿ)^{⊗3} → Mat_{u,v}(ℂ) and ALL output dimensions u, v (no restriction). Computed
in `EReal`, so an unbounded family would give `⊤` rather than a junk real value. -/
noncomputable def optimalPotency (n : ℕ) : EReal :=
  ⨆ (u : ℕ) (v : ℕ) (L : Tensor n n n →ₗ[ℂ] Matrix (Fin u) (Fin v) ℂ) (_ : L ≠ 0),
    ((potency (⇑L) : ℝ) : EReal)

/-- The matrix Σ_{ijk} x_i y_j z_k M_{ijk} (no complex conjugation), §4, pp.11–12. -/
def coeffMatrix {n r : ℕ} (M : Fin n → Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (x y z : Fin n → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  ∑ i, ∑ j, ∑ k, (x i * y j * z k) • M i j k

/-- Squared Schatten 2-norm (Hilbert–Schmidt): ‖X‖₂² = tr(X X†) = Σ |X_ab|², p.5. -/
noncomputable def schatten2Sq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ι κ ℂ) : ℝ :=
  ∑ a, ∑ b, ‖X a b‖ ^ 2

/-- Fourth power of the Schatten 4-norm: ‖X‖₄⁴ = Σ σ_j(X)⁴ = tr((X† X)²), p.5. The trace
is of a positive semidefinite matrix, hence real; its real part is taken. -/
noncomputable def schatten4Pow4 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ι κ ℂ) : ℝ :=
  (Matrix.trace ((Xᴴ * X) * (Xᴴ * X))).re

end ExplicitTensorBarrier694.Explicit.Supplement


