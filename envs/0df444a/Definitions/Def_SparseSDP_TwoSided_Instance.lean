-- Prove2me | Definitions.Def_SparseSDP_TwoSided_Instance
-- name    : SparseSDP_TwoSided_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:10.216355+00:00
-- url     : https://prove2.me/theorems/f902609d-cd57-44c5-b750-2c8e9b1a210e
-- title:
--   The SDP pair (1), (2): instance, feasibility, strong duality within radii, and additive-$\varepsilon$ solutions
-- statement:
--   An **instance** consists of matrices $C,A_1,\dots,A_m$ and thresholds $b\in\mathbb R^m$, for the pair
--   $$
--   \mathrm{OPT}=\max_{X\succeq0}\{\operatorname{Tr}(CX):\operatorname{Tr}(A_jX)\le b_j\ \forall j\},\qquad
--   \mathrm{OPT}=\min_{y\ge0}\Big\{b^\top y:\sum_j y_jA_j\succeq C\Big\}.
--   $$
--
--   1. **Normalized**: $C,A_j$ are $s$-row-sparse Hermitian matrices of operator norm at most one, with $1\le s\le n$ and $m\ge1$.
--   2. **Strong duality within radii** $R,r$: $\mathrm{OPT}$ is the primal maximum and the dual minimum, attained by an optimal $X^\star$ with $\operatorname{Tr}X^\star\le R$ and an optimal $y^\star$ with $\|y^\star\|_1\le r$.
--   3. **Additive-$\varepsilon$ solution** (p. 1): $\hat X\succeq0$, $\operatorname{Tr}\hat X\le R$, $\operatorname{Tr}(C\hat X)\ge\mathrm{OPT}-\varepsilon$, and $\operatorname{Tr}(A_j\hat X)\le b_j+\varepsilon/r$ for every $j$.
--   4. A list of vectors $L$ represents the matrix $\sum_{v\in L}vv^\dagger$, the implicit output of the solver.
--   5. The **capped instance** replaces each $b_j$ by $\min(b_j,R)$ (§2.6.1).
--
--   This is the problem of the whole mission.
--
--   **Formalization Note** $\mathrm{OPT}$ is a real number with `IsGreatest` and `IsLeast`, so no supremum is involved. The scalar field is $\mathbb C$ for the input and $\mathbb R$ for the realified instance.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, §1, Eqs. (1), (2), p. 1; §2.6.1, p. 18

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_gap

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace SparseSDP.TwoSided

/-- SDP data: `C, A₁, …, A_m` and thresholds `b`, for the primal (1) and the dual (2).

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Eqs. (1), (2), p. 1.

**Formalization Note.** The scalar field `𝕜` is `ℂ` for the input of the paper and `ℝ` for the
realified instance of Appendix A. -/
structure Instance (𝕜 : Type*) (n m : ℕ) where
  /-- The objective matrix `C`. -/
  C : Matrix (Fin n) (Fin n) 𝕜
  /-- The constraint matrices `A₁, …, A_m`. -/
  A : Fin m → Matrix (Fin n) (Fin n) 𝕜
  /-- The thresholds `b₁, …, b_m`. -/
  b : Fin m → ℝ

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}

/-- The normalization of §1, p. 1: `C, Aⱼ` are `s`-row-sparse Hermitian matrices of operator norm at
most one, with the convention `1 ≤ s ≤ n` of Definition 2.1 (p. 15) and `m ≥ 1`. -/
def Instance.Normalized [DecidableEq 𝕜] (I : Instance 𝕜 n m) (s : ℕ) : Prop :=
  I.C.IsHermitian ∧ (∀ j, (I.A j).IsHermitian) ∧ RowSparse I.C s ∧ (∀ j, RowSparse (I.A j) s) ∧
    ‖I.C‖ ≤ 1 ∧ (∀ j, ‖I.A j‖ ≤ 1) ∧ 1 ≤ s ∧ s ≤ n ∧ 1 ≤ m

/-- Feasibility for the primal (1): `X ⪰ 0` and `Tr(AⱼX) ≤ bⱼ` for all `j`. -/
def PrimalFeasible (I : Instance 𝕜 n m) (X : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  X.PosSemidef ∧ ∀ j, hs (I.A j) X ≤ I.b j

/-- Feasibility for the dual (2): `y ≥ 0` and `∑ⱼ yⱼAⱼ ⪰ C`. -/
def DualFeasible (I : Instance 𝕜 n m) (y : Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ (adj I.A y - I.C).PosSemidef

/-- Strong duality with optimal solutions inside the radii (§1, p. 1; §2.6.1, p. 18): `OPT` is the
maximum of the primal and the minimum of the dual, and there are optimal `X⋆`, `y⋆` with
`Tr X⋆ ≤ R` and `‖y⋆‖₁ ≤ r`.

**Formalization Note.** `OPT` is carried by `IsGreatest`/`IsLeast`, so no `sSup` is involved. -/
def StrongDuality (I : Instance 𝕜 n m) (R r OPT : ℝ) : Prop :=
  IsGreatest {v | ∃ X, PrimalFeasible I X ∧ v = hs I.C X} OPT ∧
  IsLeast {v | ∃ y, DualFeasible I y ∧ v = ∑ j, I.b j * y j} OPT ∧
  (∃ X, PrimalFeasible I X ∧ hs I.C X = OPT ∧ RCLike.re (Matrix.trace X) ≤ R) ∧
  (∃ y, DualFeasible I y ∧ ∑ j, I.b j * y j = OPT ∧ ∑ j, y j ≤ r)

/-- "Solving the SDP to additive error `ε`" (p. 1): `X̂ ⪰ 0`, `Tr X̂ ≤ R`, `Tr(CX̂) ≥ OPT − ε` and
`Tr(AⱼX̂) ≤ bⱼ + ε/r` for every `j`. -/
def IsApproxSolution (I : Instance 𝕜 n m) (R r ε OPT : ℝ)
    (X : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  X.PosSemidef ∧ RCLike.re (Matrix.trace X) ≤ R ∧ OPT - ε ≤ hs I.C X ∧
    ∀ j, hs (I.A j) X ≤ I.b j + ε / r

/-- The matrix represented by a list of rank-one factors, `X̂ = ∑_{v ∈ L} v v†` (the implicit output
of Corollary 7.11, p. 63). -/
noncomputable def factorSum (L : List (Fin n → 𝕜)) : Matrix (Fin n) (Fin n) 𝕜 :=
  (L.map fun v => vecMulVec v (star v)).sum

/-- The capped instance of §2.6.1, p. 18: each `bⱼ` is replaced by `min(bⱼ, R)`. -/
noncomputable def capInst (I : Instance 𝕜 n m) (R : ℝ) : Instance 𝕜 n m :=
  { I with b := fun j => min (I.b j) R }

end SparseSDP.TwoSided


