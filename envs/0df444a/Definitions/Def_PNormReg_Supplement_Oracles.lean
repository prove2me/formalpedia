-- Prove2me | Definitions.Def_PNormReg_Supplement_Oracles
-- name    : PNormReg_Supplement_Oracles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:52:39.392354+00:00
-- url     : https://prove2.me/theorems/e3e27989-6c30-4aa7-8028-f9ca4fea49ae
-- title:
--   The $\eta$-improvement oracle (Definition 1) and the $\ell_2$-$\ell_q$ game oracle (5)
-- statement:
--   Fix full column rank $A\in\mathbb R^{n\times d}$, $b\in\mathbb R^n$, $p\in[1,\infty]$ and $f_p(x)=\|Ax-b\|_p$. For $\eta>0$ and $\delta'\in(0,1)$, $\mathrm{ApproxImprovementOracle}(\eta,x,\delta')$ returns $\hat\Delta$ which, with probability at least $1-\delta'$, satisfies (4):
--
--   $$f_p(\hat\Delta+x)\le\eta^{-1}f_p(x)+\min_{\Delta\in B^d_{p,A}(2f_p(x))}f_p(\Delta+x),\qquad B^d_{p,A}(r)=\{\Delta:\|A\Delta\|_p\le r\}.$$
--
--   For $M\in\mathbb R^{n\times r}$, $c\in\mathbb R^n$ and $1/p+1/q=1$, game (5) is $\min_{x\in B^r_2}\max_{y\in B^n_q}y^\top(Mx-c)$, whose primal objective equals $\|Mx-c\|_p$. For accuracy $\alpha>0$ and failure $\delta_g\in(0,1)$ the game oracle returns, with probability at least $1-\delta_g$, an $\alpha$-additive approximate solution: $\hat x$ with $\|\hat x\|_2\le1$ and $\|M\hat x-c\|_p\le\min_{\|x\|_2\le1}\|Mx-c\|_p+\alpha$.
--
--   The first oracle is what Theorem 4 consumes and Theorem 6 implements; the second is what Theorem 6 consumes.
--
--   **Formalization Note** The minimum in (4) is written as "for every $\Delta$ in the ball". Both oracles read their query from real memory starting at the address in pointer register 0 (the game's column count $r$ from pointer register 1) and write the answer just after it. Outside the parameter range where the paper defines an oracle, its specification holds trivially.
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Definition 1 and (4), p.8; game (5), p.11; optimizer conventions, p.7

import Mathlib
import Definitions.Def_PNormReg_Supplement_Layouts
import Definitions.Def_PNormReg_Supplement_OracleMachine

open Matrix

namespace PNormReg

namespace Supplement

/-!
# The `η`-improvement oracle (Definition 1) and the `ℓ₂`-`ℓ_q` game oracle (5)

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*,
STOC 2027 submission (manuscript sha256 e335b2fa…): Definition 1 and (4), p.8; game (5), p.11;
optimizer conventions, p.7.

**Formalization Note.**
* Definition 1's minimum over `B^d_{p,A}(2f_p(x))` is written as `∀ Δ` in the ball (it is attained:
  the ball is compact for full column rank `A` and `f_p` is continuous).
* Game (5)'s primal objective `x ↦ max_{y ∈ B^n_q} y⊤(Mx − c)` is written as `∥Mx − c∥_p`, by the norm
  duality `max_{∥y∥_q ≤ 1} y⊤v = ∥v∥_p` (p.14), `1/p + 1/q = 1`. An `α`-additive approximate solution is a
  point `x̂ ∈ B^r_2` whose objective is at most the minimum over `B^r_2` plus `α` (p.7).
* A specification holds trivially on a query whose parameters are outside the range where the paper
  defines the oracle (`η > 0`, `δ ∈ (0, 1)`; for the game, accuracy `> 0`, failure in `(0, 1)`).
* Interfaces. Both oracles read their query from real memory from cell `a := p[0]` (pointer register
  `0`) on. Improvement oracle: `η, δ', x₁, …, x_d` in cells `a, a+1, a+2, …`; the answer `Δ` goes to
  cells `a+2+d, …, a+1+2d`. Game oracle: `r := max(p[1], 0)` (pointer register `1`), accuracy `α`,
  failure `δ_g`, then `M ∈ ℝ^{n×r}` row-major, then `c ∈ ℝ^n`, in cells `a, a+1, a+2, …`; the answer
  `x̂ ∈ ℝ^r` goes to the `r` cells after `c`. A query carries only these cells.
-/

/-- `Δ̂` satisfies (4) at `x`: `f_p(Δ̂ + x) ≤ η^{−1}f_p(x) + f_p(Δ + x)` for every `Δ` with
`∥AΔ∥_p ≤ 2f_p(x)`. -/
def ImproveGuarantee {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (pInv η : ℝ)
    (x Δhat : Fin d → ℝ) : Prop :=
  ∀ Δ : Fin d → ℝ, pNorm pInv (A *ᵥ Δ) ≤ 2 * fP A b pInv x →
    fP A b pInv (Δhat + x) ≤ η⁻¹ * fP A b pInv x + fP A b pInv (Δ + x)

/-- A query to the improvement oracle: `(η, δ', x)`. -/
abbrev ImproveQuery (d : ℕ) := ℝ × ℝ × (Fin d → ℝ)

/-- The first `d` entries of an answer, as a vector. -/
def ansVec (d : ℕ) (a : ℕ → ℝ) : Fin d → ℝ := fun j => a j

/-- Definition 1, `ApproxImprovementOracle(η, x, δ')`: for `η > 0`, `δ' ∈ (0, 1)`, the answer satisfies
(4) at `x`. The failure parameter of the query is `δ'`. -/
def improveSpec {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (pInv : ℝ)
    (q : ImproveQuery d) (a : ℕ → ℝ) : Prop :=
  0 < q.1 → 0 < q.2.1 → q.2.1 < 1 → ImproveGuarantee A b pInv q.1 q.2.2 (ansVec d a)

/-- The interface of the improvement oracle (see the module note). -/
noncomputable def improveIface (d : ℕ) : OracleIface (ImproveQuery d) where
  query s := (s.core.mem (s.core.ptrs 0), s.core.mem (s.core.ptrs 0 + 1),
    fun j => s.core.mem (s.core.ptrs 0 + 2 + (j : ℤ)))
  ansBase s := s.core.ptrs 0 + 2 + d
  ansLen _ := d

/-- A query to the game oracle: `(r, α, δ_g, data)`, `data` holding `M` row-major and then `c`. -/
abbrev GameQuery := ℕ × ℝ × ℝ × (ℕ → ℝ)

/-- The game matrix `M ∈ ℝ^{n×r}` of a query. -/
def gameMat (n : ℕ) (q : GameQuery) : Matrix (Fin n) (Fin q.1) ℝ :=
  fun i j => q.2.2.2 ((i : ℕ) * q.1 + j)

/-- The game vector `c ∈ ℝ^n` of a query. -/
def gameVec (n : ℕ) (q : GameQuery) : Fin n → ℝ :=
  fun i => q.2.2.2 (n * q.1 + i)

/-- `x̂ ∈ B^r_2` is an `α`-additive approximate solution of (5),
`min_{x ∈ B^r_2} max_{y ∈ B^n_q} y⊤(Mx − c) = min_{x ∈ B^r_2} ∥Mx − c∥_p`. -/
def GameSolution {n r : ℕ} (pInv α : ℝ) (M : Matrix (Fin n) (Fin r) ℝ) (c : Fin n → ℝ)
    (xhat : Fin r → ℝ) : Prop :=
  l2Norm xhat ≤ 1 ∧
    ∀ x : Fin r → ℝ, l2Norm x ≤ 1 → pNorm pInv (M *ᵥ xhat - c) ≤ pNorm pInv (M *ᵥ x - c) + α

/-- The game oracle: for accuracy `α > 0` and failure `δ_g ∈ (0, 1)`, the answer's first `r` entries
are an `α`-additive approximate solution of (5). The failure parameter of the query is `δ_g`. -/
def gameSpec (n : ℕ) (pInv : ℝ) (q : GameQuery) (a : ℕ → ℝ) : Prop :=
  0 < q.2.1 → 0 < q.2.2.1 → q.2.2.1 < 1 →
    GameSolution pInv q.2.1 (gameMat n q) (gameVec n q) (ansVec q.1 a)

/-- The interface of the game oracle (see the module note). -/
noncomputable def gameIface (n : ℕ) : OracleIface GameQuery where
  query s :=
    let r := (s.core.ptrs 1).toNat
    (r, s.core.mem (s.core.ptrs 0), s.core.mem (s.core.ptrs 0 + 1),
      fun k => if k < n * r + n then s.core.mem (s.core.ptrs 0 + 2 + (k : ℤ)) else 0)
  ansBase s := s.core.ptrs 0 + 2 + n * (s.core.ptrs 1).toNat + n
  ansLen q := q.1

end Supplement

end PNormReg


