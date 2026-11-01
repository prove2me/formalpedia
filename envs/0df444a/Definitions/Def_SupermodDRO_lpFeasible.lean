-- Prove2me | Definitions.Def_SupermodDRO_lpFeasible
-- name    : SupermodDRO_lpFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:31.588991+00:00
-- url     : https://prove2.me/theorems/cf933e80-c3ad-4c45-8537-28ba40d935c8
-- title:
--   Constraints, inner value $f(x)$ and optimal value of the linear program (6)
-- statement:
--   Let $z^{k,1},\dots,z^{k,2n+1}$, $p^k$ be the output of Algorithm 1 for scenario $k$. The linear program (6) is
--   $$
--   \begin{aligned}
--   \min\ & a^\top x+\nu^\top l\\
--   \text{s.t. }& R_k^\top l\ \ge\ \sum_{i\in[2n+1]}p_i^k\,b^\top y^{k,i}, && k\in[K],\\
--   & Wx+Uy^{k,i}\ge Vz^{k,i}+v^0, && k\in[K],\ i\in[2n+1],\\
--   & l\ge0,\ x\in\mathcal X,
--   \end{aligned}
--   $$
--   where $R_k$ is the $k$-th column of $R$. For fixed $x$, $f(x)=\min\{\nu^\top l\}$ over the $(l,y)$ satisfying the first three constraint lines, and the optimal value of (6) is the minimum over $x\in\mathcal X$ as well.
--
--   **Formalization Note** `lpFeasible` is the constraint system in $(l,y)$ at a fixed $x$ (without $x\in\mathcal X$). Both minima are infima in $[-\infty,+\infty]$; $f(x)=+\infty$ when the constraints are infeasible at $x$.
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), Theorem 1, (6), p.12; f(x), Proof of Theorem 1 (App. C.4), p.47

import Mathlib
import Definitions.Def_SupermodDRO_Data
import Definitions.Def_SupermodDRO_algorithm1

open Matrix

namespace SupermodDRO

/-- **The constraints of the linear program (6) in `(l, y)` at a fixed `x`.** Long, Qi & Zhang,
*Supermodularity in Two-Stage Distributionally Robust Optimization*, author manuscript (June 2022),
Theorem 1, (6), p.12:
"R_k⊤ l ≥ Σ_{i∈[2n+1]} pᵢᵏ b⊤y^{k,i}, k ∈ [K]; Wx + Uy^{k,i} ≥ Vz^{k,i} + v⁰, k ∈ [K], i ∈ [2n+1];
l ≥ 0", where `z^{k,1}, …, z^{k,2n+1}, pᵏ` is the output of Algorithm 1 with input `𝓕ᵏ` (p.12).

`R_k` is the `k`-th column of `R`, so `R_k⊤ l = (R⊤ l)_k`. The variables are `l ∈ ℝˢ` and
`y : [K] × [2n+1] → ℝᵐ`. The constraint `x ∈ 𝒳` of (6) is not part of this predicate.

**Formalization Note** Indices are 0-based; the support points and weights are
`algorithm1Point` and `algorithm1Weight` of scenario `k` (with the degenerate-coordinate masses
`(1, 0, 0)`, see `levelMass`). -/
def lpFeasible {l m r n K s : ℕ} (D : Data l m r n K s) (x : Fin l → ℝ) (lv : Fin s → ℝ)
    (y : Fin K → Fin (2 * n + 1) → Fin m → ℝ) : Prop :=
  0 ≤ lv ∧
    (∀ k, ∑ i, algorithm1Weight (D.μ k) (D.δ k) (D.zl k) (D.zu k) i * (D.b ⬝ᵥ y k i) ≤
      (D.Rᵀ *ᵥ lv) k) ∧
    ∀ k i, D.V *ᵥ algorithm1Point (D.μ k) (D.δ k) (D.zl k) (D.zu k) i + D.v0 ≤
      D.W *ᵥ x + D.U *ᵥ y k i

/-- **The value `f(x)` of (6) at a fixed `x`.** Long, Qi & Zhang, author manuscript (June 2022),
Proof of Theorem 1 (App. C.4), p.47: "f(x) = min ν⊤l s.t. R_k⊤l ≥ Σ pᵢᵏ b⊤y^{k,i}, k ∈ [K];
Wx + Uy^{k,i} ≥ Vz^{k,i} + v⁰; l ≥ 0".

**Formalization Note** Infimum in `EReal`: `⊤` when the constraints are infeasible at `x`. -/
noncomputable def lpInnerValue {l m r n K s : ℕ} (D : Data l m r n K s) (x : Fin l → ℝ) : EReal :=
  ⨅ (lv : Fin s → ℝ) (y : Fin K → Fin (2 * n + 1) → Fin m → ℝ) (_ : lpFeasible D x lv y),
    ((D.ν ⬝ᵥ lv : ℝ) : EReal)

/-- **The optimal value of the linear program (6).** Long, Qi & Zhang, author manuscript (June
2022), Theorem 1, (6), p.12: "min a⊤x + ν⊤l" over `x ∈ 𝒳` and `(l, y)` satisfying the constraints
`lpFeasible`.

**Formalization Note** Infimum in `EReal` (`⊤` if (6) is infeasible, `⊥` if unbounded). -/
noncomputable def lpValue {l m r n K s : ℕ} (D : Data l m r n K s) : EReal :=
  ⨅ (x ∈ D.X) (lv : Fin s → ℝ) (y : Fin K → Fin (2 * n + 1) → Fin m → ℝ)
    (_ : lpFeasible D x lv y), ((D.a ⬝ᵥ x + D.ν ⬝ᵥ lv : ℝ) : EReal)

end SupermodDRO


