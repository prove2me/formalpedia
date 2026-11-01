-- Prove2me | Definitions.Def_FWIterates_sketchPoints
-- name    : FWIterates_sketchPoints
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:29.255689+00:00
-- url     : https://prove2.me/theorems/0294b43b-036e-4001-91fb-791e89710a09
-- title:
--   §3.1, pp.5–6 — the hexagonal sketches $P_k$, the triangle $C$, the vertices $V_k$ and the choice of $(u_k)$
-- statement:
--   Let $e_1=(1,0)$, $e_2=(0,1)$, $A_0=(-1/2,0)$, $B_0=(-1/4,3/4)$, $C_0=(1/4,3/4)$, $D_0=(1/2,0)$ and, for all $k\in\mathbb N$,
--   $$
--   \begin{aligned}
--   A_{k+1}&=\Big(-\tfrac14+\tfrac{\langle B_{k+1},e_2\rangle}{\langle B_k,e_2\rangle}\big(\langle A_k,e_1\rangle+\tfrac14\big),0\Big),&
--   B_{k+1}&=\Big(-\tfrac14,\tfrac35\langle C_k,e_2\rangle\Big),\\
--   C_{k+1}&=\Big(\tfrac14,\tfrac35\langle B_k,e_2\rangle\Big),&
--   D_{k+1}&=\Big(\tfrac14+\tfrac{\langle C_{k+1},e_2\rangle}{\langle C_k,e_2\rangle}\big(\langle D_k,e_1\rangle-\tfrac14\big),0\Big).
--   \end{aligned}
--   $$
--   The **sketches** are $\mathcal P_k=\operatorname{conv}\{A_k,B_k,C_k,D_k,-D_k,-C_k,-B_k,-A_k\}$, the **constraint set** is $\mathcal C=\operatorname{conv}\{(-1,0),(0,1),(1,0)\}$, and the **vertex sequence** is $V_k=C_k$ for even $k$ and $V_k=B_k$ for odd $k$.
--
--   A sequence of unit vectors $(u_k)$ is a **direction choice** (p.6) if $u_0\in\mathcal K_{\mathcal P_0}C_0$ and, for all $k\ge1$,
--   $$
--   \begin{cases}u_k\in\mathcal K_{\mathcal P_k}C_k\text{ and }\langle C_k-B_{k-1},u_k\rangle=0&\text{if $k$ is even;}\\ u_k\in\mathcal K_{\mathcal P_k}B_k\text{ and }\langle B_k-C_{k-1},u_k\rangle=0&\text{if $k$ is odd.}\end{cases}
--   $$
--
--   These are the data of Counterexample 3.5.
--
--   **Formalization Note** The recursion is transcribed literally (`sketchPoints k = (A_k, B_k, C_k, D_k)`); the divisors equal $(3/4)(3/5)^k>0$. Unit length of $u_k$ is Theorem 3.1's $(u_k)\in\mathbb S^{\mathbb N}$. The module also declares `e₁`, `e₂`, `sketchA`–`sketchD`, `sketchPolygon`, `triangle`, `sketchVertex` and `IsDirectionChoice`.
-- source:
--   Bolte, Combettes & Pauwels, The Iterates of the Frank-Wolfe Algorithm May Not Converge, arXiv:2202.08711v1, §3.1, p.5 (A₀, B₀, C₀, D₀, the recursions, Pₖ, C) and p.6 (the choice of (uₖ), x_t = C_t or B_t)

import Mathlib
import Definitions.Def_FWIterates_admissibleCone

open scoped RealInnerProductSpace Pointwise

namespace FWIterates

noncomputable section

/-- The canonical vector `e₁ = (1, 0)` of `ℝ²` (arXiv:2202.08711v1, §2.1, p.2). -/
def e₁ : EuclideanSpace ℝ (Fin 2) := !₂[1, 0]

/-- The canonical vector `e₂ = (0, 1)` of `ℝ²` (arXiv:2202.08711v1, §2.1, p.2). -/
def e₂ : EuclideanSpace ℝ (Fin 2) := !₂[0, 1]

/-- **The vertices of the sketches of §3.1** (arXiv:2202.08711v1, §3.1, p.5):
`sketchPoints k = (A_k, B_k, C_k, D_k)` with `A₀ = (−1/2, 0)`, `B₀ = (−1/4, 3/4)`,
`C₀ = (1/4, 3/4)`, `D₀ = (1/2, 0)` and, for all `k`,

* `A_{k+1} = (−1/4 + (⟨B_{k+1}, e₂⟩/⟨B_k, e₂⟩)(⟨A_k, e₁⟩ + 1/4), 0)`,
* `B_{k+1} = (−1/4, (3/5)⟨C_k, e₂⟩)`,
* `C_{k+1} = (1/4, (3/5)⟨B_k, e₂⟩)`,
* `D_{k+1} = (1/4 + (⟨C_{k+1}, e₂⟩/⟨C_k, e₂⟩)(⟨D_k, e₁⟩ − 1/4), 0)`.

**Formalization Note** The recursion is transcribed literally. The divisors `⟨B_k, e₂⟩` and
`⟨C_k, e₂⟩` equal `(3/4)(3/5)^k > 0`, so Lean's `x/0 = 0` never applies. -/
def sketchPoints : ℕ → EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ×
    EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)
  | 0 => (!₂[-1/2, 0], !₂[-1/4, 3/4], !₂[1/4, 3/4], !₂[1/2, 0])
  | k + 1 =>
    let A := (sketchPoints k).1
    let B := (sketchPoints k).2.1
    let C := (sketchPoints k).2.2.1
    let D := (sketchPoints k).2.2.2
    let B' : EuclideanSpace ℝ (Fin 2) := !₂[-1/4, 3/5 * ⟪C, e₂⟫]
    let C' : EuclideanSpace ℝ (Fin 2) := !₂[1/4, 3/5 * ⟪B, e₂⟫]
    (!₂[-1/4 + ⟪B', e₂⟫ / ⟪B, e₂⟫ * (⟪A, e₁⟫ + 1/4), 0], B', C',
      !₂[1/4 + ⟪C', e₂⟫ / ⟪C, e₂⟫ * (⟪D, e₁⟫ - 1/4), 0])

/-- `A_k` of §3.1 (arXiv:2202.08711v1, p.5). -/
def sketchA (k : ℕ) : EuclideanSpace ℝ (Fin 2) := (sketchPoints k).1

/-- `B_k` of §3.1 (arXiv:2202.08711v1, p.5). -/
def sketchB (k : ℕ) : EuclideanSpace ℝ (Fin 2) := (sketchPoints k).2.1

/-- `C_k` of §3.1 (arXiv:2202.08711v1, p.5). -/
def sketchC (k : ℕ) : EuclideanSpace ℝ (Fin 2) := (sketchPoints k).2.2.1

/-- `D_k` of §3.1 (arXiv:2202.08711v1, p.5). -/
def sketchD (k : ℕ) : EuclideanSpace ℝ (Fin 2) := (sketchPoints k).2.2.2

/-- The sketch `P_k = conv{A_k, B_k, C_k, D_k, −D_k, −C_k, −B_k, −A_k}` of §3.1
(arXiv:2202.08711v1, p.5). -/
def sketchPolygon (k : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  convexHull ℝ {sketchA k, sketchB k, sketchC k, sketchD k,
    -sketchD k, -sketchC k, -sketchB k, -sketchA k}

/-- The constraint set `C = conv{(−1, 0), (0, 1), (1, 0)}` of §3.1 (arXiv:2202.08711v1, p.5). -/
def triangle : Set (EuclideanSpace ℝ (Fin 2)) :=
  convexHull ℝ {!₂[-1, 0], !₂[0, 1], !₂[1, 0]}

/-- The vertex sequence of §3.1 (arXiv:2202.08711v1, p.6): `V_k = C_k` for even `k` and
`V_k = B_k` for odd `k`, the vertices at which the directions `u_k` are prescribed (`u_k ∈ K_{P_k}C_k`
for even `k`, `u_k ∈ K_{P_k}B_k` for odd `k`) and the iterates of the trajectory display. -/
def sketchVertex (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  if Even k then sketchC k else sketchB k

/-- **The choice of `(u_k)` of §3.1** (arXiv:2202.08711v1, display "The construction allows to
choose (uk)", p.6): every `u_k` is a unit vector, `u₀ ∈ K_{P₀}C₀` and, for all `k ≥ 1`,
`u_k ∈ K_{P_k}C_k` and `⟨C_k − B_{k−1}, u_k⟩ = 0` if `k` is even, and `u_k ∈ K_{P_k}B_k` and
`⟨B_k − C_{k−1}, u_k⟩ = 0` if `k` is odd.

**Formalization Note** `‖u_k‖ = 1` is Theorem 3.1's `(u_k) ∈ S^ℕ`, the role these directions
play. The cone is the printed closed cone `K = N ∩ (−T)`; `k − 1` is natural subtraction, used only
for `k ≥ 1`. -/
def IsDirectionChoice (u : ℕ → EuclideanSpace ℝ (Fin 2)) : Prop :=
  (∀ k, ‖u k‖ = 1) ∧ u 0 ∈ admissibleCone (sketchPolygon 0) (sketchC 0) ∧
    ∀ k, 1 ≤ k →
      (Even k → u k ∈ admissibleCone (sketchPolygon k) (sketchC k) ∧
        ⟪sketchC k - sketchB (k - 1), u k⟫ = 0) ∧
      (Odd k → u k ∈ admissibleCone (sketchPolygon k) (sketchB k) ∧
        ⟪sketchB k - sketchC (k - 1), u k⟫ = 0)

end

end FWIterates


