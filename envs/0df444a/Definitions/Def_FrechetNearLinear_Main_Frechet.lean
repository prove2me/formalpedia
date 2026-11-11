-- Prove2me | Definitions.Def_FrechetNearLinear_Main_Frechet
-- name    : FrechetNearLinear_Main_Frechet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:35:13.202118+00:00
-- url     : https://prove2.me/theorems/dfe3b71a-5441-4fb8-8096-a3fe5d13d224
-- title:
--   Polygonal curves, matchings, and the continuous and discrete Fréchet distances (§1, §2)
-- statement:
--   A **polygonal curve** with $n\ge 1$ vertices $p_0,\dots,p_{n-1}\in\mathbb R^d$ is given by its vertex sequence `P : Fin n → E d`, where $E_d=\mathbb R^d$ with the Euclidean norm. Consecutive vertices may coincide. It is parameterized over $[0,n-1]$: for $x=i+\lambda$ with $i=\lfloor x\rfloor$ and $0\le\lambda<1$,
--   $$P(x)=(1-\lambda)\,p_i+\lambda\,p_{i+1},$$
--   so $P(i)=p_i$ and $P$ is affine on each $[i,i+1]$ (`curvePt`; `vtx P i` is $p_i$, with indices past $n-1$ read as $n-1$).
--
--   A **matching** of $P$ (with $n$ vertices) and $Q$ (with $m$ vertices) is a pair of continuous nondecreasing maps $\alpha,\beta:[0,1]\to\mathbb R$ with $\alpha(0)=0$, $\alpha(1)=n-1$, $\beta(0)=0$, $\beta(1)=m-1$. Its **cost** is $\max_{t\in[0,1]}\|P(\alpha(t))-Q(\beta(t))\|$, and the **Fréchet distance** is
--   $$d_F(P,Q)=\inf_{(\alpha,\beta)}\ \max_{t\in[0,1]}\|P(\alpha(t))-Q(\beta(t))\|.$$
--
--   A **discrete matching** is a sequence of index pairs $(i_0,j_0),\dots,(i_\ell,j_\ell)$ with $(i_0,j_0)=(0,0)$, $(i_\ell,j_\ell)=(n-1,m-1)$ and every step in $\{(1,0),(0,1),(1,1)\}$; its cost is $\max_k\|p_{i_k}-q_{j_k}\|$, and the **discrete Fréchet distance** $\tilde d_F(P,Q)$ is the minimum cost over all discrete matchings.
--
--   **Formalization Note** The paper's parameterization $\rho:[0,1]\to P$ that never moves backwards along $P$ is written through the parameter $\alpha$ with $\rho=P\circ\alpha$; neither map has to be strictly increasing. $d_F$ is `⨅` over the type of matchings, which is nonempty for $n,m\ge1$, with costs $\ge 0$; $\tilde d_F$ is `sInf` of a finite nonempty set of costs, hence a minimum. For $n=0$ or $m=0$ both are the junk value $0$; every theorem assumes $1\le m\le n$.
-- source:
--   Huang, Wang, Zhang, Constant Approximation of Fréchet Distance in Near-Linear Time, STOC 2027 submission (manuscript sha256 08be7e65…dd2d), p. 1, §1 and p. 3, §2

import Mathlib

/-!
# Polygonal curves, matchings, and the continuous and discrete Fréchet distances

Huang, Wang, Zhang, *Constant Approximation of Fréchet Distance in Near-Linear Time*, STOC 2027
submission (manuscript sha256 08be7e65…dd2d), p. 1 (§1) and p. 3 (§2).

A polygonal curve with `n` vertices `p₀, …, p_{n-1}` in `ℝ^d` is a map `P : Fin n → E d`
(`E d = EuclideanSpace ℝ (Fin d)`); consecutive vertices may coincide. It is parameterized over
`[0, n - 1]`: `curvePt P i = pᵢ` and `curvePt P` is affine on every `[i, i + 1]`.

A matching is a pair of continuous nondecreasing maps `α : [0,1] → ℝ`, `β : [0,1] → ℝ` with
`α 0 = 0`, `α 1 = n - 1`, `β 0 = 0`, `β 1 = m - 1` (so `α` ranges over `[0, n - 1]` and `β`
over `[0, m - 1]`); its cost is the largest distance between matched points, and the Fréchet
distance is the infimum of the costs. The discrete Fréchet distance is the minimum, over
sequences of vertex-index pairs from `(0,0)` to `(n-1, m-1)` advancing by `(1,0)`, `(0,1)` or
`(1,1)`, of the largest distance between paired vertices.
-/

namespace FrechetNearLinear.Main

/-- Euclidean space `ℝ^d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The `i`-th vertex of `P`, with indices beyond `n - 1` read as `n - 1` (and `0 : E d` for the
empty curve; every statement assumes `1 ≤ n`). -/
noncomputable def vtx {d n : ℕ} (P : Fin n → E d) (i : ℕ) : E d :=
  if h : 0 < n then P ⟨min i (n - 1), by omega⟩ else 0

/-- The polygonal curve of `P` parameterized over `[0, n - 1]`: for `x = i + λ` with `i = ⌊x⌋`,
`0 ≤ λ < 1`, `P(x) = (1 - λ) pᵢ + λ p_{i+1}`; in particular `P(i) = pᵢ` and `P(n - 1) = p_{n-1}`.
(Values outside `[0, n - 1]` are never used: matchings stay inside the parameter range.) -/
noncomputable def curvePt {d n : ℕ} (P : Fin n → E d) (x : ℝ) : E d :=
  (1 - (x - (⌊x⌋₊ : ℝ))) • vtx P ⌊x⌋₊ + (x - (⌊x⌋₊ : ℝ)) • vtx P (⌊x⌋₊ + 1)

/-- A matching of a curve with `n` vertices and a curve with `m` vertices, through parameters:
continuous nondecreasing `α, β` on `[0,1]` from `(0, 0)` to `(n - 1, m - 1)`. Neither map needs
to be strictly increasing. -/
structure Matching (n m : ℕ) where
  /-- The parameter on the first curve. -/
  α : unitInterval → ℝ
  /-- The parameter on the second curve. -/
  β : unitInterval → ℝ
  cont_α : Continuous α
  cont_β : Continuous β
  mono_α : Monotone α
  mono_β : Monotone β
  α_zero : α 0 = 0
  α_one : α 1 = (n : ℝ) - 1
  β_zero : β 0 = 0
  β_one : β 1 = (m : ℝ) - 1

/-- The cost of a matching: `max_{t ∈ [0,1]} ‖P(α t) - Q(β t)‖` (a supremum of a continuous
function over the compact `[0,1]`, hence attained). -/
noncomputable def Matching.cost {d n m : ℕ} (P : Fin n → E d) (Q : Fin m → E d)
    (μ : Matching n m) : ℝ :=
  ⨆ t : unitInterval, ‖curvePt P (μ.α t) - curvePt Q (μ.β t)‖

/-- The Fréchet distance `d_F(P, Q)`: the infimum of the costs of all matchings. For
`n, m ≥ 1` the set of matchings is nonempty and every cost is `≥ 0`. -/
noncomputable def frechetDist {d n m : ℕ} (P : Fin n → E d) (Q : Fin m → E d) : ℝ :=
  ⨅ μ : Matching n m, μ.cost P Q

/-- A discrete matching (coupling): a sequence of vertex-index pairs starting at `(0, 0)`, ending
at `(n - 1, m - 1)`, each step one of `(1, 0)`, `(0, 1)`, `(1, 1)`. -/
def IsCoupling (n m : ℕ) (c : List (ℕ × ℕ)) : Prop :=
  c.head? = some (0, 0) ∧ c.getLast? = some (n - 1, m - 1) ∧
    c.IsChain (fun a b => b = (a.1 + 1, a.2) ∨ b = (a.1, a.2 + 1) ∨ b = (a.1 + 1, a.2 + 1))

/-- The cost of a discrete matching: the largest distance `‖p_i - q_j‖` over its pairs. -/
noncomputable def couplingCost {d n m : ℕ} (P : Fin n → E d) (Q : Fin m → E d)
    (c : List (ℕ × ℕ)) : ℝ :=
  (c.map fun ij => ‖vtx P ij.1 - vtx Q ij.2‖).foldr max 0

/-- The discrete Fréchet distance `d̃_F(P, Q)`: the minimum cost over all discrete matchings (a
finite nonempty set of values when `n, m ≥ 1`). -/
noncomputable def discreteFrechetDist {d n m : ℕ} (P : Fin n → E d) (Q : Fin m → E d) : ℝ :=
  sInf {u : ℝ | ∃ c : List (ℕ × ℕ), IsCoupling n m c ∧ u = couplingCost P Q c}

end FrechetNearLinear.Main


