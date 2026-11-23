-- Prove2me | Definitions.Def_BHTOpinion_Approx_Supplement_Weighted
-- name    : BHTOpinion_Approx_Supplement_Weighted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:53:33.464809+00:00
-- url     : https://prove2.me/theorems/4464a345-ce5e-4d69-9ca4-4efcefb9e423
-- title:
--   Weighted system (2.4), cluster weights W_A and perturbing-agent stability (§2.2)
-- statement:
--   Fix $m$ agents with real opinions and real weights $w_1,\dots,w_m$. The **weighted system (2.4)** is the integral equation
--   $$
--   x_i(t)=x_i(0)+\int_0^t\sum_{j:\,|x_i(\tau)-x_j(\tau)|<1} w_j\,\bigl(x_j(\tau)-x_i(\tau)\bigr)\,d\tau ,\qquad t\ge 0 .
--   $$
--   A **solution** is a trajectory $x:[0,\infty)\to\mathbb R^m$ that is continuous and satisfies this identity for every $t\ge0$ and every agent $i$. The interaction radius is strict ($<1$) and each summand carries the weight of the sending agent $j$, without normalization. With all weights equal to $1$ this is the unweighted system (2.1).
--
--   For an opinion vector $s\in\mathbb R^n$ and weights $w$, the **cluster** at a value $a$ is the set of agents with $s_i=a$, and its **weight** is
--   $$
--   W_a=\sum_{i:\,s_i=a} w_i .
--   $$
--
--   **Perturbing-agent stability.** Add a new agent of weight $\delta>0$ and initial opinion $q\in\mathbb R$ to the configuration $s$. Let $\Delta(\delta,s)$ be the supremum of $|x_i(t)-s_i|$ over every perturbing opinion $q$, every original agent $i$, every time $t\ge0$ and every solution $x$ of the weighted system started at the augmented configuration (uniqueness is not required). The configuration $s$ is **stable** if $\lim_{\delta\downarrow0}\Delta(\delta,s)=0$, i.e. for every $\varepsilon>0$ there is $\eta>0$ such that for every $\delta\in(0,\eta)$ all those displacements are at most $\varepsilon$.
--
--   These objects are the setting of Theorem 3, which characterizes the stable equilibria by their intercluster distances.
--
--   **Formalization Note** The augmented configuration lives on `Fin (n+1)`, the new agent is `Fin.last n` (via `Fin.snoc`), and original agents are `Fin.castSucc i`. Stability is written as the $\varepsilon$–$\eta$ form of the limit, which avoids the real supremum of a possibly unbounded or empty set; when no solution exists for some perturbation that perturbation imposes nothing, matching the supremum of an empty family of nonnegative numbers. The paragraph defining $\Delta$ says "solutions of the system (2.1)"; in its weighted setup (2.4), with the new agent of weight $\delta$, this is read as the weighted system. Solutions require interval integrability of the integrand, which excludes no continuous solution.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, Continuous-time average-preserving opinion dynamics with opinion-dependent communications, SIAM J. Control Optim. 48 (2010), DOI 10.1137/090766188, p. 5220 (PDF 7), Eq. (2.4), the paragraph defining cluster weight, and the paragraph defining Δ(δ, s̃) and stability

import Mathlib

namespace BHTOpinion.Approx.Supplement

/-- The right-hand side of the weighted system (2.4) (p. 5220) at the opinion profile
`y : Fin m → ℝ` with agent weights `w : Fin m → ℝ`, for agent `i`:
`∑_{j : |y_i − y_j| < 1} w_j (y_j − y_i)`. The neighbourhood is **strict** (`< 1`) and contains
`j = i`, whose term is `0`. The weight is that of the sending agent `j`; there is no
normalization. -/
noncomputable def weightedRhs {m : ℕ} (w : Fin m → ℝ) (y : Fin m → ℝ) (i : Fin m) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => |y i - y j| < 1), w j * (y j - y i)

/-- `x` is a solution of the weighted integral equation (2.4) (p. 5220) with weights `w`: `x` is
continuous on `[0, ∞)` and, for every `t ≥ 0` and every agent `i`, the integrand is integrable on
`[0, t]` and `x_i(t) = x_i(0) + ∫_0^t ∑_{j : |x_i(τ) − x_j(τ)| < 1} w_j (x_j(τ) − x_i(τ)) dτ`.
Time is `ℝ`; only the values of `x` at `t ≥ 0` enter. With `w ≡ 1` this is (2.1). -/
def IsWeightedSolution {m : ℕ} (w : Fin m → ℝ) (x : ℝ → Fin m → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ i : Fin m,
      IntervalIntegrable (fun τ => weightedRhs w (x τ) i) MeasureTheory.volume 0 t) ∧
    ∀ t : ℝ, 0 ≤ t → ∀ i : Fin m, x t i = x 0 i + ∫ τ in (0 : ℝ)..t, weightedRhs w (x τ) i

/-- The weight `W_A` of the cluster of the equilibrium vector `s` located at the opinion value `a`
(p. 5220): the sum of the weights of all agents `i` with `s_i = a`. -/
noncomputable def clusterWeight {n : ℕ} (w : Fin n → ℝ) (s : Fin n → ℝ) (a : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => s i = a), w i

/-- Perturbing-agent stability (p. 5220). The configuration `s` of `n` agents with weights `w` is
augmented by one new agent (index `Fin.last n`) of weight `δ` and arbitrary initial opinion `q`.
`s` is stable when `lim_{δ↓0} Δ(δ, s) = 0`, where `Δ(δ, s)` is the supremum of `|x_i(t) − s_i|`
over every perturbing opinion `q`, every original agent `i`, every time `t ≥ 0` and every solution
`x` of the weighted system (2.4) started at the augmented configuration (uniqueness is not
required). The limit is written out: for every `ε > 0` there is `η > 0` such that for every
`δ ∈ (0, η)` all these displacements are at most `ε`. -/
def IsStable {n : ℕ} (w : Fin n → ℝ) (s : Fin n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η → ∀ q : ℝ,
    ∀ x : ℝ → Fin (n + 1) → ℝ,
      IsWeightedSolution (Fin.snoc (α := fun _ => ℝ) w δ) x →
      x 0 = Fin.snoc (α := fun _ => ℝ) s q →
      ∀ i : Fin n, ∀ t : ℝ, 0 ≤ t → |x t (Fin.castSucc i) - s i| ≤ ε

end BHTOpinion.Approx.Supplement


