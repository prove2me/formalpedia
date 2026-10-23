-- Prove2me | Definitions.Def_AdaptSubCover_Rounds_Analysis
-- name    : AdaptSubCover_Rounds_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:43.300786+00:00
-- url     : https://prove2.me/theorems/11cda638-dd1f-4135-8927-c2fca8ada298
-- title:
--   §3.1, §4, pp. 9–15 — time prefixes, scales θ, r*_{iθ}, good scales, the function g of (5), u_i, u*_i and G(Π)
-- statement:
--   Fix an instance, $\delta = 2^{-z}$, $\tau = Q(1-\delta)$, ParCA's list $L$, and an adaptive solution $\pi$ playing the role of $\mathtt{OPT}$. "Time" is cumulative cost.
--
--   1. **Prefix at time $t$.** $\mathcal X_{e(t)}$ is the first item of $L$ whose cumulative cost exceeds $t$; $\mathcal S$ is the set of items of $L$ before it (all of $L$ if there is none).
--   2. **Scales** (p. 11). For $\theta = 2^{-j}$, $0 \le j \le \log_2 Q$, a realization $S$ of $\mathcal S$ belongs to scale $\theta$, $S \in \mathcal E_\theta$, iff $\theta/2 < (Q - f(S))/Q \le \theta$.
--   3. $r^*_{i\theta} := \Pr(\mathtt{OPT}\text{ covers } f \text{ with cost at most } 2^i \text{ and } S \in \mathcal E_\theta)$; scale $\theta$ is **good** if $r^*_{i\theta}/\Pr(\mathcal E_\theta) \ge 1/6$. The sum $\sum_{\theta > \delta,\ \text{good}} r^*_{i\theta}$ runs over $j < z$.
--   4. **The function (5)**: $g(T) = \sum_{S \sim \mathcal S : f(S) < \tau} \Pr(\mathcal S = S) \cdot \frac{f(S \cup T) - f(S)}{Q - f(S)}$, and $\mathbb E_{T \sim \mathcal T}[g(T)]$ for an item set $\mathcal T$ disjoint from $\mathcal S$.
--   5. **Phases** (p. 9): $u_i$ is the probability that $\mathtt{NA}$ has cost at least $\alpha\cdot 2^i$; $u^*_i$ is the probability that $\mathtt{OPT}$ costs at least $2^i$.
--   6. **$G(\Pi)$** of (14): along the decision path $\Pi$ of $\mathtt{NA}$ with realizations $X_1, X_2, \dots$, cumulative costs $C_j = \sum_{\ell \le j} c_\ell$ and $t_j$ the width of $[C_{j-1}, C_j] \cap [\alpha 2^{i-1}, \alpha 2^i]$,
--   $$G(\Pi) = \sum_j \frac{t_j}{c_j}\cdot\frac{f(\{X_1,\dots,X_j\}) - f(\{X_1,\dots,X_{j-1}\})}{Q - f(\{X_1,\dots,X_{j-1}\})}.$$
--   7. **$\mathtt{NA}$ terminates by time $t$** if it never probes $\mathcal X_{e(t)}$, i.e. its probed items lie in the prefix at time $t$.
--
--   These are the quantities of the proof of the key Lemma 3.3.
--
--   **Formalization Note.** In $G(\Pi)$ the sum runs over all probed items; items outside phase $i$ have $t_j = 0$, so this is the paper's sum from $h$ to $p$ (and $0$ if $\Pi$ ends before phase $i$); $c_j$ is written $C_j - C_{j-1}$. The ratio $r^*/\Pr(\mathcal E_\theta)$ is $0$ in Lean when $\Pr(\mathcal E_\theta) = 0$, so such a scale is not good (its $r^*$ is $0$ anyway).
-- source:
--   Ghuge, Gupta, Nagarajan, The Power of Adaptivity for Stochastic Submodular Cover, arXiv:2106.16115v1, pp. 9–15, §3.1 (u_i, u*_i), §4 (e(t), p. 10), §4.1 items 1–3 and eq. (5) (p. 11), §4.2 eq. (14) (p. 15)

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_ParCA

namespace AdaptSubCover.Rounds

noncomputable section

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

/-- Cumulative cost of the first `j` entries of the list `L`. -/
def Instance.cumCost (I : Instance U m) (L : List (Fin m)) (j : ℕ) : ℕ :=
  ((L.take j).map I.c).sum

open Classical in
/-- The items of `L` chosen until time `t` (§4, p. 10; §4.1, p. 11): the entries before
`𝒳_{e(t)}`, the first entry whose cumulative cost exceeds `t` (all of `L` if there is none). -/
def Instance.prefixAt (I : Instance U m) (L : List (Fin m)) (t : ℝ) : Finset (Fin m) :=
  (L.take (Nat.findGreatest (fun j => (I.cumCost L j : ℝ) ≤ t) L.length)).toFinset

/-- The realization `S` of the item set `𝒮` belongs to scale `θ = 2^{-j}`, `0 ≤ j ≤ log Q`
(§4.1, item 1, p. 11): `θ/2 < (Q − f(S))/Q ≤ θ`. -/
def Instance.InScale (I : Instance U m) (j : ℕ) (S : Finset (Fin m)) (ω : Fin m → U) : Prop :=
  j ≤ Nat.log 2 I.Q ∧
    (2⁻¹ : ℝ) ^ j / 2 < ((I.Q : ℝ) - I.f (S.image ω)) / I.Q ∧
    ((I.Q : ℝ) - I.f (S.image ω)) / I.Q ≤ (2⁻¹ : ℝ) ^ j

/-- `r*_{iθ} := P(OPT covers f with cost at most 2^i and S ∈ ℰ_θ)` for `θ = 2^{-j}`
(§4.1, item 2, p. 11), with `π` in the role of `OPT`. -/
def Instance.rStar (I : Instance U m) (π : AdaptivePolicy m U) (i j : ℕ)
    (S : Finset (Fin m)) : ℝ :=
  I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ I.InScale j S ω)

/-- Scale `θ = 2^{-j}` is good if `r*_{iθ} / P(ℰ_θ) ≥ 1/6` (§4.1, item 3, p. 11). -/
def Instance.Good (I : Instance U m) (π : AdaptivePolicy m U) (i j : ℕ)
    (S : Finset (Fin m)) : Prop :=
  1 / 6 ≤ I.rStar π i j S / I.P (I.InScale j S)

open Classical in
/-- `Σ_{θ > δ, good} r*_{iθ}` for `δ = 2^{-z}`: the sum over good scales `2^{-j}` with `j < z`. -/
def Instance.goodSum (I : Instance U m) (π : AdaptivePolicy m U) (i z : ℕ)
    (S : Finset (Fin m)) : ℝ :=
  ∑ j ∈ (Finset.range z).filter (fun j => I.Good π i j S), I.rStar π i j S

open Classical in
/-- `E_{T∼𝒯}[g(T)]` for the function `g` of (5),
`g(T) = Σ_{S∼𝒮 : f(S) < τ} P(𝒮 = S) · (f(S ∪ T) − f(S)) / (Q − f(S))`, evaluated at the
random realization of an item set `𝒯` disjoint from `𝒮`. -/
def Instance.gExp (I : Instance U m) (τ : ℝ) (S T : Finset (Fin m)) : ℝ :=
  I.E (fun ω =>
    if (I.f (S.image ω) : ℝ) < τ then
      ((I.f (S.image ω ∪ T.image ω) : ℝ) - I.f (S.image ω)) / ((I.Q : ℝ) - I.f (S.image ω))
    else 0)

/-- `u_i`: the probability that `NA` has cost at least `α · 2^i` (§3.1, p. 9). -/
def Instance.uPhase (I : Instance U m) (τ α : ℝ) (L : List (Fin m)) (i : ℕ) : ℝ :=
  I.P (fun ω => α * 2 ^ i ≤ (I.costOf (I.NA τ L ω) : ℝ))

/-- `u*_i`: the probability that `OPT` (here `π`) costs at least `2^i` (§3.1, p. 9). -/
def Instance.uStar (I : Instance U m) (π : AdaptivePolicy m U) (i : ℕ) : ℝ :=
  I.P (fun ω => (2 : ℝ) ^ i ≤ (I.costOf (π.run ω) : ℝ))

/-- `G(Π)` of (14), p. 15, for the decision path `Π` of `NA` under `ω` and phase `i ≥ 1`: with
`X_1, X_2, …` the realizations along `Π`, `C_j` the cumulative cost of the first `j` probed items
and `t_j` the width of `[C_{j-1}, C_j] ∩ [α 2^{i-1}, α 2^i]`,
`G(Π) = Σ_j (t_j / c_j) · (f({X_1..X_j}) − f({X_1..X_{j-1}})) / (Q − f({X_1..X_{j-1}}))`,
where `c_j = C_j − C_{j-1}`; items outside phase `i` have `t_j = 0`. -/
def Instance.Gpath (I : Instance U m) (τ α : ℝ) (L : List (Fin m)) (i : ℕ)
    (ω : Fin m → U) : ℝ :=
  let H := I.NA τ L ω
  ∑ j ∈ Finset.range H.length,
    let a : ℝ := I.costOf (H.take j)
    let b : ℝ := I.costOf (H.take (j + 1))
    let w : ℝ := max 0 (min b (α * 2 ^ i) - max a (α * 2 ^ (i - 1)))
    let V₀ : ℝ := I.f (History.realized (H.take j))
    let V₁ : ℝ := I.f (History.realized (H.take (j + 1)))
    w / (b - a) * ((V₁ - V₀) / ((I.Q : ℝ) - V₀))

/-- `NA` terminates by time `t`: it never probes `𝒳_{e(t)}`, i.e. all its probed items lie in
the prefix of `L` chosen until time `t`. -/
def Instance.NAStoppedBy (I : Instance U m) (τ : ℝ) (L : List (Fin m)) (t : ℝ)
    (ω : Fin m → U) : Prop :=
  (I.NA τ L ω).items ⊆ I.prefixAt L t

end

end AdaptSubCover.Rounds


