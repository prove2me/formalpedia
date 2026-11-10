-- Prove2me | Definitions.Def_OptRobustCD_treeOPT
-- name    : OptRobustCD_treeOPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:49:59.675506+00:00
-- url     : https://prove2.me/theorems/74cbd7a6-6b58-4e7a-95b8-93359b2f8e97
-- title:
--   The Poisson broadcast tree, $\mathbb E|M_t|$, the tree $\mathrm{OPT}_{d,\lambda}=\lim_t\mathbb E|M_t|$, and $\gamma_\ell$
-- statement:
--   **Broadcast tree** (Definition 3.1). Let $T_d$ be the rooted Galton–Watson tree with $\mathrm{Poi}(d)$ offspring; the root $o$ gets a uniform spin $x_o\in\{\pm1\}$ and each child copies its parent's spin with probability $(1+\lambda)/2$. With $x_t$ the spins at depth $t$,
--   $$M_t=\mathbb E[x_o\mid(T,x_t)],\qquad \mathrm{OPT}_{d,\lambda}=\lim_{t\to\infty}\mathbb E|M_t|$$
--   (p.14; the sequence $\mathbb E|M_t|$ is nonincreasing).
--
--   **$\gamma_\ell$** (p.16). With $W_\ell=(d\lambda)^{-\ell}\sum_{u\text{ at depth }\ell}x_u$ and $\beta=\frac12\sqrt{1-1/(d\lambda^2)}$,
--   $$\gamma_\ell=\mathbb E\bigl[x_o\tanh\bigl(\beta W_\ell/(\mathbb EW_\ell^2)^{1/2}\bigr)\bigr].$$
--
--   This tree quantity is the benchmark of Theorems 3.7 and 4.2 and Lemma 4.4.
--
--   **Formalization Note** A depth-$\ell$ observation (the tree to depth $\ell$ with the depth-$\ell$ spins) is a number of children and each child's depth-$(\ell-1)$ observation. With $P_\pm(o)$ its probability given $x_o=\pm1$, $\mathbb E|M_t|=\sum_o|P_+(o)-P_-(o)|/2$, summed in $[0,\infty]$ where it always exists. The limit is written $\inf_t\mathbb E|M_t|$, equal to it by monotonicity.
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Definition 3.1 p.13 (pdf p.15); OPT, p.14 (pdf p.16); γ_ℓ, p.16 (pdf p.18)

import Mathlib

namespace OptRobustCD

/-!
# The Poisson broadcast tree, `E|M_t|`, the tree `OPT_{d,λ}`, and `γ_ℓ`

Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027
submission (manuscript of November 3, 2026, sha256 3d287d54…).
* Definition 3.1 (p.13, pdf p.15): "Let `T_d` be the rooted Galton–Watson tree in which every
  vertex has an independent `Poi(d)` number of children. Give its root `o` a uniformly random spin
  `x_o ∈ {±1}`, and let each child independently copy its parent's spin with probability
  `(1 + λ)/2`. … Let `x_t` consist of the spins at the depth-t vertices. … `M_t = E[x_o | (T, x_t)]`."
* p.14 (pdf p.16): "Given the tree, `x_{t+1}` is obtained from `x_t` by one more step of
  broadcasting, so `E|M_{t+1}| ⩽ E|M_t|`. Define `OPT_{d,λ} = lim_{t→∞} E|M_t|`."
* p.16 (pdf p.18): "let `W_ℓ = (dλ)^{−ℓ} Σ_u x_u` be the sum over the spins of the depth-ℓ vertices
  of the broadcast tree, and let `γ_ℓ = E[x_o tanh(βW_ℓ/(E W_ℓ²)^{1/2})]`", with
  `β = (1/2)√(1 − 1/(dλ²))`.

**Formalization Note.**
* An observation of depth `ℓ` (`Obs ℓ`) is the tree up to depth `ℓ` together with the spins at
  depth `ℓ`: `Obs 0` is a spin, and an `Obs (ℓ+1)` is a number `k` of children followed by each
  child's depth-`ℓ` observation (children are ordered; the order carries no information).
* `obsWeight d λ ℓ x o ∈ [0, ∞]` is the probability of `o` given root spin `x`: `Poi(d)` children,
  each copying the parent's spin with probability `(1+λ)/2` (flipping with `(1−λ)/2`).
* With `P_±(o)` the probabilities given `x_o = ±1`, `P(o) = (P₊ + P₋)/2` and
  `M_t = (P₊ − P₋)/(P₊ + P₋)`, so `E|M_t| = Σ_o |P₊(o) − P₋(o)|/2` (`Emag`). The sum is taken in
  `[0, ∞]`, where it always exists, and is at most `1`.
* `OPT_{d,λ} = lim_t E|M_t|` is written `⨅_t E|M_t|` (`treeOPT`); by the monotonicity on p.14 the
  two agree. The values lie in `[0,1]`, so the real infimum is the true one.
* `γ_ℓ` (`gammaEll`) uses real sums over the countable set of observations of
  `P(o) W_ℓ(o)²` and `x_o`-weighted `tanh`; both families are summable (Poisson offspring have
  all moments, and `|tanh| ≤ 1`).
* Parameters: `d > 0`, `λ ∈ (−1, 1)` (Definition 3.1), stated where used.
-/

/-- Observations of the broadcast tree to depth `ℓ`: `Obs 0` is the spin of a vertex; an
`Obs (ℓ+1)` is a number of children and each child's depth-`ℓ` observation. -/
def Obs : ℕ → Type
  | 0 => Bool
  | ℓ + 1 => Σ k : ℕ, (Fin k → Obs ℓ)

/-- The `Poi(d)` probability of `k`: `e^{−d} d^k / k!`. -/
noncomputable def poisWeight (d : ℝ) (k : ℕ) : ENNReal :=
  ENNReal.ofReal (Real.exp (-d) * d ^ k / (Nat.factorial k))

/-- The probability of the depth-`ℓ` observation `o` of the subtree of a vertex with spin `x`. -/
noncomputable def obsWeight (d lam : ℝ) : (ℓ : ℕ) → Bool → Obs ℓ → ENNReal
  | 0, x, o => if (show Bool from o) = x then 1 else 0
  | ℓ + 1, x, o =>
      poisWeight d o.1 * ∏ i : Fin o.1,
        (ENNReal.ofReal ((1 + lam) / 2) * obsWeight d lam ℓ x (o.2 i) +
          ENNReal.ofReal ((1 - lam) / 2) * obsWeight d lam ℓ (!x) (o.2 i))

/-- `E|M_t| = Σ_o |P₊(o) − P₋(o)| / 2`. -/
noncomputable def Emag (d lam : ℝ) (t : ℕ) : ℝ :=
  (∑' o : Obs t, ((obsWeight d lam t true o - obsWeight d lam t false o) +
    (obsWeight d lam t false o - obsWeight d lam t true o)) / 2).toReal

/-- The tree `OPT_{d,λ} = lim_t E|M_t| = inf_t E|M_t|` of §3.3. -/
noncomputable def treeOPT (d lam : ℝ) : ℝ := ⨅ t : ℕ, Emag d lam t

/-- The sum of the spins at depth `ℓ` of an observation (`±1` each, `true ↦ +1`). -/
noncomputable def leafSum : (ℓ : ℕ) → Obs ℓ → ℝ
  | 0, o => if (show Bool from o) then 1 else -1
  | ℓ + 1, o => ∑ i : Fin o.1, leafSum ℓ (o.2 i)

/-- `γ_ℓ = E[x_o tanh(β W_ℓ / (E W_ℓ²)^{1/2})]` with `W_ℓ = (dλ)^{−ℓ} Σ_{depth ℓ} x_u` and
`β = (1/2)√(1 − 1/(dλ²))`. -/
noncomputable def gammaEll (d lam : ℝ) (ℓ : ℕ) : ℝ :=
  let W : Obs ℓ → ℝ := fun o => (d * lam) ^ (-(ℓ : ℤ)) * leafSum ℓ o
  let P : Bool → Obs ℓ → ℝ := fun x o => (obsWeight d lam ℓ x o).toReal
  let β : ℝ := (1 / 2) * Real.sqrt (1 - 1 / (d * lam ^ 2))
  let EW2 : ℝ := ∑' o : Obs ℓ, (P true o + P false o) / 2 * W o ^ 2
  ∑' o : Obs ℓ, (P true o - P false o) / 2 * Real.tanh (β * W o / Real.sqrt EW2)

end OptRobustCD


