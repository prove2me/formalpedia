-- Prove2me | Definitions.Def_KTaxi_Competitive_Potential
-- name    : KTaxi_Competitive_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:52.96089+00:00
-- url     : https://prove2.me/theorems/caea7fd3-fdf3-4be4-9541-921c2d9a5fca
-- title:
--   Minimum injective matching cost $D(X_m,Y)$, the potential $\Phi$, and Property 4.1
-- statement:
--   Let $x=(x_1,\dots,x_k)$ be the online ordered list and $Y=(Y_1,\dots,Y_k)$ an adversary configuration. For $1\le m\le k$ the **level-$m$ prefix** is $X_m=\{x_1,\dots,x_m\}$ (a multiset).
--
--   1. The **minimum injective matching cost** is
--   $$
--   D(X_m,Y)=\min_{\sigma:\{1,\dots,m\}\hookrightarrow\{1,\dots,k\}}\ \sum_{i=1}^m d\bigl(x_i,Y_{\sigma(i)}\bigr),
--   $$
--   the minimum over injections of the prefix into the adversary's taxis.
--
--   2. For coefficients $\alpha_1,\dots,\alpha_k$ the **potential** is $\Phi(x,Y)=\sum_{m=1}^k\alpha_m D(X_m,Y)$.
--
--   3. **Property 4.1** (for the coefficients $\alpha$ on the space $V$): for every pickup $r$, every online ordered list $x$ and every adversary configuration $Y$ containing $r$ (some adversary taxi is at $r$),
--   $$
--   \mathbb E\bigl[\Delta\Phi+\mathrm{ALG}_t\bigr]\le0,
--   $$
--   where the expectation is over one round of Algorithm 1, $\Delta\Phi=\Phi(x',Y)-\Phi(x,Y)$ with $x'$ the list after the update and the movement to $r$, and $\mathrm{ALG}_t=d(x_{\pi(1)},r)$ is the cost of the serving taxi.
--
--   Property 4.1 is the hypothesis of Lemma 4.2 and the conclusion of Lemmas 4.7 and 4.8.
--
--   **Formalization Note** `levelCost x Y m` is the real infimum over embeddings `{j : Fin k // j < m} ↪ Fin k`; this finite type is never empty (the inclusion is an embedding), so the infimum is a minimum. For `m ≥ k` the prefix is the whole list. Coefficients are a function `α : ℕ → ℝ` indexed by the level; only `α 1, …, α k` enter. In `Property41` the expectation is the finite sum over permutations `π` of `(scanLaw x r π).toReal` times the bracket.
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (October 2026; PDF SHA-256 09242267e431f586117500ee75c63e6f203519f497d01ee4d90d6989341648ed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, §4 (PDF p. 6, definition of D and Φ) and §4.1 (PDF p. 7, Property 4.1)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Algorithm1

namespace KTaxi.Competitive

/-! # Matching costs, the potential Φ and Property 4.1

Coester, Huang, Poon, STOC 2027 submission #96, §4 (PDF p. 6) and §4.1 (PDF p. 7).

Slots are 0-based; a **level** `m : ℕ` is the number of leading slots: the level-`m` prefix of
an ordered list `x : Fin k → V` is the slots `j` with `j < m` (the paper's `x₁, …, x_m`).
An adversary configuration is `Y : Fin k → V`.
-/

variable {V : Type*} [MetricSpace V] {k : ℕ}

/-- The **minimum injective matching cost** `D(X_m, Y)` from the level-`m` prefix
`X_m = {x_j : j < m}` of the ordered list `x` to the adversary configuration `Y`:
the minimum, over injections `σ` of the prefix slots into the `k` adversary taxis, of
`∑_{j < m} d(x_j, Y_{σ j})`. (For `m ≥ k` the prefix is the whole list.) -/
noncomputable def levelCost (x Y : Fin k → V) (m : ℕ) : ℝ :=
  ⨅ σ : {j : Fin k // j.val < m} ↪ Fin k,
    ∑ j : {j : Fin k // j.val < m}, dist (x j.1) (Y (σ j))

/-- The potential `Φ(x, Y) = ∑_{m=1}^{k} α_m D(X_m, Y)`, with coefficients `α : ℕ → ℝ`
indexed by the level `m`. -/
noncomputable def potential (α : ℕ → ℝ) (x Y : Fin k → V) : ℝ :=
  ∑ m ∈ Finset.Icc 1 k, α m * levelCost x Y m

/-- **Property 4.1** (§4.1, PDF p. 7) for the coefficients `α` on the metric space `V`: for
every request with pickup `r`, every online ordered list `x` and every adversary configuration
`Y` containing `r` (some adversary taxi is located at `r`),
`E[ΔΦ + ALG_t] ≤ 0`, where the expectation is over one round of Algorithm 1 (list update
`π ∼ scanLaw x r`), `ΔΦ = Φ(x', Y) - Φ(x, Y)` with `x' = afterRound x π r` the list after the
update and the movement to `r`, and `ALG_t = d(x_{π 0}, r)` is the movement cost of the serving
taxi. (The drop-off `s` plays no role.) -/
def Property41 (V : Type*) [MetricSpace V] (k : ℕ) [NeZero k] (α : ℕ → ℝ) : Prop :=
  ∀ (x Y : Fin k → V) (r : V), (∃ i, Y i = r) →
    ∑ π : Equiv.Perm (Fin k), (scanLaw x r π).toReal *
      (potential α (afterRound x π r) Y - potential α x Y + dist (x (π 0)) r) ≤ 0

end KTaxi.Competitive


