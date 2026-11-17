-- Prove2me | Definitions.Def_DeepQOperator_Supplement_LipschitzRows
-- name    : DeepQOperator_Supplement_LipschitzRows
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:40:52.338784+00:00
-- url     : https://prove2.me/theorems/21894eee-28b6-4a54-95d9-ee0e5007c831
-- title:
--   Independent bounded Lipschitz rows: adaptive recovery of $b+\gamma AM$, fill distances and the allocation value
-- statement:
--   Rows $i=1,\dots,m$ carry nonempty compact metric domains $\mathcal A_i$, bounds $B_i\ge0$ and Lipschitz constants $L_i\ge0$. An input is a tuple $(f_i)$, chosen independently across rows, with $f_i:\mathcal A_i\to[-B_i,B_i]$ $L_i$-Lipschitz. Write $M_i=\max f_i$. For a known $b\in\mathbb{R}^K$, $\gamma$ and $A\in\mathbb{R}^{K\times m}$ the target is $b+\gamma AM$.
--
--   A **deterministic adaptive algorithm** makes at most $N$ exact scalar queries $(i,x)\mapsto f_i(x)$ with $x\in\mathcal A_i$, each chosen from the earlier answers, and then outputs an estimate in $\mathbb{R}^K$. The **minimax error** $\mathfrak R_N(A)$ is the infimum over such algorithms of the worst $\|\text{estimate}-(b+\gamma AM)\|_\infty$ over the input class.
--
--   For $n\ge1$, the **infimal fill distance** is
--   $$
--   h_i(n)=\inf_{S\subset\mathcal A_i,\ |S|\le n}\ \sup_{a\in\mathcal A_i}\min_{x\in S}d(a,x).
--   $$
--   The row widths are $D_i(n)=\min\{2B_i,L_ih_i(n)\}$ for $n\ge1$ and $D_i(0)=2B_i$ (118). The **allocation value** is $\min_{n\in\mathbb N_0^m,\ \sum_in_i\le N}\max_{k\le K}\sum_i|A_{ki}|D_i(n_i)$.
--
--   The **midpoint estimate** on fixed sites $S_i$ with observed maximum $s_i$ uses the midpoint of $[s_i,\min\{B_i,s_i+L_ih(S_i)\}]$ (and $0$ on an unqueried row).
--
--   These objects state Theorem 26.
--
--   **Formalization Note** $n$ sites are a map from $\{1,\dots,n\}$ to $\mathcal A_i$, so repetitions are allowed; this gives the same infimum as sets of at most $n$ points. An algorithm's query location is optional, with no location meaning that the run stops; this totalizes the empty-row case without changing the nonempty-row algorithm class. The minimax error is an infimum of suprema in $\mathbb{R}_{\ge0}\cup\{\infty\}$. A maximum over $k\le K$ is a real supremum over $K$ indices.
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix U eq. (118), p.71 (PDF p.74); Appendix W, pp.73–74 (PDF pp.76–77)

import Mathlib

open Finset

namespace DeepQOperator.Supplement

/-!
# Independent bounded Lipschitz rows: adaptive recovery of `b + γAM` and the allocation value

Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix U eq. (118) p.71 (PDF p.74),
Appendix W pp.73–74 (PDF pp.76–77).

Rows `i = 1, …, m` carry nonempty compact metric domains `𝒜_i`, bounds `B_i ≥ 0` and Lipschitz
constants `L_i ≥ 0`. An input is a tuple `(f_i)` with `f_i : 𝒜_i → [−B_i, B_i]` `L_i`-Lipschitz,
chosen independently across rows, and `M_i = max f_i`. For known `b ∈ ℝ^K`, `γ` and `A ∈ ℝ^{K×m}` the
recovery target is `b + γAM`. A deterministic adaptive algorithm makes at most `N` exact scalar
queries `(i, x) ↦ f_i(x)`, each chosen from the earlier answers, and then outputs an estimate in
`ℝ^K`; its error is the worst `‖estimate − (b + γAM)‖_∞` over inputs. For `n ≥ 1`, `h_i(n)` is the
infimal fill distance `sup_{a ∈ 𝒜_i} min_{x ∈ S} d(a, x)` of `n` sites `S ⊂ 𝒜_i`, and
`D_i(n) = min{2B_i, L_i h_i(n)}`, `D_i(0) = 2B_i` (118).

**Formalization Note.**
* An algorithm is given by its behaviour at every list of earlier answers: whether to ask
  (`ask`), the optional row and point asked (`site`), and the final estimate (`est`). A missing site
  stops the run; this totalizes the zero-row case, where no scalar query exists. `run A f N` runs it
  with fuel `N`; the deterministic adaptive algorithms with at most `N` queries are exactly these
  runs.
* The error is the sup norm on `Fin K → ℝ`. The minimax error `minimaxError` is an infimum over
  algorithms of a supremum over the input class, both in `ℝ≥0∞`, so neither needs to be attained and
  an unbounded estimator is not truncated.
* `n` sites are a map `Fin n → 𝒜_i` (repetition allowed, so a set of at most `n` distinct sites);
  their fill distance is `sup_a infDist(a, sites)`, finite on a compact domain. `fillDistance 𝒜 n` is
  the infimum over all `n`-site maps.
* `M_i = sup f_i` is the maximum (attained on a compact domain). The allocation minimum is the
  infimum over the finite nonempty set `{n ∈ ℕ^m : Σ n_i ≤ N}`, and `max_{k ≤ K}` is the supremum over
  `Fin K` (zero if `K = 0`).
* `midpointEstimate` is the fixed-cover estimate of Appendix W.2: on a row with `n_i ≥ 1` sites
  `S_i` and observed maximum `s_i`, the interval `[s_i, min{B_i, s_i + L_i h(S_i)}]` contains `M_i`
  and its midpoint is used; an unqueried row has interval `[−B_i, B_i]` and midpoint `0`.
-/

/-- A deterministic adaptive algorithm with exact scalar queries `(i, x)`, `x ∈ 𝒜_i`, and an
estimate in `ℝ^K`. -/
structure LipAlg (m K : ℕ) (𝒜 : Fin m → Type) where
  /-- whether a further query is made after these answers (`false` = stop) -/
  ask : List ℝ → Bool
  /-- the row and point queried after these answers, or `none` when no query location exists -/
  site : List ℝ → Option (Σ i, 𝒜 i)
  /-- the final estimate from the answers -/
  est : List ℝ → Fin K → ℝ

namespace LipAlg

variable {m K : ℕ} {𝒜 : Fin m → Type}

/-- Run at most `k` further queries from the answers `h`, on input `f`. -/
def run (A : LipAlg m K 𝒜) (f : ∀ i, 𝒜 i → ℝ) : ℕ → List ℝ → List ℝ
  | 0, h => h
  | k + 1, h =>
      if A.ask h then
        match A.site h with
        | none => h
        | some q => A.run f k (h ++ [f q.1 q.2])
      else h

end LipAlg

/-- The row maximum `M_i = max f_i`. -/
noncomputable def rowMax {m : ℕ} {𝒜 : Fin m → Type} (f : ∀ i, 𝒜 i → ℝ) (i : Fin m) : ℝ :=
  ⨆ x, f i x

/-- The input class: every row `f_i` takes values in `[−B_i, B_i]` and is `L_i`-Lipschitz. -/
def InLipClass {m : ℕ} {𝒜 : Fin m → Type} [∀ i, PseudoMetricSpace (𝒜 i)] (Bd : Fin m → ℝ)
    (L : Fin m → NNReal) (f : ∀ i, 𝒜 i → ℝ) : Prop :=
  ∀ i, (∀ x, f i x ∈ Set.Icc (-Bd i) (Bd i)) ∧ LipschitzWith (L i) (f i)

/-- The recovery target `b + γAM`. -/
noncomputable def recTarget {m K : ℕ} {𝒜 : Fin m → Type} (b : Fin K → ℝ) (γ : ℝ)
    (Amat : Matrix (Fin K) (Fin m) ℝ) (f : ∀ i, 𝒜 i → ℝ) : Fin K → ℝ :=
  fun k => b k + γ * ∑ i, Amat k i * rowMax f i

/-- The deterministic adaptive minimax `∞`-norm recovery error `ℜ_N(A)` from at most `N` queries. -/
noncomputable def minimaxError {m K : ℕ} (𝒜 : Fin m → Type) [∀ i, PseudoMetricSpace (𝒜 i)]
    (Bd : Fin m → ℝ) (L : Fin m → NNReal) (b : Fin K → ℝ) (γ : ℝ) (Amat : Matrix (Fin K) (Fin m) ℝ)
    (N : ℕ) : ENNReal :=
  ⨅ A : LipAlg m K 𝒜, ⨆ (f : ∀ i, 𝒜 i → ℝ) (_ : InLipClass Bd L f),
    ENNReal.ofReal ‖A.est (A.run f N []) - recTarget b γ Amat f‖

/-- The fill distance `sup_{a ∈ X} min_j d(a, x_j)` of the sites `x`. -/
noncomputable def siteFill {X : Type} [PseudoMetricSpace X] {n : ℕ} (x : Fin n → X) : ℝ :=
  ⨆ a : X, Metric.infDist a (Set.range x)

/-- The infimal fill distance `h(n)` of `n` sites. -/
noncomputable def fillDistance (X : Type) [PseudoMetricSpace X] (n : ℕ) : ℝ :=
  ⨅ x : Fin n → X, siteFill x

/-- `D_i(n) = min{2B_i, L_i h_i(n)}` for `n ≥ 1` and `D_i(0) = 2B_i` (118). -/
noncomputable def rowWidth {m : ℕ} (𝒜 : Fin m → Type) [∀ i, PseudoMetricSpace (𝒜 i)]
    (Bd : Fin m → ℝ) (L : Fin m → NNReal) (i : Fin m) (n : ℕ) : ℝ :=
  if n = 0 then 2 * Bd i else min (2 * Bd i) ((L i : ℝ) * fillDistance (𝒜 i) n)

/-- The allocation value `min_{n ∈ ℕ^m, Σ n_i ≤ N} max_{k ≤ K} Σ_i |A_ki| D_i(n_i)`. -/
noncomputable def allocationValue {m K : ℕ} (𝒜 : Fin m → Type) [∀ i, PseudoMetricSpace (𝒜 i)]
    (Bd : Fin m → ℝ) (L : Fin m → NNReal) (Amat : Matrix (Fin K) (Fin m) ℝ) (N : ℕ) : ℝ :=
  ⨅ n : {n : Fin m → ℕ // ∑ i, n i ≤ N}, ⨆ k : Fin K, ∑ i, |Amat k i| * rowWidth 𝒜 Bd L i (n.1 i)

/-- The midpoint estimate of `b + γAM` from fixed sites `x_i : Fin (n_i) → 𝒜_i` (Appendix W.2). -/
noncomputable def midpointEstimate {m K : ℕ} {𝒜 : Fin m → Type} [∀ i, PseudoMetricSpace (𝒜 i)]
    (Bd : Fin m → ℝ) (L : Fin m → NNReal) (b : Fin K → ℝ) (γ : ℝ) (Amat : Matrix (Fin K) (Fin m) ℝ)
    (n : Fin m → ℕ) (x : ∀ i, Fin (n i) → 𝒜 i) (f : ∀ i, 𝒜 i → ℝ) : Fin K → ℝ :=
  fun k => b k + γ * ∑ i, Amat k i *
    (if n i = 0 then 0 else
      ((⨆ j, f i (x i j)) + min (Bd i) ((⨆ j, f i (x i j)) + (L i : ℝ) * siteFill (x i))) / 2)

end DeepQOperator.Supplement


