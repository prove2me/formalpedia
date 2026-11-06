-- Prove2me | Definitions.Def_TemporalVoter_temporalConductance
-- name    : TemporalVoter_temporalConductance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:04.570378+00:00
-- url     : https://prove2.me/theorems/510f1601-f69a-4914-9fc2-889fd5cd26f7
-- title:
--   Temporal conductance $\Phi(\mathcal G)$ and the interval and window conductances $\phi^{[a,b]}$, $\phi^{\Delta}$
-- statement:
--   Let $\mathcal G=(G_t)$ be a temporal graph with fixed degrees, with volume $\mathrm{Vol}$, $m$ edges and cut sizes $e_t$.
--
--   1. The conductance of a set $S$ at time $t$ is $\phi^t(S)=e_t(S,\overline S)/\mathrm{Vol}(S)$.
--   2. For an integer interval $[a,b]$, $\phi^{[a,b]}(S)=\max_{a\le t\le b}\phi^t(S)$, and the **conductance of $\mathcal G$ on $[a,b]$** is
--   $$\phi^{[a,b]}(\mathcal G)=\min_{S\subseteq V,\ 0<\mathrm{Vol}(S)\le m}\phi^{[a,b]}(S).$$
--   3. For $\Delta\ge1$, the **$\Delta$-window conductance** is $\phi^{\Delta}(\mathcal G)=\min_{t\in\mathbb N}\phi^{[t,t+\Delta-1]}(\mathcal G)$.
--   4. The **temporal conductance** is
--   $$\Phi(\mathcal G)=\max_{\Delta\ge1}\frac{\phi^{\Delta}(\mathcal G)}{\Delta}.$$
--
--   We also write $I^-_j=\Delta_0+\dots+\Delta_{j-1}$ and $I^+_j=I^-_j+\Delta_j-1$ for the ends of the $j$-th interval of a partition of time into lengths $\Delta_0,\Delta_1,\ldots$.
--
--   $\phi^{[a,b]}(\mathcal G)\ge\phi$ says that every set with $0<\mathrm{Vol}(S)\le m$ is cut well at *some* step of $[a,b]$, possibly a different step for each set; $\Phi$ amortises this over the window length. It replaces static conductance in the consensus-time bound of the mission.
--
--   **Formalization Note** The maximum over $t\in[a,b]$, the minimum over $S$ and the minimum over $t\in\mathbb N$ are written as `⨆`/`⨅` in $\mathbb R$ over values in $[0,1]$; on finite nonempty index sets they are the maximum and minimum, and the infimum over $t\in\mathbb N$ is bounded below by $0$. The maximum over $\Delta\ge1$ is a supremum over $\Delta=\Delta'+1$, bounded by $1$; that it is attained is a milestone. The window $[t,t+\Delta-1]$ uses natural-number subtraction, exact for $\Delta\ge1$.
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), §1.3, (2)–(5), p.6; Theorem 1.3, p.7 (I⁻_j, I⁺_j)

import Mathlib
import Definitions.Def_TemporalVoter_TemporalGraph

open scoped Classical

namespace TemporalVoter

variable {V : Type} [Fintype V]

/-- **Conductance of a set at time `t`**, `φ^t(S) = e_t(S, S̄)/Vol(S)` (arXiv:2606.13374, version of
2 Nov 2026, §1.3, (2), p.6). -/
noncomputable def condAt (T : TemporalGraph V) (t : ℕ) (S : Finset V) : ℝ :=
  T.cut t S / T.vol S

/-- `φ^{[a,b]}(S) = max_{a ≤ t ≤ b} φ^t(S)` (§1.3, (3), p.6).

**Formalization Note** A supremum over the finite set `{a, …, b}`, i.e. the maximum when `a ≤ b`. -/
noncomputable def intervalCondSet (T : TemporalGraph V) (a b : ℕ) (S : Finset V) : ℝ :=
  ⨆ t : ↥(Finset.Icc a b), condAt T t S

/-- **Conductance on an integer interval**, `φ^{[a,b]}(G) = min_{S ⊆ V, 0 < Vol(S) ≤ m} φ^{[a,b]}(S)`
(§1.3, (3), p.6).

**Formalization Note** An infimum over the finite type of sets with `0 < Vol(S) ≤ m`, i.e. the
minimum whenever such a set exists (always, under Definition 1.1, when `V` is nonempty). -/
noncomputable def intervalCond (T : TemporalGraph V) (a b : ℕ) : ℝ :=
  ⨅ S : {S : Finset V // 0 < T.vol S ∧ T.vol S ≤ T.m}, intervalCondSet T a b S.1

/-- **`Δ`-window conductance**, `φ^Δ(G) = min_{t ∈ ℕ} φ^{[t, t+Δ−1]}(G)` for `Δ ≥ 1` (§1.3, (4), p.6).

**Formalization Note** `⨅ t : ℕ` of values in `[0, 1]`; the window is `[t, t + Δ − 1]` with
natural-number subtraction, which is the paper's window whenever `Δ ≥ 1`. -/
noncomputable def windowCond (T : TemporalGraph V) (Δ : ℕ) : ℝ :=
  ⨅ t : ℕ, intervalCond T t (t + Δ - 1)

/-- **Temporal conductance** `Φ(G) = max_{Δ ≥ 1} φ^Δ(G)/Δ` (§1.3, (5), p.6).

**Formalization Note** Written as `⨆ Δ : ℕ, φ^{Δ+1}(G)/(Δ+1)`, a supremum over `Δ ≥ 1` of values
in `[0, 1]`; that it is attained (a maximum) is milestone `sup_attained` (p.6). -/
noncomputable def temporalConductance (T : TemporalGraph V) : ℝ :=
  ⨆ Δ : ℕ, windowCond T (Δ + 1) / ((Δ + 1 : ℕ) : ℝ)

/-- `I⁻_j = Δ_0 + ⋯ + Δ_{j−1}`, the left end of the `j`-th interval (Theorem 1.3, p.7). -/
def Iminus (Δ : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ ℓ ∈ Finset.range j, Δ ℓ

/-- `I⁺_j = I⁻_j + Δ_j − 1`, the right end of the `j`-th interval (Theorem 1.3, p.7); every theorem
using it assumes `Δ_j ≥ 1`, so the natural-number subtraction is exact. -/
def Iplus (Δ : ℕ → ℕ) (j : ℕ) : ℕ :=
  Iminus Δ j + Δ j - 1

end TemporalVoter


