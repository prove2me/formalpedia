-- Prove2me | Definitions.Def_WeakGraphOracles_OneSided_Supplement_degrees
-- name    : WeakGraphOracles_OneSided_Supplement_degrees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:25:20.15262+00:00
-- url     : https://prove2.me/theorems/5f25ce3a-66b0-45eb-a3d8-3396f071f007
-- title:
--   Degree vectors $\mathrm{hist}(G)$, the threshold property $P_d^+$, target dominance $P_\alpha^+$ and interval concentration
-- statement:
--   For a graph $G$ on $n$ labels, $\deg_G(v)$ is the number of neighbours of $v$, and the degree vector $\mathrm{hist}(G)$ is the full sequence of the $n$ degrees (zeros included) sorted in non-increasing order.
--
--   The property $P_d^+$ holds when at least $n/2$ vertices have degree at least $d$.
--
--   A sorted target is a non-increasing vector $\alpha\in[0,n-1]^n$ of nonnegative integers; it need not be the degree vector of any graph. The property $P_\alpha^+$ holds when $\mathrm{hist}(G)\ge\alpha$ coordinatewise on the sorted vectors.
--
--   Definition 7: $\alpha$ is $(\delta,\gamma,k)$-interval concentrated if there are $k$ pairwise disjoint nonempty index intervals $I_h=[a_h,b_h]$ of positions such that
--
--   $$\alpha_{b_h}\ge(1-\gamma)\,\alpha_{a_h}\quad(h=1,\dots,k),\qquad \sum_{i\in I_1\cup\dots\cup I_k}\alpha_i\ge(1-\delta)\,|\alpha|,$$
--
--   where $|\alpha|=\sum_i\alpha_i$. The intervals need not cover all positions and have no length bound.
--
--   **Formalization Note** Positions are 0-based indices in `Fin n`; the sorted vector is obtained by sorting the multiset of degrees.
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 12 (PDF p. 13), Lemma 6.1 (P_d^+); p. 13 (PDF p. 14), §6.2, hist(G), |α|, P_α^+; p. 14 (PDF p. 15), Definition 7

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_graphs

set_option autoImplicit false

namespace WeakGraphOracles.OneSided.Supplement

/-- `deg_G(v) = |N_G(v)|`. -/
noncomputable def degree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  (G.neighborSet v).ncard

/-- `hist(G)`: the full degree sequence (all `n` entries, zeros included) sorted
in non-increasing order; `hist G i` is its `i`-th entry (0-based). -/
noncomputable def hist {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) : ℕ :=
  (((Finset.univ : Finset (Fin n)).val.map (degree G)).sort (· ≥ ·)).getD i.val 0

/-- `P_d^+`: at least `n/2` vertices have degree at least `d`. -/
noncomputable def DegreeThreshold (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  (n : ℝ) / 2 ≤ (((Finset.univ : Finset (Fin n)).filter fun v => d ≤ degree G v).card : ℝ)

/-- A sorted target degree vector `α ∈ [0, n-1]^n`: non-increasing, entries at
most `n - 1`. It need not be graphical. -/
def IsDegreeTarget {n : ℕ} (α : Fin n → ℕ) : Prop :=
  Antitone α ∧ ∀ i, α i ≤ n - 1

/-- `P_α^+`: `hist(G) ≥ α` coordinatewise on sorted vectors. -/
noncomputable def DominatesTarget {n : ℕ} (α : Fin n → ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ i, α i ≤ hist G i

/-- Definition 7, `(δ, γ, k)`-interval concentration: there are `k` pairwise
disjoint nonempty index intervals `[a_h, b_h]` (0-based indices in `Fin n`) with
`α(b_h) ≥ (1-γ) α(a_h)` for every `h`, and the coordinates indexed by their union
carry mass at least `(1-δ)|α|`. -/
def IntervalConcentrated {n : ℕ} (δ γ : ℝ) (k : ℕ) (α : Fin n → ℕ) : Prop :=
  ∃ a b : Fin k → Fin n,
    (∀ h, a h ≤ b h) ∧
    (∀ h h', h ≠ h' → Disjoint (Set.Icc (a h) (b h)) (Set.Icc (a h') (b h'))) ∧
    (∀ h, (1 - γ) * (α (a h) : ℝ) ≤ α (b h)) ∧
    (1 - δ) * ((∑ i, α i : ℕ) : ℝ) ≤
      ((∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => ∃ h, a h ≤ i ∧ i ≤ b h),
        α i : ℕ) : ℝ)

end WeakGraphOracles.OneSided.Supplement


