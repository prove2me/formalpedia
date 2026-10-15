-- Prove2me | Definitions.Def_InterdepSOS_RSVCG_Mechanism
-- name    : InterdepSOS_RSVCG_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:33.730815+00:00
-- url     : https://prove2.me/theorems/bb247d6d-f1ce-407c-a8bd-bf57842e831a
-- title:
--   §5, pp. 16–17 — the Random-Sampling VCG mechanism: proxy weights $w_{jT}$, maximising allocation, $w_{-i}$ and payments
-- statement:
--   This file defines the **Random-Sampling VCG** (RS-VCG) mechanism of §5 for a fixed partition of the agents into $A$ and $B = [n] \setminus A$, given reported signals $\tilde s$ and separable valuations $v_{iT} = g_{-iT} + h_{iT}$.
--
--   1. **Proxy weights.** For $j \in B$ and a bundle $T$,
--   $$w_{jT} := v_{jT}(\tilde s_{jT}, \tilde s_{AT}, 0_{B-jT}),$$
--   agent $j$'s value for $T$ when the bundle-$T$ signals of $A$ and of $j$ are kept and those of $B \setminus \{j\}$ are set to $0$.
--   2. **Allocation.** $\{T_i\}_{i \in B}$ is any feasible allocation to $B$ that maximises $\sum_{i \in B} w_{iT_i}$ over all feasible allocations to $B$; agents of $A$ receive nothing. The mechanism is described by an arbitrary **selector** returning such a maximiser for every $B$ and every reported profile.
--   3. **Weight without $i$.** $w_{-i} := \max \sum_{j \in B \setminus \{i\}} w_{jT'_j}$, the maximum over all feasible allocations $\{T'_j\}$ to $B \setminus \{i\}$.
--   4. **Payments.** A winning agent $i \in B$ receiving the nonempty bundle $T_i$ pays
--   $$p_i(\tilde s) := g_{-iT_i}(\tilde s_{-iT_i}) - g_{-iT_i}(\tilde s_{AT_i}, 0_{B-iT_i}) - \sum_{j \in B \setminus \{i\}} w_{jT_j} + w_{-i};$$
--   every other agent pays $0$.
--
--   Theorem 5.1 states that this mechanism is ex-post IC-IR for every partition and that, with $B$ uniformly random, it is a 4-approximation to the optimal social welfare.
--
--   **Formalization Note** The selector `alloc B s̃` is a function of the partition and the reported profile, and `IsVCGSelector` requires it to return a feasible maximiser; no tie-breaking rule is fixed. $w_{-i}$ is `Finset.sup'` over the finite, nonempty set of feasible allocations to $B \setminus \{i\}$ (the empty allocation belongs to it), so it is a genuine maximum. The paper defines payments only for winners; agents of $A$ and agents of $B$ allocated the empty bundle pay $0$. Since $g_{-iT}$ ignores coordinate $i$, the term $g_{-iT_i}(\tilde s_{AT_i}, 0_{B-iT_i})$ is written as $g$ applied to the vector that keeps the coordinates of $A \cup \{i\}$.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), pp. 16–17, §5, Random-Sampling VCG (RS-VCG)

import Mathlib
import Definitions.Def_InterdepSOS_RSVCG_Setting

namespace InterdepSOS.RSVCG

/-- The RS-VCG proxy weight `w_{jT} = v_{jT}(s̃_{jT}, s̃_{AT}, 0_{B−jT})` with `A = Bᶜ`: agent `j`'s
value for `T` with the bundle-`T` signals of `B ∖ {j}` set to `0`. -/
def vcgWeight {n m : ℕ} (v : Valuation n m) (B : Finset (Fin n)) (s : Profile n m)
    (j : Fin n) (T : Bundle m) : ℝ :=
  v j T (keepOn (insert j Bᶜ) (sigT s T))

/-- An RS-VCG allocation selector: for every partition `B` and reported profile `s`, it returns a
feasible allocation to `B` maximising `Σ_{i∈B} w_{iT_i}` over all feasible allocations to `B`. -/
def IsVCGSelector {n m : ℕ} (v : Valuation n m)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) : Prop :=
  ∀ B s, IsAllocOn B (alloc B s) ∧
    ∀ T : Alloc n m, IsAllocOn B T →
      ∑ i ∈ B, vcgWeight v B s i (T i) ≤ ∑ i ∈ B, vcgWeight v B s i (alloc B s i)

/-- The (finite) set of feasible allocations to the agents of `N`. -/
noncomputable def allocsOn {n m : ℕ} (N : Finset (Fin n)) : Finset (Alloc n m) := by
  classical exact Finset.univ.filter (IsAllocOn N)

theorem allocsOn_nonempty {n m : ℕ} (N : Finset (Fin n)) : (allocsOn (m := m) N).Nonempty := by
  classical
  refine ⟨fun _ => ∅, ?_⟩
  simp only [allocsOn, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun _ _ _ => Finset.disjoint_empty_left _, fun _ _ => rfl⟩

/-- `w_{−i} = max Σ_{j∈B∖{i}} w_{jT'_j}` over feasible allocations `T'` to `B ∖ {i}`: the weight of the
best allocation without agent `i`. -/
noncomputable def wMinus {n m : ℕ} (v : Valuation n m) (B : Finset (Fin n)) (s : Profile n m)
    (i : Fin n) : ℝ :=
  (allocsOn (B.erase i)).sup' (allocsOn_nonempty _)
    (fun T => ∑ j ∈ B.erase i, vcgWeight v B s j (T j))

/-- The RS-VCG payment of agent `i` at the reported profile `s`: a winning agent `i ∈ B` receiving the
nonempty bundle `T_i` pays
`g_{−iT_i}(s̃_{−iT_i}) − g_{−iT_i}(s̃_{AT_i}, 0_{B−iT_i}) − Σ_{j∈B∖{i}} w_{jT_j} + w_{−i}`;
every other agent pays `0`. -/
noncomputable def vcgPay {n m : ℕ} (v g : Valuation n m)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) (B : Finset (Fin n)) (s : Profile n m)
    (i : Fin n) : ℝ :=
  if i ∈ B ∧ (alloc B s i).Nonempty then
    g i (alloc B s i) (sigT s (alloc B s i)) -
      g i (alloc B s i) (keepOn (insert i Bᶜ) (sigT s (alloc B s i))) -
      ∑ j ∈ B.erase i, vcgWeight v B s j (alloc B s j) + wMinus v B s i
  else 0

end InterdepSOS.RSVCG


