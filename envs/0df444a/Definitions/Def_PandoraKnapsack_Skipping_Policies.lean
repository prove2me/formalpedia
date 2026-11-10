-- Prove2me | Definitions.Def_PandoraKnapsack_Skipping_Policies
-- name    : PandoraKnapsack_Skipping_Policies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:23:28.025407+00:00
-- url     : https://prove2.me/theorems/6fab6585-e78d-405d-bee4-90415fddec86
-- title:
--   Fully-adaptive and skipping-adaptive policies and their expected net utility
-- statement:
--   A run starts with an empty knapsack and attempts distinct items one at a time. Attempting choice $j$ of item $i$ pays $p_i^j$ and reveals its size $s\sim F_i^j$, independent of everything before. With used capacity $S$, the item fits if $S+s\le T$ (equality fits) and contributes $v_i-p_i^j$; otherwise it is the overflow item, contributes $-p_i^j$, and the run ends.
--
--   A **fully-adaptive policy** $\pi$ maps every history (the ordered list of attempted item, choice and realized size) to "stop" or a next item-choice pair; choosing an already attempted item stops. Its expected utility `adaptValue I π` is computed by the exact recursion over the size laws; $\mathrm{ADAPT}(I)$ is the maximum over all $\pi$.
--
--   A **skipping-adaptive policy** is a list $\sigma$ of (item, choice, threshold) triples with no repeated item and thresholds in $\{0,\dots,T\}$ (`IsSkippingPolicy`). The pairs are considered in order: with remaining capacity $B=T-S$, a pair with threshold $\theta>B$ is skipped, otherwise it is attempted; the run ends at the end of the list or at the first overflow. `skipValue I σ` is its expected utility.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen (2026), Pandora's Knapsack via Simple Policies, supplied PDF (STOC 2027 submission), SHA256 45e5830b173d687c08d5175988af81bf660c693ff805b1d2e7bc213140d27a2d, §2, Definitions 2.2–2.3 and the utility paragraph, printed pp. 9–10 (PDF 11–12)

import Definitions.Def_PandoraKnapsack_Skipping_Instance

namespace PandoraKnapsack.Skipping

/-- **Fully-adaptive and skipping-adaptive policies and their expected net utility.**

Barak et al. (2026), *Pandora's Knapsack via Simple Policies*, supplied PDF (SHA256
45e5830b…7a2d), §2, Definitions 2.2–2.3 and the utility paragraph, printed pp. 9–10 (PDF 11–12).

A run starts with an empty knapsack and attempts distinct items one at a time. Attempting
choice `j` of item `i` pays `p_i^j` and then reveals its size `s`, drawn from `F_i^j`
independently of everything before. If the used capacity `S` plus `s` is at most `T` the item fits
and contributes `v_i − p_i^j`; otherwise it is the overflow item, contributes `−p_i^j`, and the run
stops.

**Formalization Note.** A *history* lists the attempted (item, choice, realized size) triples in
order; all of them fitted. A fully-adaptive policy is an arbitrary function from histories to
"stop" (`none`) or a next item-choice pair; choosing an item that was already attempted is read as
stopping, which adds no behaviour. Its expected utility is computed by the exact recursion over
the size law of each attempted pair; `n` levels suffice because each level attempts a new item. -/
abbrev History (n m : ℕ) := List (Fin n × Fin m × ℕ)

/-- A fully-adaptive (deterministic, history-dependent) policy, Definition 2.3. -/
abbrev AdaptivePolicy (n m : ℕ) := History n m → Option (Fin n × Fin m)

variable {n m T : ℕ}

/-- The used capacity after a history: the total realized size. -/
def usedCapacity (h : History n m) : ℕ := (h.map fun e => e.2.2).sum

/-- Expected utility collected from history `h` on, with `k` attempts still allowed. -/
noncomputable def adaptValueFrom (I : Instance n m T) (π : AdaptivePolicy n m) :
    ℕ → History n m → ℝ
  | 0, _ => 0
  | k + 1, h =>
    match π h with
    | none => 0
    | some (i, j) =>
      if i ∈ h.map (fun e => e.1) then 0 else
        ∑ s : Fin (T + 2), (I.sizeLaw i j s).toReal *
          (if usedCapacity h + (s : ℕ) ≤ T then
            I.value i - I.cost i j + adaptValueFrom I π k (h ++ [(i, j, (s : ℕ))])
          else -I.cost i j)

/-- `E[utility(π)]` for a fully-adaptive policy `π`; `ADAPT(I)` is its maximum over all `π`. -/
noncomputable def adaptValue (I : Instance n m T) (π : AdaptivePolicy n m) : ℝ :=
  adaptValueFrom I π n []

/-- A skipping-adaptive policy (Definition 2.3): a priority order of (item, choice, threshold)
triples. Thresholds are in the units of the §5 grid (capacity `T`), so the source's `τ ∈ [0, 1]`
becomes a threshold in `{0, …, T}`; the remaining capacity is always an integer. -/
abbrev SkipList (n m : ℕ) := List (Fin n × Fin m × ℕ)

/-- Validity of a skipping-adaptive policy: no item appears twice (Definition 2.2) and every
threshold lies in `[0, T]`. -/
def IsSkippingPolicy (T : ℕ) (σ : SkipList n m) : Prop :=
  (σ.map fun e => e.1).Nodup ∧ ∀ e ∈ σ, e.2.2 ≤ T

/-- Expected utility of the remaining list when `S ≤ T` capacity is used: a pair whose threshold
exceeds the remaining capacity `T − S` is skipped; otherwise it is attempted. The run stops at the
end of the list or at the first overflow. -/
noncomputable def skipValueFrom (I : Instance n m T) : SkipList n m → ℕ → ℝ
  | [], _ => 0
  | (i, j, θ) :: rest, S =>
    if θ ≤ T - S then
      ∑ s : Fin (T + 2), (I.sizeLaw i j s).toReal *
        (if S + (s : ℕ) ≤ T then I.value i - I.cost i j + skipValueFrom I rest (S + (s : ℕ))
        else -I.cost i j)
    else skipValueFrom I rest S

/-- `E[utility(σ)]` of a skipping-adaptive policy started with an empty knapsack. -/
noncomputable def skipValue (I : Instance n m T) (σ : SkipList n m) : ℝ :=
  skipValueFrom I σ 0

end PandoraKnapsack.Skipping


