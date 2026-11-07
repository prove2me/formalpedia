-- Prove2me | Definitions.Def_AKSZigZag_Errors
-- name    : AKSZigZag_Errors
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:50.082701+00:00
-- url     : https://prove2.me/theorems/497dcd11-680d-4ad6-919e-73ba12bd74c7
-- title:
--   The errors $\Delta_r$ and $\delta$ of a configuration
-- statement:
--   At time $t$ the intervals of §5 partition the registers; registers and contents are both identified with $1,\dots,n$, and $R(J)$ is the set of contents of the registers of $J$. For intervals, $K<J$ means $K$ lies entirely below $J$, and $K'$ is the next interval to the right of $K$. The **lower section** $L(K)$ is the union of the intervals not exceeding $K$; the **upper section** $U(K)$ is defined symmetrically.
--
--   For an interval $J$ and $r\ge0$:
--   1. $S_1=\sup|R(J)\cap L(K)|$ over the intervals $K<J$ with $K'\ne J$ and tree distance $d(J,K)\ge r$;
--   2. $S_2=\sup|R(J)\cap U(K)|$ over the intervals $K>J$ with $K\ne J'$ and $d(J,K)\ge r$;
--   3. a supremum over the empty set is $0$.
--
--   Then
--   $$
--   \Delta_r(J)=\frac{\max(S_1,S_2)}{|J|},\qquad \delta(J)=\frac{|R(J)-J|}{|J|},\qquad \Delta_r=\sup_J\Delta_r(J),\qquad \delta=\sup_J\delta(J).
--   $$
--
--   $\Delta_r$ measures the elements misplaced by at least $r$ levels of the tree. $\delta$ measures the elements not at their own interval. The §8 induction bounds both.
--
--   **Formalization Note** A configuration is `y : Fin n → Fin n`, from registers to contents. Only nonempty intervals are used, so no $0/0$ occurs, and the suprema are maxima over finitely many nonnegative numbers ($0$ when there are none). "$K'\ne J$" is encoded as "some interval lies strictly between $K$ and $J$".
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §8, p.7 (R(I), intervals, lower/upper sections, distance d(J,L), Δ_r(J), δ(J), Δ_r, δ)

import Mathlib
import Definitions.Def_AKSZigZag_RegisterAssignment

namespace AKSZigZag

/-- `K < J` for intervals: every register of `K` is below every register of `J`. -/
def IvLt {n : ℕ} (K J : Finset (Fin n)) : Prop := ∀ p ∈ K, ∀ q ∈ J, p < q

/-- The **lower section** `L(K)` (AKS, STOC 1983, §8, p.7): "all intervals not exceeding" `K`,
as a set of registers. -/
noncomputable def lowerSec {n : ℕ} (ivs : List (ℕ × ℕ × Finset (Fin n))) (K : Finset (Fin n)) :
    Finset (Fin n) := by
  classical
  exact ((ivs.filter fun I => IvLt I.2.2 K ∨ I.2.2 = K).map fun I => I.2.2).foldr (· ∪ ·) ∅

/-- The **upper section** `U(K)`: all intervals not below `K`. -/
noncomputable def upperSec {n : ℕ} (ivs : List (ℕ × ℕ × Finset (Fin n))) (K : Finset (Fin n)) :
    Finset (Fin n) := by
  classical
  exact ((ivs.filter fun I => IvLt K I.2.2 ∨ I.2.2 = K).map fun I => I.2.2).foldr (· ∪ ·) ∅

/-- `|R(J) ∩ T|` for the configuration `y` (register ↦ content): the number of registers of `J`
whose content lies in the register set `T` (contents and registers are both `Fin n`). -/
noncomputable def hits {n : ℕ} (y : Fin n → Fin n) (J T : Finset (Fin n)) : ℕ := by
  classical
  exact (J.filter fun p => y p ∈ T).card

/-- `Δ_r(J)` (AKS, STOC 1983, §8, p.7): "for a given J and r ≥ 0, find S1 = sup|R(J) ∩ L(K)| over
all intervals K, K < J, K' ≠ J, d(J,L(K)) ≥ r, and also S2 = sup|R(J) ∩ U(K)| over all intervals
K, K > J, K ≠ J', d(J,U(K)) ≥ r. Then Δr(J) is defined by Δr(J) = max(S1,S2)/|J| (when sup is
taken over an empty set, we define it as 0)."

`K' ≠ J` (the next interval right of `K` is not `J`) is "some interval lies strictly between
`K` and `J`"; likewise `K ≠ J'`. The distance `d(J, L(K))` is the tree distance of the nodes
holding `J` and `K`. -/
noncomputable def DeltaJ {n : ℕ} (ivs : List (ℕ × ℕ × Finset (Fin n))) (y : Fin n → Fin n)
    (r : ℕ) (J : ℕ × ℕ × Finset (Fin n)) : ℝ := by
  classical
  exact
    let between : Finset (Fin n) → Finset (Fin n) → Prop :=
      fun K J' => ∃ I ∈ ivs, IvLt K I.2.2 ∧ IvLt I.2.2 J'
    let S1 : ℕ := ((ivs.filter fun K => IvLt K.2.2 J.2.2 ∧ between K.2.2 J.2.2 ∧
        r ≤ treeDist J.1 J.2.1 K.1 K.2.1).map fun K => hits y J.2.2 (lowerSec ivs K.2.2)).foldr
        max 0
    let S2 : ℕ := ((ivs.filter fun K => IvLt J.2.2 K.2.2 ∧ between J.2.2 K.2.2 ∧
        r ≤ treeDist J.1 J.2.1 K.1 K.2.1).map fun K => hits y J.2.2 (upperSec ivs K.2.2)).foldr
        max 0
    (max S1 S2 : ℝ) / J.2.2.card

/-- `δ(J) = |R(J) - J|/|J|` (AKS, STOC 1983, §8, p.7): the proportion of registers of `J`
holding an element that does not belong to `J`. -/
noncomputable def deltaJ {n : ℕ} (y : Fin n → Fin n) (J : Finset (Fin n)) : ℝ := by
  classical
  exact ((J.filter fun p => y p ∉ J).card : ℝ) / J.card

/-- **The error `Δ_r = sup_J Δ_r(J)`** at time `t` (AKS, STOC 1983, §8, p.7), for the
configuration `y : Fin n → Fin n` (register ↦ content), over the intervals of time `t`.

**Formalization Note.** Only nonempty intervals are used, so no `0/0` occurs; the supremum of
the finitely many nonnegative values is a maximum (and `0` for no interval, as the paper sets
it for an empty supremum). -/
noncomputable def Delta (A n t : ℕ) (r : ℕ) (y : Fin n → Fin n) : ℝ :=
  ((intervals A n t).map fun J => DeltaJ (intervals A n t) y r J).foldr max 0

/-- **The error `δ = sup_J δ(J)`** at time `t` (AKS, STOC 1983, §8, p.7), for the configuration
`y` over the (nonempty) intervals of time `t`. -/
noncomputable def delta (A n t : ℕ) (y : Fin n → Fin n) : ℝ :=
  ((intervals A n t).map fun J => deltaJ y J.2.2).foldr max 0

end AKSZigZag


