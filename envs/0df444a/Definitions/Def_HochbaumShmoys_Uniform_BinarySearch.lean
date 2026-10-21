-- Prove2me | Definitions.Def_HochbaumShmoys_Uniform_BinarySearch
-- name    : HochbaumShmoys_Uniform_BinarySearch
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:25.761271+00:00
-- url     : https://prove2.me/theorems/9bfef59e-4663-4745-908d-c04bba442fd8
-- title:
--   The binary search procedure of §2 driven by a decision procedure (pp. 540–541)
-- statement:
--   Fix $m\ge1$ machines with speeds $s_i$, $n$ jobs with processing times $p_j$, and a decision procedure $D$ (any map from instances $(p,b)$ to an optional packing). The binary search of §2 keeps a lower bound $L$, an upper bound $U$ and a current schedule.
--
--   1. **Initialization.** $U_0=\sum_j p_j/\max_i s_i$ (schedule all jobs on the fastest machine), $L_0=\sum_j p_j/(m\cdot\max_i s_i)$, and the current schedule puts every job on a fastest machine $i^\ast$ (an index with $s_{i^\ast}=\max_i s_i$).
--   2. **Iteration.** Let $T=(L+U)/2$. Run $D$ on the deadline-$T$ instance: pieces $p_1,\dots,p_n$ and bins $T s_1,\dots,T s_m$. If $D$ returns a packing $\sigma$, set $U:=T$ and make $\sigma$ the current schedule; otherwise set $L:=T$.
--   3. **Output.** After $K$ iterations, the current schedule.
--
--   The iteration count of Theorem 1 is
--   $$K(m,\varepsilon)=\Big\lceil \log_2 m+\log_2(3/\varepsilon)\Big\rceil ,$$
--   taken to be $0$ when the real number inside is $\le 0$.
--
--   This is the algorithm whose quality Theorem 1 bounds, and, with the decision procedure all-pack of §3, the polynomial approximation scheme of the paper.
--
--   **Formalization Note** The deadline-$T$ instance is written with bins $T s_i$ instead of the paper's equivalent rescaling of all sizes by $1/T$, so no division by $T$ occurs. The paper's "log" is taken to base 2 (each iteration halves the range) and rounded up. The output is the schedule kept with the final upper bound (the last schedule found, or the initial one if none was found). If several machines are fastest, a fixed one is chosen.
-- source:
--   Hochbaum & Shmoys, A Polynomial Approximation Scheme for Scheduling on Uniform Processors: Using the Dual Approximation Approach, SIAM J. Comput. 17(3) 1988, p. 540, §2 (binary search, U and L) and p. 541, Theorem 1 (iteration count)

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_Packing

namespace HochbaumShmoys.Uniform

/-- A fastest machine (an index maximizing the speed; any one if several tie). -/
noncomputable def fastestMachine {m : ℕ} (s : Fin m → ℝ) (hm : 0 < m) : Fin m :=
  Classical.choose (Finset.exists_max_image Finset.univ s ⟨⟨0, hm⟩, Finset.mem_univ _⟩)

/-- The initial upper bound `U = Σ_j p_j / max_i s_i` (all jobs on the fastest machine). -/
noncomputable def initialUpper {m n : ℕ} (p : Fin n → ℝ) (s : Fin m → ℝ) : ℝ :=
  (∑ j, p j) / (⨆ i, s i)

/-- The initial lower bound `L = Σ_j p_j / (m · max_i s_i)`. -/
noncomputable def initialLower {m n : ℕ} (p : Fin n → ℝ) (s : Fin m → ℝ) : ℝ :=
  (∑ j, p j) / ((m : ℝ) * ⨆ i, s i)

/-- State of the binary search: the current lower and upper bounds and the current schedule. -/
structure SearchState (m n : ℕ) where
  lower : ℝ
  upper : ℝ
  schedule : Fin n → Fin m

/-- One iteration of the binary search of §2: test the midpoint `T` by running the decision
procedure `D` on the deadline-`T` instance (pieces `p j`, bins `T * s i`). If it returns a
packing, the upper bound becomes `T` and that packing is the current schedule; otherwise the
lower bound becomes `T`. -/
noncomputable def searchStep {m n : ℕ}
    (D : (Fin n → ℝ) → (Fin m → ℝ) → Option (Fin n → Fin m))
    (p : Fin n → ℝ) (s : Fin m → ℝ) (st : SearchState m n) : SearchState m n :=
  match D p (fun i => (st.lower + st.upper) / 2 * s i) with
  | some σ => ⟨st.lower, (st.lower + st.upper) / 2, σ⟩
  | none => ⟨(st.lower + st.upper) / 2, st.upper, st.schedule⟩

/-- The binary search procedure driven by `D`, initialized with `L`, `U` and the schedule with all
jobs on a fastest machine, run for `K` iterations; it outputs the schedule kept with the final
upper bound. -/
noncomputable def binarySearch {m n : ℕ}
    (D : (Fin n → ℝ) → (Fin m → ℝ) → Option (Fin n → Fin m))
    (p : Fin n → ℝ) (s : Fin m → ℝ) (hm : 0 < m) (K : ℕ) : Fin n → Fin m :=
  ((searchStep D p s)^[K]
    ⟨initialLower p s, initialUpper p s, fun _ => fastestMachine s hm⟩).schedule

/-- The iteration count `log m + log (3/ε)` of Theorem 1, logarithms to base 2, rounded up
(`0` when the real number is `≤ 0`). -/
noncomputable def iterationCount (m : ℕ) (ε : ℝ) : ℕ :=
  ⌈Real.logb 2 m + Real.logb 2 (3 / ε)⌉₊

end HochbaumShmoys.Uniform


