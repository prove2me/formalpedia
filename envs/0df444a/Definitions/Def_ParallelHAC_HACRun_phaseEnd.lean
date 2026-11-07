-- Prove2me | Definitions.Def_ParallelHAC_HACRun_phaseEnd
-- name    : ParallelHAC_HACRun_phaseEnd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:23.912671+00:00
-- url     : https://prove2.me/theorems/26eff857-b933-4467-b70b-a968413f8d46
-- title:
--   Phases $I_j=[s_j,f_j]$ of a HAC run (Definition 9)
-- statement:
--   Fix a HAC run on $P$ ($n=|P|$), a point $x_0\in P$, and the triangle constant $c_\Delta\ge1$. The merges are divided into **phases** $I_j=[s_j,f_j]$, $j=1,2,\dots$, with $f_0=0$ and $s_j=f_{j-1}+1$. Write $\tilde\delta_j=\max_{i\le s_j}\delta_i$ and $\tilde X_j=X_{s_j}$. Then $f_j$ is the maximum integer in $[s_j,n-1]$ such that for every $i\in[s_j,f_j]$:
--
--   1. **Small merges:** $\delta_i\le2\tilde\delta_j$;
--   2. **Small size increase:** $|X_i|<\tfrac32|\tilde X_j|$;
--   3. **Small drift:** $d(\tilde X_j,\bar X_i)\le3c_\Delta\tilde\delta_j$ whenever $X_i$ participates in the $i$-th merge.
--
--   Phases continue until the last merge $n-1$ is reached; the number of phases is the number $J$ of indices $j\ge1$ with $f_{j-1}<n-1$.
--
--   The phases are the bookkeeping device of the proof of Theorem 3: inside a phase, a potential function controls how often $x_0$'s cluster merges.
--
--   **Formalization Note** If no admissible $f$ existed the value would be $0$; for a well-behaved linkage all three conditions hold at $i=s_j$ (p.19), so every phase is nonempty. Once $f_j=n-1$ the sequence stays at $n-1$.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §4.1, Definition 9, p.19 (PDF p.22)

import Mathlib
import Definitions.Def_ParallelHAC_HACRun
import Definitions.Def_ParallelHAC_HACRun_mergeValue
import Definitions.Def_ParallelHAC_HACRun_clusterOf

namespace ParallelHAC

/-!
# Phases `I_j = [s_j, f_j]` (§4.1, Definition 9, p.19)

Source: arXiv:2507.20047 (sha256 a21061c8…), §4.1, p.19.

**Formalization Note.** Merges are indexed `1, …, n − 1` (`n = |P|`). A phase starting at merge `s`
uses `δ̃ = maxMergeValue s = max_{1≤i≤s} δ_i` and `X̃ = X_s`. `phaseEnd j` is `f_j`, with
`f_0 = 0`; once `f_j = n − 1` (the last merge) the sequence stays there, so the phases are the
`j ≥ 1` with `f_{j−1} < n − 1`. The constant `cΔ` is the triangle constant of the linkage, taken
`≥ 1` as on p.19.
-/

/-- The three conditions of Definition 9 at merge `i` for a phase starting at merge `s`:
1. small merges `δ_i ≤ 2 δ̃`; 2. small size increase `|X_i| < (3/2)|X̃|`; 3. small drift
`d(X̃, X̄_i) ≤ 3 cΔ δ̃` if `X_i` participates in the merge, where `X̃ = X_s` and
`δ̃ = max_{i' ≤ s} δ_{i'}` (Definition 9, p.19). -/
def HACRun.PhaseOK {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (cΔ : ℝ) (s i : ℕ) :
    Prop :=
  R.mergeValue i ≤ 2 * R.maxMergeValue s ∧
  ((R.clusterOf x₀ i).card : ℝ) < 3 / 2 * ((R.clusterOf x₀ s).card : ℝ) ∧
  (R.Participates x₀ i → d (R.clusterOf x₀ s) (R.partner x₀ i) ≤ 3 * cΔ * R.maxMergeValue s)

/-- The end `f` of the phase starting at merge `s`: the maximum integer `f ∈ [s, n − 1]` such that
the three conditions of Definition 9 hold for every `i ∈ [s, f]` (Definition 9, p.19).

**Formalization Note.** If no such `f` exists (never the case for a run of a well-behaved linkage,
p.19) the value is `0`. -/
noncomputable def HACRun.phaseEndFrom {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (cΔ : ℝ) (s : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc s (P.card - 1)).filter
    (fun f => ∀ i ∈ Finset.Icc s f, R.PhaseOK x₀ cΔ s i)).sup id

/-- `f_j`, the last merge of the `j`-th phase (Definition 9, p.19): `f_0 = 0` and
`f_j = phaseEndFrom (f_{j−1} + 1)` while `f_{j−1} < n − 1`; it stays at `n − 1` afterwards. -/
noncomputable def HACRun.phaseEnd {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (cΔ : ℝ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if R.phaseEnd x₀ cΔ j < P.card - 1 then
      R.phaseEndFrom x₀ cΔ (R.phaseEnd x₀ cΔ j + 1) else R.phaseEnd x₀ cΔ j

/-- `s_j = f_{j−1} + 1`, the first merge of the `j`-th phase (`j ≥ 1`) (Definition 9, p.19). -/
noncomputable def HACRun.phaseStart {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (cΔ : ℝ) (j : ℕ) : ℕ :=
  R.phaseEnd x₀ cΔ (j - 1) + 1

/-- `j` is a phase: `j ≥ 1` and the previous phase ended before the last merge `n − 1`, i.e.
`s_j ≤ n − 1`. -/
def HACRun.IsPhase {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (cΔ : ℝ) (j : ℕ) : Prop :=
  1 ≤ j ∧ R.phaseEnd x₀ cΔ (j - 1) < P.card - 1

/-- The number of phases: the number of `j ≥ 0` with `f_j < n − 1` (each such `j` is followed by
phase `j + 1`). There are at most `n − 1` phases, since phases are nonempty, so `j` ranges over
`[0, n)`. -/
noncomputable def HACRun.numPhases {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (cΔ : ℝ) : ℕ := by
  classical
  exact ((Finset.range P.card).filter (fun j => R.phaseEnd x₀ cΔ j < P.card - 1)).card

end ParallelHAC


