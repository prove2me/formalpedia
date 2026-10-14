-- Prove2me | Definitions.Def_HighUncertHT_Game_System
-- name    : HighUncertHT_Game_System
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:34:12.448966+00:00
-- url     : https://prove2.me/theorems/bd4948aa-8d04-44d3-ae2c-f26785bf39db
-- title:
--   (1)–(4), pp. 5–8 — arrivals, workload, departures, queue length, idleness, scaling and the holding cost
-- statement:
--   This file describes the $n$-th system as a deterministic function of a sample path of the adversary's control and of the server's cumulative effort.
--
--   A **control path** lists, for each arrival epoch $k/n$ ($k\ge1$), the distributions $\pi^{\ell n}_k$ chosen for the $L$ types and the job sizes $J^{\ell n}_k\ge0$ that arrive at that epoch, one job of each type. An **effort path** $B=(B^\ell)_\ell$ gives the cumulative effort $B^\ell_t$ devoted to type $\ell$ by time $t$; the server works at rate $n$. From these:
--
--   1. the arrived work $A^{\ell n}_t=\sum_{k=1}^{\lfloor nt\rfloor}J^{\ell n}_k$ (1);
--   2. the workload $W^{\ell n}_t=A^{\ell n}_t-nB^{\ell n}_t$ (2);
--   3. the departure count $D^{\ell n}_t$, the largest $k\le\lfloor nt\rfloor$ such that the $k$-th type-$\ell$ job has left by time $t$, i.e. $S^{\ell n}_k=\inf\{s\ge0: nB^{\ell n}_s\ge A^{\ell n}_{k/n}\}\le t$;
--   4. the queue length $Q^{\ell n}_t=\lfloor nt\rfloor-D^{\ell n}_t$ (3) and the idleness $R^n_t=nt-nB^{\mathrm{tot},n}_t$;
--   5. the diffusion-scaled processes $\hat W^{\ell n}=n^{-1/2}W^{\ell n}$, $\hat Q^{\ell n}=n^{-1/2}Q^{\ell n}$ and their totals over $\ell$;
--   6. the norm $\|f\|_t=\sup_{0\le s\le t}|f(s)|$;
--   7. the pathwise discounted holding cost
--   $$
--   \int_0^\infty e^{-t}\,h\cdot\hat Q^n_t\,dt,
--   $$
--   whose expectation is the cost (4).
--
--   **Formalization Note** The control path is shifted to base 0: entry $i$ is the pair chosen at epoch $(i+1)/n$. The departure count is capped at $\lfloor nt\rfloor$: the page's $\sup\{k\ge0:S^{\ell n}_k\le t\}$ would also count not-yet-arrived jobs of size $0$ (a corrected reading; the text defines $D$ as the number of jobs that have left). "$S^{\ell n}_k\le t$" is written as "$nB^{\ell n}_s\ge A^{\ell n}_{k/n}$ for some $s\in[0,t]$", which is equivalent for the continuous effort paths of admissible strategies. The norm and the cost are computed in $[0,\infty]$ (the cost as a lower Lebesgue integral of a nonnegative integrand), so neither can take a junk value.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, pp. 5–8, (1), (2), (3), (4), definitions of S^{ℓn}_k, D^{ℓn}_t, R^n_t, Ŵ^n, Q̂^n (p. 6) and ‖f‖_t (p. 5)

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting

namespace HighUncertHT.Game

open MeasureTheory
open scoped ENNReal

/-!
Atar, Castiel, Shadmi, arXiv:2204.05733v1, §2.1.1–§2.1.2, pp. 5–8, (1)–(4): the `n`-th system as a
deterministic function of a sample path of the adversary's control and of the server's effort path.

* A **control path** `a : ControlPath L` is the paper's `a̲ⁿ = (π̲ⁿ, J̲ⁿ) ∈ (Πⁿ × ℝ^L_+)^ℕ` (p. 7),
  **shifted to base 0**: `a i = (π_{i+1}, J_{i+1})` is the pair chosen at the `(i+1)`-st arrival
  epoch `(i+1)/n`. `(a i).1 ℓ` is the distribution chosen for type `ℓ` and `(a i).2 ℓ` the size of
  the type-`ℓ` job arriving at time `(i+1)/n`.
* An **effort path** `B : EffortPath L` is `t ↦ (B^ℓ_t)_ℓ`; time is real and only `t ≥ 0` is used.

The paper's `Σ_{k=1}^{nt}` is the sum over `1 ≤ k ≤ ⌊nt⌋` (§1.4, p. 4), here `⌊n t⌋₊` terms.
-/

/-- Sample paths of the adversary's control, `(Πⁿ × ℝ^L_+)^ℕ` (p. 7), 0-based (see the module
doc). The ambient type allows any probability measures and real sizes; admissibility conditions
quantify over the paper's subset only (`pathSpace`). -/
abbrev ControlPath (L : ℕ) := ℕ → (Fin L → ProbabilityMeasure ℝ) × (Fin L → ℝ)

/-- Sample paths of the server's cumulative effort `B = (B^ℓ)_ℓ`; real time. -/
abbrev EffortPath (L : ℕ) := ℝ → Fin L → ℝ

variable {L : ℕ}

/-- The arrived work `A^{ℓn}_t = Σ_{k=1}^{⌊nt⌋} J^{ℓn}_k` ((1), p. 5): jobs arrive at `k/n`,
`k ≥ 1`, so `⌊nt⌋` jobs of each type have arrived by time `t`. -/
noncomputable def arrivals (n : ℕ) (a : ControlPath L) (t : ℝ) (ℓ : Fin L) : ℝ :=
  ∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (a i).2 ℓ

/-- The workload `W^{ℓn}_t = A^{ℓn}_t - n B^{ℓn}_t` ((2), p. 5). -/
noncomputable def workload (n : ℕ) (a : ControlPath L) (B : EffortPath L) (t : ℝ) (ℓ : Fin L) : ℝ :=
  arrivals n a t ℓ - n * B t ℓ

open Classical in
/-- The departure count `D^{ℓn}_t` (p. 6): the largest `k ≤ ⌊nt⌋` with `S^{ℓn}_k ≤ t`, where
`S^{ℓn}_k = inf{s ≥ 0 : n B^{ℓn}_s ≥ A^{ℓn}_{k/n}}` is the departure time of the `k`-th type-`ℓ`
job. The cap `k ≤ ⌊nt⌋` is the corrected reading of p. 6 (printed: all `k ≥ 0`, which counts
not-yet-arrived jobs of size `0`). `S^{ℓn}_k ≤ t` is written `∃ s ∈ [0, t], n B^{ℓn}_s ≥ A^{ℓn}_{k/n}`,
which is equivalent for the continuous effort paths of `Lip(Sim)` (the set `{s ≥ 0 : nB_s ≥ c}` is
then closed, so its infimum, `+∞` when empty, is `≤ t` iff it meets `[0, t]`). -/
noncomputable def departures (n : ℕ) (a : ControlPath L) (B : EffortPath L) (t : ℝ) (ℓ : Fin L) : ℕ :=
  ((Finset.range (⌊(n : ℝ) * t⌋₊ + 1)).filter
    (fun k : ℕ => ∃ s ∈ Set.Icc (0 : ℝ) t, arrivals n a ((k : ℝ) / n) ℓ ≤ n * B s ℓ)).sup id

/-- The queue length `Q^{ℓn}_t = ⌊nt⌋ - D^{ℓn}_t` ((3), p. 6). Since `D^{ℓn}_t ≤ ⌊nt⌋`, the
natural-number subtraction is exact. -/
noncomputable def queue (n : ℕ) (a : ControlPath L) (B : EffortPath L) (t : ℝ) (ℓ : Fin L) : ℝ :=
  ((⌊(n : ℝ) * t⌋₊ - departures n a B t ℓ : ℕ) : ℝ)

/-- The idleness `Rⁿ_t = n t - n B^{tot,n}_t` (p. 7). -/
noncomputable def idleness (n : ℕ) (B : EffortPath L) (t : ℝ) : ℝ :=
  n * t - n * ∑ ℓ, B t ℓ

/-- Diffusion scaling `n^{-1/2}` (p. 6). -/
noncomputable def scale (n : ℕ) (x : ℝ) : ℝ := (Real.sqrt n)⁻¹ * x

/-- `Ŵ^{ℓn}_t = n^{-1/2} W^{ℓn}_t` (p. 6). -/
noncomputable def scaledWorkload (n : ℕ) (a : ControlPath L) (B : EffortPath L) (t : ℝ)
    (ℓ : Fin L) : ℝ :=
  scale n (workload n a B t ℓ)

/-- `Ŵ^{tot,n}_t = Σ_ℓ Ŵ^{ℓn}_t`. -/
noncomputable def scaledTotalWorkload (n : ℕ) (a : ControlPath L) (B : EffortPath L) (t : ℝ) : ℝ :=
  ∑ ℓ, scaledWorkload n a B t ℓ

/-- `Q̂^{ℓn}_t = n^{-1/2} Q^{ℓn}_t` (p. 6). -/
noncomputable def scaledQueue (n : ℕ) (a : ControlPath L) (B : EffortPath L) (t : ℝ)
    (ℓ : Fin L) : ℝ :=
  scale n (queue n a B t ℓ)

/-- `Q̂^{tot,n}_t = Σ_ℓ Q̂^{ℓn}_t`. -/
noncomputable def scaledTotalQueue (n : ℕ) (a : ControlPath L) (B : EffortPath L) (t : ℝ) : ℝ :=
  ∑ ℓ, scaledQueue n a B t ℓ

/-- `‖f‖_t = sup_{s ∈ [0, t]} |f(s)|` (§1.4, p. 5), computed in `[0, ∞]` so that it is never a junk
value. -/
noncomputable def supNorm (f : ℝ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ s ∈ Set.Icc (0 : ℝ) t, ENNReal.ofReal |f s|

/-- The pathwise discounted holding cost `∫₀^∞ e^{-t} h · Q̂ⁿ_t dt` inside the expectation (4), p. 6,
as a lower Lebesgue integral in `[0, ∞]` (the integrand is nonnegative). -/
noncomputable def pathCost (S : Setting L) (n : ℕ) (a : ControlPath L) (B : EffortPath L) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioi (0 : ℝ),
    ENNReal.ofReal (Real.exp (-t) * ∑ ℓ, S.h ℓ * scaledQueue n a B t ℓ)

end HighUncertHT.Game


