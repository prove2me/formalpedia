-- Prove2me | Definitions.Def_GenCMu_HeavyTraffic_Sequence
-- name    : GenCMu_HeavyTraffic_Sequence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:05.450839+00:00
-- url     : https://prove2.me/theorems/a748c7b0-63ab-4b93-a223-014c8d18c760
-- title:
--   The heavy-traffic sequence of §3.1: expansions (12)–(13), $R^n = (\bar S^n)^{-1}\circ\bar A^n$ (14), and the scaled processes (21)–(26), (39)
-- statement:
--   A **heavy-traffic sequence** is a sequence of systems $Q^n$, $n \in \mathbb N$, of the kind defined in `GenCMu.HeavyTraffic.Model`, the $n$th one operating during $[0,n]$, together with a decomposition of its arrival and service processes into first- and second-order terms:
--   $$A^n(nt) = n\bar A^n(t) + n^{1/2}\tilde A^n(t) + o(n^{1/2}), \qquad S^n(nt) = n\bar S^n(t) + n^{1/2}\tilde S^n(t) + o(n^{1/2}) \qquad (12)\text{–}(13),$$
--   where the $o(n^{1/2})$ terms are uniform in $t$ and in the class. The trends $\bar A^n_k, \bar S^n_k$ are continuously differentiable and strictly increasing, and the fluctuation terms $\tilde A^n, \tilde S^n$ are continuous. The arrival side is described for $t \in [0,1]$, the service side for $t \in [0,2]$.
--
--   With the inverse $(\bar S^n_k)^{-1}$ one defines
--   $$R^n_k = (\bar S^n_k)^{-1}\circ \bar A^n_k, \qquad R^n_+ = \sum_k R^n_k \qquad (14),$$
--   the first-order approximation of the work input. For a sequence of policies $T^n$ the scaled processes are
--   $$\tilde W^n_k(t) = \frac{W^n_k(nt)}{\sqrt n},\quad \tilde N^n_k(t) = \frac{N^n_k(nt)}{\sqrt n},\quad \tilde\tau^n_k(t) = \frac{\tau^n_k(nt)}{\sqrt n},\quad \tilde T^n_k(t) = \frac{T^n_k(nt) - nR^n_k(t)}{\sqrt n},\quad \tilde L^n_k(t) = \frac{L^n_k(nt) - nR^n_k(t)}{\sqrt n},$$
--   with $\tilde W^n_+ = \sum_k \tilde W^n_k$, and the scaled cumulative cost is $\tilde J^n(t) = n^{-1}J^n(nt)$ (39).
--
--   These are the objects in which Propositions 2–7 are stated.
--
--   **Formalization Note** The paper's expansions (21)–(26) are "only unique in the limit" (p. 826). Here the scaled processes are defined exactly, with the paper's own first-order choices $\bar T^n = \bar L^n = R^n$ ((69), (75), p. 827), so (21), (22), (25), (26) hold with zero remainder and their content is in the convergence statements. The inverse in (14) is the generalized inverse $\inf\{s \in [0,1] : a \le \bar S^n_k(s)\}$, which is the inverse for $a$ in the range and $0$ for $a$ above it. The paper states the trends are continuous and nondecreasing, "so that the inverse functions exist"; we state them continuously differentiable and strictly increasing, which loses nothing because the decomposition is chosen and (12)–(13) are only asymptotic. The paper states the service expansion on $[0,1]$; we state it on server time $[0,2n]$: for $d = 1$ in heavy traffic, $A^n(n)$ may exceed $S^n(n)$, and the service times of the excess jobs, which enter $W^n(n)$, would otherwise be unconstrained.
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), §3.1, pp. 816–818, (12)–(14), (21)–(26), (39); Appendix, (69), (75), p. 827

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model

namespace GenCMu.HeavyTraffic

open Filter Topology Finset

/-- Generalized inverse of a nondecreasing `f` on `[0, 1]`: `inf {s ∈ [0, 1] | a ≤ f s}`. For a
continuous strictly increasing `f` and `a ∈ [f 0, f 1]` it is `f⁻¹(a)`; for `a > f 1` the set is
empty and the value is `sInf ∅ = 0`. -/
noncomputable def genInv (f : ℝ → ℝ) (a : ℝ) : ℝ := sInf {s ∈ Set.Icc (0 : ℝ) 1 | a ≤ f s}

/-- The heavy-traffic sequence of §3.1 (pp. 816–817): systems `Q n`, `n ∈ ℕ`, the `n`th operating
during `[0, n]`, with the first- and second-order terms of (12)–(13),
`Aⁿ(nt) = nĀⁿ(t) + n^{1/2}Ãⁿ(t) + o(n^{1/2})`, `Sⁿ(nt) = nS̄ⁿ(t) + n^{1/2}S̃ⁿ(t) + o(n^{1/2})`.

The decomposition is data, as in the paper. `Ãⁿ, S̃ⁿ` are continuous; the trends `Āⁿ, S̄ⁿ` are
continuously differentiable (the paper: continuous) and strictly increasing (the paper:
nondecreasing "so that the inverse functions exist"). The `o(n^{1/2})` terms are uniform in the
scaled time and in the class.

Domains: the arrival side is described on `[0, 1]` (real time `[0, n]`), the service side on
`[0, 2]` (class-`k` server time `[0, 2n]`). The paper uses `[0, 1]` for both; the longer service
window makes the service times of every job that can arrive by time `n` part of the hypotheses
(for `d = 1` in heavy traffic, `Aⁿ(n)` may exceed `Sⁿ(n)`, and the service times of the excess
jobs are otherwise unconstrained). -/
structure HTSeq (d : ℕ) where
  Q : ℕ → System d
  Abar : ℕ → ℝ → Fin d → ℝ
  Atil : ℕ → ℝ → Fin d → ℝ
  Sbar : ℕ → ℝ → Fin d → ℝ
  Stil : ℕ → ℝ → Fin d → ℝ
  Abar_C1 : ∀ n k, ContDiffOn ℝ 1 (fun t => Abar n t k) (Set.Icc 0 1)
  Sbar_C1 : ∀ n k, ContDiffOn ℝ 1 (fun t => Sbar n t k) (Set.Icc 0 2)
  Atil_cont : ∀ n, ContinuousOn (Atil n) (Set.Icc 0 1)
  Stil_cont : ∀ n, ContinuousOn (Stil n) (Set.Icc 0 2)
  Abar_mono : ∀ n k, StrictMonoOn (fun t => Abar n t k) (Set.Icc 0 1)
  Sbar_mono : ∀ n k, StrictMonoOn (fun t => Sbar n t k) (Set.Icc 0 2)
  /-- (12), uniformly in `t ∈ [0, 1]`. -/
  expA : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ k,
    |((Q n).A k (n * t) : ℝ) - (n * Abar n t k + Real.sqrt n * Atil n t k)| ≤ ε * Real.sqrt n
  /-- (13), uniformly in `t ∈ [0, 2]` (server time up to `2n`). -/
  expS : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc (0 : ℝ) 2, ∀ k,
    |((Q n).S k (n * t) : ℝ) - (n * Sbar n t k + Real.sqrt n * Stil n t k)| ≤ ε * Real.sqrt n

namespace HTSeq

variable {d : ℕ} (H : HTSeq d)

/-- (14): `Rⁿ_k = (S̄ⁿ_k)⁻¹ ∘ Āⁿ_k`. -/
noncomputable def R (n : ℕ) (t : ℝ) (k : Fin d) : ℝ :=
  genInv (fun s => H.Sbar n s k) (H.Abar n t k)
/-- (14): `Rⁿ_+ = Σ_k Rⁿ_k`. -/
noncomputable def Rplus (n : ℕ) (t : ℝ) : ℝ := ∑ k, H.R n t k

/-- Scaled class workload `W̃ⁿ_k(t) = n^{-1/2} Wⁿ_k(nt)`, (25), for a policy sequence `T`. -/
noncomputable def Wt (T : ℕ → Alloc d) (n : ℕ) (t : ℝ) (k : Fin d) : ℝ :=
  (H.Q n).W (T n) k (n * t) / Real.sqrt n
/-- Scaled total workload `W̃ⁿ_+ = Σ_k W̃ⁿ_k`. -/
noncomputable def Wpt (T : ℕ → Alloc d) (n : ℕ) (t : ℝ) : ℝ := ∑ k, H.Wt T n t k
/-- Scaled headcount `Ñⁿ_k(t) = n^{-1/2} Nⁿ_k(nt)`, (21). -/
noncomputable def Nt (T : ℕ → Alloc d) (n : ℕ) (t : ℝ) (k : Fin d) : ℝ :=
  (H.Q n).N (T n) k (n * t) / Real.sqrt n
/-- Scaled delay `τ̃ⁿ_k(t) = n^{-1/2} τⁿ_k(nt)`, (26). -/
noncomputable def taut (T : ℕ → Alloc d) (n : ℕ) (t : ℝ) (k : Fin d) : ℝ :=
  (H.Q n).delay (T n) k (n * t) / Real.sqrt n
/-- Second-order policy term `T̃ⁿ_k(t) = n^{-1/2}(Tⁿ_k(nt) − nRⁿ_k(t))`, (22) with `T̄ⁿ = Rⁿ`
((75), p. 827). -/
noncomputable def Ttil (T : ℕ → Alloc d) (n : ℕ) (t : ℝ) (k : Fin d) : ℝ :=
  (T n (n * t) k - n * H.R n t k) / Real.sqrt n
/-- Second-order work input term `L̃ⁿ_k(t) = n^{-1/2}(Lⁿ_k(nt) − nRⁿ_k(t))`, (68) with `L̄ⁿ = Rⁿ`
((69), p. 827). -/
noncomputable def Ltil (n : ℕ) (t : ℝ) (k : Fin d) : ℝ :=
  ((H.Q n).L k (n * t) - n * H.R n t k) / Real.sqrt n
/-- (39): scaled cumulative cost `J̃ⁿ(t) = n^{-1} Jⁿ(nt)`. -/
noncomputable def Jt (T : ℕ → Alloc d) (n : ℕ) (t : ℝ) : ℝ := (H.Q n).cost (T n) (n * t) / n

end HTSeq

end GenCMu.HeavyTraffic


