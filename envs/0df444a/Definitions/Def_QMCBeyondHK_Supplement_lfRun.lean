-- Prove2me | Definitions.Def_QMCBeyondHK_Supplement_lfRun
-- name    : QMCBeyondHK_Supplement_lfRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:16:10.125448+00:00
-- url     : https://prove2.me/theorems/4069332a-38d6-4691-bf80-db6eb271d807
-- title:
--   Linear-feedback Haar-thinning (14), its run, output, sample count and the FAIL condition
-- statement:
--   This module defines the **linear-feedback Haar-thinning** algorithm of Section 4.1, an instance of the $(1+\varepsilon)$-online thinning framework of Section 2.1.
--
--   Fix $d \ge 1$, $\varepsilon \in (0,1)$, a level $\ell$ and a threshold $B > 0$. Let $\Pi_{\le \ell}$ be the set of non-constant Haar functions $H_{j,k}$ with $j_i \le \ell$ for every coordinate. If $A_t$ is the list of points retained in steps $0, \dots, t-1$ and $\varphi_t(H) = \sum_{y \in A_t} H(y)$ is the discrepancy of the Haar function $H$, the **linear feedback** and the **target density** at step $t$ are
--   $$
--   \Phi_t(x) = \sum_{H \in \Pi_{\le \ell}} \varphi_t(H)\, H(x), \qquad \mu_t(x) = 1 - \frac{\varepsilon}{2B}\,\Phi_t(x). \tag{14}
--   $$
--
--   1. **Step.** At step $t = 0, 1, \dots$ the algorithm reads $x_t \sim \mathrm{Unif}[0,1)^d$ and $\xi_t \sim \mathrm{Unif}[0,1)$. If $\xi_t \le \mu_t(x_t) - \varepsilon/2$ it retains $x_t$; otherwise it retains a fresh sample $y_t \sim \mathrm{Unif}[0,1)^d$. The retained point is $z_t$, and $A_{t+1} = A_t \cup \{z_t\}$, starting from $A_0 = \emptyset$.
--   2. **Output.** After $n$ steps the output is $A = A_n = (z_0, \dots, z_{n-1})$.
--   3. **Sample count.** The algorithm consumes $n$ samples $x_t$ plus one fresh sample $y_t$ for every rejected $x_t$.
--   4. **FAIL (Stopping Condition 4.2).** The algorithm FAILs at time $t$ if $|\Phi_t(x)| > B$ for some $x \in [0,1)^d$. Before it FAILs, $\mu_t(x) \in [1 - \varepsilon/2, 1 + \varepsilon/2]$, so $\mu_t$ is a valid $(1+\varepsilon)$-thinning density.
--   5. **Parameters.** The level and threshold may depend on the step: step $t$ uses $\ell_s(t)$ and $B_s(t)$. The point-set algorithm of §4.1 for a given $n$ uses the constant values $\ell = \lceil \kappa \log_2(nd) \rceil$ and $B = C_B (1 + \log_2 n)^{d+1}$ (`lfLevel`, `lfBudget`), the paper's $\ell = O(\log(nd))$ and $B = O_{d,\varepsilon}(\log^{d+1} n)$ \"for a sufficiently large constant\"; the point sequence of Theorem 1.3 (footnotes 7 and 9) lets them depend on the current step.
--
--   The difference from the Haar-thinning strategy (7) of Section 3 is that $\varphi_t(H)$ itself, not its sign, enters the density, which produces a drift of $\varphi_t(H)$ towards zero proportional to $\varphi_t(H)$.
--
--   **Formalization Note** The run is defined with the unclipped density (14) at every step, so it is defined also after a FAIL; statements about it account for the FAIL event separately. The "modified process" of §4.1 is a device of the proof and is not defined. $\Pi_{\le\ell}$, the Haar functions and $\varphi_t$ are the published `QMCBeyondHK.lowOrder`, `QMCBeyondHK.haar` and `QMCBeyondHK.disc`. The schedules $\ell_s, B_s$ are arguments of the run; `lfLevel` and `lfBudget` give the parameter values for a given number of points.
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), §4.1, eq. (14) and Stopping Condition 4.2, p.16 (PDF p.18); thinning framework §2.1, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_QMCBeyondHK_haarRun

set_option autoImplicit false

open MeasureTheory

namespace QMCBeyondHK.Supplement

/-- The linear feedback `Φ_t(x) = ∑_{H∈Π≤ℓ} φ_t(H) H(x)` of (14), where `A` is the list `A_t` of
points retained so far and `φ_t(H) = ∑_{y∈A_t} H(y)` (arXiv:2609.10921, sha256 bc273e88…, §4.1,
eq. (14), printed p.16, PDF p.18).

**Formalization Note** `Π≤ℓ` is the published `lowOrder d ℓ` (the non-constant Haar functions
with every `j_i ≤ ℓ`) and `φ_t` the published `disc`. -/
noncomputable def feedback (d ℓ : ℕ) (A : List (Fin d → ℝ)) (x : Fin d → ℝ) : ℝ :=
  ∑ H ∈ lowOrder d ℓ, disc A H * haar H x

/-- The target density of linear-feedback Haar-thinning,
`μ_t(x) = 1 − (ε/(2B)) Φ_t(x)` (arXiv:2609.10921, sha256 bc273e88…, §4.1, eq. (14), printed p.16,
PDF p.18). -/
noncomputable def lfDensity (d : ℕ) (ε B : ℝ) (ℓ : ℕ) (A : List (Fin d → ℝ)) (x : Fin d → ℝ) :
    ℝ :=
  1 - ε / (2 * B) * feedback d ℓ A x

/-- The acceptance test of a linear-feedback Haar-thinning step: `x` is retained iff
`ξ ≤ μ_t(x) − ε/2` (arXiv:2609.10921, sha256 bc273e88…, §2.1, printed p.7, PDF p.9, with the
density (14)). -/
def LFAccepts (d : ℕ) (ε B : ℝ) (ℓ : ℕ) (A : List (Fin d → ℝ)) (x : Fin d → ℝ) (ξ : ℝ) : Prop :=
  ξ ≤ lfDensity d ε B ℓ A x - ε / 2

open Classical in
/-- One linear-feedback Haar-thinning step: retain `x` if it is accepted, otherwise retain the
fresh sample `y` (arXiv:2609.10921, sha256 bc273e88…, §2.1, printed p.7, PDF p.9). -/
noncomputable def lfStep (d : ℕ) (ε B : ℝ) (ℓ : ℕ) (A : List (Fin d → ℝ)) (x : Fin d → ℝ) (ξ : ℝ)
    (y : Fin d → ℝ) : Fin d → ℝ :=
  if LFAccepts d ε B ℓ A x ξ then x else y

/-- The retained list `A_t = (z_0, …, z_{t−1})` of linear-feedback Haar-thinning after `t` steps on
the input stream `(x_t, ξ_t, y_t)_{t≥0}`, where step `t` uses the level `ℓs t` and the threshold
`Bs t` (arXiv:2609.10921, sha256 bc273e88…, §2.1, printed p.7, PDF p.9, and §4.1, printed p.16,
PDF p.18, with footnotes 7 and 9).

**Formalization Note** The parameters are schedules `ℓs : ℕ → ℕ`, `Bs : ℕ → ℝ`. The point-set
algorithm of §4.1 for a given `n` is the constant schedule `ℓs t = ℓ`, `Bs t = B`; footnote 9
(p.16) produces the point sequence of Theorem 1.3 by letting the parameters depend on the current
step, as in footnote 7 (p.8: `ℓ = ℓ(t) = O(log t)`). The run uses the unclipped density (14) at
every step, so it is defined for every `t`, also after the algorithm FAILs (Stopping Condition 4.2,
`FailsAt`); every statement about its output also controls the FAIL event. The paper's "modified
process" of §4.1 is a proof device and is not defined here. -/
noncomputable def lfRun (d : ℕ) (ε : ℝ) (ℓs : ℕ → ℕ) (Bs : ℕ → ℝ) (xs : ℕ → Fin d → ℝ)
    (ξs : ℕ → ℝ) (ys : ℕ → Fin d → ℝ) : ℕ → List (Fin d → ℝ)
  | 0 => []
  | t + 1 => lfRun d ε ℓs Bs xs ξs ys t ++
      [lfStep d ε (Bs t) (ℓs t) (lfRun d ε ℓs Bs xs ξs ys t) (xs t) (ξs t) (ys t)]

/-- The point `z_t` retained at step `t` by linear-feedback Haar-thinning with schedules `ℓs, Bs`
(arXiv:2609.10921, sha256 bc273e88…, §2.1, printed p.7, PDF p.9). -/
noncomputable def lfPoint (d : ℕ) (ε : ℝ) (ℓs : ℕ → ℕ) (Bs : ℕ → ℝ) (xs : ℕ → Fin d → ℝ)
    (ξs : ℕ → ℝ) (ys : ℕ → Fin d → ℝ) (t : ℕ) : Fin d → ℝ :=
  lfStep d ε (Bs t) (ℓs t) (lfRun d ε ℓs Bs xs ξs ys t) (xs t) (ξs t) (ys t)

/-- The first `n` points `A_n = (z_0, …, z_{n−1})` of linear-feedback Haar-thinning with schedules
`ℓs, Bs` (arXiv:2609.10921, sha256 bc273e88…, §2.1, printed p.7, PDF p.9). For a point sequence
this is the prefix of length `n` (footnote 2, printed p.1, PDF p.3). -/
noncomputable def lfOutput (d : ℕ) (ε : ℝ) (ℓs : ℕ → ℕ) (Bs : ℕ → ℝ) (n : ℕ)
    (xs : ℕ → Fin d → ℝ) (ξs : ℕ → ℝ) (ys : ℕ → Fin d → ℝ) : Fin n → Fin d → ℝ :=
  fun t => lfPoint d ε ℓs Bs xs ξs ys t

open Classical in
/-- The number of uniform samples linear-feedback Haar-thinning consumes in its first `n` steps:
one sample `x_t` per step plus one fresh sample `y_t` per rejection (arXiv:2609.10921,
sha256 bc273e88…, §2.1 and Proposition 2.4, printed p.7, PDF p.9). -/
noncomputable def lfNumSamples (d : ℕ) (ε : ℝ) (ℓs : ℕ → ℕ) (Bs : ℕ → ℝ) (n : ℕ)
    (xs : ℕ → Fin d → ℝ) (ξs : ℕ → ℝ) (ys : ℕ → Fin d → ℝ) : ℕ :=
  n + ((Finset.range n).filter
    (fun t => ¬ LFAccepts d ε (Bs t) (ℓs t) (lfRun d ε ℓs Bs xs ξs ys t) (xs t) (ξs t))).card

/-- Stopping Condition 4.2: the algorithm FAILs at a time whose retained list is `A` if
`|Φ_t(x)| > B` for some `x ∈ [0,1)^d` (arXiv:2609.10921, sha256 bc273e88…, §4.1, printed p.16,
PDF p.18). Away from FAIL, `μ_t(x) ∈ [1 − ε/2, 1 + ε/2]` on the cube. -/
def FailsAt (d : ℕ) (B : ℝ) (ℓ : ℕ) (A : List (Fin d → ℝ)) : Prop :=
  ∃ x ∈ cube d, B < |feedback d ℓ A x|

/-- The level `ℓ = ⌈κ log₂(nd)⌉` of linear-feedback Haar-thinning, the paper's `ℓ := O(log(nd))`
with its constant `κ` made explicit (for the sequence version, `n` is the current number of points) (arXiv:2609.10921, sha256 bc273e88…, §4.1, printed p.16,
PDF p.18). -/
noncomputable def lfLevel (κ : ℝ) (n d : ℕ) : ℕ := ⌈κ * Real.logb 2 ((n : ℝ) * d)⌉₊

/-- The threshold `B = C_B (1 + log₂ n)^{d+1}` of linear-feedback Haar-thinning, the paper's
`B = O_{d,ε}(log^{d+1} n)` "for a sufficiently large constant" with the constant `C_B` made
explicit (arXiv:2609.10921, sha256 bc273e88…, §4.1, printed p.16, PDF p.18).

**Formalization Note** `1 + log₂ n` in place of `log n`, so that `B > 0` also at `n = 1`. -/
noncomputable def lfBudget (C_B : ℝ) (d n : ℕ) : ℝ := C_B * (1 + Real.logb 2 n) ^ (d + 1)

end QMCBeyondHK.Supplement


