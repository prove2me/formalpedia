-- Prove2me | Definitions.Def_QMCBeyondHK_haarRun
-- name    : QMCBeyondHK_haarRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:50.327199+00:00
-- url     : https://prove2.me/theorems/cb14dfa1-1500-4a6b-9f5e-3095e66e0f8c
-- title:
--   The Haar-thinning strategy (7), its run, and the uniformly-shifted Haar-thinning algorithm
-- statement:
--   Fix $\varepsilon \in (0,1)$ and a level $\ell$.
--
--   1. For a list $A$ of retained points and a Haar function $H$, the **discrepancy** is $\varphi(H) = \sum_{y \in A} H(y)$.
--   2. The **Haar-thinning target density** (7) is
--   $$
--   \mu(x) := 1 + \frac{\varepsilon}{2N_\ell} \sum_{H \in \Pi_{\le\ell}} \operatorname{sgn}\big(-\varphi(H)\big)\, H(x), \qquad \operatorname{sgn}(0) := 0 .
--   $$
--   3. **One step** on input $(x, \xi, y)$: the point $x$ is accepted iff $\xi \le \mu(x) - \varepsilon/2$; the retained point is $x$ if accepted and $y$ otherwise.
--   4. **The run** on an input stream $(x_t, \xi_t, y_t)_{t \ge 0}$: $A_0$ is empty and $A_{t+1}$ is $A_t$ followed by the point $z_t$ retained at step $t$ with the density built from $A_t$. The output of the **Haar-thinning strategy** with $n$ steps is $A = (z_0,\dots,z_{n-1})$, run with $\ell = \lceil 10\log_2 n \rceil$.
--   5. The **uniformly-shifted Haar-thinning algorithm** with shift $s$ simulates the strategy on $(x_t - s, \xi_t, y_t - s)$ (shifts modulo $[0,1)^d$), and whenever the simulation retains $x_t - s$ it retains the original sample $x_t$, otherwise the original fresh sample $y_t$. Its output is $A_s = (z^s_0,\dots,z^s_{n-1})$.
--   6. The **number of samples** it consumes in $n$ steps is $n$ plus the number of steps $t < n$ at which $x_t$ is rejected.
--
--   **Formalization Note** The run is defined for every $t \in \mathbb N$ by recursion; $\operatorname{sgn}$ is `Real.sign`; the acceptance test is the non-strict $\xi_t \le \mu_t(x_t) - \varepsilon/2$. The samples $x_t$ and the fresh samples $y_t$ are two separate input sequences, which is the same as reading one sequence of samples in order.
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), §2.1, p.7 (PDF p.9): the thinning step, A_t, φ_t; §3.1, (7), p.8 (PDF p.10); §3.1 'Uniformly-Shifted Haar-Thinning', p.9 (PDF p.11)

import Mathlib
import Definitions.Def_QMCBeyondHK_lowOrder

set_option autoImplicit false

open MeasureTheory

namespace QMCBeyondHK

/-- The discrepancy `φ_t(H) := ∑_{y∈A_t} H(y)` of a Haar function on the retained points
(arXiv:2609.10921, sha256 bc273e88…, §2.1, p.7, PDF p.9). -/
noncomputable def disc {d : ℕ} (A : List (Fin d → ℝ)) (H : HaarIdx d) : ℝ := (A.map (haar H)).sum

/-- The Haar-thinning target density (7) (arXiv:2609.10921, sha256 bc273e88…, §3.1, p.8,
PDF p.10): `μ_t(x) := 1 + (ε/(2N_ℓ)) ∑_{H∈Π≤ℓ} sgn(−φ_t(H)) H(x)`, where `A` is the list of points
retained so far.

**Formalization Note** `sgn` is `Real.sign`, so `sgn(0) = 0` as in the paper. -/
noncomputable def density (d : ℕ) (ε : ℝ) (ℓ : ℕ) (A : List (Fin d → ℝ)) (x : Fin d → ℝ) : ℝ :=
  1 + ε / (2 * (Nell d ℓ : ℝ)) * ∑ H ∈ lowOrder d ℓ, Real.sign (-(disc A H)) * haar H x

/-- The acceptance test of the thinning step: `x` is retained iff `ξ ≤ μ_t(x) − ε/2`
(arXiv:2609.10921, sha256 bc273e88…, §2.1, p.7, PDF p.9). -/
def Accepts (d : ℕ) (ε : ℝ) (ℓ : ℕ) (A : List (Fin d → ℝ)) (x : Fin d → ℝ) (ξ : ℝ) : Prop :=
  ξ ≤ density d ε ℓ A x - ε / 2

open Classical in
/-- One Haar-thinning step: retain `x` if it is accepted, otherwise retain the fresh sample `y`
(arXiv:2609.10921, sha256 bc273e88…, §2.1, p.7, PDF p.9). -/
noncomputable def haarStep (d : ℕ) (ε : ℝ) (ℓ : ℕ) (A : List (Fin d → ℝ)) (x : Fin d → ℝ) (ξ : ℝ)
    (y : Fin d → ℝ) : Fin d → ℝ :=
  if Accepts d ε ℓ A x ξ then x else y

/-- The retained list `A_t = (z_0, …, z_{t−1})` of the Haar-thinning strategy after `t` steps on
the input stream `(x_t, ξ_t, y_t)_{t≥0}` (arXiv:2609.10921, sha256 bc273e88…, §2.1, p.7, PDF p.9,
and (7), p.8).

**Formalization Note** The run is defined for every `t ∈ ℕ`; the level `ℓ` is a parameter (the
algorithm uses `ℓ = ell n`). -/
noncomputable def haarRun (d : ℕ) (ε : ℝ) (ℓ : ℕ) (xs : ℕ → Fin d → ℝ) (ξs : ℕ → ℝ)
    (ys : ℕ → Fin d → ℝ) : ℕ → List (Fin d → ℝ)
  | 0 => []
  | t + 1 => haarRun d ε ℓ xs ξs ys t ++
      [haarStep d ε ℓ (haarRun d ε ℓ xs ξs ys t) (xs t) (ξs t) (ys t)]

/-- The point `z_t` retained at step `t` by the Haar-thinning strategy (arXiv:2609.10921,
sha256 bc273e88…, §2.1, p.7, PDF p.9). -/
noncomputable def haarPoint (d : ℕ) (ε : ℝ) (ℓ : ℕ) (xs : ℕ → Fin d → ℝ) (ξs : ℕ → ℝ)
    (ys : ℕ → Fin d → ℝ) (t : ℕ) : Fin d → ℝ :=
  haarStep d ε ℓ (haarRun d ε ℓ xs ξs ys t) (xs t) (ξs t) (ys t)

/-- The output `A = A_n = (z_0, …, z_{n−1})` of the (unshifted) Haar-thinning strategy with
`ℓ = ⌈10 log₂ n⌉` (arXiv:2609.10921, sha256 bc273e88…, §2.1, p.7 and §3.1, p.8). -/
noncomputable def haarOutput (d : ℕ) (ε : ℝ) (n : ℕ) (xs : ℕ → Fin d → ℝ) (ξs : ℕ → ℝ)
    (ys : ℕ → Fin d → ℝ) : Fin n → Fin d → ℝ :=
  fun t => haarPoint d ε (ell n) xs ξs ys t

/-- The simulated run of the uniformly-shifted Haar-thinning algorithm: the Haar-thinning strategy
with `ℓ = ⌈10 log₂ n⌉` on the shifted stream `(x_t − s, ξ_t, y_t − s)` (arXiv:2609.10921,
sha256 bc273e88…, §3.1, p.9, PDF p.11). -/
noncomputable def shiftedRun (d : ℕ) (ε : ℝ) (n : ℕ) (s : Fin d → ℝ) (xs : ℕ → Fin d → ℝ)
    (ξs : ℕ → ℝ) (ys : ℕ → Fin d → ℝ) : ℕ → List (Fin d → ℝ) :=
  haarRun d ε (ell n) (fun u => fracSub (xs u) s) ξs (fun u => fracSub (ys u) s)

/-- The shifted strategy accepts the sample `x_t` at step `t` (it retains `x_t − s` in the
simulated run) (arXiv:2609.10921, sha256 bc273e88…, §3.1, p.9, PDF p.11). -/
def ShiftedAccepts (d : ℕ) (ε : ℝ) (n : ℕ) (s : Fin d → ℝ) (xs : ℕ → Fin d → ℝ) (ξs : ℕ → ℝ)
    (ys : ℕ → Fin d → ℝ) (t : ℕ) : Prop :=
  Accepts d ε (ell n) (shiftedRun d ε n s xs ξs ys t) (fracSub (xs t) s) (ξs t)

open Classical in
/-- The output `A_s` of the uniformly-shifted Haar-thinning algorithm (arXiv:2609.10921,
sha256 bc273e88…, §3.1, p.9, PDF p.11): at step `t` it retains the original sample `x_t` when the
simulated run retains `x_t − s`, and otherwise the original fresh sample `y_t`. -/
noncomputable def shiftedOutput (d : ℕ) (ε : ℝ) (n : ℕ) (s : Fin d → ℝ) (xs : ℕ → Fin d → ℝ)
    (ξs : ℕ → ℝ) (ys : ℕ → Fin d → ℝ) : Fin n → Fin d → ℝ :=
  fun t => if ShiftedAccepts d ε n s xs ξs ys t then xs t else ys t

open Classical in
/-- The number of uniform samples the uniformly-shifted algorithm consumes in its `n` steps: one
sample `x_t` per step plus one fresh sample `y_t` per rejection (arXiv:2609.10921,
sha256 bc273e88…, §2.1 and Proposition 2.4, p.7, PDF p.9). -/
noncomputable def numSamples (d : ℕ) (ε : ℝ) (n : ℕ) (s : Fin d → ℝ) (xs : ℕ → Fin d → ℝ)
    (ξs : ℕ → ℝ) (ys : ℕ → Fin d → ℝ) : ℕ :=
  n + ((Finset.range n).filter (fun t => ¬ ShiftedAccepts d ε n s xs ξs ys t)).card

end QMCBeyondHK


