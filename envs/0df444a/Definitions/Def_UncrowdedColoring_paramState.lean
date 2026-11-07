-- Prove2me | Definitions.Def_UncrowdedColoring_paramState
-- name    : UncrowdedColoring_paramState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:35.78484+00:00
-- url     : https://prove2.me/theorems/4249fe24-c031-43ef-a683-c3daf9ff1b3b
-- title:
--   The parameters $\eta,\alpha,\delta,s$ and the sequences $t_i,q_i,\beta_i,\gamma_i,\mathrm{keep}_i,\mathrm{uncolor}_i$
-- statement:
--   Fix $k\ge 2$, $\varepsilon>0$ and $d$. Put
--   $$\eta=\frac{\varepsilon}{6},\quad \alpha=\frac{\eta}{\log d},\quad \delta=d^{-\frac{\eta/6}{k-1}},\quad s=\left\lceil\frac{(1+\eta)\log d\,\log\log d}{\eta(1-\eta)}\right\rceil.$$
--   The sequences start at $t_1=d$, $q_1=(1+\varepsilon)\big((k-1)\tfrac{d}{\log d}\big)^{1/(k-1)}$, and satisfy
--   $$t_{i+1}=(1+\delta)^{k-1}t_i\,\mathrm{keep}_i^{k-1},\qquad q_{i+1}=(1-\delta)q_i\,\mathrm{keep}_i,$$
--   $$\mathrm{keep}_i=1-\frac{\alpha^{k-1}t_i}{q_i^{k-1}}\big(\gamma_{i+1}^{k-1}-\gamma_i^{k-1}\big),\quad \mathrm{uncolor}_i=1-\alpha\,\mathrm{keep}_i,\quad \beta_i=\prod_{j<i}\mathrm{uncolor}_j,\quad \gamma_i=\sum_{j<i}\beta_j.$$
--
--   These numbers govern every stage of the iterated nibble: $q_i$ is the list size and $t_i$ scales the color degrees at stage $i$.
--
--   **Formalization Note** The mutually recursive displays are computed from a state $(t_i,q_i,\beta_i,\gamma_i)$ in the well-founded order the paper describes. Indices are base $1$. The sanity file proves the closed forms for $\beta_i$ and $\gamma_i$ and the display for $\mathrm{keep}_i$.
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), eqs. (13)–(17), p.16

import Mathlib

namespace UncrowdedColoring

/-- `η := ε/6` (eq. (13), p.16). (Dhawan, Methuku, Vo, manuscript sha256 2e7243ce…, p.16.) -/
noncomputable def eta (ε : ℝ) : ℝ := ε / 6

/-- `α := η / log d` (eq. (13), p.16). -/
noncomputable def alpha (ε d : ℝ) : ℝ := eta ε / Real.log d

/-- `δ := d^{−(η/6)/(k−1)}` (eq. (13), p.16). -/
noncomputable def delta (k : ℕ) (ε d : ℝ) : ℝ :=
  d ^ (-(eta ε / 6) / ((k : ℝ) - 1))

/-- `s := ⌈(1 + η) log d log log d / (η(1 − η))⌉` (eq. (13), p.16). -/
noncomputable def numSteps (ε d : ℝ) : ℕ :=
  ⌈(1 + eta ε) * Real.log d * Real.log (Real.log d) / (eta ε * (1 - eta ε))⌉₊

/-- The state `(t_i, q_i, β_i, γ_i)` of the parameter recursion (eqs. (14)–(17), p.16). -/
structure ParamState where
  /-- `t_i` -/
  t : ℝ
  /-- `q_i` -/
  q : ℝ
  /-- `β_i` -/
  β : ℝ
  /-- `γ_i` -/
  γ : ℝ

/-- `keep_i` computed from the state at `i`, using `γ_{i+1} = γ_i + β_i` (eqs. (16), (17), p.16):
`keep_i := 1 − (α^{k−1} t_i / q_i^{k−1}) (γ_{i+1}^{k−1} − γ_i^{k−1})`. -/
noncomputable def keepOf (k : ℕ) (ε d : ℝ) (S : ParamState) : ℝ :=
  1 - alpha ε d ^ (k - 1) * S.t / S.q ^ (k - 1) * ((S.γ + S.β) ^ (k - 1) - S.γ ^ (k - 1))

/-- One step of the recursion (eqs. (15)–(17), p.16):
`t_{i+1} = (1 + δ)^{k−1} t_i keep_i^{k−1}`, `q_{i+1} = (1 − δ) q_i keep_i`,
`β_{i+1} = β_i uncolor_i` with `uncolor_i = 1 − α keep_i`, and `γ_{i+1} = γ_i + β_i`. -/
noncomputable def nextState (k : ℕ) (ε d : ℝ) (S : ParamState) : ParamState where
  t := (1 + delta k ε d) ^ (k - 1) * S.t * keepOf k ε d S ^ (k - 1)
  q := (1 - delta k ε d) * S.q * keepOf k ε d S
  β := S.β * (1 - alpha ε d * keepOf k ε d S)
  γ := S.γ + S.β

/-- The parameter recursion (eqs. (14)–(17), p.16). `paramState k ε d n` is the state at index
`i = n + 1`, with `t_1 = d`, `q_1 = (1 + ε)((k − 1) d / log d)^{1/(k−1)}`, `β_1 = 1` and `γ_1 = 0`.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), eqs. (13)–(17), p.16.

**Formalization Note.** The paper's displays (14)–(17) are mutually recursive and are well founded
in the order the paper explains below (17): `β_i` gives `γ_{i+1}`, which with `t_i`, `q_i` gives
`keep_i`, then `uncolor_i`, `t_{i+1}`, `q_{i+1}`, `β_{i+1}`. That the closed forms
`β_i = ∏_{j<i} uncolor_j` and `γ_i = ∑_{j<i} β_j` of (17) hold is proved in
`Solutions/verification/UncrowdedColoring_sanity.lean`. All powers with exponent `k − 1`, `k − ℓ`,
`ℓ − 1` are natural powers with `k ≥ 2`, `2 ≤ ℓ ≤ k`, so the subtraction does not truncate. -/
noncomputable def paramState (k : ℕ) (ε d : ℝ) : ℕ → ParamState
  | 0 =>
    { t := d
      q := (1 + ε) * (((k : ℝ) - 1) * (d / Real.log d)) ^ (1 / ((k : ℝ) - 1))
      β := 1
      γ := 0 }
  | n + 1 => nextState k ε d (paramState k ε d n)

/-- `t_i` for `i ≥ 1` (index base 1, as in the paper; `i = 0` is never used). -/
noncomputable def tSeq (k : ℕ) (ε d : ℝ) (i : ℕ) : ℝ := (paramState k ε d (i - 1)).t

/-- `q_i` for `i ≥ 1` (index base 1). -/
noncomputable def qSeq (k : ℕ) (ε d : ℝ) (i : ℕ) : ℝ := (paramState k ε d (i - 1)).q

/-- `β_i` for `i ≥ 1` (index base 1). -/
noncomputable def betaSeq (k : ℕ) (ε d : ℝ) (i : ℕ) : ℝ := (paramState k ε d (i - 1)).β

/-- `γ_i` for `i ≥ 1` (index base 1). -/
noncomputable def gammaSeq (k : ℕ) (ε d : ℝ) (i : ℕ) : ℝ := (paramState k ε d (i - 1)).γ

/-- `keep_i` for `i ≥ 1` (eq. (16), p.16). -/
noncomputable def keep (k : ℕ) (ε d : ℝ) (i : ℕ) : ℝ := keepOf k ε d (paramState k ε d (i - 1))

/-- `uncolor_i := 1 − α keep_i` for `i ≥ 1` (eq. (17), p.16). -/
noncomputable def uncolor (k : ℕ) (ε d : ℝ) (i : ℕ) : ℝ := 1 - alpha ε d * keep k ε d i

end UncrowdedColoring


