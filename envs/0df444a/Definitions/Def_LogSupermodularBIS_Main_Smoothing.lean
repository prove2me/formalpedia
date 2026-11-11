-- Prove2me | Definitions.Def_LogSupermodularBIS_Main_Smoothing
-- name    : LogSupermodularBIS_Main_Smoothing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:44.848618+00:00
-- url     : https://prove2.me/theorems/9a8c5563-b878-4c1a-94c4-1a9a10781ca7
-- title:
--   Threshold smoothing: shifted thresholds, the smoothed guide (5.2) and ordered threshold trees
-- statement:
--   Fix a smoothing parameter $w$ and put $h(c)=wc(1-c)$ for $c\in[0,1]$. The loss function is $\Delta_w(c)=H(c)-\tfrac12H(c-h(c))-\tfrac12H(c+h(c))$, the threshold indicator is $\iota_c=\mathbf 1_{[c,1)}$, and the smoothed indicator is
--   $$\phi_c=\tfrac12\mathbf 1_{[c-h(c),1)}+\tfrac12\mathbf 1_{[c+h(c),1)}.\tag{5.8}$$
--
--   The **smoothed guide** (5.2) uses one shared perturbed run: with independent fair signs $\sigma_i\in\{-1,1\}$,
--   $$c^\sigma_i=1-p_i(X^\sigma_{<i}),\qquad X^\sigma_i=\mathbf 1\{U_i\ge c^\sigma_i+\sigma_ih(c^\sigma_i)\},\qquad g(U)=E_\sigma[X^\sigma\mid U],$$
--   the average over the $2^d$ sign vectors at fixed inputs.
--
--   An **ordered threshold tree** (Definition 5.4) on $d$ coordinates compares $u_1,\dots,u_d$ in order with thresholds $c_j\in[0,1]$ chosen by the earlier outcomes $x_1,\dots,x_{j-1}$, records $x_j=\mathbf 1\{u_j\ge c_j\}$, and outputs a real number depending on $x_1,\dots,x_d$. Its perturbed run $T^\sigma(u)$ replaces each reached threshold $c$ by $c+\sigma_jh(c)$, the perturbed outcomes choosing the later thresholds, and its **smoothing** is $g_T(u)=E_\sigma T^\sigma(u)$ (5.1). The variance of a function of the inputs is $\mathrm{Var}(\varphi)=E\varphi^2-(E\varphi)^2$.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), pp. 26–28 (PDF 27–29), Definition 5.4, (5.1), (5.2), (5.8)

import Mathlib
import Definitions.Def_LogSupermodularBIS_Main_Interaction

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-!
# Threshold smoothing (§5.2, pp. 26–28)

A smoothing parameter `w` and a fair sign `σ_j ∈ {−1, +1}` per comparison; signs are encoded as
`Bool` (`true` = `+1`) and averaged uniformly over `Fin d → Bool`.
-/

/-- `h(c) = w c (1 − c)`. -/
noncomputable def shiftAmount (w c : ℝ) : ℝ := w * c * (1 - c)

/-- The sign `±1` of a Boolean sign variable. -/
def signVal (b : Bool) : ℝ := if b then 1 else -1

/-- `Δ_w(c) = H(c) − ½ H(c − h(c)) − ½ H(c + h(c))`. -/
noncomputable def smoothingLoss (w c : ℝ) : ℝ :=
  H c - (1 / 2) * H (c - shiftAmount w c) - (1 / 2) * H (c + shiftAmount w c)

/-- The threshold indicator `ι_c = 1_{[c,1)}` on `(0,1)`. -/
noncomputable def thresholdIndicator (c u : ℝ) : ℝ := if c ≤ u then 1 else 0

/-- The smoothed indicator (5.8): `ϕ_c = ½ 1_{[c−h(c),1)} + ½ 1_{[c+h(c),1)}`. -/
noncomputable def smoothedIndicator (w c u : ℝ) : ℝ :=
  (1 / 2) * thresholdIndicator (c - shiftAmount w c) u +
    (1 / 2) * thresholdIndicator (c + shiftAmount w c) u

/-- The prefix `X^σ_{<i}` of the shared perturbed run (5.2) after `i` steps:
`c^σ_i = 1 − p_i(X^σ_{<i})`, `X^σ_i = 1{U_i ≥ c^σ_i + σ_i h(c^σ_i)}`. -/
noncomputable def perturbedPrefix {d : ℕ} (Φ : (Fin d → Bool) → ℝ) (w : ℝ) (σ : Fin d → Bool)
    (U : Fin d → ℝ) : ℕ → List Bool
  | 0 => []
  | i + 1 =>
      let v := perturbedPrefix Φ w σ U i
      if h : i < d then
        let c := 1 - condMarginal Φ v
        v ++ [decide (c + signVal (σ ⟨i, h⟩) * shiftAmount w c ≤ U ⟨i, h⟩)]
      else v

/-- The coordinates of the shared perturbed run `X^σ(U)`, as reals in `{0,1}`. -/
noncomputable def perturbedRun {d : ℕ} (Φ : (Fin d → Bool) → ℝ) (w : ℝ) (σ : Fin d → Bool)
    (U : Fin d → ℝ) : Fin d → ℝ :=
  fun i =>
    let c := 1 - condMarginal Φ (perturbedPrefix Φ w σ U i.val)
    if c + signVal (σ i) * shiftAmount w c ≤ U i then 1 else 0

/-- The smoothed exact guide (5.2): `g(U) = E_σ[X^σ | U]`, the average of the shared perturbed run
over independent fair signs. -/
noncomputable def smoothedGuide {d : ℕ} (Φ : (Fin d → Bool) → ℝ) (w : ℝ) (U : Fin d → ℝ) :
    Fin d → ℝ :=
  fun i => (∑ σ : Fin d → Bool, perturbedRun Φ w σ U i) / 2 ^ d

/-- Definition 5.4: an ordered threshold tree on `d` coordinates. At each step the input `u_j` is
compared with a threshold `c_j ∈ [0,1]` chosen by the outcomes of the earlier comparisons; the
leaves carry arbitrary real outputs. -/
inductive ThresholdTree : ℕ → Type
  | leaf (r : ℝ) : ThresholdTree 0
  | node {d : ℕ} (c : ℝ) (zero one : ThresholdTree d) : ThresholdTree (d + 1)

/-- All thresholds of the tree lie in `[0,1]`. -/
def ThresholdTree.Valid : {d : ℕ} → ThresholdTree d → Prop
  | 0, .leaf _ => True
  | _, .node c t0 t1 => c ∈ Set.Icc (0 : ℝ) 1 ∧ t0.Valid ∧ t1.Valid

/-- Evaluation: `x_1 = 1{u_1 ≥ c}`; continue in the corresponding subtree with `u_2, …`. -/
noncomputable def ThresholdTree.eval : {d : ℕ} → ThresholdTree d → (Fin d → ℝ) → ℝ
  | 0, .leaf r, _ => r
  | _, .node c t0 t1, u => if c ≤ u 0 then t1.eval (Fin.tail u) else t0.eval (Fin.tail u)

/-- The perturbed run `T^σ(u)`: in each comparison the reached threshold `c` is replaced by
`c + σ_j h(c)`, and the perturbed outcomes choose the later thresholds. -/
noncomputable def ThresholdTree.perturbedEval (w : ℝ) :
    {d : ℕ} → ThresholdTree d → (Fin d → Bool) → (Fin d → ℝ) → ℝ
  | 0, .leaf r, _, _ => r
  | _, .node c t0 t1, σ, u =>
      if c + signVal (σ 0) * shiftAmount w c ≤ u 0 then
        t1.perturbedEval w (Fin.tail σ) (Fin.tail u)
      else t0.perturbedEval w (Fin.tail σ) (Fin.tail u)

/-- The smoothing (5.1) `g_T(u) = E_σ T^σ(u)`. -/
noncomputable def ThresholdTree.smoothing {d : ℕ} (w : ℝ) (T : ThresholdTree d)
    (u : Fin d → ℝ) : ℝ :=
  (∑ σ : Fin d → Bool, T.perturbedEval w σ u) / 2 ^ d

/-- The variance `Var(φ) = E φ² − (E φ)²` under independent uniform inputs. -/
noncomputable def variance {k : ℕ} (φ : (Fin k → ℝ) → ℝ) : ℝ :=
  (∫ u, φ u ^ 2 ∂unifCube k) - (∫ u, φ u ∂unifCube k) ^ 2

end LogSupermodularBIS.Main


