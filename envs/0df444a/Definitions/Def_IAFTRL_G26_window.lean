-- Prove2me | Definitions.Def_IAFTRL_G26_window
-- name    : IAFTRL_G26_window
-- status  : Definition
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:29:30.56256+00:00
-- url     : https://prove2.me/theorems/0f89699d-ebe8-4065-befa-d328e056d01d
-- title:
--   Window parameters, events, and constants for Lemma G.26 (reference blocks, alive window, contraction, good event)
-- statement:
--   This bundle fixes the parameters, events and constants of the compensated projective windows (Definition G.8) used in the proof of Lemma G.26.
--
--   * `Dfar ℬ θ a* ε` $=\{a\in\mathcal K:\Delta(a)\ge\varepsilon\}$ is the far region of Lemma G.29. `Dexpr`, `X1`, `Sref` and `Dref` are the explicit constant, the polynomial threshold, the block start threshold and the block constant of the reference block bound.
--   * `cX1`, `cXB` are the constants of the normalized crossing bound over dyadic blocks, `cTw` is the window threshold for $(m+1)^{1/8}$, and `cCo` is the constant of the contraction step.
--   * `Agood` is the event $\{0\le A_n\le C\ \forall n\le T\}$. `Bad` is the event that the shifted normalized field drops below $4\tau_t$ somewhere on $U_\theta$, i.e. $\max_{U_\theta}(-W^u_t)>-4\tau_t$. The good event of Lemma G.26 is
--   $$
--   G_t=I_t\cap\mathrm{Agood}\cap\mathrm{Bad}^c,\qquad I_t=\{\text{reference }=a^*\text{ and }\max_{D_\theta}(-W^u_j)\le\tau_j\text{ for all }m\le j\le t\}\quad(\texttt{Gev}).
--   $$
--   * Window parameters (0-based rounds): $n_C=\lceil C\rceil+1$ (`nCf`), $H_C=(n_C+1)\log(e(n_C+1))$ (`Hcf`), $m=\lceil M_0H_C\rceil+\lceil\sqrt{H_C(t+1)}\rceil$ (`mw`) and $z=(t+1)\big((m+1)/(t+1)\big)^{7/8}$ (`zw`), with instance constants `M0`, `κ1`, `ε0`, `Uw` and the start time $t_0=\lceil U_wH_C\rceil$ (`t0f`).
--   * `Dθ` is the per-round failure constant $D_\theta$ in $\mathbb P(G_t^c)\le D_\theta\{(t+1)^{-2}+(H_C/(t+1))^2\}$.
--
--   These are the definitions that the window lemmas and the final assembly of Lemma G.26 refer to.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Definition G.8 (G.522)–(G.524) (p.173), Lemma G.26 (p.174), Lemma G.28 (p.178), Lemma G.29 (p.182)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run

-- ===== Solutions.G26.RefBlock =====

/-! ### Uniform reference control on a block (Lemma G.29) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the far region `{a ∈ K : Δ(a) ≥ ε}` -/
def Dfar (ℬ : Set (Fin d → ℝ)) (θ astar : Fin d → ℝ) (ε : ℝ) : Set (Fin d → ℝ) :=
  {a | a ∈ Kset ℬ ∧ ε ≤ gap θ astar a}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

variable (he : Function.Surjective e)
include he

end Sharp

end G26G


-- ===== Solutions.G26.RefAlg3 =====

/-! ### The reference block bound (Lemma G.29): algebra -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the constant of the reference block bound, as a function of `d`, `ς`, and `(D0+1)^8` -/
noncomputable def Dexpr (d : ℕ) (sig c0 : ℝ) : ℝ :=
  cK d * 2 ^ (4 * kk d) + 2 ^ (4 * kk d) * cK d +
    2 ^ (4 * kk d) * 4 ^ d * Hneg (kk d) (16 * d + 1) (gB d) * 4 ^ d * 8 ^ (3 * kk d) * 256 +
    2 ^ (4 * kk d) * 4 ^ d * 2 ^ (d + 2) * 2 ^ (4 * kk d) * (cK d + 2 ^ (4 * kk d)) +
    2 ^ (4 * kk d) * cK d * (2 ^ 32 * (512 ^ 32 + 16 ^ 32)) +
    2 ^ (2 * (4 * kk d) + d) * 4 ^ (4 * kk d) * sig⁻¹ ^ (4 * kk d) *
      (2 ^ (8 * (256 * (d + 1))) *
        (512 ^ (8 * (256 * (d + 1))) *
            ((4 + c0) ^ (512 * (d + 1)) * ((512 * (d + 1)).factorial : ℝ) * 6) +
          16 ^ (8 * (256 * (d + 1))) * (12 + c0) ^ (512 * (d + 1))))

/-- the polynomial threshold for the reference block bound -/
noncomputable def X1 (d : ℕ) : ℝ :=
  (gB d * (16 * d + 4)) ^ 8 + (2 * (((4 * kk d : ℕ) : ℝ) + 1)) ^ 8 +
    (960 * (((4 * kk d : ℕ) : ℝ) + 1) * (16 * d + 1)) ^ 8 + (((4 * kk d : ℕ) : ℝ) + 1)

end G26G


-- ===== Solutions.G26.RefClean =====

/-! ### The reference block bound (Lemma G.29): probabilistic decomposition -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

/-- the block start threshold -/
noncomputable def Sref : ℕ :=
  ⌈4 * X1 d + 2 * H.hs he + ((16 * d + 1) * H.hs he) ^ 8 + 2 ^ 80⌉₊ + 2

/-- the constant of the reference block bound -/
noncomputable def Dref : ℝ := Dexpr d H.sig ((H.D0 he + 1) ^ 8)

end Sharp

end G26G


-- ===== Solutions.G26.WinCross =====

/-! ### The alive window (Lemma G.28): normalized crossings over dyadic blocks -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

/-- the constants of the normalized crossing bound -/
noncomputable def cX1 (_H : Sharp 𝒜 ℬ θ astar) : ℝ :=
  (Lam1 ℬ θ astar / 2) ^ (4 * kk d) * cK d + 4 ^ d * (Lam1 ℬ θ astar ^ (4 * kk d) * cK d + 1)

noncomputable def cXB : ℝ :=
  2 ^ (4 * kk d) * 4 ^ d * Hneg (kk d) (H.kb * (16 * d + 1)) (gB d) * 4 ^ d * 8 ^ (3 * kk d) * 256

end Sharp

end G26G


-- ===== Solutions.G26.WinMom =====

/-! ### The alive window (Lemma G.28): local per-point moments of the compensated variable -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the window threshold for `root8 (n+1)` -/
noncomputable def cTw (d : ℕ) (l kb : ℝ) : ℝ :=
  gB d * (l * (16 * d + 3) + 2) + 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * (16 * d + 1) +
    10 * ((4 * kk d : ℕ) : ℝ) * kb * (16 * d + 1) + (((4 * kk d : ℕ) : ℝ) + 1) + 1

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

end Sharp

end G26G


-- ===== Solutions.G26.WinContr =====

/-! ### Lemma G.26: the contraction step on the projective body -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the event on which the cumulative corruption is within budget -/
def Agood (𝒜 : Set (Fin d → ℝ)) (R : GRun d Ω) (θ : Fin d → ℝ) (C : ℝ) (T : ℕ) : Set Ω :=
  {ω | ∀ n ≤ T, 0 ≤ Acum 𝒜 R θ n ω ∧ Acum 𝒜 R θ n ω ≤ C}

/-- the bad event: the shifted normalized field falls below `4τ_t` somewhere on `U_θ` -/
def Bad (ℬ : Set (Fin d → ℝ)) (𝒜 : Set (Fin d → ℝ)) (R : GRun d Ω) (θ astar : Fin d → ℝ)
    (l C z : ℝ) (t : ℕ) : Set Ω :=
  {ω | -(4 * tauB z t) < negMax (UT ℬ θ astar) (R.cumEst t ω) (cN 𝒜 R θ l C t ω)}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

/-- the constant of the contraction bound -/
noncomputable def cCo (_H : Sharp 𝒜 ℬ θ astar) : ℝ := (2 * Lam1 ℬ θ astar / 7) ^ (4 * kk d) * cK d + 56 ^ (4 * kk d)

end Sharp

end G26G


-- ===== Solutions.G26.WinRatio =====

/-! ### Lemma G.26: uniform ratios for the normalized cumulative loss estimate -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the good event of Lemma G.26 -/
def Gev (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (js : ℕ) (R : GRun d Ω)
    (θ astar : Fin d → ℝ) (l C z : ℝ) (T m t : ℕ) : Set Ω :=
  IN 𝒜 ℬ e js R θ astar l C (tauB z) m t ∩ Agood 𝒜 R θ C T ∩ (Bad ℬ 𝒜 R θ astar l C z t)ᶜ

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

end Sharp

end G26G


-- ===== Solutions.G26.WinPar =====

/-! ### Lemma G.26: the window parameters and the per-round failure bound -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the corruption scale -/
noncomputable def nCf (C : ℝ) : ℕ := ⌈C⌉₊ + 1

noncomputable def Hcf (C : ℝ) : ℝ :=
  ((nCf C : ℝ) + 1) * Real.log (Real.exp 1 * ((nCf C : ℝ) + 1))

/-- the window start and buffer -/
noncomputable def mw (M0 : ℕ) (Hc : ℝ) (t : ℕ) : ℕ := ⌈(M0 : ℝ) * Hc⌉₊ + ⌈Real.sqrt (Hc * ((t : ℝ) + 1))⌉₊

noncomputable def zw (m t : ℕ) : ℝ := ((t : ℝ) + 1) * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 7

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

/-- the window constants -/
noncomputable def M0 : ℕ :=
  ⌈cTw d H.sig⁻¹ H.kb ^ 8 + H.sig⁻¹ + 2 ^ 22⌉₊ + 2 * H.Sref he + 2

omit he in
noncomputable def κ1 (_H : Sharp 𝒜 ℬ θ astar) : ℝ := 2 * (Lam1 ℬ θ astar * max 1 (cK d) + 4) + 16

omit he in
noncomputable def ε0 : ℝ := 1 / (2 * (8 * H.κ1) ^ 8)

noncomputable def Uw : ℝ := 4 * ((H.M0 he : ℝ) + 3) / H.ε0 + 4 / H.ε0 ^ 2 + 256

noncomputable def t0f (C : ℝ) : ℕ := ⌈H.Uw he * Hcf C⌉₊

end Sharp

end G26G


-- ===== Solutions.G26.WinSum =====

/-! ### Lemma G.26: the per-round failure bound and the weighted failure sum -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

/-- the per-round failure constant -/
noncomputable def Dθ : ℝ :=
  300 * H.Dref he + 32 * H.cX1 * (((H.M0 he : ℝ) + 3) ^ 4 + 1) + 18 * H.cXB +
    2 ^ 16 * H.cCo * (1 + 16 * 4 ^ 16 * (((H.M0 he : ℝ) + 3) ^ 4 + 1))

end Sharp

end G26G


