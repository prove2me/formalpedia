-- Prove2me | Definitions.Def_IAFTRL_G26_run
-- name    : IAFTRL_G26_run
-- status  : Definition
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:28:33.161478+00:00
-- url     : https://prove2.me/theorems/4e7b924a-0d3b-4eae-b240-a0c546be9ecd
-- title:
--   Run-level processes for Lemma G.26: shifted and normalized loss-difference fields, the projective body, and compensated scalar variables
-- statement:
--   This bundle defines the processes built from a GIA-FTRL run $R$ (cumulative loss estimate $S_n=\sum_{j<n}\hat\theta_j$, corrupted loss vectors $\theta_j$) that are fed into the abstract interfaces.
--
--   * `Fx R T n` is the run filtration $\mathcal G_n$ for $n<T$, extended by the full $\sigma$-algebra at $n=T$.
--   * $A_n=\sum_{j<n}\|\theta_j-\theta\|_{\mathcal A}$ (`Acum`), and `cW` is the shift of the remaining-budget field $W_n(a)=(a-a^*)^\top S_n-2(C-A_n)$ of Lemma G.30.
--   * `Sharp 𝒜 ℬ θ astar` bundles the standing hypotheses of the sharp instance: $1\le d$, compactness, $\mathcal B$ generates $\mathcal A$, $\mathcal A$ in the unit ball and spanning, $\dim\mathcal K\ge1$, $\|\theta\|_{\mathcal A}\le1$, $a^*$ the unique optimal action, and sharpness. `H.sig` is a chosen sharpness modulus $\varsigma$, $\Delta(a)=(a-a^*)^\top\theta$ is `gap`.
--   * The projective body of Lemma G.16:
--   $$
--   U_\theta=\overline{\big\{\Delta(a)^{-1}(a-a^*):a\in\mathcal K\setminus\{a^*\}\big\}},\qquad D_\theta=\{\lambda u:\lambda\in[0,1],\ u\in U_\theta\}.
--   $$
--   `Lam1` is a constant $\Lambda_1$ for the projective extension (G.306), and `kb` $=\varsigma^{-2}+\varsigma^{-1}+1$.
--   * `goodS ℬ e j* n S` states that the atom $j^*$ of $a^*$ is the strict minimizer of the penalized reference problem (3.4) at round $n$ and score $S$. `js` is the index of $a^*$ among the first-occurrence atoms, `hs` its prior penalty, and `D0` the sum of the inverse $\mathcal S$-distances of the earlier atoms.
--   * `cN` is the shift $-\Lambda(C-A_n)$ of the normalized field $W^u_n(u)=u^\top S_n-\Lambda(C-A_n)$ on $D_\theta$. `JN m n` is the event that the reference was strictly $a^*$ at every round in $[m,n]$.
--   * Compensated scalar variables: $E_n(w)=\sum_{j<n}w^\top(\theta_j-\theta)$ (`Ecor`),
--   $$
--   Y^F_n(a)=(a-a^*)^\top S_n-E_n(a-a^*)+2C+2\tau_n\ (\texttt{YF}),\qquad Y^\dagger_n(u)=u^\top S_n-E_n(u)+\Lambda C+2\tau_n\ (\texttt{YN}),
--   $$
--   with alive events `IW` (no negative crossing of $W$ since $m_0$) and `IN` (reference $a^*$ and no normalized negative crossing since $m$), as in (G.523), (G.597) and (G.636).
--   * Constants: `kk d` $=1024(d+1)$ (moment order $P=4k$), `cK d` (the absolute-envelope constant), the buffer `tauB z s` $=(s+1)^{7/8}+4z$, and `root8 x` $=x^{1/8}$.
--
--   These objects instantiate the interfaces of the body bundle for the run-level estimates in Lemmas G.26–G.30.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Lemma G.10 (p.138), Lemma G.16 (p.153), Lemma G.17 (p.154), Definition G.8 (p.173), Lemmas G.28–G.30 (pp.178–188), (G.595)–(G.601), (G.635)–(G.641)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body

-- ===== Solutions.G26.RunK =====

/-! ### The loss-difference field on `K` satisfies the field interface (Lemma G.10) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}

section

variable (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤)
include hd hℬ hgen hspan

end

end G26R

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the filtration extended by `mΩ` at the horizon -/
def Fx (R : GRun d Ω) (T : ℕ) (n : ℕ) : MeasurableSpace Ω := if n < T then R.G n else mΩ

end G26R


-- ===== Solutions.G26.RunW =====

/-! ### The remaining-budget shifted field on `K` (Lemma G.30) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26R

open G26

variable {d : ℕ}

/-- the realized cumulative corruption `A_n = Σ_{j<n} ‖θ_j − θ‖_𝒜` -/
noncomputable def Acum {Ω : Type*} (𝒜 : Set (Fin d → ℝ)) (R : GRun d Ω) (θ : Fin d → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range n, setNorm 𝒜 (R.θs j ω - θ)

/-- the shift of the remaining-budget field -/
noncomputable def cW {Ω : Type*} (𝒜 : Set (Fin d → ℝ)) (R : GRun d Ω) (θ astar : Fin d → ℝ) (C : ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  -(astar ⬝ᵥ R.cumEst n ω) - 2 * (C - Acum 𝒜 R θ n ω)

variable {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

end G26R

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

end G26R


-- ===== Solutions.G26.Geo =====

/-! ### The projective body of normalized directions (Lemma G.16) -/

open MeasureTheory ProbabilityTheory Set IAFTRL

namespace G26G

open G26

variable {d : ℕ}

/-- the standing hypotheses of the sharp corrupted setting -/
structure Sharp (𝒜 ℬ : Set (Fin d → ℝ)) (θ astar : Fin d → ℝ) : Prop where
  hd : 1 ≤ d
  h𝒜 : IsCompact 𝒜
  hℬ : IsCompact ℬ
  hgen : IsGenerator 𝒜 ℬ
  hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1
  hspan : Submodule.span ℝ 𝒜 = ⊤
  hk : 1 ≤ kdim ℬ
  hθ : setNorm 𝒜 θ ≤ 1
  hastar : astar ∈ 𝒜
  huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ
  hsharp : IsSharp 𝒜 θ astar

variable {𝒜 ℬ : Set (Fin d → ℝ)} {θ astar : Fin d → ℝ}

/-- the gap `Δ(a) = (a − a*)ᵀθ` -/
def gap (θ astar a : Fin d → ℝ) : ℝ := (a - astar) ⬝ᵥ θ

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

/-- the sharpness modulus -/
noncomputable def sig : ℝ := Classical.choose H.hsharp

end Sharp

/-- the normalized direction of an action -/
noncomputable def ndir (θ astar a : Fin d → ℝ) : Fin d → ℝ := (gap θ astar a)⁻¹ • (a - astar)

/-- normalized directions of positive-gap actions -/
def U0 (ℬ : Set (Fin d → ℝ)) (θ astar : Fin d → ℝ) : Set (Fin d → ℝ) :=
  ndir θ astar '' (Kset ℬ \ {astar})

/-- the projective body `U_θ` -/
def UT (ℬ : Set (Fin d → ℝ)) (θ astar : Fin d → ℝ) : Set (Fin d → ℝ) := closure (U0 ℬ θ astar)

/-- the cone body `D_θ = {λu : λ ∈ [0,1], u ∈ U_θ}` -/
def DT (ℬ : Set (Fin d → ℝ)) (θ astar : Fin d → ℝ) : Set (Fin d → ℝ) :=
  (fun q : ℝ × (Fin d → ℝ) => q.1 • q.2) '' (Icc (0 : ℝ) 1 ×ˢ UT ℬ θ astar)

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

end Sharp

end G26G


-- ===== Solutions.G26.RefGood =====

/-! ### A measurable sufficient condition for the reference to be `a*` -/

open MeasureTheory ProbabilityTheory Set IAFTRL

namespace G26G

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}

/-- strict optimality of the atom `j*` in the penalized reference problem (3.4) -/
def goodS (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (js : ℕ) (n : ℕ) (S : Fin d → ℝ) : Prop :=
  ∀ i ∈ Jset ℬ e, i ≠ js →
    cand ℬ e js ⬝ᵥ S + gbeta d n * hPen ℬ e js < cand ℬ e i ⬝ᵥ S + gbeta d n * hPen ℬ e i

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

omit H he in
/-- the index of `a*` among the reference atoms -/
noncomputable def js (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (astar : Fin d → ℝ) : ℕ :=
  open Classical in
  if h : ∃ m ∈ Jset ℬ e, cand ℬ e m = astar then Classical.choose h else 0

/-- the prior penalty of `a*` -/
noncomputable def hs (_H : Sharp 𝒜 ℬ θ astar) (_he : Function.Surjective e) : ℝ :=
  hPen ℬ e (js ℬ e astar)

open Classical in
/-- the inverse distances of the earlier atoms -/
noncomputable def D0 (_H : Sharp 𝒜 ℬ θ astar) (_he : Function.Surjective e) : ℝ :=
  ∑ i ∈ (Finset.range (js ℬ e astar)).filter (· ∈ Jset ℬ e), (sNorm ℬ (cand ℬ e i - astar))⁻¹

end Sharp

end G26G


-- ===== Solutions.G26.RunN =====

/-! ### The normalized field on the cone body satisfies the field interface (Lemmas G.17, G.28) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

omit H in
/-- the constant of the projective extension (G.306) -/
noncomputable def Lam1 (ℬ : Set (Fin d → ℝ)) (θ astar : Fin d → ℝ) : ℝ :=
  open Classical in
  if h : ∃ Λ1 : ℝ, 0 < Λ1 ∧ ∀ (w : Fin d → ℝ) (M : ℝ),
      (∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ w| ≤ M) → ∀ u ∈ DT ℬ θ astar, |u ⬝ᵥ w| ≤ Λ1 * M
  then Classical.choose h else 1

/-- the variance constant of the normalized field -/
noncomputable def kb : ℝ := H.sig⁻¹ ^ 2 + H.sig⁻¹ + 1

end Sharp

end G26G

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the remaining-budget shift of the normalized field -/
noncomputable def cN (𝒜 : Set (Fin d → ℝ)) (R : GRun d Ω) (θ : Fin d → ℝ) (l C : ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  -(l * (C - Acum 𝒜 R θ n ω))

/-- the reference has been `a*` (strictly) at every round of `[m, n]` -/
def JN (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (js : ℕ) (R : GRun d Ω) (m n : ℕ) : Set Ω :=
  {ω | ∀ j, m ≤ j → j ≤ n → goodS ℬ e js (j + 1) (R.cumEst j ω)}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

end Sharp

end G26G


-- ===== Solutions.G26.RunSI =====

/-! ### Compensated per-action scalar processes (Lemma G.29, (G.635)–(G.641)) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the corruption accumulated in the direction `w` -/
noncomputable def Ecor (R : GRun d Ω) (θ w : Fin d → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range n, w ⬝ᵥ (R.θs j ω - θ)

/-- the compensated positive variable of an action, (G.636) -/
noncomputable def YF (R : GRun d Ω) (θ astar : Fin d → ℝ) (C : ℝ) (τ : ℕ → ℝ) (a : Fin d → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  (a - astar) ⬝ᵥ R.cumEst n ω - Ecor R θ (a - astar) n ω + 2 * C + 2 * τ n

/-- no negative crossing of the remaining-budget field since `m0` -/
def IW (𝒜 ℬ : Set (Fin d → ℝ)) (R : GRun d Ω) (θ astar : Fin d → ℝ) (C : ℝ) (τ : ℕ → ℝ)
    (m0 n : ℕ) : Set Ω :=
  {ω | ∀ j, m0 ≤ j → j ≤ n → negMax (Kset ℬ) (R.cumEst j ω) (cW 𝒜 R θ astar C j ω) ≤ τ j}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

end Sharp

end G26G


-- ===== Solutions.G26.RunSIN =====

/-! ### Compensated normalized pointwise variables (Lemma G.28, (G.595)–(G.601)) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the compensated normalized variable of a direction, (G.596) -/
noncomputable def YN (R : GRun d Ω) (θ : Fin d → ℝ) (l C : ℝ) (τ : ℕ → ℝ) (u : Fin d → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  u ⬝ᵥ R.cumEst n ω - Ecor R θ u n ω + l * C + 2 * τ n

/-- references strictly `a*` and no normalized negative crossing since `m` -/
def IN (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (js : ℕ) (R : GRun d Ω) (θ astar : Fin d → ℝ)
    (l C : ℝ) (τ : ℕ → ℝ) (m n : ℕ) : Set Ω :=
  JN ℬ e js R m n ∩
    {ω | ∀ j, m ≤ j → j ≤ n → negMax (DT ℬ θ astar) (R.cumEst j ω) (cN 𝒜 R θ l C j ω) ≤ τ j}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

end Sharp

end G26G


-- ===== Solutions.G26.RunEnv =====

/-! ### Envelopes of the run fields: absolute maxima and block crossings (Lemmas G.15, G.30) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26

variable {d : ℕ} {Ω : Type*}

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end G26

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the moment order `P = 4k`, `k = 1024(d+1)` -/
@[irreducible] def kk (d : ℕ) : ℕ := 1024 * (d + 1)

/-- the absolute-envelope constant -/
noncomputable def cK (d : ℕ) : ℝ :=
  2 ^ (4 * kk d) * 4 ^ d * Cabs (4 * kk d) (16 * d + 1) (gB d) 0

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

end Sharp

end G26G


-- ===== Solutions.G26.Params =====

/-! ### Thresholds: buffers `τ_s = (s+1)^{7/8} + 4z` and logarithmic gap cutoffs -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

/-- the moving buffer with plateau `z` -/
noncomputable def tauB (z : ℝ) (s : ℕ) : ℝ := ((s : ℝ) + 1) ^ ((7 : ℝ) / 8) + 4 * z

/-- an eighth root -/
noncomputable def root8 (x : ℝ) : ℝ := Real.sqrt (Real.sqrt (Real.sqrt x))

end G26G

namespace G26G

end G26G


