-- Prove2me | Definitions.Def_IAFTRL_C37_scalar
-- name    : IAFTRL_C37_scalar
-- status  : Definition
-- author  : @Canzhe Zhao
-- created : 2026-11-15T15:46:21.064226+00:00
-- url     : https://prove2.me/theorems/405ee5c7-43ab-44da-ab42-64c69d2f370b
-- title:
--   Scalar moment objects for the difference interface (Appendix C.6.7–C.6.11, v1)
-- statement:
--   This file fixes the objects of the scalar moment analysis in Appendix C.6.7–C.6.11 of the source. All of them are stated for the abstract full-history difference interface of Lemma C.34.
--
--   **The interface.** `Iface` bundles the hypotheses (C.226)–(C.228). There are $K$ actions with a distinguished action $a^*$ and gaps $\Delta(a^*)=0$, $\Delta_0\le\Delta(a)\le2$. The processes satisfy $X_{0,a}=0$, $X_{t+1,a}=X_{t,a}+D_{t,a}$ and $D_{t,a^*}=0$, together with
--   $$
--   \mathbb E[D_{t,a}\mid\mathcal F_t]=\Delta(a)+e_{t,a},\qquad |e_{t,a}|\le2\kappa_t,\qquad \sum_{t<T}\kappa_t\le C,
--   $$
--   $$
--   |D_{t,a}|\le2\beta_{t+1}+\frac{Z_{t,a}+Z_{t,a^*}}B,\qquad
--   \mathbb E[D_{t,a}^2\mid\mathcal F_t]\le V_{t,a}=4\beta_{t+1}+\frac{2(Z_{t,a}^2+Z_{t,a^*}^2)}{B(t+1)},
--   $$
--   where $Z_{t,a}=X_{t,a}-\min_bX_{t,b}$ (`Zx`) and $V_{t,a}$ is `Venv`.
--
--   **Moment order and constants.** The moment order is $P=2\lceil256+\log(2K)\rceil$ (`Pord`), with $k=K^{1/P}$ (`kK`) and $\nu=3P/4$ (`nuP`). The quantities $H_G$ (`HG`) and $H_0$ (`HN`) are the constants of the supersolutions $A_*n^P+H_Gn^\nu$ and $H_0n^\nu+(64n_0)^P(n/n_0)^q$ for the absolute and negative moments (Definitions C.32, C.35). They are built from $J_G$, $v_G$, $J_0$ and $v$, and $q=\lceil v\rceil$ (`qN`).
--
--   **Processes and events.**
--   - $G_t=\sum_aX_{t,a}^P$ is `Gsum`.
--   - The remaining budget is $b_t=C-\sum_{s<t}\kappa_s$ (`bR`). The negative-part power sum is $F_t=\sum_a(2b_t-X_{t,a})_+^P$ (`Fneg`, with `yN`$=2b-X$ and `vpos` the positive part), as in (C.207).
--   - `survSet m L s` is the window survival event $\{F_j\le L\ \text{for}\ m\le j<s\}$, and `sv` is its indicator (Lemma C.28).
--   - The compensated process (C.197) is $Y_{s,a}=X_{s,a}-\sum_{i<s}e_{i,a}+2C+2\theta$ (`Ecum`, `Yc`).
--   - `Iset m θ s` is the surviving-window event: the budget is not exceeded before $s$, and $F_j\le\theta^P$ for $m\le j\le s$. `Ii` is its indicator.
--   - `kap0` is the distortion exponent $\kappa_0=2(P-1)/B$ of Lemma C.14.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299v1, Appendix C.6.7–C.6.11 (pp.77–90): Lemma C.34 (C.226)–(C.228), Definitions C.17, C.32, C.35, (C.197), (C.207), Lemmas C.14, C.28

import Mathlib
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_Bc

/-!
# Scalar moment machinery for the IA-FTRL difference interface

Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299v1, Appendix C.6.7–C.6.11
(Definitions C.17, C.32, C.35 and the objects of Lemmas C.24–C.37).

* `Iface` bundles the hypotheses of the full-history scalar difference interface (C.226)–(C.228).
* `Pord K = 2⌈256 + log 2K⌉` is the moment order `P`, `kK K = K^{1/P}`, `nuP K = 3P/4`.
* `HG`, `HN` are the absolute- and negative-moment supersolution constants, `qN` the integer exponent
  `⌈v⌉` of the homogeneous negative-moment solution.
* `Gsum` is `G_t = Σ_a X_{t,a}^P`; `bR` the remaining budget `b_t = C − Σ_{s<t} κ_s`; `yN = 2b − X`;
  `Fneg = Σ_a (2b_t − X_{t,a})_+^P`.
* `survSet m L s` is the window survival event `{F_j ≤ L for m ≤ j < s}` and `sv` its indicator.
* `Ecum`, `Yc` give the compensated process `Y_{s,a} = X_{s,a} − Σ_{i<s} e_{i,a} + 2C + 2θ`;
  `Iset m θ s` is the surviving-window event (budget not exceeded and `F_j ≤ θ^P` for `m ≤ j ≤ s`),
  `Ii` its indicator; `kap0 K = 2(P−1)/B` is the multiplicative distortion exponent.
-/

namespace C37

open MeasureTheory Finset

/-- the moment order `P = 2⌈256 + log 2K⌉` -/
noncomputable def Pord (K : ℕ) : ℕ := 2 * ⌈256 + Real.log (2 * (K : ℝ))⌉₊

/-- `C_β = 16 d + √(d/(1 + log K))`, so that `β_n ≤ C_β √n` -/
noncomputable def Cb (d K : ℕ) : ℝ := 16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K))

/-- reference gap `Z_{t,a} = X_{t,a} − min_b X_{t,b}` -/
noncomputable def Zx {K : ℕ} {Ω : Type*} (X : ℕ → Fin K → Ω → ℝ) (t : ℕ) (a : Fin K) (ω : Ω) : ℝ :=
  X t a ω - ⨅ b, X t b ω

/-- second-moment envelope `V_{t,a} = 4β + 2(Z_a² + Z_{a*}²)/(B(t+1))` -/
noncomputable def Venv (d K : ℕ) {Ω : Type*} (X : ℕ → Fin K → Ω → ℝ) (jstar : Fin K) (t : ℕ)
    (a : Fin K) (ω : Ω) : ℝ :=
  4 * IAFTRL.beta d K (t + 1) + 2 * (Zx X t a ω ^ 2 + Zx X t jstar ω ^ 2) / (IAFTRL.Bc K * ((t : ℝ) + 1))

/-- the full-history scalar difference interface (C.226)–(C.228) -/
structure Iface (d K : ℕ) (jstar : Fin K) (Δ : Fin K → ℝ) (Δ₀ : ℝ) {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (F : ℕ → MeasurableSpace Ω) (T : ℕ) (C : ℝ)
    (X D e : ℕ → Fin K → Ω → ℝ) (κ : ℕ → Ω → ℝ) : Prop where
  hd : 1 ≤ d
  hΔ₀ : 0 < Δ₀
  hΔ₀1 : Δ₀ ≤ 1
  hΔj : Δ jstar = 0
  hΔge : ∀ a, a ≠ jstar → Δ₀ ≤ Δ a
  hΔ2 : ∀ a, Δ a ≤ 2
  hT : 1 ≤ T
  hC : 0 ≤ C
  filt : ∀ t < T, F t ≤ mΩ ∧ F t ≤ F (t + 1)
  X0 : ∀ a ω, X 0 a ω = 0
  Xs : ∀ t a ω, X (t + 1) a ω = X t a ω + D t a ω
  Dj : ∀ t ω, D t jstar ω = 0
  Dm : ∀ t < T, ∀ a, Measurable[F (t + 1)] (D t a) ∧ Measurable (D t a)
  κm : ∀ t < T, Measurable[F t] (κ t) ∧ ∀ a, Measurable[F t] (e t a)
  κb : ∀ t < T, ∀ ω, 0 ≤ κ t ω ∧ κ t ω ≤ 2 ∧ ∀ a, |e t a ω| ≤ 2 * κ t ω ∧ |Δ a + e t a ω| ≤ 2
  κsum : ∀ᵐ ω ∂μ, ∑ t ∈ Finset.range T, κ t ω ≤ C
  mean : ∀ t < T, ∀ a, μ[D t a | F t] =ᵐ[μ] fun ω => Δ a + e t a ω
  mag : ∀ t < T, ∀ a ω, |D t a ω| ≤ 2 * IAFTRL.beta d K (t + 1) + (Zx X t a ω + Zx X t jstar ω) / IAFTRL.Bc K
  sec : ∀ t < T, ∀ a, μ[fun ω => D t a ω ^ 2 | F t] ≤ᵐ[μ] Venv d K X jstar t a

/-- `k = K^{1/P}` -/
noncomputable def kK (K : ℕ) : ℝ := (K : ℝ) ^ ((1 : ℝ) / Pord K)

/-- `ν = 3P/4` -/
noncomputable def nuP (K : ℕ) : ℝ := 3 * (Pord K : ℝ) / 4

/-- `h = P/2` -/
noncomputable def hP (K : ℕ) : ℕ := ⌈256 + Real.log (2 * (K : ℝ))⌉₊

/-- constants of the absolute-moment recursion -/
noncomputable def aplus (K : ℕ) : ℝ := 10 * (Pord K : ℝ) ^ 2 * kK K ^ 2 / IAFTRL.Bc K
noncomputable def vG (K : ℕ) : ℝ := (Pord K : ℝ) / 4 + aplus K
noncomputable def cplus (d K : ℕ) : ℝ := 4 * (Pord K : ℝ) ^ 2 * kK K ^ 2 * Cb d K
noncomputable def wplus (d K : ℕ) : ℝ :=
  4 * Cb d K + 640 * (Pord K : ℝ) ^ 2 * kK K ^ 2 * Cb d K ^ 2 / IAFTRL.Bc K
noncomputable def Dplus (d K : ℕ) : ℝ :=
  ((Pord K : ℝ) * (Pord K - 1) / 2) * kK K ^ 2 * (18 * Pord K * kK K * Cb d K) ^ (Pord K - 2) *
    wplus d K
noncomputable def JG (d K : ℕ) : ℝ :=
  cplus d K * (8 * cplus d K / Pord K) ^ (hP K - 1) + Dplus d K

/-- `H_G = max{1, J_G/(ν − v_G)}` -/
noncomputable def HG (d K : ℕ) : ℝ := max 1 (JG d K / (nuP K - vG K))

/-- `G_t = Σ_a X_{t,a}^P` -/
noncomputable def Gsum {K : ℕ} {Ω : Type*} (X : ℕ → Fin K → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, X t a ω ^ Pord K

/-- constants of the negative-moment recursion -/
noncomputable def cminus (d K : ℕ) : ℝ := 6 * (Pord K : ℝ) ^ 2 * kK K ^ 2 * Cb d K
noncomputable def aminus (K : ℕ) : ℝ := 6 * (Pord K : ℝ) ^ 2 * kK K ^ 2 / IAFTRL.Bc K
noncomputable def wminus (d K : ℕ) : ℝ :=
  6 * Cb d K + 1000 * (Pord K : ℝ) ^ 2 * kK K ^ 2 * Cb d K ^ 2 / IAFTRL.Bc K
noncomputable def Dminus (d K : ℕ) : ℝ :=
  ((Pord K : ℝ) * (Pord K - 1) / 2) * kK K ^ 2 * (16 * Pord K * kK K * Cb d K) ^ (Pord K - 2) *
    wminus d K
noncomputable def Lam (K : ℕ) : ℝ := (Pord K : ℝ) / 4096
noncomputable def vN (K : ℕ) : ℝ := aminus K + Lam K
noncomputable def J0 (d K : ℕ) : ℝ :=
  cminus d K * (cminus d K / Lam K) ^ (hP K - 1) + Dminus d K

/-- `H_0 = max{1, J_0/(ν − v)}` and the integer exponent `q = ⌈v⌉` -/
noncomputable def HN (d K : ℕ) : ℝ := max 1 (J0 d K / (nuP K - vN K))
noncomputable def qN (K : ℕ) : ℕ := ⌈vN K⌉₊

/-- positive parts -/
noncomputable def vpos {K : ℕ} (y : Fin K → ℝ) : Fin K → ℝ := fun b => max (y b) 0

section Defs

variable {K : ℕ} {Ω : Type*}

/-- remaining budget `b_t = C − Σ_{s<t} κ_s` -/
noncomputable def bR (C : ℝ) (κ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := C - ∑ s ∈ range t, κ s ω

/-- `y_{t,a} = 2 b_t − X_{t,a}` -/
noncomputable def yN (C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ) (t : ℕ) (a : Fin K) (ω : Ω) : ℝ :=
  2 * bR C κ t ω - X t a ω

/-- `F_t = Σ_a (y_{t,a})_+^P` -/
noncomputable def Fneg (C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, vpos (fun b => yN C κ X t b ω) a ^ Pord K

/-- the survival set `{F_j ≤ L for m ≤ j < s}` -/
def survSet (C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ) (m : ℕ) (L : ℝ) (s : ℕ) : Set Ω :=
  {ω | ∀ j ∈ Finset.Ico m s, Fneg C κ X j ω ≤ L}

/-- its indicator -/
noncomputable def sv (C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ) (m : ℕ) (L : ℝ) (s : ℕ) :
    Ω → ℝ := (survSet C κ X m L s).indicator 1

/-- cumulative signed drift error `E_{s,a} = Σ_{i<s} e_{i,a}` -/
noncomputable def Ecum (e : ℕ → Fin K → Ω → ℝ) (s : ℕ) (a : Fin K) (ω : Ω) : ℝ :=
  ∑ i ∈ range s, e i a ω

/-- the compensated process `Y_{s,a} = X_{s,a} − E_{s,a} + 2C + 2θ` -/
noncomputable def Yc (C θ : ℝ) (X e : ℕ → Fin K → Ω → ℝ) (s : ℕ) (a : Fin K) (ω : Ω) : ℝ :=
  X s a ω - Ecum e s a ω + 2 * C + 2 * θ

/-- the budget is not exceeded before `s` -/
def BokSet (C : ℝ) (κ : ℕ → Ω → ℝ) (s : ℕ) : Set Ω := {ω | ∑ i ∈ range s, κ i ω ≤ C}

/-- the surviving-window event through time `s` -/
def Iset (C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ) (m : ℕ) (θ : ℝ) (s : ℕ) : Set Ω :=
  BokSet C κ s ∩ survSet C κ X m (θ ^ Pord K) (s + 1)

/-- its indicator -/
noncomputable def Ii (C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ) (m : ℕ) (θ : ℝ) (s : ℕ) :
    Ω → ℝ := (Iset C κ X m θ s).indicator 1

end Defs

/-- the multiplicative distortion exponent `κ_0 = 2(P−1)/B` -/
noncomputable def kap0 (K : ℕ) : ℝ := 2 * ((Pord K : ℝ) - 1) / IAFTRL.Bc K

end C37


