-- Prove2me | Definitions.Def_RobustKellyTV_oracleE
-- name    : RobustKellyTV_oracleE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:17.189282+00:00
-- url     : https://prove2.me/theorems/44bc9402-1455-4db1-a49c-17e379d20667
-- title:
--   The e-variable class $\mathcal E_0$, the thresholds $a(U),b(U)$, the clipped-Kelly oracle $E_U$, $R_U$ and $h(S,U)$
-- statement:
--   The **one-step e-variable class** is
--
--   $$\mathcal E_0=\Big\{E\in[0,\infty)^d:\ \sup_{R\in\mathcal P_0}\sum_i R_iE_i\le 1\Big\}.$$
--
--   For weights $c\in[0,\infty)^d$ the logarithmic objective is $\sum_i c_i\log E_i$, computed in the extended reals with $\log 0=-\infty$ (zero-weight terms omitted).
--
--   For $U\in\Delta_d^\circ\setminus\mathcal P_0$ the **thresholds** $a(U)$ and $b(U)$ are the positive solutions of
--
--   $$\sum_{i=1}^d (a(U)P_i-U_i)_+=a(U)\epsilon_0,\qquad \sum_{i=1}^d (U_i-b(U)P_i)_+=b(U)\epsilon_0 .$$
--
--   The **pointwise Kelly oracle** clips the nominal likelihood ratio,
--
--   $$E_U(i)=\mathrm{clip}\Big(\frac{U_i}{P_i},a(U),b(U)\Big),\qquad \mathrm{clip}(z,a,b)=\min\{b,\max\{a,z\}\},$$
--
--   and $R_U(i)=U_i/E_U(i)$. For $U\in\mathcal P_0$ the convention is $E_U\equiv 1$ and $R_U=U$. Finally $h(S,U)=\sum_i S_i\log E_U(i)$ is the expected log return under $S$ of the factor designed for $U$.
--
--   These objects are the oracle that the adaptive clipped-Kelly process learns.
--
--   **Formalization Note** The positive root is required because $z=0$ always solves the first equation. The thresholds are chosen (by choice) among the positive roots; Lemma 2.1 shows there is exactly one. $\log 0=-\infty$ is the platform definition `HayashiHoeffding.elog`.
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §2.1 eq. (8) p.6, (10)–(13) p.7, h(S,U) p.8

import Mathlib
import Definitions.Def_RobustKellyTV_Setting
import Definitions.Def_HayashiHoeffding_elog

namespace RobustKellyTV

variable {d : ℕ}

/-- The one-step e-variable class `E0 = {E ≥ 0 : sup_{R ∈ P0} E_R E ≤ 1}` (arXiv:2611.02130v1,
eq. (8), p.6), where `E_R E = Σᵢ Rᵢ Eᵢ`. -/
def eClass (σ : Setting d) : Set (Fin d → ℝ) :=
  {E | (∀ i, 0 ≤ E i) ∧ ∀ R ∈ nullBall σ, ∑ i, R i * E i ≤ 1}

/-- The logarithmic objective `Σᵢ cᵢ log Eᵢ` of (9) and Corollary 2.3 (arXiv:2611.02130v1, pp.6–8),
in the extended reals.

**Formalization Note.** `log 0 = −∞` through `HayashiHoeffding.elog`, so a factor with a zero
coordinate carrying positive weight has objective `−∞`; a zero weight contributes `0 · (−∞) = 0`
in `EReal`, i.e. zero-weight terms are omitted, as on p.24. -/
noncomputable def logObj (c E : Fin d → ℝ) : EReal :=
  ∑ i, (c i : EReal) * HayashiHoeffding.elog (E i)

/-- `z` is a positive solution of the lower-threshold equation (10),
`Σᵢ (z Pᵢ − Uᵢ)₊ = z ϵ0` (arXiv:2611.02130v1, p.7).

**Formalization Note.** `z = 0` always solves (10), so the threshold is a positive root. -/
def IsLowerRoot (σ : Setting d) (U : Fin d → ℝ) (z : ℝ) : Prop :=
  0 < z ∧ ∑ i, max (z * σ.P i - U i) 0 = z * σ.ε₀

/-- `z` is a positive solution of the upper-threshold equation (11),
`Σᵢ (Uᵢ − z Pᵢ)₊ = z ϵ0` (arXiv:2611.02130v1, p.7). -/
def IsUpperRoot (σ : Setting d) (U : Fin d → ℝ) (z : ℝ) : Prop :=
  0 < z ∧ ∑ i, max (U i - z * σ.P i) 0 = z * σ.ε₀

/-- The lower threshold `a(U)`: a positive root of (10) (arXiv:2611.02130v1, p.7). By Lemma 2.1 it
is the unique positive root, and it lies in `(0, 1)`, for `U ∈ ∆°_d \ P0`.

**Formalization Note.** Chosen by `Classical.epsilon` among the positive roots; its value is only
used for `U ∈ ∆°_d \ P0`, where a positive root exists. -/
noncomputable def lowerThr (σ : Setting d) (U : Fin d → ℝ) : ℝ :=
  Classical.epsilon (IsLowerRoot σ U)

/-- The upper threshold `b(U)`: a positive root of (11) (arXiv:2611.02130v1, p.7). By Lemma 2.1 it
is the unique positive root, and it lies in `(1, ∞)`, for `U ∈ ∆°_d \ P0`. -/
noncomputable def upperThr (σ : Setting d) (U : Fin d → ℝ) : ℝ :=
  Classical.epsilon (IsUpperRoot σ U)

/-- `clip(z, a, b) = min{b, max{a, z}}` (arXiv:2611.02130v1, eq. (12), p.7). -/
def clip (z a b : ℝ) : ℝ :=
  min b (max a z)

open Classical in
/-- The pointwise Kelly oracle `E_U` (arXiv:2611.02130v1, eq. (12), p.7):
`E_U(i) = clip(Uᵢ / Pᵢ, a(U), b(U))` for `U ∉ P0`, and the convention `E_U ≡ 1` for `U ∈ P0` (p.7).

**Formalization Note.** The paper defines `E_U` for interior `U`; the formula is evaluated at every
`U`, but every statement applies it to `U ∈ ∆°_d`. -/
noncomputable def oracleE (σ : Setting d) (U : Fin d → ℝ) (i : Fin d) : ℝ :=
  if U ∈ nullBall σ then 1 else clip (U i / σ.P i) (lowerThr σ U) (upperThr σ U)

/-- The reverse projection candidate `R_U(i) = Uᵢ / E_U(i)` (arXiv:2611.02130v1, eq. (13), p.7);
`R_U = U` for `U ∈ P0`. -/
noncomputable def oracleR (σ : Setting d) (U : Fin d → ℝ) (i : Fin d) : ℝ :=
  U i / oracleE σ U i

/-- `h(S, U) = Σᵢ Sᵢ log E_U(i)` (arXiv:2611.02130v1, p.8), the expected log return under `S` of
the factor designed for `U`. For interior `U` every `E_U(i)` is positive, so the real logarithm is
the paper's. -/
noncomputable def hRet (σ : Setting d) (S U : Fin d → ℝ) : ℝ :=
  ∑ i, S i * Real.log (oracleE σ U i)

end RobustKellyTV


