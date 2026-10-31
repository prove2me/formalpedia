-- Prove2me | Definitions.Def_LevyExtrema_SBA_Constants
-- name    : LevyExtrema_SBA_Constants
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:03.251952+00:00
-- url     : https://prove2.me/theorems/f252844c-b898-400d-9868-97596b7d9822
-- title:
--   Explicit constants $C_{p,1},\dots,C_{p,4}$, $m^p_X(t)$ (4.12)–(4.13), $C_p(X)$, $C^*_p(X)$ (4.23)
-- statement:
--   Fix a Lévy triplet $(\sigma^2,\nu,b)$, a horizon $T>0$, an admissible $\delta$ and $p>0$; write $\beta_+$ for the (corrected) index of `betaPlus`, $x^+=\max\{x,0\}$ and $I'=\int_{(0,1)}x^{\beta_+}\nu(dx)$. The constants of Lemma 2 are
--
--   $$C_{p,1}=2^{(p-1)^+}T^{p-p/\beta_+}(I^{\beta_+}_0)^p+T^{-p/\beta_+}\Big(2^pT^{p/2}(I^{\beta_+}_0)^{p/2}\mathbb 1_{\{p\le2\}}+2\big(p^2/(p-1)\big)^p e^{TI^{\beta_+}_0-p}\mathbb 1_{\{p>2\}}\Big),$$
--
--   $$C_{p,2}=|\sigma|^p\,\Gamma\Big(\frac{p+1}2\Big)\frac{2^{p/2}}{\sqrt\pi},\qquad C_{p,3}=2^{(p-1)^+}\big(b^+\mathbb 1_{\{I^1_0=\infty\}}+b_0^+\mathbb 1_{\{I^1_0<\infty\}}\big)^p,$$
--
--   $$C_{p,4}=T^{(1-p/\beta_+)^+}\big(I^p_++I'\big)\sum_{k=1}^{\lceil p\rceil}\Big\{{\lceil p\rceil\atop k}\Big\}T^{k-1}\big(I'+\nu([1,\infty))\big)^{k-1},$$
--
--   with $\{\,m\atop k\,\}$ the Stirling numbers of the second kind, and
--
--   $$m^p_X(t)=4^{(p-1)^+}\big(C_{p,1}t^{p/\beta_+}+C_{p,2}t^{p/2}+C_{p,3}t^p+C_{p,4}t^{\min\{1,p/\beta_+\}}\big).\tag{4.12}$$
--
--   The constants of Corollary 3 are
--
--   $$\frac{C_p(X)}{4^{(p-1)^+}}=\begin{cases}C_{p,1}T^{p/\beta_+-p/\alpha_+}+C_{p,2}+C_{p,3}T^{p-p/\alpha_+}+C_{p,4}T^{\min\{1,p/\beta_+\}-p/\alpha_+},&p\le\alpha,\\ C_{p,1}T^{p/\beta_+-1}+C_{p,2}T^{p/2-1}+C_{p,3}T^{p-1}+C_{p,4},&p>\alpha,\end{cases}\tag{4.23}$$
--
--   and $C^*_p(X)=C_p(X)\mathbb 1_{\{I^p_+<\infty\}}+C_p(-X)\mathbb 1_{\{I^p_+=\infty\}}$, where $C_p(-X)$ is computed from the triplet of $-X$.
--
--   These constants make the moment bounds of Lemma 2 and Corollary 3, and hence the geometric bounds (4.24) of Theorem 2, explicit in the characteristics of $X$.
--
--   **Formalization Note** The Lévy-measure integrals are converted from extended reals with `toReal`; $I^{\beta_+}_0$, $I'$ and $\nu([1,\infty))$ are finite for every Lévy triplet and admissible $\delta$, and every theorem using $C_{p,4}$ assumes $I^p_+<\infty$ (resp. $\min\{I^p_+,I^p_-\}<\infty$ for $C^*_p$), so no infinite value is replaced by $0$. $\lceil p\rceil$ is `⌈p⌉₊`, equal to the integer ceiling for $p>0$; the Stirling numbers are Mathlib's `Nat.stirlingSecond`, which agree with the explicit formula of (4.10).
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, (4.12)–(4.13), p. 22; (4.23), p. 25

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_LevyExtrema_SBA_LevyMeasureIntegrals
import Definitions.Def_LevyExtrema_SBA_naturalDrift
import Definitions.Def_LevyExtrema_SBA_betaPlus
import Definitions.Def_LevyExtrema_SBA_alpha
import Definitions.Def_LevyExtrema_SBA_negTriplet

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-! The explicit constants of Lemma 2 ((4.12)–(4.13), p. 22) and Corollary 3 ((4.23), p. 25) of
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3. Throughout, `T` is the time horizon,
`β₊ = betaPlus Tr δ` (corrected, see `betaPlus`), `(x)^+ = max x 0`, and every `ℝ≥0∞` quantity
is converted with `toReal`; each theorem using these constants carries the paper's finiteness
hypothesis on `I^p_+` (resp. `min{I^p_+, I^p_−}`), and the other `ℝ≥0∞` quantities used here
(`I^{β₊}_0`, `I′`, `ν([1,∞))`) are finite for every Lévy triplet and admissible δ. -/

/-- **I′ = ∫_{(0,1)} x^{β₊} ν(dx)** (p. 22, after (4.13)). -/
noncomputable def Iprime (Tr : Triplet) (δ : ℝ) : ℝ :=
  (∫⁻ x in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (x ^ betaPlus Tr δ) ∂Tr.levyMeasure).toReal

/-- **C_{p,1}**, (4.13), p. 22:
`2^{(p−1)^+} T^{p−p/β₊} (I^{β₊}_0)^p + T^{−p/β₊} (2^p T^{p/2} (I^{β₊}_0)^{p/2} · 1{p≤2}
+ 2 (p²/(p − 1))^p exp(T I^{β₊}_0 − p) · 1{p>2})`. -/
noncomputable def Cp1 (Tr : Triplet) (T : ℝ≥0) (δ p : ℝ) : ℝ :=
  (2 : ℝ) ^ (max (p - 1) 0) * (T : ℝ) ^ (p - p / betaPlus Tr δ) *
      ((I0 Tr (betaPlus Tr δ)).toReal) ^ p +
    (T : ℝ) ^ (-(p / betaPlus Tr δ)) *
      ((if p ≤ 2 then (2 : ℝ) ^ p * (T : ℝ) ^ (p / 2) *
          ((I0 Tr (betaPlus Tr δ)).toReal) ^ (p / 2) else 0) +
        (if 2 < p then 2 * (p ^ 2 / (p - 1)) ^ p *
          Real.exp ((T : ℝ) * (I0 Tr (betaPlus Tr δ)).toReal - p) else 0))

/-- **C_{p,2} = |σ|^p Γ((p + 1)/2) 2^{p/2}/√π**, (4.13), p. 22 (`Real.Gamma`). -/
noncomputable def Cp2 (Tr : Triplet) (p : ℝ) : ℝ :=
  |Tr.σ| ^ p * Real.Gamma ((p + 1) / 2) * (2 : ℝ) ^ (p / 2) / Real.sqrt Real.pi

/-- **C_{p,3} = 2^{(p−1)^+} (b^+ · 1{I^1_0=∞} + b_0^+ · 1{I^1_0<∞})^p**, (4.13), p. 22. -/
noncomputable def Cp3 (Tr : Triplet) (p : ℝ) : ℝ :=
  (2 : ℝ) ^ (max (p - 1) 0) *
    ((if I0 Tr 1 = ⊤ then max Tr.γ 0 else 0) +
      (if I0 Tr 1 < ⊤ then max (naturalDrift Tr) 0 else 0)) ^ p

/-- **C_{p,4}**, (4.13), p. 22:
`T^{(1−p/β₊)^+} (I^p_+ + I′) Σ_{k=1}^{⌈p⌉} {⌈p⌉ k} T^{k−1} (I′ + ν([1, ∞)))^{k−1}`, with
`{m k}` the Stirling numbers of the second kind (`Nat.stirlingSecond`, which agree with the
explicit formula of (4.10)). For `p > 0`, `⌈p⌉₊ = ⌈p⌉`. -/
noncomputable def Cp4 (Tr : Triplet) (T : ℝ≥0) (δ p : ℝ) : ℝ :=
  (T : ℝ) ^ (max (1 - p / betaPlus Tr δ) 0) * ((Iplus Tr p).toReal + Iprime Tr δ) *
    ∑ k ∈ Finset.Icc 1 ⌈p⌉₊, (Nat.stirlingSecond ⌈p⌉₊ k : ℝ) * (T : ℝ) ^ (k - 1) *
      (Iprime Tr δ + (Tr.levyMeasure (Set.Ici 1)).toReal) ^ (k - 1)

/-- **m^p_X(t)**, (4.12), p. 22:
`4^{(p−1)^+} (C_{p,1} t^{p/β₊} + C_{p,2} t^{p/2} + C_{p,3} t^p + C_{p,4} t^{min{1,p/β₊}})`. -/
noncomputable def mpX (Tr : Triplet) (T : ℝ≥0) (δ p : ℝ) (t : ℝ≥0) : ℝ :=
  (4 : ℝ) ^ (max (p - 1) 0) *
    (Cp1 Tr T δ p * (t : ℝ) ^ (p / betaPlus Tr δ) + Cp2 Tr p * (t : ℝ) ^ (p / 2) +
      Cp3 Tr p * (t : ℝ) ^ p + Cp4 Tr T δ p * (t : ℝ) ^ (min 1 (p / betaPlus Tr δ)))

/-- **C_p(X)**, (4.23), p. 25: `C_p(X)/4^{(p−1)^+}` equals
`C_{p,1}T^{p/β₊ − p/α₊} + C_{p,2} + C_{p,3}T^{p − p/α₊} + C_{p,4}T^{min{1, p/β₊} − p/α₊}` if `p ≤ α`,
and `C_{p,1}T^{p/β₊ − 1} + C_{p,2}T^{p/2 − 1} + C_{p,3}T^{p−1} + C_{p,4}` if `p > α`. -/
noncomputable def CpX (Tr : Triplet) (T : ℝ≥0) (δ p : ℝ) : ℝ :=
  (4 : ℝ) ^ (max (p - 1) 0) *
    (if p ≤ alpha Tr then
      Cp1 Tr T δ p * (T : ℝ) ^ (p / betaPlus Tr δ - p / alphaPlus Tr δ) + Cp2 Tr p +
        Cp3 Tr p * (T : ℝ) ^ (p - p / alphaPlus Tr δ) +
        Cp4 Tr T δ p * (T : ℝ) ^ (min 1 (p / betaPlus Tr δ) - p / alphaPlus Tr δ)
    else
      Cp1 Tr T δ p * (T : ℝ) ^ (p / betaPlus Tr δ - 1) + Cp2 Tr p * (T : ℝ) ^ (p / 2 - 1) +
        Cp3 Tr p * (T : ℝ) ^ (p - 1) + Cp4 Tr T δ p)

/-- **C*_p(X) = C_p(X) · 1{I^p_+<∞} + C_p(−X) · 1{I^p_+=∞}**, (4.23), p. 25. `C_p(−X)` is `CpX`
of the triplet of −X (`negTriplet`), with the same δ (β, I^β_0 and hence the admissible δ are the
same for X and −X). -/
noncomputable def CpStar (Tr : Triplet) (T : ℝ≥0) (δ p : ℝ) : ℝ :=
  if Iplus Tr p < ⊤ then CpX Tr T δ p else CpX (negTriplet Tr) T δ p

end LevyExtrema.SBA


