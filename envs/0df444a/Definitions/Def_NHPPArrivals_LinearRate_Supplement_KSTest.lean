-- Prove2me | Definitions.Def_NHPPArrivals_LinearRate_Supplement_KSTest
-- name    : NHPPArrivals_LinearRate_Supplement_KSTest
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:07:44.950657+00:00
-- url     : https://prove2.me/theorems/afc10fe8-4643-4638-9e63-cd7f32367b5f
-- title:
--   Exact CU KS critical value and rejection of pooled actual arrivals
-- statement:
--   For $m$ observations $x$, put $D_m(x)=\sup_{0\le t\le1}|\bar F_m(t)-t|$. Let $U^{(m)}$ have the product law of $m$ independent uniforms on $[0,1]$. The exact null critical value is
--   $$\delta(m,\alpha)=\inf\{d\in[0,1]:P(D_m(U^{(m)})>d)\le\alpha\}.$$
--   For $m\ge1$ and $0<\alpha<1$, continuity of the null statistic's distribution gives tail probability $\alpha$ at this quantile. This is not the numerical approximation $1.36/\sqrt m$.
--   For a process on $[0,T]$ divided into $k$ equal pieces, retain every observed arrival, rescaled within its piece by $u_j=\operatorname{fract}(kX_j/T)$. With the actual random total $M=N(T)$, reject exactly on
--   $$\{M>0,\ D_M(u_1,\ldots,u_M)>\delta(M,\alpha)\}.$$
--   The rejection probability is the probability of this event; the test does not reject at zero arrivals. Fixed endpoints and subinterval boundaries have probability zero under an NHPP with integrable intensity. The infimum set is nonempty (it contains $1$) and bounded below by $0$ at all significance levels used in Theorem 6. The model uses the published degree function, without changing it.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, DOI 10.1287/msom.2014.0490, pp. 465, 474, §1.1 (1)–(2), §3.7 THEOREM 6

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_Supplement_EmpiricalCdf

namespace NHPPArrivals.LinearRate.Supplement

open MeasureTheory ProbabilityTheory

noncomputable def ks {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  degree (empiricalCdf x)

/-- The null law of m independent uniforms. The unit interval has volume one. -/
noncomputable def uniformSampleLaw (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi (fun _ : Fin m => volume.restrict (Set.Icc (0 : ℝ) 1))

/-- Exact upper-tail critical value, not the asymptotic 1.36/sqrt(m).
For m>0 and 0<alpha<1 the null KS distribution is continuous and this
quantile has upper-tail probability alpha. At m=0 no test is performed. -/
noncomputable def criticalValue (m : ℕ) (alpha : ℝ) : ℝ :=
  sInf {d : ℝ | d ∈ Set.Icc (0 : ℝ) 1 ∧
    (uniformSampleLaw m).real {x | d < ks x} ≤ alpha}

/-- Fold every actual arrival into its own subinterval and retain every point.
Endpoints can be assigned to the interval on their right: they have zero law. -/
noncomputable def pooledVector {Ω : Type*} (N : ℝ → Ω → ℕ)
    (X : ℕ → Ω → ℝ) (T : ℝ) (k : ℕ) (ω : Ω) : Fin (N T ω) → ℝ :=
  fun i => Int.fract ((k : ℝ) * X (i : ℕ) ω / T)

noncomputable def rejectionEvent {Ω : Type*} (N : ℝ → Ω → ℕ)
    (X : ℕ → Ω → ℝ) (T : ℝ) (k : ℕ) (alpha : ℝ) : Set Ω :=
  {ω | 0 < N T ω ∧
    criticalValue (N T ω) alpha < ks (pooledVector N X T k ω)}

noncomputable def rejectionProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (N : ℝ → Ω → ℕ) (X : ℕ → Ω → ℝ)
    (T : ℝ) (k : ℕ) (alpha : ℝ) : ℝ :=
  P.real (rejectionEvent N X T k alpha)

end NHPPArrivals.LinearRate.Supplement


