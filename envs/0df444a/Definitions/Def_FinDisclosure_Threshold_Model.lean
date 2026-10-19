-- Prove2me | Definitions.Def_FinDisclosure_Threshold_Model
-- name    : FinDisclosure_Threshold_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:43.194033+00:00
-- url     : https://prove2.me/theorems/ccba0b95-3696-4bb1-ad55-08515c8de6f2
-- title:
--   §2 and §4, pp. 7–34 — financing-and-disclosure model: standing assumptions, price (1), payoff (3), value of a policy, threshold policy (17), problems (30)–(31)
-- statement:
--   The model of Szydlowski's *Optimal Financing and Disclosure*. A project pays $s \in [0,1]$. An entrepreneur must raise the investment cost $I$ by selling a security with payoff $c(s)$ to competitive investors, and chooses how much to disclose about $s$.
--
--   1. **Standing assumptions** (§2, p. 7). $I \in (0,1)$, the private benefit is $B > 0$, and the excess-cash share is $\lambda \in [0,1]$. The security $c$ is continuous on $[0,1]$, both $c(s)$ and the residual $s - c(s)$ are (weakly) increasing in $s$, and $0 \le c(s) \le s$. The prior $\mu_0$ has a continuous density, also written $\mu_0(s)$, which is nonnegative, integrates to $1$ over $[0,1]$, and has support $[0,1]$: every interval $[a,b] \subseteq [0,1]$ with $a < b$ has positive prior mass.
--
--   2. **Price and financing** (1)–(2), p. 8. At posterior $\mu$ the price is $p(\mu) = \mathbb E_\mu c(s)$, and the project is financed iff $p(\mu) \ge I$.
--
--   3. **Entrepreneur's payoff** (3), p. 9:
--   $$V(\mu) = \begin{cases} \mathbb E_\mu[s - c(s) + B] + \lambda\big(\mathbb E_\mu c(s) - I\big) & \text{if } \mathbb E_\mu c(s) \ge I,\\ 0 & \text{otherwise.}\end{cases}$$
--   The value of a distribution $\tau$ over posteriors is $\mathbb E_\tau V(\mu)$, the objective of problem (6).
--
--   4. **Threshold policy** (17), (19), p. 17: truthfully reveal whether $s \ge t$ or $s < t$.
--
--   5. **Fixed-$q$ problems** (30), p. 33, and (31), p. 34. Write $g(s) = s - c(s) + B + \lambda(c(s) - I)$. For $q \in (0,1)$ a density $\mu_h$ on $[0,1]$ is feasible for (30) if it is integrable, $0 \le \mu_h(s) \le \mu_0(s)/q$ for all $s$ (so that $\mu_l = (\mu_0 - q\mu_h)/(1-q) \ge 0$, the Bayes plausibility constraint (13)), $\int_0^1 \mu_h = 1$, and the financing condition (14) holds, $\int_0^1 c(s)\mu_h(s)\,ds \ge I$. Problem (31) relaxes the mass condition to $\int_0^1 \mu_h \le 1$. The objective of both is
--   $$q\int_0^1 g(s)\,\mu_h(s)\,ds,$$
--   and $V(q)$ is its supremum over the feasible set of (30). The threshold density with cutoff $t$ is $\mu_h(s) = \mu_0(s)/q$ for $s \ge t$ and $0$ otherwise, the high posterior of (17) with $\hat S = [t,1]$.
--
--   These are the objects in terms of which the paper's Lemmas 1–6 and Propositions 1, 7 and 8 are stated.
--
--   **Formalization Note** The state space is $\mathbb R$, with $c$ and $\mu_0$ read only on $[0,1]$; the prior is Lebesgue measure on $[0,1]$ with density $\mu_0$. Posterior expectations are taken over $[0,1]$ and written as the difference of the integrals of the positive and negative parts. They equal the ordinary integral whenever it exists, and they are measurable in the posterior, so the value $\mathbb E_\tau V(\mu)$ is never a junk zero. "Increasing" is weak monotonicity, as for debt $\min(s,R)$, one of the paper's examples. The formula (3) is binding: the entrepreneur keeps $\lambda(p - I)$. The sentence on p. 8 that "when $\lambda = 0$, the entrepreneur receives all additional cash" contradicts the formula and is not followed. The equicontinuity restriction (32), p. 34, which the paper imposes on (31) only to prove the compactness Lemma 2, is dropped. `V` is used only where its feasible set is nonempty; that set is always bounded above.
-- source:
--   Szydlowski, Optimal Financing and Disclosure, working paper (version of March 2017), pp. 7–9 (PDF 7–9), §2, eqs. (1)–(6); pp. 15–17 (PDF 15–17), §4, eqs. (13)–(17), (19); pp. 33–34 (PDF 33–34), eqs. (30)–(31)

import Mathlib
import Definitions.Def_FinDisclosure_Threshold_BayesPlausible

open MeasureTheory ProbabilityTheory Set

namespace FinDisclosure.Threshold

/-- Standing assumptions of §2 (p. 7) of Szydlowski, *Optimal Financing and Disclosure*:
`I ∈ (0,1)`, `B > 0`, `λ ∈ [0,1]` (written `lam`); the security `c` is continuous on `[0,1]`, weakly
increasing, with weakly increasing residual `s - c s`, and `c s ∈ [0, s]`; the prior density `f0` is
continuous and nonnegative on `[0,1]`, integrates to `1`, and has support `[0,1]` (every nondegenerate
subinterval of `[0,1]` has positive prior mass). Only the values of `c` and `f0` on `[0,1]` matter. -/
structure Standing (c f0 : ℝ → ℝ) (I B lam : ℝ) : Prop where
  I_pos : 0 < I
  I_lt_one : I < 1
  B_pos : 0 < B
  lam_nonneg : 0 ≤ lam
  lam_le_one : lam ≤ 1
  c_cont : ContinuousOn c (Icc 0 1)
  c_mono : MonotoneOn c (Icc 0 1)
  resid_mono : MonotoneOn (fun s => s - c s) (Icc 0 1)
  c_range : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ c s ∧ c s ≤ s
  f0_cont : ContinuousOn f0 (Icc 0 1)
  f0_nonneg : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ f0 s
  f0_int : ∫ s in (0:ℝ)..1, f0 s = 1
  f0_supp : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → 0 < ∫ s in a..b, f0 s

/-- The prior `µ0` on the state space: the measure on `ℝ` with density `f0` on `[0,1]` and no mass
outside `[0,1]`. -/
noncomputable def prior (f0 : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Icc (0:ℝ) 1)).withDensity (fun s => ENNReal.ofReal (f0 s))

/-- The posterior expectation `E_µ g = ∫_{[0,1]} g dµ`, written as the difference of the integrals of
the positive and negative parts of `g` on `[0,1]` (it equals the Bochner integral
`∫ s in Icc 0 1, g s ∂µ` whenever `g` is `µ`-integrable on `[0,1]`, and is a measurable function of
`µ` for measurable `g`). -/
noncomputable def postExp (μ : Measure ℝ) (g : ℝ → ℝ) : ℝ :=
  (∫⁻ s in Icc (0:ℝ) 1, ENNReal.ofReal (g s) ∂μ).toReal
    - (∫⁻ s in Icc (0:ℝ) 1, ENNReal.ofReal (-g s) ∂μ).toReal

/-- The competitive price (1), p. 8: `p(µ) = E_µ c(s)`. -/
noncomputable def price (c : ℝ → ℝ) (μ : Measure ℝ) : ℝ :=
  postExp μ c

/-- The entrepreneur's expected payoff (3), p. 9, at posterior `µ`: if the project is financed,
`p(µ) ≥ I` (2), it is `E_µ[s - c(s) + B] + λ (E_µ c(s) - I)`; otherwise `0`. -/
noncomputable def payoff (c : ℝ → ℝ) (I B lam : ℝ) (μ : Measure ℝ) : ℝ :=
  if I ≤ price c μ then postExp μ (fun s => s - c s + B) + lam * (price c μ - I) else 0

/-- The value `E_τ V(µ)` of a distribution `τ` over posteriors, the objective of problem (6), p. 9. -/
noncomputable def value (c : ℝ → ℝ) (I B lam : ℝ) (τ : Measure (Measure ℝ)) : ℝ :=
  ∫ μ, payoff c I B lam μ ∂τ

/-- The threshold policy (17), (19), p. 17: truthfully reveal whether `s ≥ t` or `s < t`. -/
noncomputable def thresholdPolicy (f0 : ℝ → ℝ) (t : ℝ) : Measure (Measure ℝ) :=
  revealPolicy (prior f0) (Ici t)

/-- The integrand of (15) and (30): `s - c(s) + B + λ (c(s) - I)`. -/
def gE (c : ℝ → ℝ) (I B lam : ℝ) (s : ℝ) : ℝ :=
  s - c s + B + lam * (c s - I)

/-- Feasibility for problem (30), p. 33, at a fixed `q`: `µh` (a density `mh` on `[0,1]`) is
integrable, `0 ≤ mh ≤ f0 / q` (so that `µl = (µ0 - q µh)/(1 - q) ≥ 0`, Bayes plausibility (13)),
`∫_0^1 mh = 1`, and the financing condition (14) `∫_0^1 c mh ≥ I` holds. -/
def Feas30 (c f0 : ℝ → ℝ) (I q : ℝ) (mh : ℝ → ℝ) : Prop :=
  IntegrableOn mh (Icc 0 1) ∧ (∀ s ∈ Icc (0:ℝ) 1, 0 ≤ mh s ∧ q * mh s ≤ f0 s) ∧
    ∫ s in (0:ℝ)..1, mh s = 1 ∧ I ≤ ∫ s in (0:ℝ)..1, c s * mh s

/-- Feasibility for the relaxed problem (31), p. 34: as `Feas30`, but with `∫_0^1 mh ≤ 1`. -/
def Feas31 (c f0 : ℝ → ℝ) (I q : ℝ) (mh : ℝ → ℝ) : Prop :=
  IntegrableOn mh (Icc 0 1) ∧ (∀ s ∈ Icc (0:ℝ) 1, 0 ≤ mh s ∧ q * mh s ≤ f0 s) ∧
    ∫ s in (0:ℝ)..1, mh s ≤ 1 ∧ I ≤ ∫ s in (0:ℝ)..1, c s * mh s

/-- The objective of (30) and (31): `q ∫_0^1 (s - c(s) + B + λ (c(s) - I)) mh(s) ds`. -/
noncomputable def obj (c : ℝ → ℝ) (I B lam q : ℝ) (mh : ℝ → ℝ) : ℝ :=
  q * ∫ s in (0:ℝ)..1, gE c I B lam s * mh s

/-- The value `V(q)` of problem (30): the supremum of the objective over feasible `mh`. Used only where
the feasible set is nonempty (it is always bounded above). -/
noncomputable def V (c f0 : ℝ → ℝ) (I B lam q : ℝ) : ℝ :=
  sSup (obj c I B lam q '' {mh | Feas30 c f0 I q mh})

/-- The high-posterior density of the threshold policy (17) with `Ŝ = [t, 1]`:
`µh(s) = µ0(s)/q` for `s ≥ t`, `0` otherwise. -/
noncomputable def thresholdDensity (f0 : ℝ → ℝ) (q t : ℝ) (s : ℝ) : ℝ :=
  if t ≤ s then f0 s / q else 0

end FinDisclosure.Threshold


