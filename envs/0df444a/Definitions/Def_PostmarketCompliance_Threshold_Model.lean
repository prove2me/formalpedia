-- Prove2me | Definitions.Def_PostmarketCompliance_Threshold_Model
-- name    : PostmarketCompliance_Threshold_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:29.46208+00:00
-- url     : https://prove2.me/theorems/8bb149f6-2166-4924-bf5e-8fdd21d289b3
-- title:
--   §§3–4 — post-market study model, profit, compliance, and cost-type threshold
-- statement:
--   A regulator sets a deadline $d$ for a drug’s post-market study. Patent expiry is $T$, the profit rates before and after regular approval are $\pi_A$ and $\pi_R$, study success has probability $\alpha$, and withdrawal after a missed deadline takes an exponential time of rate $s$. A study requiring $n$ patients completes at Gamma$(n,\lambda)$ time when recruitment effort $\lambda>0$. The manufacturer pays effort cost $\theta\lambda^k$.
--
--   For withdrawal delay $\tau$, set $\tilde d=\min(d+\tau,T)$. The model’s revenue and positive-effort profit are
--
--   $$
--   \phi(t,\tau)=\begin{cases}t\pi_A+(T-t)\alpha\pi_R,&t\le\tilde d,\\\tilde d\pi_A,&t>\tilde d,\end{cases}
--   \qquad
--   \Pi(\lambda,d,\theta)=\mathbb E_t\mathbb E_\tau[\phi(t,\tau)]-\theta\lambda^k.
--   $$
--
--   At zero effort the study never completes and profit is $\Pi_N(d)=\mathbb E_\tau[\tilde d]\pi_A$. Compliance means that a positive effort actually maximizes profit over all nonnegative efforts, including a tie with zero. The compliant cost types are positive $\theta$ for which some $d\in[0,T]$ induces compliance, and $\hat\theta$ is their supremum.
--
--   These definitions supply the common model for every theorem in the mission.
--
--   **Formalization Note** The standing regime has $T>0$, $0<\pi_A\le\pi_R$, $0<\alpha\le1$, $s>0$, and $1\le k<n$. The last three restrictions beyond the paper’s explicit $k\ge1$ are disclosed in the mission scope. Gamma measure at rate zero is replaced by the paper’s no-study branch.
-- source:
--   Xu, Zhao & Petruzzi, Inducing Compliance with Post-Market Studies for Drugs under FDA's Accelerated Approval Pathway, SSRN 3471632 (version of March 2019), pp. 7–12 (PDF 8–13), §§3–4

import Mathlib

namespace PostmarketCompliance.Threshold

open MeasureTheory ProbabilityTheory

structure Params where
  T : ℝ
  piA : ℝ
  piR : ℝ
  alpha : ℝ
  s : ℝ
  n : ℕ
  k : ℝ

def Params.Standing (P : Params) : Prop :=
  0 < P.T ∧ 0 < P.piA ∧ P.piA ≤ P.piR ∧
  0 < P.alpha ∧ P.alpha ≤ 1 ∧ 0 < P.s ∧
  1 ≤ P.k ∧ P.k < (P.n : ℝ)

def dTilde (P : Params) (d τ : ℝ) : ℝ := min (d + τ) P.T

noncomputable def phi (P : Params) (d t τ : ℝ) : ℝ :=
  if t ≤ dTilde P d τ then
    t * P.piA + (P.T - t) * P.alpha * P.piR
  else dTilde P d τ * P.piA

noncomputable def expectedPhi (P : Params) (d t : ℝ) : ℝ :=
  ∫ τ, phi P d t τ ∂(expMeasure P.s)

noncomputable def profitN (P : Params) (d : ℝ) : ℝ :=
  ∫ τ, dTilde P d τ * P.piA ∂(expMeasure P.s)

noncomputable def profit (P : Params) (d θ lam : ℝ) : ℝ :=
  if lam = 0 then profitN P d
  else (∫ t, expectedPhi P d t ∂(gammaMeasure (P.n : ℝ) lam)) - θ * lam ^ P.k

def IsOptimalEffort (P : Params) (d θ lam : ℝ) : Prop :=
  0 ≤ lam ∧ ∀ μ : ℝ, 0 ≤ μ → profit P d θ μ ≤ profit P d θ lam

def Complies (P : Params) (d θ : ℝ) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ IsOptimalEffort P d θ lam

def compliantTypes (P : Params) : Set ℝ :=
  {θ | 0 < θ ∧ ∃ d ∈ Set.Icc (0 : ℝ) P.T, Complies P d θ}

noncomputable def thetaHat (P : Params) : ℝ := sSup (compliantTypes P)

noncomputable def gPdf (P : Params) (lam t : ℝ) : ℝ :=
  gammaPDFReal (P.n : ℝ) lam t

noncomputable def GCdf (P : Params) (lam t : ℝ) : ℝ :=
  (gammaMeasure (P.n : ℝ) lam (Set.Iic t)).toReal

noncomputable def R (P : Params) (θ lam d : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..d,
    (t * P.piA + (P.T - t) * P.alpha * P.piR) * gPdf P lam t) +
    d * P.piA * (1 - GCdf P lam d) - θ * lam ^ P.k

noncomputable def K (P : Params) (lam t : ℝ) : ℝ :=
  -(P.piA * GCdf P lam t) + (P.T - t) * P.alpha * P.piR * gPdf P lam t

end PostmarketCompliance.Threshold


