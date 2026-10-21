-- Prove2me | Definitions.Def_AuctionDuration_ClearingError_Model
-- name    : AuctionDuration_ClearingError_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:19.468329+00:00
-- url     : https://prove2.me/theorems/4ae8284a-f84f-4e68-b1d7-bb5f9d0ef7f3
-- title:
--   §2.1–§2.4, pp. 5–10, Assumption 2 as read in Appendix A — one call auction: Brownian efficient price, Poisson market makers, clearing price (2), mid-price (3), E(h), E^mid(h)
-- statement:
--   This file sets up the first auction of the call-auction market of Jusselin, Mastrolia and Rosenbaum, in the form used by the proof of their Theorem 2.1 (Appendix A).
--
--   **Constants.** $\nu>0$ is the intensity of the opening time, $\mu>0$ the intensity of the market-maker arrivals, $\sigma_f>0$ the volatility of the efficient price, $\sigma\ge 0$ the standard deviation of the market makers' estimation noise, $K>0$ the slope of the market makers' supply functions, and $P_0$ the initial efficient price. The auction duration is $h\ge 0$.
--
--   **Random objects.** On a probability space $(\Omega,\mathcal F,\mathbb P)$:
--
--   1. $W$ is a standard real Brownian motion, with continuous paths, and the efficient price is $P_t = P_0 + \sigma_f W_t$ for $t\ge 0$.
--   2. The market makers arrive at the epochs $\tau^{mm}_1<\tau^{mm}_2<\dots$ of a Poisson process of intensity $\mu$, built from i.i.d. $\mathrm{Exp}(\mu)$ interarrival times; $N^{mm}_t$ counts the arrivals in $[0,t]$.
--   3. The opening time $\tau^{op}_1$ is $\mathrm{Exp}(\nu)$, and the clearing time is $\tau^{cl}_1=\tau^{op}_1+h$.
--   4. The estimation noises $g_1,g_2,\dots$ are i.i.d., square integrable, centred, with variance $\sigma^2$. The $k$-th market maker's view of the price is
--   $$\tilde P_k = P_{\tau^{mm}_k} + g_k .$$
--   5. $I_{\tau^{cl}_1}$, the market takers' imbalance at the clearing, is square integrable.
--   6. The five families $W$, $(\tau^{mm}_k)$, $\tau^{op}_1$, $(g_k)$, $I_{\tau^{cl}_1}$ are mutually independent.
--
--   **Prices.** With $N=N^{mm}_{\tau^{cl}_1}$ market makers present at the clearing, the mid-price (3) and the clearing price (2) are
--   $$P^{mid}_{\tau^{cl}_1}=\frac1N\sum_{k=1}^{N}\tilde P_k,\qquad P^{cl}_{\tau^{cl}_1}=\frac1N\sum_{k=1}^{N}\tilde P_k+\frac1K\,\frac{I_{\tau^{cl}_1}}{N}.$$
--   The clearing price solves the clearing equation $\sum_{k=1}^N K(p-\tilde P_k)-I_{\tau^{cl}_1}=0$.
--
--   **Quality criteria.** Let $\tilde\Omega=\{N^{mm}_{\tau^{cl}_1}>0\}$ be the event that at least one market maker is present at the clearing. Then
--   $$E(h)=\mathbb E\big[(P^{cl}_{\tau^{cl}_1}-P_{\tau^{cl}_1})^2\,\big|\,\tilde\Omega\big],\qquad E^{mid}(h)=\mathbb E\big[(P^{mid}_{\tau^{op}_1+h}-P_{\tau^{op}_1+h})^2\,\big|\,\tilde\Omega\big].$$
--   At a deterministic time $t$ the proof also uses
--   $$g(t)=\mathbb E\Big[\mathbf 1_{N^{mm}_t>0}\Big(\sum_{k=1}^{N^{mm}_t}\frac{P_{\tau^{mm}_k}-P_t}{N^{mm}_t}\Big)^2\Big],\quad f(t)=\mathbb E\Big[\frac{\mathbf 1_{N^{mm}_t>0}}{N^{mm}_t}\Big],\quad \ell(t)=\mathbb E[I^2_{\tau^{cl}_1}]\,\mathbb E\Big[\frac{\mathbf 1_{N^{mm}_t>0}}{(N^{mm}_t)^2}\Big].$$
--
--   These objects are the common setting of Theorem 2.1 and of the lemmas of its proof.
--
--   **Formalization Note** (1) The model is the one Appendix A computes with: a Poisson($\mu$) process and an independent $\mathrm{Exp}(\nu)$ opening time, conditioned *jointly* on $\tilde\Omega$. Assumption 2 (p. 8) read literally (an unconditioned $\mathrm{Exp}(\nu)$ opening time and the market-maker process conditioned given it) gives a different value of $E(h)$, and Theorem 2.1 fails under it (a Monte Carlo at $\nu=1,\mu=2,h=0.5,\sigma_f=1,\sigma=0.5,K=1.5,\mathbb E[I^2]=1.44$ gives $0.9401$ against the formula's $0.9526$; the joint model gives $0.9515\pm0.0036$). (2) Added hypotheses, not on the page: $\mathbb E[g_k]=0$; independence of $I_{\tau^{cl}_1}$ from everything else; every path of $W$ continuous (a version choice). (3) Index shift: Lean's `g k` and `arrivalTime A (k+1)` are the paper's $g_{k+1}$ and $\tau^{mm}_{k+1}$. (4) $W$ is indexed by $\mathbb R_{\ge0}$ and evaluated at `t.toNNReal`; all arrival epochs and $\tau^{op}_1$ are a.s. nonnegative. (5) $1/N$ with $N=0$ is $0$ in Lean; $E$ and $E^{mid}$ are integrals under `P[|OmegaT X h]` and $f,\ell,g$ carry the indicator explicitly, so this convention is never seen. (6) Independence is `iIndep` of the five generated σ-algebras; the internal i.i.d. structure of the arrivals and the noises is part of `IsExpInterarrivals` and `iIndepFun`. Only the first auction is modelled.
-- source:
--   Jusselin, Mastrolia & Rosenbaum, Optimal auction duration: a price formation viewpoint, arXiv:1906.01713v3, pp. 5–10, §2.1–§2.4, Assumption 2, (2), (3); p. 20, Appendix A

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_ArrivalProcess

namespace AuctionDuration.ClearingError

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations
open scoped NNReal ENNReal

/-- The constants of the model (§2.2 and Assumption 2): `nu` = ν, the intensity of the opening time
`τ^op_1`; `mu` = µ, the intensity of the market-maker arrivals; `sigmaF` = σ_f, the volatility of the
efficient price; `sigma` = σ, the standard deviation of the market makers' estimation noise;
`K` = K, the slope of the market makers' supply functions; `P0` = P_0, the initial efficient price. -/
structure Params where
  nu : ℝ
  mu : ℝ
  sigmaF : ℝ
  sigma : ℝ
  K : ℝ
  P0 : ℝ

/-- Standing assumptions: ν > 0, µ > 0 (Assumption 2), σ_f > 0 and K > 0 (p. 6), σ ≥ 0. -/
def Params.Standing (p : Params) : Prop :=
  0 < p.nu ∧ 0 < p.mu ∧ 0 < p.sigmaF ∧ 0 ≤ p.sigma ∧ 0 < p.K

/-- The random objects of the first auction: the Brownian motion `W`, the market-maker interarrival
times `A` (the `n`-th market maker arrives at `arrivalTime A n`), the opening time `T` = τ^op_1,
the estimation noises `g` (`g k` is the paper's `g_{k+1}`), and the market takers' imbalance at the
clearing `J` = I_{τ^cl_1}. -/
structure Auction (Ω : Type*) where
  W : ℝ≥0 → Ω → ℝ
  A : ℕ → Ω → ℝ
  T : Ω → ℝ
  g : ℕ → Ω → ℝ
  J : Ω → ℝ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- σ-algebra generated by the Brownian motion. -/
abbrev Auction.sigmaW (X : Auction Ω) : MeasurableSpace Ω :=
  ⨆ t, MeasurableSpace.comap (X.W t) inferInstance

/-- σ-algebra generated by the market-maker interarrival times. -/
abbrev Auction.sigmaA (X : Auction Ω) : MeasurableSpace Ω :=
  ⨆ k, MeasurableSpace.comap (X.A k) inferInstance

/-- σ-algebra generated by the opening time. -/
abbrev Auction.sigmaT (X : Auction Ω) : MeasurableSpace Ω :=
  MeasurableSpace.comap X.T inferInstance

/-- σ-algebra generated by the estimation noises. -/
abbrev Auction.sigmaG (X : Auction Ω) : MeasurableSpace Ω :=
  ⨆ k, MeasurableSpace.comap (X.g k) inferInstance

/-- σ-algebra generated by the clearing imbalance. -/
abbrev Auction.sigmaJ (X : Auction Ω) : MeasurableSpace Ω :=
  MeasurableSpace.comap X.J inferInstance

/-- The model of Appendix A (the reading of Assumption 2 used by the proof of Theorem 2.1):
`W` is a standard Brownian motion with continuous paths; the market makers arrive according to a
Poisson process of intensity µ (i.i.d. Exp(µ) interarrival times); the opening time is Exp(ν);
the noises are i.i.d., centred, square integrable, with variance σ²; the imbalance `J` is square
integrable; and the five families `W`, `A`, `T`, `g`, `J` are mutually independent. -/
def IsModel (p : Params) (P : Measure Ω) (X : Auction Ω) : Prop :=
  IsProbabilityMeasure P ∧
  IsBrownianReal X.W P ∧ (∀ ω, Continuous fun t => X.W t ω) ∧ (∀ t, Measurable (X.W t)) ∧
  IsExpInterarrivals P p.mu X.A ∧
  Measurable X.T ∧ P.map X.T = expMeasure p.nu ∧
  (∀ k, Measurable (X.g k)) ∧ iIndepFun X.g P ∧ (∀ k, IdentDistrib (X.g k) (X.g 0) P P) ∧
  MemLp (X.g 0) 2 P ∧ ∫ ω, X.g 0 ω ∂P = 0 ∧ variance (X.g 0) P = p.sigma ^ 2 ∧
  Measurable X.J ∧ MemLp X.J 2 P ∧
  iIndep (fun i : Fin 5 => ![X.sigmaW, X.sigmaA, X.sigmaT, X.sigmaG, X.sigmaJ] i) P

/-- N^mm_t: the number of market makers arrived by time `t`. -/
noncomputable def Nmm (X : Auction Ω) (t : ℝ) (ω : Ω) : ℕ := countingProcess X.A t ω

/-- The clearing time τ^cl_1 = τ^op_1 + h. -/
def tauCl (X : Auction Ω) (h : ℝ) (ω : Ω) : ℝ := X.T ω + h

/-- The efficient price P_t = P_0 + σ_f W_t (for `t ≥ 0`). -/
noncomputable def Peff (p : Params) (X : Auction Ω) (t : ℝ) (ω : Ω) : ℝ :=
  p.P0 + p.sigmaF * X.W t.toNNReal ω

/-- The view of the `(k+1)`-th market maker: P̃_{k+1} = P_{τ^mm_{k+1}} + g_{k+1}. -/
noncomputable def view (p : Params) (X : Auction Ω) (k : ℕ) (ω : Ω) : ℝ :=
  Peff p X (arrivalTime X.A (k + 1) ω) ω + X.g k ω

/-- The mid-price (3): the average view of the market makers present at the clearing. -/
noncomputable def Pmid (p : Params) (X : Auction Ω) (h : ℝ) (ω : Ω) : ℝ :=
  (∑ k ∈ Finset.range (Nmm X (tauCl X h ω) ω), view p X k ω) / (Nmm X (tauCl X h ω) ω : ℝ)

/-- The clearing price (2): the mid-price plus `J / (K N)`. -/
noncomputable def Pcl (p : Params) (X : Auction Ω) (h : ℝ) (ω : Ω) : ℝ :=
  Pmid p X h ω + X.J ω / (p.K * (Nmm X (tauCl X h ω) ω : ℝ))

/-- Ω̃ = {N^mm_{τ^cl_1} > 0}: at least one market maker is present at the clearing. -/
def OmegaT (X : Auction Ω) (h : ℝ) : Set Ω := {ω | 0 < Nmm X (tauCl X h ω) ω}

/-- E(h) = E[(P^cl_{τ^cl_1} − P_{τ^cl_1})² | Ω̃]. -/
noncomputable def E (p : Params) (P : Measure Ω) (X : Auction Ω) (h : ℝ) : ℝ :=
  ∫ ω, (Pcl p X h ω - Peff p X (tauCl X h ω) ω) ^ 2 ∂(P[|OmegaT X h])

/-- E^mid(h) = E[(P^mid_{τ^op_1+h} − P_{τ^op_1+h})² | Ω̃]. -/
noncomputable def Emid (p : Params) (P : Measure Ω) (X : Auction Ω) (h : ℝ) : ℝ :=
  ∫ ω, (Pmid p X h ω - Peff p X (tauCl X h ω) ω) ^ 2 ∂(P[|OmegaT X h])

/-- g(t) = E[1_{N_t>0} (Σ_{k=1}^{N_t} (P_{τ^mm_k} − P_t)/N_t)²] at a deterministic time `t`. -/
noncomputable def gFun (p : Params) (P : Measure Ω) (X : Auction Ω) (t : ℝ) : ℝ :=
  ∫ ω, (if 0 < Nmm X t ω then
          ((∑ k ∈ Finset.range (Nmm X t ω),
              (Peff p X (arrivalTime X.A (k + 1) ω) ω - Peff p X t ω)) / (Nmm X t ω : ℝ)) ^ 2
        else 0) ∂P

/-- f(t) = E[1_{N_t>0} / N_t]. -/
noncomputable def fFun (P : Measure Ω) (X : Auction Ω) (t : ℝ) : ℝ :=
  ∫ ω, (if 0 < Nmm X t ω then 1 / (Nmm X t ω : ℝ) else 0) ∂P

/-- ℓ(t) = E[I²_{τ^cl_1}] E[1_{N_t>0} / N_t²]. -/
noncomputable def ellFun (P : Measure Ω) (X : Auction Ω) (t : ℝ) : ℝ :=
  (∫ ω, X.J ω ^ 2 ∂P) * ∫ ω, (if 0 < Nmm X t ω then 1 / (Nmm X t ω : ℝ) ^ 2 else 0) ∂P

end AuctionDuration.ClearingError


