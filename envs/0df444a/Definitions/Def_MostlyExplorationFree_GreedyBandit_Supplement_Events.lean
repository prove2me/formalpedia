-- Prove2me | Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_Events
-- name    : MostlyExplorationFree_GreedyBandit_Supplement_Events
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:49:23.484049+00:00
-- url     : https://prove2.me/theorems/6dd81bf4-9838-4b5b-be32-d8ef2b7de01f
-- title:
--   Appendix F and (9)–(12) — estimation events and explicit probability bounds
-- statement:
--   Put $\theta_1=h/(2x_{\max})$. For the greedy run with $m$ initial samples per arm define
--   $$H_i^\delta=\{\lambda_{\min}(\hat\Sigma(S_{i,Km}))\ge\delta\},\quad G_{i,t}^\chi=\{\|\hat\beta(S_{i,t})-\beta_i\|_2<\chi\},$$
--   $$J_{i,t}^\lambda=\{\lambda_{\min}(\hat\Sigma(S_{i,t}))\ge\lambda(t-m|K_{\rm sub}|)\},\quad \mathrm{Success}=\bigcap_i\bigcap_{t\ge Km}G_{i,t}^{\theta_1}.$$
--   Let $q_\delta$ be the probability that the Gram matrix of $m$ independent contexts has minimum eigenvalue at least $\delta$, and put
--   $$D_1(\gamma)=\frac{\lambda_1[\gamma+(1-\gamma)\log(1-\gamma)]}{x_{\max}^2},\quad D_2(\gamma)=\frac{\lambda_1^2h^2(1-\gamma)^2}{8d\sigma^2x_{\max}^4}.$$
--   Then the explicit function in (9) is
--   $$\begin{aligned}L(\gamma,\delta,p)={}&1-q_\delta^K+2Kdq_\delta e^{-h^2\delta/(8d\sigma^2x_{\max}^2)}\\&+\sum_{j=Km+1}^{p-1}2d e^{-h^2\delta^2/[8d(j-(K-1)m)\sigma^2x_{\max}^4]}\\&+\frac{d e^{-D_1(\gamma)(p-m|K_{\rm sub}|)}}{1-e^{-D_1(\gamma)}}+\frac{2d e^{-D_2(\gamma)(p-m|K_{\rm sub}|)}}{1-e^{-D_2(\gamma)}}.\end{aligned}$$
--   Equation (12) adds $(K-1)d e^{-D_1(\gamma)p}/(1-e^{-D_1(\gamma)})$ to define $L'$. Also write $A=128C_0\bar C x_{\max}^4\sigma^2d(\log d)^{3/2}/\lambda_0^2$ and $B=160b_{\max}x_{\max}^3d/\lambda_0+2x_{\max}b_{\max}$, and set $C_{\rm GB}=A+(A+B)/\log3$ using the published form of Theorem 1. Finally $\delta(t_0)=2d e^{-t_0 C_1}/C_1$, where $C_1=\lambda_0/(40x_{\max}^2)$.
--
--   These shared definitions keep each probability statement's events and constants identical across the supplement.
--
--   **Formalization Note** The missing parentheses in $J$ on p. 53 are repaired using pp. 20 and 55. Time differences in exponents and denominators are real differences. The first $m$ contexts compute $q_\delta$; iid sampling gives exactly the random-design law in (9). Bounds use $0<\gamma<1$, $\delta>0$, positive noise proxy, and positive scale constants. The infima in the theorems are stated pointwise; no empty real infimum is evaluated. The base Cbar and C1 definitions are imported unchanged. Cbar is used only with $d\ge2$.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, pp. 19–20, 25, 53, events H, J, G, equations (9)–(12); pp. 12, 23–24, 42, constants

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Model
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_PositiveDefiniteness
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_GreedyFirst

namespace MostlyExplorationFree.GreedyBandit.Supplement

open Matrix MeasureTheory

noncomputable def theta1 (h xmax : ℝ) : ℝ := h / (2 * xmax)

def H {Ω : Type*} {d K : ℕ} [NeZero K] (E : Environment Ω d K)
    (m : ℕ) (δ : ℝ) (i : Fin K) : Set Ω :=
  {ω | δ ≤ lambdaMin (gram E m i (K * m) ω)}

/-- Parentheses repaired from p. 20 and the application of Lemma 9 on p. 55.
Subtractions occur in ℝ. -/
def J {Ω : Type*} {d K : ℕ} [NeZero K] (E : Environment Ω d K)
    (m : ℕ) (Ksub : Finset (Fin K)) (lam : ℝ) (i : Fin K) (t : ℕ) : Set Ω :=
  {ω | lam * ((t : ℝ) - (m : ℝ) * Ksub.card) ≤ lambdaMin (gram E m i t ω)}

def G {Ω : Type*} {d K : ℕ} [NeZero K] (E : Environment Ω d K)
    (m : ℕ) (χ : ℝ) (i : Fin K) (t : ℕ) : Set Ω :=
  {ω | l2norm (est E m i t ω - E.β i) < χ}

def AccurateThrough {Ω : Type*} {d K : ℕ} [NeZero K] (E : Environment Ω d K)
    (m : ℕ) (χ : ℝ) (t : ℕ) : Set Ω :=
  {ω | ∀ i j, K * m ≤ j → j < t → ω ∈ G E m χ i j}

def Success {Ω : Type*} {d K : ℕ} [NeZero K] (E : Environment Ω d K)
    (m : ℕ) (h xmax : ℝ) : Set Ω :=
  {ω | ∀ i t, K * m ≤ t → ω ∈ G E m (theta1 h xmax) i t}

/-- Probability of a good Gram matrix from m iid context samples, using the first m contexts. -/
noncomputable def sampleGood {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ}
    (P : Measure Ω) (E : Environment Ω d K) (m : ℕ) (δ : ℝ) : ℝ :=
  P.real {ω | δ ≤ lambdaMin (gramOn E ω (Finset.Icc 1 m))}

noncomputable def D1 (lam1 xmax γ : ℝ) : ℝ :=
  lam1 * (γ + (1 - γ) * Real.log (1 - γ)) / xmax ^ 2

noncomputable def D2 (d : ℕ) (σ xmax h lam1 γ : ℝ) : ℝ :=
  lam1 ^ 2 * h ^ 2 * (1 - γ) ^ 2 / (8 * d * σ ^ 2 * xmax ^ 4)

/-- Exactly (9), including the factor qδ and the two different powers of xmax. -/
noncomputable def L {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ}
    (P : Measure Ω) (E : Environment Ω d K) (m : ℕ) (Ksub : Finset (Fin K))
    (σ xmax h lam1 γ δ : ℝ) (p : ℕ) : ℝ :=
  let qδ := sampleGood P E m δ
  let a := D1 lam1 xmax γ
  let b := D2 d σ xmax h lam1 γ
  let v := (p : ℝ) - (m : ℝ) * Ksub.card
  1 - qδ ^ K + 2 * K * d * qδ * Real.exp (-h ^ 2 * δ / (8 * d * σ ^ 2 * xmax ^ 2))
    + (∑ j ∈ Finset.Icc (K * m + 1) (p - 1),
        2 * d * Real.exp (-h ^ 2 * δ ^ 2 /
          (8 * d * ((j : ℝ) - ((K : ℝ) - 1) * m) * σ ^ 2 * xmax ^ 4)))
    + d * Real.exp (-a * v) / (1 - Real.exp (-a))
    + 2 * d * Real.exp (-b * v) / (1 - Real.exp (-b))

noncomputable def Lprime {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ}
    (P : Measure Ω) (E : Environment Ω d K) (m : ℕ) (Ksub : Finset (Fin K))
    (σ xmax h lam1 γ δ : ℝ) (p : ℕ) : ℝ :=
  L P E m Ksub σ xmax h lam1 γ δ p +
    ((K : ℝ) - 1) * d * Real.exp (-D1 lam1 xmax γ * p) /
      (1 - Real.exp (-D1 lam1 xmax γ))

/-- C_GB obtained from the already-published, proved form of Theorem 1. -/
noncomputable def CGB (d : ℕ) (C0 xmax bmax σ lam0 : ℝ) : ℝ :=
  let A := 128 * C0 * Cbar d * xmax ^ 4 * σ ^ 2 * d * Real.log d ^ (3 / 2 : ℝ) / lam0 ^ 2
  let B := 160 * bmax * xmax ^ 3 * d / lam0 + 2 * xmax * bmax
  A + (A + B) / Real.log 3

noncomputable def switchFailure (d : ℕ) (lam0 xmax : ℝ) (t0 : ℕ) : ℝ :=
  2 * d * Real.exp (-(t0 : ℝ) * C1 lam0 xmax) / C1 lam0 xmax

end MostlyExplorationFree.GreedyBandit.Supplement


