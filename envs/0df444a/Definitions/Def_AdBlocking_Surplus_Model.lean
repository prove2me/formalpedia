-- Prove2me | Definitions.Def_AdBlocking_Surplus_Model
-- name    : AdBlocking_Surplus_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:55.98344+00:00
-- url     : https://prove2.me/theorems/9d2dd4b9-3f79-431b-82cf-7aeb16758aee
-- title:
--   Ad-blocking game, equilibria, and consumer surplus
-- statement:
--   A publisher chooses nonnegative quality $q$ at cost $cq^2$ and advertising volume $A$ at price $p_a$ per impression. Independent consumer characteristics are quality sensitivity $\vartheta\sim U[t,1]$, ad sensitivity $\gamma\sim U[r,1]$, and adblocker download cost $\kappa\sim U[0,\bar\kappa]$. The standing conditions are $p_a,c>0$, $0<r\le1$, and $0\le t\le1$. A consumer's utility with an adblocker that lets volume $V$ through is
--
--   $$U=\max\{\vartheta q-\gamma A,\;\vartheta q-\gamma V-\kappa,\;0\}.$$
--
--   The definitions give benchmark demand and publisher profit, the mass of downloaders, the adblocker's payment, the publisher's profit after that payment, and expected consumer surplus in both regimes. Best-response and equilibrium predicates maximize the relevant payoffs over nonnegative advertising, ad limits, and quality. These objects determine the comparison in Proposition 3.
--
--   **Formalization Note** A consumer downloads only when adblocker utility strictly exceeds both other options; without the adblocker, visiting includes the zero-utility tie. The adblocker regime uses the same benchmark-optimal ad volume and sets realized downloader ads equal to $V$. The negotiation is represented by a payment of all downloader ad revenue to the adblocker. Expectations are iterated integrals; $U[t,1]$ and $U[r,1]$ become point masses at their degenerate endpoints.
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), pp. 10–17 (PDF 11–18), §3–§3.2; p. 40 (PDF 41), proof of Proposition 1

import Mathlib
import Definitions.Def_AdBlocking_Surplus_Uniform

open MeasureTheory

namespace AdBlocking.Surplus

def Standing (pa c r t : ℝ) : Prop :=
  0 < pa ∧ 0 < c ∧ 0 < r ∧ r ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1

noncomputable def E2 (r t : ℝ) (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ θ, ∫ γ, f θ γ ∂(unifIcc r 1) ∂(unifIcc t 1)

noncomputable def E3 (r t κbar : ℝ) (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ θ, ∫ γ, ∫ κ, f θ γ κ ∂(unifIcc 0 κbar) ∂(unifIcc r 1) ∂(unifIcc t 1)

def visits (q A θ γ : ℝ) : Prop := 0 ≤ θ * q - γ * A

noncomputable def demand (r t q A : ℝ) : ℝ :=
  by classical exact E2 r t (fun θ γ => if visits q A θ γ then 1 else 0)

noncomputable def benchRev (pa r t q A : ℝ) : ℝ :=
  pa * A * demand r t q A

noncomputable def benchProfit (pa c r t : ℝ) (Asel : ℝ → ℝ) (q : ℝ) : ℝ :=
  benchRev pa r t q (Asel q) - c * q ^ 2

def downloads (q A V θ γ κ : ℝ) : Prop :=
  max (θ * q - γ * A) 0 < θ * q - γ * V - κ

noncomputable def dlMass (r t κbar q A V : ℝ) : ℝ :=
  by classical exact E3 r t κbar (fun θ γ κ => if downloads q A V θ γ κ then 1 else 0)

noncomputable def adblockerPayoff (pa r t κbar q A V : ℝ) : ℝ :=
  pa * V * dlMass r t κbar q A V

noncomputable def pubProfitAB (pa c r t κbar q A V : ℝ) : ℝ :=
  by
    classical
    exact pa * A * E3 r t κbar
      (fun θ γ κ => if visits q A θ γ ∧ ¬ downloads q A V θ γ κ then 1 else 0)
      - c * q ^ 2

noncomputable def csNA (r t q A : ℝ) : ℝ :=
  E2 r t (fun θ γ => max (θ * q - γ * A) 0)

noncomputable def csAB (r t κbar q A V : ℝ) : ℝ :=
  E3 r t κbar
    (fun θ γ κ => max (max (θ * q - γ * A) (θ * q - γ * V - κ)) 0)

def IsBenchAdBest (pa r t q A : ℝ) : Prop :=
  0 ≤ A ∧ ∀ B, 0 ≤ B → benchRev pa r t q B ≤ benchRev pa r t q A

def IsAdblockBest (pa r t κbar q A V : ℝ) : Prop :=
  0 ≤ V ∧ ∀ W, 0 ≤ W →
    adblockerPayoff pa r t κbar q A W ≤ adblockerPayoff pa r t κbar q A V

def IsBenchEq (pa c r t : ℝ) (Asel : ℝ → ℝ) (qN : ℝ) : Prop :=
  (∀ q, 0 ≤ q → IsBenchAdBest pa r t q (Asel q)) ∧
  0 ≤ qN ∧ ∀ q, 0 ≤ q →
    benchProfit pa c r t Asel q ≤ benchProfit pa c r t Asel qN

def IsABEq (pa c r t κbar : ℝ) (Asel Vsel : ℝ → ℝ) (qA : ℝ) : Prop :=
  (∀ q, 0 ≤ q → IsAdblockBest pa r t κbar q (Asel q) (Vsel q)) ∧
  0 ≤ qA ∧ ∀ q, 0 ≤ q →
    pubProfitAB pa c r t κbar q (Asel q) (Vsel q) ≤
      pubProfitAB pa c r t κbar qA (Asel qA) (Vsel qA)

end AdBlocking.Surplus


