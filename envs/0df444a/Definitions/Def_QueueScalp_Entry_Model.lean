-- Prove2me | Definitions.Def_QueueScalp_Entry_Model
-- name    : QueueScalp_Entry_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:23.913867+00:00
-- url     : https://prove2.me/theorems/bc427cbe-4a74-4c90-8c8e-209a8e6df821
-- title:
--   Single queue-scalper model, §3–§4.1
-- statement:
--   A single queue-scalper offers arriving customers the option to buy a better queue position in an unobservable M/M/1 service system. Capacity is $\mu>0$, customers value service at $V>1/\mu$, their delay costs are uniform on $[0,1]$, and the scalper's unit-time cost is $k\ge0$. Demand volume is $\Lambda>0$; throughput $\lambda=\Lambda c^S$ is the rate that actually joins.
--
--   For a given purchase fraction $q$, the expected delays $W^I_1(\lambda,q)$ for buyers and $W^I_2(\lambda,q)$ for nonbuyers are the formulas of Lemma 1. Customer equilibrium imposes the two cutoff conditions and consistency equations (1b)–(1d): $0\le\tilde c\le c^S\le1$, $c^S>0$, $\lambda<\mu$, nonnegative utility at $c^S$, its complementarity condition, buyer indifference at $\tilde c$, $\lambda=\Lambda c^S$, and $q=(c^S-\tilde c)/c^S$.
--
--   The optimum is an attained joint maximum of $P\lambda q$ over nonnegative prices $P$ and compatible customer equilibria. Entry occurs exactly when this maximum exceeds $k$; equality is resolved as no entry. The remaining definitions record the paper's closed-form cutoffs, price, revenue, and peak demand. These provide a reusable interface for the single-scalper analysis.
--
--   **Formalization Note** The delays are those of Lemma 1, taken as given; the queueing-process derivation is outside this definition. The uniform CDF is written as the identity on $[0,1]$.
-- source:
--   Yang, Wang & Cui, A Model of Queue-Scalping, authors' manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3865), pp. 5–12 (PDF 5–12), §3, §4, §4.1, Lemma 1, (1a)–(1d); Online Appendix pp. 1–3 (PDF 34–36), Lemma A.1, (A.1), (A.4)

import Mathlib

namespace QueueScalp.Entry

structure Params where
  mu : ℝ
  V : ℝ
  k : ℝ

def Params.Standing (P : Params) : Prop :=
  0 < P.mu ∧ 1 / P.mu < P.V ∧ 0 ≤ P.k

noncomputable def W1 (mu lam q : ℝ) : ℝ :=
  1 / (mu - lam) - (lam / mu) ^ 2 * (1 - q) / (mu - lam + lam * q)

noncomputable def W2 (mu lam q : ℝ) : ℝ :=
  1 / (mu - lam) + (lam / mu) ^ 2 * q / (mu - lam + lam * q)

noncomputable def D (mu lam q : ℝ) : ℝ := W2 mu lam q - W1 mu lam q

structure IsCustEq (P : Params) (Lam price lam q cS ct : ℝ) : Prop where
  ct_nonneg : 0 ≤ ct
  ct_le_cS : ct ≤ cS
  cS_pos : 0 < cS
  cS_le_one : cS ≤ 1
  stable : lam < P.mu
  join : 0 ≤ P.V - cS * W1 P.mu lam q - price
  slack : (1 - cS) * (P.V - cS * W1 P.mu lam q - price) = 0
  indiff : price = ct * (W2 P.mu lam q - W1 P.mu lam q)
  thru : lam = Lam * cS
  rate : q = (cS - ct) / cS

def IsOptRevenue (P : Params) (Lam R : ℝ) : Prop :=
  (∃ price lam q cS ct, 0 ≤ price ∧ IsCustEq P Lam price lam q cS ct ∧
    price * lam * q = R) ∧
  ∀ price lam q cS ct, 0 ≤ price → IsCustEq P Lam price lam q cS ct →
    price * lam * q ≤ R

def IsOptPrice (P : Params) (Lam price : ℝ) : Prop :=
  ∃ lam q cS ct, 0 ≤ price ∧ IsCustEq P Lam price lam q cS ct ∧
    IsOptRevenue P Lam (price * lam * q)

noncomputable def entry (P : Params) (R : ℝ) : ℕ :=
  if P.k < R then 1 else 0

noncomputable def cSOf (P : Params) (Lam : ℝ) : ℝ :=
  if Lam ≤ P.mu - 1 / P.V then 1 else P.mu * P.V / (1 + Lam * P.V)

noncomputable def ctStar (P : Params) (Lam : ℝ) : ℝ :=
  (P.mu - Real.sqrt (P.mu ^ 2 - Lam * cSOf P Lam * P.mu)) / Lam

noncomputable def priceStar (P : Params) (Lam : ℝ) : ℝ :=
  if Lam ≤ P.mu - 1 / P.V then
    Lam * (Real.sqrt P.mu - Real.sqrt (P.mu - Lam)) /
      (P.mu ^ 2 * Real.sqrt (P.mu - Lam))
  else
    Lam * P.V ^ 2 * (Real.sqrt (Lam * P.V + 1) - 1) /
      (Lam * P.V + 1) ^ 2

noncomputable def PiStar (P : Params) (Lam : ℝ) : ℝ :=
  if Lam ≤ P.mu - 1 / P.V then
    Lam ^ 3 * ctStar P Lam * (1 - ctStar P Lam) /
      (P.mu ^ 2 * (P.mu - Lam * ctStar P Lam))
  else
    Lam * P.V ^ 2 *
      (-Real.sqrt (P.mu ^ 2 * (Lam * P.V + 1)) + Lam * P.mu * P.V + P.mu) *
      (Real.sqrt (P.mu ^ 2 * (Lam * P.V + 1)) - P.mu) /
      ((Lam * P.V + 1) ^ 3 * Real.sqrt (P.mu ^ 2 * (Lam * P.V + 1)))

noncomputable def LamTilde (P : Params) : ℝ :=
  (5 + Real.sqrt 13) / (2 * P.V)

noncomputable def LamStar (P : Params) : ℝ :=
  max (P.mu - 1 / P.V) (LamTilde P)

end QueueScalp.Entry


