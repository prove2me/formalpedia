-- Prove2me | Definitions.Def_KangKurtz_SCC_Setting
-- name    : KangKurtz_SCC_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T00:47:05.988512+00:00
-- url     : https://prove2.me/theorems/69c3dea3-32f1-47c9-9b3d-6b937e30e12f
-- title:
--   Reaction-network scaling, Condition 3.2, and the species graph
-- statement:
--   The paper considers a finite indexed reaction network. Reaction $k$ consumes $\nu_{ik}$ molecules of species $i$ and produces $\nu'_{ik}$; it consumes at most two molecules in total. For nonnegative species exponents $\alpha_i$ and real reaction exponents $\beta_k$, set $\zeta_{ik}=\nu'_{ik}-\nu_{ik}$ and $\rho_k=\beta_k+\sum_i\nu_{ik}\alpha_i$.
--
--   For a nonnegative vector $\theta$, let $\Gamma^+_\theta$ and $\Gamma^-_\theta$ contain the reactions with $\theta\cdot\zeta_k>0$ and $\theta\cdot\zeta_k<0$. The two alternatives of Condition 3.2 are
--
--   $$
--   \max_{k\in\Gamma^-_\theta}\rho_k=\max_{k\in\Gamma^+_\theta}\rho_k
--   \qquad\text{or}\qquad
--   \gamma\le\gamma_\theta
--   =\max_{i:\theta_i>0}\alpha_i-\max_{k\in\Gamma^+_\theta\cup\Gamma^-_\theta}\rho_k.
--   $$
--
--   A species-graph edge $i\to j$ exists when an indexed reaction consumes $i$ and produces $j$. Two species are in the same maximal strongly connected component exactly when they are mutually reachable. These definitions supply the common vocabulary for the lemma and its milestones.
--
--   **Formalization Note** Empty reaction maxima equal $-\infty$. If both sign sets are empty, $\gamma_\theta=+\infty$. The support maximum's default at empty support is never used in the nonempty-reaction case.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, pp. 4–6, 10, 15, §2, Definition 3.1, Condition 3.2, §3.4

import Mathlib
noncomputable section

namespace KangKurtz.SCC

def BinaryReactions {s r : ℕ} (ν : Fin r → Fin s → ℕ) : Prop :=
  ∀ k, ∑ i, ν k i ≤ 2

def zeta {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (k : Fin r) (i : Fin s) : ℝ :=
  (ν' k i : ℝ) - (ν k i : ℝ)

def rho {s r : ℕ} (ν : Fin r → Fin s → ℕ)
    (α : Fin s → ℝ) (β : Fin r → ℝ) (k : Fin r) : ℝ :=
  β k + ∑ i, (ν k i : ℝ) * α i

def dot {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (θ : Fin s → ℝ) (k : Fin r) : ℝ :=
  ∑ i, θ i * zeta ν ν' k i

def GammaPlus {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (θ : Fin s → ℝ) : Finset (Fin r) :=
  Finset.univ.filter (fun k => 0 < dot ν ν' θ k)

def GammaMinus {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (θ : Fin s → ℝ) : Finset (Fin r) :=
  Finset.univ.filter (fun k => dot ν ν' θ k < 0)

def maxRho {s r : ℕ} (ν : Fin r → Fin s → ℕ)
    (α : Fin s → ℝ) (β : Fin r → ℝ) (S : Finset (Fin r)) : WithBot ℝ :=
  S.sup (fun k => (rho ν α β k : WithBot ℝ))

def Balance {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (α : Fin s → ℝ) (β : Fin r → ℝ) (θ : Fin s → ℝ) : Prop :=
  maxRho ν α β (GammaMinus ν ν' θ) = maxRho ν α β (GammaPlus ν ν' θ)

def alphaTheta {s : ℕ} (α θ : Fin s → ℝ) : ℝ :=
  let S := Finset.univ.filter (fun i => 0 < θ i)
  if h : S.Nonempty then S.sup' h α else 0

def gammaTheta {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (α : Fin s → ℝ) (β : Fin r → ℝ) (θ : Fin s → ℝ) : EReal :=
  let S := GammaPlus ν ν' θ ∪ GammaMinus ν ν' θ
  if h : S.Nonempty then
    ((alphaTheta α θ - S.sup' h (rho ν α β) : ℝ) : EReal)
  else ⊤

def TimeScale {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (α : Fin s → ℝ) (β : Fin r → ℝ) (γ : ℝ) (θ : Fin s → ℝ) : Prop :=
  (γ : EReal) ≤ gammaTheta ν ν' α β θ

def Cond32 {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (α : Fin s → ℝ) (β : Fin r → ℝ) (γ : ℝ) (θ : Fin s → ℝ) : Prop :=
  Balance ν ν' α β θ ∨ TimeScale ν ν' α β γ θ

def Edge {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (i j : Fin s) : Prop :=
  ∃ k, 0 < ν k i ∧ 0 < ν' k j

def SameComp {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (i j : Fin s) : Prop :=
  Relation.ReflTransGen (Edge ν ν') i j ∧ Relation.ReflTransGen (Edge ν ν') j i

end KangKurtz.SCC


