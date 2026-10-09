-- Prove2me | Definitions.Def_KangKurtz_SecondScale_Setting
-- name    : KangKurtz_SecondScale_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T01:41:32.450319+00:00
-- url     : https://prove2.me/theorems/de8bb29b-8b1e-4603-9319-ef63fac3d05c
-- title:
--   §2–4 — reaction scaling and first and second time scales
-- statement:
--   A network has finitely many indexed species and reactions. Reaction $k$ consumes $\nu_{ik}$ molecules of species $i$ and produces $\nu'_{ik}$, with net change $\zeta_{ik}=\nu'_{ik}-\nu_{ik}$. Species abundance and reaction rates have scaling exponents $\alpha_i\geq0$ and $\beta_k\in\mathbb R$. The rate exponent of reaction $k$ is
--
--   $$\rho_k=\beta_k+\sum_i\nu_{ik}\alpha_i.$$
--
--   For a nonnegative weight vector $\theta$, the changing reactions are $\Gamma^+_\theta=\{k:\theta\cdot\zeta_k>0\}$ and $\Gamma^-_\theta=\{k:\theta\cdot\zeta_k<0\}$. Define $\alpha_\theta=\max_{i:\theta_i>0}\alpha_i$ and $\gamma_\theta=\alpha_\theta-\max_{k\in\Gamma^+_\theta\cup\Gamma^-_\theta}\rho_k$. The maximum of an empty reaction set is $-\infty$, so $\gamma_\theta=+\infty$ when no reaction changes the weighted combination. The value of $\alpha_0$ is immaterial in that case.
--
--   The corresponding species time scale is $\gamma_i=\alpha_i-\max_{k\in\Gamma^+_i\cup\Gamma^-_i}\rho_k$, and $r_1=\min_i\gamma_i$. The fast-reaction set is $\Gamma_i^{r_1}=\{k:r_1+\rho_k=\alpha_i\}$. Let $\mathbb S_1=\{e_i:\Gamma_i^{r_1}\ne\varnothing\}$, let $\Pi_1$ retain precisely those coordinates, and set
--
--   $$\mathbb K_2=\{\theta\geq0:\theta\cdot\Pi_1\zeta_k=0\text{ for every }k\in\bigcup_i\Gamma_i^{r_1}\},\qquad r_2=\inf_{\theta\in\mathbb K_2}\gamma_\theta.$$
--
--   These definitions isolate the combinations unchanged by the first-scale reactions and supply the objects in Lemma 4.4.
--
--   **Formalization Note** Species and reactions use zero-based finite indices. The maximum of the empty set is represented by a bottom-extended real; time scales are extended reals, and their finite values use subtraction in $\mathbb R$. The coordinate projection realizes the paper's projection onto the span of $\mathbb S_1$. The infimum defining $r_2$ agrees with the paper's minimum because the non-infinite values of $\gamma_\theta$ belong to a finite set.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, pp. 4–6, 8–10, 20–21, §2, (3.5), Definition 3.1, (4.1), Theorem 4.1, §4 before Lemma 4.4

import Mathlib
import Definitions.Def_KangKurtz_SCC_Setting

namespace KangKurtz.SecondScale

noncomputable def support {s : ℕ} (θ : Fin s → ℝ) : Finset (Fin s) :=
  Finset.univ.filter (fun i => 0 < θ i)

noncomputable def alphaTheta {s : ℕ} (α θ : Fin s → ℝ) : ℝ :=
  if h : (support θ).Nonempty then (support θ).sup' h α else 0

noncomputable def GammaSpPlus {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (i : Fin s) : Finset (Fin r) :=
  Finset.univ.filter (fun k => ν k i < ν' k i)

noncomputable def GammaSpMinus {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (i : Fin s) : Finset (Fin r) :=
  Finset.univ.filter (fun k => ν' k i < ν k i)

noncomputable def gammaSp {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ)
    (β : Fin r → ℝ) (i : Fin s) : EReal :=
  if h : (GammaSpPlus ν ν' i ∪ GammaSpMinus ν ν' i).Nonempty then
    ((α i - (GammaSpPlus ν ν' i ∪ GammaSpMinus ν ν' i).sup' h (KangKurtz.SCC.rho ν α β) : ℝ) : EReal)
  else ⊤

noncomputable def r1 {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ)
    (β : Fin r → ℝ) : EReal :=
  ⨅ i, gammaSp ν ν' α β i

noncomputable def GammaR1 {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ)
    (β : Fin r → ℝ) (i : Fin s) : Finset (Fin r) :=
  Finset.univ.filter (fun k => r1 ν ν' α β + (KangKurtz.SCC.rho ν α β k : EReal) = (α i : EReal))

noncomputable def S1 {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ)
    (β : Fin r → ℝ) : Finset (Fin s) :=
  Finset.univ.filter (fun i => (GammaR1 ν ν' α β i).Nonempty)

noncomputable def Pi1 {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ)
    (β : Fin r → ℝ) (x : Fin s → ℝ) : Fin s → ℝ :=
  fun i => if i ∈ S1 ν ν' α β then x i else 0

def K2 {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ)
    (β : Fin r → ℝ) : Set (Fin s → ℝ) :=
  {θ | (∀ i, 0 ≤ θ i) ∧
    ∀ k, (∃ i, k ∈ GammaR1 ν ν' α β i) →
      (∑ i, θ i * Pi1 ν ν' α β (KangKurtz.SCC.zeta ν ν' k) i) = 0}

noncomputable def r2 {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ)
    (β : Fin r → ℝ) : EReal :=
  ⨅ θ ∈ K2 ν ν' α β, KangKurtz.SCC.gammaTheta ν ν' α β θ

end KangKurtz.SecondScale


