-- Prove2me | Definitions.Def_TabooRegen_Window
-- name    : TabooRegen_Window
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:26:18.230682+00:00
-- url     : https://prove2.me/theorems/6619b508-1149-483c-88a8-50c4a876415d
-- title:
--   The window of cycles around $t$, the age $\beta(t)$, the taboo limit $P^*$ on finite windows, and the kernel $\tilde b_{B,\ell}$
-- statement:
--   Let $N(t)=\max\{n:T(n)\le t\}$ (with $T(-1)=0$, so $N(t)=-1$ before $T(0)$). The cycle straddling time $t$ is $W_{N(t)+1}$, and the **age** is $\beta(t)=t-T(N(t))$. For $k\ge0$ the **window** of $2k+1$ cycles around $t$ is $(W_{N(t)+1+j}:|j|\le k)$; on the event $N(t)\ge k$ all its indices are at least $1$.
--
--   The **two-sided taboo limit** $P^*$ is defined in the paper on a bi-infinite sequence of cycles $(W_j)_{j\in\mathbb Z}$ and an age $\beta$, by (4.1) and the change of measure of p.285: cycles $W_j$, $j<0$, are fully tabooed (they stay in $A$) with lengths exponentially biased by $e^{\alpha\tau}$; the cycle $W_0$ straddles the origin, is biased by $\int_0^{\tau_0\wedge\gamma_0}e^{\alpha u}du$, and given $W_0$ the age $\beta$ has density proportional to $e^{\alpha x}$ on $[0,\tau_0\wedge\gamma_0)$; cycles $W_j$, $j>0$, are ordinary. Its window law is
--
--   $$
--   P^*\big(((W_j:|j|\le k),\beta)\in B\big)=\frac{E\Big[e^{\alpha(\tau_1+\cdots+\tau_k)}\,\mathbf 1\{\Gamma\ge T(k)\}\int_0^{\tau_{k+1}\wedge\gamma_{k+1}}e^{\alpha x}\,\mathbf 1\{((W_1,\dots,W_{2k+1}),x)\in B\}\,dx\Big]}{E\int_0^{\tau_1\wedge\gamma_1}e^{\alpha u}\,du},
--   $$
--
--   where window position $j$ is $W_{k+1+j}$ on the right.
--
--   The **kernel** of the proof of Theorem 2 is
--
--   $$
--   \tilde b_{B,\ell}(t)=e^{\alpha t}\,P\big(((W_{\ell+j+1}:|j|\le\ell),\,t-T(\ell))\in B,\ T(\ell)\le t<T(\ell+1),\ \Gamma>t\big).
--   $$
--
--   These are the objects in which the main theorem and its proof are stated.
--
--   **Formalization Note** The straddling index $N(t)+1$ is `strad t` $=\min\{n\ge0:t<T(n)\}$, so $N(t)\ge k$ is `k < strad t`; on the null explosion event the set is empty and the event is false. Window position $i\in\{0,\dots,2k\}$ stands for $j=i-k$. $P^*$ enters only through its window laws, so no bi-infinite space is constructed; the expectation is under the cycle law $Q$ and the numerator and normalizer are in $[0,\infty]$. The printed definition of $\tilde b_{B,\ell}$ omits the factor $e^{\alpha t}$, which the kernel convolved in (4.2) and bounded on p.287 carries.
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, N(t) p.282, β(t) and (4.1) p.284, P* p.285, Remark 12 and b̃ p.286

import Mathlib
import Definitions.Def_TabooRegen_Assumptions

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

/-- Drop the two outer positions of a window of `2(k + 1) + 1` cycles, keeping the middle
`2k + 1` (positions `−k, …, k`). Used to state that the window laws of `P*` are consistent
(Queueing Systems 46 (2004), p.285). -/
def dropOuter {β : Type*} (k : ℕ) (w : Fin (2 * (k + 1) + 1) → β) : Fin (2 * k + 1) → β :=
  fun i => w ⟨i.1 + 1, by omega⟩

namespace Model

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

/-- The index `N(t) + 1` of the cycle straddling time `t`, where `N(t) = max{n : T(n) ⩽ t}`
(Queueing Systems 46 (2004), p.282), with `T(−1) = 0`, so that `N(t) = −1` when `t < T(0)`:
`strad t = min{n ⩾ 0 : t < T(n)}`. Then `N(t) ⩾ k ⟺ T(k) ⩽ t ⟺ k < strad t`.

**Formalization Note.** If `T(n) ⩽ t` for every `n` (an explosion, a null event under the
hypotheses of the paper) the set is empty and `strad t = 0`, so the event `N(t) ⩾ k` is false
there. -/
noncomputable def strad (t : ℝ) (ω : Ω) : ℕ := sInf {n : ℕ | ENNReal.ofReal t < M.T n ω}

/-- The window of `2k + 1` cycles centred on the cycle straddling `t`:
`(W_{N(t)+1+j} : |j| ⩽ k)` (Queueing Systems 46 (2004), Theorem 2, p.286, with the index
corrected to the straddling cycle `W_{N(t)+1}`).

**Formalization Note.** Position `i ∈ Fin (2k + 1)` is `j = i − k`; the centre `i = k` is the
straddling cycle `W_{N(t)+1}`. On the event `N(t) ⩾ k` every index is at least `1`. -/
noncomputable def win (k : ℕ) (t : ℝ) (ω : Ω) : Fin (2 * k + 1) → Path S :=
  fun i => M.W (M.strad t ω - k + i) ω

/-- The age `β(t) = t − T(N(t))` (Queueing Systems 46 (2004), p.284), with `T(−1) = 0`. -/
noncomputable def age (t : ℝ) (ω : Ω) : ℝ := t - (M.Tm (M.strad t ω) ω).toReal

/-- The unnormalized `P*` window mass (Queueing Systems 46 (2004), (4.1) p.284 and the
change-of-measure formula of p.285, with `n = k` and `F_{W₀}` integrated):
`E[e^{α(τ₁+⋯+τ_k)} 1{Γ ⩾ T(k)} ∫₀^{τ_{k+1}∧γ_{k+1}} e^{αx} 1{((W₁, …, W_{2k+1}), x) ∈ B} dx]`
under the cycle law `Q`.

**Formalization Note.** Window position `i` (`j = i − k`) of `P*` is `W_{1+i}`: positions
`j = −k, …, −1` are the fully tabooed cycles, `j = 0` (`W_{k+1}`) is the straddling cycle with the
age `x = β`, and `j = 1, …, k` are ordinary cycles. `τ₁ + ⋯ + τ_k = T(k) − T(0)`, and on
`{Γ ⩾ T(0)}` the event `{Γ ⩾ T(k)}` is `{I₁ = ⋯ = I_k = 1}`. -/
noncomputable def PstarNum (α : ℝ) (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) : ℝ≥0∞ :=
  ∫⁻ ω in {ω | M.T k ω ≤ M.Γ ω},
    ENNReal.ofReal (Real.exp (α * ((M.T k ω).toReal - (M.T 0 ω).toReal))) *
      (∫⁻ x in {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < min (M.γ (k + 1) ω) (M.τ (k + 1) ω)},
        ENNReal.ofReal (Real.exp (α * x)) *
          B.indicator (fun _ => (1 : ℝ≥0∞)) ((fun i : Fin (2 * k + 1) => M.W (1 + i) ω), x)) ∂M.Q

/-- The law of the window `((W_j : |j| ⩽ k), β)` under the two-sided taboo limit `P*`
(Queueing Systems 46 (2004), (4.1) p.284 and p.285):
`P*_k(B) = PstarNum k B / E ∫₀^{τ₁∧γ₁} e^{αu} du`.

**Formalization Note.** `P*` enters Theorem 2 only through these finite windows, so no
bi-infinite sequence space is built. Under Definition 2, A1 and A4 the normalizer is positive and
finite and `P*_k` is a probability (milestone `pstar_consistent`). -/
noncomputable def PstarWindow (α : ℝ) (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) :
    ℝ≥0∞ :=
  M.PstarNum α k B / M.cycleWeight α

/-- The kernel `b̃_{B,ℓ}(t)` of the proof of Theorem 2 (Queueing Systems 46 (2004), p.286):
`e^{αt} P(((W_{ℓ+j+1} : |j| ⩽ ℓ), t − T(ℓ)) ∈ B, T(ℓ) ⩽ t < T(ℓ + 1), Γ > t)`.

**Formalization Note.** The factor `e^{αt}` is the one carried by the kernel convolved in (4.2) and
bounded on p.287; the printed definition omits it. Position `i` of the window is `W_{1+i}`. -/
noncomputable def btilde (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (t : ℝ) : ℝ :=
  Real.exp (α * t) *
    (M.P {ω | ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) ω), t - (M.T ℓ ω).toReal) ∈ B ∧
      M.T ℓ ω ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < M.T (ℓ + 1) ω ∧
      ENNReal.ofReal t < M.Γ ω}).toReal

end Model

end TabooRegen


