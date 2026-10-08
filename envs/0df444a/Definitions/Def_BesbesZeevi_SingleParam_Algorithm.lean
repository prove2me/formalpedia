-- Prove2me | Definitions.Def_BesbesZeevi_SingleParam_Algorithm
-- name    : BesbesZeevi_SingleParam_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:17:55.96999+00:00
-- url     : https://prove2.me/theorems/b38e9182-7651-47f7-9e05-8e8fb24a7740
-- title:
--   Algorithm 3 $\pi(\ell,\Delta^{(1)},\dots,\Delta^{(\ell)})$, its expected revenue $J^\pi_n$ and regret $\mathcal R^\pi_n$
-- statement:
--   Fix a market, a family with a selection $(p^u,p^c)$, a market size $n$, a number of stages $\ell$ with lengths $\Delta^{(1)},\dots,\Delta^{(\ell)}$, a true parameter $\theta^*$, and a path of a unit-rate Poisson process $N$. **Algorithm 3** runs as follows, with $\hat p_1=p_1$ and $\Lambda_0=0$: for $i=1,\dots,\ell$,
--
--   1. apply $\hat p_i$ during stage $i$; the cumulative demand intensity at the end of the stage is $\Lambda_i=\Lambda_{i-1}+n\lambda(\hat p_i;\theta^*)\Delta^{(i)}$, and the demand observed in stage $i$ is $N(\Lambda_i)-N(\Lambda_{i-1})$;
--   2. estimate the demand rate $\hat d_i=\big(N(\Lambda_i)-N(\Lambda_{i-1})\big)/(n\Delta^{(i)})$ and the parameter $\hat\theta_i=g(\hat p_i,\hat d_i)$, the solution of $\lambda(\hat p_i;\theta)=\hat d_i$;
--   3. set $\hat p_{i+1}=\max\{p^u(\hat\theta_i),p^c(\hat\theta_i)\}$.
--
--   Sales are capped by the inventory $\lfloor nx\rfloor$, so the revenue on the path is
--
--   $$
--   \sum_{i=1}^{\ell}\hat p_i\Big(\min\{N(\Lambda_i),\lfloor nx\rfloor\}-\min\{N(\Lambda_{i-1}),\lfloor nx\rfloor\}\Big).
--   $$
--
--   The expected revenue $J^\pi_n(x,T;\theta^*)$ is its expectation, and the regret is
--
--   $$
--   \mathcal R^\pi_n(x,T;\theta^*)=1-\frac{J^\pi_n(x,T;\theta^*)}{J^D_n(x,T\mid\theta^*)},
--   $$
--
--   with $J^D_n(x,T\mid\theta^*)=J^D(nx,T\mid n\lambda(\cdot;\theta^*))$. The tuned policy $\pi_n$ uses $\ell=\ell_n$ and $\Delta^{(m)}=\Delta^{(m)}_n$ from (19)–(20). The notation $X^i_n=\Lambda_i$ and $Y_n=N(X^{\ell}_n)$ follows the proof of Proposition 5.
--
--   **Formalization Note** The stage boundaries $\Lambda_i$ are random: they depend on earlier observations. This is the time change $N^\pi(t)=N(\int_0^t n\lambda(p(s))\,ds)$ of eq. (1), applied stage by stage. After a stock-out the paper's algorithm applies $p_\infty$; in the formula the capped increments are then $0$, so computing later prices from the uncapped counts does not change the revenue. Step 2(a)iv's "$\lambda(p_i,\theta)=\hat d_i$" is read as $\lambda(\hat p_i;\theta)=\hat d_i$, and Step 2(b)'s "$x/t$" as $x/T$, as in Algorithms 1–2. The inventory is $\lfloor nx\rfloor$ units, which equals $nx$ when $nx$ is an integer. The expectation is the lower Lebesgue integral of the nonnegative revenue, converted to a real number (the revenue is bounded by $\overline p\lfloor nx\rfloor$).
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 7 (PDF p. 9), eqs. (1)-(4); p. 17 (PDF p. 19), Algorithm 3; p. 15 (PDF p. 17), regret (16); p. 34 (PDF p. 36), X^i_n, Y^i_n

import Mathlib
import Definitions.Def_BesbesZeevi_SingleParam_PoissonProcess
import Definitions.Def_BesbesZeevi_SingleParam_Model
import Definitions.Def_BesbesZeevi_SingleParam_Family
import Definitions.Def_BesbesZeevi_SingleParam_Tuning

open MeasureTheory

namespace BesbesZeevi.SingleParam

/-- The state of Algorithm 3, `π(ℓ, Δ^{(1)}, …, Δ^{(ℓ)})` (p. 17), in the market of size `n`
(scaling (11)), run on one path `Nω : ℝ → ℕ` of the unit-rate Poisson process under the true
parameter `θ`. `Δ i` is the length of stage `i` (`i = 1, …, ℓ`).

`algState … k = (p̂_{k+1}, Λ_k)`: the price applied in stage `k + 1` and the cumulative intensity
`Λ_k = ∑_{j ≤ k} n λ(p̂_j; θ) Δ^{(j)}` at the end of stage `k` (`Λ_0 = 0`, `p̂_1 = p₁`). Stage
`k + 1` observes the demand `N(Λ_{k+1}) - N(Λ_k)` (time change (1)), forms
`d̂ = (N(Λ_{k+1}) - N(Λ_k)) / (n Δ^{(k+1)})`, the estimate `θ̂ = g(p̂_{k+1}, d̂)` (Step 2(a)iv,
read as `λ(p̂_{k+1}; θ) = d̂`) and the next price `max {p^u(θ̂), p^c(θ̂)}` (Step 2(b), with
`x/T`). The demand counts are uncapped; after a stock-out the capped sales in `revenue` are
zero, so this does not change the revenue. -/
noncomputable def algState (D : Market) (F : Family D) (σ : Selection D F) (n : ℕ)
    (Δ : ℕ → ℝ) (θ : ℝ) (Nω : ℝ → ℕ) : ℕ → ℝ × ℝ
  | 0 => (F.p1, 0)
  | k + 1 =>
    let s := algState D F σ n Δ θ Nω k
    let Λ' := s.2 + (n : ℝ) * F.lam s.1 θ * Δ (k + 1)
    let dhat := ((Nω Λ' : ℝ) - (Nω s.2 : ℝ)) / ((n : ℝ) * Δ (k + 1))
    let θhat := F.g s.1 dhat
    (max (σ.pu θhat) (σ.pc θhat), Λ')

/-- `p̂_i`, the price Algorithm 3 applies in stage `i ≥ 1`. -/
noncomputable def stagePrice (D : Market) (F : Family D) (σ : Selection D F) (n : ℕ)
    (Δ : ℕ → ℝ) (θ : ℝ) (Nω : ℝ → ℕ) (i : ℕ) : ℝ :=
  (algState D F σ n Δ θ Nω (i - 1)).1

/-- `X^i_n = Λ_i = ∑_{j=1}^{i} n λ(p̂_j; θ) Δ^{(j)}`, the cumulative demand intensity at the end
of stage `i` (p. 34); `X^0_n = 0`. -/
noncomputable def cumIntensity (D : Market) (F : Family D) (σ : Selection D F) (n : ℕ)
    (Δ : ℕ → ℝ) (θ : ℝ) (Nω : ℝ → ℕ) (i : ℕ) : ℝ :=
  (algState D F σ n Δ θ Nω i).2

/-- The inventory `⌊n x⌋` of the market of size `n`, in units. -/
noncomputable def capacity (D : Market) (n : ℕ) : ℕ := ⌊(n : ℝ) * D.x⌋₊

/-- The revenue of Algorithm 3 with `ℓ` stages on one path: sales are the demand counts capped
at the inventory, `∑_{i=1}^{ℓ} p̂_i (min{N(Λ_i), ⌊nx⌋} - min{N(Λ_{i-1}), ⌊nx⌋})`. -/
noncomputable def revenue (D : Market) (F : Family D) (σ : Selection D F) (n ℓ : ℕ)
    (Δ : ℕ → ℝ) (θ : ℝ) (Nω : ℝ → ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 ℓ, stagePrice D F σ n Δ θ Nω i *
    (((min (Nω (cumIntensity D F σ n Δ θ Nω i)) (capacity D n) : ℕ) : ℝ) -
      ((min (Nω (cumIntensity D F σ n Δ θ Nω (i - 1))) (capacity D n) : ℕ) : ℝ))

/-- `J^π_n(x, T; θ)`: the expected revenue of Algorithm 3 with `ℓ` stages of lengths `Δ`, under
the true parameter `θ`, computed as the (finite) lower Lebesgue integral of the nonnegative
revenue and converted to a real number. -/
noncomputable def expRevenue {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : PoissonProcess Ω P) (D : Market) (F : Family D) (σ : Selection D F) (n ℓ : ℕ)
    (Δ : ℕ → ℝ) (θ : ℝ) : ℝ :=
  (∫⁻ ω, ENNReal.ofReal (revenue D F σ n ℓ Δ θ (fun t => N.N t ω)) ∂P).toReal

/-- `R^π_n(x, T; θ) = 1 - J^π_n(x, T; θ) / J^D_n(x, T | θ)` (regret (16), scaled by (11)). -/
noncomputable def regret {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : PoissonProcess Ω P) (D : Market) (F : Family D) (σ : Selection D F) (n ℓ : ℕ)
    (Δ : ℕ → ℝ) (θ : ℝ) : ℝ :=
  1 - expRevenue N D F σ n ℓ Δ θ / detValueScaled D (fun p => F.lam p θ) n

/-- The regret of `π_n = π(ℓ_n, Δ^{(1)}_n, …, Δ^{(ℓ_n)}_n)` with the tuning (19)–(20). -/
noncomputable def tunedRegret {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : PoissonProcess Ω P) (D : Market) (F : Family D) (σ : Selection D F) (n : ℕ)
    (θ : ℝ) : ℝ :=
  regret N D F σ n (numStages n) (stageLength D.T n) θ

end BesbesZeevi.SingleParam


