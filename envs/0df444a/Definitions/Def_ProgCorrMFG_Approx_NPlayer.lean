-- Prove2me | Definitions.Def_ProgCorrMFG_Approx_NPlayer
-- name    : ProgCorrMFG_Approx_NPlayer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:28.427965+00:00
-- url     : https://prove2.me/theorems/5a7d2b56-038e-472b-b840-c6af7a473059
-- title:
--   §3, Definitions 3.1, 3.5, (3.1)–(3.3) — the $N$-player game: realizations, costs $J^N_i$, strategy modifications and $\varepsilon$-correlated equilibria
-- statement:
--   This file defines the $N$-player game with a mediator and progressive deviations.
--
--   **Empirical measures and strategies.** For states $x=(x_1,\dots,x_N)\in\mathcal X^N$ and a player $l$, the empirical measure of the others is
--   $$\mu^{l,N}=\frac1{N-1}\sum_{j\neq l}\delta_{x_j},$$
--   an element of the finite set $\mathcal M^{\mathcal X}_{N-1}$ of empirical measures of $N-1$ points. An $N$-player progressive strategy $\varphi\in\widehat{\mathcal R}_N$ assigns to each time $t$ a map $(x^{(t)},m^{(t)})\mapsto\varphi(t,x^{(t)},m^{(t)})\in\Gamma$ of the player's own state history and the history of empirical measures; the time-$t$ components form $\widehat{\mathcal E}_{t,N}$. Restricted strategies embed by $\varphi\mapsto((t,x,m)\mapsto\varphi(t,x_t))$.
--
--   **Strategy modifications (3.1).** For $\gamma\in\mathcal P(\widehat{\mathcal R}_N)$, the set $\mathcal N^N_\gamma$ consists of the measures
--   $$\tilde\gamma(d\varphi,d\psi)=\beta_0(\varphi,d\psi_0)\cdots\beta_{T-1}(\varphi,d\psi_{T-1})\,\gamma(d\varphi)$$
--   for probability kernels $\beta_t$ from $\widehat{\mathcal R}_N$ to $\widehat{\mathcal E}_{t,N}$. The modification "follow the suggestion" is $\iota_\gamma(d\varphi,d\psi)=\delta_\varphi(d\psi)\gamma(d\varphi)$.
--
--   **Realizations (Definition 3.1).** Given an initial law $\mathfrak m^N\in\mathcal P(\mathcal X^N)$, a correlated suggestion $\gamma^N\in\mathcal P(\widehat{\mathcal R}_N^N)$ and $\tilde\gamma\in\mathcal N^N_{\gamma^N_i}$, a realization for player $i$ is a probability space carrying states $X^{j,N}_t$, suggestions $\Phi_1,\dots,\Phi_N$, a modified strategy $\tilde\Phi_i$, noises $\xi^{j,N}_t$ and a randomization device $\vartheta_t$ such that: (i)–(iv) the noises, the initial states, the device and the suggestions are independent, with laws $\nu^{\otimes NT}$, $\mathfrak m^N$, $\nu^{\otimes T}$ and $\gamma^N$; (v) $(\Phi_i,\tilde\Phi_i)$ has law $\tilde\gamma$ and $\tilde\Phi_i(t,\cdot,\cdot)$ is $\sigma(\Phi_i,\vartheta_t)$-measurable; (vi) almost surely, player $i$ moves by $X^{i,N}_{t+1}=\Psi(t,X^{i,N}_t,\mu^{i,N}_t,\tilde\Phi_i(t,X^{i,N},\mu^{i,N}),\xi^{i,N}_{t+1})$ and every $j\neq i$ by the same rule with $\Phi_j$.
--
--   **Cost (3.3) and equilibrium (Definition 3.5).** The cost of player $i$ is
--   $$J^N_i(\mathfrak m^N,\gamma^N,\tilde\gamma)=\mathbb E\Big[\sum_{t=0}^{T-1}f\big(t,X^{i,N}_t,\mu^{i,N}_t,\tilde\Phi_i(t,X^{i,N},\mu^{i,N})\big)+F(X^{i,N}_T,\mu^{i,N}_T)\Big].$$
--   For $\varepsilon\ge0$, $\gamma^N$ is an $\varepsilon$-correlated equilibrium with initial distribution $\mathfrak m^N$ if $J^N_i(\mathfrak m^N,\gamma^N,\iota_{\gamma^N_i})\le J^N_i(\mathfrak m^N,\gamma^N,\tilde\gamma)+\varepsilon$ for every player $i$ and every $\tilde\gamma\in\mathcal N^N_{\gamma^N_i}$.
--
--   **Formalization Note** Players are `Fin N` (the paper's player 1 is index `0`). The paper defines $\widehat{\mathcal R}_N$ on $\mathcal M^{\mathcal X}_N$ but feeds it $\mu^{l,N}\in\mathcal M^{\mathcal X}_{N-1}$; strategies here read elements of $\mathcal M^{\mathcal X}_{N-1}$, so $\widehat{\mathcal R}_N$ is finite and carries the discrete σ-algebra, as the paper intends. The empirical measure is meaningful only for $N\ge2$ (every statement assumes it). Conditions (i)–(iv) are stated as one product-law identity. The cost is the expected cost of a realization; the paper asserts that it does not depend on the realization, so Definition 3.5 is required for every realization of each side. Completeness of the probability space is dropped: every condition concerns laws and almost-sure relations.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, pp. 4–6, (2.2), (3.1), Definition 3.1, (3.2), (3.3), Remark 3.4, Definition 3.5

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval

/-- `ℳ^𝒳_n` (p. 4): the empirical measures of `n`-samples, i.e. the `m ∈ 𝒫(𝒳)` with
`m(x) ∈ {0, 1/n, …, 1}` for every `x`. Here it is used with `n = N − 1`, the number of the other
players. -/
def EmpMeas (X : Type) [Fintype X] (n : ℕ) : Type :=
  {m : Meas X // ∃ k : X → ℕ, ∀ y, (m : X → ℝ) y * (n : ℝ) = (k y : ℝ)}

/-- The weights of `(N−1)⁻¹ ∑_{j ≠ l} δ_{x_j}` at `y`. -/
noncomputable def empVal {X : Type} [DecidableEq X] {N : ℕ} (x : Fin N → X) (l : Fin N) (y : X) : ℝ :=
  (∑ j ∈ Finset.univ.erase l, if x j = y then (1 : ℝ) else 0) / ((N - 1 : ℕ) : ℝ)

/-- The empirical measure of all players' states but the `l`-th,
`μ^{l,N} := (N−1)⁻¹ ∑_{j ≠ l} δ_{x_j}` ((3.2), p. 5), as an element of `ℳ^𝒳_{N−1}`. It is only
meaningful for `N ≥ 2`; for `N ≤ 1` it is set to `δ_{x_l}` and never used. -/
noncomputable def empOthers {X : Type} [Fintype X] [DecidableEq X] {N : ℕ} (x : Fin N → X)
    (l : Fin N) : EmpMeas X (N - 1) :=
  if hN : 2 ≤ N then
    ⟨⟨empVal x l,
      by
        have hpos : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - 1 by omega)
        refine ⟨fun y => div_nonneg (Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num)
          hpos.le, ?_⟩
        unfold empVal
        rw [← Finset.sum_div, Finset.sum_comm]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, nsmul_eq_mul,
          mul_one, Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin]
        exact div_self hpos.ne'⟩,
      ⟨fun y => ∑ j ∈ Finset.univ.erase l, if x j = y then 1 else 0, fun y => by
        have hpos : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - 1 by omega)
        show empVal x l y * _ = _
        unfold empVal
        rw [div_mul_cancel₀ _ hpos.ne']
        push_cast
        rfl⟩⟩
  else
    ⟨⟨Pi.single (x l) 1, single_mem_stdSimplex ℝ (x l)⟩,
      ⟨fun _ => 0, fun y => by
        have : N - 1 = 0 := by omega
        simp [this]⟩⟩

/-- The time-`t` component `ℰ̂_{t,N}` of an `N`-player progressive strategy: a map
`(x, m) ↦ φ(t, x^{(t)}, m^{(t)}) ∈ Γ` of the player's state path and the path of empirical measures
of the others, depending only on the histories up to `t`. It is a finite set with the discrete
σ-algebra. -/
def CompN (T : ℕ) (X G : Type) [Fintype X] (n : ℕ) (t : Fin T) : Type :=
  {g : (Fin (T + 1) → X) → (Fin (T + 1) → EmpMeas X n) → G // NonAnt t g}

instance (T : ℕ) (X G : Type) [Fintype X] (n : ℕ) (t : Fin T) : MeasurableSpace (CompN T X G n t) :=
  ⊤

/-- `ℛ̂_N` (p. 4): the progressive strategies of the `N`-player game, with `n = N − 1`. It is the
product of the `ℰ̂_{t,N}`, with the product (= discrete) σ-algebra. -/
abbrev ProgN (T : ℕ) (X G : Type) [Fintype X] (n : ℕ) : Type :=
  (t : Fin T) → CompN T X G n t

/-- The inclusion `ℛ ⊂ ℛ̂_N`, `φ ↦ ((t, x, m) ↦ φ(t, x_t))`. -/
def embN {T : ℕ} {X G : Type} [Fintype X] {n : ℕ} (φ : Strat T X G) : ProgN T X G n :=
  fun t => ⟨fun x _ => φ t (x t.castSucc), fun x x' m m' h => by simp only [(h t.castSucc le_rfl).1]⟩

/-- The set `𝒩^N_γ` of strategy modifications (3.1), p. 4: the measures
`γ̃(dφ, dψ) = β_0(φ, dψ_0) ⋯ β_{T−1}(φ, dψ_{T−1}) γ(dφ)` on `ℛ̂_N × ℛ̂_N`, for a flow of probability
kernels `β = (β_t)_t ∈ 𝒦_N`, `β_t` a kernel from `ℛ̂_N` to `ℰ̂_{t,N}`. -/
def StratModSet {T : ℕ} {X G : Type} [Fintype X] {n : ℕ} (γ : Measure (ProgN T X G n)) :
    Set (Measure (ProgN T X G n × ProgN T X G n)) :=
  {γ' | ∃ β : (t : Fin T) → Kernel (ProgN T X G n) (CompN T X G n t),
    ∃ hβ : ∀ t, IsMarkovKernel (β t),
      γ' = (letI := hβ
        γ.bind (fun φ => (Measure.pi (fun t => β t φ)).map (fun ψ => (φ, ψ))))}

/-- `ι_γ ∈ 𝒩^N_γ` (Remark 3.4, p. 6): the modification "follow the suggestion",
`ι_γ(dφ, dψ) = δ_φ(dψ) γ(dφ)`. -/
noncomputable def iotaN {T : ℕ} {X G : Type} [Fintype X] {n : ℕ} (γ : Measure (ProgN T X G n)) :
    Measure (ProgN T X G n × ProgN T X G n) :=
  γ.map (fun φ => (φ, φ))

/-- The progressive strategy actually played by player `j` when player `i` uses `dev` and every
other player `j` follows the suggestion `sugg j`. -/
def played {T : ℕ} {X G : Type} [Fintype X] {n N : ℕ} (i : Fin N) (sugg : Fin N → ProgN T X G n)
    (dev : ProgN T X G n) (j : Fin N) : ProgN T X G n :=
  if j = i then dev else sugg j

/-- A realization of `(𝔪^N, γ^N, γ̃)` for player `i` (Definition 3.1, pp. 4–5), on a probability
space `(Ω, P)`. Fields: states `X^{j,N}_t` (`state ω t j`, `t ∈ ⟦0,T⟧`), suggestions `Φ_j`
(`sugg ω j`), the modified strategy `Φ̃_i` (`dev ω`), noises `ξ^{j,N}_{t+1}` (`noise ω t j`,
`t ∈ ⟦0, T−1⟧`) and the randomization device `ϑ_t` (`coin ω t`).
* `law` is i)–iv): the vector `(ξ, X_0, ϑ, Φ)` has the product law
  `ν^{⊗TN} ⊗ 𝔪^N ⊗ ν^{⊗T} ⊗ γ^N` (initial law `𝔪^N`, suggestion law `γ^N`, i.i.d. uniform `ξ` and
  `ϑ`, the four independent);
* `dev_law` and `dev_adapted` are v): `ℙ ∘ (Φ_i, Φ̃_i)⁻¹ = γ̃`, and `Φ̃_i(t, ·, ·)` is
  `σ(Φ_i, ϑ_t)`-measurable;
* `dynamics` is vi), (3.2), almost surely. -/
structure NRealization {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [MeasurableSpace X]
    (M : Model T X G) (N : ℕ) (i : Fin N) (mN : Measure (Fin N → X))
    (γ : Measure (Fin N → ProgN T X G (N - 1)))
    (γ' : Measure (ProgN T X G (N - 1) × ProgN T X G (N - 1)))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) where
  state : Ω → Fin (T + 1) → Fin N → X
  sugg : Ω → Fin N → ProgN T X G (N - 1)
  dev : Ω → ProgN T X G (N - 1)
  noise : Ω → Fin T → Fin N → I
  coin : Ω → Fin T → I
  measurable_state : Measurable state
  measurable_sugg : Measurable sugg
  measurable_dev : Measurable dev
  measurable_noise : Measurable noise
  measurable_coin : Measurable coin
  law : P.map (fun ω => (noise ω, state ω 0, coin ω, sugg ω)) =
    (Measure.pi fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I)).prod
      (mN.prod ((Measure.pi fun _ : Fin T => (volume : Measure I)).prod γ))
  dev_law : P.map (fun ω => (sugg ω i, dev ω)) = γ'
  dev_adapted : ∀ t : Fin T,
    Measurable[MeasurableSpace.comap (fun ω => (sugg ω i, coin ω t)) inferInstance] (fun ω => dev ω t)
  dynamics : ∀ᵐ ω ∂P, ∀ (t : Fin T) (j : Fin N),
    state ω t.succ j =
      M.Ψ t (state ω t.castSucc j) (empOthers (state ω t.castSucc) j).1
        ((played i (sugg ω) (dev ω) j t).1 (fun s => state ω s j) (fun s => empOthers (state ω s) j))
        (noise ω t j)

/-- The cost (3.3) of player `i` in a realization:
`𝔼[∑_{t=0}^{T−1} f(t, X^{i,N}_t, μ^{i,N}_t, Φ̃_i(t, X^{i,N}, μ^{i,N})) + F(X^{i,N}_T, μ^{i,N}_T)]`. -/
noncomputable def NRealization.cost {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] {M : Model T X G} {N : ℕ} {i : Fin N} {mN : Measure (Fin N → X)}
    {γ : Measure (Fin N → ProgN T X G (N - 1))}
    {γ' : Measure (ProgN T X G (N - 1) × ProgN T X G (N - 1))}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (R : NRealization M N i mN γ γ' P) : ℝ :=
  ∫ ω, ((∑ t : Fin T, M.f t (R.state ω t.castSucc i) (empOthers (R.state ω t.castSucc) i).1
      ((R.dev ω t).1 (fun s => R.state ω s i) (fun s => empOthers (R.state ω s) i))) +
    M.F (R.state ω (Fin.last T) i) (empOthers (R.state ω (Fin.last T)) i).1) ∂P

/-- Definition 3.5 (p. 6): `γ^N ∈ 𝒫(ℛ̂_N^N)` is an `ε`-correlated equilibrium with initial
distribution `𝔪^N` if `J^N_i(𝔪^N, γ^N, ι_{γ^N_i}) ≤ J^N_i(𝔪^N, γ^N, γ̃) + ε` for every player `i`
and every `γ̃ ∈ 𝒩^N_{γ^N_i}`. Each cost is the expected cost of a realization; the inequality is
required for every realization of each side. -/
def IsEpsCorrEq {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [MeasurableSpace X]
    (M : Model T X G) (N : ℕ) (ε : ℝ) (γ : Measure (Fin N → ProgN T X G (N - 1)))
    (mN : Measure (Fin N → X)) : Prop :=
  ∀ (i : Fin N), ∀ γ' ∈ StratModSet (γ.map (fun φ => φ i)),
    ∀ (Ω₀ : Type) [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
      (R₀ : NRealization M N i mN γ (iotaN (γ.map (fun φ => φ i))) P₀)
      (Ω₁ : Type) [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
      (R₁ : NRealization M N i mN γ γ' P₁),
      R₀.cost ≤ R₁.cost + ε

end ProgCorrMFG.Approx


