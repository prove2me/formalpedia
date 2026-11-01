-- Prove2me | Definitions.Def_BilateralRegret_sbPrice
-- name    : BilateralRegret_sbPrice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:24.886997+00:00
-- url     : https://prove2.me/theorems/ece1955a-9fb2-4a70-af8b-d1fb1b8e193c
-- title:
--   Scouting Bandits (Algorithm 3): the grid $q_k$, the estimates $\widehat F_k,\widehat G_k$, the surrogate rewards $Z_{H,t}(k)$ and the posted prices $P_t$
-- statement:
--   **Scouting Bandits** (SB) with exploration time $T_0$, grid size $K$ and a $K$-armed bandit strategy $\alpha$ works as follows.
--
--   1. **Grid.** $q_k=k/(K+1)$, $k=1,\dots,K$.
--   2. **Scouting phase**, rounds $t=1,\dots,T_0$: post the uniform price $P_t=U_t$ and observe the realistic feedback $(\mathbb I\{S_t\le U_t\},\mathbb I\{U_t\le B_t\})$. Then set
--
--   $$
--   \widehat F_k=\frac1{T_0}\sum_{s=1}^{T_0}\mathbb I\{q_k\le U_s\le B_s\},\qquad \widehat G_k=\frac1{T_0}\sum_{s=1}^{T_0}\mathbb I\{S_s\le U_s\le q_k\},
--   $$
--
--   and $H=(\widehat F_k,\widehat G_k)_{k\in[K]}$.
--   3. **Bandit phase**, rounds $t=T_0+1,T_0+2,\dots$: let $\alpha$ choose the arm $I_t$ (its round $t-T_0$, with uniforms $U_{T_0+1},\dots,U_t$), post $P_t=q_{I_t}$, observe $(\mathbb I\{S_t\le q_{I_t}\},\mathbb I\{q_{I_t}\le B_t\})$ and feed $\alpha$ the reward
--
--   $$
--   Z_{H,t}(I_t)=\mathbb I\{S_t\le q_{I_t}\}\widehat F_{I_t}+\mathbb I\{q_{I_t}\le B_t\}\widehat G_{I_t}.
--   $$
--
--   The module also defines $Z_{H,t}(k)$ for every arm, the arm $I_{H,t}$, the set of bandit-phase rounds, and the numbers $\mathbb P[q_k\le U_1\le B_1]$ and $\mathbb P[S_1\le U_1\le q_k]$ used in the analysis. The valuations enter the prices only through the realistic feedback bits of earlier rounds.
--
--   **Formalization Note** Arms are `Fin K`, so $q_k$ is `grid K (k-1)` with `grid K k = (k+1)/(K+1)`. The player's randomization is one i.i.d. uniform sequence: SB posts $U_t$ in the scouting phase and passes $U_{T_0+1},U_{T_0+2},\dots$ to $\alpha$ as its uniforms.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, Bilateral Trade: A Regret Minimization Perspective, arXiv:2109.12974v1, Algorithm 3, p.11; proof of Theorem 3, pp.12–13 (H, Z_(h,t), I_(H,t), P[q_k ≤ U_1 ≤ B_1], P[S_1 ≤ U_1 ≤ q_k])

import Mathlib
import Definitions.Def_BilateralRegret_regret
import Definitions.Def_BilateralRegret_BanditStrategy

namespace BilateralRegret

open MeasureTheory

/-- **The price grid of Scouting Bandits**: `q_k = k/(K+1)`, `k = 1, …, K` (Algorithm 3, p.11).

**Formalization Note.** Arms are `k : Fin K`, so the paper's `q_k` is `grid K (k − 1)`:
`grid K k = (k + 1)/(K + 1)`. -/
noncomputable def grid (K : ℕ) (k : Fin K) : ℝ := ((k : ℝ) + 1) / ((K : ℝ) + 1)

/-- **The scouting estimate `F̂_k`** after the scouting phase (Algorithm 3, p.11):
`F̂_k = (1/T₀) Σ_{s=1}^{T₀} 𝕀{q_k ≤ U_s ≤ B_s}`, written as `𝕀{q_k ≤ U_s} · 𝕀{U_s ≤ B_s}`, the
product of a known quantity and the realistic feedback bit `𝕀{P_s ≤ B_s}` of round `s` (the
posted price is `P_s = U_s`).

`u`, `b` are the uniform draws and buyer valuations, round `s + 1` at index `s`. -/
noncomputable def Fhat (T₀ K : ℕ) (u b : ℕ → ℝ) (k : Fin K) : ℝ :=
  (1 / (T₀ : ℝ)) * ∑ s ∈ Finset.range T₀, ind (grid K k ≤ u s) * ind (u s ≤ b s)

/-- **The scouting estimate `Ĝ_k`** (Algorithm 3, p.11):
`Ĝ_k = (1/T₀) Σ_{s=1}^{T₀} 𝕀{S_s ≤ U_s ≤ q_k}`, written as `𝕀{S_s ≤ U_s} · 𝕀{U_s ≤ q_k}`, the
product of the realistic feedback bit `𝕀{S_s ≤ P_s}` and a known quantity. -/
noncomputable def Ghat (T₀ K : ℕ) (u s : ℕ → ℝ) (k : Fin K) : ℝ :=
  (1 / (T₀ : ℝ)) * ∑ i ∈ Finset.range T₀, ind (s i ≤ u i) * ind (u i ≤ grid K k)

/-- **The surrogate reward** `Z_{h}(k) = 𝕀{S ≤ q_k} f_k + 𝕀{q_k ≤ B} g_k` of arm `k` for the
estimates `h = (f_k, g_k)_k` and a valuation pair `(S, B)` (proof of Theorem 3, p.12; Algorithm 3,
p.11, "feed α the reward"). For the arm `k` that is posted, `𝕀{S ≤ q_k}` and `𝕀{q_k ≤ B}` are the
realistic feedback. -/
noncomputable def Zfun {K : ℕ} (f g : Fin K → ℝ) (s b : ℝ) (k : Fin K) : ℝ :=
  ind (s ≤ grid K k) * f k + ind (grid K k ≤ b) * g k

/-- **The arm played by Scouting Bandits** in its `(j+1)`-th bandit round, i.e. in round
`T₀ + j + 1` (Algorithm 3, p.11): the arm that `α` plays on its own round counter, with
uniforms `V_{j+1} = U_{T₀+j+1}` and fed the rewards
`Z_{T₀+i+1}(I_{T₀+i+1}) = 𝕀{S ≤ q_I} F̂_I + 𝕀{q_I ≤ B} Ĝ_I` of the earlier bandit rounds.

`u`, `s`, `b`: uniform draws, seller and buyer valuations, round `r + 1` at index `r`. -/
noncomputable def sbArm (T₀ K : ℕ) (α : BanditStrategy K) (u s b : ℕ → ℝ) (j : ℕ) : Fin K :=
  α.action (fun i => u (T₀ + i))
    (fun i k => Zfun (Fhat T₀ K u b) (Ghat T₀ K u s) (s (T₀ + i)) (b (T₀ + i)) k) j

open Classical in
/-- **The price posted by Scouting Bandits** in round `t + 1` (Algorithm 3, p.11): `U_{t+1}` in
the scouting phase (`t + 1 ≤ T₀`), and `q_{I_{t+1}}` in the bandit phase.

The valuations enter only through the realistic feedback bits `𝕀{S_r ≤ P_r}`, `𝕀{P_r ≤ B_r}` of
earlier rounds `r` (via `F̂`, `Ĝ` and the rewards fed to `α`). -/
noncomputable def sbPriceSeq (T₀ K : ℕ) (α : BanditStrategy K) (u s b : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t < T₀ then u t else grid K (sbArm T₀ K α u s b (t - T₀))

/-- **Scouting Bandits (SB) run with parameters `T₀`, `K`, `α`** as a price process on the
horizon-`T` sample space (Algorithm 3, p.11): the price `P_t(ω)` posted in round `t`.

**Formalization Note.** The player's randomization is the one i.i.d. uniform sequence `U_t` of
the sample space (Definition 2, p.23): SB posts `U_t` in rounds `t ≤ T₀` and passes
`U_{T₀+1}, U_{T₀+2}, …` to `α` as its internal randomization. -/
noncomputable def sbPrice (T₀ K : ℕ) (α : BanditStrategy K) (T : ℕ) : Scenario T → Fin T → ℝ :=
  fun ω t => sbPriceSeq T₀ K α (extendSeq (unifDraw ω)) (extendSeq (sellerVal ω))
    (extendSeq (buyerVal ω)) t

/-- The estimates `H = (F̂_k, Ĝ_k)_k` on the horizon-`T` sample space: the `F̂` part. -/
noncomputable def HF (T₀ K T : ℕ) (ω : Scenario T) : Fin K → ℝ :=
  Fhat T₀ K (extendSeq (unifDraw ω)) (extendSeq (buyerVal ω))

/-- The estimates `H = (F̂_k, Ĝ_k)_k` on the horizon-`T` sample space: the `Ĝ` part. -/
noncomputable def HG (T₀ K T : ℕ) (ω : Scenario T) : Fin K → ℝ :=
  Ghat T₀ K (extendSeq (unifDraw ω)) (extendSeq (sellerVal ω))

/-- `Z_{H,t}(k) = 𝕀{S_t ≤ q_k} F̂_k + 𝕀{q_k ≤ B_t} Ĝ_k` (proof of Theorem 3, p.12). -/
noncomputable def ZH (T₀ K T : ℕ) (ω : Scenario T) (t : Fin T) (k : Fin K) : ℝ :=
  Zfun (HF T₀ K T ω) (HG T₀ K T ω) (sellerVal ω t) (buyerVal ω t) k

/-- `I_{H,t}`: the arm played by SB in the bandit-phase round `t` (`t ≥ T₀ + 1`), i.e. the arm
`α` plays on the rewards `(Z_{H,t})_{t ≥ T₀+1}` (proof of Theorem 3, p.12). -/
noncomputable def IH (T₀ K : ℕ) (α : BanditStrategy K) (T : ℕ) (ω : Scenario T) (t : Fin T) :
    Fin K :=
  sbArm T₀ K α (extendSeq (unifDraw ω)) (extendSeq (sellerVal ω)) (extendSeq (buyerVal ω))
    ((t : ℕ) - T₀)

/-- The bandit-phase rounds `t = T₀ + 1, …, T` (indices `T₀, …, T − 1`). -/
def banditRounds (T₀ T : ℕ) : Finset (Fin T) := Finset.univ.filter fun t => T₀ ≤ (t : ℕ)

/-- `ℙ[q_k ≤ U_1 ≤ B_1]` for `U_1` uniform on `[0,1]` independent of `B_1 ∼ μ_B`
(proof of Theorem 3, p.13). -/
noncomputable def pF (K : ℕ) (μB : Measure ℝ) (k : Fin K) : ℝ :=
  (unif.prod μB).real {x | grid K k ≤ x.1 ∧ x.1 ≤ x.2}

/-- `ℙ[S_1 ≤ U_1 ≤ q_k]` for `S_1 ∼ μ_S` independent of `U_1` uniform on `[0,1]`
(proof of Theorem 3, p.13). -/
noncomputable def pG (K : ℕ) (μS : Measure ℝ) (k : Fin K) : ℝ :=
  (μS.prod unif).real {x | x.1 ≤ x.2 ∧ x.2 ≤ grid K k}

end BilateralRegret


