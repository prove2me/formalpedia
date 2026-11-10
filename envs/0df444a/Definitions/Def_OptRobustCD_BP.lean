-- Prove2me | Definitions.Def_OptRobustCD_BP
-- name    : OptRobustCD_BP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:51:32.635284+00:00
-- url     : https://prove2.me/theorems/0f5bcb13-3ef9-4ec3-91ef-adf5992053cf
-- title:
--   Belief propagation from an initialization $\mathrm{BP}_{t,\gamma}(G,Y)$, its output law, and $\mathrm{Ov}_{t,\gamma}(G,y)$
-- statement:
--   **BP update** (1): for messages $m_w\in[-1,1]$,
--   $$\mathrm{BP}(\{m_w\})=\frac{\prod_w(1+\lambda m_w)-\prod_w(1-\lambda m_w)}{\prod_w(1+\lambda m_w)+\prod_w(1-\lambda m_w)}.$$
--
--   **$\mathrm{BP}_{t,\gamma}(G,Y)$** (Definition 4.1), for $Y\in\mathbb R^{\vec E(G)}$, $t\ge1$, $\gamma\in(0,1)$:
--
--   1. independently for each directed edge $e$, draw $\tau_e\in\{\pm1\}$ with $\mathbb E\tau_e=\tanh Y_e$;
--   2. set $m^{(0)}_{u\to v}=\gamma\tau_{v\to u}$ and, for $s=1,\dots,t$, $m^{(s)}_{u\to v}=\mathrm{BP}(\{m^{(s-1)}_{w\to u}:w\in\partial u\setminus\{v\}\})$;
--   3. output $\hat\sigma_v=\mathrm{sign}\,\mathrm{BP}(\{m^{(t)}_{w\to v}:w\in\partial v\})$.
--
--   Its output law is a finite law, and $\mathbb E\,\mathrm{ov}(\hat\sigma,\sigma^\star)$ is a finite sum over the rounding.
--
--   **$\mathrm{Ov}_{t,\gamma}(G,y)$** (p.16) is the expected overlap of the output of $\mathrm{BP}_{t,\gamma}(G,\beta\sqrt{|\vec E(G)|}\,y)$ with $\beta=\frac12\sqrt{1-1/(d\lambda^2)}$.
--
--   **Formalization Note** The rounding is drawn on all ordered pairs with weight $\prod_p(1+\tau_p\tanh Y_p)/2$; the output depends only on the directed edges, so its law is that of Definition 4.1. $m^{(0)}_{u\to v}$ uses the reverse edge, as printed. $\mathrm{sign}(0)=+1$ (the paper fixes no rule; $\mathrm{BP}(\emptyset)=0$ at isolated vertices).
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), (1) Definition 3.2 p.13 (pdf p.15); Definition 4.1 p.15 (pdf p.17); Ov and β, p.16 (pdf p.18)

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting
import Definitions.Def_OptRobustCD_DirEdges
import Definitions.Def_OptRobustCD_nbWalks

namespace OptRobustCD

/-!
# Belief propagation from an initialization, `BP_{t,γ}(G, Y)`, and `Ov_{t,γ}(G, y)`

Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027
submission (manuscript of November 3, 2026, sha256 3d287d54…).
* (1), Definition 3.2 (p.13, pdf p.15):
  `BP({m_w}) = (∏(1 + λm_w) − ∏(1 − λm_w)) / (∏(1 + λm_w) + ∏(1 − λm_w))`.
* Definition 4.1 (p.15, pdf p.17): "Given a graph G, an initialization `Y ∈ R^{E⃗(G)}`, an integer
  `t ⩾ 1`, and `γ ∈ (0, 1)`, the procedure `BP_{t,γ}(G, Y)` does the following.
  1. Independently for each directed edge e, draw `τ_e ∈ {±1}` with `E τ_e = tanh Y_e`.
  2. Set `m^{(0)}_{u→v} = γτ_{v→u}` and, for `s = 1, …, t`,
     `m^{(s)}_{u→v} = BP({m^{(s−1)}_{w→u} : w ∈ ∂u ∖ {v}})`.
  3. Output `σ̂_v = sign(BP({m^{(t)}_{w→v} : w ∈ ∂v}))`."
* p.16 (pdf p.18): "`Ov_{t,γ}(G, y)` [is] the expected overlap `E ov(σ̂, σ⋆)` of the output `σ̂` of
  `BP_{t,γ}(G, β√|E⃗(G)| y)`, where the expectation is over the randomized rounding", and
  "`β = (1/2)√(1 − 1/(dλ²))`".

**Formalization Note.**
* The rounding `τ` ranges over `Fin n × Fin n → Bool` (`true ↦ +1`) with weight
  `∏_p (1 + τ_p tanh Y_p)/2`, a product law with `E τ_p = tanh Y_p`; the output depends only on
  `τ` on directed edges, so the law of the output is that of Definition 4.1. Its law and the
  expected overlap are finite sums (`bpProb`, `bpExpOv`).
* `m^{(0)}_{u→v}` uses the rounding of the **reverse** edge `v → u`, as printed.
* `sign x = +1` for `x ≥ 0` and `−1` for `x < 0` (`BP(∅) = 0` at isolated vertices); any fixed rule
  for `0` would do.
* For `|λ| < 1` and messages in `[−1, 1]` the denominator of (1) is positive.
* `Ov` uses the fixed `β = (1/2)√(1 − 1/(dλ²))` of p.16 (`betaKS`) and `|E⃗(G)| = numArcs G`.
-/

open Finset
open scoped Classical

/-- The BP update (1) on the messages `m w`, `w ∈ S`. -/
noncomputable def bpMap {n : ℕ} (lam : ℝ) (S : Finset (Fin n)) (m : Fin n → ℝ) : ℝ :=
  ((∏ w ∈ S, (1 + lam * m w)) - ∏ w ∈ S, (1 - lam * m w)) /
    ((∏ w ∈ S, (1 + lam * m w)) + ∏ w ∈ S, (1 - lam * m w))

/-- The neighbours of `u` in `G`. -/
noncomputable def nbrs {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) : Finset (Fin n) :=
  univ.filter fun w => G.Adj u w

/-- The messages `m^{(s)}_{u→v}` of `BP_{t,γ}` for the rounding `τ`. -/
noncomputable def bpMsg {n : ℕ} (G : SimpleGraph (Fin n)) (lam γ : ℝ) (τ : Fin n × Fin n → Bool) :
    ℕ → Fin n → Fin n → ℝ
  | 0, u, v => γ * spinR (τ (v, u))
  | s + 1, u, v => bpMap lam ((nbrs G u).erase v) (fun w => bpMsg G lam γ τ s w u)

/-- The output `σ̂_v = sign(BP({m^{(t)}_{w→v} : w ∈ ∂v}))` (`true ↦ +1`, sign of `0` is `+1`). -/
noncomputable def bpOut {n : ℕ} (G : SimpleGraph (Fin n)) (lam : ℝ) (t : ℕ) (γ : ℝ)
    (τ : Fin n × Fin n → Bool) : Fin n → Bool :=
  fun v => decide (0 ≤ bpMap lam (nbrs G v) (fun w => bpMsg G lam γ τ t w v))

/-- The probability of the rounding `τ`: `∏_p (1 + τ_p tanh Y_p)/2`. -/
noncomputable def roundWeight {n : ℕ} (Y : EVec n) (τ : Fin n × Fin n → Bool) : ℝ :=
  ∏ p : Fin n × Fin n, (1 + spinR (τ p) * Real.tanh (Y p)) / 2

/-- The probability that `BP_{t,γ}(G, Y)` outputs the labelling `x`. -/
noncomputable def bpProb {n : ℕ} (G : SimpleGraph (Fin n)) (lam : ℝ) (t : ℕ) (γ : ℝ) (Y : EVec n)
    (x : Fin n → Bool) : ℝ :=
  ∑ τ : Fin n × Fin n → Bool, roundWeight Y τ * (if bpOut G lam t γ τ = x then 1 else 0)

/-- `E ov(σ̂, σ⋆)` for the output `σ̂` of `BP_{t,γ}(G, Y)`, over the randomized rounding. -/
noncomputable def bpExpOv {n : ℕ} (G : SimpleGraph (Fin n)) (lam : ℝ) (t : ℕ) (γ : ℝ) (Y : EVec n)
    (σ : Fin n → Bool) : ℝ :=
  ∑ τ : Fin n × Fin n → Bool, roundWeight Y τ * SBMThreshold.Main.overlap σ (bpOut G lam t γ τ)

/-- `β = (1/2)√(1 − 1/(dλ²))` (p.16). -/
noncomputable def betaKS (d lam : ℝ) : ℝ := (1 / 2) * Real.sqrt (1 - 1 / (d * lam ^ 2))

/-- `Ov_{t,γ}(G, y)`: the expected overlap of the output of `BP_{t,γ}(G, β√|E⃗(G)| y)`. -/
noncomputable def Ov {n : ℕ} (d lam : ℝ) (t : ℕ) (γ : ℝ) (G : SimpleGraph (Fin n))
    (σ : Fin n → Bool) (y : EVec n) : ℝ :=
  bpExpOv G lam t γ (fun p => betaKS d lam * Real.sqrt (numArcs G) * y p) σ

end OptRobustCD


