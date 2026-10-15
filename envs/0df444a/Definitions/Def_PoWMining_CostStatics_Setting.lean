-- Prove2me | Definitions.Def_PoWMining_CostStatics_Setting
-- name    : PoWMining_CostStatics_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:18.684845+00:00
-- url     : https://prove2.me/theorems/5b10693c-4b46-4a30-8ed9-a1f6afd62c29
-- title:
--   (4.1), (B.3), (B.4), p. 42 — the closed-form equilibrium of the mining game at a fixed active set, and the direct and indirect cost sensitivities
-- statement:
--   Consider $n$ miners who are all active in the equilibrium of the proof-of-work mining game of Capponi, Ólafsson and Alsabah. Miner $i$ has cost-per-hash $c_i > 0$; every miner bears the quadratic capacity cost $(\gamma/2)h_i^2$ with $\gamma \ge 0$, and the miners compete for a reward $R > 0$. Write $c^{(n)} = c_1 + \dots + c_n$ for the cumulative cost.
--
--   **Aggregate hash rate (4.1)/(B.3).** The aggregate equilibrium hash rate is
--   $$g = g(c_1,\dots,c_n,\gamma,R) = \begin{cases} \dfrac{\sqrt{(c^{(n)})^2 + 4(n-1)R\gamma} - c^{(n)}}{2\gamma}, & \gamma > 0,\\[2mm] \dfrac{(n-1)R}{c^{(n)}}, & \gamma = 0,\end{cases}$$
--   the positive root of $\gamma H^2 + c^{(n)} H - (n-1)R = 0$.
--
--   **Individual hash rates (B.3).** For an argument $G$ standing for the aggregate,
--   $$f_i(G) = G\,\frac{R - c_i G}{R + \gamma G^2},$$
--   and the equilibrium hash rate of miner $i$ is $h^*_i = f_i(g)$; its hash rate share is $h^*_i/H^* = f_i(g)/g$.
--
--   **Sensitivities.** Write $\partial g/\partial c_i$ for the derivative of $g$ in the $i$-th cost (all other costs, $\gamma$ and $R$ fixed) and $\partial f_i/\partial g$ for the derivative of $f_i(G)$ in $G$ at $G = g$. The direct and indirect sensitivities of (B.4) and their share analogues (decomposition on p. 42) are
--   $$\Delta_{i,1} = \frac{\partial f_i}{\partial c_i}\Big|_{g\text{ fixed}},\qquad \Delta_{i,2} = \frac{\partial f_i}{\partial g}\,\frac{\partial g}{\partial c_i},\qquad \widetilde\Delta_{i,1} = \frac{\Delta_{i,1}}{g},\qquad \widetilde\Delta_{i,2} = \frac{1}{g}\,\frac{\partial g}{\partial c_i}\Big(\frac{\partial f_i}{\partial g} - \frac{f_i}{g}\Big).$$
--
--   **Standing assumptions.** $n \ge 2$, $R > 0$, $\gamma \ge 0$, every $c_k > 0$, and all $n$ miners are active at the point: $R - c_k g > 0$ for every $k$.
--
--   These objects are what Proposition 4.6 is about: the derivatives of equilibrium hash rates and shares with respect to costs, at a state where small cost changes do not alter the set of active miners.
--
--   **Formalization Note.** Miners are indexed by `Fin n`, 0-based: Lean miner `i` is the paper's miner $i+1$. The sensitivities are defined by `deriv` (one-variable derivatives along `Function.update c i`), never by their closed forms; the closed forms are theorems. The paper never defines $\widetilde\Delta_{i,1}, \widetilde\Delta_{i,2}$; they are pinned by the decomposition $\partial(f_i/g)/\partial c_i = \frac1g(\partial f_i/\partial c_i + \partial g/\partial c_i(\partial f_i/\partial g - f_i/g))$ printed on p. 42. Only the $n$ active miners appear; the inactive miners of the full game do not enter (B.3). Sorting of the costs is not needed.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 12 (c^(n), (4.1)), p. 39 (B.3), p. 40 (B.4), p. 42 (proof of Proposition 4.6, part (iii))

import Mathlib

namespace PoWMining.CostStatics

/-- Cumulative cost `c⁽ⁿ⁾ = c₁ + ⋯ + cₙ` of the `n` active miners (p. 12). -/
def cumCost {n : ℕ} (c : Fin n → ℝ) : ℝ := ∑ k, c k

/-- The aggregate equilibrium hash rate `g = H*` of (4.1)/(B.3) for the `n` active miners with
costs `c`, capacity parameter `γ` and reward `R`: the positive root of
`γ H² + c⁽ⁿ⁾ H − (n − 1) R = 0` when `γ > 0`, and `(n − 1) R / c⁽ⁿ⁾` when `γ = 0`. -/
noncomputable def gH {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) : ℝ :=
  if 0 < γ then (Real.sqrt (cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ) - cumCost c) / (2 * γ)
  else ((n : ℝ) - 1) * R / cumCost c

/-- The map `fᵢ` of (B.3), with the aggregate `g` as a free argument `G`:
`fᵢ = G (R − cᵢ G) / (R + γ G²)`. -/
noncomputable def fH {n : ℕ} (c : Fin n → ℝ) (γ R G : ℝ) (i : Fin n) : ℝ :=
  G * (R - c i * G) / (R + γ * G ^ 2)

/-- The equilibrium hash rate `h*ᵢ = fᵢ(c₁, …, cₙ, γ, R)` of an active miner (B.3). -/
noncomputable def hstar {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (i : Fin n) : ℝ :=
  fH c γ R (gH c γ R) i

/-- The hash rate share `h*ᵢ / H*` of miner `i`. -/
noncomputable def share {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (i : Fin n) : ℝ :=
  hstar c γ R i / gH c γ R

/-- `∂g/∂cᵢ`: derivative of the aggregate along the `i`-th cost coordinate. -/
noncomputable def dgdc {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (i : Fin n) : ℝ :=
  deriv (fun t => gH (Function.update c i t) γ R) (c i)

/-- `∂fᵢ/∂g`: derivative of `fᵢ` in its aggregate argument, at `G = g`. -/
noncomputable def dfdg {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (i : Fin n) : ℝ :=
  deriv (fun G => fH c γ R G i) (gH c γ R)

/-- Direct sensitivity `Δᵢ,₁ := ∂fᵢ/∂cᵢ` with `g` held fixed (B.4). -/
noncomputable def Delta1 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (i : Fin n) : ℝ :=
  deriv (fun t => fH (Function.update c i t) γ R (gH c γ R) i) (c i)

/-- Indirect sensitivity `Δᵢ,₂ := ∂fᵢ/∂g · ∂g/∂cᵢ` (B.4). -/
noncomputable def Delta2 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (i : Fin n) : ℝ :=
  dfdg c γ R i * dgdc c γ R i

/-- `Δ̃ᵢ,₁ := (1/g) ∂fᵢ/∂cᵢ` (decomposition on p. 42). -/
noncomputable def DeltaT1 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (i : Fin n) : ℝ :=
  Delta1 c γ R i / gH c γ R

/-- `Δ̃ᵢ,₂ := (1/g) ∂g/∂cᵢ (∂fᵢ/∂g − fᵢ/g)` (decomposition on p. 42). -/
noncomputable def DeltaT2 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (i : Fin n) : ℝ :=
  dgdc c γ R i * (dfdg c γ R i - hstar c γ R i / gH c γ R) / gH c γ R

/-- Standing assumptions: at least two miners, positive reward, `γ ≥ 0`, positive costs, and
all `n` miners active at the point (`R − cₖ g > 0`, i.e. `h*ₖ > 0`). -/
structure Standing {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) : Prop where
  two_le : 2 ≤ n
  R_pos : 0 < R
  γ_nonneg : 0 ≤ γ
  c_pos : ∀ k, 0 < c k
  active : ∀ k, 0 < R - c k * gH c γ R

end PoWMining.CostStatics


