-- Prove2me | Definitions.Def_CtrlVolMFG_IsMFE
-- name    : CtrlVolMFG_IsMFE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:36.36098+00:00
-- url     : https://prove2.me/theorems/8142f927-dd62-4de6-b8dc-f381abb7dbbf
-- title:
--   The data, the Hamiltonian, the $N$-player game with its Nash equilibria, and the mean field equilibrium
-- statement:
--   The data are $b:\mathbb R^n\times\mathbb R^k\times\mathcal P_2(\mathbb R^n)\to\mathbb R^n$, $\sigma,\sigma^0:\mathbb R^n\times\mathbb R^k\times\mathcal P_2(\mathbb R^n)\to\mathbb R^{n\times d}$, $L:\mathbb R^n\times\mathbb R^k\times\mathcal P_2(\mathbb R^n)\to\mathbb R$ and $G:\mathbb R^n\times\mathcal P_2(\mathbb R^n)\to\mathbb R$. The Hamiltonian (2.18) is
--   $$H(x,y,z,z^0,m)=\inf_{a\in\mathbb R^k}\{b(x,a,m)\cdot y+\sigma(x,a,m)\cdot z+\sigma^0(x,a,m)\cdot z^0+L(x,a,m)\},$$
--   and $\hat\alpha(x,y,z,z^0,m)$ denotes a minimizer.
--
--   **$N$-player game (§2.4.1).** Player $i$ controls
--   $$dX^i_t=b(X^i_t,\alpha^i_t,m^N_{\mathbf X_t})dt+\sigma(X^i_t,\alpha^i_t,m^N_{\mathbf X_t})dW^i_t+\sigma^0(X^i_t,\alpha^i_t,m^N_{\mathbf X_t})dW^0_t,\qquad X^i_0=\xi^i,$$
--   with an $\mathbb F^N$-progressive control satisfying $\mathbb E\int_0^T|\alpha_t|^2dt<\infty$, and minimizes $J^{N,i}(\boldsymbol\alpha)=\mathbb E[\int_0^TL(X^i_t,\alpha^i_t,m^N_{\mathbf X_t})dt+G(X^i_T,m^N_{\mathbf X_T})]$. A Nash equilibrium is a tuple $\boldsymbol\alpha$ with $J^{N,i}(\boldsymbol\alpha)\le J^{N,i}(\boldsymbol\alpha^{-i},\alpha)$ for every $i$ and every admissible $\alpha$.
--
--   **Mean field game (§2.4.2).** Given an $\mathbb F^0$-adapted flow $m$, the representative player controls $dX_t=b(X_t,\alpha_t,m_t)dt+\sigma(X_t,\alpha_t,m_t)dW_t+\sigma^0(X_t,\alpha_t,m_t)dW^0_t$, $X_0=\xi$, and minimizes $J_m(\alpha)=\mathbb E[\int_0^TL(X_t,\alpha_t,m_t)dt+G(X_T,m_T)]$. A mean field equilibrium (MFE) is a pair $(m,\alpha)$ with $m$ continuous and $\mathbb F^0$-adapted, $\alpha$ a minimizer of $J_m$ with state process $X$, and
--   $$m_t=\mathcal L(X_t\mid\mathcal F^0_t)\quad d\mathbb P\text{-a.e., for each }t\in[0,T].$$
--
--   **Formalization Note** States solve their equations as continuous progressive Itô processes. Costs are Bochner integrals; the equilibrium costs are required finite and only deviations of finite cost are compared (footnote 1, p.12: under the assumptions every cost is finite). $\hat\alpha$ is chosen by `Classical.choose` when a minimizer exists. The gradients $D_xH$, $D_yH$, $D_zH$, $D_{z^0}H$, $D_xL$, $D_aL$, $D_xG$ are Mathlib gradients.
-- source:
--   Jackson & Tangpi, Quantitative Convergence for Displacement Monotone Mean Field Games with Controlled Volatility, arXiv:2304.04543v2, §2.4 pp.11–13, (2.3)–(2.9); (2.18) p.16

import Mathlib
import Definitions.Def_CtrlVolMFG_Setup

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CtrlVolMFG

/-- The data of the games (Jackson & Tangpi, arXiv:2304.04543v2, §2.4, p.12): the drift
`b : ℝⁿ × ℝᵏ × 𝒫₂(ℝⁿ) → ℝⁿ`, the volatilities `σ, σ⁰ : ℝⁿ × ℝᵏ × 𝒫₂(ℝⁿ) → ℝ^{n×d}`, the running
cost `L : ℝⁿ × ℝᵏ × 𝒫₂(ℝⁿ) → ℝ` and the terminal cost `G : ℝⁿ × 𝒫₂(ℝⁿ) → ℝ` (the initial measure
`m₀` is part of `Setup`). `d` is the Brownian dimension, `n` the state dimension, `k` the control
dimension. -/
structure Data (n k d : ℕ) where
  b : Rn n → Rn k → P2 n → Rn n
  σ : Rn n → Rn k → P2 n → Mat n d
  σ0 : Rn n → Rn k → P2 n → Mat n d
  L : Rn n → Rn k → P2 n → ℝ
  G : Rn n → P2 n → ℝ

namespace Data

variable {n k d : ℕ}

/-- The function minimized in (2.18), (2.20), (3.1) (arXiv:2304.04543v2, pp.16, 19):
`a ↦ b(x, a, m)·y + σ(x, a, m)·z + σ⁰(x, a, m)·z⁰ + L(x, a, m)` (Frobenius pairing for `z, z⁰`). -/
noncomputable def ham (D : Data n k d) (x : Rn n) (a : Rn k) (y : Rn n) (z z0 : Mat n d)
    (m : P2 n) : ℝ :=
  inner ℝ (D.b x a m) y + inner ℝ (D.σ x a m) z + inner ℝ (D.σ0 x a m) z0 + D.L x a m

/-- The Hamiltonian (2.18), p.16: `H(x, y, z, z⁰, m) = inf_{a ∈ ℝᵏ} ham(x, a, y, z, z⁰, m)`.

**Formalization Note** A real infimum; it is a junk value only when the family is unbounded
below, which the assumptions exclude (they give a minimizer). -/
noncomputable def H (D : Data n k d) (x y : Rn n) (z z0 : Mat n d) (m : P2 n) : ℝ :=
  ⨅ a : Rn k, D.ham x a y z z0 m

/-- `α̂(x, y, z, z⁰, m)`, a minimizer of `a ↦ ham(x, a, y, z, z⁰, m)` ((2.20), p.16; (3.1),
p.19); it is the unique minimizer under Assumptions 2.5, 2.12 and 2.19.

**Formalization Note** Chosen by `Classical.choose` when a minimizer exists, `0` otherwise. -/
noncomputable def alphaHat (D : Data n k d) (x y : Rn n) (z z0 : Mat n d) (m : P2 n) : Rn k := by
  classical
  exact if h : ∃ a : Rn k, ∀ a', D.ham x a y z z0 m ≤ D.ham x a' y z z0 m then h.choose else 0

/-- `D_xH`, the gradient of the Hamiltonian in `x` (Assumption 2.17, p.16). -/
noncomputable def DxH (D : Data n k d) (x y : Rn n) (z z0 : Mat n d) (m : P2 n) : Rn n :=
  gradient (fun x' => D.H x' y z z0 m) x

/-- `D_yH`, the gradient of the Hamiltonian in `y`. -/
noncomputable def DyH (D : Data n k d) (x y : Rn n) (z z0 : Mat n d) (m : P2 n) : Rn n :=
  gradient (fun y' => D.H x y' z z0 m) y

/-- `D_zH`, the gradient of the Hamiltonian in `z` (Frobenius). -/
noncomputable def DzH (D : Data n k d) (x y : Rn n) (z z0 : Mat n d) (m : P2 n) : Mat n d :=
  gradient (fun z' => D.H x y z' z0 m) z

/-- `D_{z⁰}H`, the gradient of the Hamiltonian in `z⁰` (Frobenius). -/
noncomputable def Dz0H (D : Data n k d) (x y : Rn n) (z z0 : Mat n d) (m : P2 n) : Mat n d :=
  gradient (fun z' => D.H x y z z' m) z0

/-- `D_xL(x, a, m)`. -/
noncomputable def DxL (D : Data n k d) (x : Rn n) (a : Rn k) (m : P2 n) : Rn n :=
  gradient (fun x' => D.L x' a m) x

/-- `D_aL(x, a, m)`. -/
noncomputable def DaL (D : Data n k d) (x : Rn n) (a : Rn k) (m : P2 n) : Rn k :=
  gradient (fun a' => D.L x a' m) a

/-- `D_xG(x, m)`. -/
noncomputable def DxG (D : Data n k d) (x : Rn n) (m : P2 n) : Rn n := Dx D.G x m

end Data

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n k d : ℕ}

/-- The finite-cost condition for a cost `𝔼[∫₀ᵀ ℓ_t dt + g]`: `t ↦ ℓ_t(ω)` is integrable on
`[0, T]` for almost every `ω`, and `ω ↦ ∫₀ᵀ ℓ_t(ω) dt` and `g` are integrable. -/
def CostFinite (P : Measure Ω) (T : ℝ≥0) (ℓ : ℝ≥0 → Ω → ℝ) (g : Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => ℓ s.toNNReal ω) (Set.Icc 0 T)) ∧
    Integrable (fun ω => ∫ s in Set.Icc (0 : ℝ) T, ℓ s.toNNReal ω) P ∧ Integrable g P

/-- The cost `𝔼[∫₀ᵀ ℓ_t dt + g]` (Bochner integrals; used only together with `CostFinite`). -/
noncomputable def cost (P : Measure Ω) (T : ℝ≥0) (ℓ : ℝ≥0 → Ω → ℝ) (g : Ω → ℝ) : ℝ :=
  ∫ ω, ((∫ s in Set.Icc (0 : ℝ) T, ℓ s.toNNReal ω) + g ω) ∂P

/-- The state equations (2.3), p.12, of the `N`-player game on `[0, T]`, for controls
`α = (α¹, …, αᴺ)`: for each player `i`,
`dXⁱ_t = b(Xⁱ_t, αⁱ_t, m^N_{X_t})dt + σ(Xⁱ_t, αⁱ_t, m^N_{X_t})dWⁱ_t + σ⁰(Xⁱ_t, αⁱ_t, m^N_{X_t})dW⁰_t`,
`Xⁱ_0 = ξⁱ`, as continuous `𝔽ᴺ`-progressive Itô processes. -/
def StateEqN (S : Setup n d Ω) (D : Data n k d) (T : ℝ≥0) (N : ℕ)
    (α : Fin N → ℝ≥0 → Ω → Rn k) (X : Fin N → ℝ≥0 → Ω → Rn n) : Prop :=
  ∀ i : Fin N, IsItoProc (S.filtN N) S.P T (S.noise i) (S.ξ i)
    (fun t ω => D.b (X i t ω) (α i t ω) (empP2 fun l => X l t ω))
    (Sum.elim (fun j t ω => col (D.σ (X i t ω) (α i t ω) (empP2 fun l => X l t ω)) j)
      (fun j t ω => col (D.σ0 (X i t ω) (α i t ω) (empP2 fun l => X l t ω)) j))
    (X i)

/-- The running cost of player `i` in (2.5), p.12. -/
noncomputable def runCostN (D : Data n k d) {N : ℕ} (α : Fin N → ℝ≥0 → Ω → Rn k)
    (X : Fin N → ℝ≥0 → Ω → Rn n) (i : Fin N) : ℝ≥0 → Ω → ℝ :=
  fun t ω => D.L (X i t ω) (α i t ω) (empP2 fun l => X l t ω)

/-- The terminal cost of player `i` in (2.5), p.12. -/
noncomputable def termCostN (D : Data n k d) (T : ℝ≥0) {N : ℕ} (X : Fin N → ℝ≥0 → Ω → Rn n)
    (i : Fin N) : Ω → ℝ :=
  fun ω => D.G (X i T ω) (empP2 fun l => X l T ω)

/-- A Nash equilibrium of the `N`-player game (arXiv:2304.04543v2, §2.4.1, p.12), with its state
process `X`: each `αⁱ` is admissible ((2.4): `𝔽ᴺ`-progressive with `𝔼∫₀ᵀ|αⁱ_t|²dt < ∞`), `X`
solves (2.3), every cost `J^{N,i}(α)` of (2.5) is finite, and for every player `i`, every
admissible `α'` and the state process `X'` of `(α^{-i}, α')`, `J^{N,i}(α) ≤ J^{N,i}(α^{-i}, α')`.

**Formalization Note** Footnote 1, p.12: under the paper's assumptions every cost is finite.
Deviations whose cost is not finite (not integrable) are not compared. -/
def IsNashN (S : Setup n d Ω) (D : Data n k d) (T : ℝ≥0) (N : ℕ)
    (α : Fin N → ℝ≥0 → Ω → Rn k) (X : Fin N → ℝ≥0 → Ω → Rn n) : Prop :=
  (∀ i, Peng1990.SMP.L2F (S.filtN N) S.P T (α i)) ∧ StateEqN S D T N α X ∧
    (∀ i, CostFinite S.P T (runCostN D α X i) (termCostN D T X i)) ∧
    ∀ (i : Fin N) (α' : ℝ≥0 → Ω → Rn k) (X' : Fin N → ℝ≥0 → Ω → Rn n),
      Peng1990.SMP.L2F (S.filtN N) S.P T α' →
      StateEqN S D T N (Function.update α i α') X' →
      CostFinite S.P T (runCostN D (Function.update α i α') X' i) (termCostN D T X' i) →
      cost S.P T (runCostN D α X i) (termCostN D T X i) ≤
        cost S.P T (runCostN D (Function.update α i α') X' i) (termCostN D T X' i)

/-- The state equation (2.8), p.12, of the mean field game given a measure flow `m`:
`dX_t = b(X_t, α_t, m_t)dt + σ(X_t, α_t, m_t)dW_t + σ⁰(X_t, α_t, m_t)dW⁰_t`, `X₀ = ξ`, as a
continuous `𝔽`-progressive Itô process (`𝔽 = 𝔽¹`, `ξ = ξ¹`, `W = W¹`). -/
def StateEqMF (S : Setup n d Ω) (D : Data n k d) (T : ℝ≥0) (m : ℝ≥0 → Ω → P2 n)
    (α : ℝ≥0 → Ω → Rn k) (X : ℝ≥0 → Ω → Rn n) : Prop :=
  IsItoProc (S.filtN 1) S.P T (S.noise 0) (S.ξ 0)
    (fun t ω => D.b (X t ω) (α t ω) (m t ω))
    (Sum.elim (fun j t ω => col (D.σ (X t ω) (α t ω) (m t ω)) j)
      (fun j t ω => col (D.σ0 (X t ω) (α t ω) (m t ω)) j)) X

/-- A mean field equilibrium (MFE) `(m, α)` with state process `X` (arXiv:2304.04543v2, §2.4.2,
pp.12–13):
1. `m` is an `𝔽⁰`-adapted `𝒫₂(ℝⁿ)`-valued process with continuous paths on `[0, T]` (for `𝒲₂`);
2. `α ∈ 𝒜` ((2.6): `𝔽`-progressive with `𝔼∫₀ᵀ|α_t|²dt < ∞`), `X` solves (2.8), and `α`
   minimizes `J_m` of (2.7) over `𝒜`;
3. `m_t = ℒ(X_t | ℱ⁰_t)` almost surely, for each `t ∈ [0, T]` (2.9).

**Formalization Note** `𝔽⁰`-adaptedness of `m` is measurability of `ω ↦ m_t(ω)(A)` for every
Borel `A` (the Giry σ-algebra). Path continuity is required almost surely. As in `IsNashN`, the
costs are finite and only deviations with finite cost are compared. -/
def IsMFE (S : Setup n d Ω) (D : Data n k d) (T : ℝ≥0) (m : ℝ≥0 → Ω → P2 n)
    (α : ℝ≥0 → Ω → Rn k) (X : ℝ≥0 → Ω → Rn n) : Prop :=
  (∀ t ≤ T, ∀ A : Set (Rn n), MeasurableSet A → Measurable[S.F0 t] (fun ω => (m t ω).1 A)) ∧
    (∀ᵐ ω ∂S.P, ∀ t ∈ Set.Icc 0 T, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Set.Icc 0 T,
      dist s t < δ → W2 (m s ω) (m t ω) < ε) ∧
    Peng1990.SMP.L2F (S.filtN 1) S.P T α ∧ StateEqMF S D T m α X ∧
    CostFinite S.P T (fun t ω => D.L (X t ω) (α t ω) (m t ω)) (fun ω => D.G (X T ω) (m T ω)) ∧
    (∀ (α' : ℝ≥0 → Ω → Rn k) (X' : ℝ≥0 → Ω → Rn n),
      Peng1990.SMP.L2F (S.filtN 1) S.P T α' → StateEqMF S D T m α' X' →
      CostFinite S.P T (fun t ω => D.L (X' t ω) (α' t ω) (m t ω))
        (fun ω => D.G (X' T ω) (m T ω)) →
      cost S.P T (fun t ω => D.L (X t ω) (α t ω) (m t ω)) (fun ω => D.G (X T ω) (m T ω)) ≤
        cost S.P T (fun t ω => D.L (X' t ω) (α' t ω) (m t ω))
          (fun ω => D.G (X' T ω) (m T ω))) ∧
    ∀ t ∈ Set.Icc 0 T, IsCondLaw S X m t

end CtrlVolMFG


