-- Prove2me | Definitions.Def_OfflineCMC_Minimax_HardFamily
-- name    : OfflineCMC_Minimax_HardFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:43.7136+00:00
-- url     : https://prove2.me/theorems/e9be56b7-4351-4cff-81b4-67703ad2c20c
-- title:
--   Hard family of G.3 Part 1: base row b, perturbed rows η(σ), matrices M_σ (G.19) and M_0, path laws, KL divergence, the vector (G.23) (pp. 51–53)
-- statement:
--   Fix an even integer $d$, a number $0<p_\star<1/(d+1)$ and $0<\varepsilon<1/32$. The state space has $d+1$ states. The last one, $d+1$, is special.
--
--   **Rows.** The base row is
--   $$
--   b=\Big(\tfrac{1-p_\star}{d},\dots,\tfrac{1-p_\star}{d},\,p_\star\Big).
--   $$
--   For a sign vector $\sigma=(\sigma_1,\dots,\sigma_{d/2})\in\{-1,1\}^{d/2}$, the perturbed row is
--   $$
--   \eta(\sigma)=\Big(\tfrac{1-p_\star+16\sigma_1\varepsilon}{d},\tfrac{1-p_\star-16\sigma_1\varepsilon}{d},\dots,\tfrac{1-p_\star+16\sigma_{d/2}\varepsilon}{d},\tfrac{1-p_\star-16\sigma_{d/2}\varepsilon}{d},\,p_\star\Big).
--   $$
--
--   **Matrices.** $M_\sigma$ (eq. (G.19)) is the $(d+1)\times(d+1)$ matrix whose first $d$ rows equal $b$ and whose last row is $\eta(\sigma)$. $M_0$ is the matrix all of whose rows equal $b$.
--
--   **Path laws and divergence.** For an initial law $\nu$ and a transition matrix $Q$, the path $(X_0,\dots,X_m)$ of the Markov chain has law
--   $$
--   P(x_0,\dots,x_m)=\nu(x_0)\prod_{i<m}Q(x_i,x_{i+1}).
--   $$
--   The Kullback–Leibler divergence of two mass functions on a finite set is $D(P\|Q)=\sum_x P(x)\log\frac{P(x)}{Q(x)}$, with the natural logarithm.
--
--   **The vector (G.23).** Its coordinate at a non-special state is $((1-p_\star)^2+(1-p_\star\pm16\sigma_i\varepsilon)p_\star)/d$, with the sign of $\eta(\sigma)$ at that coordinate. Its last coordinate is $p_\star$.
--
--   **Realization.** A controlled Markov chain *realizes* $M_\sigma$ when it has one control, its transition matrix is $M_\sigma$, and $X_0$ has law $b$.
--
--   This family is the subclass $\mathcal M'$ of the minimax lower bound.
--
--   **Formalization Note**
--   1. States are `Fin (d + 1)`, with the special state `Fin.last d`; the paper's states $1,\dots,d$ are $0,\dots,d-1$.
--   2. Sign vectors are maps `Fin (d / 2) → ℤˣ` (the units of $\mathbb Z$ are $\pm1$). Coordinates $2i-2$ and $2i-1$ carry $+\sigma_i$ and $-\sigma_i$.
--   3. If $d$ were odd, a leftover coordinate would get sign $0$. Every statement assumes $d$ even.
-- source:
--   Banerjee, Honnappa & Rao, Offline Estimation of Controlled Markov Chains: Minimaxity and Sample Complexity, arXiv:2211.07092v5, p. 51 (η(σ), (G.19), (G.22)), p. 52 (D_σ), p. 53 (G.23), App. G.3 Part 1

import Mathlib
import Definitions.Def_OfflineCMC_Minimax_CMC

namespace OfflineCMC.Minimax

open MeasureTheory

/-! ### The hard family of Appendix G.3, Part 1 (p. 51)

States are `Fin (d + 1)`; the special state `d + 1` of the paper is `Fin.last d`, and the paper's
states `1, …, d` are `0, …, d − 1`. Sign vectors `σ ∈ {−1, 1}^{d/2}` are maps `Fin (d / 2) → ℤˣ`. -/

/-- The sign with which `ε` enters coordinate `t` of `η(σ)`: for the paper's coordinates
`2i − 1, 2i` (`i = 1, …, d/2`), here `t = 2i − 2, 2i − 1`, it is `+σ_i` and `−σ_i`; `0` at the
special state (and at a leftover coordinate when `d` is odd). -/
def hardSign {d : ℕ} (σ : Fin (d / 2) → ℤˣ) (t : Fin (d + 1)) : ℝ :=
  if h : t.val / 2 < d / 2 then
    (if t.val % 2 = 0 then (1 : ℝ) else -1) * (((σ ⟨t.val / 2, h⟩ : ℤˣ) : ℤ) : ℝ)
  else 0

/-- The base row `b = ((1 − p★)/d, …, (1 − p★)/d, p★)`. -/
noncomputable def baseRow (d : ℕ) (p : ℝ) (t : Fin (d + 1)) : ℝ :=
  if t = Fin.last d then p else (1 - p) / (d : ℝ)

/-- The perturbed row `η(σ) = ((1 − p★ + 16σ₁ε)/d, (1 − p★ − 16σ₁ε)/d, …, (1 − p★ − 16σ_{d/2}ε)/d, p★)`. -/
noncomputable def etaRow (d : ℕ) (p ε : ℝ) (σ : Fin (d / 2) → ℤˣ) (t : Fin (d + 1)) : ℝ :=
  if t = Fin.last d then p else (1 - p + 16 * hardSign σ t * ε) / (d : ℝ)

/-- The transition matrix `M_σ` of (G.19): rows `1, …, d` equal `b`, the last row is `η(σ)`. -/
noncomputable def hardMatrix (d : ℕ) (p ε : ℝ) (σ : Fin (d / 2) → ℤˣ) (s t : Fin (d + 1)) : ℝ :=
  if s = Fin.last d then etaRow d p ε σ t else baseRow d p t

/-- The matrix `M_0`, every row equal to `b`. -/
noncomputable def baseMatrix (d : ℕ) (p : ℝ) (_s t : Fin (d + 1)) : ℝ :=
  baseRow d p t

/-- The Kullback–Leibler divergence `D(P ‖ Q) = ∑_x P(x) log(P(x)/Q(x))` of two mass functions on a
finite set (natural logarithm). -/
noncomputable def klDivFin {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ :=
  ∑ x, P x * Real.log (P x / Q x)

/-- The law of the path `(X_0, …, X_m)` of a Markov chain with initial law `ν` and transition
matrix `Q`: `P(x_0, …, x_m) = ν(x_0) ∏_{i<m} Q(x_i, x_{i+1})`. -/
noncomputable def pathLaw {n : ℕ} (ν : Fin n → ℝ) (Q : Fin n → Fin n → ℝ) (m : ℕ)
    (x : Fin (m + 1) → Fin n) : ℝ :=
  ν (x 0) * ∏ i : Fin m, Q (x i.castSucc) (x i.succ)

/-- The vector of (G.23): coordinate `t < d` is `((1 − p★)² + (1 − p★ ± 16σ_iε) p★)/d` with the sign
of `η(σ)`, the last coordinate is `p★`. -/
noncomputable def statDist (d : ℕ) (p ε : ℝ) (σ : Fin (d / 2) → ℤˣ) (t : Fin (d + 1)) : ℝ :=
  if t = Fin.last d then p else ((1 - p) ^ 2 + (1 - p + 16 * hardSign σ t * ε) * p) / (d : ℝ)

/-- A controlled Markov chain realizes the hard chain `M_σ`: it has one control, its transition matrix
is `M_σ`, and `X_0` has law `b`. -/
def IsHardRealization {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (d : ℕ) (p ε : ℝ)
    (σ : Fin (d / 2) → ℤˣ) (C : CMC (d + 1) 1 μ) : Prop :=
  C.M 0 = hardMatrix d p ε σ ∧ ∀ t, μ.real {ω | C.X 0 ω = t} = baseRow d p t

end OfflineCMC.Minimax


