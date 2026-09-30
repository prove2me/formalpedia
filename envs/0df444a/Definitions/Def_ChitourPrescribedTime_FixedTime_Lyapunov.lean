-- Prove2me | Definitions.Def_ChitourPrescribedTime_FixedTime_Lyapunov
-- name    : ChitourPrescribedTime_FixedTime_Lyapunov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:06:06.171517+00:00
-- url     : https://prove2.me/theorems/4585f652-295a-487f-bb83-94a475257467
-- title:
--   The homogeneous Lyapunov function $V_\kappa$ (35), (37) and the decay inequality (36)
-- statement:
--   With the notation of Definition 23 (weights $r_j$, exponents $\beta_j$, virtual controls $v_j$), set for $1\le j\le n$
--   $$W_{\kappa,j}(x)=\frac{|x_j|^{\beta_{j-1}+1}-|v_{j-1}|^{\beta_{j-1}+1}}{\beta_{j-1}+1}-\lceil v_{j-1}\rfloor^{\beta_{j-1}}\,(x_j-v_{j-1}),$$
--   which is the closed form (37) of $\int_{v_{j-1}}^{x_j}\big(\lceil s\rfloor^{\beta_{j-1}}-\lceil v_{j-1}\rfloor^{\beta_{j-1}}\big)\,ds$, and
--   $$V_\kappa(x)=\sum_{j=1}^n W_{\kappa,j}(x)$$
--   as in (35). For $n=1$ this is $V_\kappa(x)=|x_1|^{2+\kappa}/(2+\kappa)$. Also set $\alpha(\kappa):=\kappa/(2+\kappa)$.
--
--   Given gains $\ell$ and a constant $C$, the **decay inequality (36)** is the requirement that, for every $\kappa\in[-\tfrac1{2n},\tfrac1{2n}]$ and every $x\in\mathbb R^n$,
--   $$\dot V_\kappa(x):=DV_\kappa(x)\big[J_nx+\omega^H_\kappa(x)e_n\big]\le -C\,V_\kappa(x)^{1+\alpha(\kappa)},$$
--   with one constant $C$ for all $\kappa$ in that range.
--
--   The constant $C$ of (36) enters the settling-time bound (52); every theorem of this mission that uses it takes the gains and $C$ as data satisfying (36).
--
--   **Formalization Note** `lyapW ℓ κ x j` is $W_{\kappa,j+1}$ (0-based $j$), `lyapV` is $V_\kappa$, `alpha` is $\alpha$, and `Decay36 ℓ C` is (36), with $\dot V_\kappa$ the Fréchet derivative `fderiv` of $V_\kappa$ applied to the closed-loop vector field. (37) prints $\beta_{i-1}$ in the prefactor, a slip for $\beta_{j-1}$.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1034, Proposition 24, eqs. (35)–(36), and the proof, eqs. (37)–(38)

import Mathlib
import Definitions.Def_ChitourPrescribedTime_FixedTime_PureChain
import Definitions.Def_ChitourPrescribedTime_FixedTime_Feedback

namespace ChitourPrescribedTime.FixedTime

/-- The summand `W_{κ,j}` of (37), in closed form, for the 0-based index `j` (the paper's
`j + 1`): with `β = β_j`, `v = v_j(x)` and `x_{j+1}` the `(j+1)`-th coordinate,
`W = (|x_{j+1}|^{β+1} - |v|^{β+1}) / (β + 1) - ⌈v⌋^β (x_{j+1} - v)`. -/
noncomputable def lyapW {n : ℕ} (ℓ : Fin n → ℝ) (κ : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (j : ℕ) : ℝ :=
  (|coord x j| ^ (beta κ j + 1) - |vSeq ℓ κ x j| ^ (beta κ j + 1)) / (beta κ j + 1)
    - sgnPow (vSeq ℓ κ x j) (beta κ j) * (coord x j - vSeq ℓ κ x j)

/-- The Lyapunov function (35): `V_κ(x) = Σ_{j=1}^n W_{κ,j}(x)`. -/
noncomputable def lyapV {n : ℕ} (ℓ : Fin n → ℝ) (κ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ j ∈ Finset.range n, lyapW ℓ κ x j

/-- The exponent `α(κ) := κ / (2 + κ)` of (36). -/
noncomputable def alpha (κ : ℝ) : ℝ := κ / (2 + κ)

/-- The differential inequality (36), `V̇_κ ≤ -C V_κ^{1+α(κ)}` along the closed loop
`ẋ = J_n x + ω^H_κ(x) e_n`, for every `κ ∈ [-1/(2n), 1/(2n)]` with one constant `C`
(independent of `κ`); `V̇_κ(x)` is the Fréchet derivative of `V_κ` at `x` applied to the
vector field. -/
def Decay36 {n : ℕ} (ℓ : Fin n → ℝ) (C : ℝ) : Prop :=
  ∀ κ ∈ Set.Icc (-(1 / (2 * (n : ℝ)))) (1 / (2 * (n : ℝ))),
    ∀ x : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (lyapV ℓ κ) x (chainField n x (omegaH ℓ κ x)) ≤
        -C * lyapV ℓ κ x ^ (1 + alpha κ)

end ChitourPrescribedTime.FixedTime


