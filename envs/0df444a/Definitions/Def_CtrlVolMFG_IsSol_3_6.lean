-- Prove2me | Definitions.Def_CtrlVolMFG_IsSol_3_6
-- name    : CtrlVolMFG_IsSol_3_6
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:23:35.814324+00:00
-- url     : https://prove2.me/theorems/417d5f27-ccb8-40ac-becb-e56977d324d8
-- title:
--   The open-loop adjoint system (3.2′), the conditional McKean–Vlasov FBSDE (3.6), and the error terms of Proposition 3.16
-- statement:
--   **The system (3.2′).** For the controls $\boldsymbol\alpha^N$ of an $N$-player game with states $\mathbf X$, player $i$'s Hamiltonian is
--   $$\mathcal H^i(\mathbf x)=\sum_k\big[b(x^k,\alpha^k,m^N_{\mathbf x})\cdot Y^{i,k}+\sigma(x^k,\alpha^k,m^N_{\mathbf x})\cdot Z^{i,k,k}+\sigma^0(x^k,\alpha^k,m^N_{\mathbf x})\cdot Z^{i,k,0}\big]+L(x^i,\alpha^i,m^N_{\mathbf x}).$$
--   A solution of (3.2′) consists of the states, adjoints $Y^{i,j}\in\mathbb R^n$ and integrands $Z^{i,j,l}\in\mathbb R^{n\times d}$ ($i,j\le N$, $0\le l\le N$) with
--   $$dY^{i,j}_t=-\partial_{x^j}\mathcal H^i(\mathbf X_t)dt+\sum_{l=0}^NZ^{i,j,l}_tdW^l_t,\qquad Y^{i,j}_T=\delta_{ij}D_xG(X^i_T,m^N_{\mathbf X_T})+\tfrac1ND_mG(X^i_T,m^N_{\mathbf X_T},X^j_T),$$
--   where $\partial_{x^j}\mathcal H^i=D_xb(X^j,\alpha^j,m)^\top Y^{i,j}+D_x\sigma(\dots)^\top Z^{i,j,j}+D_x\sigma^0(\dots)^\top Z^{i,j,0}+\delta_{ij}D_xL(X^i,\alpha^i,m)+\frac1N\sum_k[D_mb(X^k,\alpha^k,m,X^j)^\top Y^{i,k}+D_m\sigma(\dots)^\top Z^{i,k,k}+D_m\sigma^0(\dots)^\top Z^{i,k,0}]+\frac1ND_mL(X^i,\alpha^i,m,X^j)$, together with continuity, progressive measurability and the integrability (3.3). When $b,\sigma,\sigma^0$ do not depend on $m$, the equations for $Y^{i,i}$ are those of $Y^{N,i}$ in (3.2).
--
--   **The FBSDE (3.6).** With $m_t$ a version of $\mathcal L(X_t\mid\mathcal F^0_t)$,
--   $$dX_t=D_yH(\Theta_t)dt+D_zH(\Theta_t)dW_t+D_{z^0}H(\Theta_t)dW^0_t,\quad dY_t=-D_xH(\Theta_t)dt+Z_tdW_t+Z^0_tdW^0_t,\quad X_0=\xi,\ Y_T=D_xG(X_T,m_T),$$
--   $\Theta_t=(X_t,Y_t,Z_t,Z^0_t,m_t)$, with $X,Y$ continuous adapted, $Z,Z^0$ progressive and (3.7).
--
--   **Error terms (p.34).** For copies $(X^i,Y^i,Z^i,Z^{i,0})$ of a solution of (3.6), $\bar m^N_t=\frac1N\sum_i\delta_{X^i_t}$, $\bar m_t=\mathcal L(X^i_t\mid\mathcal F^0_t)$: $E^{b,i}_t=D_yH(\cdot,\bar m^N_t)-D_yH(\cdot,\bar m_t)$, $E^{\sigma,i}$, $E^{\sigma^0,i}$ likewise with $D_zH$, $D_{z^0}H$, $E^{L,i}_t=\frac1ND_mH(\cdot,\bar m^N_t,X^i_t)+D_xH(\cdot,\bar m^N_t)-D_xH(\cdot,\bar m_t)$, $E^{G,i}=\frac1ND_mG(X^i_T,\bar m^N_T,X^i_T)+D_xG(X^i_T,\bar m^N_T)-D_xG(X^i_T,\bar m_T)$, and the expectation $\mathbb E[\int_0^T\sum_i(|E^{b,i}_t|^2+|E^{\sigma,i}_t|^2+|E^{\sigma^0,i}_t|^2+|E^{L,i}_t|^2)dt+\sum_i|E^{G,i}|^2]$.
--
--   **Formalization Note** (3.2′) replaces the printed (3.2), which omits the cross terms through the measure argument (see the item `lemma_3_2`). In (3.6) the coefficients $D_yH,D_zH,D_{z^0}H,D_xH$ are written through the minimizer, $b(x,\hat\alpha,m)$, $\sigma(x,\hat\alpha,m)$, $\sigma^0(x,\hat\alpha,m)$, $D_x[b\cdot y+\sigma\cdot z+\sigma^0\cdot z^0](x,\hat\alpha,m)+D_xL(x,\hat\alpha,m)$: equal wherever $H$ is differentiable, in particular under Assumption 2.17, and the form of (3.9), (3.10) in the other two cases. Backward equations are written as Itô processes from their initial value with an a.s. terminal condition. In the error terms $\bar m_t$ is $m_t$, the conditional law of every copy.
-- source:
--   Jackson & Tangpi, Quantitative Convergence for Displacement Monotone Mean Field Games with Controlled Volatility, arXiv:2304.04543v2, (3.2), (3.3) p.19; (3.6), (3.7) p.20; Proposition 3.16 p.34

import Mathlib
import Definitions.Def_CtrlVolMFG_Assumption_3_1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CtrlVolMFG

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n k d : ℕ}

/-- The gradient in `x` of the dynamics part of the function (3.1),
`x ↦ b(x, a, m)·y + σ(x, a, m)·z + σ⁰(x, a, m)·z⁰`, i.e. `D_xb(x, a, m)ᵀy + D_xσ(x, a, m)ᵀz +
D_xσ⁰(x, a, m)ᵀz⁰` (the terms `B₂ᵀY + Σ₂ᵀZ + (Σ⁰₂)ᵀZ⁰` of (3.5), p.20). -/
noncomputable def DxDyn (D : Data n k d) (x : Rn n) (a : Rn k) (y : Rn n) (z z0 : Mat n d)
    (m : P2 n) : Rn n :=
  gradient (fun x' => inner ℝ (D.b x' a m) y + inner ℝ (D.σ x' a m) z +
    inner ℝ (D.σ0 x' a m) z0) x

/-- The Lions derivative at the point `p` of the dynamics part of (3.1),
`D_mb(x, a, m, p)ᵀy + D_mσ(x, a, m, p)ᵀz + D_mσ⁰(x, a, m, p)ᵀz⁰` (adjoints of the versions `V`). -/
noncomputable def DmDyn (V : Derivs n k d) (x : Rn n) (a : Rn k) (y : Rn n) (z z0 : Mat n d)
    (m : P2 n) (p : Rn n) : Rn n :=
  ContinuousLinearMap.adjoint (V.Dmb x a m p) y + ContinuousLinearMap.adjoint (V.Dmσ x a m p) z +
    ContinuousLinearMap.adjoint (V.Dmσ0 x a m p) z0

/-- `∂_{xʲ}𝓗ⁱ`, the gradient in the state `xʲ` of player `j` of player `i`'s Hamiltonian
`𝓗ⁱ(x) = ∑ₖ [b(xᵏ, αᵏ, m^N_x)·Y^{i,k} + σ(xᵏ, αᵏ, m^N_x)·Z^{i,k,k} + σ⁰(xᵏ, αᵏ, m^N_x)·Z^{i,k,0}]
 + L(xⁱ, αⁱ, m^N_x)`, at `x = X_t`, `m = m^N_{X_t}`:
`D_xb(Xʲ, αʲ, m)ᵀY^{i,j} + D_xσ(…)ᵀZ^{i,j,j} + D_xσ⁰(…)ᵀZ^{i,j,0} + δ_{ij} D_xL(Xⁱ, αⁱ, m)
 + (1/N) ∑ₖ [D_mb(Xᵏ, αᵏ, m, Xʲ)ᵀY^{i,k} + D_mσ(…)ᵀZ^{i,k,k} + D_mσ⁰(…)ᵀZ^{i,k,0}]
 + (1/N) D_mL(Xⁱ, αⁱ, m, Xʲ)`.
`Z i j none` is the integrand `Z^{i,j,0}` against `W⁰` and `Z i j (some l)` the one against
`W^{l}` (players indexed from `0`). -/
noncomputable def adjDrift (D : Data n k d) (V : Derivs n k d) {N : ℕ}
    (α : Fin N → ℝ≥0 → Ω → Rn k) (X : Fin N → ℝ≥0 → Ω → Rn n)
    (Y : Fin N → Fin N → ℝ≥0 → Ω → Rn n) (Z : Fin N → Fin N → Option (Fin N) → ℝ≥0 → Ω → Mat n d)
    (i j : Fin N) (t : ℝ≥0) (ω : Ω) : Rn n :=
  DxDyn D (X j t ω) (α j t ω) (Y i j t ω) (Z i j (some j) t ω) (Z i j none t ω)
      (empP2 fun l => X l t ω) +
    (if i = j then D.DxL (X i t ω) (α i t ω) (empP2 fun l => X l t ω) else 0) +
    (1 / (N : ℝ)) • ∑ l : Fin N, DmDyn V (X l t ω) (α l t ω) (Y i l t ω) (Z i l (some l) t ω)
      (Z i l none t ω) (empP2 fun l' => X l' t ω) (X j t ω) +
    (1 / (N : ℝ)) • V.DmL (X i t ω) (α i t ω) (empP2 fun l => X l t ω) (X j t ω)

/-- A solution of the open-loop adjoint system (3.2′) of the `N`-player game for the controls `α`
(the corrected form of (3.2), Jackson & Tangpi, arXiv:2304.04543v2, p.19): for
`i, j ∈ {1, …, N}`, `l ∈ {0, …, N}`,
1. `X` solves the state equations (2.3) driven by `α`;
2. `dY^{i,j}_t = −∂_{xʲ}𝓗ⁱ_t dt + ∑_{l=0}^N Z^{i,j,l}_t dWˡ_t` (`adjDrift`), with
   `Y^{i,j}_T = δ_{ij} D_xG(Xⁱ_T, m^N_{X_T}) + (1/N) D_mG(Xⁱ_T, m^N_{X_T}, Xʲ_T)`;
3. `X, Y` are continuous and `𝔽ᴺ`-adapted, each `Z^{i,j,l}` is `𝔽ᴺ`-progressive and
   `ℝ^{n×d}`-valued, and the integrability condition (3.3) holds.

When `b, σ, σ⁰` do not depend on `m`, the equations for `Y^{i,i}` are those of `Y^{N,i}` in (3.2).

**Formalization Note** The backward equations are written in forward form from the random
initial value `Y^{i,j}_0` together with the terminal condition, which is the integral form of a
BSDE. -/
def IsSol_3_2c (S : Setup n d Ω) (D : Data n k d) (V : Derivs n k d) (T : ℝ≥0) (N : ℕ)
    (α : Fin N → ℝ≥0 → Ω → Rn k) (X : Fin N → ℝ≥0 → Ω → Rn n)
    (Y : Fin N → Fin N → ℝ≥0 → Ω → Rn n)
    (Z : Fin N → Fin N → Option (Fin N) → ℝ≥0 → Ω → Mat n d) : Prop :=
  StateEqN S D T N α X ∧
    (∀ i j, IsItoProc (S.filtN N) S.P T (S.noiseAll N) (Y i j 0)
      (fun t ω => -adjDrift D V α X Y Z i j t ω)
      (fun q t ω => col (Z i j q.1 t ω) q.2) (Y i j)) ∧
    (∀ i j, ∀ᵐ ω ∂S.P, Y i j T ω =
      (if i = j then D.DxG (X i T ω) (empP2 fun l => X l T ω) else 0) +
        (1 / (N : ℝ)) • V.DmG (X i T ω) (empP2 fun l => X l T ω) (X j T ω)) ∧
    (∀ i j l, IsStronglyProgressive (S.filtN N) (Z i j l)) ∧
    ∀ i j l, ∫⁻ ω, ((⨆ t ∈ Set.Icc 0 T, (‖X i t ω‖ₑ ^ 2 + ‖Y i j t ω‖ₑ ^ 2)) +
      ∫⁻ s in Set.Icc (0 : ℝ) T, ‖Z i j l s.toNNReal ω‖ₑ ^ 2) ∂S.P < ⊤

/-- A solution `(X, Y, Z, Z⁰)` of the conditional McKean–Vlasov FBSDE (3.6), p.20
(arXiv:2304.04543v2), where `m` is a version of `t ↦ ℒ(X_t | ℱ⁰_t)` on `[0, T]` and
`α̂_t = α̂(X_t, Y_t, Z_t, Z⁰_t, m_t)`:
1. `dX_t = b(X_t, α̂_t, m_t)dt + σ(X_t, α̂_t, m_t)dW_t + σ⁰(X_t, α̂_t, m_t)dW⁰_t`, `X₀ = ξ`;
2. `dY_t = −(D_xb(…)ᵀY_t + D_xσ(…)ᵀZ_t + D_xσ⁰(…)ᵀZ⁰_t + D_xL(X_t, α̂_t, m_t))dt + Z_t dW_t + Z⁰_t dW⁰_t`,
   `Y_T = D_xG(X_T, m_T)`;
3. `X, Y` continuous and `𝔽`-adapted, `Z, Z⁰` `𝔽`-progressive, and (3.7)
   `𝔼[sup_{0≤t≤T}(|X_t|² + |Y_t|²) + ∫₀ᵀ(|Z_t|² + |Z⁰_t|²)dt] < ∞`.

**Formalization Note** The coefficients `D_yH, D_zH, D_{z⁰}H, D_xH` of (3.6) are written through
the minimizer: `D_yH(x, y, z, z⁰, m) = b(x, α̂, m)`, `D_zH = σ(x, α̂, m)`, `D_{z⁰}H = σ⁰(x, α̂, m)`,
`D_xH = D_xb(x, α̂, m)ᵀy + D_xσ(…)ᵀz + D_xσ⁰(…)ᵀz⁰ + D_xL(x, α̂, m)`, with `α̂ = α̂(x, y, z, z⁰, m)`.
These identities hold wherever `H` is differentiable (since `H ≤ ham(·, a, ·)` with equality at
`a = α̂`), in particular under Assumption 2.17; this is the form of (3.9), (3.10) under
Assumptions 2.4–2.5 and 2.11–2.12. -/
def IsSol_3_6 (S : Setup n d Ω) (D : Data n k d) (T : ℝ≥0) (m : ℝ≥0 → Ω → P2 n)
    (X Y : ℝ≥0 → Ω → Rn n) (Z Z0 : ℝ≥0 → Ω → Mat n d) : Prop :=
  (∀ t ∈ Set.Icc 0 T, IsCondLaw S X m t) ∧
    IsItoProc (S.filtN 1) S.P T (S.noise 0) (S.ξ 0)
      (fun t ω => D.b (X t ω) (D.alphaHat (X t ω) (Y t ω) (Z t ω) (Z0 t ω) (m t ω)) (m t ω))
      (Sum.elim
        (fun j t ω => col (D.σ (X t ω)
          (D.alphaHat (X t ω) (Y t ω) (Z t ω) (Z0 t ω) (m t ω)) (m t ω)) j)
        (fun j t ω => col (D.σ0 (X t ω)
          (D.alphaHat (X t ω) (Y t ω) (Z t ω) (Z0 t ω) (m t ω)) (m t ω)) j)) X ∧
    IsItoProc (S.filtN 1) S.P T (S.noise 0) (Y 0)
      (fun t ω => -(DxDyn D (X t ω) (D.alphaHat (X t ω) (Y t ω) (Z t ω) (Z0 t ω) (m t ω))
          (Y t ω) (Z t ω) (Z0 t ω) (m t ω) +
        D.DxL (X t ω) (D.alphaHat (X t ω) (Y t ω) (Z t ω) (Z0 t ω) (m t ω)) (m t ω)))
      (Sum.elim (fun j t ω => col (Z t ω) j) (fun j t ω => col (Z0 t ω) j)) Y ∧
    (∀ᵐ ω ∂S.P, Y T ω = D.DxG (X T ω) (m T ω)) ∧
    IsStronglyProgressive (S.filtN 1) Z ∧ IsStronglyProgressive (S.filtN 1) Z0 ∧
    ∫⁻ ω, ((⨆ t ∈ Set.Icc 0 T, (‖X t ω‖ₑ ^ 2 + ‖Y t ω‖ₑ ^ 2)) +
      ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z s.toNNReal ω‖ₑ ^ 2 + ‖Z0 s.toNNReal ω‖ₑ ^ 2)) ∂S.P < ⊤

/-! ### The error terms of Proposition 3.16 (arXiv:2304.04543v2, p.34)

They are evaluated at the copies `(Xⁱ, Yⁱ, Zⁱ, Z^{i,0})` (index `i - 1`) of a solution of (3.6),
with `m̄ᴺ_t = (1/N) ∑ᵢ δ_{Xⁱ_t}` and `m̄_t = ℒ(Xⁱ_t | ℱ⁰_t)`, which is `m_t` (the copies have the
conditional law of `X`, and `m_t = ℒ(X_t | ℱ⁰_t)`). -/

/-- `m̄ᴺ_t = (1/N) ∑_{i=1}^N δ_{Xⁱ_t}`, the empirical measure of the copies. -/
noncomputable def empCopies (N : ℕ) (Xc : ℕ → ℝ≥0 → Ω → Rn n) (t : ℝ≥0) (ω : Ω) : P2 n :=
  empP2 fun i : Fin N => Xc i t ω

/-- `|E^{b,i}_t|² + |E^{σ,i}_t|² + |E^{σ⁰,i}_t|² + |E^{L,i}_t|²` (p.34), where
`E^{b,i}_t = D_yH(Xⁱ_t, Yⁱ_t, Zⁱ_t, Z^{i,0}_t, m̄ᴺ_t) − D_yH(…, m̄_t)`, `E^{σ,i}` and `E^{σ⁰,i}` the
same with `D_zH`, `D_{z⁰}H`, and
`E^{L,i}_t = (1/N) D_mH(Xⁱ_t, Yⁱ_t, Zⁱ_t, Z^{i,0}_t, m̄ᴺ_t, Xⁱ_t) + D_xH(…, m̄ᴺ_t) − D_xH(…, m̄_t)`. -/
noncomputable def errRun (D : Data n k d) (V : Derivs n k d) (N : ℕ) (m : ℝ≥0 → Ω → P2 n)
    (Xc Yc : ℕ → ℝ≥0 → Ω → Rn n) (Zc Z0c : ℕ → ℝ≥0 → Ω → Mat n d) (i : ℕ) (t : ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  ‖D.DyH (Xc i t ω) (Yc i t ω) (Zc i t ω) (Z0c i t ω) (empCopies N Xc t ω) -
      D.DyH (Xc i t ω) (Yc i t ω) (Zc i t ω) (Z0c i t ω) (m t ω)‖ₑ ^ 2 +
    ‖D.DzH (Xc i t ω) (Yc i t ω) (Zc i t ω) (Z0c i t ω) (empCopies N Xc t ω) -
      D.DzH (Xc i t ω) (Yc i t ω) (Zc i t ω) (Z0c i t ω) (m t ω)‖ₑ ^ 2 +
    ‖D.Dz0H (Xc i t ω) (Yc i t ω) (Zc i t ω) (Z0c i t ω) (empCopies N Xc t ω) -
      D.Dz0H (Xc i t ω) (Yc i t ω) (Zc i t ω) (Z0c i t ω) (m t ω)‖ₑ ^ 2 +
    ‖(1 / (N : ℝ)) • V.DmH (Xc i t ω) (Yc i t ω) (Zc i t ω) (Z0c i t ω) (empCopies N Xc t ω)
        (Xc i t ω) +
      D.DxH (Xc i t ω) (Yc i t ω) (Zc i t ω) (Z0c i t ω) (empCopies N Xc t ω) -
      D.DxH (Xc i t ω) (Yc i t ω) (Zc i t ω) (Z0c i t ω) (m t ω)‖ₑ ^ 2

/-- `|E^{G,i}|²` (p.34), where
`E^{G,i} = (1/N) D_mG(Xⁱ_T, m̄ᴺ_T, Xⁱ_T) + D_xG(Xⁱ_T, m̄ᴺ_T) − D_xG(Xⁱ_T, m̄_T)`. -/
noncomputable def errTerm (D : Data n k d) (V : Derivs n k d) (N : ℕ) (T : ℝ≥0)
    (m : ℝ≥0 → Ω → P2 n) (Xc : ℕ → ℝ≥0 → Ω → Rn n) (i : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ‖(1 / (N : ℝ)) • V.DmG (Xc i T ω) (empCopies N Xc T ω) (Xc i T ω) +
      D.DxG (Xc i T ω) (empCopies N Xc T ω) - D.DxG (Xc i T ω) (m T ω)‖ₑ ^ 2

/-- The right-hand side expectation of Proposition 3.16 (p.34),
`𝔼[∫₀ᵀ ∑ᵢ (|E^{b,i}_t|² + |E^{σ,i}_t|² + |E^{σ⁰,i}_t|² + |E^{L,i}_t|²)dt + ∑ᵢ |E^{G,i}|²]`, the sums
over `i ∈ {1, …, N}`. -/
noncomputable def errSum (S : Setup n d Ω) (D : Data n k d) (V : Derivs n k d) (N : ℕ)
    (T : ℝ≥0) (m : ℝ≥0 → Ω → P2 n) (Xc Yc : ℕ → ℝ≥0 → Ω → Rn n)
    (Zc Z0c : ℕ → ℝ≥0 → Ω → Mat n d) : ℝ≥0∞ :=
  ∫⁻ ω, ((∫⁻ s in Set.Icc (0 : ℝ) T,
      ∑ i : Fin N, errRun D V N m Xc Yc Zc Z0c i s.toNNReal ω) +
    ∑ i : Fin N, errTerm D V N T m Xc i ω) ∂S.P

end CtrlVolMFG


