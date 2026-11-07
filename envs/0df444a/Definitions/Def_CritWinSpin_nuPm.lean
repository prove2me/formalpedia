-- Prove2me | Definitions.Def_CritWinSpin_nuPm
-- name    : CritWinSpin_nuPm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:42:33.974194+00:00
-- url     : https://prove2.me/theorems/64510a95-2764-4b15-bafd-962ba23a2d84
-- title:
--   Cloud laws $\nu_\pm$, discrepancy $D_y$, typical event $G_y$, acceptance $a_y$, the lift $(\tilde J,\tilde h)$
-- statement:
--   Replace each binary spin by a cloud $\sigma_i\in A^r$ with sum $M_i=\sum_\alpha\sigma_{i,\alpha}$. For $\beta=\tau+\theta$ put $w_r(\sigma_i)=\rho^{\otimes r}(\sigma_i)\exp(\frac{\beta}{2r}M_i^2)$ and
--   $$\nu_\pm(\sigma_i)=\frac{w_r(\sigma_i)}{Z_+}\Bigl(1_{\{\pm M_i>0\}}+\tfrac121_{\{M_i=0\}}\Bigr),\qquad Z_+=\sum_{\sigma_i}w_r(\sigma_i)\Bigl(1_{\{M_i>0\}}+\tfrac121_{\{M_i=0\}}\Bigr),$$
--   with $\nu_y=\prod_i\nu_{y_i}$. Further $\xi_i=|M_i|/(r\hat u)-1$, $t(\sigma)=\#\{i:M_i=0\}$, $D_y(\sigma)=H(M/(r\hat u))-H(y)$, $G_y=\{t(\sigma)=0,|D_y(\sigma)|\le1\}$ and $a_y=e^{D_y-1}1_{G_y}$. The **lift** of $H$ is
--   $$\tilde J=\Bigl(\beta I_n+\frac{J_0}{r\hat u^2}\Bigr)\otimes P_r,\quad P_r=\tfrac1r1_r1_r^\top,\qquad\tilde h_{i,\alpha}=\frac{(h_0)_i}{r\hat u}.$$
--   The parameters of (36) are $r=n^{pC}$ and $\theta=n^{A-(p-1)C}$ with integers satisfying $Ap/(p-1)>2w+4$, $(p-1)C>A+1$, $\varepsilon(1+pC)>A+d_p+1$. The approximation $\hat u$ satisfies (28): $|\hat u-u|\le r^{-3}$, $u/2\le\hat u\le2u$ for the solution $u\in(0,1)$ of $u=\phi'(\beta u)$. The module also defines the ideal rejection step (draw $\sigma\sim\nu_y$, accept with probability $a_y(\sigma)$).
--
--   **Formalization Note** The paper's $\hat u$ is dyadic; the bounds (28) are what the theorems use, and every dyadic choice is a rational one. `liftInst` reindexes $[n]\times[r]$ to $[N]$, $N=nr$.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), §6.1, pp.20–21, eqs. (28)–(30); §6.2, pp.22, 24, eq. (36)

import Mathlib
import Definitions.Def_CritWinSpin_encInst
import Definitions.Def_CritWinSpin_BinarySource
set_option autoImplicit false

namespace CritWinSpin

/-- The cloud sum `M = ∑_α τ_α` of a single cloud `τ ∈ A^r`, §6.1, p.20. -/
noncomputable def oneSum {S : SpinLaw} {r : ℕ} (τ : Config S (Fin r)) : ℝ := ∑ α, spinVal τ α

/-- The mean-field cloud weight `w_r(τ) = ρ^{⊗r}(τ) exp(β M² / (2r))`, §6.1, p.20. -/
noncomputable def cloudWeight (S : SpinLaw) (β : ℝ) {r : ℕ} (τ : Config S (Fin r)) : ℝ :=
  prodRho S τ * Real.exp (β / (2 * (r : ℝ)) * oneSum τ ^ 2)

/-- `Z_+ = ∑_τ w_r(τ) (1{M > 0} + ½ 1{M = 0})`, §6.1, p.20. -/
noncomputable def zPlus (S : SpinLaw) (β : ℝ) (r : ℕ) : ℝ :=
  ∑ τ : Config S (Fin r), cloudWeight S β τ *
    ((if 0 < oneSum τ then (1 : ℝ) else 0) + (1 / 2) * (if oneSum τ = 0 then (1 : ℝ) else 0))

/-- **The single-cloud laws** `ν_±(τ) = (w_r(τ)/Z_+) (1{±M > 0} + ½ 1{M = 0})`, §6.1, p.20
(Liu–Zhang–Ren, STOC 2027 submission, manuscript sha256 f77584da…). `s = true` is `ν_+`. -/
noncomputable def nuPm (S : SpinLaw) (β : ℝ) {r : ℕ} (s : Bool) (τ : Config S (Fin r)) : ℝ :=
  cloudWeight S β τ / zPlus S β r *
    ((if 0 < spinOf s * oneSum τ then (1 : ℝ) else 0) + (1 / 2) * (if oneSum τ = 0 then (1 : ℝ) else 0))

/-- The `i`-th cloud of `σ ∈ A^{[n]×[r]} = (A^r)^n`. -/
def slice {S : SpinLaw} {n r : ℕ} (σ : Config S (Fin n × Fin r)) (i : Fin n) : Config S (Fin r) :=
  fun α => σ (i, α)

/-- The cloud sums `M_i` of `σ` (§6.1, p.21). -/
noncomputable def cloudSum {S : SpinLaw} {n r : ℕ} (σ : Config S (Fin n × Fin r)) (i : Fin n) : ℝ :=
  oneSum (slice σ i)

/-- `ν_y(σ) = ∏_i ν_{y_i}(σ_i)`, §6.1, p.21. -/
noncomputable def nuProd (S : SpinLaw) (β : ℝ) {n r : ℕ} (y : BinCfg n)
    (σ : Config S (Fin n × Fin r)) : ℝ :=
  ∏ i, nuPm S β (y i) (slice σ i)

/-- The number `t(σ)` of tied clouds, §6.1, p.21. -/
noncomputable def tiedCount {S : SpinLaw} {n r : ℕ} (σ : Config S (Fin n × Fin r)) : ℕ :=
  open Classical in (Finset.univ.filter fun i => cloudSum σ i = 0).card

/-- The relative deviation `ξ_i = |M_i| / (r û) − 1`, §6.1, p.21. -/
noncomputable def xi {S : SpinLaw} {n r : ℕ} (û : ℝ) (σ : Config S (Fin n × Fin r)) (i : Fin n) : ℝ :=
  |cloudSum σ i| / ((r : ℝ) * û) - 1

/-- The energy discrepancy `D_y(σ) = H(M/(r û)) − H(y)`, §6.1, p.21. -/
noncomputable def Dy {S : SpinLaw} {n r : ℕ} (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (û : ℝ)
    (y : BinCfg n) (σ : Config S (Fin n × Fin r)) : ℝ :=
  energy J₀ h₀ (fun i => cloudSum σ i / ((r : ℝ) * û)) - energy J₀ h₀ (binVec y)

/-- The typical event `G_y = {σ : t(σ) = 0, |D_y(σ)| ≤ 1}`, §6.2, p.22. -/
def InGy {S : SpinLaw} {n r : ℕ} (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (û : ℝ)
    (y : BinCfg n) (σ : Config S (Fin n × Fin r)) : Prop :=
  tiedCount σ = 0 ∧ |Dy J₀ h₀ û y σ| ≤ 1

/-- The truncated acceptance probability `a_y(σ) = e^{D_y(σ)−1} 1_{G_y}(σ)`, §6.2, p.22. -/
noncomputable def ay {S : SpinLaw} {n r : ℕ} (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (û : ℝ)
    (y : BinCfg n) (σ : Config S (Fin n × Fin r)) : ℝ :=
  open Classical in if InGy J₀ h₀ û y σ then Real.exp (Dy J₀ h₀ û y σ - 1) else 0

/-- The ideal rejection step of `L̂_{T,k}` on input `y` (p.24, steps 1–2, with exact draws from `ν_y`):
output `σ` with probability `ν_y(σ) a_y(σ)`, and `⊥` otherwise. -/
noncomputable def idealSlot (S : SpinLaw) (β : ℝ) {n r : ℕ} (J₀ : Matrix (Fin n) (Fin n) ℝ)
    (h₀ : Fin n → ℝ) (û : ℝ) (y : BinCfg n) : Option (Config S (Fin n × Fin r)) → ℝ
  | none => 1 - ∑ σ : Config S (Fin n × Fin r), nuProd S β y σ * ay J₀ h₀ û y σ
  | some σ => nuProd S β y σ * ay J₀ h₀ û y σ

/-- The lifted interaction `J̃ = (β I_n + J₀/(r û²)) ⊗ P_r` with `P_r = (1/r) 1_r 1_rᵀ`, eq. (30), p.21,
on the index set `[n] × [r]`. -/
def liftJ {K : Type} [Field K] {n : ℕ} (r : ℕ) (β û : K) (J₀ : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n × Fin r) (Fin n × Fin r) K :=
  Matrix.of fun a b =>
    ((if a.1 = b.1 then β else 0) + J₀ a.1 b.1 / ((r : K) * û ^ 2)) * (1 / (r : K))

/-- The lifted field `h̃_{i,α} = (h₀)_i / (r û)`, eq. (30), p.21. -/
def liftH {K : Type} [Field K] {n : ℕ} (r : ℕ) (û : K) (h₀ : Fin n → K) : Fin n × Fin r → K :=
  fun a => h₀ a.1 / ((r : K) * û)

/-- The cloud size `r = n^{pC}` of (36), p.24. -/
def cloudSize (p Cc n : ℕ) : ℕ := n ^ (p * Cc)

/-- The shift `θ = n^{A − (p−1)C}` of (36), p.24 (a rational number, for `n ≥ 1`). -/
noncomputable def thetaQ (p Ac Cc n : ℕ) : ℚ := (n : ℚ) ^ ((Ac : ℤ) - ((p : ℤ) - 1) * (Cc : ℤ))

/-- The inequalities on the integers `A, C` of (36), p.24. -/
def GadgetParams (p : ℕ) (w ε : ℝ) (Ac Cc : ℕ) : Prop :=
  (Ac : ℝ) * p / ((p : ℝ) - 1) > 2 * w + 4 ∧
  ((p : ℝ) - 1) * (Cc : ℝ) > (Ac : ℝ) + 1 ∧
  ε * (1 + (p : ℝ) * (Cc : ℝ)) > (Ac : ℝ) + dExp p + 1

/-- The condition (28), p.20, on a rational `û`, for the given shift `θ` and cloud size `r`: there is
`u ∈ (0,1)` with `u = ϕ'(βu)`, `β = τ + θ`, and `|û − u| ≤ r^{−3}`, `u/2 ≤ û ≤ 2u`.

**Formalization Note.** The paper asks for a dyadic `û`; the theorems hold for every rational `û` with
these bounds, and a machine may choose a dyadic one. -/
def IsUhat (S : SpinLaw) (θ : ℝ) (r : ℕ) (û : ℚ) : Prop :=
  ∃ u : ℝ, 0 < u ∧ u < 1 ∧ u = deriv (phi S) ((tau S + θ) * u) ∧
    |(û : ℝ) - u| ≤ 1 / (r : ℝ) ^ 3 ∧ u / 2 ≤ (û : ℝ) ∧ (û : ℝ) ≤ 2 * u

/-- The lifted rational interaction `J̃` of (30) and (36) on `[n] × [r]`. -/
noncomputable def liftJQ (S : SpinLaw) (p Ac Cc : ℕ) {n : ℕ} (H : Inst n) (û : ℚ) :
    Matrix (Fin n × Fin (cloudSize p Cc n)) (Fin n × Fin (cloudSize p Cc n)) ℚ :=
  liftJ (cloudSize p Cc n) (tauQ S + thetaQ p Ac Cc n) û H.1

/-- The lifted rational field `h̃` of (30) and (36) on `[n] × [r]`. -/
def liftHQ (p Cc : ℕ) {n : ℕ} (H : Inst n) (û : ℚ) : Fin n × Fin (cloudSize p Cc n) → ℚ :=
  liftH (cloudSize p Cc n) û H.2

/-- **The lifted rational model** `(J̃, h̃)` on `N = nr` sites of (30) and (36), pp.21, 24, reindexed
from `[n] × [r]` to `[N]` (Liu–Zhang–Ren, STOC 2027 submission, manuscript sha256 f77584da…). -/
noncomputable def liftInst (S : SpinLaw) (p Ac Cc : ℕ) {n : ℕ} (H : Inst n) (û : ℚ) :
    Inst (n * cloudSize p Cc n) :=
  (Matrix.reindex finProdFinEquiv finProdFinEquiv (liftJQ S p Ac Cc H û),
    fun a => liftHQ p Cc H û (finProdFinEquiv.symm a))

end CritWinSpin


