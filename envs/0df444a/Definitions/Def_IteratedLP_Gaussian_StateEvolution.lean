-- Prove2me | Definitions.Def_IteratedLP_Gaussian_StateEvolution
-- name    : IteratedLP_Gaussian_StateEvolution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:21:36.921679+00:00
-- url     : https://prove2.me/theorems/92b8d9d0-58f9-4569-bc3d-7350dc13d039
-- title:
--   Algorithm 2 — the state-evolution recursion for ITERATED-LP
-- statement:
--   **State.** Entering round $t=p+1$, the state consists of the free fraction $q=q_p$, the law $\pi^{\mathrm{col}}_p$ of the free-column history $(X,R)\in\mathbb R^p\times\mathbb R^p$, the law $\pi^{\mathrm{row}}_p$ of the row history $(U,\Lambda)\in\mathbb R^p\times\mathbb R^p$, and the law $\mu^{\mathrm{col}}_p$ of the full coordinate trajectory $\bar X\in[-1,1]^p$. It starts from $q_0=1$ and empty histories. $X_p$ is the last coordinate of $X$ and $e_p$ the last basis vector; at $t=1$ every term involving the histories is omitted.
--
--   1. **Moments.** $Q^x=\mathbb E[\bar X\bar X^\top]$, $Q^x_F=q\mathbb E[XX^\top]$, $Q^{rx}_F=q\mathbb E[RX^\top]$, $Q^\lambda=\alpha\mathbb E[\Lambda\Lambda^\top]$, $\Gamma=\alpha\mathbb E[\Lambda U^\top]$.
--   2. **Column value.** With $G\sim N(0,1)$ independent of the state and $\omega=(s,a,b)\in\mathbb R\times\mathbb R^p\times\mathbb R^p$,
--   $$\phi_t(\omega)=\sup\{q\mathbb E[GY]:Y\in[-1,1],\ q\mathbb EY^2=s,\ q\mathbb E[X(Y-X_p)]=a,\ q\mathbb E[R(Y-X_p)]=b\},$$
--   where $Y$ may depend on $(X,R,G)$ and on independent randomness.
--   3. **Row cost.** With $G_{\mathrm{row}}\sim N(0,1)$ independent, $\rho_\omega^2=s-(Q^x_F)_{pp}-2e_p^\top a-a^\top(Q^x)^{-1}a$,
--   $$Z_\omega=(e_p+(Q^x)^{-1}a)^\top U+\big((Q^\lambda)^{-1}(b-\Gamma(Q^x)^{-1}a)\big)^\top\Lambda+\rho_\omega G_{\mathrm{row}},$$
--   $$d_t(\omega)^2=\alpha\min\{\mathbb E(\tilde U-Z_\omega)^2:\tilde U\ge\kappa_t,\ \alpha\mathbb E[\Lambda\tilde U]=\Gamma e_p+b\}.$$
--   4. **Value.** $\omega$ is admissible if $\rho_\omega^2\ge0$ and the sets in Steps 2 and 3 are nonempty. $V_t=\max\{\sqrt{\phi_t(\omega)^2-d_t(\omega)^2}:\omega\text{ admissible},\ \phi_t(\omega)\ge d_t(\omega)\}$, $\omega^\star_t=(s^\star_t,a^\star_t,b^\star_t)$ the maximizer, $\gamma_t=d_t(\omega^\star_t)/V_t$.
--   5. **Coefficients.** $(\tau_t,\eta_{x,t},\eta_{r,t})$ minimizes $\frac{\tau s^\star_t}2-\eta_x^\top(Q^x_Fe_p+a^\star_t)-\eta_r^\top(Q^{rx}_Fe_p+b^\star_t)+q\mathbb E\,\ell(G+\eta_x^\top X+\eta_r^\top R;\tau)$ with $\ell(z;\tau)=\max_{|y|\le1}\{zy-\tau y^2/2\}$; $\eta_{\lambda,t}$ is the multiplier for which $U_t=\max\{\kappa_t,Z_t-\eta_{\lambda,t}^\top\Lambda\}$, $Z_t=Z_{\omega^\star_t}$, satisfies $\alpha\mathbb E[\Lambda U_t]=\Gamma e_p+b^\star_t$.
--   6. **Update.** With $V\sim N(0,1)$ independent of $G$, $G_{\mathrm{row}}$ and the state: $S_t=(V+\gamma_tG)/\sqrt{1+\gamma_t^2}$, $Y_t=\max\{-1,\min\{1,(S_t+\eta_{x,t}^\top X+\eta_{r,t}^\top R)/\tau_t\}\}$, $\Lambda_t=(\kappa_t-Z_t+\eta_{\lambda,t}^\top\Lambda)_+/V_t$.
--   7. **New state.** $q_t=q\,\mathbb P(|Y_t|<1)$; $\pi^{\mathrm{col}}_t=\mathrm{Law}((X,Y_t),(R,-V)\mid|Y_t|<1)$; $\pi^{\mathrm{row}}_t=\mathrm{Law}((U,U_t),(\Lambda,\Lambda_t))$;
--   $$\mu^{\mathrm{col}}_t(\cdot)=\mathbb P\big((\bar X,\bar X_p)\in\cdot,\ |\bar X_p|=1\big)+q\,\mathbb P\big((X,Y_t)\in\cdot\big),$$
--   the first term omitted at $t=1$.
--
--   **Output:** $q_t$, $\mu^{\mathrm{col}}_t$ and $\mu^{\mathrm{row}}_t=\mathrm{Law}(U_1,\dots,U_t)$ for $t\le K$. The same objects ($\phi_t$, $d_t$, $\Psi_t$, the column dual, the row multiplier) define the population problem of §6.2 for a general input.
--
--   **Formalization Note.** A state is a `PopState p` (a real `q` and three measures on `RVec p`-spaces). Randomized suprema and minima are over **joint laws**: `colCouplings` are laws of $(((X,R),G),Y)$ with $((X,R),G)$-marginal $\pi^{\mathrm{col}}_p\otimes N(0,1)$, and `rowCouplings` laws of $(((U,\Lambda),G_{\mathrm{row}}),\tilde U)$ with $((U,\Lambda),G_{\mathrm{row}})$-marginal $\pi^{\mathrm{row}}_p\otimes N(0,1)$, $\tilde U\in L^2$; extra randomization does not lower the row minimum (conditional expectation), and the minimum is an infimum that is attained. `Psi` is $\sqrt{\phi_t^2-d_t^2}$ on admissible $\omega$ with $\phi_t\ge d_t$ and $\bot=-\infty$ otherwise (eq. (6.17)). Since Algorithm 2 makes choices ("the maximizer", a dual minimizer, "the multiplier"), one round is the relation `IsStep`: the next state is `stepOutput` for **some** valid choice; `IsStateEvolution α K κ S` says `S 0` is the empty state and every round $p+1\le K$ is a step with margin `κ ⟨p, _⟩`. Matrix inverses are Mathlib's (`0` for a singular matrix; the paper proves $Q^x,Q^\lambda\succ0$ along the recursion). At $p=0$, `lastE`, `lastV`, `lastDiag`, `lastCol` are $0$/empty, which implements the empty-history conventions of §4.2, and the frozen term of $\mu^{\mathrm{col}}_t$ is dropped explicitly.
-- source:
--   Zhang, Li, State Evolution and Universality of Iterated Linear Programs for the Binary Perceptron, arXiv:2611.04294v1, p. 12, Algorithm 2; pp. 25–30, §6.2–6.3, eqs. (6.9)–(6.17), (6.25)

import Mathlib
import Definitions.Def_IteratedLP_Gaussian_Model

open MeasureTheory ProbabilityTheory Matrix

namespace IteratedLP.Gaussian

/-- The state of Algorithm 2 entering round `t = p + 1` (§2.3, p. 11; §6.2, p. 25):
the free fraction `q = q_p`, the free-column law `π^col_p` of `(X, R) ∈ ℝ^p × ℝ^p`, the row law
`π^row_p` of `(U, Λ) ∈ ℝ^p × ℝ^p`, and the full coordinate-trajectory law `μ^col_p` of
`X̄ ∈ [-1,1]^p`. -/
structure PopState (p : ℕ) where
  q : ℝ
  πcol : Measure (RVec p × RVec p)
  πrow : Measure (RVec p × RVec p)
  μcol : Measure (RVec p)

/-- The empty state (`p = 0`, `q₀ = 1`, empty histories), with which Algorithm 2 starts. -/
noncomputable def emptyState : PopState 0 :=
  ⟨1, Measure.dirac 0, Measure.dirac 0, Measure.dirac 0⟩

/-- Last coordinate `x_p` of `x ∈ ℝ^p` (`0` when `p = 0`, where every term containing it is
omitted, §4.2). -/
def lastE {p : ℕ} (x : RVec p) : ℝ := if h : 0 < p then x ⟨p - 1, by omega⟩ else 0

/-- `e_p⊤ a`, the last entry of a vector (`0` when `p = 0`). -/
def lastV {p : ℕ} (a : Fin p → ℝ) : ℝ := if h : 0 < p then a ⟨p - 1, by omega⟩ else 0

/-- `Q e_p`, the last column of a `p × p` matrix (the empty vector when `p = 0`). -/
def lastCol {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ) : Fin p → ℝ :=
  fun i => if h : 0 < p then Q i ⟨p - 1, by omega⟩ else 0

/-- `Q_pp`, the last diagonal entry (`0` when `p = 0`: "an old-moment entry indexed by `(p,p)`
is zero at `p = 0`", §4.2). -/
def lastDiag {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  if h : 0 < p then Q ⟨p - 1, by omega⟩ ⟨p - 1, by omega⟩ else 0

/-- Append a coordinate: `(x, y) ∈ ℝ^p × ℝ ↦ (x_1, …, x_p, y) ∈ ℝ^{p+1}`. -/
def snocE {p : ℕ} (x : RVec p) (y : ℝ) : RVec (p + 1) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => x i) y)

/-- Step 1: `Q^x = E[X̄ X̄⊤]`. -/
noncomputable def Qx {p : ℕ} (S : PopState p) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j => ∫ z, z i * z j ∂S.μcol

/-- Step 1: `Q^x_F = q E[X X⊤]`. -/
noncomputable def QxF {p : ℕ} (S : PopState p) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j => S.q * ∫ w, w.1 i * w.1 j ∂S.πcol

/-- Step 1: `Q^{rx}_F = q E[R X⊤]`. -/
noncomputable def QrxF {p : ℕ} (S : PopState p) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j => S.q * ∫ w, w.2 i * w.1 j ∂S.πcol

/-- Step 1: `Q^λ = α E[Λ Λ⊤]`. -/
noncomputable def Qlam (α : ℝ) {p : ℕ} (S : PopState p) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j => α * ∫ w, w.2 i * w.2 j ∂S.πrow

/-- Step 1: `Γ = α E[Λ U⊤]`. -/
noncomputable def Gam (α : ℝ) {p : ℕ} (S : PopState p) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j => α * ∫ w, w.2 i * w.1 j ∂S.πrow

/-- Overlap parameters `ω = (s, a, b) ∈ ℝ × ℝ^p × ℝ^p`. -/
abbrev Param (p : ℕ) : Type := ℝ × (Fin p → ℝ) × (Fin p → ℝ)

/-- Step 2 / eq. (6.9): the column competitors at `ω = (s, a, b)`, as joint laws of
`(((X, R), G), Y)` whose `((X, R), G)`-marginal is `π^col_p ⊗ N(0,1)` (so `Y` may depend on
`(X, R, G)` and on independent randomness), with `Y ∈ [-1,1]` a.s., `q E Y² = s`,
`q E[X (Y - X_p)] = a`, `q E[R (Y - X_p)] = b`. -/
def colCouplings {p : ℕ} (S : PopState p) (ω : Param p) :
    Set (Measure (((RVec p × RVec p) × ℝ) × ℝ)) :=
  {ν | IsProbabilityMeasure ν ∧ ν.map Prod.fst = S.πcol.prod (gaussianReal 0 1) ∧
    (∀ᵐ w ∂ν, |w.2| ≤ 1) ∧ S.q * ∫ w, w.2 ^ 2 ∂ν = ω.1 ∧
    (∀ i, S.q * ∫ w, w.1.1.1 i * (w.2 - lastE w.1.1.1) ∂ν = ω.2.1 i) ∧
    (∀ i, S.q * ∫ w, w.1.1.2 i * (w.2 - lastE w.1.1.1) ∂ν = ω.2.2 i)}

/-- Step 2 / eq. (6.11): the column width `ϕ_t(ω) = sup {q E[G Y]}` over the competitors. -/
noncomputable def colWidth {p : ℕ} (S : PopState p) (ω : Param p) : ℝ :=
  ⨆ ν : colCouplings S ω, S.q * ∫ w, w.1.2 * w.2 ∂(ν : Measure (((RVec p × RVec p) × ℝ) × ℝ))

/-- Step 3 / eq. (6.10): `ρ_ω² = s - (Q^x_F)_pp - 2 e_p⊤ a - a⊤ (Q^x)⁻¹ a`. -/
noncomputable def transVar {p : ℕ} (S : PopState p) (ω : Param p) : ℝ :=
  ω.1 - lastDiag (QxF S) - 2 * lastV ω.2.1 - ω.2.1 ⬝ᵥ ((Qx S)⁻¹ *ᵥ ω.2.1)

/-- Step 3 / eq. (6.13): the pre-projection row margin
`Z_ω = (e_p + (Q^x)⁻¹ a)⊤ U + ((Q^λ)⁻¹ (b - Γ (Q^x)⁻¹ a))⊤ Λ + ρ_ω G_row`,
as a function of `((U, Λ), G_row)`, with `ρ_ω = √(ρ_ω²)`. -/
noncomputable def rowField (α : ℝ) {p : ℕ} (S : PopState p) (ω : Param p)
    (w : RVec p × RVec p) (g : ℝ) : ℝ :=
  lastE w.1 + ((Qx S)⁻¹ *ᵥ ω.2.1) ⬝ᵥ (fun i => w.1 i) +
    ((Qlam α S)⁻¹ *ᵥ (ω.2.2 - Gam α S *ᵥ ((Qx S)⁻¹ *ᵥ ω.2.1))) ⬝ᵥ (fun i => w.2 i) +
    Real.sqrt (transVar S ω) * g

/-- Step 3: the admissible row margins `C_ω`, as joint laws of `(((U, Λ), G_row), Ũ)` with
`((U, Λ), G_row)`-marginal `π^row_p ⊗ N(0,1)`, `Ũ ≥ κ_t` a.s., `Ũ ∈ L²`, and
`α E[Λ Ũ] = Γ e_p + b`. -/
def rowCouplings (α κt : ℝ) {p : ℕ} (S : PopState p) (ω : Param p) :
    Set (Measure (((RVec p × RVec p) × ℝ) × ℝ)) :=
  {ν | IsProbabilityMeasure ν ∧ ν.map Prod.fst = S.πrow.prod (gaussianReal 0 1) ∧
    (∀ᵐ w ∂ν, κt ≤ w.2) ∧ Integrable (fun w => w.2 ^ 2) ν ∧
    ∀ i, α * ∫ w, w.1.1.2 i * w.2 ∂ν = lastCol (Gam α S) i + ω.2.2 i}

/-- Step 3: `d_t(ω)² = α min {E(Ũ - Z_ω)² : Ũ ∈ C_ω}` (the minimum is attained: it is the
`L²` projection onto a closed convex set). -/
noncomputable def rowCostSq (α κt : ℝ) {p : ℕ} (S : PopState p) (ω : Param p) : ℝ :=
  α * ⨅ ν : rowCouplings α κt S ω,
    ∫ w, (w.2 - rowField α S ω w.1.1 w.1.2) ^ 2 ∂(ν : Measure (((RVec p × RVec p) × ℝ) × ℝ))

/-- `d_t(ω) = √(d_t(ω)²)`. -/
noncomputable def rowCost (α κt : ℝ) {p : ℕ} (S : PopState p) (ω : Param p) : ℝ :=
  Real.sqrt (rowCostSq α κt S ω)

/-- Step 4: `ω` is admissible if `ρ_ω² ≥ 0` and the sets of Steps 2 and 3 are nonempty. -/
def Admissible (α κt : ℝ) {p : ℕ} (S : PopState p) (ω : Param p) : Prop :=
  0 ≤ transVar S ω ∧ (colCouplings S ω).Nonempty ∧ (rowCouplings α κt S ω).Nonempty

open scoped Classical in
/-- The population objective (6.17): `Ψ_t(ω) = √(ϕ_t(ω)² - d_t(ω)²)` if `ω` is admissible and
`ϕ_t(ω) ≥ d_t(ω)`, and `-∞` otherwise (in particular when `C_ω = ∅`). Step 4 maximizes it:
`V_t = max_ω Ψ_t(ω)`. -/
noncomputable def Psi (α κt : ℝ) {p : ℕ} (S : PopState p) (ω : Param p) : EReal :=
  if Admissible α κt S ω ∧ rowCost α κt S ω ≤ colWidth S ω then
    ((Real.sqrt (colWidth S ω ^ 2 - rowCost α κt S ω ^ 2) : ℝ) : EReal)
  else ⊥

/-- `ℓ(z; τ) = max_{|y| ≤ 1} {z y - τ y² / 2}` (Step 5). -/
noncomputable def ellFn (z τ : ℝ) : ℝ :=
  ⨆ y : Set.Icc (-1 : ℝ) 1, (z * (y : ℝ) - τ * (y : ℝ) ^ 2 / 2)

/-- Step 5 / eq. (6.12): the dual function of the column problem at `ω = (s, a, b)`,
`τ s / 2 - η_x⊤ (Q^x_F e_p + a) - η_r⊤ (Q^{rx}_F e_p + b) + q E ℓ(G + η_x⊤ X + η_r⊤ R; τ)`,
the expectation over `((X, R), G) ∼ π^col_p ⊗ N(0,1)`. -/
noncomputable def colDual {p : ℕ} (S : PopState p) (ω : Param p) (τ : ℝ)
    (ηx ηr : Fin p → ℝ) : ℝ :=
  τ * ω.1 / 2 - ηx ⬝ᵥ (lastCol (QxF S) + ω.2.1) - ηr ⬝ᵥ (lastCol (QrxF S) + ω.2.2) +
    S.q * ∫ w, ellFn (w.2 + ηx ⬝ᵥ (fun i => w.1.1 i) + ηr ⬝ᵥ (fun i => w.1.2 i)) τ
      ∂(S.πcol.prod (gaussianReal 0 1))

/-- The row update `U = max{κ_t, Z_ω - η_λ⊤ Λ}` (Step 5, eq. (6.14)), as a function of
`((U, Λ), G_row)`. -/
noncomputable def rowUpdate (α κt : ℝ) {p : ℕ} (S : PopState p) (ω : Param p) (ηl : Fin p → ℝ)
    (w : RVec p × RVec p) (g : ℝ) : ℝ :=
  max κt (rowField α S ω w g - ηl ⬝ᵥ (fun i => w.2 i))

/-- `η_λ` is a row multiplier at `ω` (Step 5, eq. (6.14)): `U = max{κ_t, Z_ω - η_λ⊤Λ}` satisfies
`α E[Λ U] = Γ e_p + b`. -/
def IsRowMultiplier (α κt : ℝ) {p : ℕ} (S : PopState p) (ω : Param p) (ηl : Fin p → ℝ) :
    Prop :=
  ∀ i, α * ∫ w, w.1.2 i * rowUpdate α κt S ω ηl w.1 w.2 ∂(S.πrow.prod (gaussianReal 0 1)) =
    lastCol (Gam α S) i + ω.2.2 i

/-- `(τ, η_x, η_r)` minimizes the column dual (6.12) at `ω` (Step 5). -/
def IsColDualMin {p : ℕ} (S : PopState p) (ω : Param p) (τ : ℝ) (ηx ηr : Fin p → ℝ) : Prop :=
  ∀ τ' (ηx' ηr' : Fin p → ℝ), colDual S ω τ ηx ηr ≤ colDual S ω τ' ηx' ηr'

/-- `V = √(ϕ_t(ω)² - d_t(ω)²)` at a parameter `ω`. -/
noncomputable def valueAt (α κt : ℝ) {p : ℕ} (S : PopState p) (ω : Param p) : ℝ :=
  Real.sqrt (colWidth S ω ^ 2 - rowCost α κt S ω ^ 2)

/-- `γ = d_t(ω) / V` (Step 4). -/
noncomputable def gammaAt (α κt : ℝ) {p : ℕ} (S : PopState p) (ω : Param p) : ℝ :=
  rowCost α κt S ω / valueAt α κt S ω

/-- The column sample space of Step 6: `(((X, R), G), V) ∼ π^col_p ⊗ N(0,1) ⊗ N(0,1)`. -/
noncomputable def colSpace {p : ℕ} (S : PopState p) :
    Measure (((RVec p × RVec p) × ℝ) × ℝ) :=
  (S.πcol.prod (gaussianReal 0 1)).prod (gaussianReal 0 1)

/-- The row sample space: `((U, Λ), G_row) ∼ π^row_p ⊗ N(0,1)`. -/
noncomputable def rowSpace {p : ℕ} (S : PopState p) : Measure ((RVec p × RVec p) × ℝ) :=
  S.πrow.prod (gaussianReal 0 1)

/-- Step 6: `Y_t = max{-1, min{1, (S_t + η_x⊤X + η_r⊤R)/τ}}` with
`S_t = (V + γ G)/√(1 + γ²)`, as a function of `(((X, R), G), V)`. -/
noncomputable def colUpdate {p : ℕ} (γ τ : ℝ) (ηx ηr : Fin p → ℝ)
    (w : ((RVec p × RVec p) × ℝ) × ℝ) : ℝ :=
  max (-1) (min 1 (((w.2 + γ * w.1.2) / Real.sqrt (1 + γ ^ 2) +
    ηx ⬝ᵥ (fun i => w.1.1.1 i) + ηr ⬝ᵥ (fun i => w.1.1.2 i)) / τ))

/-- Step 6: `Λ_t = (κ_t - Z_t + η_λ⊤Λ)₊ / V_t`, as a function of `((U, Λ), G_row)`. -/
noncomputable def rowMult (α κt : ℝ) {p : ℕ} (S : PopState p) (ω : Param p) (ηl : Fin p → ℝ)
    (V : ℝ) (w : (RVec p × RVec p) × ℝ) : ℝ :=
  max (κt - rowField α S ω w.1 w.2 + ηl ⬝ᵥ (fun i => w.1.2 i)) 0 / V

/-- The choices Algorithm 2 makes in one round: the maximizer `ω⋆ = (s⋆, a⋆, b⋆)` (Step 4),
the dual minimizer `(τ, η_x, η_r)` (Step 5) and the row multiplier `η_λ` (Step 5). -/
structure StepChoice (p : ℕ) where
  ω : Param p
  τ : ℝ
  ηx : Fin p → ℝ
  ηr : Fin p → ℝ
  ηl : Fin p → ℝ

/-- The choices are those of Algorithm 2: `ω⋆` maximizes `Ψ_t` over the admissible parameters
with `ϕ_t ≥ d_t` (Step 4), `(τ, η_x, η_r)` minimizes the column dual at `ω⋆`, and `η_λ` is a row
multiplier at `ω⋆` (Step 5). -/
def IsValidChoice (α κt : ℝ) {p : ℕ} (S : PopState p) (c : StepChoice p) : Prop :=
  Psi α κt S c.ω ≠ ⊥ ∧ (∀ ω', Psi α κt S ω' ≤ Psi α κt S c.ω) ∧
  IsColDualMin S c.ω c.τ c.ηx c.ηr ∧ IsRowMultiplier α κt S c.ω c.ηl

/-- Steps 6–7: the new state produced from the choices `c`, with `V_t`, `γ_t` computed at
`ω⋆ = c.ω`:
* `q_t = q P(|Y_t| < 1)`;
* `π^col_t = Law(((X, Y_t), (R, -V)) | |Y_t| < 1)`;
* `π^row_t = Law((U, U_t), (Λ, Λ_t))`;
* `μ^col_t(·) = P((X̄, X̄_p) ∈ ·, |X̄_p| = 1) + q P((X, Y_t) ∈ ·)`, the first term omitted at
  `t = 1` (eq. (6.25)). -/
noncomputable def stepOutput (α κt : ℝ) {p : ℕ} (S : PopState p) (c : StepChoice p) :
    PopState (p + 1) :=
  let V := valueAt α κt S c.ω
  let γ := gammaAt α κt S c.ω
  let Y := colUpdate γ c.τ c.ηx c.ηr
  { q := S.q * (colSpace S {w | |Y w| < 1}).toReal
    πcol := (cond (colSpace S) {w | |Y w| < 1}).map
      (fun w => (snocE w.1.1.1 (Y w), snocE w.1.1.2 (-w.2)))
    πrow := (rowSpace S).map
      (fun w => (snocE w.1.1 (rowUpdate α κt S c.ω c.ηl w.1 w.2),
        snocE w.1.2 (rowMult α κt S c.ω c.ηl V w)))
    μcol := (if p = 0 then 0 else
        (S.μcol.restrict {z | |lastE z| = 1}).map (fun z => snocE z (lastE z))) +
      ENNReal.ofReal S.q • (colSpace S).map (fun w => snocE w.1.1.1 (Y w)) }

/-- One round of Algorithm 2 with margin `κ_t`: the next state is the output of some valid
choice. -/
def IsStep (α κt : ℝ) {p : ℕ} (S : PopState p) (S' : PopState (p + 1)) : Prop :=
  ∃ c : StepChoice p, IsValidChoice α κt S c ∧ S' = stepOutput α κt S c

/-- `S` is a state-evolution sequence of Algorithm 2 for density `α` and margins
`κ_1 > ⋯ > κ_K` (0-based `κ : Fin K → ℝ`): it starts from the empty state and every round
`t = p + 1 ≤ K` is a step of Algorithm 2 with margin `κ_t`. Its outputs are `q_t = (S t).q`,
`μ^col_t = (S t).μcol` and `μ^row_t = Law(U_1, …, U_t)`, the first marginal of `(S t).πrow`. -/
def IsStateEvolution (α : ℝ) (K : ℕ) (κ : Fin K → ℝ) (S : (p : ℕ) → PopState p) : Prop :=
  S 0 = emptyState ∧ ∀ p (hp : p < K), IsStep α (κ ⟨p, hp⟩) (S p) (S (p + 1))

end IteratedLP.Gaussian


