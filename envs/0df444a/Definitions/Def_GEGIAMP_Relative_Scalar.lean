-- Prove2me | Definitions.Def_GEGIAMP_Relative_Scalar
-- name    : GEGIAMP_Relative_Scalar
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:51:35.658912+00:00
-- url     : https://prove2.me/theorems/a93e0ae4-87b3-4bd4-b637-ee0bd009c7cb
-- title:
--   Grid (6.1)–(6.2), point quadrature (6.5)–(6.6), the scalar recursions and proof quantities
-- statement:
--   Fixed algorithmic constants $c_\tau,c_h,c_B,c_q,K_R$. The grid at internal accuracy $\varepsilon$: $\tau$ halved from $1/2$ until $\tau^3L_\varepsilon\le c_\tau^3\varepsilon^2$, $T=1-\tau$, $L_\tau$, $B=\lceil T/(c_B\varepsilon)\rceil$, $\Delta=T/B$, $h^*=c_h\varepsilon^2/L_\tau^2$, $m_f=\lceil\Delta/h^*\rceil$, $h=\Delta/m_f$, $K=Bm_f$, $d=B+1$, $t_k=kh$. $R=K_R\Lambda(T)$, $\eta_q=c_q\varepsilon^2/R$, $r^q_k=\max\{1,\lceil(\gamma(t_{k+1})-\gamma(t_k))/\eta_q\rceil\}$ and the trapezoid values $\Gamma^q_k$ (6.6); the exact integrals $\Gamma_k$ (7.14). The scalar recursion $Y_{k+1}=Y_k+\Gamma_km(t_k,Y_k)+G_k$, $M^\omega_{k+1}=M^\omega_k+a(t_k,Y_k)G_k/\omega_k$ with $G_k$ i.i.d. $N(0,h)$ (6.7)–(6.8); $\rho_k=(\mathbb Ea(t_k,Y_k)^2)^{1/2}$ (6.16), $\mathcal E=\mathbb E[W_TM^\rho_K]$ (6.17), $\nu=c_\nu\varepsilon/\log(4d)$ (6.18), condition (7.116); the group correlations $c_s$ (8.6), $V=\sum_{j<K}K_xh\Lambda(t_j)$ (8.27), $\overline V=1+V$, and $b_0$ (8.71) with its constant. Groups are 0-based in Lean.
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), (6.1)–(6.8) pp. 17–18; (6.16)–(6.18) pp. 19–20; (7.14)–(7.16) p. 22; (7.116) p. 37; (8.6) p. 42; (8.27) p. 47; (8.71) p. 56

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-!
# Grid parameters, point quadrature and the scalar recursions

Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1 (SHA-256 ea6508af…5658e):
(6.1)–(6.3) p. 17 (grid), (6.5)–(6.6) p. 17 (point quadrature), (6.7)–(6.8) p. 18 (scalar
recursion), (6.16)–(6.18) pp. 19–20 (`ρ`, `E`, `ν`), (7.14)–(7.16) p. 22 (exact-drift
recursion), (7.116) p. 37, (8.6) p. 42, (8.27) p. 47, (8.71) p. 56.

**Conventions.** Time-grid indices are 0-based as in the paper (`t_k = k h`, `0 ≤ k ≤ K`).
Groups are **0-based** in Lean: the paper's group `s ∈ {1, …, B}` is Lean's `s − 1`, with
indices `{s m_f, …, (s+1) m_f − 1}`. The Gaussian increments `G_0, …, G_{K−1}` are the
coordinates of `g : Fin K → ℝ` under `gaussLaw K h = ⊗ N(0, h)`; `gx g k` is `G_k` (`0` for
`k ≥ K`, never used). Expectations of the scalar recursion are integrals against `gaussLaw`.
The oracles `γ, m, a` are passed as plain functions `gm`, `mo`, `ao`.
-/

namespace GEGIAMP.Relative

/-! ## Fixed algorithmic constants and the grid (6.1)–(6.2) -/

/-- The fixed algorithmic constants `c_τ, c_h, c_B, c_q, K_R` of §6.1–§6.2 (p. 17). -/
structure AlgConsts where
  cτ : ℝ
  ch : ℝ
  cB : ℝ
  cq : ℝ
  KR : ℝ

/-- All algorithmic constants are positive. -/
def AlgConsts.Pos (κ : AlgConsts) : Prop :=
  0 < κ.cτ ∧ 0 < κ.ch ∧ 0 < κ.cB ∧ 0 < κ.cq ∧ 0 < κ.KR

open Classical in
/-- The cutoff `τ` of (6.1): start with `τ = 1/2` and halve until the first time
`τ³ L_ε ≤ c_τ³ ε²`; so `τ = 2^{-(j+1)}` for the least `j ≥ 0` passing the test (`1/2` if no
`j` passes, which does not happen for `ε, c_τ > 0`). -/
noncomputable def tauOf (κ : AlgConsts) (ε : ℝ) : ℝ :=
  if h : ∃ j : ℕ, ((1 / 2 : ℝ) ^ (j + 1)) ^ 3 * Lg ε ≤ κ.cτ ^ 3 * ε ^ 2 then
    (1 / 2 : ℝ) ^ (Nat.find h + 1)
  else 1 / 2

/-- The grid of (6.1)–(6.2), p. 17, at internal accuracy `ε`. -/
structure Params where
  /-- `τ`, (6.1). -/
  τ : ℝ
  /-- `T = 1 − τ`. -/
  T : ℝ
  /-- `L_τ = log(e/τ)`. -/
  Lτ : ℝ
  /-- `B = ⌈T/(c_B ε)⌉`, the number of observation intervals (groups). -/
  B : ℕ
  /-- `Δ = T/B`. -/
  Δ : ℝ
  /-- `h* = c_h ε²/L_τ²`. -/
  hstar : ℝ
  /-- `m_f = ⌈Δ/h*⌉`, the number of steps per group. -/
  mf : ℕ
  /-- `h = Δ/m_f`, the time step. -/
  h : ℝ
  /-- `K = B m_f`, the number of discretization steps (italic `K`). -/
  K : ℕ
  /-- `d = B + 1`. -/
  d : ℕ

/-- The grid (6.1)–(6.2) at internal accuracy `ε` and constants `κ`. -/
noncomputable def params (κ : AlgConsts) (ε : ℝ) : Params :=
  let τ := tauOf κ ε
  let T := 1 - τ
  let Lτ := Lg τ
  let B := ⌈T / (κ.cB * ε)⌉₊
  let Δ := T / B
  let hstar := κ.ch * ε ^ 2 / Lτ ^ 2
  let mf := ⌈Δ / hstar⌉₊
  let h := Δ / mf
  { τ := τ, T := T, Lτ := Lτ, B := B, Δ := Δ, hstar := hstar, mf := mf, h := h,
    K := B * mf, d := B + 1 }

/-- The grid node `t_k = k h`. -/
noncomputable def Params.t (P : Params) (k : ℕ) : ℝ := (k : ℝ) * P.h

/-! ## Point quadrature (6.5)–(6.6), p. 17 -/

/-- `R = K_R Λ(T)`, (6.5). -/
noncomputable def Rq (κ : AlgConsts) (ε : ℝ) : ℝ := κ.KR * Lam (params κ ε).T

/-- `η_q = c_q ε²/R`, (6.5). -/
noncomputable def etaq (κ : AlgConsts) (ε : ℝ) : ℝ := κ.cq * ε ^ 2 / Rq κ ε

/-- `r^q_k = max{1, ⌈[γ(t_{k+1}) − γ(t_k)]/η_q⌉}`, (6.6). -/
noncomputable def rq (gm : ℝ → ℝ) (κ : AlgConsts) (ε : ℝ) (k : ℕ) : ℕ :=
  let P := params κ ε
  max 1 ⌈(gm (P.t (k + 1)) - gm (P.t k)) / etaq κ ε⌉₊

/-- The quadrature value `Γ^q_k = (h/(2 r^q_k)) ∑_{j<r^q_k} {γ(s_{k,j}) + γ(s_{k,j+1})}` with
`s_{k,j} = t_k + j h / r^q_k`, (6.6). -/
noncomputable def Gq (gm : ℝ → ℝ) (κ : AlgConsts) (ε : ℝ) (k : ℕ) : ℝ :=
  let P := params κ ε
  let r := rq gm κ ε k
  let s : ℕ → ℝ := fun j => P.t k + (j : ℝ) * P.h / r
  P.h / (2 * r) * ∑ j ∈ Finset.range r, (gm (s j) + gm (s (j + 1)))

/-- The exact drift integral `Γ_k = ∫_{t_k}^{t_{k+1}} γ(s) ds`, (7.14). -/
noncomputable def Gex (gm : ℝ → ℝ) (P : Params) (k : ℕ) : ℝ :=
  ∫ s in P.t k..P.t (k + 1), gm s

/-! ## The scalar recursion (6.7)–(6.8) -/

/-- The law of `(G_0, …, G_{K−1})`: independent `N(0, h)`. -/
noncomputable def gaussLaw (K : ℕ) (h : ℝ) : Measure (Fin K → ℝ) :=
  Measure.pi fun _ : Fin K => gaussianReal 0 h.toNNReal

/-- `G_k` (zero beyond the horizon, never used there). -/
def gx {K : ℕ} (g : Fin K → ℝ) (k : ℕ) : ℝ := if hk : k < K then g ⟨k, hk⟩ else 0

/-- The state recursion `Y_0 = 0`, `Y_{k+1} = Y_k + Γ_k m(t_k, Y_k) + G_k` with drift
coefficients `Γc` ((6.7) with `Γc = Γ^q`, (7.14) with `Γc = Γ`). -/
noncomputable def Ys (mo : ℝ → ℝ → ℝ) (h : ℝ) (Γc : ℕ → ℝ) {K : ℕ} (g : Fin K → ℝ) :
    ℕ → ℝ
  | 0 => 0
  | k + 1 => Ys mo h Γc g k + Γc k * mo ((k : ℝ) * h) (Ys mo h Γc g k) + gx g k

/-- The magnetization `M^ω_0 = 0`, `M^ω_{k+1} = M^ω_k + a(t_k, Y_k) G_k / ω_k`, (6.8). -/
noncomputable def Ms (mo ao : ℝ → ℝ → ℝ) (h : ℝ) (Γc : ℕ → ℝ) (ω : ℕ → ℝ) {K : ℕ}
    (g : Fin K → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => Ms mo ao h Γc ω g k + ao ((k : ℝ) * h) (Ys mo h Γc g k) * gx g k / ω k

/-- `W_T = ∑_{k<K} G_k`, (6.17). -/
def WT {K : ℕ} (g : Fin K → ℝ) : ℝ := ∑ k, g k

/-- The normalization factors `ρ_k = (E a(t_k, Y_k)²)^{1/2}` (nonnegative root), (6.16)
(`(7.15)` for the exact-drift recursion). -/
noncomputable def rhoOf (mo ao : ℝ → ℝ → ℝ) (h : ℝ) (Γc : ℕ → ℝ) (K : ℕ) (k : ℕ) : ℝ :=
  Real.sqrt (∫ g, (ao ((k : ℝ) * h) (Ys mo h Γc g k)) ^ 2 ∂(gaussLaw K h))

/-- The correlation `E = E[W_T M^ρ_K]`, (6.17) (`E^r` of (7.16) for the exact-drift
recursion). -/
noncomputable def corrE (mo ao : ℝ → ℝ → ℝ) (h : ℝ) (Γc : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∫ g, WT g * Ms mo ao h Γc (rhoOf mo ao h Γc K) g K ∂(gaussLaw K h)

/-- The tolerance `ν = c_ν ε / log(4d)`, (6.18), p. 20. -/
noncomputable def nuOf (cν ε : ℝ) (d : ℕ) : ℝ := cν * ε / Real.log (4 * d)

/-- Condition (7.116), p. 37: `1/2 ≤ ω_k ≤ 2` and `|ω_k²/ρ_k² − 1| ≤ ν` for every `k < K`. -/
def Cond7116 (ω ρ : ℕ → ℝ) (ν : ℝ) (K : ℕ) : Prop :=
  ∀ k < K, 1 / 2 ≤ ω k ∧ ω k ≤ 2 ∧ |ω k ^ 2 / ρ k ^ 2 - 1| ≤ ν

/-! ## Proof quantities for the matrix analysis -/

/-- The group correlation `c_s = E[(∑_{j∈I_s} G_j) δ_s M^ρ]`,
`δ_s M^ρ = ∑_{j∈I_s} a(t_j, Y_j) G_j / ρ_j`, (8.6), p. 42; Lean group `s` is the paper's
group `s + 1`, so the paper's `c_1` is `cGroup … 0`. -/
noncomputable def cGroup (mo ao : ℝ → ℝ → ℝ) (P : Params) (Γc : ℕ → ℝ) (s : ℕ) : ℝ :=
  let ρ := rhoOf mo ao P.h Γc P.K
  ∫ g, (∑ j ∈ Finset.Ico (s * P.mf) ((s + 1) * P.mf), gx g j) *
      (∑ j ∈ Finset.Ico (s * P.mf) ((s + 1) * P.mf),
        ao ((j : ℝ) * P.h) (Ys mo P.h Γc g j) * gx g j / ρ j) ∂(gaussLaw P.K P.h)

/-- `V = ∑_{j<K} x^var_j`, `x^var_j = K_x h Λ(t_j)`, (8.27), p. 47, for the variance constant
`K_x`. -/
noncomputable def Vsum (Kx : ℝ) (P : Params) : ℝ :=
  ∑ j ∈ Finset.range P.K, Kx * P.h * Lam (P.t j)

/-- `V̄ = 1 + V` (p. 47, after (8.27)), used in (8.40), (8.67) and (8.82). -/
noncomputable def Vbar (Kx : ℝ) (P : Params) : ℝ := 1 + Vsum Kx P

/-- `b_0 = K_b {h L_τ²/τ + η_q (1 + h L_τ^{3/2}/√τ)}`, (8.71), p. 56, with its universal
constant `K_b`. -/
noncomputable def b0Of (Kb : ℝ) (κ : AlgConsts) (ε : ℝ) : ℝ :=
  let P := params κ ε
  Kb * (P.h * P.Lτ ^ 2 / P.τ + etaq κ ε * (1 + P.h * P.Lτ ^ (3 / 2 : ℝ) / Real.sqrt P.τ))

end GEGIAMP.Relative


