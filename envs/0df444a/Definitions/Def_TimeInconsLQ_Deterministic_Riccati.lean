-- Prove2me | Definitions.Def_TimeInconsLQ_Deterministic_Riccati
-- name    : TimeInconsLQ_Deterministic_Riccati
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:59.129109+00:00
-- url     : https://prove2.me/theorems/53ce73d9-a0dd-4265-847d-b00304c0aa7c
-- title:
--   §4 — deterministic scalar-state coefficients, the systems (4.8), (4.9), (4.10), (4.13), the feedback (4.4) and the three cases of Theorem 4.4
-- statement:
--   This module sets up §4 of Hu, Jin and Zhou: the scalar-state problem ($n=1$, (3.7)) with **deterministic** coefficients, the coupled Riccati systems that produce an explicit equilibrium, and the hypotheses of Theorems 4.2–4.4.
--
--   **Coefficients.** Deterministic functions on $[0,T]$: $A_s,b_s,Q_s\in\mathbb R$, $B_s\in\mathbb R^l$, $C_s,\sigma_s\in\mathbb R^d$, $D_s\in\mathbb R^{d\times l}$, $R_s\in\mathbb R^{l\times l}$, and constants $G,h,\mu_1,\mu_2\in\mathbb R$; the state equation is $dX_s=[A_sX_s+B_s'u_s+b_s]ds+[C_sX_s+D_su_s+\sigma_s]'dW_s$ (3.7). The standing assumptions are: $A$ measurable and bounded; $B,C,D,Q,R$ measurable and essentially bounded on $[0,T]$; $b,\sigma$ measurable and square integrable on $[0,T]$; $R_s$ symmetric for $s\in[0,T]$; $Q\ge0$, $R\succeq0$ a.e. on $[0,T]$; $G\ge0$. The map `toData` embeds these data into the general model of §2 with $n=1$ (the $j$-th noise coefficient is $C_{s,j}X+(D_su)_j+\sigma_{s,j}$).
--
--   **Notation.** $|C|^2=C'C$, $\mathcal S(M)=\tfrac12(M+M')$, $\Gamma^{(1)}_s=\mu_1e^{\int_s^TA_r\,dr}$ (the solution of (4.7)), and $l$ is the control dimension.
--
--   **The systems.** With $K=(R+MD'D)^{-1}$,
--   $$\begin{aligned}\dot M&=-\big[2A+|C|^2+\Gamma^{(1)}B'K(B+D'C)\big]M-Q+(B+D'C)'K(B+D'C)M^2-B'K(B+D'C)MN, & M_T&=G,\\ \dot N&=-\big[2A+\Gamma^{(1)}B'KB\big]N+B'K(B+D'C)MN-B'KBN^2, & N_T&=h,\end{aligned}\tag{4.9}$$
--   and, for $J=M/N$,
--   $$\begin{aligned}\dot M&=-\big[2A+|C|^2+\Gamma^{(1)}B'K(B+D'C)\big]M-Q+(B+D'C)'K(B+D'C)M^2-B'K(B+D'C)\tfrac{M^2}{J}, & M_T&=G,\\ \dot J&=-\big[|C|^2-C'DK(B+D'C)M+\Gamma^{(1)}B'KD'C+\tfrac QM\big]J-B'KD'CM, & J_T&=\tfrac Gh.\end{aligned}\tag{4.10}$$
--   The system (4.13) is (4.10) with $R\equiv0$, written with $(D'D)^{-1}$. The linear equation (4.8) for $\Phi$ is
--   $$\dot\Phi+\{A-[(M-N)B'+MC'D]KB\}\Phi+(M-N)b+C'M\sigma-[(M-N)B'+MC'D]KMD'\sigma=0,\qquad\Phi_T=-\mu_2.$$
--   A **positive solution pair** is a solution with both components positive on $[0,T]$.
--
--   **Feedback (4.4).** $\alpha_s=-(R_s+M_sD_s'D_s)^{-1}[(M_s-N_s-\Gamma^{(1)}_s)B_s+M_sD_s'C_s]$ and $\beta_s=-(R_s+M_sD_s'D_s)^{-1}(\Phi_sB_s+M_sD_s'\sigma_s)$; a closed-loop state is a solution $X$ of (3.7) with $u_s=\alpha_sX_s+\beta_s$.
--
--   **The three cases of Theorem 4.4.** (i) $R-\delta I\succeq0$ for some $\delta>0$, $\frac{QD'D+|C|^2R}{l}+\Gamma^{(1)}\mathcal S(D'CB')\succeq0$ and $B=\lambda D'C$ for some $\lambda\ge0$; (ii) the first two conditions and $D'D-\delta I\succeq0$ for some $\delta>0$; (iii) $R\equiv0$, $D'D-\delta I\succeq0$ for some $\delta>0$, $Q+\Gamma^{(1)}B'(D'D)^{-1}(B+D'C)\ge0$ and $Q+\Gamma^{(1)}B'(D'D)^{-1}D'C\ge0$.
--
--   **Formalization Note.** The coefficients are only bounded measurable, so every ODE is stated in integral form on $[0,T]$ (Carathéodory): e.g. $M_s=G-\int_s^T F(r,M_r,N_r)\,dr$ for every $s\in[0,T]$, with the right-hand side integrable on $[0,T]$; no differentiability or continuity of the coefficients is assumed. A solution of (4.9) or (4.10) includes invertibility of $R_s+M_sD_s'D_s$ for $s\in[0,T]$ (and of $D_s'D_s$ for (4.13)), the domain on which the printed equation is defined, so Lean's junk inverse never enters. The constants $\delta,\lambda$ are uniform in $s$ and the case conditions are required for every $s\in[0,T]$ (the literal reading). "Unique" means: any two solutions agree on $[0,T]$ (values after $T$ are free).
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 7 (3.7), pp. 8–10 (4.4), (4.7)–(4.10), p. 13 (4.13), p. 14 Theorem 4.4 (i)–(iii)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Deterministic_Model

namespace TimeInconsLQ.Deterministic

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

/-- §3 (3.7) and §4: deterministic data of the scalar-state (`n = 1`) problem, in the paper's
shapes: `A_s, b_s, Q_s ∈ ℝ`, `B_s ∈ ℝˡ`, `C_s, σ_s ∈ ℝᵈ`, `D_s ∈ ℝ^{d×l}`, `R_s ∈ ℝ^{l×l}`, and
the constants `G, h, μ₁, μ₂ ∈ ℝ`. The state equation is
`dX = [AX + B′u + b] ds + [CX + Du + σ]′ dW`. -/
structure Coeffs (l d : ℕ) where
  A : ℝ≥0 → ℝ
  B : ℝ≥0 → Fin l → ℝ
  C : ℝ≥0 → Fin d → ℝ
  D : ℝ≥0 → Matrix (Fin d) (Fin l) ℝ
  b : ℝ≥0 → ℝ
  σ : ℝ≥0 → Fin d → ℝ
  Q : ℝ≥0 → ℝ
  R : ℝ≥0 → Matrix (Fin l) (Fin l) ℝ
  G : ℝ
  h : ℝ
  μ₁ : ℝ
  μ₂ : ℝ

variable {l d : ℕ}

/-- The standing assumptions of §2–§4 for deterministic coefficients on `[0, T]`: `A` is
measurable and bounded; `B, C, D, Q, R` are measurable and essentially bounded on `[0, T]`;
`b, σ` are measurable and square integrable on `[0, T]`; `R_s` is symmetric for `s ∈ [0, T]`; `Q ≥ 0` and
`R ⪰ 0` for a.e. `s ∈ [0, T]`; `G ≥ 0`. -/
structure CoeffsStanding (c : Coeffs l d) (T : ℝ≥0) : Prop where
  A_meas : Measurable c.A
  A_bdd : ∃ K : ℝ, ∀ s ≤ T, |c.A s| ≤ K
  B_meas : Measurable c.B
  C_meas : Measurable c.C
  D_meas : ∀ i j, Measurable (fun s => c.D s i j)
  b_meas : Measurable c.b
  σ_meas : Measurable c.σ
  Q_meas : Measurable c.Q
  R_meas : ∀ i j, Measurable (fun s => c.R s i j)
  B_bdd : ∃ K : ℝ, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i, |c.B s.toNNReal i| ≤ K
  C_bdd : ∃ K : ℝ, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ j, |c.C s.toNNReal j| ≤ K
  D_bdd : ∃ K : ℝ, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
    ∀ i j, |c.D s.toNNReal i j| ≤ K
  Q_bdd : ∃ K : ℝ, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), |c.Q s.toNNReal| ≤ K
  R_bdd : ∃ K : ℝ, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
    ∀ i j, |c.R s.toNNReal i j| ≤ K
  b_L2 : ∫⁻ s in Set.Icc (0 : ℝ) T, ‖c.b s.toNNReal‖ₑ ^ 2 < ⊤
  σ_L2 : ∫⁻ s in Set.Icc (0 : ℝ) T, ‖c.σ s.toNNReal‖ₑ ^ 2 < ⊤
  R_symm : ∀ s ≤ T, (c.R s).IsSymm
  Q_nonneg : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), 0 ≤ c.Q s.toNNReal
  R_psd : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), (c.R s.toNNReal).PosSemidef
  G_nonneg : 0 ≤ c.G

/-- The deterministic scalar-state data as an instance of the general model (2.1)–(2.3) with
`n = 1`, on a probability space carrying the Brownian motion `W`: `A` is the `1 × 1` matrix
`(A_s)`, `B` the `l × 1` column `B_s` (so `B′u = Σᵢ Bᵢuᵢ`), `Cʲ = (C_{s,j})`, `Dʲ` the `j`-th
row of `D_s` (so the `j`-th noise coefficient is `C_jX + (Du)_j + σ_j`), `σʲ = σ_{s,j}`,
`Q = (Q_s)`, `R = R_s`, and `G, h, μ₁, μ₂` the `1 × 1` constants. None depends on `ω`. -/
noncomputable def toData {Ω : Type*} [MeasurableSpace Ω] (c : Coeffs l d) (P : Measure Ω)
    (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W) (T : ℝ≥0) (hT : 0 < T)
    (x₀ : Fin 1 → ℝ) : TimeInconsLQ.Sufficient.Data Ω 1 l d where
  P := P
  W := W
  hW := hW
  T := T
  hT := hT
  x₀ := x₀
  A := fun s => Matrix.of fun _ _ => c.A s
  B := fun s _ => Matrix.of fun i _ => c.B s i
  C := fun j s _ => Matrix.of fun _ _ => c.C s j
  D := fun j s _ => Matrix.of fun _ k => c.D s j k
  b := fun s _ _ => c.b s
  σ := fun j s _ _ => c.σ s j
  Q := fun s _ => Matrix.of fun _ _ => c.Q s
  R := fun s _ => c.R s
  G := Matrix.of fun _ _ => c.G
  h := Matrix.of fun _ _ => c.h
  μ₁ := Matrix.of fun _ _ => c.μ₁
  μ₂ := fun _ => c.μ₂

/-- `D′_sD_s ∈ ℝ^{l×l}`. -/
def DtD (c : Coeffs l d) (s : ℝ≥0) : Matrix (Fin l) (Fin l) ℝ := (c.D s)ᵀ * c.D s

/-- `D′_sC_s ∈ ℝˡ`. -/
def DtC (c : Coeffs l d) (s : ℝ≥0) : Fin l → ℝ := (c.D s)ᵀ *ᵥ c.C s

/-- `D′_sσ_s ∈ ℝˡ`. -/
def Dtσ (c : Coeffs l d) (s : ℝ≥0) : Fin l → ℝ := (c.D s)ᵀ *ᵥ c.σ s

/-- `B_s + D′_sC_s ∈ ℝˡ`. -/
def BDC (c : Coeffs l d) (s : ℝ≥0) : Fin l → ℝ := c.B s + DtC c s

/-- `|C_s|² = C′_sC_s` (Euclidean norm). -/
def normC2 (c : Coeffs l d) (s : ℝ≥0) : ℝ := c.C s ⬝ᵥ c.C s

/-- `Γ⁽¹⁾_s = μ₁ exp(∫ₛᵀ A_r dr)`, the solution of (4.7) given on p. 9. -/
noncomputable def Gam1 (c : Coeffs l d) (T : ℝ≥0) (s : ℝ≥0) : ℝ :=
  c.μ₁ * Real.exp (∫ r in Set.Icc (s : ℝ) T, c.A r.toNNReal)

/-- `(R_s + mD′_sD_s)⁻¹`, evaluated at the value `m = M_s`. -/
noncomputable def Kinv (c : Coeffs l d) (s : ℝ≥0) (m : ℝ) : Matrix (Fin l) (Fin l) ℝ :=
  (c.R s + m • DtD c s)⁻¹

/-- `(D′_sD_s)⁻¹` (used when `R ≡ 0`). -/
noncomputable def KD (c : Coeffs l d) (s : ℝ≥0) : Matrix (Fin l) (Fin l) ℝ := (DtD c s)⁻¹

/-- Right-hand side of the `M`-equation of (4.9) at time `s` and values `M_s = m`, `N_s = n`:
`−[2A + |C|² + Γ⁽¹⁾B′(R + mD′D)⁻¹(B + D′C)]m − Q + (B + D′C)′(R + mD′D)⁻¹(B + D′C)m²
 − B′(R + mD′D)⁻¹(B + D′C)mn`. -/
noncomputable def rhs49M (c : Coeffs l d) (T s : ℝ≥0) (m n : ℝ) : ℝ :=
  -(2 * c.A s + normC2 c s + Gam1 c T s * (c.B s ⬝ᵥ (Kinv c s m *ᵥ BDC c s))) * m - c.Q s
    + (BDC c s ⬝ᵥ (Kinv c s m *ᵥ BDC c s)) * m ^ 2
    - (c.B s ⬝ᵥ (Kinv c s m *ᵥ BDC c s)) * m * n

/-- Right-hand side of the `N`-equation of (4.9):
`−[2A + Γ⁽¹⁾B′(R + mD′D)⁻¹B]n + B′(R + mD′D)⁻¹(B + D′C)mn − B′(R + mD′D)⁻¹Bn²`. -/
noncomputable def rhs49N (c : Coeffs l d) (T s : ℝ≥0) (m n : ℝ) : ℝ :=
  -(2 * c.A s + Gam1 c T s * (c.B s ⬝ᵥ (Kinv c s m *ᵥ c.B s))) * n
    + (c.B s ⬝ᵥ (Kinv c s m *ᵥ BDC c s)) * m * n
    - (c.B s ⬝ᵥ (Kinv c s m *ᵥ c.B s)) * n ^ 2

/-- `(M, N)` solves the coupled Riccati system (4.9) on `[0, T]`, in integral form:
`R_s + M_sD′_sD_s` is invertible for every `s ∈ [0, T]`, both right-hand sides are integrable
on `[0, T]`, and for every `s ∈ [0, T]`
`M_s = G − ∫ₛᵀ rhs49M(r, M_r, N_r) dr`, `N_s = h − ∫ₛᵀ rhs49N(r, M_r, N_r) dr`. -/
def IsSol49 (c : Coeffs l d) (T : ℝ≥0) (M N : ℝ≥0 → ℝ) : Prop :=
  (∀ s ≤ T, IsUnit (c.R s + M s • DtD c s)) ∧
  IntegrableOn (fun r : ℝ => rhs49M c T r.toNNReal (M r.toNNReal) (N r.toNNReal))
    (Set.Icc 0 (T : ℝ)) ∧
  IntegrableOn (fun r : ℝ => rhs49N c T r.toNNReal (M r.toNNReal) (N r.toNNReal))
    (Set.Icc 0 (T : ℝ)) ∧
  ∀ s ≤ T,
    M s = c.G - ∫ r in Set.Icc (s : ℝ) T, rhs49M c T r.toNNReal (M r.toNNReal) (N r.toNNReal) ∧
    N s = c.h - ∫ r in Set.Icc (s : ℝ) T, rhs49N c T r.toNNReal (M r.toNNReal) (N r.toNNReal)

/-- A positive solution pair of (4.9): a solution with `M_s > 0` and `N_s > 0` on `[0, T]`. -/
def IsPosSol49 (c : Coeffs l d) (T : ℝ≥0) (M N : ℝ≥0 → ℝ) : Prop :=
  IsSol49 c T M N ∧ ∀ s ≤ T, 0 < M s ∧ 0 < N s

/-- Right-hand side of the `M`-equation of (4.10) at values `M_s = m`, `J_s = j`:
`−[2A + |C|² + Γ⁽¹⁾B′(R + mD′D)⁻¹(B + D′C)]m − Q + (B + D′C)′(R + mD′D)⁻¹(B + D′C)m²
 − B′(R + mD′D)⁻¹(B + D′C)m²/j`. -/
noncomputable def rhs410M (c : Coeffs l d) (T s : ℝ≥0) (m j : ℝ) : ℝ :=
  -(2 * c.A s + normC2 c s + Gam1 c T s * (c.B s ⬝ᵥ (Kinv c s m *ᵥ BDC c s))) * m - c.Q s
    + (BDC c s ⬝ᵥ (Kinv c s m *ᵥ BDC c s)) * m ^ 2
    - (c.B s ⬝ᵥ (Kinv c s m *ᵥ BDC c s)) * (m ^ 2 / j)

/-- Right-hand side of the `J`-equation of (4.10):
`−[|C|² − C′D(R + mD′D)⁻¹(B + D′C)m + Γ⁽¹⁾B′(R + mD′D)⁻¹D′C + Q/m]j
 − B′(R + mD′D)⁻¹D′Cm`. -/
noncomputable def rhs410J (c : Coeffs l d) (T s : ℝ≥0) (m j : ℝ) : ℝ :=
  -(normC2 c s - (DtC c s ⬝ᵥ (Kinv c s m *ᵥ BDC c s)) * m
      + Gam1 c T s * (c.B s ⬝ᵥ (Kinv c s m *ᵥ DtC c s)) + c.Q s / m) * j
    - (c.B s ⬝ᵥ (Kinv c s m *ᵥ DtC c s)) * m

/-- `(M, J)` solves (4.10) on `[0, T]` in integral form, with `M_T = G`, `J_T = G/h`
(and `R_s + M_sD′_sD_s` invertible on `[0, T]`). -/
def IsSol410 (c : Coeffs l d) (T : ℝ≥0) (M J : ℝ≥0 → ℝ) : Prop :=
  (∀ s ≤ T, IsUnit (c.R s + M s • DtD c s)) ∧
  IntegrableOn (fun r : ℝ => rhs410M c T r.toNNReal (M r.toNNReal) (J r.toNNReal))
    (Set.Icc 0 (T : ℝ)) ∧
  IntegrableOn (fun r : ℝ => rhs410J c T r.toNNReal (M r.toNNReal) (J r.toNNReal))
    (Set.Icc 0 (T : ℝ)) ∧
  ∀ s ≤ T,
    M s = c.G - ∫ r in Set.Icc (s : ℝ) T, rhs410M c T r.toNNReal (M r.toNNReal) (J r.toNNReal) ∧
    J s = c.G / c.h
      - ∫ r in Set.Icc (s : ℝ) T, rhs410J c T r.toNNReal (M r.toNNReal) (J r.toNNReal)

/-- A positive solution pair of (4.10): `M_s > 0`, `J_s > 0` on `[0, T]`. -/
def IsPosSol410 (c : Coeffs l d) (T : ℝ≥0) (M J : ℝ≥0 → ℝ) : Prop :=
  IsSol410 c T M J ∧ ∀ s ≤ T, 0 < M s ∧ 0 < J s

/-- Right-hand side of the `M`-equation of (4.13) (`R ≡ 0`):
`−[2A + |C|² − (B + D′C)′(D′D)⁻¹(B + D′C) + B′(D′D)⁻¹(B + D′C)/j]m − Q
 − Γ⁽¹⁾B′(D′D)⁻¹(B + D′C)`. -/
noncomputable def rhs413M (c : Coeffs l d) (T s : ℝ≥0) (m j : ℝ) : ℝ :=
  -(2 * c.A s + normC2 c s - BDC c s ⬝ᵥ (KD c s *ᵥ BDC c s)
      + (c.B s ⬝ᵥ (KD c s *ᵥ BDC c s)) / j) * m
    - c.Q s - Gam1 c T s * (c.B s ⬝ᵥ (KD c s *ᵥ BDC c s))

/-- Right-hand side of the `J`-equation of (4.13):
`−[|C|² − C′D(D′D)⁻¹(B + D′C) + (Γ⁽¹⁾B′(D′D)⁻¹D′C + Q)/m]j − B′(D′D)⁻¹D′C`. -/
noncomputable def rhs413J (c : Coeffs l d) (T s : ℝ≥0) (m j : ℝ) : ℝ :=
  -(normC2 c s - DtC c s ⬝ᵥ (KD c s *ᵥ BDC c s)
      + (Gam1 c T s * (c.B s ⬝ᵥ (KD c s *ᵥ DtC c s)) + c.Q s) / m) * j
    - c.B s ⬝ᵥ (KD c s *ᵥ DtC c s)

/-- `(M, J)` solves (4.13) on `[0, T]` in integral form, with `M_T = G`, `J_T = G/h`
(and `D′_sD_s` invertible on `[0, T]`). -/
def IsSol413 (c : Coeffs l d) (T : ℝ≥0) (M J : ℝ≥0 → ℝ) : Prop :=
  (∀ s ≤ T, IsUnit (DtD c s)) ∧
  IntegrableOn (fun r : ℝ => rhs413M c T r.toNNReal (M r.toNNReal) (J r.toNNReal))
    (Set.Icc 0 (T : ℝ)) ∧
  IntegrableOn (fun r : ℝ => rhs413J c T r.toNNReal (M r.toNNReal) (J r.toNNReal))
    (Set.Icc 0 (T : ℝ)) ∧
  ∀ s ≤ T,
    M s = c.G - ∫ r in Set.Icc (s : ℝ) T, rhs413M c T r.toNNReal (M r.toNNReal) (J r.toNNReal) ∧
    J s = c.G / c.h
      - ∫ r in Set.Icc (s : ℝ) T, rhs413J c T r.toNNReal (M r.toNNReal) (J r.toNNReal)

/-- A positive solution pair of (4.13): `M_s > 0`, `J_s > 0` on `[0, T]`. -/
def IsPosSol413 (c : Coeffs l d) (T : ℝ≥0) (M J : ℝ≥0 → ℝ) : Prop :=
  IsSol413 c T M J ∧ ∀ s ≤ T, 0 < M s ∧ 0 < J s

/-- Right-hand side of the linear ODE (4.8) for `Φ`, at values `M_s = m`, `N_s = n`, `Φ_s = φ`,
with `w = (m − n)B + mD′C` (so `w′ = (M − N)B′ + MC′D`):
`−{A − w′(R + mD′D)⁻¹B}φ − (m − n)b − mC′σ + w′(R + mD′D)⁻¹mD′σ`. -/
noncomputable def rhs48 (c : Coeffs l d) (s : ℝ≥0) (m n φ : ℝ) : ℝ :=
  -(c.A s - ((m - n) • c.B s + m • DtC c s) ⬝ᵥ (Kinv c s m *ᵥ c.B s)) * φ
    - (m - n) * c.b s - m * (c.C s ⬝ᵥ c.σ s)
    + m * (((m - n) • c.B s + m • DtC c s) ⬝ᵥ (Kinv c s m *ᵥ Dtσ c s))

/-- `Φ` solves (4.8) on `[0, T]` in integral form, given `(M, N)`: the right-hand side is
integrable on `[0, T]` and `Φ_s = −μ₂ − ∫ₛᵀ rhs48(r, M_r, N_r, Φ_r) dr` for `s ∈ [0, T]`. -/
def IsSol48 (c : Coeffs l d) (T : ℝ≥0) (M N Φ : ℝ≥0 → ℝ) : Prop :=
  IntegrableOn (fun r : ℝ => rhs48 c r.toNNReal (M r.toNNReal) (N r.toNNReal) (Φ r.toNNReal))
    (Set.Icc 0 (T : ℝ)) ∧
  ∀ s ≤ T, Φ s = -c.μ₂
    - ∫ r in Set.Icc (s : ℝ) T, rhs48 c r.toNNReal (M r.toNNReal) (N r.toNNReal) (Φ r.toNNReal)

/-- The feedback gain of (4.4):
`α_s = −(R_s + M_sD′_sD_s)⁻¹[(M_s − N_s − Γ⁽¹⁾_s)B_s + M_sD′_sC_s] ∈ ℝˡ`. -/
noncomputable def alpha (c : Coeffs l d) (T : ℝ≥0) (M N : ℝ≥0 → ℝ) (s : ℝ≥0) : Fin l → ℝ :=
  -(Kinv c s (M s) *ᵥ ((M s - N s - Gam1 c T s) • c.B s + M s • DtC c s))

/-- The feedback offset of (4.4): `β_s = −(R_s + M_sD′_sD_s)⁻¹(Φ_sB_s + M_sD′_sσ_s) ∈ ℝˡ`. -/
noncomputable def beta (c : Coeffs l d) (M Φ : ℝ≥0 → ℝ) (s : ℝ≥0) : Fin l → ℝ :=
  -(Kinv c s (M s) *ᵥ (Φ s • c.B s + M s • Dtσ c s))

/-- `X` is a closed-loop state of the linear feedback `u_s = X_s α_s + β_s` (scalar state,
`n = 1`): `X` solves (2.1) for the control `s ↦ X_s α_s + β_s`. -/
def IsClosedLoop {Ω : Type*} [MeasurableSpace Ω] (M : TimeInconsLQ.Sufficient.Data Ω 1 l d)
    (α β : ℝ≥0 → Ω → Fin l → ℝ) (X : ℝ≥0 → Ω → Fin 1 → ℝ) : Prop :=
  TimeInconsLQ.Sufficient.IsState M (fun s ω => X s ω 0 • α s ω + β s ω) X

/-- `R − δI ⪰ 0` on `[0, T]` for some constant `δ > 0`. -/
def StdCond (c : Coeffs l d) (T : ℝ≥0) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ s ≤ T, (c.R s - δ • (1 : Matrix (Fin l) (Fin l) ℝ)).PosSemidef

/-- `(QD′D + |C|²R)/l + Γ⁽¹⁾S(D′CB′) ⪰ 0` on `[0, T]`, where `l` is the control dimension and
`S(X) = ½(X + X′)`. -/
def HCond (c : Coeffs l d) (T : ℝ≥0) : Prop :=
  ∀ s ≤ T,
    ((1 / (l : ℝ)) • (c.Q s • DtD c s + normC2 c s • c.R s)
      + Gam1 c T s • ((1 / 2 : ℝ) • (vecMulVec (DtC c s) (c.B s)
          + (vecMulVec (DtC c s) (c.B s))ᵀ))).PosSemidef

/-- `B = λD′C` on `[0, T]` for some constant `λ ≥ 0`. -/
def ColinCond (c : Coeffs l d) (T : ℝ≥0) : Prop :=
  ∃ lam : ℝ, 0 ≤ lam ∧ ∀ s ≤ T, c.B s = lam • DtC c s

/-- `D′D − δI ⪰ 0` on `[0, T]` for some constant `δ > 0`. -/
def DNondeg (c : Coeffs l d) (T : ℝ≥0) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ s ≤ T, (DtD c s - δ • (1 : Matrix (Fin l) (Fin l) ℝ)).PosSemidef

/-- Case (i) of Theorem 4.4. -/
def Case_i (c : Coeffs l d) (T : ℝ≥0) : Prop :=
  StdCond c T ∧ HCond c T ∧ ColinCond c T

/-- Case (ii) of Theorem 4.4. -/
def Case_ii (c : Coeffs l d) (T : ℝ≥0) : Prop :=
  StdCond c T ∧ HCond c T ∧ DNondeg c T

/-- Case (iii) of Theorem 4.4: `R ≡ 0`, `D′D − δI ⪰ 0`, and on `[0, T]`
`Q + Γ⁽¹⁾B′(D′D)⁻¹(B + D′C) ≥ 0`, `Q + Γ⁽¹⁾B′(D′D)⁻¹D′C ≥ 0`. -/
def Case_iii (c : Coeffs l d) (T : ℝ≥0) : Prop :=
  (∀ s ≤ T, c.R s = 0) ∧ DNondeg c T ∧
  ∀ s ≤ T, 0 ≤ c.Q s + Gam1 c T s * (c.B s ⬝ᵥ (KD c s *ᵥ BDC c s)) ∧
    0 ≤ c.Q s + Gam1 c T s * (c.B s ⬝ᵥ (KD c s *ᵥ DtC c s))

/-- The pair-valued system `S` has a solution, and any two solutions agree on `[0, T]`. -/
def HasUniqueSolOn (T : ℝ≥0) (S : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) → Prop) : Prop :=
  (∃ M N, S M N) ∧
  ∀ M N M' N', S M N → S M' N' → ∀ s ≤ T, M s = M' s ∧ N s = N' s

end TimeInconsLQ.Deterministic


