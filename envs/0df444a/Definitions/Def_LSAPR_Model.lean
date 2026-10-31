-- Prove2me | Definitions.Def_LSAPR_Model
-- name    : LSAPR_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:32:13.149991+00:00
-- url     : https://prove2.me/theorems/88d10980-6218-4698-97c8-0a5232063028
-- title:
--   Linear stochastic approximation with Polyak–Ruppert averaging: the model, A 1, A 2, IND 1, the constants, and the expansion terms
-- statement:
--   This file fixes the objects of the paper.
--
--   **Model (pp.1, 3, 6).** For measurable $\mathbf A:\mathsf Z\to\mathbb R^{d\times d}$, $\mathbf b:\mathsf Z\to\mathbb R^d$ and a probability measure $\pi$ on $\mathsf Z$: the means $\bar{\mathbf A}=\int\mathbf A\,d\pi$, $\bar{\mathbf b}=\int\mathbf b\,d\pi$; the centered parts $\tilde{\mathbf A}(z)=\mathbf A(z)-\bar{\mathbf A}$, $\tilde{\mathbf b}(z)=\mathbf b(z)-\bar{\mathbf b}$; the noise $\varepsilon(z)=\tilde{\mathbf A}(z)\theta^\star-\tilde{\mathbf b}(z)$ and $e(\theta,z)=\tilde{\mathbf A}(z)\theta-\tilde{\mathbf b}(z)$; the covariance $\Sigma_\varepsilon=\int\varepsilon(z)\varepsilon(z)^\top d\pi(z)$.
--
--   **Assumptions (p.6).** A 1: $\|\mathbf A(z)\|$ and $\|\tilde{\mathbf A}(z)\|$ are at most $\mathrm C_{\mathbf A}$ in the spectral norm and every eigenvalue of $\bar{\mathbf A}$ has positive real part. A 2: $\bar{\mathbf A}\theta^\star=\bar{\mathbf b}$ and $\|\varepsilon(z)\|\le\|\varepsilon\|_\infty$. IND 1: $(Z_k)$ is i.i.d. with law $\pi$.
--
--   **Constants.** The Lyapunov solution $Q$ ($\bar{\mathbf A}^\top Q+Q\bar{\mathbf A}=\mathrm I$, $Q\succ0$); $\|x\|_Q=(x^\top Qx)^{1/2}$ and $\|M\|_Q=\max_{\|x\|_Q=1}\|Mx\|_Q$ (p.15); $a=\|Q\|^{-1}/2$, $\alpha_\infty=\tfrac12\|\bar{\mathbf A}\|_Q^{-2}\|Q\|^{-1}\wedge\|Q\|$ (6); $\kappa_Q=\lambda_{\max}(Q)/\lambda_{\min}(Q)$, $b_Q=2\sqrt{\kappa_Q}\mathrm C_{\mathbf A}$ (18); $\mathrm c_{\mathbf A}=a/\{2b_Q^2\}$, $\alpha_{q,\infty}=\alpha_\infty\wedge\mathrm c_{\mathbf A}/q$ (19); the step size $\alpha(n,d,p)=(\alpha_\infty\wedge\mathrm c_{\mathbf A}/\{1+\log d\})(pn^{1/2})^{-1}$ (21); $\mathrm D_1,\dots,\mathrm D_4$ ((22), (45), (48)); $\mathrm C_{\mathrm{Rm},1}=60\mathrm e$, $\mathrm C_{\mathrm{Rm},2}=60$ (p.16); $\Delta^{(\mathrm{fl})}_{n,p,\alpha}$, $\Delta^{(\mathrm{tr})}_{n,p,\alpha}$ (53).
--
--   **Recursions.** The LSA iterates $\theta_k=\theta_{k-1}-\alpha\{\mathbf A(Z_k)\theta_{k-1}-\mathbf b(Z_k)\}$ and the average $\bar\theta_n=(n-n_0)^{-1}\sum_{k=n_0}^{n-1}\theta_k$ (1); the product $\Gamma^{(\alpha)}_{m:n}=\prod_{i=m}^n(\mathrm I-\alpha\mathbf A(Z_i))$ with later factors on the left and $\Gamma^{(\alpha)}_{m:n}=\mathrm I$ for $m>n$ (3); the expansion terms $J^{(0)}_n,H^{(0)}_n,J^{(1)}_n,H^{(1)}_n$ ((9), (10), (12)).
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`; matrices act and are measured through the reused `matApply` and `matNorm` (the spectral norm), and the Hurwitz condition is the reused `EigenRePos`. $\bar{\mathbf A}$ and $\Sigma_\varepsilon$ are entrywise integrals because `Matrix` has no default norm. $\mathrm C_{\mathbf A}$ and $\|\varepsilon\|_\infty$ are upper bounds rather than suprema. All integrals are genuine: $\mathbf A$ and $\varepsilon$ are bounded and measurable, and that forces $\mathbf b$ to be bounded. `matQNorm` is an `sSup` that is the attained maximum for $Q\succ0$, $d\ge1$; $\lambda_{\max},\lambda_{\min}$ are the extreme points of the real spectrum.
-- source:
--   Durmus, Moulines, Naumov & Samsonov, Finite-time High-probability Bounds for Polyak-Ruppert Averaged Iterates of Linear Stochastic Approximation, arXiv:2207.04475v2, (1) p.1; (2)–(4) p.3; (6), (9), (10) p.4; (12) p.5; (15) p.5; A 1, A 2, IND 1, (18), (19) p.6; (21) p.7; Appendix A p.15; table p.16; (45) p.17; (48) p.18; (53) p.19

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model

open MeasureTheory ProbabilityTheory PolyakJuditsky.Averaging

namespace LSAPR

/-- `ℝ^d` with the Euclidean norm (arXiv:2207.04475v2, Appendix A, p.15). -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Real `d × d` matrices. There is no default norm on `Matrix`; every matrix norm of this
mission is the spectral norm `PolyakJuditsky.Averaging.matNorm`. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

section Setting

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

/-- `Ā = ∫ A dπ` (A 2, p.6), computed entrywise. -/
noncomputable def Abar (π : Measure Z) (A : Z → Mat d) : Mat d :=
  Matrix.of fun i j => ∫ z, A z i j ∂π

/-- `b̄ = ∫ b dπ` (A 2, p.6). -/
noncomputable def bbar (π : Measure Z) (b : Z → Vec d) : Vec d :=
  ∫ z, b z ∂π

/-- `Ã(z) = A(z) - Ā` ((2), p.3). -/
noncomputable def Atilde (π : Measure Z) (A : Z → Mat d) (z : Z) : Mat d :=
  A z - Abar π A

/-- `b̃(z) = b(z) - b̄` ((2), p.3). -/
noncomputable def btilde (π : Measure Z) (b : Z → Vec d) (z : Z) : Vec d :=
  b z - bbar π b

/-- The noise `ε(z) = Ã(z) θ⋆ - b̃(z)` ((2), p.3). -/
noncomputable def epsNoise (π : Measure Z) (A : Z → Mat d) (b : Z → Vec d) (θstar : Vec d)
    (z : Z) : Vec d :=
  matApply (Atilde π A z) θstar - btilde π b z

/-- `e(θ, z) = Ã(z) θ - b̃(z)` ((15), p.5). -/
noncomputable def eNoise (π : Measure Z) (A : Z → Mat d) (b : Z → Vec d) (θ : Vec d)
    (z : Z) : Vec d :=
  matApply (Atilde π A z) θ - btilde π b z

/-- The noise covariance `Σ_ε = ∫ ε(z) ε(z)ᵀ dπ(z)` (p.6), computed entrywise, for
`ε : Z → ℝ^d`. -/
noncomputable def SigmaEps (π : Measure Z) (ε : Z → Vec d) : Mat d :=
  Matrix.of fun i j => ∫ z, ε z i * ε z j ∂π

/-- Assumption A 1 (p.6), with `CA` an upper bound of `sup_z ‖A(z)‖ ∨ sup_z ‖Ã(z)‖` in the
spectral norm, plus the measurability of `A : Z → ℝ^{d×d}` (p.1).

**Formalization Note.** `Ā` is `∫ A dπ`, so the hypothesis also records the relation between
`Ā` and `π` that A 2 and p.1 state. `A` is bounded and measurable, so `Abar π A` is a genuine
integral whenever `π` is finite. -/
structure SatisfiesA1 (π : Measure Z) (A : Z → Mat d) (CA : ℝ) : Prop where
  measurable_A : ∀ i j, Measurable fun z => A z i j
  norm_A_le : ∀ z, matNorm (A z) ≤ CA
  norm_Atilde_le : ∀ z, matNorm (Atilde π A z) ≤ CA
  hurwitz : EigenRePos (Abar π A)

/-- Assumption A 2 (p.6), with `εmax` an upper bound of `‖ε‖∞ = sup_z ‖ε(z)‖`, plus the
measurability of `b : Z → ℝ^d` (p.1).

**Formalization Note.** The two integral identities of A 2 are the definitions `Abar`, `bbar`.
`θstar` is the solution of `Ā θ = b̄` (p.6). With `A` bounded, a bounded `ε` forces `b` to be
bounded, so `bbar π b` is a genuine integral whenever `π` is finite. -/
structure SatisfiesA2 (π : Measure Z) (A : Z → Mat d) (b : Z → Vec d) (θstar : Vec d)
    (εmax : ℝ) : Prop where
  measurable_b : Measurable b
  solves : matApply (Abar π A) θstar = bbar π b
  norm_eps_le : ∀ z, ‖epsNoise π A b θstar z‖ ≤ εmax

/-- Assumption IND 1 (p.6): `{Z_k}` is an i.i.d. sequence on `(Ω, F, P)` with distribution `π`. -/
structure SatisfiesIND1 {Ω : Type*} [MeasurableSpace Ω] (π : Measure Z) (P : Measure Ω)
    (Zs : ℕ → Ω → Z) : Prop where
  measurable : ∀ k, Measurable (Zs k)
  indep : iIndepFun Zs P
  law : ∀ k, P.map (Zs k) = π

end Setting

section Constants

variable {d : ℕ}

/-- `Q` is the solution of the Lyapunov equation `Āᵀ Q + Q Ā = I` (Proposition 1, p.4):
symmetric (part of `Matrix.PosDef`) and positive definite. -/
def IsLyapunov (Ā Q : Mat d) : Prop :=
  Q.PosDef ∧ Ā.transpose * Q + Q * Ā = 1

/-- `‖x‖_Q = {xᵀ Q x}^{1/2}` (Appendix A, p.15). -/
noncomputable def qNorm (Q : Mat d) (x : Vec d) : ℝ :=
  Real.sqrt (inner ℝ x (matApply Q x))

/-- `‖M‖_Q = max_{‖x‖_Q = 1} ‖M x‖_Q` (Appendix A, p.15).

**Formalization Note.** For `Q` positive definite and `d ≥ 1` the set is the continuous image
of a nonempty compact ellipsoid, so the `sSup` is the attained maximum. -/
noncomputable def matQNorm (Q M : Mat d) : ℝ :=
  sSup ((fun x => qNorm Q (matApply M x)) '' {x | qNorm Q x = 1})

/-- `λ_max(Q) / λ_min(Q)` ((18), p.6), with `λ_max`, `λ_min` the extreme points of the real
spectrum (finite and nonempty for `Q` symmetric and `d ≥ 1`). -/
noncomputable def kappaQ (Q : Mat d) : ℝ :=
  sSup (spectrum ℝ Q) / sInf (spectrum ℝ Q)

/-- `a = ‖Q‖⁻¹ / 2` ((6), p.4). -/
noncomputable def aQ (Q : Mat d) : ℝ :=
  (matNorm Q)⁻¹ / 2

/-- `α∞ = (1/2) ‖Ā‖_Q^{-2} ‖Q‖⁻¹ ∧ ‖Q‖` ((6), p.4). -/
noncomputable def alphaInf (Ā Q : Mat d) : ℝ :=
  min ((1 / 2) * ((matQNorm Q Ā)⁻¹) ^ 2 * (matNorm Q)⁻¹) (matNorm Q)

/-- `b_Q = 2 √κ_Q C_A` ((18), p.6). -/
noncomputable def bQ (Q : Mat d) (CA : ℝ) : ℝ :=
  2 * Real.sqrt (kappaQ Q) * CA

/-- `c_A = a / {2 b_Q²}` ((19), p.6). -/
noncomputable def cA (Q : Mat d) (CA : ℝ) : ℝ :=
  aQ Q / (2 * bQ Q CA ^ 2)

/-- `α_{q,∞} = α∞ ∧ c_A / q` ((19), p.6). -/
noncomputable def alphaQInf (Ā Q : Mat d) (CA q : ℝ) : ℝ :=
  min (alphaInf Ā Q) (cA Q CA / q)

/-- `D₁ = √(2 κ_Q) / a` ((22), p.8). -/
noncomputable def D1 (Q : Mat d) : ℝ :=
  Real.sqrt (2 * kappaQ Q) / aQ Q

/-- `D₂ = (2 κ_Q)^{1/2} a⁻¹ (1 + 4 κ_Q^{1/2} C_A a⁻¹)` ((45), p.17). -/
noncomputable def D2 (Q : Mat d) (CA : ℝ) : ℝ :=
  Real.sqrt (2 * kappaQ Q) * (aQ Q)⁻¹ * (1 + 4 * Real.sqrt (kappaQ Q) * CA * (aQ Q)⁻¹)

/-- `D₃ = 2 κ_Q C_A / a²` ((48), p.18). -/
noncomputable def D3 (Q : Mat d) (CA : ℝ) : ℝ :=
  2 * kappaQ Q * CA / aQ Q ^ 2

/-- `D₄ = 4 κ_Q^{1/2} C_A D₃ / a` ((48), p.18). -/
noncomputable def D4 (Q : Mat d) (CA : ℝ) : ℝ :=
  4 * Real.sqrt (kappaQ Q) * CA * D3 Q CA / aQ Q

/-- `C_{Rm,1} = 60 e` (table, p.16). -/
noncomputable def CRm1 : ℝ := 60 * Real.exp 1

/-- `C_{Rm,2} = 60` (table, p.16). -/
noncomputable def CRm2 : ℝ := 60

/-- `Δ^{(fl)}_{n,p,α}` ((53), p.19). -/
noncomputable def DeltaFl (Q : Mat d) (CA : ℝ) (n : ℕ) (p α : ℝ) : ℝ :=
  4 * Real.exp (1 / p) * D2 Q CA * Real.sqrt (aQ Q * p) / Real.sqrt (α * n)
    + Real.exp (1 / p) * CA * (D3 Q CA + D4 Q CA) * α * aQ Q * p ^ (5 / 2 : ℝ)
    + 2 * CRm2 * p / Real.sqrt n
    + CA * D1 Q * Real.sqrt (α * aQ Q) * p ^ (3 / 2 : ℝ)

/-- `Δ^{(tr)}_{n,p,α}` ((53), p.19). -/
noncomputable def DeltaTr (Q : Mat d) (CA : ℝ) (n : ℕ) (p α : ℝ) : ℝ :=
  Real.exp (1 / p) * Real.sqrt (kappaQ Q) *
    (4 / (α * Real.sqrt n) + (Real.sqrt 2)⁻¹ * Real.sqrt n * CA)

/-- The step size `α(n, d, p) = (α∞ ∧ c_A / {1 + log d}) (p n^{1/2})⁻¹` ((21), p.7). -/
noncomputable def stepSize (Ā Q : Mat d) (CA : ℝ) (n : ℕ) (p : ℝ) : ℝ :=
  min (alphaInf Ā Q) (cA Q CA / (1 + Real.log d)) * (p * Real.sqrt n)⁻¹

end Constants

section Recursions

variable {d : ℕ} {Z : Type*}

/-- The LSA iterates along a sample path `Z₁, Z₂, …` ((1), p.1):
`θ_k = θ_{k-1} - α {A(Z_k) θ_{k-1} - b(Z_k)}`, `k ≥ 1`. `Zpath 0` is not used. -/
noncomputable def lsaIter (α : ℝ) (A : Z → Mat d) (b : Z → Vec d) (θ0 : Vec d)
    (Zpath : ℕ → Z) : ℕ → Vec d
  | 0 => θ0
  | k + 1 => lsaIter α A b θ0 Zpath k
      - α • (matApply (A (Zpath (k + 1))) (lsaIter α A b θ0 Zpath k) - b (Zpath (k + 1)))

/-- The Polyak–Ruppert average `θ̄_n = (n - n0)⁻¹ ∑_{k=n0}^{n-1} θ_k` ((1), p.1). The standing
burn-in of the paper is `n0 = n / 2` with `n` even (p.5). -/
noncomputable def prAvg (α : ℝ) (A : Z → Mat d) (b : Z → Vec d) (θ0 : Vec d) (Zpath : ℕ → Z)
    (n0 n : ℕ) : Vec d :=
  ((n : ℝ) - n0)⁻¹ • ∑ k ∈ Finset.Ico n0 n, lsaIter α A b θ0 Zpath k

/-- `Γ^{(α)}_{m:n} = ∏_{i=m}^n (I - α A(Z_i))` ((3), p.3), with the later factors on the left
(Appendix A, p.15) and `Γ^{(α)}_{m:n} = I` for `m > n`. -/
noncomputable def Gamma (α : ℝ) (A : Z → Mat d) (Zpath : ℕ → Z) (m n : ℕ) : Mat d :=
  (((List.range' m (n + 1 - m)).reverse).map fun i => (1 : Mat d) - α • A (Zpath i)).prod

/-- `J^{(0)}_n = (I - α Ā) J^{(0)}_{n-1} - α ε(Z_n)`, `J^{(0)}_0 = 0` ((9), p.4). -/
noncomputable def J0 (Ā : Mat d) (ε : Z → Vec d) (α : ℝ) (Zpath : ℕ → Z) : ℕ → Vec d
  | 0 => 0
  | n + 1 => matApply (1 - α • Ā) (J0 Ā ε α Zpath n) - α • ε (Zpath (n + 1))

/-- `H^{(0)}_n = (I - α A(Z_n)) H^{(0)}_{n-1} - α Ã(Z_n) J^{(0)}_{n-1}`, `H^{(0)}_0 = 0`
((10), p.4). -/
noncomputable def H0 (Ā : Mat d) (A : Z → Mat d) (ε : Z → Vec d) (α : ℝ) (Zpath : ℕ → Z) :
    ℕ → Vec d
  | 0 => 0
  | n + 1 => matApply (1 - α • A (Zpath (n + 1))) (H0 Ā A ε α Zpath n)
      - α • matApply (A (Zpath (n + 1)) - Ā) (J0 Ā ε α Zpath n)

/-- `J^{(1)}_n = (I - α Ā) J^{(1)}_{n-1} - α Ã(Z_n) J^{(0)}_{n-1}`, `J^{(1)}_0 = 0`
((12), p.5). -/
noncomputable def J1 (Ā : Mat d) (A : Z → Mat d) (ε : Z → Vec d) (α : ℝ) (Zpath : ℕ → Z) :
    ℕ → Vec d
  | 0 => 0
  | n + 1 => matApply (1 - α • Ā) (J1 Ā A ε α Zpath n)
      - α • matApply (A (Zpath (n + 1)) - Ā) (J0 Ā ε α Zpath n)

/-- `H^{(1)}_n = (I - α A(Z_n)) H^{(1)}_{n-1} - α Ã(Z_n) J^{(1)}_{n-1}`, `H^{(1)}_0 = 0`
((12), p.5). -/
noncomputable def H1 (Ā : Mat d) (A : Z → Mat d) (ε : Z → Vec d) (α : ℝ) (Zpath : ℕ → Z) :
    ℕ → Vec d
  | 0 => 0
  | n + 1 => matApply (1 - α • A (Zpath (n + 1))) (H1 Ā A ε α Zpath n)
      - α • matApply (A (Zpath (n + 1)) - Ā) (J1 Ā A ε α Zpath n)

end Recursions

end LSAPR


