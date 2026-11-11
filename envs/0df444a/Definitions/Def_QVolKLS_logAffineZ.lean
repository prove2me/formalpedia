-- Prove2me | Definitions.Def_QVolKLS_logAffineZ
-- name    : QVolKLS_logAffineZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:39:46.764231+00:00
-- url     : https://prove2.me/theorems/a0de1684-8a6a-42b0-ab80-dc24b0f6360e
-- title:
--   Log-affine laws $\pi_b\propto e^{-\langle b,x\rangle}1_K$, lattice laws $\pi_{b,\Lambda}$, the smoothed law $\tilde\pi_\Lambda$, $d_{\mathrm{TV}}$
-- statement:
--   Let $K\subseteq\mathbb R^D$ be a convex body and $b\in\mathbb R^D$ a tilt.
--
--   1. The **log-affine law** (36) is $\pi_b(dx)=Z_b^{-1}e^{-\langle b,x\rangle}1_K(x)\,dx$ with $Z_b=\int_Ke^{-\langle b,x\rangle}dx$.
--   2. On the lattice $\Lambda=h\mathbb Z^D$: $Z_{b,\Lambda}=h^D\sum_{z\in K\cap\Lambda}e^{-\langle b,z\rangle}$ and $\pi_{b,\Lambda}(z)=h^De^{-\langle b,z\rangle}/Z_{b,\Lambda}$.
--   3. The lattice cell is $Q_\Lambda=h[-\tfrac12,\tfrac12)^D$, and $\tilde\pi_\Lambda$ is the law of $X_\Lambda+E$ with $X_\Lambda\sim\pi_{b,\Lambda}$ and $E$ uniform on $Q_\Lambda$, independent.
--   4. $d_{\mathrm{TV}}(\mu,\nu)=\sup_A|\mu(A)-\nu(A)|$ over measurable $A$.
--   5. Covariances are compared through quadratic forms: $u^\top\mathrm{Cov}_\mu(X)u=\mathrm{Var}_\mu(\langle u,X\rangle)$, and for a rational matrix $A$, $u^\top Au=\sum_{i,j}u_iA_{ij}u_j$; $\Sigma\preceq A$ means $u^\top\Sigma u\le u^\top Au$ for all $u$.
--
--   These are the targets of the lattice Metropolis walk (§5.1) and of the quadrature estimate (Lemma B.2).
--
--   **Formalization Note** `logAffineZ`, `logAffineMeasure`, `latticeZ`, `latticeLaw`, `cellQ`, `smoothedLatticeMeasure`, `measTV`, `dirVariance`, `quadForm`. $Z_b$ is a Bochner integral of a bounded function over a compact set.
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), §5.1, p.37, (36); App. B.2, pp.62–63, (64)–(65); §2.3, p.23 (d_TV)

import Definitions.Def_QVolKLS_pencil

set_option autoImplicit false

namespace QVolKLS

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

/-!
# Log-affine laws on a convex body and their lattice discretizations

R. Zhang, *Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation*,
arXiv:2610.04987 (held version, sha256 eee7a45e…): §5.1, p.37, (36)
(`Z_b = ∫_K e^{−⟨b,x⟩} dx`, `π_b(dx) = Z_b^{−1} e^{−⟨b,x⟩} 1_K(x) dx`,
`Z_{b,Λ} = h^D Σ_{x ∈ K ∩ hℤ^D} e^{−⟨b,x⟩}`, `π_{b,Λ}(x) = h^D e^{−⟨b,x⟩}/Z_{b,Λ}`, the Loewner comparison
`A ≍ Σ`), and App. B.2, p.62, (64)–(65) (the cell `Q_Λ = h[−1/2, 1/2)^D`), p.63 (the law `π̃_Λ` of
`X_Λ + E`), §2.3, p.23 (`d_TV(µ, ν) = sup_A |µ(A) − ν(A)|`).

**Formalization Note.**
* `logAffineZ K b` is a Bochner integral; for a compact `K` the integrand is bounded on `K`, so it is
  integrable. `logAffineMeasure K b` is the measure with density `e^{−⟨b,x⟩}/Z_b` on `K`.
* `smoothedLatticeMeasure K h b` is the law of `X_Λ + E`, `X_Λ ∼ π_{b,Λ}` and `E` uniform on `Q_Λ`
  independent: `Σ_z π_{b,Λ}(z) · (Lebesgue on z + Q_Λ)/h^D`.
* `measTV µ ν = sup_A |µ(A) − ν(A)|` over measurable `A` (finite measures; values via `toReal`).
* Covariance comparisons are stated through quadratic forms: `Σ ⪯ A` means `uᵀΣu ≤ uᵀAu` for every
  `u`, and `uᵀ Cov_µ(X) u = Var_µ(⟨u, X⟩)` (`dirVariance`). The laws used have finite second moments
  (log-concave laws, or laws on a compact set), so `variance` is the genuine variance.
-/

/-- Zhang, (36): `Z_b = ∫_K e^{−⟨b,x⟩} dx`. -/
noncomputable def logAffineZ {D : ℕ} (K : Set (Euc D)) (b : Euc D) : ℝ :=
  ∫ x in K, Real.exp (-⟪b, x⟫)

/-- Zhang, (36): the log-affine law `π_b(dx) = Z_b^{−1} e^{−⟨b,x⟩} 1_K(x) dx`. -/
noncomputable def logAffineMeasure {D : ℕ} (K : Set (Euc D)) (b : Euc D) : Measure (Euc D) :=
  (volume.restrict K).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-⟪b, x⟫) / logAffineZ K b))

/-- Zhang, (36), (65): `Z_{b,Λ} = h^D Σ_{z ∈ K ∩ hℤ^D} e^{−⟨b,z⟩}`. -/
noncomputable def latticeZ {D : ℕ} (K : Set (Euc D)) (h : ℝ) (b : Euc D) : ℝ :=
  h ^ D * latSum K h (fun z => Real.exp (-⟪b, z⟫))

/-- Zhang, (36), (65): the lattice law `π_{b,Λ}(z) = h^D e^{−⟨b,z⟩}/Z_{b,Λ}` on `K ∩ hℤ^D`. -/
noncomputable def latticeLaw {D : ℕ} (K : Set (Euc D)) (h : ℝ) (b : Euc D) (z : Euc D) : ℝ :=
  h ^ D * Real.exp (-⟪b, z⟫) / latticeZ K h b

/-- Zhang, App. B.2, p.62: the lattice cell `Q_Λ = h[−1/2, 1/2)^D`. -/
def cellQ (D : ℕ) (h : ℝ) : Set (Euc D) :=
  {e | ∀ i, -(h / 2) ≤ e i ∧ e i < h / 2}

/-- Zhang, Lemma B.2, p.63: the law `π̃_Λ` of `X_Λ + E` with `X_Λ ∼ π_{b,Λ}` and `E` uniform on
`Q_Λ`, independent: `Σ_{z ∈ K ∩ hℤ^D} π_{b,Λ}(z) · h^{−D} · Lebesgue restricted to z + Q_Λ`. -/
noncomputable def smoothedLatticeMeasure {D : ℕ} (K : Set (Euc D)) (h : ℝ) (b : Euc D) :
    Measure (Euc D) :=
  Measure.sum fun k : {k : Fin D → ℤ // latticePt h k ∈ K} =>
    ENNReal.ofReal (latticeLaw K h b (latticePt h k.1) / h ^ D) •
      volume.restrict ((fun e => latticePt h k.1 + e) '' cellQ D h)

/-- Zhang, §2.3, p.23: total variation `d_TV(µ, ν) = sup_A |µ(A) − ν(A)|` over measurable `A`. -/
noncomputable def measTV {D : ℕ} (μ ν : Measure (Euc D)) : ℝ :=
  ⨆ A : {A : Set (Euc D) // MeasurableSet A}, |(μ A.1).toReal - (ν A.1).toReal|

/-- `uᵀ Cov_µ(X) u = Var_µ(⟨u, X⟩)`, the covariance quadratic form of `µ` in direction `u`. -/
noncomputable def dirVariance {D : ℕ} (μ : Measure (Euc D)) (u : Euc D) : ℝ :=
  variance (fun x => ⟪u, x⟫) μ

/-- `uᵀ A u` for a rational `D × D` matrix `A`. -/
noncomputable def quadForm {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ) (u : Euc D) : ℝ :=
  ∑ i, ∑ j, u i * ((A i j : ℚ) : ℝ) * u j

end QVolKLS


