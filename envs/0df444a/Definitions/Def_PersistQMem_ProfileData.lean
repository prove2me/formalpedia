-- Prove2me | Definitions.Def_PersistQMem_ProfileData
-- name    : PersistQMem_ProfileData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:31:51.159707+00:00
-- url     : https://prove2.me/theorems/57c7449e-b547-4275-923e-e80c30602025
-- title:
--   Source profile: $\tau$, $\rho_{j,z}$, the Gram norm $\beta$, the profile $\zeta(q)$ and the budget $B_K$
-- statement:
--   Let $\tau=I_D/D$ be the maximally mixed state on $\mathbb C^D$. The **profile data** (Definition 2.1) are Hermitian matrices $G_1,\dots,G_M\in\mathbb C^{D\times D}$ with $\|G_j\|_{\mathrm{op}}\le1$ and $\operatorname{Tr}(\tau G_j)=0$, and a prior $p_1,\dots,p_M$ with $p_j>0$ and $\sum_jp_j=1$, such that at least one $G_j$ is nonzero. From these data:
--
--   1. the **weighted Gram norm** is the operator norm of a real $M\times M$ matrix,
--   $$\beta=\Big\|\big[\sqrt{p_ip_j}\,\Re\operatorname{Tr}(\tau G_iG_j)\big]_{i,j=1}^M\Big\|_{\mathrm{op}};$$
--   2. the **rank-constrained response profile** is, for $q\ge1$,
--   $$\zeta(q)=\sup\Big\{\sum_{j=1}^Mp_j\operatorname{Tr}(TG_jTG_j)\;:\;T\succeq0,\ \operatorname{Tr}(T^2)=1,\ \operatorname{rank}T\le\min\{q,D\}\Big\};$$
--   3. the **information budget** is $B_K=\zeta(K)+(2K-2)\beta$.
--
--   For a sign $z\in\{-1,1\}$ and $0<\theta<1$ the perturbed source state is $\rho_{j,z}=(I_D+z\theta G_j)/D$ (Theorem 2.2, (4)). The normalisation in $\zeta$ is $\operatorname{Tr}(T^2)=1$, not $\operatorname{Tr}T=1$: the trial matrices are not states.
--
--   These are the quantities in which the copy lower bound of Theorem 2.2 is expressed; they depend only on the observables and the prior.
--
--   **Formalization Note** $\|\cdot\|_{\mathrm{op}}$ is Mathlib's $\ell^2$ operator norm (`opNorm`). $\zeta(q)$ is the `sSup` of the value set `profileSet`; its boundedness and attainment are the milestone `zeta_attained_budget_pos`. $\operatorname{Tr}(TG_jTG_j)$ enters through its real part (it is real). A sign is a Boolean: `zsign true = 1`, `zsign false = -1`. $2K-2$ is computed in $\mathbb R$.
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), Definition 2.1, (1)–(3), p.3 (PDF p.6); Theorem 2.2, (4), p.4 (PDF p.7)

import Mathlib

open scoped Matrix ComplexOrder

namespace PersistQMem

/-- The l2 operator norm `‖A‖_op = sup_{‖v‖ = 1} ‖A v‖` of a matrix over `ℝ` or `ℂ`
(Tao, Shen, *Structural Lower Bounds for Quantum Property Estimation with Persistent Memory*,
STOC 2027 submission, manuscript of 2026-11-03, sha256 6d48ad24…, §5.1, p.13).

**Formalization Note.** Mathlib's l2 operator norm on matrices (a scoped instance, opened only
here so that no global norm on `Matrix` is chosen). -/
noncomputable def opNorm {𝕜 : Type} [RCLike 𝕜] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n 𝕜) : ℝ :=
  open scoped Matrix.Norms.L2Operator in ‖A‖

/-- The maximally mixed state `τ = I_D / D` (Definition 2.1, p.3). -/
noncomputable def tau (D : ℕ) : Matrix (Fin D) (Fin D) ℂ :=
  ((D : ℂ)⁻¹) • (1 : Matrix (Fin D) (Fin D) ℂ)

/-- The sign `z ∈ {−1, 1}` of Theorem 2.2 (p.4), encoded by a Boolean:
`zsign true = 1`, `zsign false = −1`. -/
def zsign (z : Bool) : ℝ := if z then 1 else -1

/-- The perturbed state `ρ_{j,z} = (I_D + zθG_j)/D` of Theorem 2.2, (4), p.4, for one observable
`G = G_j` and a sign `z` (encoded as `Bool`, see `zsign`). -/
noncomputable def rhoAlt {D : ℕ} (θ : ℝ) (G : Matrix (Fin D) (Fin D) ℂ) (z : Bool) :
    Matrix (Fin D) (Fin D) ℂ :=
  ((D : ℂ)⁻¹) • (1 + (((zsign z * θ : ℝ)) : ℂ) • G)

/-- **Definition 2.1 (Source profile), p.3 — the data.** `G_1, …, G_M` are Hermitian `D × D`
matrices with `‖G_j‖_op ≤ 1` and `Tr(τ G_j) = 0`; the prior has `p_j > 0` and `Σ_j p_j = 1`; and at
least one `G_j` is nonzero (Tao, Shen, STOC 2027 submission, manuscript of 2026-11-03,
sha256 6d48ad24…, Definition 2.1, p.3).

**Formalization Note.** Indices are `Fin M`; `‖·‖_op` is the l2 operator norm `opNorm`. -/
structure ProfileData {D M : ℕ} (G : Fin M → Matrix (Fin D) (Fin D) ℂ) (p : Fin M → ℝ) :
    Prop where
  hermitian : ∀ j, (G j).IsHermitian
  opNorm_le : ∀ j, opNorm (G j) ≤ 1
  centered : ∀ j, (tau D * G j).trace = 0
  prior_pos : ∀ j, 0 < p j
  prior_sum : ∑ j, p j = 1
  exists_ne_zero : ∃ j, G j ≠ 0

/-- The weighted tracial Gram matrix `[√(p_i p_j) ℜ Tr(τ G_i G_j)]_{i,j=1}^M` of (1), p.3. -/
noncomputable def gramMatrix {D M : ℕ} (G : Fin M → Matrix (Fin D) (Fin D) ℂ) (p : Fin M → ℝ) :
    Matrix (Fin M) (Fin M) ℝ :=
  Matrix.of fun i j => Real.sqrt (p i * p j) * (tau D * G i * G j).trace.re

/-- The weighted Gram norm `β = ‖[√(p_i p_j) ℜ Tr(τ G_i G_j)]_{i,j}‖_op` of Definition 2.1, (1), p.3:
the l2 operator norm of the real `M × M` matrix `gramMatrix G p`. -/
noncomputable def gramNorm {D M : ℕ} (G : Fin M → Matrix (Fin D) (Fin D) ℂ) (p : Fin M → ℝ) : ℝ :=
  opNorm (gramMatrix G p)

/-- The set of values `Σ_j p_j Tr(T G_j T G_j)` over the feasible matrices of (2), p.3:
`T ⪰ 0`, `Tr(T²) = 1` (Hilbert–Schmidt normalization, not `Tr T = 1`), `rank T ≤ min{q, D}`.

**Formalization Note.** `Tr(T G_j T G_j)` is real for Hermitian `T` and `G_j`; its real part is taken.
The rank is `Matrix.rank` over `ℂ`. -/
def profileSet {D M : ℕ} (G : Fin M → Matrix (Fin D) (Fin D) ℂ) (p : Fin M → ℝ) (q : ℕ) :
    Set ℝ :=
  {v | ∃ T : Matrix (Fin D) (Fin D) ℂ, T.PosSemidef ∧ (T * T).trace = 1 ∧ T.rank ≤ min q D ∧
    v = ∑ j, p j * (T * G j * T * G j).trace.re}

/-- The rank-constrained response profile
`ζ(q) = sup_{T ⪰ 0, Tr(T²) = 1, rank T ≤ min{q, D}} Σ_j p_j Tr(T G_j T G_j)`, `q ≥ 1`
(Definition 2.1, (2), p.3).

**Formalization Note.** `sSup` of `profileSet`; the set is nonempty and bounded above under
`ProfileData` for `q ≥ 1` (§2.1, pp.3–4, milestone `zeta_attained_budget_pos`), so `sSup` is the
paper's supremum. -/
noncomputable def profile {D M : ℕ} (G : Fin M → Matrix (Fin D) (Fin D) ℂ) (p : Fin M → ℝ)
    (q : ℕ) : ℝ :=
  sSup (profileSet G p q)

/-- The information budget `B_K = ζ(K) + (2K − 2)β` of Definition 2.1, (3), p.3, computed in `ℝ`. -/
noncomputable def budget {D M : ℕ} (G : Fin M → Matrix (Fin D) (Fin D) ℂ) (p : Fin M → ℝ)
    (K : ℕ) : ℝ :=
  profile G p K + (2 * (K : ℝ) - 2) * gramNorm G p

end PersistQMem


