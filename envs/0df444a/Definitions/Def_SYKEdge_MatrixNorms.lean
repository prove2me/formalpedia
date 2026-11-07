-- Prove2me | Definitions.Def_SYKEdge_MatrixNorms
-- name    : SYKEdge_MatrixNorms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:04:57.246242+00:00
-- url     : https://prove2.me/theorems/f75a5ac0-9c25-40f6-a05e-5f3c54dfddf7
-- title:
--   Normalized trace, Hilbert–Schmidt norm, operator norm, $\lambda_{\max}$ and $\lambda_{\min}$ of complex matrices
-- statement:
--   For an $N\times N$ complex matrix $A$ (rows and columns indexed by a finite set $\iota$, $N=|\iota|$) the paper uses:
--
--   1. the **normalized trace** $\operatorname{tr}(A)=\operatorname{Tr}(A)/N$, so that $\operatorname{tr}(\mathrm{Id})=1$;
--   2. the normalized **Hilbert–Schmidt norm** $\|A\|_{HS}=\sqrt{\operatorname{tr}(A^*A)}$;
--   3. the **operator norm** $\|A\|_{op}=\sup_{\|v\|_2=1}\|Av\|_2$ on $\mathbb C^N$ with the Euclidean norm;
--   4. the extreme Rayleigh quotients
--   $$\lambda_{\max}(A)=\sup_{\|v\|_2=1}\operatorname{Re}\langle v,Av\rangle,\qquad \lambda_{\min}(A)=\inf_{\|v\|_2=1}\operatorname{Re}\langle v,Av\rangle ,$$
--   which for Hermitian $A$ are its largest and smallest eigenvalues.
--
--   These are the norms and spectral quantities in which every bound of the mission is stated: $\mathbb E\|H_{SYK}\|_{op}$, the ground-state quantity $\mathbb E\lambda_{\max}(H_{SYK})$, and the leakage parameters $\rho^\pm$ of the sign matrix.
--
--   **Formalization Note** The operator norm is the norm of the matrix acting on `EuclideanSpace ℂ ι`. For nonempty $\iota$ the Rayleigh quotient is bounded by $\|A\|_{op}$ on the unit sphere, so the supremum is a genuine one; every use in the mission has $N\ge1$.
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, §3 'Miscellaneous', p.15; λmax in Theorem 1.1, p.2 and (18)–(19), p.25

import Mathlib

open Matrix

namespace SYKEdge

/-!
# Normalized trace, Hilbert–Schmidt norm, operator norm, `λ_max` and `λ_min`

A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, §3 "Miscellaneous", p.15; `λ_max` as used in Theorem 1.1, p.2 and (18)–(19), p.25.

**Formalization Note.**
* `ntr A = Tr(A)/N` with `N` the number of rows (the page's normalized trace, `tr(Id) = 1`).
* `hsNorm A = √(tr(A*A))` is the page's normalized Hilbert–Schmidt norm `‖A‖_HS`.
* `opNorm A` is the ℓ²→ℓ² operator norm, the norm of `A` acting on `EuclideanSpace ℂ ι`.
* `lamMax A` (resp. `lamMin A`) is the supremum (resp. infimum) of the Rayleigh quotient
  `re ⟨v, A v⟩` over unit vectors `v ∈ ℂ^ι`. For Hermitian `A` these are the largest and the
  smallest eigenvalue. For nonempty `ι` the unit sphere is nonempty and the quotient is bounded by
  `opNorm A`, so no junk value of `iSup`/`iInf` is used; every use in this mission has nonempty `ι`.
* `vecNorm v = (Σ |v_i|²)^{1/2}` is the Euclidean norm of a vector of `ℂ^ι`.
-/

/-- The normalized trace `tr(A) = Tr(A)/N` (p.15). -/
noncomputable def ntr {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : ℂ :=
  A.trace / (Fintype.card ι : ℂ)

/-- The normalized Hilbert–Schmidt norm `‖A‖_HS = √(tr(A*A))` (p.15). -/
noncomputable def hsNorm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : ℝ :=
  Real.sqrt (ntr (Aᴴ * A)).re

/-- The operator norm `‖A‖_op` of `A` acting on `ℂ^ι` with the Euclidean norm. -/
noncomputable def opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A‖

/-- The Euclidean norm `‖v‖₂ = (Σ_i |v_i|²)^{1/2}` of a vector `v ∈ ℂ^ι`. -/
noncomputable def vecNorm {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖v i‖ ^ 2)

/-- The Rayleigh quotient numerator `re ⟨v, A v⟩ = re (v* A v)`. -/
noncomputable def rayleigh {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  (star v ⬝ᵥ (A *ᵥ v)).re

/-- `λ_max(A) = sup_{‖v‖₂ = 1} re ⟨v, A v⟩`, the largest eigenvalue of a Hermitian `A`. -/
noncomputable def lamMax {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : ℝ :=
  ⨆ v : {v : ι → ℂ // vecNorm v = 1}, rayleigh A v.1

/-- `λ_min(A) = inf_{‖v‖₂ = 1} re ⟨v, A v⟩`, the smallest eigenvalue of a Hermitian `A`. -/
noncomputable def lamMin {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : ℝ :=
  ⨅ v : {v : ι → ℂ // vecNorm v = 1}, rayleigh A v.1

end SYKEdge


