-- Prove2me | Definitions.Def_KelnerLinSolve_kappa2
-- name    : KelnerLinSolve_kappa2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:41.365878+00:00
-- url     : https://prove2.me/theorems/57567f2f-4bd2-4a34-a544-26a7b7ad725d
-- title:
--   Norms, the spectral condition number $\kappa_2(A)$ and $\rho$
-- statement:
--   For $v \in \mathbb R^n$, $\|v\|_2 = (\sum_i v_i^2)^{1/2}$ and $\|v\|_\infty = \max_i |v_i|$. For $A \in \mathbb R^{n\times n}$, $\max_{i,j}|A_{ij}|$ is its largest absolute entry, and
--
--   $$
--   \kappa_2(A) = \|A\|_2\,\|A^{-1}\|_2 ,
--   $$
--
--   where $\|\cdot\|_2$ is the $\ell_2$ operator (spectral) norm. For $n, E \in \mathbb N$ and $\kappa \ge 1$,
--
--   $$
--   \rho(n, E, \kappa) = 1 + E + \lceil \log_2 \kappa \rceil + \lceil \log_2(n+1) \rceil .
--   $$
--
--   The parameter $\rho$ at $\kappa = \kappa_2(A)$ and $\varepsilon = 2^{-E}$ governs the cost of the main theorem.
--
--   **Formalization Note** The spectral norm is `WainwrightHDS.EigPert.opNorm2` (the norm of `Matrix.toEuclideanCLM`), not an entrywise or Frobenius norm. $\lceil\log_2\kappa\rceil$ is `⌈Real.logb 2 κ⌉₊`, the page's ceiling because $\kappa_2(A)\ge1$ for nonsingular $A$ and $n\ge1$; $\lceil\log_2(n+1)\rceil$ is `Nat.clog 2 (n+1)`. Every statement using $\kappa_2(A)$ assumes $A$ nonsingular.
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), §1.1, p.3; Theorem 1.1, p.3; Lemma 3.4, p.11

import Mathlib
import Definitions.Def_WainwrightHDS_EigPert_opNorm2

namespace KelnerLinSolve

/-- The Euclidean norm `‖v‖₂ = (∑ᵢ vᵢ²)^{1/2}` of a real vector (Kelner, sha256 d1af55cb…, §1.1,
p.3, Theorem 1.1). -/
noncomputable def norm2 {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- The max norm `‖v‖_∞ = maxᵢ |vᵢ|` of a real vector (Kelner, sha256 d1af55cb…, Lemma 3.4, p.11).

**Formalization Note.** A supremum over the finite index set `Fin n` of the nonnegative reals
`|vᵢ|`; it is attained for `n ≥ 1`, and is `0` for `n = 0`. -/
noncomputable def infNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ((Finset.univ.sup fun i => ‖v i‖₊ : NNReal) : ℝ)

/-- The largest absolute entry `max_{i,j} |A_{ij}|` of a real square matrix (Kelner,
sha256 d1af55cb…, Lemma 3.4, p.11, and §4.1, p.12). A finite supremum of nonnegative reals; `0` for
`n = 0`. -/
noncomputable def maxAbsEntry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ((Finset.univ.sup fun p : Fin n × Fin n => ‖A p.1 p.2‖₊ : NNReal) : ℝ)

/-- The **spectral condition number** `κ₂(A) = ‖A‖₂ ‖A⁻¹‖₂` (Kelner, sha256 d1af55cb…, §1.1, p.3),
with `‖·‖₂` the ℓ₂ operator norm (`WainwrightHDS.EigPert.opNorm2`, the norm of
`Matrix.toEuclideanCLM`).

**Formalization Note.** `A⁻¹` is Mathlib's `Matrix.inv`, the true inverse when `det A ≠ 0`. Every
statement of the mission that uses `kappa2 A` assumes `A` nonsingular (the value `0` of a singular
matrix's `A⁻¹` is never used). -/
noncomputable def kappa2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  WainwrightHDS.EigPert.opNorm2 A * WainwrightHDS.EigPert.opNorm2 A⁻¹

/-- `ρ = 1 + E + ⌈log₂ κ⌉ + ⌈log₂(n + 1)⌉` (Kelner, sha256 d1af55cb…, Theorem 1.1, p.3), as a
function of `n`, `E` and `κ`; the mission applies it at `κ = κ₂(A)`.

**Formalization Note.** `⌈log₂ κ⌉` is `⌈Real.logb 2 κ⌉₊`; it is the page's ceiling because
`κ₂(A) ≥ 1` for every nonsingular `A` with `n ≥ 1`, so `log₂ κ ≥ 0`. `⌈log₂(n + 1)⌉` is
`Nat.clog 2 (n + 1)`, exact on naturals. -/
noncomputable def rho (n E : ℕ) (κ : ℝ) : ℕ :=
  1 + E + ⌈Real.logb 2 κ⌉₊ + Nat.clog 2 (n + 1)

end KelnerLinSolve


