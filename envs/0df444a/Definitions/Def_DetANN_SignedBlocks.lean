-- Prove2me | Definitions.Def_DetANN_SignedBlocks
-- name    : DetANN_SignedBlocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:25:46.542209+00:00
-- url     : https://prove2.me/theorems/6a428674-103f-4fb8-9479-45319e6b9422
-- title:
--   Signed Hadamard blocks, the parameters $p_0$, $L$, and the potential $\Phi$
-- statement:
--   For a $d\times d$ matrix $h$ (in the paper the unnormalized Walsh–Hadamard matrix, entries $\pm1$), an integer $L$ and signs $\xi^{(1)},\dots,\xi^{(L)}\in\{-1,+1\}^d$, the **signed blocks** $A_j:\mathbb R^d\to\mathbb R^L$ are
--
--   $$(A_jz)_\ell=(Ld)^{-1/2}\sum_{r=1}^dh_{jr}\xi^{(\ell)}_rz_r .$$
--
--   For a finite set $\mathcal D$ of $N$ nonzero vectors put $p_0=\lceil\log_4(8Nd)\rceil$, $L=\lceil C_0\tau^{-2}p_0\rceil$, $r_v=\|v\|_2^2$, and
--
--   $$\Phi=\sum_{v\in\mathcal D}\sum_{j=1}^d\Big(\frac{d\|A_jv\|_2^2-r_v}{\tau r_v}\Big)^{2p_0}.\qquad(24)$$
--
--   These are the objects of the deterministic block construction (Theorem 3.2).
--
--   **Formalization Note** Signs are booleans ($\mathtt{true}\mapsto+1$, $\mathtt{false}\mapsto-1$). The properties of $h$ that a theorem needs are its hypotheses.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), §6.1, p.14; §6.3, p.15 ((24))

import Mathlib

namespace DetANN

/-!
# Signed Hadamard blocks and the potential of §6

Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), §6.1, p.14 (the blocks) and §6.3, p.15 (the parameters
`p₀`, `L` and the potential (24)).

**Formalization Note.**
* Signs are booleans, `signOf true = 1`, `signOf false = −1`; a sign assignment is
  `ξ : Fin L → Fin d → Bool`, with `ξ ℓ r` the paper's `ξ^(ℓ)_r`. "Independent uniform signs" is the
  uniform average over all `2^{Ld}` assignments.
* The blocks are built from an arbitrary real `d × d` matrix `h` (the paper's unnormalized
  Walsh–Hadamard matrix, entries `h_{jr} ∈ {−1, +1}`): `(A_j z)_ℓ = (Ld)^{−1/2} ∑_r h_{jr} ξ^(ℓ)_r z_r`,
  i.e. `A_j = (Ld)^{−1/2} B_j`. The properties of `h` that a theorem needs are its hypotheses.
* `(Ld)^{−1/2}` is written `(√(L·d))⁻¹`.
* `p₀ = ⌈log₄(8Nd)⌉` uses `Real.logb 4` and `Nat.ceil`; `L = ⌈C₀ τ^{−2} p₀⌉` uses `Nat.ceil`.
* In the potential, `r_v = ‖v‖²`; the theorems assume every `v ∈ 𝒟` is nonzero, so no division by
  zero occurs.
-/

/-- The sign `+1` or `−1` encoded by a boolean. -/
def signOf (b : Bool) : ℝ := if b then 1 else -1

/-- The signed Hadamard blocks `A_j : ℝ^d → ℝ^L`,
`(A_j z)_ℓ = (Ld)^{−1/2} ∑_r h_{jr} ξ^(ℓ)_r z_r` (§6.1, p.14). -/
noncomputable def signedBlocks {d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (L : ℕ)
    (ξ : Fin L → Fin d → Bool) (j : Fin d) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin L) :=
  Matrix.toEuclideanLin (Matrix.of fun (ℓ : Fin L) (r : Fin d) =>
    (Real.sqrt ((L : ℝ) * d))⁻¹ * (h j r * signOf (ξ ℓ r)))

/-- `p₀ = ⌈log₄(8Nd)⌉` (§6.3, p.15). -/
noncomputable def momentOrder (N d : ℕ) : ℕ := ⌈Real.logb 4 (8 * N * d)⌉₊

/-- `L = ⌈C₀ τ^{−2} p₀⌉` (§6.3, p.15). -/
noncomputable def numReps (C₀ τ : ℝ) (p₀ : ℕ) : ℕ := ⌈C₀ * (τ ^ 2)⁻¹ * p₀⌉₊

/-- The potential (24): `Φ = ∑_{v ∈ 𝒟} ∑_j ((d ‖A_j v‖² − r_v)/(τ r_v))^{2p₀}` with `r_v = ‖v‖²`. -/
noncomputable def potential {d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (L : ℕ)
    (ξ : Fin L → Fin d → Bool) (τ : ℝ) (p₀ : ℕ) (D : Finset (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ∑ v ∈ D, ∑ j : Fin d,
    (((d : ℝ) * ‖signedBlocks h L ξ j v‖ ^ 2 - ‖v‖ ^ 2) / (τ * ‖v‖ ^ 2)) ^ (2 * p₀)

end DetANN


