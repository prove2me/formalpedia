-- Prove2me | Definitions.Def_FourierEntropyApprox_Supplement_aUCParity
-- name    : FourierEntropyApprox_Supplement_aUCParity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:04:45.636107+00:00
-- url     : https://prove2.me/theorems/b12a34ca-8475-44f4-8863-f2cb20e96a6a
-- title:
--   Unambiguous $b$-parity-certificates and $\mathrm{aUC}^{\oplus}_b(f)$
-- statement:
--   Let $f:\{-1,1\}^n\to\{-1,1\}$ and $b\in\{0,1\}$. An **unambiguous $b$-parity-certificate** $U_b$ for $f$ is a finite set of nonempty, pairwise disjoint affine subspaces of the cube whose union is exactly $f^{-1}((-1)^b)$ (for $b=0$ the inputs with $f=1$, for $b=1$ those with $f=-1$); $f$ is constant on each cell. Its **average cost** is
--
--   $$\mathrm{aUC}^{\oplus}(f,U_b)=\sum_{C\in U_b}\operatorname{co-dim}(C)\,2^{-\operatorname{co-dim}(C)},$$
--
--   which is the uniform average over the whole cube of the codimension of the cell containing $x$, with cost zero off the $b$ side. The **average unambiguous $b$-parity-certificate complexity** is
--
--   $$\mathrm{aUC}^{\oplus}_b(f)=\min_{U_b}\mathrm{aUC}^{\oplus}(f,U_b).$$
--
--   It is the complexity measure of Theorem 4.3; restricting the cells to subcubes gives the ordinary one-sided unambiguous certificate complexity.
--
--   **Formalization Note** Cells are indexed by `Fin m` (with $m=0$ for an empty side) as affine subspaces of $\mathbb F_2^n$ via `cubeSet`, each nonempty. `aUCParity f b` is the infimum in $\mathbb R$ of the costs; for Boolean $f$ the set of costs is finite and nonempty (singleton cells always work), so this is the paper's minimum.
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), §1, p.4 (average cost of a partition of f⁻¹((−1)^b)); §2, pp.11–12 (unambiguous b-certificates, aUC_b, unambiguous ⊕-certificates, aUC⊕_b)

import Mathlib
import Definitions.Def_FourierEntropyApprox_Supplement_cubeSet

set_option autoImplicit false

namespace FourierEntropyApprox

/-!
# Unambiguous b-parity-certificates and the average complexity `aUC⊕_b(f)`

M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), §2, pp.11–12 ("Let U = U₀ ⊔ U₁ be such that, for b ∈ {0, 1}, U_b is an unambiguous
b-certificate, i.e., U_b is a subcube partition of f⁻¹((−1)^b). Then, define aUC(f, U_b) =
(1/2ⁿ) ∑_{x∈U_b} UC(U_b, x) … aUC_b(f) := min_{U_b} aUC(f, U_b) … An unambiguous ⊕-certificate … is defined to
be a collection of monochromatic affine subspaces … Similarly, we define … aUC⊕₀(f), aUC⊕₁(f)"), and §1, p.4
("For b ∈ {0, 1}, consider a partition U_b of f⁻¹((−1)^b) ⊆ {−1, 1}ⁿ into affine subspaces. Its average cost
is ∑_{C∈U_b} co-dim(C)2^{−co-dim(C)}, and minimizing this quantity gives aUC⊕_b(f).").

**Formalization Note.**
* An unambiguous `b`-parity-certificate is a finite family of nonempty affine subspaces (`cubeSet`), indexed
  by `Fin m`, pairwise disjoint, whose union is exactly `f⁻¹((−1)^b)` (`b = 0`: the inputs with `f = 1`;
  `b = 1`: those with `f = −1`). The cells are then automatically monochromatic. `m = 0` is the certificate of
  an empty side.
* Its cost is `∑_C co-dim(C) 2^{−co-dim(C)}` (p.4), which equals the uniform average over the whole cube of
  the codimension of the cell containing `x` (zero off the `b` side), the form of p.12, since an affine
  subspace of codimension `k` has `2^{n−k}` points.
* `aUCParity f b` is the infimum (`sInf` in `ℝ`) of the costs. The set is nonempty for Boolean `f` (singleton
  cells, or the empty family) and bounded below by `0`; it is a finite set of values (finitely many
  partitions), so the infimum is the paper's minimum.
-/

namespace Supplement

/-- An unambiguous `b`-parity-certificate for `f` (pp.11–12): `m` nonempty, pairwise disjoint affine subspaces
of the cube whose union is `f⁻¹((−1)^b)`. -/
structure UnambParityCert {n : ℕ} (f : Cube n → ℝ) (b : Fin 2) where
  /-- number of cells -/
  m : ℕ
  /-- the cells, as affine subspaces of `𝔽₂ⁿ` -/
  cell : Fin m → AffineSubspace (ZMod 2) (Fin n → ZMod 2)
  /-- every cell is nonempty -/
  nonempty : ∀ i, (cubeSet (cell i)).Nonempty
  /-- distinct cells are disjoint -/
  disjoint : ∀ i j, i ≠ j → Disjoint (cubeSet (cell i)) (cubeSet (cell j))
  /-- the cells cover exactly `f⁻¹((−1)^b)` -/
  cover : ∀ x, (∃ i, x ∈ cubeSet (cell i)) ↔ f x = (-1 : ℝ) ^ (b : ℕ)

/-- The average cost `aUC⊕(f, U_b) = ∑_{C ∈ U_b} co-dim(C) 2^{−co-dim(C)}` (p.4; p.12). -/
noncomputable def UnambParityCert.cost {n : ℕ} {f : Cube n → ℝ} {b : Fin 2}
    (U : UnambParityCert f b) : ℝ :=
  ∑ i, (codim (U.cell i) : ℝ) * (2 : ℝ)⁻¹ ^ codim (U.cell i)

/-- The average unambiguous `b`-parity-certificate complexity `aUC⊕_b(f) = min_{U_b} aUC⊕(f, U_b)`
(pp.4, 11–12). -/
noncomputable def aUCParity {n : ℕ} (f : Cube n → ℝ) (b : Fin 2) : ℝ :=
  sInf {c : ℝ | ∃ U : UnambParityCert f b, U.cost = c}

end Supplement

end FourierEntropyApprox


