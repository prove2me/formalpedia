-- Prove2me | Definitions.Def_GaussToomCook_Supplement_IsDivisionFactor
-- name    : GaussToomCook_Supplement_IsDivisionFactor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:54:56.113292+00:00
-- url     : https://prove2.me/theorems/ad9112e0-1d94-4872-a2e9-9f1942d00d40
-- title:
--   The division factor of a matrix
-- statement:
--   Let $A$ be a square matrix with entries in $\mathbb Q(i)$ (represented in $\mathbb C$). A Gaussian integer $\alpha$ **clears the denominators** of $A$ if there is $j\in\mathbb Z_{\ge0}$ such that
--   $$2^j\cdot\alpha\cdot A$$
--   has only Gaussian-integer entries. A **division factor** of $A$ is a nonzero Gaussian integer $\alpha$ that clears the denominators of $A$ and has minimal norm $\mathrm{Nr}(\alpha)$ among all nonzero Gaussian integers that do.
--
--   This is the paper's definition: "the division factor $\alpha$ of a matrix $A$ is the minimal integer (or the Gaussian integer with minimal norm) such that there is $k\in\mathbb Z_{\ge0}$ such that $2^k\cdot\alpha\cdot A$ has only (Gaussian) integer entries." The factor $2^j$ is free because divisions by powers of $2$ are regarded as trivial. The division factor measures the "depth" of the non-trivial divisions of an interpolation matrix.
--
--   **Formalization Note** Two predicates are defined: `IsDenominatorClearing α A` (admissibility) and `IsDivisionFactor α A` (nonzero, admissible, of minimal norm among nonzero admissible elements). $\alpha=0$ clears every matrix and is excluded, as the paper intends. The minimal-norm element is determined only up to a unit, so every associate of it satisfies the predicate. "A Gaussian-integer entry" means an entry equal to the image of some $z\in\mathbb Z[i]$ under `GaussianInt.toComplex`.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §2.2.3, p. 8 (PDF p. 10)

import Mathlib
import Definitions.Def_GaussToomCook_Nr

namespace GaussToomCook.Supplement

/-- **Admissible denominators of a matrix**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*,
manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §2.2.3, p. 8 (PDF 10): a Gaussian integer `α` is
admissible for a matrix `A` when there is `j ∈ ℤ_{≥0}` such that `2^j · α · A` has only Gaussian-integer entries.

**Formalization Note.** `A` has complex entries (the interpolation matrix is the inverse of a Gaussian-integer
matrix, computed over `ℂ`); "a Gaussian-integer entry" means an entry equal to `GaussianInt.toComplex z` for
some `z : ℤ[i]`. -/
def IsDenominatorClearing {n : Type*} (α : GaussianInt) (A : Matrix n n ℂ) : Prop :=
  ∃ j : ℕ, ∀ r c, ∃ z : GaussianInt,
    GaussianInt.toComplex z = 2 ^ j * GaussianInt.toComplex α * A r c

/-- **The division factor of a matrix**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*,
manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §2.2.3, p. 8 (PDF 10): "the division factor `α` of a
matrix `A` is the minimal integer (or the Gaussian integer with minimal norm) such that there is `k ∈ ℤ_{≥0}`
such that `2^k · α · A` has only (Gaussian) integer entries."

**Formalization Note.** `IsDivisionFactor α A` says that `α` is *a* division factor: `α` is nonzero, admissible
(`IsDenominatorClearing`), and has minimal norm `Nr` among nonzero admissible Gaussian integers. `α = 0` is
admissible for every matrix and is excluded, as the paper intends. The minimal-norm element is determined only up
to units, so the predicate is satisfied by every associate of it. -/
def IsDivisionFactor {n : Type*} (α : GaussianInt) (A : Matrix n n ℂ) : Prop :=
  α ≠ 0 ∧ IsDenominatorClearing α A ∧
    ∀ β : GaussianInt, β ≠ 0 → IsDenominatorClearing β A → GaussToomCook.Nr α ≤ GaussToomCook.Nr β

end GaussToomCook.Supplement


