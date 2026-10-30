-- Prove2me | Definitions.Def_HayashiHoeffding_tensorPowBundle
-- name    : HayashiHoeffding_tensorPowBundle
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:12.732196+00:00
-- url     : https://prove2.me/theorems/245b5f23-8d54-410a-9e8a-d2f0ce390de7
-- title:
--   Hilbert-space tensor powers $\mathcal H^{\otimes n}$ (bundled)
-- statement:
--   Let $\mathcal H$ be a complex Hilbert space. Its **Hilbert-space tensor powers** are defined recursively: $\mathcal H^{\otimes 1} = \mathcal H$, and $\mathcal H^{\otimes (n+1)}$ is the completion of the algebraic tensor product $\mathcal H^{\otimes n} \otimes \mathcal H$ for the inner product
--
--   $$\langle x \otimes y, x' \otimes y' \rangle = \langle x, x' \rangle \, \langle y, y' \rangle .$$
--
--   Each $\mathcal H^{\otimes n}$ is a complex Hilbert space in which the elementary tensors $x_1 \otimes \cdots \otimes x_n$ span a dense subspace. These are the spaces $\mathcal H^{\otimes n}$ on which the $n$-copy hypotheses $\rho^{\otimes n}$, $\sigma^{\otimes n}$ and the tests act.
--
--   **Formalization Note** The $k$-th entry of the family is $\mathcal H^{\otimes (k+1)}$: copies are indexed $k \mapsto k+1$, which avoids the zero-copy space $\mathbb C$ (in another universe). The completion is essential: in infinite dimension the algebraic tensor product is not complete.
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, "Formulation and main results", p.2

import Mathlib
import Definitions.Def_HayashiHoeffding_HilbertBundle

open scoped TensorProduct

namespace HayashiHoeffding

universe u

/-- The Hilbert-space tensor powers of a complex Hilbert space `H`, bundled: the `k`-th entry
models `H^{⊗(k+1)}`. The entry at `0` is `H` itself, and the entry at `k + 1` is the
**completion** of the algebraic tensor product of the entry at `k` with `H`, carrying Mathlib's
inner product `⟪x ⊗ y, x' ⊗ y'⟫ = ⟪x, x'⟫ ⟪y, y'⟫` (`TensorProduct.instInnerProductSpace`). The
completion is a complex Hilbert space in which the elementary tensors span a dense subspace.

Hayashi, arXiv:quant-ph/0611013v2, "Formulation and main results", p.2: "ρ⊗n and σ⊗n are the
nth tensor powers of arbitrarily given density operators ρ and σ on H", acting on `H⊗n`.

**Formalization Note.** Copies are indexed `k ↦ k + 1`: the entry at `k` is `H^{⊗(k+1)}`, so
the paper's `n` corresponds to `k + 1` (this avoids the zero-copy space `ℂ`, which lives in a
different universe from `H`). The completion is essential: the algebraic tensor product of
infinite-dimensional spaces is not complete. -/
noncomputable def tensorPowBundle (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : ℕ → HilbertBundle.{u}
  | 0 => HilbertBundle.mk H
  | k + 1 => HilbertBundle.mk (UniformSpace.Completion ((tensorPowBundle H k).carrier ⊗[ℂ] H))

end HayashiHoeffding


