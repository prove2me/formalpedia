-- Prove2me | Definitions.Def_FourierRankQLB_eigenangles
-- name    : FourierRankQLB_eigenangles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:54.12914+00:00
-- url     : https://prove2.me/theorems/4046ea61-1f18-4b23-93ef-c1d803d3f89e
-- title:
--   The positive eigenangles of an orthogonal matrix
-- statement:
--   The nonreal eigenvalues of a real orthogonal matrix come in rotation pairs $e^{\pm i\theta}$. The **positive eigenangles** of $Q$ are the angles $\theta$ representing these pairs, one per pair, with multiplicity.
--
--   Lemma 3.7 gives their expected density under $\mu_{n,\pm}$.
--
--   **Formalization Note** A pair is represented by the eigenvalue with positive imaginary part, so $\theta\in(0,\pi)$, and a real eigenvalue contributes no angle. Matrices with eigenvalues $\pm1$ beyond the forced ones are Haar-null on each component.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §3.3, p.20

import Mathlib
import Definitions.Def_FourierRankQLB_eigenvaluesC

namespace FourierRankQLB

/-- The positive eigenangles of `Q`: one angle `θ` per rotation pair `e^{±iθ}` of nonreal eigenvalues.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §3.3, p. 20 ("The nonreal eigenvalues of a real orthogonal matrix come in rotation pairs
`e^{±iθ}`. We represent each pair by an angle `θ ∈ [0, π]`").

**Formalization Note.** A pair is represented by its eigenvalue with positive imaginary part, whose
argument lies in `(0, π)`. The real eigenvalues `±1` contribute no angle. On each component of `O(2N)`
the matrices with an eigenvalue `±1` beyond the forced ones form a Haar-null set, so this convention
changes no expectation in Lemma 3.7. -/
noncomputable def eigenangles {d : ℕ} (Q : Od d) : Multiset ℝ :=
  ((eigenvaluesC Q).filter fun z => 0 < z.im).map Complex.arg

end FourierRankQLB


