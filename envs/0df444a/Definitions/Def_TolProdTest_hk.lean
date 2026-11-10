-- Prove2me | Definitions.Def_TolProdTest_hk
-- name    : TolProdTest_hk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:25:46.284654+00:00
-- url     : https://prove2.me/theorems/d1f0fd0c-5431-4bc1-b9f1-eb1a27165868
-- title:
--   $h_k(A)=\mathrm{Tr}(Q_kA^{\otimes k})$ and the symmetric projector on $(\mathbb C^D)^{\otimes k}$
-- statement:
--   On a finite-dimensional space $\mathbb C^X$, let $Q_k=\frac1{k!}\sum_{\pi\in S_k}P_\pi$ be the orthogonal projector onto the symmetric subspace $\mathrm{Sym}^k(\mathbb C^X)\subseteq(\mathbb C^X)^{\otimes k}$. For an operator $A$ on $\mathbb C^X$ define
--
--   $$
--   h_k(A)=\mathrm{Tr}\big(Q_k\,A^{\otimes k}\big).
--   $$
--
--   For positive $A$ with eigenvalues $\lambda_i$, $h_k(A)$ is the complete homogeneous symmetric polynomial of degree $k$ in the $\lambda_i$. It is the block-level acceptance probability in the proof of Lemma 3.6.
--
--   The projector $Q_k$ is the published `QMAPlusGap.symProj` (built on the published `OptimalSpectrum.Entangled.permOp`), and $A^{\otimes k}$ the published `ShadowTomography.UpperBound.tensorPow`.
--
--   **Formalization Note** The value is complex; for positive semidefinite $A$ it is real and nonnegative, and statements take its real part where they compare it with reals.
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eqs. (56), (64), pp.15–16

import Mathlib
import Definitions.Def_QMAPlusGap_symProj
import Definitions.Def_ShadowTomography_UpperBound_tensorPow

set_option autoImplicit false

namespace TolProdTest

/-- **`h_k(A) := Tr(Q_k A^{⊗k})`**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (56), p.15:
"For any positive operator A on H_c, define h_k(A) := Tr(Q_{k,c} A^{⊗k})".

The space is `ℂ^X` for a finite basis type `X` (the paper's `H_c`, or `E_c`); `Q_k`, the orthogonal projector
onto `Sym^k(ℂ^X)` (the subspace "invariant under all permutations of the tensor factors", §2.1, p.8), is the
published `QMAPlusGap.symProj k = (1/k!) Σ_{π ∈ S_k} P_π` on the basis `Fin k → X`, and `A^{⊗k}` is the published
`ShadowTomography.UpperBound.tensorPow A k`.

**Formalization Note** The value is a complex number; for positive semidefinite `A` it is real and nonnegative,
and statements comparing it with reals take its real part. -/
noncomputable def hk {X : Type} [Fintype X] [DecidableEq X] (k : ℕ) (A : Matrix X X ℂ) : ℂ :=
  (QMAPlusGap.symProj (ι := X) k * ShadowTomography.UpperBound.tensorPow A k).trace

end TolProdTest


