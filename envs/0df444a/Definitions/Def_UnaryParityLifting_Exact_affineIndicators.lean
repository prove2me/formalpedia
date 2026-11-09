-- Prove2me | Definitions.Def_UnaryParityLifting_Exact_affineIndicators
-- name    : UnaryParityLifting_Exact_affineIndicators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:55.846525+00:00
-- url     : https://prove2.me/theorems/81390c1a-c07b-45f0-b08e-af36009c2f11
-- title:
--   Indicators of affine subspaces, including the empty set
-- statement:
--   Let $V$ be a finite coordinate set and let $A\subseteq\mathbb F_2^V$ be an affine subspace, with the empty affine set allowed. Send a Boolean bit to the corresponding element of $\mathbb F_2$. The affine indicator is
--   $$\mathbf 1_A(x)=\begin{cases}1&x\in A,\\0&x\notin A.\end{cases}$$
--   It is real valued on the Boolean cube. Mathlib's affine-subspace type includes the empty set as its bottom element, whose indicator is zero. The full affine space has indicator one. No restriction on dimension, rank, codimension, or the blocks involved is imposed.
--
--   This is the general affine object used by the affine-to-conical milestone; it does not carry any assumed conical decomposition or error estimate. The Walsh characters, Fourier coefficients and spectral norm used alongside it are the referenced `FourierEntropyApprox` definitions, instantiated over real-valued functions with the identical bit-to-Walsh-sign convention.
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), citation_basis: published; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/567.pdf; p.6, Definition 2.1; pp.10–11, Section 3.2 and Lemma 3.8

import Mathlib
import Definitions.Def_UnaryParityLifting_Exact_certificateSyntax

namespace UnaryParityLifting.Exact

/-- Mathlib affine subspaces include the empty subspace (bottom), needed in Lemma 3.8. -/
noncomputable def affineIndicator {V : Type*}
    (A : AffineSubspace (ZMod 2) (V → ZMod 2)) (x : V → Bool) : ℝ := by
  classical
  exact if (fun v => fieldBit (x v)) ∈ A then 1 else 0

end UnaryParityLifting.Exact


