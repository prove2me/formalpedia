-- Prove2me | Definitions.Def_LatticePrepro_Conversions_Padding
-- name    : LatticePrepro_Conversions_Padding
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:09:50.542636+00:00
-- url     : https://prove2.me/theorems/4a8adbb9-16c2-4dfe-81ec-a8fbebea9935
-- title:
--   Padding a word by zero coordinates along an injection (proof of Lemma 3.12)
-- statement:
--   Let $f\colon\iota\hookrightarrow M$ be an injection of coordinate sets and $F$ a semiring.
--
--   **Padding** (`padMap f`) is the $F$-linear map $F^{\iota}\to F^{M}$ that extends a word by zeros:
--   $$(\operatorname{pad}_f y)_{m}=\begin{cases}y_i,&m=f(i),\\0,&m\notin f(\iota).\end{cases}$$
--
--   In the proof of Lemma 3.12 (Appendix B.3) every block of the code of Lemma 3.11 is padded in this way to a size that is a power of two, so that the Walsh–Hadamard transform can be applied blockwise.
--
--   **Formalization Note.** The preimage of $m$ is picked by classical choice; it is unique because $f$ is injective.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), proof of Lemma 3.12 (\label{lem:block-system-lattices}) in Appendix B.3 (\label{subsec:gap-search-proof}); Lean: LatticePrepro/Conversions/Padding.lean, LatticePrepro.padMap

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks

/-!
# Padding codes by zero coordinates

Extension by zero along an injection `f : ι ↪ M` of coordinates, as a linear map
`padMap f : (ι → F) →ₗ[F] (M → F)`. It preserves Hamming weights and distances, binary vectors,
and block sparsity (when `f` respects blocks). This is the padding of the proof of Lemma 3.12,
which makes every block of a code have size a power of two.
-/

namespace LatticePrepro

open Finset

variable {F : Type*} [Semiring F] {ι M : Type*}

open Classical in
/-- Extension by zero along an embedding, as a linear map. -/
noncomputable def padMap (f : ι ↪ M) : (ι → F) →ₗ[F] (M → F) :=
  LinearMap.pi fun m => if h : ∃ i, f i = m then LinearMap.proj h.choose else 0

variable [Fintype ι] [Fintype M] [DecidableEq F]

end LatticePrepro


