-- Prove2me | Definitions.Def_MatSemiBurnside_rowKer
-- name    : MatSemiBurnside_rowKer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:37:21.59423+00:00
-- url     : https://prove2.me/theorems/3cbe3234-1751-47ae-a288-48e0019692ce
-- title:
--   Row kernel and row image of a matrix
-- statement:
--   Let $d$ be a positive integer. For $a\in\mathrm{Mat}_d(\mathbb Q)$, matrices act on **row vectors**: $a$ defines the linear map $x\mapsto xa$ on $\mathbb Q^d$. Its kernel and image are
--   $$\ker(a)=\{x\in\mathbb Q^d : xa=0\},\qquad \operatorname{im}(a)=\{xa : x\in\mathbb Q^d\}.$$
--
--   These are the kernel and image used throughout the paper: in the definition of stable sets, in the rank formula (7) and in Claim A.2, where a rank-preserving product keeps the kernel of its first factor and the image of its last.
--
--   **Formalization Note** `rowKer a` and `rowIm a` are the kernel and range of `Matrix.vecMulLinear a`, the map $x\mapsto x\,a$ on `Fin d → ℚ`.
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, p.6

import Mathlib
set_option autoImplicit false

namespace MatSemiBurnside

/-- **Row kernel of a matrix.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, p.6: "Given a ∈ Matd(F), write ker(a) and im(a) for the
kernel and image of the linear transformation x ↦ xa on F^d, respectively."

`rowKer a` is the kernel of the row action `x ↦ x ᵥ* a` on `Fin d → ℚ`.

**Formalization Note.** Matrices act on row vectors (`Matrix.vecMulLinear`), as on p.6 and in
Appendix A ("Throughout the appendix, matrices act on row vectors"). -/
noncomputable def rowKer {d : ℕ} (a : Matrix (Fin d) (Fin d) ℚ) : Submodule ℚ (Fin d → ℚ) :=
  LinearMap.ker (Matrix.vecMulLinear a)

/-- **Row image of a matrix.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, p.6: the image of the linear transformation `x ↦ xa`
on ℚ^d (row vectors). -/
noncomputable def rowIm {d : ℕ} (a : Matrix (Fin d) (Fin d) ℚ) : Submodule ℚ (Fin d → ℚ) :=
  LinearMap.range (Matrix.vecMulLinear a)

end MatSemiBurnside


