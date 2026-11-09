-- Prove2me | Definitions.Def_KSPolySign_faceFun
-- name    : KSPolySign_faceFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:36:49.79026+00:00
-- url     : https://prove2.me/theorems/559fef2c-7c06-41aa-82c3-27e0cc35f8e7
-- title:
--   The potential restricted to the face of $y$
-- statement:
--   For a fixed $y$, the function
--   $$x \mapsto P(\mathrm{faceProj}(y,x))$$
--   is the potential as a function of the active coordinates of $y$, with the signed coordinates and the matrix $F$ held fixed. Its derivatives at $y$ are the gradient and Hessian "taken with respect to the active coordinates".
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.5, p.19 (PDF p.19); Lemma 2.7, p.11 (PDF p.11)

import Mathlib
import Definitions.Def_KSPolySign_pot
import Definitions.Def_KSPolySign_faceProj
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The potential on the face of `y`.** `faceFun C F ρ y x = P(faceProj y x)`: the potential as a
function of the active coordinates of `y`, the fixed coordinates and the matrix `F` held fixed.
Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.5, p.19 (PDF p.19): "The matrix F is held fixed during differentiation";
Lemma 2.7, p.11: "The gradient and Hessian are taken with respect to the active coordinates". -/
noncomputable def faceFun {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ)
    (ρ : ℝ) (y x : Fin k → ℝ) : ℝ :=
  pot C F ρ (faceProj y x)

end KSPolySign


