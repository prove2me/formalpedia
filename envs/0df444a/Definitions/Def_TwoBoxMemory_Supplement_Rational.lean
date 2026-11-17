-- Prove2me | Definitions.Def_TwoBoxMemory_Supplement_Rational
-- name    : TwoBoxMemory_Supplement_Rational
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:12:07.93577+00:00
-- url     : https://prove2.me/theorems/f3c18209-a796-4341-b9c5-b53093ece9b2
-- title:
--   Rational reals, rational controllers, and integer codes for rationals
-- statement:
--   A real number $x$ is **rational** if $x=q$ for some $q\in\mathbb Q$. A controller $(\mu,K_A,K_B)$ with $m$ labels (initial probability row $\mu$, nonnegative joint command/transition matrices with $(K_A+K_B)\mathbf 1=\mathbf 1$) is a **rational controller** when every entry of $\mu$, $K_A$ and $K_B$ is rational.
--
--   For computability statements, a rational is given by an **integer code** $(n,d)\in\mathbb Z\times\mathbb N$, which denotes $n/(d+1)$. Every rational has such a code.
--
--   These notions state the rational density theorem (Theorem C.2), the rational certificates of Theorem C.6, and the effective openness clause of Theorem E.3.
--
--   **Formalization Note** Controllers are the published `TwoBoxMemory.Controller`. The code type $\mathbb Z\times\mathbb N$ carries Mathlib's standard `Primcodable` structure.
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), Theorem C.2, p.29 (PDF 31); §C.3, p.31 (PDF 33)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller

namespace TwoBoxMemory.Supplement

/-!
# Rational reals, rational controllers, and integer codes for rationals

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
Appendix C, Theorem C.2, p.29 (PDF 31) ("`K_A, K_B, µ` rational, at most `M` labels"); §C.3, p.31
(PDF 33).

A controller (the published `TwoBoxMemory.Controller`) is **rational** when every entry of its
initial row `µ` and of its joint matrices `K_A`, `K_B` is a rational number.

**Formalization Note.**
* `IsRat x` says that the real number `x` is the image of a rational.
* `RatCode = ℤ × ℕ` is a concrete code for rationals: `(n, d)` denotes `n / (d + 1)`. Every
  rational has a code (`n / d = (n) / ((d - 1) + 1)` for `d ≥ 1`), and the code type carries
  Mathlib's standard `Primcodable` structure, so computability statements about rational inputs
  and outputs are made over codes rather than over Mathlib's ranking encoding of `ℚ`.
-/

noncomputable section

/-- The real number `x` is rational. -/
def IsRat (x : ℝ) : Prop := ∃ q : ℚ, x = (q : ℝ)

/-- A rational controller: every entry of `µ`, `K_A`, `K_B` is rational (Theorem C.2, p.29). -/
def IsRationalCtrl {m : ℕ} (κ : TwoBoxMemory.Controller m) : Prop :=
  (∀ i, IsRat (κ.μ i)) ∧ ∀ a i j, IsRat (κ.K a i j)

/-- Integer codes of rationals: `(n, d)` denotes `n / (d + 1)`. -/
abbrev RatCode : Type := ℤ × ℕ

/-- The rational denoted by a code. -/
def RatCode.val (c : RatCode) : ℚ := (c.1 : ℚ) / ((c.2 : ℚ) + 1)

end

end TwoBoxMemory.Supplement


