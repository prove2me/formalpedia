-- Prove2me | Definitions.Def_SymCircMM_WCircuit_IsBilinear
-- name    : SymCircMM_WCircuit_IsBilinear
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:31:34.593565+00:00
-- url     : https://prove2.me/theorems/17b2fc5e-ff11-452c-8fd8-2a0351522654
-- title:
--   Bilinear circuits and the shape of Figure 1
-- statement:
--   Partition the input variables into the $A$-variables and the $B$-variables. A weighted circuit is **bilinear** (Definition 4.1) if every gate computes a linear form in the $A$'s, a linear form in the $B$'s, or a bilinear form, i.e. a polynomial whose monomials all have bidegree $(1,0)$, all $(0,1)$, or all $(1,1)$.
--
--   The bilinear circuit has **the form of Figure 1** if every product gate $g$ has exactly two inputs, each joined by a single edge: a gate $L$ computing a linear form in the $A$'s and a gate $R$ computing a linear form in the $B$'s, so that $\hat g=\hat L\cdot\hat R$.
--
--   Proposition 4.2 reduces every symmetric circuit for $\mathrm{MM}_n$ to this shape; the lower bound is proved by counting its product gates.
--
--   **Formalization Note** Linear and bilinear forms are weighted homogeneous polynomials of weights $(1,0)$, $(0,1)$, $(1,1)$ for the bidegree weight; the zero polynomial has every weight and a nonzero constant has none, so a bilinear circuit has no nonzero constant gate.
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Definition 4.1, p.10 (PDF p.11); §4.2 feature (i) and Figure 1, pp.10–11 (PDF pp.11–12)

import Mathlib
import Definitions.Def_SymCircMM_WCircuit
import Definitions.Def_SymCircMM_MMVar

set_option autoImplicit false

namespace SymCircMM

variable {F ι γ : Type} [Field F]

/-- A **bilinear circuit** with respect to the partition of the inputs into the `A`- and the
`B`-variables (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript
(sha256 999a7eba…), Definition 4.1, p.10 (PDF p.11)): every gate computes a linear form in the `A`'s
(bidegree `(1, 0)`), a linear form in the `B`'s (bidegree `(0, 1)`), or a bilinear form (bidegree
`(1, 1)`).

**Formalization Note.** Linear and bilinear forms are the weighted homogeneous polynomials of weight
`(1,0)`, `(0,1)`, `(1,1)` for `bideg`; the zero polynomial is all three, a nonzero constant none. -/
def WCircuit.IsBilinear [Fintype γ] (C : WCircuit F (MMVar ι) γ) : Prop :=
  ∀ g, MvPolynomial.IsWeightedHomogeneous bideg (C.val g) (1, 0) ∨
    MvPolynomial.IsWeightedHomogeneous bideg (C.val g) (0, 1) ∨
    MvPolynomial.IsWeightedHomogeneous bideg (C.val g) (1, 1)

/-- The bilinear circuit has **the form of Figure 1** (§4.1–4.2, pp.10–11 (PDF pp.11–12), feature (i)):
every product gate has exactly two inputs, each with an edge of multiplicity one, a gate `L` computing
a linear form in the `A`'s and a gate `R` computing a linear form in the `B`'s, so that it computes
`L · R`. -/
def WCircuit.IsFigure1 [Fintype γ] (C : WCircuit F (MMVar ι) γ) : Prop :=
  ∀ g, (C.label g).isMul = true → ∃ l r : γ, l ≠ r ∧ C.wire g l = 1 ∧ C.wire g r = 1 ∧
    (∀ c, c ≠ l → c ≠ r → C.wire g c = 0) ∧
    MvPolynomial.IsWeightedHomogeneous bideg (C.val l) (1, 0) ∧
    MvPolynomial.IsWeightedHomogeneous bideg (C.val r) (0, 1)

end SymCircMM


