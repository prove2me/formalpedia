-- Prove2me | Definitions.Def_PartialHomog_Threshold_ProductGates
-- name    : PartialHomog_Threshold_ProductGates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:27:12.308035+00:00
-- url     : https://prove2.me/theorems/498e2807-3449-4000-93c2-a3447eb8bd77
-- title:
--   Removable product gates, product gates that multiply two affine functions, and the space $V=\operatorname{span}\{\hat q^{[\ge 2]}\}$ (§E.2)
-- statement:
--   Let $\Phi$ be a circuit over a commutative ring $R$.
--
--   1. A product gate is **removable** if it computes $0$ or has at most one input edge carrying a non-constant polynomial, inputs counted with multiplicity.
--   2. A product gate **multiplies two affine functions** (has exactly two non-constant inputs, both affine) if, among its inputs counted with multiplicity, exactly two compute non-constant polynomials, both of total degree at most $1$, and all other inputs compute constants.
--   3. For the product gates $q$ of $\Phi$,
--   $$V=\operatorname{span}_R\{\hat q^{[\ge 2]} : q\text{ a product gate of }\Phi\}.$$
--
--   **Formalization Note** The inputs of product gate `v` are the entries of the list `Φ.prodInputs v`, indexed by `Fin (Φ.prodInputs v).length`; "at most one non-constant input" is: of any two distinct positions, at least one computes a constant. `MultipliesTwoAffine` asks for two distinct positions `i ≠ j` that are non-constant and affine, with every other position constant; it is false for a gate that is not a product gate. `numRemovable` counts removable gates.
-- source:
--   Spiizer, Partial Homogenization and the Structure of Optimal Algebraic Algorithms, STOC 2027 submission (manuscript sha256 33096d05…), p. 26 (PDF 28), §E.2 (removable gates) and Lemma E.13; p. 27 (PDF 29), proof of Lemma E.13 (V)

import Mathlib
import Definitions.Def_PartialHomog_Threshold_Components
import Definitions.Def_PartialHomog_Threshold_Circuit

/-!
# Removable product gates, gates multiplying two affine functions, and the space `V`

Spiizer, *Partial Homogenization and the Structure of Optimal Algebraic Algorithms*,
STOC 2027 submission, §E.2 (pp. 26–28): removable gates (p. 26), Lemma E.13 (p. 26) and its
proof (p. 27).

Inputs of a product gate are counted with multiplicity: they are the entries of the gate's
input list `Φ.prodInputs v`, indexed by `Fin (Φ.prodInputs v).length`.
-/

namespace PartialHomog.Threshold

open MvPolynomial

namespace Circuit

variable {R : Type*} [CommRing R] {N K : ℕ}

/-- A product gate is **removable** if it computes `0` or has at most one input edge carrying a
non-constant polynomial (inputs counted with multiplicity: of any two distinct entries of its
input list, at least one computes a constant). -/
def IsRemovable (Φ : Circuit R N K) (v : Fin Φ.size) : Prop :=
  Φ.IsProdGate v ∧
    (Φ.value v = 0 ∨
      ∀ i j : Fin (Φ.prodInputs v).length, i ≠ j →
        IsConstPoly (Φ.value (Φ.prodInputs v)[i]) ∨ IsConstPoly (Φ.value (Φ.prodInputs v)[j]))

/-- The number of removable product gates of `Φ`. -/
noncomputable def numRemovable (Φ : Circuit R N K) : ℕ :=
  open Classical in (Finset.univ.filter fun v => Φ.IsRemovable v).card

/-- The product gate `v` **multiplies two affine functions** (has exactly two non-constant
inputs, both affine): its input list, counted with multiplicity, has exactly two entries that
compute non-constant polynomials, both of total degree at most one, and every other entry
computes a constant. False for a gate that is not a product gate. -/
def MultipliesTwoAffine (Φ : Circuit R N K) (v : Fin Φ.size) : Prop :=
  ∃ i j : Fin (Φ.prodInputs v).length, i ≠ j ∧
    ¬ IsConstPoly (Φ.value (Φ.prodInputs v)[i]) ∧ ¬ IsConstPoly (Φ.value (Φ.prodInputs v)[j]) ∧
    IsAffine (Φ.value (Φ.prodInputs v)[i]) ∧ IsAffine (Φ.value (Φ.prodInputs v)[j]) ∧
    ∀ l : Fin (Φ.prodInputs v).length, l ≠ i → l ≠ j → IsConstPoly (Φ.value (Φ.prodInputs v)[l])

/-- `V = span_R {q̂^{[≥2]} : q a product gate of Φ}`, the span of the parts of degree at least
two of the product gates. -/
noncomputable def spanV (Φ : Circuit R N K) : Submodule R (MvPolynomial (Fin N) R) :=
  Submodule.span R ((fun q => partGe 2 (Φ.value q)) '' (Φ.prodGates : Set (Fin Φ.size)))

end Circuit

end PartialHomog.Threshold


