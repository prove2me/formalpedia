-- Prove2me | Definitions.Def_OptTwoSrcExt_Supplement_BinField
-- name    : OptTwoSrcExt_Supplement_BinField
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:35:45.071762+00:00
-- url     : https://prove2.me/theorems/0735d1ba-685c-4f21-a14e-8fc29141adc7
-- title:
--   Explicit binary field $\mathbb F_{2^\ell}$ given by a polynomial-time construction machine
-- statement:
--   Let $P_m$ be a machine that, on input $1^\ell$ (the string of $\ell$ ones), prints a list of bits $(p_0,\dots,p_d)$, read as the polynomial $P_\ell(X)=\sum_i p_iX^i\in\mathbb F_2[X]$. The machine **constructs $\mathbb F_{2^\ell}$** if $P_\ell$ has degree exactly $\ell$ and is irreducible over $\mathbb F_2$; then
--   $$\mathbb F_{2^\ell}=\mathbb F_2[X]/(P_\ell)$$
--   is a field with $2^\ell$ elements. Its elements are written in the power basis $1,X,\dots,X^{\ell-1}$: a vector $v\in\mathbb F_2^\ell$ stands for $\sum_{i<\ell}v_iX^i$, an $\ell$-bit string is read the same way, a string of $R\ell$ bits is read as $R$ consecutive field elements, and conversely every element has its $\ell$ coordinate bits. The absolute trace $\mathrm{Tr}_{\mathbb F_{2^\ell}/\mathbb F_2}$ is the usual field trace.
--
--   The paper uses fixed binary bases and deterministic construction of binary fields in fixed characteristic (Shoup). This object pins down the representation, so that a statement such as "explicit maps $G_L,G_R:\{0,1\}^n\to\mathbb F_n^R$" refers to computable bit strings and not to a field known only up to isomorphism.
--
--   **Formalization Note** The quotient ring is defined for every printed polynomial; theorems that use it also assert that the machine constructs the field at every length they use, and that the machine runs in polynomial time.
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), §2.2 "Explicit fields", p.18 (PDF p.20); §3.2.1, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime

namespace OptTwoSrcExt.Supplement

/-- **The polynomial over `𝔽₂` with coefficient list `l`**: `∑ᵢ lᵢ Xⁱ` (`true ↦ 1`). -/
noncomputable def polyOfBits (l : List Bool) : Polynomial (ZMod 2) :=
  ∑ i ∈ Finset.range l.length, Polynomial.monomial i (if l.getD i false then (1 : ZMod 2) else 0)

/-- **The defining polynomial of degree `ℓ` output by a field-construction machine `Pm`**: the
polynomial whose coefficient list is the output of `Pm` on the input `1^ℓ` (unary). -/
noncomputable def fieldPoly (Pm : List (List Bool) → List Bool) (ℓ : ℕ) : Polynomial (ZMod 2) :=
  polyOfBits (Pm [List.replicate ℓ true])

/-- **`Pm` constructs `𝔽_{2^ℓ}`**: the polynomial `fieldPoly Pm ℓ` is irreducible over `𝔽₂` and has
degree exactly `ℓ`, so `𝔽₂[X]/(fieldPoly Pm ℓ)` is a field with `2^ℓ` elements. -/
def IsFieldPolyAt (Pm : List (List Bool) → List Bool) (ℓ : ℕ) : Prop :=
  (fieldPoly Pm ℓ).natDegree = ℓ ∧ Irreducible (fieldPoly Pm ℓ)

/-- **Explicit binary field `𝔽_{2^ℓ}`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), §2.2 "Explicit fields", printed p.18 (PDF p.20): "We use
fixed binary bases and deterministic finite-field construction in fixed characteristic, as in
Shoup [57]. … All such arithmetic is polynomial-time in the displayed binary field degree"; §3.2.1,
printed p.36 (PDF p.38): "Compatible finite fields and their operations can be constructed in
deterministic polynomial time in fixed characteristic [57]."

`BinField Pm ℓ = 𝔽₂[X]/(P_ℓ)` with `P_ℓ = fieldPoly Pm ℓ`, the polynomial whose coefficients a
construction machine `Pm` prints on input `1^ℓ`. When `IsFieldPolyAt Pm ℓ` holds and `Pm` is
polynomial time (`LowErrExt.IsPolyTime Pm`), this is the field `𝔽_{2^ℓ}` given explicitly: its
elements are written in the power basis `1, X, …, X^{ℓ−1}` (`eltOfVec`, `eltBits`).

**Formalization Note.** A field given only up to isomorphism (`GaloisField 2 ℓ` with an unspecified
basis) would make "explicit field-valued map" empty; here the representation is pinned by the machine
`Pm`, quantified together with the maps it serves. The ring `AdjoinRoot P` is defined for every
polynomial; statements using it assert `IsFieldPolyAt Pm ℓ` at every length they use. -/
abbrev BinField (Pm : List (List Bool) → List Bool) (ℓ : ℕ) : Type :=
  AdjoinRoot (fieldPoly Pm ℓ)

/-- **The field element with power-basis coordinates `v`**: `∑_{i<ℓ} vᵢ Xⁱ mod P_ℓ`. When
`fieldPoly Pm ℓ` has degree `ℓ`, this is a bijection `𝔽₂^ℓ ≃ BinField Pm ℓ`. -/
noncomputable def eltOfVec (Pm : List (List Bool) → List Bool) (ℓ : ℕ) (v : Fin ℓ → ZMod 2) :
    BinField Pm ℓ :=
  AdjoinRoot.mk (fieldPoly Pm ℓ) (∑ i : Fin ℓ, Polynomial.C (v i) * Polynomial.X ^ (i : ℕ))

/-- **The field element written by the first `ℓ` bits of `l`** (bits past the end read as `0`). -/
noncomputable def eltOfBits (Pm : List (List Bool) → List Bool) (ℓ : ℕ) (l : List Bool) :
    BinField Pm ℓ :=
  eltOfVec Pm ℓ fun i => if LowErrExt.listOut ℓ l i then 1 else 0

/-- **`R` field elements written consecutively in `R` blocks of `ℓ` bits**: block `r` is bits
`rℓ, …, rℓ + ℓ − 1` of `l`. -/
noncomputable def eltsOfBits (Pm : List (List Bool) → List Bool) (ℓ R : ℕ) (l : List Bool) :
    Fin R → BinField Pm ℓ :=
  fun r => eltOfBits Pm ℓ (l.drop ((r : ℕ) * ℓ))

/-- **Power-basis coordinates of a field element**: the coefficients of the remainder of any
representative modulo `P_ℓ` (independent of the representative). -/
noncomputable def coeffVec (Pm : List (List Bool) → List Bool) (ℓ : ℕ) (z : BinField Pm ℓ) :
    Fin ℓ → ZMod 2 :=
  fun i => ((Function.surjInv (AdjoinRoot.mk_surjective (g := fieldPoly Pm ℓ)) z) %
    fieldPoly Pm ℓ).coeff i

/-- **A field element written as `ℓ` bits** (its power-basis coordinates, `1 ↦ true`). -/
noncomputable def eltBits (Pm : List (List Bool) → List Bool) (ℓ : ℕ) (z : BinField Pm ℓ) :
    List Bool :=
  List.ofFn fun i => decide (coeffVec Pm ℓ z i = 1)

/-- **Absolute trace `Tr_{𝔽_{2^ℓ}/𝔽₂}`** on the explicit field (Mathlib's `Algebra.trace`). -/
noncomputable def absTr (Pm : List (List Bool) → List Bool) (ℓ : ℕ) : BinField Pm ℓ → ZMod 2 :=
  Algebra.trace (ZMod 2) (BinField Pm ℓ)

end OptTwoSrcExt.Supplement


