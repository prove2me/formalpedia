-- Prove2me | Definitions.Def_PricingWithTips3DM_0ce3e5e1c7f27e9a1020a44d
-- name    : PricingWithTips3DM_0ce3e5e1c7f27e9a1020a44d
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:19:56.372329+00:00
-- url     : https://prove2.me/theorems/070ca4b8-1fd5-4097-999d-0512ec0a750b
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Cert.Bridge
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Definitions.Def_PricingWithTips3DM_2b9b1ca3b5e0361c4e5bb9c7
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# The bridge: certified reductions

This file connects the two layers of the library:

* the **mathematical layer**, where problems live on structured, bundled
  instance types and reductions are arbitrary Lean functions with correctness
  proofs, and
* the **certificate layer** (`Cert/Language.lean`), where instance
  transformations are programs of the builder language `Code`, polynomial-time
  by construction.

The connection is made on *concrete instances*: each problem gets a
representation over the type universe `Ty` together with a total decoding
function into its bundled instance type. Abstract problems pull back along the
decoding (`Problem.comap`), and a `CertifiedReduction` is a `Code` program
that is correct with respect to these decoded semantics. Every certified
reduction *is* an ordinary reduction (`toReduction`), composes
(`CertifiedReduction.comp`), and carries polynomial cost and output-size
bounds for free (`cost_size_le`).

## Decoding discipline

Decoding must be **total**: every value of the concrete type means *some*
instance, so no well-formedness side conditions infect the reduction
statements. The per-problem encodings and decoders live next to the problem
definitions (`Graph/Encoding.lean`, `Logic/Sat/Encoding.lean`, …); see there
for how junk inputs are given meaning.
-/

namespace Hardness
namespace Cert

/-! ## Certified reductions -/

variable {σ τ ρ : Ty}

/-- A reduction between problems on concrete instances, certified
polynomial-time by construction: the instance map is a program of the builder
language. -/
structure CertifiedReduction (P : Problem σ.denote) (Q : Problem τ.denote) where
  /-- The instance map, as a program. -/
  code : Code σ τ
  /-- The program is a correct reduction. -/
  correct : ∀ x, P x ↔ Q (code.eval x)

namespace CertifiedReduction

variable {P : Problem σ.denote} {Q : Problem τ.denote} {R : Problem ρ.denote}

/-- Every certified reduction is in particular a plain reduction. -/
def toReduction (r : CertifiedReduction P Q) : P ⟶ᵣ Q :=
  ⟨r.code.eval, r.correct⟩

/-- Certified reductions compose; the certificate of the composite is the
composite program. -/
def comp (r : CertifiedReduction P Q) (s : CertifiedReduction Q R) :
    CertifiedReduction P R where
  code := .comp r.code s.code
  correct x := (r.correct x).trans (s.correct _)

/-- Weakening a restriction, certified: with a program deciding the side
condition and a fixed no-instance to send offenders to, `P.restrict R`
reduces to `P` — `Reduction.ofRestrict` at the certificate level. The
decidability that `ofRestrict` demands of the promise sharpens, here, into
*computability by a program of the builder language*. -/
def ofRestrict {R : σ.denote → Prop} (d : Code σ .bool)
    (hd : ∀ x, d.eval x = true ↔ R x) (x₀ : σ.denote) (hx₀ : ¬P x₀) :
    CertifiedReduction (P.restrict R) P where
  code := .branch d .id (.const σ x₀)
  correct x := by
    by_cases hR : R x
    · have he : (Code.branch d .id (.const σ x₀)).eval x = x := by
        change (if d.eval x = true then x else x₀) = x
        rw [if_pos ((hd x).mpr hR)]
      rw [he]
      exact and_iff_right hR
    · have he : (Code.branch d .id (.const σ x₀)).eval x = x₀ := by
        change (if d.eval x = true then x else x₀) = x₀
        rw [if_neg fun hc ↦ hR ((hd x).mp hc)]
      rw [he]
      exact iff_of_false (fun hc ↦ hR hc.1) hx₀

/-- The free lunch: a certified reduction's map has polynomially bounded cost
and output size, with no per-reduction proof obligation. -/
theorem cost_size_le (r : CertifiedReduction P Q) :
    ∃ C d, ∀ x, r.code.cost x + τ.size (r.code.eval x)
      ≤ polyBound C d (σ.size x) :=
  Code.cost_size_le_polyBound r.code

end CertifiedReduction

end Cert
end Hardness


