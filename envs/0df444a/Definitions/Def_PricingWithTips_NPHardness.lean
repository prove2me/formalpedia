-- Prove2me | Definitions.Def_PricingWithTips_NPHardness
-- name    : PricingWithTips_NPHardness
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-21T19:47:58.359711+00:00
-- url     : https://prove2.me/theorems/f6951501-cfe3-4d58-9cbc-f8aeb9d86f3a
-- title:
--   Machine-model NP-hardness for encoded delivery markets
-- statement:
--   Defines polynomially verifiable languages using polynomial-length certificates checked by a polynomial-time Turing machine, and NP-hardness of a finite market decision predicate as polynomial-time reducibility from every such language. Market instances use an explicit binary incidence-table encoding.
-- source:
--   CLRS Chapter 34 Sections 34.2–34.3 (polynomial verification and NP-hardness); https://tanktechnology.github.io/CLRS-Lean/CLRSLean/FourthEdition/Chapter_34/ ; applied to arXiv:2507.10872v1, Theorems 4.1–4.2

import Definitions.Def_PricingWithTips_ThreeDM

namespace PricingWithTips

/-- A self-delimiting encoding of an input/certificate pair over alphabet `Γ`. -/
def certificatePairEncoding {Γ : Type} (p : List Γ × List Γ) :
    List (Option Γ) :=
  p.1.map some ++ [none] ++ p.2.map some

/-- An NP language is accepted by a polynomial-time verifier with a
polynomial-length certificate. The verifier's actual running time is certified
by Mathlib's `TM2ComputableInPolyTime` machine model. -/
def PolynomiallyVerifiable {Γ : Type} (L : Set (List Γ)) : Prop :=
  ∃ (V : List Γ → List Γ → Bool) (p : Polynomial ℕ),
    Nonempty (Turing.TM2ComputableInPolyTime
      certificatePairEncoding (fun b : Bool => [b])
      (fun pair : List Γ × List Γ => V pair.1 pair.2)) ∧
    ∀ x : List Γ, x ∈ L ↔
      ∃ c : List Γ, c.length ≤ p.eval x.length ∧ V c x = true

/-- A finite-market decision predicate is NP-hard if every polynomially
verifiable language over every alphabet reduces to it by a polynomial-time
Turing-machine computation producing the explicit 3DM/market encoding. -/
def NPHardMarketPredicate (target : ThreeDMInstance → Prop) : Prop :=
  ∀ (Γ : Type) (L : Set (List Γ)), PolynomiallyVerifiable L →
    ∃ f : List Γ → ThreeDMInstance,
      Nonempty (Turing.TM2ComputableInPolyTime
        (id : List Γ → List Γ) encodeThreeDMInstance f) ∧
      ∀ x : List Γ, x ∈ L ↔ target (f x)

end PricingWithTips


