-- Prove2me | Definitions.Def_IntractableCoding_Weights_NPComplete
-- name    : IntractableCoding_Weights_NPComplete
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:31.973508+00:00
-- url     : https://prove2.me/theorems/4c3bc713-12ff-4fc3-ba13-322000663799
-- title:
--   NP-hardness and NP-completeness of an encoded decision problem (Section II, pp. 384–385)
-- statement:
--   Let $\alpha$ be a type of problem instances, $P$ a property of instances (the "yes" answers) and $\mathrm{enc}:\alpha\to\{0,1\}^*$ a binary encoding of instances.
--
--   1. The **language** of $(\mathrm{enc},P)$ is the set of binary strings $\mathrm{enc}(a)$ with $P(a)$; strings that encode no instance are not in it.
--   2. $P$ is **NP-hard** (with respect to $\mathrm{enc}$) if for every finite alphabet $\Gamma$ and every language $L\subseteq\Gamma^*$ in NP there is a map $f$ from strings to instances, computed by a polynomial-time multi-stack Turing machine (Mathlib's `TM2ComputableInPolyTime`) from $x$ to $\mathrm{enc}(f(x))$, such that
--   $$x\in L\iff P(f(x))\qquad\text{for every }x\in\Gamma^*.$$
--   3. $P$ is **NP-complete** if its language is in NP and $P$ is NP-hard.
--
--   Membership in NP is the published notion `PricingWithTips.PolynomiallyVerifiable`: a Boolean verifier $V(c,x)$ computed by a polynomial-time TM2 machine and a polynomial $p$ with $x\in L\iff\exists c,\ |c|\le p(|x|)\wedge V(c,x)$.
--
--   These are the standard precise forms of the notions the paper describes heuristically in Section II, with polynomial-time many-one (Karp) reductions. For 3DM instances with their published encoding, NP-hardness here is literally the published `PricingWithTips.NPHardMarketPredicate`.
--
--   **Formalization Note** The alphabet $\Gamma$ ranges over all types; for an infinite $\Gamma$ no TM2 machine reads $\Gamma$, so no language over it is polynomially verifiable and the condition is empty there.
-- source:
--   Berlekamp, McEliece & van Tilborg, On the Inherent Intractability of Certain Coding Problems, IEEE Trans. Inform. Theory IT-24(3), 1978, https://doi.org/10.1109/TIT.1978.1055873, pp. 384–385, Section II (NP-complete problems)

import Mathlib
import Definitions.Def_PricingWithTips_NPHardness

namespace IntractableCoding.Weights

/-- The language of an encoded decision problem: the binary strings that encode some
yes-instance. Strings that encode no instance at all are not in the language. -/
def languageOf {α : Type} (enc : α → List Bool) (P : α → Prop) : Set (List Bool) :=
  {s | ∃ a, enc a = s ∧ P a}

/-- NP-hardness of a decision problem `P` on instances `α`, presented to machines through the
binary encoding `enc`: every polynomially verifiable language `L` over every alphabet `Γ`
(`PricingWithTips.PolynomiallyVerifiable`, a polynomial-time TM2 verifier with polynomially
long certificates) many-one reduces to `P` by a map `f` computed by a polynomial-time TM2
machine from the input string to the encoding `enc (f x)` of the produced instance.
For `α = ThreeDMInstance` and `enc = encodeThreeDMInstance` this is literally
`PricingWithTips.NPHardMarketPredicate`. -/
def NPHardFor {α : Type} (enc : α → List Bool) (P : α → Prop) : Prop :=
  ∀ (Γ : Type) (L : Set (List Γ)), PricingWithTips.PolynomiallyVerifiable L →
    ∃ f : List Γ → α,
      Nonempty (Turing.TM2ComputableInPolyTime (id : List Γ → List Γ) enc f) ∧
      ∀ x : List Γ, x ∈ L ↔ P (f x)

/-- NP-completeness of an encoded decision problem: its language is in NP and it is NP-hard
under polynomial-time many-one reductions. -/
def NPCompleteFor {α : Type} (enc : α → List Bool) (P : α → Prop) : Prop :=
  PricingWithTips.PolynomiallyVerifiable (languageOf enc P) ∧ NPHardFor enc P

end IntractableCoding.Weights


