-- Prove2me | Definitions.Def_ArtinHeckeRowL
-- name    : ArtinHeckeRowL
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T20:43:57.763993+00:00
-- url     : https://prove2.me/theorems/999260b9-c194-4525-a71e-28f52a1c8b7f
-- title:
--   The L-series L^S(w, χ•(u)) and L^S(ξ, η conj χ•(u)), ζ_F^S and the first region of (7.13), from §7.3 of OpenAI's Primitive roots paper
-- statement:
--   Objects of §7.3 of OpenAI, *Primitive roots for every admissible integer base* (2026), pp. 46 and 49. They are built on the bundles `Def_ArtinHecke` (`HeckeChar F 𝔪`) and `Def_ArtinHeckeTheta` (`SInt 𝔪`, `IsExterior`, `residueSymbol`). Here $\iota : F \to \mathbb C$ is a ring homomorphism, $\mathfrak m$ is an ideal of $\mathcal O_F$, $u \in R$ = `SInt 𝔪`, and $q_{\mathfrak a} = \mathrm N\mathfrak a$ is the absolute norm.
--
--   - `kummerL ι 𝔪 u w`: the sum (`tsum`) over the exterior ideals $\mathfrak a$ (`IsExterior 𝔪 𝔞`) of $\chi_{\mathfrak a}(u)\,q_{\mathfrak a}^{-w}$, where $\chi_{\mathfrak a}(u)$ = `residueSymbol ι 𝔪 𝔞 u`.
--   - `twistedL ι χ u ξ`, for a Hecke character $\chi$ of modulus $\mathfrak m$ with values $\eta$: the sum over the exterior ideals $\mathfrak a$ of $\eta(\mathfrak a)\,\overline{\chi_{\mathfrak a}(u)}\,q_{\mathfrak a}^{-\xi}$.
--   - `zetaSF 𝔪 s`: $\prod (1 - q_P^{-s})$ over the nonzero primes $P \supseteq \mathfrak m$, times `NumberField.dedekindZeta F s`.
--   - `regionOne`: the triples $(\xi, w, z) \in \mathbb C^3$ with $\operatorname{Re}\xi > .99799$, $\operatorname{Re} w > .00299$ and $\operatorname{Re} z > .39999$.
--
--   In the paper's notation `kummerL` is $L^S(w, \chi_\bullet(u))$, `twistedL` is the denominator $L^S(\xi, \eta\overline{\chi_\bullet(u)})$ of (7.12), and `zetaSF` is $\zeta_F^S$. `regionOne` is the first region of (7.13), $\operatorname{Re}\xi \ge .998$, $\operatorname{Re} w \ge .003$, $\operatorname{Re} z \ge .4$, with each lower endpoint decreased by $10^{-5}$ as in the proof of Proposition 7.3 (p. 49).
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 46: “We extend the notation $L^S(s, \eta)$ from Section 4 to a Hecke character on exterior primes: the factors at $S$ are omitted, and any additional zero prime values are retained in the Euler product. Thus, for example, $L^S(w, \chi_\bullet(u)) = \prod_{\mathfrak p \notin S}(1 - \chi_{\mathfrak p}(u)q_{\mathfrak p}^{-w})^{-1}$ $(\operatorname{Re} w > 1)$. As before, $\zeta_F^S(s) = \prod_{\mathfrak p \notin S}(1 - q_{\mathfrak p}^{-s})^{-1}$.” and p. 49: “in each line of Equation (7.13) decrease all three lower endpoints by $10^{-5}$, and use the resulting strict inequalities.”
--
--   **Formalization note.** The Euler products of the paper are written as Dirichlet series over the exterior ideals; for $\operatorname{Re} > 1$ they agree, since $\chi_{\mathfrak a}(u)$ is completely multiplicative in $\mathfrak a$ and vanishes on ideals meeting $(u)R$ (the retained zero prime values). The bar on $\chi_\bullet(u)$ in the denominator is the paper's, in (7.12) and in $D_1 = \eta(\mathfrak p)\overline{\chi_{\mathfrak p}(u)}Q^{-\xi}$ (p. 48).
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 46, 49, §7.3 (the L-series L^S(w, χ•(u)), L^S(ξ, η conj χ•(u)), ζ_F^S and the first region of (7.13))

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- `L^S(w, χ•(u))` of §7.3 (p. 46) of OpenAI's *Primitive roots for every admissible integer
base*: the sum over the exterior ideals `𝔞` of `χ_𝔞(u) q_𝔞^{-w}`, with `χ_𝔞(u)` the residue symbol
`residueSymbol ι 𝔪 𝔞 u`. -/
noncomputable def kummerL (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (u : SInt 𝔪) (w : ℂ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 F) // IsExterior 𝔪 I},
    residueSymbol ι 𝔪 I.1 u * (Ideal.absNorm I.1 : ℂ) ^ (-w)

/-- `L^S(ξ, η conj(χ•(u)))` of §7.3 (p. 46): the sum over the exterior ideals `𝔞` of
`η(𝔞) conj(χ_𝔞(u)) q_𝔞^{-ξ}`, with `η` the values of `χ`. -/
noncomputable def twistedL (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (u : SInt 𝔪)
    (ξ : ℂ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 F) // IsExterior 𝔪 I},
    χ.toFun I.1 * starRingEnd ℂ (residueSymbol ι 𝔪 I.1 u) * (Ideal.absNorm I.1 : ℂ) ^ (-ξ)

/-- `ζ_F^S(s)` of §7.3 (p. 46): `∏ (1 − q_P^{-s})` over the nonzero primes `P ⊇ 𝔪`, times the
Dedekind zeta function of `F`. -/
noncomputable def zetaSF (𝔪 : Ideal (𝓞 F)) (s : ℂ) : ℂ :=
  (∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P}, (1 - (Ideal.absNorm P : ℂ) ^ (-s))) *
    dedekindZeta F s

/-- The first region `Re ξ ≥ .998, Re w ≥ .003, Re z ≥ .4` of (7.13) (p. 46), with each lower
endpoint decreased by `10⁻⁵` (p. 49), as an open set of triples `(ξ, w, z)`. -/
def regionOne : Set (ℂ × ℂ × ℂ) :=
  {p | 99799 / 100000 < p.1.re ∧ 299 / 100000 < p.2.1.re ∧ 39999 / 100000 < p.2.2.re}

end ArtinPrimitiveRoots


