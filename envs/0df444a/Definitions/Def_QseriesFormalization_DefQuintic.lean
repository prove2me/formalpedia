-- Prove2me | Definitions.Def_QseriesFormalization_DefQuintic
-- name    : QseriesFormalization_DefQuintic
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:31:05.560087+00:00
-- url     : https://prove2.me/theorems/2b0f3f41-375c-4100-bafd-7e6ecf503984
-- title:
--   Quintic eta products, residue sections, and fifth-root expressions
-- statement:
--   The definitions include the products $F(q^5)=(q^{10},q^{15},q^{25};q^{25})_\infty$ and $G(q^5)=(q^5,q^{20},q^{25};q^{25})_\infty$ over a topological commutative ring, and the corresponding theta series $\sum(-1)^kX^{(25k^2-5k)/2}$ and $\sum(-1)^kX^{(25k^2-15k)/2}$ (the pentagonal series after $X\mapsto X^5$). It also defines the mod-5 shifted product $-3X\,G(q^5)$ over $\mathbb{Z}/5$, used in the mod-5 eta-quotient congruences.
--
--   The definitions include residue sections and compressed sections mod $5$ of a power series, the residue predicate, and the sections $E_r$ of Euler's product $(q;q)_\infty$. It defines the denominator core $E_0^5+11E_1^5+E_2^5$ and the rationalizer numerator $\mathcal{R}$ (a quartic in $E_0,E_1,E_2$), the left side of Ramanujan's identity for $\sum p(5n+4)q^n$ and the numerator core $E(X^5)^5$ of its right side, where $E=(q;q)_\infty$, the products $(q^5,q^{20},q^{25};q^{25})_\infty$ and $(q^{10},q^{15},q^{25};q^{25})_\infty$ lifted to the ambient variable, and three versions of the Ramanujan mod-5 product core. It also contains a bookkeeping equivalence between $5$-indexed sigma types and the naturals.
--
--   The uncompressed section and support predicate use the literal equality $n\bmod5=r$, so $r\ge5$ gives a zero section and forces a supported series to be zero. The compressed section instead takes coefficient $5n+r$ literally.
--
--   The definitions include the substitution $f(X)\mapsto f(cX)$ on power series, the cyclotomic field $\mathbb{Q}(\zeta_5)$ with a chosen primitive fifth root of unity $\zeta$, and the Gaussian periods $\zeta+\zeta^4$ and $\zeta^2+\zeta^3$. It also defines the quintic product core $G^{10}-11XH^5G^5-X^2H^{10}$ for power series $H,G$, which is only an algebraic expression and not a claim about products.
--
--   The definitions include Hirschhorn's golden-ratio numbers $\alpha=-(\zeta^2+\zeta^3)$ and $\beta=-(\zeta+\zeta^4)$ from a fifth root of unity, the series $A=(q^{10},q^{15},q^{25};q^{25})_\infty$ and $B=(q^5,q^{20},q^{25};q^{25})_\infty$ (as series in the ambient variable), and the right-hand sides $A+(\zeta^2+\zeta^3)XB$ and $A+(\zeta+\zeta^4)XB$ of Hirschhorn (8.3.1)--(8.3.2). It defines formal and analytic products $(zq,z^{-1}q,q;q)_\infty$ with scalar constants, their triangular theta terms $(-z)^nq^{n(n+1)/2}$, the pentagonal-type theta terms of $A$ and $B$, and formal multilinear series from coefficient sequences, plus a fifth-collapse factor and an index equivalence.
--
--   The general scalar $z$ is arbitrary, with inverse $0^{-1}=0$. The complex products are totalized tprods, whose default is $1$ for a nonmultipliable family; the definitions alone assert no analytic convergence.
--
--   The definitions include over $\mathbb{C}$ the series $f(-q^{25})=(q^{25};q^{25})_\infty$, the denominators $(q^5,q^{20};q^{25})_\infty$ and $(q^{10},q^{15};q^{25})_\infty$ with the inverses $G(q^5)$ and $H(q^5)$, and the four series $A=f(-q^{25})G^2/H$, $B=f(-q^{25})G$, $C=f(-q^{25})H$, $D=f(-q^{25})H^2/G$. It also defines the left side $(q;q)_\infty/((\zeta q;q)_\infty(\zeta^{-1}q;q)_\infty)$ and the right side $A-(\zeta+\zeta^{-1})^2XB+(\zeta^2+\zeta^{-2})X^2C-(\zeta+\zeta^{-1})X^3D$ of Chan's Theorem 11.6 (with a separately defined expression in Gaussian periods), together with the denominator product. These are definitions only.
--
--   All series here lie in $\mathbb{C}[[X]]$, with $q$ denoting the formal variable $X$. Every formal-series denominator displayed above has constant coefficient $1$, so its inverse is an actual inverse of a unit. The scalar parameter $\zeta\in\mathbb{C}$ is unrestricted in these definitions, and its scalar inverse uses $0^{-1}=0$. The primitive-fifth-root hypothesis is imposed in the theorem; under that hypothesis the two right-side expressions agree and $\zeta^{-1}$ is the usual reciprocal.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/ASD_EtaProducts.lean (definitions of this module that the uploaded theorems need; ported to Lean v4.33.1 / Mathlib 0df444a).
--
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 16. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter16_MBI_Proof.lean (definitions of this module that the uploaded theorems need; ported to Lean v4.33.1 / Mathlib 0df444a).
--
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuintic.lean (definitions of this module that the uploaded theorems need; ported to Lean v4.33.1 / Mathlib 0df444a).
--
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuinticJTP.lean (definitions of this module that the uploaded theorems need; ported to Lean v4.33.1 / Mathlib 0df444a).
--
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 14. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter14_Thm116.lean (definitions of this module that the uploaded theorems need; ported to Lean v4.33.1 / Mathlib 0df444a).

-- Definition group: QseriesFormalization_DefQuintic; exact rendered source bodies in isolated sections.
import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_QseriesFormalization_Chapter05_Franklin
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic

-- Source module: QseriesFormalization.Pending.ASD_EtaProducts
section

namespace QseriesFormalization.PartIV.Ch17 end QseriesFormalization.PartIV.Ch17
namespace QseriesFormalization.PartIV.Ch19 end QseriesFormalization.PartIV.Ch19
namespace QseriesFormalization.Pending.ASDMod5 end QseriesFormalization.Pending.ASDMod5
namespace QseriesFormalization.Pending.ASDMod5Full end QseriesFormalization.Pending.ASDMod5Full

/-!
# ASD eta-product formal identities

This file records the modulus-25 eta-product identities obtained from the
closed mod-5 formal Jacobi triple product identities by the substitution
`X ↦ X^5`.
-/

namespace QseriesFormalization
namespace Pending
namespace ASDEtaProducts

open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology

open JTPFormalPSPentagonal
open QseriesFormalization.PartIV.Ch19

/-! ## Expanding AP products -/

/-! ## Hirschhorn §3.6.5: the mod-25 F/G eta products -/

/-- Hirschhorn's `F(q^5) = (q^10,q^15,q^25;q^25)_∞`. -/
noncomputable def asd5FProductPS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R 10 25 * qPochAPPS R 15 25 * qPochAPPS R 25 25

/-- Hirschhorn's `G(q^5) = (q^5,q^20,q^25;q^25)_∞`. -/
noncomputable def asd5GProductPS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R 5 25 * qPochAPPS R 20 25 * qPochAPPS R 25 25

/--
The theta side of `F(q^5)`: the mod-5 `pentagonal023` theta series after
`X ↦ X^5`, i.e. `∑ (-1)^k X^((25k^2 - 5k)/2)`.
-/
noncomputable def asd5FSeriesPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS R)

/--
The theta side of `G(q^5)`: the mod-5 `pentagonal014` theta series after
`X ↦ X^5`, i.e. `∑ (-1)^k X^((25k^2 - 15k)/2)`.
-/
noncomputable def asd5GSeriesPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS R)

/-! ## Integral and mod-5 forms of the two JTP product identities -/

/-!
## Section-to-eta bridge, conditional on the remaining A-section identifications

The hard coefficient-level gap left by this file is the identification
`A 0 = F(q^5)` and `A 1 = -3qG(q^5)` in `ZMod 5`.  The following lemmas
show that once those two identifications are supplied, the section-form ASD
congruences from `Chapter17_ASD_Mod5_Full` immediately rewrite to the
eta-product form.
-/

noncomputable abbrev asd5GShiftedProductPS : (ZMod 5)⟦X⟧ :=
  -(3 : (ZMod 5)⟦X⟧) * PowerSeries.X * asd5GProductPS (ZMod 5)

open QseriesFormalization.Pending.ASDMod5
open QseriesFormalization.Pending.ASDMod5Full
open QseriesFormalization.PartIV.Ch17

/-! ### UNCONDITIONAL ASD mod-5 η-quotient congruences (Hirschhorn 3.6.7)

The `A 0 = F`, `A 1 = -3qG` identifications are now theorems
(`A0_eq_asd5FProductPS_zmod5`, `A1_eq_asd5GShiftedProductPS_zmod5`), so the
conditional forms above become unconditional. -/

end ASDEtaProducts
end Pending
end QseriesFormalization

end

-- Source module: QseriesFormalization.Pending.Chapter16_MBI_Proof
section

/-!
# Pending proof work for Chan §16 / Hirschhorn §5

This file is intentionally standalone: it does not edit or import the existing
`Pending/Chapter16_MBI.lean` stub.  It develops the mod-5 section bookkeeping
needed for Ramanujan's most beautiful identity.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch16MBIProof

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartI.Ch04Franklin (pentagonalSign)
open QseriesFormalization.Pending.JTPFormalPSPentagonal

/-- The residue-`r` mod 5 section of a formal power series. -/
noncomputable def section5 (R : Type*) [CommRing R] (r : ℕ) (φ : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk (fun n => if n % 5 = r then φ.coeff n else 0)

/-- The compressed residue-`r` mod 5 section: coefficient `n` is the
coefficient of the original series at `5n+r`. -/
noncomputable def compressedSection5 (R : Type*) [CommRing R] (r : ℕ)
    (φ : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk (fun n => φ.coeff (5 * n + r))

/-- `φ` is supported on one residue class modulo 5. -/
def IsRes5 {R : Type*} [CommRing R] (r : ℕ) (φ : R⟦X⟧) : Prop :=
  ∀ n, n % 5 ≠ r → φ.coeff n = 0

/-- The three nonzero residue sections of Euler's product. -/
noncomputable def E5 (R : Type*) [CommRing R] (r : ℕ) : R⟦X⟧ :=
  section5 R r (qPochInfPS R)

/-- The rationalized denominator core from the mod-5 dissection:
`E_0^5 + 11 E_1^5 + E_2^5`.  The remaining Route A eta-product gap is the
identity `E5DenominatorCoreRat * E(q^25) = E(q^5)^6`. -/
noncomputable def E5DenominatorCoreRat : ℚ⟦X⟧ :=
  (E5 ℚ 0)^5 + (11 : ℚ⟦X⟧) * (E5 ℚ 1)^5 + (E5 ℚ 2)^5

/-- The rationalizer numerator, reduced using `E_0 E_2 = -E_1^2`. -/
noncomputable def E5RationalizerRat : ℚ⟦X⟧ :=
  (E5 ℚ 2)^4 - E5 ℚ 1 * (E5 ℚ 2)^3 +
    (2 : ℚ⟦X⟧) * (E5 ℚ 1)^2 * (E5 ℚ 2)^2 -
    (3 : ℚ⟦X⟧) * (E5 ℚ 1)^3 * E5 ℚ 2 +
    (5 : ℚ⟦X⟧) * (E5 ℚ 1)^4 -
    (3 : ℚ⟦X⟧) * E5 ℚ 0 * (E5 ℚ 1)^3 +
    (2 : ℚ⟦X⟧) * (E5 ℚ 0)^2 * (E5 ℚ 1)^2 -
    (E5 ℚ 0)^3 * E5 ℚ 1 +
    (E5 ℚ 0)^4

/-- The compressed residue-4 partition-generating series
`∑ p(5n+4) X^n`, over `ℚ`. -/
noncomputable def mostBeautifulLHS : ℚ⟦X⟧ :=
  PowerSeries.mk (fun n : ℕ => (partitionGenFun ℚ).coeff (5 * n + 4))

/-- The numerator core on the right side of MBI, `E(q^5)^5`. -/
noncomputable def mostBeautifulRHSCore : ℚ⟦X⟧ :=
  (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)) ^ 5

/-! ## JTP-product reduction of the remaining denominator identity -/

def finFiveSigmaNatEquivNat : (Sigma fun _ : Fin 5 => ℕ) ≃ ℕ where
  toFun p := 5 * p.2 + p.1.val
  invFun k := Sigma.mk ⟨k % 5, Nat.mod_lt k (by decide)⟩ (k / 5)
  left_inv := by
    rintro ⟨i, n⟩
    simp
    constructor
    · ext
      exact Nat.mod_eq_of_lt i.2
    · have hi : i.val < 5 := i.2
      omega
  right_inv := by
    intro k
    exact Nat.div_add_mod k 5

/-- The first JTP factor, lifted from the `q^5` variable to the ambient
`q`-series variable. -/
noncomputable def pentagonalProduct014AtFiveRat : ℚ⟦X⟧ :=
  PowerSeries.expand 5 (by decide) (pentagonalProduct014PS ℚ)

/-- The second JTP factor, lifted from the `q^5` variable to the ambient
`q`-series variable. -/
noncomputable def pentagonalProduct023AtFiveRat : ℚ⟦X⟧ :=
  PowerSeries.expand 5 (by decide) (pentagonalProduct023PS ℚ)

/-- Cross-multiplied Ramanujan product core for the remaining denominator
identity.  This is the formal version of the quintic expression in the
Rogers-Ramanujan continued fraction. -/
noncomputable def ramanujanMod5ProductCoreRat : ℚ⟦X⟧ :=
  (pentagonalProduct023AtFiveRat)^10 -
    (11 : ℚ⟦X⟧) * PowerSeries.X^5 *
      (pentagonalProduct014AtFiveRat)^5 * (pentagonalProduct023AtFiveRat)^5 -
    PowerSeries.X^10 * (pentagonalProduct014AtFiveRat)^10

/-- The same quintic product core before the ambient substitution `X ↦ X^5`.
Expanding this by `5` gives `ramanujanMod5ProductCoreRat`. -/
noncomputable def ramanujanMod5ProductCoreCompressedRat : ℚ⟦X⟧ :=
  (pentagonalProduct023PS ℚ)^10 -
    (11 : ℚ⟦X⟧) * PowerSeries.X *
      (pentagonalProduct014PS ℚ)^5 * (pentagonalProduct023PS ℚ)^5 -
    PowerSeries.X^2 * (pentagonalProduct014PS ℚ)^10

/-
Closed algebraic reduction of the remaining denominator identity.

It isolates the exact product-side work left after the new JTP keystone:
prove the two cross-multiplied identifications of `E_0,E_2` with the mod-5
JTP products, and prove the single cross-multiplied Ramanujan quintic product
identity.  These three hypotheses imply the `hden` expected by the existing
`most_beautiful_identity_of_E5_denominator_identity` wrapper.
-/

/-! ## Theta-series form of the final product gaps -/

/-- Theta-series rewrite of the compressed Ramanujan quintic core. -/
noncomputable def ramanujanMod5ProductCoreThetaRat : ℚ⟦X⟧ :=
  (pentagonal023SeriesPS ℚ)^10 -
    (11 : ℚ⟦X⟧) * PowerSeries.X *
      (pentagonal014SeriesPS ℚ)^5 * (pentagonal023SeriesPS ℚ)^5 -
    PowerSeries.X^2 * (pentagonal014SeriesPS ℚ)^10

end Ch16MBIProof
end Pending
end QseriesFormalization

end

-- Source module: QseriesFormalization.Pending.RamanujanQuintic
section

namespace QseriesFormalization.PartIV.Ch19 end QseriesFormalization.PartIV.Ch19

/-!
# Ramanujan quintic cyclotomic infrastructure

This file builds a small, reusable formal-power-series layer for the
root-of-unity product route toward Hirschhorn's quintic product identity.

The results below are deliberately finite/product-local: they prove the
`X ↦ cX` power-series homomorphism API and the fifth-root finite factor
collapse.  They do not assert the infinite-product quotient or the final
`core * P5 = E^11` identity.
-/

namespace QseriesFormalization
namespace Pending
namespace RamanujanQuintic

open Finset
open PowerSeries
open scoped PowerSeries
open QseriesFormalization.PartIV.Ch19

/-! ## Scaling the variable -/

/-- The power-series ring homomorphism `f(X) ↦ f(c X)`.  This is Mathlib's
`PowerSeries.rescale`, exposed under the name used by the quintic route. -/
noncomputable abbrev scaleX {R : Type*} [CommSemiring R] (c : R) :
    R⟦X⟧ →+* R⟦X⟧ :=
  PowerSeries.rescale c

/-! ## Fifth-root finite factor collapse -/

/-! ## The concrete fifth cyclotomic field over `ℚ` -/

instance quinticNeZero : NeZero ((5 : ℕ) : ℚ) := ⟨by norm_num⟩

instance quinticIsCyclotomic : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

noncomputable abbrev QuinticCyclotomicField : Type :=
  CyclotomicField 5 ℚ

/-- A chosen primitive fifth root in `CyclotomicField 5 ℚ`. -/
noncomputable def quinticZeta : QuinticCyclotomicField :=
  IsCyclotomicExtension.zeta 5 ℚ QuinticCyclotomicField

/-! ## Gaussian periods for primitive fifth roots -/

/-- The Gaussian period `ζ + ζ^4`. -/
noncomputable def quinticPeriodAlpha {R : Type*} [CommRing R] (ζ : R) : R :=
  ζ + ζ ^ 4

/-- The Gaussian period `ζ^2 + ζ^3`. -/
noncomputable def quinticPeriodBeta {R : Type*} [CommRing R] (ζ : R) : R :=
  ζ ^ 2 + ζ ^ 3

/-! ## Local quadratic factors behind the §8.6 product route -/

/-! ## Algebraic §8.5 factor-pair reduction -/

/-- The compressed quintic core written with arbitrary `H,G`.  This is only
an algebraic expression; it does not assert Hirschhorn's product identity. -/
noncomputable def quinticProductCore (R : Type*) [CommRing R] (H G : R⟦X⟧) : R⟦X⟧ :=
  G ^ 10 - (11 : R⟦X⟧) * PowerSeries.X * H ^ 5 * G ^ 5 -
    PowerSeries.X ^ 2 * H ^ 10

end RamanujanQuintic
end Pending
end QseriesFormalization

end

-- Source module: QseriesFormalization.Pending.RamanujanQuinticJTP
section

namespace QseriesFormalization.Pending.Ch16MBIProof end QseriesFormalization.Pending.Ch16MBIProof

/-!
# Ramanujan quintic: JTP-at-a-fifth-root scaffolding

This file keeps the `a = eta` bookkeeping for Hirschhorn §8.3 separate from
the older finite product/cyclotomic infrastructure in `RamanujanQuintic`.

The main convention issue is that `RamanujanQuintic.quinticPeriodAlpha/Beta`
are the Gaussian periods

* `ζ + ζ^4`, `ζ^2 + ζ^3`, with sum `-1`;

whereas Hirschhorn §8.3 writes the golden-ratio pair with sum `1`.  The
definitions below expose the book's pair as the negatives of the appropriate
Gaussian periods.
-/

namespace QseriesFormalization
namespace Pending
namespace RamanujanQuinticJTP

open Finset
open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.RamanujanQuintic
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.Ch16MBIProof

/-! ## The §8.3 period convention -/

/-- Hirschhorn's `α = (1 + sqrt 5) / 2`, represented from a primitive fifth
root by `-(ζ^2 + ζ^3)`. -/
noncomputable def bookAlpha {R : Type*} [CommRing R] (ζ : R) : R :=
  -quinticPeriodBeta ζ

/-- Hirschhorn's `β = (1 - sqrt 5) / 2`, represented from a primitive fifth
root by `-(ζ + ζ^4)`. -/
noncomputable def bookBeta {R : Type*} [CommRing R] (ζ : R) : R :=
  -quinticPeriodAlpha ζ

/-! ## Local factors for the `a = η²` specialization -/

/-! ## Book-period form of the §8.3 quadratic factors -/

/-! ## The fifth-power algebra used after the §8.3 factor identities -/

/-! ## Names for the two `A,B` series in Hirschhorn §8.3 -/

/-- `A = (q^10,q^15,q^25;q^25)_∞`, written in the compressed variable as
`G(X^5)`. -/
noncomputable def section83A (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS R)

/-- `B = (q^5,q^20,q^25;q^25)_∞`, written in the compressed variable as
`H(X^5)`. -/
noncomputable def section83B (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS R)

/-- The right-hand side of Hirschhorn (8.3.2), in this file's period
convention: `A - α q B = A + (ζ²+ζ³) q B`. -/
noncomputable def section83_rhs_pair14 {R : Type*} [CommRing R] (ζ : R) : R⟦X⟧ :=
  section83A R + PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X * section83B R

/-- The right-hand side of Hirschhorn (8.3.1), in this file's period
convention: `A - β q B = A + (ζ+ζ⁴) q B`. -/
noncomputable def section83_rhs_pair23 {R : Type*} [CommRing R] (ζ : R) : R⟦X⟧ :=
  section83A R + PowerSeries.C (quinticPeriodAlpha ζ) * PowerSeries.X * section83B R

/-! ## Free-constant Euler factors for the §8.3 JTP product side -/

/-- The formal factor `1 - c X^(n+1)`.  This is the product-side atom for
`(c q; q)_∞`, where the scalar `c` is independent of the exponent. -/
noncomputable def constQFactorPS (c : ℂ) (n : ℕ) : ℂ⟦X⟧ :=
  (1 : ℂ⟦X⟧) - PowerSeries.C c * PowerSeries.X ^ (n + 1)

@[simp] theorem constQFactorPS_def (c : ℂ) (n : ℕ) :
    constQFactorPS c n =
      (1 : ℂ⟦X⟧) - PowerSeries.C c * PowerSeries.X ^ (n + 1) := rfl

/-- The formal q-Pochhammer product `(c q; q)_∞`. -/
noncomputable def constQPochInfPS (c : ℂ) : ℂ⟦X⟧ :=
  ∏' n : ℕ, constQFactorPS c n

/-- Per-`n` product factor for `(z q, z⁻¹ q, q; q)_∞`. -/
noncomputable def section83JTPTripleFactorPS (z : ℂ) (n : ℕ) : ℂ⟦X⟧ :=
  constQFactorPS 1 n * constQFactorPS z n * constQFactorPS z⁻¹ n

/-- Formal product side of the shifted two-variable JTP
`(z q, z⁻¹ q, q; q)_∞`. -/
noncomputable def section83JTPProductPS (z : ℂ) : ℂ⟦X⟧ :=
  constQPochInfPS 1 * constQPochInfPS z * constQPochInfPS z⁻¹

/-! ### Analytic product attached to the free-constant formal product -/

/-- Analytic factor `1 - c q^(n+1)`. -/
def constQFactorAnalytic (c q : ℂ) (n : ℕ) : ℂ :=
  1 - c * q ^ (n + 1)

/-- Analytic per-`n` factor for `(z q, z⁻¹ q, q; q)_∞`. -/
noncomputable def section83JTPTripleFactorAnalytic (z q : ℂ) (n : ℕ) : ℂ :=
  constQFactorAnalytic 1 q n * constQFactorAnalytic z q n *
    constQFactorAnalytic z⁻¹ q n

/-- Analytic product side of `(z q, z⁻¹ q, q; q)_∞`. -/
noncomputable def section83JTPProductAnalytic (z q : ℂ) : ℂ :=
  (∏' n : ℕ, constQFactorAnalytic 1 q n) *
    (∏' n : ℕ, constQFactorAnalytic z q n) *
      (∏' n : ℕ, constQFactorAnalytic z⁻¹ q n)

/-! ### Bilateral triangular terms for the fifth-root period collapse -/

noncomputable def section83TriangularTerm (z q : ℂ) (n : ℤ) : ℂ :=
  (-z : ℂ) ^ n * q ^ (n * (n + 1) / 2)

noncomputable def section83PairedTriangularTerm (z q : ℂ) (n : ℕ) : ℂ :=
  section83TriangularTerm z q n +
    section83TriangularTerm z q (-(n + 1 : ℤ))

noncomputable def section83ATerm (q : ℂ) (k : ℤ) : ℂ :=
  (-1 : ℂ) ^ k * (q ^ 5) ^ (k * (5 * k - 1) / 2)

noncomputable def section83BTerm (q : ℂ) (k : ℤ) : ℂ :=
  (-1 : ℂ) ^ k * (q ^ 5) ^ (k * (5 * k - 3) / 2)

noncomputable def section83JTPProductCoeffFMLS (z : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (section83JTPProductPS z).coeff n)

/-! ### Keystone-style transfer for the two §8.3 factors

The declarations below deliberately isolate the remaining analytic theorem:
the RHS period-collapse Taylor expansion must be proved for the same analytic
product.  Once that is available, `eq_formalMultilinearSeries` gives the formal
identity exactly as in `JTP_FormalPS_Pentagonal`.
-/

noncomputable def section83RhsPair14FMLS (ζ : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (section83_rhs_pair14 ζ).coeff n)

noncomputable def section83RhsPair23FMLS (ζ : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (section83_rhs_pair23 ζ).coeff n)

/-! ## Infinite fifth-root product collapse -/

def finFiveSigmaNatEquivNat : (Sigma fun _ : Fin 5 => ℕ) ≃ ℕ where
  toFun p := 5 * p.2 + p.1.val
  invFun k := Sigma.mk ⟨k % 5, Nat.mod_lt k (by decide)⟩ (k / 5)
  left_inv := by
    rintro ⟨i, n⟩
    simp
    constructor
    · ext
      exact Nat.mod_eq_of_lt i.2
    · have hi : i.val < 5 := i.2
      omega
  right_inv := by
    intro k
    exact Nat.div_add_mod k 5

noncomputable def fifthCollapseFactor (n : ℕ) : ℂ⟦X⟧ :=
  if 5 ∣ n + 1 then
    (oneSubXPow ℂ n)^5
  else
    (1 : ℂ⟦X⟧) - PowerSeries.X ^ (5 * (n + 1))

/-! ## Identification with the Chapter 16 denominator core -/

end RamanujanQuinticJTP
end Pending
end QseriesFormalization

end

-- Source module: QseriesFormalization.Chapter14_Thm116
section

namespace QseriesFormalization.Pending.Ch16MBIProof end QseriesFormalization.Pending.Ch16MBIProof

/-!
# Chapter 14 — Chan Theorem 11.6 formal target

This file records the formal-power-series objects for the Lost Notebook
identity in Chan Theorem 11.6 and closes the reusable JTP-at-a-fifth-root
denominator collapse.  The remaining unproved bridge is isolated as a single
product identity involving the Rogers-Ramanujan `G,H` product factors below.
-/

namespace QseriesFormalization
namespace PartIII
namespace Ch14Thm116

open PowerSeries
open Filter
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.RamanujanQuintic
open QseriesFormalization.Pending.RamanujanQuinticJTP
open QseriesFormalization.Pending.Ch16MBIProof

noncomputable abbrev CPowerSeries := ℂ⟦X⟧

/-! ## The four product-side series in Theorem 11.6 -/

/-- Formal `f(-q^25) = (q^25;q^25)_∞`. -/
noncomputable def fMinusQ25PS : CPowerSeries :=
  PowerSeries.expand 25 (by decide) (qPochInfPS ℂ)

/-- Denominator of `G(q^5)`: `(q^5,q^20;q^25)_∞`. -/
noncomputable def rrGDenAtQ5PS : CPowerSeries :=
  qPochAPPS ℂ 5 25 * qPochAPPS ℂ 20 25

/-- Denominator of `H(q^5)`: `(q^10,q^15;q^25)_∞`. -/
noncomputable def rrHDenAtQ5PS : CPowerSeries :=
  qPochAPPS ℂ 10 25 * qPochAPPS ℂ 15 25

/-- Formal Rogers-Ramanujan product `G(q^5)`. -/
noncomputable def rrGAtQ5PS : CPowerSeries :=
  (rrGDenAtQ5PS)⁻¹

/-- Formal Rogers-Ramanujan product `H(q^5)`. -/
noncomputable def rrHAtQ5PS : CPowerSeries :=
  (rrHDenAtQ5PS)⁻¹

/-- `A(q^5) = f(-q^25) G(q^5)^2 / H(q^5)`. -/
noncomputable def chan116A : CPowerSeries :=
  fMinusQ25PS * rrGAtQ5PS ^ 2 * (rrHAtQ5PS)⁻¹

/-- `B(q^5) = f(-q^25) G(q^5)`. -/
noncomputable def chan116B : CPowerSeries :=
  fMinusQ25PS * rrGAtQ5PS

/-- `C(q^5) = f(-q^25) H(q^5)`. -/
noncomputable def chan116C : CPowerSeries :=
  fMinusQ25PS * rrHAtQ5PS

/-- `D(q^5) = f(-q^25) H(q^5)^2 / G(q^5)`. -/
noncomputable def chan116D : CPowerSeries :=
  fMinusQ25PS * rrHAtQ5PS ^ 2 * (rrGAtQ5PS)⁻¹

/-- The denominator `(ζq;q)_∞ (ζ⁻¹q;q)_∞` in formal-power-series form. -/
noncomputable def chan116DenomPS (ζ : ℂ) : CPowerSeries :=
  constQPochInfPS ζ * constQPochInfPS ζ⁻¹

/-- The formal left side `(q;q)_∞ / ((ζq;q)_∞(ζ⁻¹q;q)_∞)`. -/
noncomputable def chan116LHS (ζ : ℂ) : CPowerSeries :=
  qPochInfPS ℂ * (chan116DenomPS ζ)⁻¹

/-- The four-term right side in the statement of Chan Theorem 11.6. -/
noncomputable def chan116RHS (ζ : ℂ) : CPowerSeries :=
  chan116A
    - PowerSeries.C ((ζ + ζ⁻¹) ^ 2) * PowerSeries.X * chan116B
    + PowerSeries.C (ζ ^ 2 + (ζ⁻¹) ^ 2) * PowerSeries.X ^ 2 * chan116C
    - PowerSeries.C (ζ + ζ⁻¹) * PowerSeries.X ^ 3 * chan116D

/-- The same RHS, written with the Gaussian periods already used by the
quintic JTP formalization. -/
noncomputable def chan116RHS_period (ζ : ℂ) : CPowerSeries :=
  chan116A
    - PowerSeries.C ((quinticPeriodAlpha ζ) ^ 2) * PowerSeries.X * chan116B
    + PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X ^ 2 * chan116C
    - PowerSeries.C (quinticPeriodAlpha ζ) * PowerSeries.X ^ 3 * chan116D

/-! ## Period normalizations for a primitive fifth root -/

/-! ## Product rewrites for the §8.3 factors -/

/-! ## The JTP denominator collapse reused by Theorem 11.6 -/

/-! ## Unit bookkeeping for the reciprocal side -/

/-! ## Closing the remaining product bridge -/

end Ch14Thm116
end PartIII

namespace Pending
namespace Ch16MBIProof

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal

end Ch16MBIProof
end Pending

namespace PartIII
namespace Ch14Thm116

open PowerSeries
open Filter
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.RamanujanQuintic
open QseriesFormalization.Pending.RamanujanQuinticJTP
open QseriesFormalization.Pending.Ch16MBIProof

end Ch14Thm116
end PartIII
end QseriesFormalization

end


