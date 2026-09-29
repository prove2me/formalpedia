-- Prove2me | Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstance
-- name    : AlgebraicCurve_CanonicalLocalResidueInstance
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/ca8b9ea1-0e1c-5aa3-82b2-ae295dd41855
-- title:
--   Valuation-ring membership criterion via the order function
-- statement:
--   The setting is a field extension $F/K$ of fields and a place $v$ of $F$ over $K$, i.e. an object of the project's type `Place K F`, whose underlying datum is a valuation subring $\mathcal{O}_v \subseteq F$ containing the image of $K$, proper in $F$, and a principal ideal ring, hence a discrete valuation ring; $\operatorname{ord}_v$ denotes the associated normalised order function on $F$, normalised so that a uniformiser has order $1$ and with the convention $\operatorname{ord}_v 0 = 0$. Three lemmas, all kept private to the module, record the expected comparison between membership in $\mathcal{O}_v$ and the sign of the order. First, `ord_nonneg_of_mem_loc`: if $f \in \mathcal{O}_v$ then $0 \le \operatorname{ord}_v f$, proved by writing a nonzero element of the discrete valuation ring as a unit times a power of an irreducible element. Second, `mem_of_ord_nonneg_loc`: if $f \ne 0$ and $0 \le \operatorname{ord}_v f$ then $f \in \mathcal{O}_v$, obtained from the corresponding factorisation of $f$ in $F^{\times}$ as a unit of $\mathcal{O}_v$ times an integral power of an irreducible element. Third, `mem_iff_ord_nonneg_loc` combines the two into the equivalence $f \in \mathcal{O}_v \iff 0 \le \operatorname{ord}_v f$ for $f \ne 0$; the nonvanishing hypothesis is needed only for the direction reconstructing membership, because of the convention at $0$. The remaining material of the module consists of the ambient contexts for the local-residue and function-field development: places of $F/K$ with canonical local residue data, canonical divisors, places whose differential coordinate generates $\Omega_{F/K}$, and Henselian local rings with a coefficient embedding lifting the residue field.
--
--   **Relation to Mathlib.** `Place` and its order function $\operatorname{ord}_v$ are project notions built on Mathlib's `ValuationSubring` and discrete valuation ring API; these lemmas are the project's own restatements of the membership criterion in terms of $\operatorname{ord}_v$, and duplicate, under local private names, lemmas proved elsewhere in the project (for instance [`AlgebraicCurve.Place.mem_of_ord_nonneg_localResidueAux`](../def/AlgebraicCurve_LocalResidue.html#L63)).
--
--   **Where it is used.** These membership criteria are the basic bookkeeping behind the local residue maps `Place.localResidue` and the adelic Riemann–Roch and residue-theorem machinery for function fields $F/K$, which in this development serves the theory of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstance.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlaceCompletion
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Definitions.Def_AlgebraicCurve_WeilOfKaehler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section PerfectDischarge

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end PerfectDischarge

end AlgebraicCurve

end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open Polynomial IntermediateField

namespace ModularCurve.Ldgr37Ch

universe u v

section HenselEngine

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
variable {F : Type v} [Field F] [Algebra F (IsLocalRing.ResidueField R)]
variable (i : F →+* R)
variable (hi : (IsLocalRing.residue R).comp i
  = algebraMap F (IsLocalRing.ResidueField R))
variable (abar : IsLocalRing.ResidueField R)

include hi

end HenselEngine

section CoefficientEmbedding

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
variable {F : Type v} [Field F] [Algebra F (IsLocalRing.ResidueField R)]
variable (i : F →+* R)
variable (hi : (IsLocalRing.residue R).comp i
  = algebraMap F (IsLocalRing.ResidueField R))
variable (abar : IsLocalRing.ResidueField R)

include hi

end CoefficientEmbedding

section SectionIdentity

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
variable {F : Type v} [Field F] [Algebra F (IsLocalRing.ResidueField R)]
variable (i : F →+* R)
variable (hi : (IsLocalRing.residue R).comp i
  = algebraMap F (IsLocalRing.ResidueField R))
variable (abar : IsLocalRing.ResidueField R)

include hi

end SectionIdentity

end ModularCurve.Ldgr37Ch

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable [HasCanonicalLocalResidueKStar K F]

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]]

variable (K F)

variable {K F}

variable (K F)

variable {K F}

variable (K F)

variable {K F}

end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

namespace AlgebraicCurve

namespace Place

section DegPos

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

end DegPos

end Place

namespace Place

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F'] [Algebra K F] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] (w : Place K F')

end Restrict

end Place
end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

private theorem ord_nonneg_of_mem_loc {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

private theorem mem_of_ord_nonneg_loc {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

private theorem mem_iff_ord_nonneg_loc {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem_loc, v.mem_of_ord_nonneg_loc hf⟩

end Place

variable [HasCanonicalLocalResidueKStar K F]

end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

end Place

end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

end Place

namespace Place

variable (v : Place K F)

end Place

end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

end Place

namespace Place

variable (v : Place K F)

end Place

end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

end Place

namespace Place

variable (v : Place K F)

end Place

end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

namespace CanonicalLocalResidueDataS

variable {v} {σ : v.CoefficientFieldSection} (R : v.CanonicalLocalResidueDataS σ)

end CanonicalLocalResidueDataS

end Place

end AlgebraicCurve

end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000

noncomputable section

open IsDedekindDomain WithZero IsLocalRing Polynomial

namespace ModularCurve.Ldgr35Cl

open AlgebraicCurve

end ModularCurve.Ldgr35Cl

end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace ModularCurve.Ldgr35Cs

open AlgebraicCurve

end ModularCurve.Ldgr35Cs

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing Polynomial
open AlgebraicCurve
open scoped Polynomial

end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000

noncomputable section

open IsDedekindDomain WithZero IsLocalRing Polynomial

namespace ModularCurve.Ldgr36Si

open AlgebraicCurve

section Generic

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']

end Generic

end ModularCurve.Ldgr36Si

end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace ModularCurve.Ldgr36Rc

open AlgebraicCurve
open ModularCurve.Ldgr35Cs
open ModularCurve.Ldgr35Cl

section Restriction

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']

end Restriction

section ReCarve

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']

end ReCarve

section NoForkTies

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']

end NoForkTies

section PaymentRewire

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [HasCanonicalLocalResidueKStar K F']

end PaymentRewire

section Supply

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']

end Supply

end ModularCurve.Ldgr36Rc

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing Polynomial

end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace ModularCurve.Lg37

open AlgebraicCurve
open ModularCurve.Ldgr36Si
open ModularCurve.Ldgr36Rc
open ModularCurve.Ldgr35Cs

section CompletionCarrier

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end CompletionCarrier

section MovedCarrier

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
variable [HasCanonicalLocalResidueKStar K F']

end MovedCarrier

end ModularCurve.Lg37

end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing Polynomial

namespace Mp72a102T1

open AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.Ldgr37Ch

open scoped Polynomial

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end Engine

end Mp72a102T1

end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

noncomputable section

open IsLocalRing Polynomial

open scoped Polynomial

namespace ModularCurve.Mp72a102T3

open AlgebraicCurve ModularCurve.Lg37

section General

variable {R : Type*} [CommRing R] (I : Ideal R)

end General

section Carrier

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end Carrier

section RatProduction

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

variable [HasCanonicalLocalResidueKStar ℚ (RatFunc ℚ)]
variable [HasCanonicalLocalResidueKStar (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))]

end RatProduction

end ModularCurve.Mp72a102T3

end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing Polynomial

namespace Mp72a102T2

open AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.Ldgr35Cs

open scoped Polynomial

section ResidueCalculus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end ResidueCalculus

section RatProduction

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

end RatProduction

end Mp72a102T2

end

set_option autoImplicit false
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve.Lg37 Polynomial IntermediateField Mp72a102T1 Mp72a102T2

namespace ModularCurve.KwNo6Section

section GenericIso

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

end GenericIso

section GenericSection

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

end GenericSection

end ModularCurve.KwNo6Section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

noncomputable section

open IsDedekindDomain IsLocalRing Polynomial

open scoped Polynomial

namespace Mp72a103T2

open AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.Mp72a102T3
open Mp72a102T2

section Calculus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end Calculus

section RatProduction

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

variable [HasCanonicalLocalResidueKStar ℚ (RatFunc ℚ)]
variable [HasCanonicalLocalResidueKStar (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))]

end RatProduction

end Mp72a103T2

end

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Polynomial IsLocalRing AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.Mp72a102T3 Mp72a103T2 Mp72a102T1
open ModularCurve.KwNo6Section

namespace ModularCurve.KwNo6Pin

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end ModularCurve.KwNo6Pin

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Polynomial IsLocalRing AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.Mp72a102T3 Mp72a103T2 Mp72a102T1
open ModularCurve.KwNo6Section

namespace ModularCurve.KwNo6Pin

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section WitnessW
variable {v : Place K F} {ℓ : v.toValuationSubring}
  (hℓ : IsLocalRing.residue v.toValuationSubring ℓ ∉ Set.range (algebraMap K v.ResidueField))
include hℓ

end WitnessW

end ModularCurve.KwNo6Pin

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Polynomial IsLocalRing AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.KwNo6Section ModularCurve.KwNo6Pin
open Mp72a102T1

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end AlgebraicCurve


