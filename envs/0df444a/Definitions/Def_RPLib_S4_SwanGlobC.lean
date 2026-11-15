-- Prove2me | Definitions.Def_RPLib_S4_SwanGlobC
-- name    : RPLib_S4_SwanGlobC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:34:55.958193+00:00
-- url     : https://prove2.me/theorems/37a6c323-4ee4-4121-9cea-f7fb730819aa
-- title:
--   Local data of a Galois cover at a place over infinity, and the Swan conductor at infinity
-- statement:
--   For a Galois cover $C$ (a finite Galois extension $L$ of $\mathbb{F}_q(x)$ with group $G$) let $B_\infty$ be the integral closure in $L$ of the valuation ring of $\mathbb{F}_q(x)$ at infinity (with uniformiser $1/x$). The file shows that $B_\infty$ is a Dedekind domain with fraction field $L$, finite and free over the valuation ring with finite residue rings, and for a place $P$ of $B_\infty$ it builds the local data of the inertia group $I_P$, its ramification function, and the Swan conductor at infinity $$\mathrm{Sw}_P(\rho) = \sum_{u \ge 1} \frac{|I_{P,u}|}{|I_{P,0}|}\, \operatorname{cod}\big(V^{I_{P,u}}\big)$$ of a representation $\rho$ of $G$, which is nonnegative.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapters I and IV; N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), Chapter 1

import Mathlib
import Definitions.Def_RPLib_S4_SwanGlobVal
import Definitions.Def_RPLib_S4_GalCover

/-!
# S4-Swan (K2), part 17: local data of a Galois cover at a place over `∞`

For a finite separable `L / Fq(X)` the chart at infinity `infChart Fq L = integralClosure O_∞ L` is a Dedekind
domain, finite and free over `O_∞`, with finite residue rings (instances below, as in `S3-Places_B` for `Rinf`).
For a Galois cover `C : GalCover A` with function field `L`, a nonzero prime `P` of the chart gives local data
`C.infLocData Fq L P : LocData (infInertia P) L` (the `P`-adic valuation on `L` with the inertia group at `P`),
hence a ramification function `C.infRamFn` on the inertia group and the Swan conductor `C.swanInf ρ P` of a
representation `ρ` of the cover group at `P`.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain Polynomial

namespace RamanujanPetersson

namespace GalCover

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal

section InfChart

variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] (L : Type) [Field L] [Algebra (RatFunc Fq) L]
  [FiniteDimensional (RatFunc Fq) L] [Algebra.IsSeparable (RatFunc Fq) L]

instance infChart_isDedekindDomain : IsDedekindDomain (infChart Fq L) :=
  integralClosure.isDedekindDomain (Places.Oinf Fq) (RatFunc Fq) L

instance infChart_isFractionRing : IsFractionRing (infChart Fq L) L :=
  integralClosure.isFractionRing_of_finite_extension (RatFunc Fq) L

instance infChart_finite : Module.Finite (Places.Oinf Fq) (infChart Fq L) :=
  IsIntegralClosure.finite (Places.Oinf Fq) (RatFunc Fq) L _

instance infChart_free : Module.Free (Places.Oinf Fq) (infChart Fq L) :=
  IsIntegralClosure.module_free (Places.Oinf Fq) (RatFunc Fq) L _

theorem finite_quot_span [Fintype Fq] (a : infChart Fq L) (ha : a ≠ 0) :
    Finite (infChart Fq L ⧸ Ideal.span {a}) := by
  have hN : Algebra.norm (Places.Oinf Fq) a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  apply Nat.finite_of_card_ne_zero
  rw [Places.card_quot_eq_card_quot_norm (A := Places.Oinf Fq) a ha, Places.card_quot_Oinf Fq hN]
  exact pow_ne_zero _ Fintype.card_ne_zero

instance infChart_finite_residue [Fintype Fq] (P : HeightOneSpectrum (infChart Fq L)) :
    Finite (infChart Fq L ⧸ P.asIdeal) := by
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have := finite_quot_span Fq L a ha0
  exact Finite.of_surjective _
    (Ideal.Quotient.factor_surjective ((Ideal.span_singleton_le_iff_mem _).mpr haP))

/-- A boundary place at infinity as a height-one prime of the chart. -/
def IsInfBoundary.toHOS {P : Ideal (infChart Fq L)} (hP : IsInfBoundary Fq L P) :
    HeightOneSpectrum (infChart Fq L) :=
  ⟨P, hP.1, hP.2⟩

end InfChart

section SwanInf

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)
variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] [Algebra A (RatFunc Fq)]
  [IsFractionRing A (RatFunc Fq)]
variable (L : Type) [Field L] [Algebra C.B L] [IsFractionRing C.B L] [Algebra (RatFunc Fq) L]
  [Algebra A L] [IsScalarTower A (RatFunc Fq) L] [IsScalarTower A C.B L] [MulSemiringAction C.G L]
  [SMulDistribClass C.G C.B L]

include C in
/-- The function field of a Galois cover is separable over `Fq(X)`. -/
theorem isSeparable_frac : Algebra.IsSeparable (RatFunc Fq) L := by
  haveI := C.isGaloisGroup_frac (RatFunc Fq) L
  haveI := IsGaloisGroup.isGalois C.G (RatFunc Fq) L
  infer_instance

variable [FiniteDimensional (RatFunc Fq) L] [Algebra.IsSeparable (RatFunc Fq) L] [Fintype Fq]

/-- The local data of the cover at a place `P` over `∞`: the `P`-adic valuation with the inertia group. -/
def infLocData (P : HeightOneSpectrum (infChart Fq L)) :
    Swan.LocData (C.infInertia Fq L P.asIdeal) L :=
  letI := C.chartAction (RatFunc Fq) L (Places.Oinf Fq)
  haveI := C.isGaloisGroup_chart (RatFunc Fq) L (Places.Oinf Fq)
  Swan.inertiaLocData (R := Places.Oinf Fq) (fun _ _ => rfl) P

theorem infLocData_v (P : HeightOneSpectrum (infChart Fq L)) :
    (C.infLocData Fq L P).v = Swan.adicAdd P := rfl

/-- The ramification function of the inertia group at a place over `∞`. -/
def infRamFn (P : HeightOneSpectrum (infChart Fq L)) : Swan.RamFn (C.infInertia Fq L P.asIdeal) :=
  (C.infLocData Fq L P).ramFn

instance infInertia_fintype (P : HeightOneSpectrum (infChart Fq L)) :
    Fintype (C.infInertia Fq L P.asIdeal) :=
  Fintype.ofFinite _

/-- The Swan conductor at a place `P` over `∞` of a representation of the cover group. -/
def swanInf {k V : Type} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k C.G V)
    (P : HeightOneSpectrum (infChart Fq L)) : ℚ :=
  (C.infRamFn Fq L P).swan (ρ.comp (C.infInertia Fq L P.asIdeal).subtype)

theorem swanInf_nonneg {k V : Type} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k C.G V)
    (P : HeightOneSpectrum (infChart Fq L)) : 0 ≤ C.swanInf Fq L ρ P :=
  Swan.RamFn.swan_nonneg _ _

end SwanInf

end GalCover

end RamanujanPetersson


