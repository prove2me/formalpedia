-- Prove2me | Definitions.Def_RPLib_FX_GOSC_02
-- name    : RPLib_FX_GOSC_02
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:42:45.676453+00:00
-- url     : https://prove2.me/theorems/34a9ad91-33ec-45e3-9b33-f7707cb39d85
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 02 of 14
-- statement:
--   File 02 of 14 of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S3.RR_C`: Riemann-Roch, part C: the concrete instance for function fields
--   * `S4.Def_RP_GalCover`: S4-GalCover draft v1: Galois etale covers and Frobenius (S4_DESIGN section 1)
--   * `S4.Def_RP_CP4a_HypC`: S4-CP4a, part g3: the place at infinity of `y² = x⁵ + 1`
--   * `S4.Def_RP_PicDescent_E4`: S4-PicDescent, part E4 (review R6): function fields whose full constant field is `F_(q^d)`
--   * `S4.Def_RP_Lefschetz_PtData`: S4-Lefschetz, L6b: the point data of the trace formula
--   * `S4.Def_RP_GOS_B_Cot`: S4-GOS-B, part Cot: abstract cotrace data between two `RR.Data` (Riemann-Hurwitz, O2a)
--   * `S4.Def_RP_GOS_B_Inst`: S4-GOS-B, part Inst: the cotrace data of a two-chart extension
--   * `S4.Def_RP_GOS_B_Cot2`: S4-GOS-B, part Cot2: the cotrace Weil differential and abstract Riemann-Hurwitz (O2b)
--   * `S4.Def_RP_GOS_B_Cot3`: S4-GOS-B, part Cot3: degree of the conorm and the abstract Riemann-Hurwitz formula
--   * `S4.Def_RP_GOS_B_Deg`: S4-GOS-B, part Deg: the fundamental identity in degree form
--   * `S4.Def_RP_CupDuality_Cover`: Curve duality (unit S4-CurveDuality), finite covers of function fields: contraction of places
--   * `S4.Def_RP_Swan_GlobC`: S4-Swan (K2), part 17: local data of a Galois cover at a place over `∞`
--   * `S4.Def_RP_GOS_B_Shf`: S4-GOS-B, part Shf: integer linear recurrences through the shift operator (O6d, algebra)
--   * `S4.Def_RP_GOS_B_Lvl`: S4-GOS-B, part Lvl: `𝔽_{q^m}`-points as Frobenius-fixed points (O6c, generic)
--   * `S4.Def_RP_GOS_B_Pos`: S4-GOS-B, part Pos: subgroup sums of the character from an integer recurrence of the counts (O6a)
--   * `S4.Def_RP_GOS_C_B1a`: S4-GOS-C, part B1a: idempotents of `End(Y)[C]` and traces on projective modules (abelian `C`)
--   * `S4.Def_RP_GOS_C_B1b`: S4-GOS-C, part B1b: the conjugation argument and restriction of Higman elements
--   * `S4.Def_RP_GOS_C_B1c`: S4-GOS-C, part B1c: characters of projective modules vanish on `l`-singular elements
--   * `S4.Def_RP_GOS_C_C0`: S4-GOS-C, part C0: traces agree on two lifts of the same module
--   * `S4.Def_RP_GOS_C_LIFTa`: S4-GOS-C, part LIFTa: permutation modules and reduction maps for lifting projective modules
--   * `S4.Def_RP_GOS_C_LIFTb`: S4-GOS-C, part LIFTb: lifting the idempotent of a projective module
--   * `S4.Def_RP_GOS_C_LIFTc`: S4-GOS-C, part LIFTc: projective modules lift
--   * `S4.Def_RP_GOS_C_BETA`: S4-GOS-C, part BETA: the Brauer trace function `β`
--   * `S4.Def_RP_GOS_C_HSR`: S4-GOS-C, part HSR: the sum of the character of a projective module
--   * `S4.Def_RP_GOS_C_HSR2`: S4-GOS-C, part HSR2: coinvariants of a lift
--   * `S4.Def_RP_GOS_C_TLIFT`: S4-GOS-C, part TLIFT: reductions, `1 ⊗ q = 0`, and tensor products of lifts
--   * `S4.Def_RP_GOS_C_EUL`: S4-GOS-C, part EUL: the Euler characteristic of the perfect complex is `h²_c - h¹_c`
--   * `S4.Def_RP_GOS_C_GOSF`: S4-GOS-C, part GOSF: the abstract GOS combination and integrality
--   * `S4.Def_RP_Swan_Slope1a`: S4-Swan (K2), part 28: slope-1 local structure (abstract part)
--   * `S4.Def_RP_GOS_C_WILD`: S4-GOS-C, part WILD: wild ramification groups are `p`-groups
--   * `S4.Def_RP_GOS_C_GOSI`: S4-GOS-C, part GOSI: the integer Grothendieck-Ogg-Shafarevich identity on the concrete cover
--   * `S4.Def_RP_GOS_C_MASCH`: S4-GOS-C, part MASCH: coinvariants and invariants for groups of invertible order
--   * `S4.Def_RP_Swan_GlobPc`: S4-Swan (K2), part 20: Swan conductors and breaks at `∞` do not depend on the place
--   * `S4.Def_RP_GOS_C_GOSF2`: S4-GOS-C, part GOSF2: Grothendieck-Ogg-Shafarevich on `𝔸¹`
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib
import Definitions.Def_RPLib_F2_001
import Definitions.Def_RPLib_FX_GOSC_01

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 02 of 14

Declarations of the formalization of the Grothendieck–Ogg–Shafarevich formula for lisse sheaves on the affine
line over a finite field (h²_c - h¹_c = rank - Swan conductor at infinity), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S3.RR_C`: Riemann-Roch, part C: the concrete instance for function fields
* `S4.Def_RP_GalCover`: S4-GalCover draft v1: Galois etale covers and Frobenius (S4_DESIGN section 1)
* `S4.Def_RP_CP4a_HypC`: S4-CP4a, part g3: the place at infinity of `y² = x⁵ + 1`
* `S4.Def_RP_PicDescent_E4`: S4-PicDescent, part E4 (review R6): function fields whose full constant field is `F_(q^d)`
* `S4.Def_RP_Lefschetz_PtData`: S4-Lefschetz, L6b: the point data of the trace formula
* `S4.Def_RP_GOS_B_Cot`: S4-GOS-B, part Cot: abstract cotrace data between two `RR.Data` (Riemann-Hurwitz, O2a)
* `S4.Def_RP_GOS_B_Inst`: S4-GOS-B, part Inst: the cotrace data of a two-chart extension
* `S4.Def_RP_GOS_B_Cot2`: S4-GOS-B, part Cot2: the cotrace Weil differential and abstract Riemann-Hurwitz (O2b)
* `S4.Def_RP_GOS_B_Cot3`: S4-GOS-B, part Cot3: degree of the conorm and the abstract Riemann-Hurwitz formula
* `S4.Def_RP_GOS_B_Deg`: S4-GOS-B, part Deg: the fundamental identity in degree form
* `S4.Def_RP_CupDuality_Cover`: Curve duality (unit S4-CurveDuality), finite covers of function fields: contraction of places
* `S4.Def_RP_Swan_GlobC`: S4-Swan (K2), part 17: local data of a Galois cover at a place over `∞`
* `S4.Def_RP_GOS_B_Shf`: S4-GOS-B, part Shf: integer linear recurrences through the shift operator (O6d, algebra)
* `S4.Def_RP_GOS_B_Lvl`: S4-GOS-B, part Lvl: `𝔽_{q^m}`-points as Frobenius-fixed points (O6c, generic)
* `S4.Def_RP_GOS_B_Pos`: S4-GOS-B, part Pos: subgroup sums of the character from an integer recurrence of the counts (O6a)
* `S4.Def_RP_GOS_C_B1a`: S4-GOS-C, part B1a: idempotents of `End(Y)[C]` and traces on projective modules (abelian `C`)
* `S4.Def_RP_GOS_C_B1b`: S4-GOS-C, part B1b: the conjugation argument and restriction of Higman elements
* `S4.Def_RP_GOS_C_B1c`: S4-GOS-C, part B1c: characters of projective modules vanish on `l`-singular elements
* `S4.Def_RP_GOS_C_C0`: S4-GOS-C, part C0: traces agree on two lifts of the same module
* `S4.Def_RP_GOS_C_LIFTa`: S4-GOS-C, part LIFTa: permutation modules and reduction maps for lifting projective modules
* `S4.Def_RP_GOS_C_LIFTb`: S4-GOS-C, part LIFTb: lifting the idempotent of a projective module
* `S4.Def_RP_GOS_C_LIFTc`: S4-GOS-C, part LIFTc: projective modules lift
* `S4.Def_RP_GOS_C_BETA`: S4-GOS-C, part BETA: the Brauer trace function `β`
* `S4.Def_RP_GOS_C_HSR`: S4-GOS-C, part HSR: the sum of the character of a projective module
* `S4.Def_RP_GOS_C_HSR2`: S4-GOS-C, part HSR2: coinvariants of a lift
* `S4.Def_RP_GOS_C_TLIFT`: S4-GOS-C, part TLIFT: reductions, `1 ⊗ q = 0`, and tensor products of lifts
* `S4.Def_RP_GOS_C_EUL`: S4-GOS-C, part EUL: the Euler characteristic of the perfect complex is `h²_c - h¹_c`
* `S4.Def_RP_GOS_C_GOSF`: S4-GOS-C, part GOSF: the abstract GOS combination and integrality
* `S4.Def_RP_Swan_Slope1a`: S4-Swan (K2), part 28: slope-1 local structure (abstract part)
* `S4.Def_RP_GOS_C_WILD`: S4-GOS-C, part WILD: wild ramification groups are `p`-groups
* `S4.Def_RP_GOS_C_GOSI`: S4-GOS-C, part GOSI: the integer Grothendieck-Ogg-Shafarevich identity on the concrete cover
* `S4.Def_RP_GOS_C_MASCH`: S4-GOS-C, part MASCH: coinvariants and invariants for groups of invertible order
* `S4.Def_RP_Swan_GlobPc`: S4-Swan (K2), part 20: Swan conductors and breaks at `∞` do not depend on the place
* `S4.Def_RP_GOS_C_GOSF2`: S4-GOS-C, part GOSF2: Grothendieck-Ogg-Shafarevich on `𝔸¹`
-/

set_option autoImplicit false

-- ===== S3.RR_C =====
section

/-!
# Riemann-Roch, part C: the concrete instance for function fields

The abstract axioms of `RR_A` (`Data.Axioms`) hold for the places of a function field
`F / Fq` (unit S3-Places): the local index `[ball (n+1) : ball n] = q ^ deg P` (generic
Dedekind lemma `relIndex_ballG`), the product formula, `L(0)` = constants, and the Riemann
input with `B` the pole divisor of `x` and `C` the pole divisor of an integral basis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial

namespace RamanujanPetersson.RR

/-! ### The local index at a place of a Dedekind domain -/

section LocalIndex

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {K : Type*} [Field K] [Algebra S K]
  [IsFractionRing S K]

end LocalIndex

/-! ### The data of a function field -/

section FunctionField

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable {Fq F}

variable (Fq F)

variable {Fq F}

end FunctionField

/-! ### The Riemann input -/

section RiemannInput

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable {Fq F}

end RiemannInput

/-! ### Riemann-Roch for function fields -/

section Concrete

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- A place of degree one forces `ℓ(0) = 1`. -/
theorem ellF_zero_of_deg_one {P : Places.Place Fq F} (hP : P.deg = 1) : ellF Fq F 0 = 1 :=
  ellF_zero_of_bot (Places.constField_eq_bot_of_deg_one Fq F hP)

/-! #### The classical statements (full constant field `Fq`, so `ℓ(0) = 1`) -/

section FullConstantField

variable (hk : Places.constField Fq F = ⊥)
include hk

end FullConstantField

end Concrete

end RamanujanPetersson.RR


end

-- ===== S4.Def_RP_GalCover =====
section

/-!
# S4-GalCover draft v1: Galois etale covers and Frobenius (S4_DESIGN section 1)
-/

set_option autoImplicit false

open scoped Pointwise

namespace RamanujanPetersson

namespace GalCover

variable {A : Type} [CommRing A] [IsDomain A]

/-! ## Constants, the geometric subgroup, Frobenius on constants -/

section Constants

variable (Fq : Type) [Field Fq] [Algebra Fq A]

end Constants

/-! ## Morphisms of covers -/

/-! ## Etale Galois extensions have trivial inertia (bridge `ofEtale`) -/

section Etale

variable {B G : Type} [CommRing B] [IsDomain B] [Algebra A B] [Group G] [Finite G]
  [MulSemiringAction G B] [IsGaloisGroup G A B]

end Etale

end GalCover

/-! ## The etale fundamental group and the finite-quotient bridge -/

section Pi1

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

section Bridge

variable [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]

end Bridge

end Pi1

/-! ## Charts over other base rings: the infinity chart and boundary places (review R5) -/

namespace GalCover

section Charts

variable {A : Type} [CommRing A] [IsDomain A]
variable (K L : Type) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

variable (R0 : Type) [CommRing R0] [IsDomain R0] [IsIntegrallyClosed R0] [Algebra R0 K]
  [IsFractionRing R0 K] [Algebra R0 L] [IsScalarTower R0 K L]

end Charts

/-! ### The two charts of a base curve inside `𝔸¹`: finite (`Fq[X]`) and infinity (`O_∞`) -/

section CurveCharts

open Polynomial

variable {A : Type} [CommRing A] [IsDomain A]
variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] [Algebra A (RatFunc Fq)]
  [IsFractionRing A (RatFunc Fq)]
variable (L : Type) [Field L] [Algebra (RatFunc Fq) L] [Algebra A L] [IsScalarTower A (RatFunc Fq) L]

/-- The infinity chart: the integral closure in `L` of the valuation ring `O_∞ ⊆ Fq(X)` at `x = ∞`. Its nonzero
primes are the places of the cover over `∞`. -/
noncomputable abbrev infChart : Subalgebra (Places.Oinf Fq) L := integralClosure (Places.Oinf Fq) L

variable [Algebra Fq[X] L] [IsScalarTower Fq[X] (RatFunc Fq) L]

end CurveCharts

end GalCover

end RamanujanPetersson


end

-- ===== S4.Def_RP_CP4a_HypC =====
section

/-!
# S4-CP4a, part g3: the place at infinity of `y² = x⁵ + 1`

For `F = Fq(x, y)`, `y² = x⁵ + 1` (`2 ≠ 0` in `Fq`):
* `ord_tF_eq_two`, `deg_infPlace_eq_one`: every place over `x = ∞` has `ord(1/x) = 2` and degree one
  (`w = y/x³` has `w² = (1/x)(1 + 1/x⁵)`, so `ord(1/x)` is even, and `Σ ord(1/x) deg P = 2`);
* `infPlace_eq`: there is exactly one such place; `constField_hyp`: the full constant field is `Fq`;
* `ord_poly`: `ord_∞ a(x) = -2 deg a`; `ord_yF`: `ord_∞ y = -5`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.CP4a.Hyp2

open Places ZetaSB

noncomputable section

section Gen

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [FiniteQuot S] {K : Type*} [Field K] [Algebra S K]
  [IsFractionRing S K]

theorem ord_one' (P : HeightOneSpectrum S) : Places.ord P (1 : K) = 0 := by
  simp [Places.ord]

theorem ord_pow' (P : HeightOneSpectrum S) {f : K} (hf : f ≠ 0) (k : ℕ) :
    Places.ord P (f ^ k) = k * Places.ord P f := by
  induction k with
  | zero => rw [pow_zero, ord_one', Nat.cast_zero, zero_mul]
  | succ k ih => rw [pow_succ, Places.ord_mul P (pow_ne_zero _ hf) hf, ih]; push_cast; ring

theorem ord_alg_nonneg (P : HeightOneSpectrum S) (a : S) : 0 ≤ Places.ord P (algebraMap S K a) := by
  by_cases ha : a = 0
  · rw [ha, map_zero, Places.ord_zero]
  · rw [Places.ord_algebraMap P ha]; exact Int.natCast_nonneg _

theorem one_le_ord_of_mem (P : HeightOneSpectrum S) {a : S} (ha : a ≠ 0) (hP : a ∈ P.asIdeal) :
    1 ≤ Places.ord P (algebraMap S K a) := by
  rw [Places.ord_algebraMap P ha]
  have h : Places.cnt P a ≠ 0 := by
    rw [Places.cnt, Associates.count_ne_zero_iff_dvd
      (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]) P.irreducible, Ideal.dvd_span_singleton]
    exact hP
  omega

end Gen

section Hyp

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)] [Fact ((2 : Fq) ≠ 0)]

end Hyp

end

end RamanujanPetersson.CP4a.Hyp2


end

-- ===== S4.Def_RP_PicDescent_E4 =====
section

/-!
# S4-PicDescent, part E4 (review R6): function fields whose full constant field is `F_(q^d)`

For a function field `F / Fq` with full constant field `K = constField Fq F` (`#K = q ^ d`, `d = [K : Fq]`,
`card_constField`), `F` is rebased as a function field over `K` with the same separating element `x`:
* instances `Algebra K[X] F` (`x ↦ xF Fq F`), `Algebra (RatFunc K) F`, the towers, `FunctionField K F`,
  `Algebra.IsSeparable (RatFunc K) F`; `xF_constField : xF K F = xF Fq F`;
* `constField_K : constField K F = ⊥` (`F / K` is geometrically connected),
  `exists_deg_one_K` (F. K. Schmidt over `K`), `finite_Pic0_K`;
so parts A–E apply over `K` with `q ^ d` in place of `q`; the `K`-Frobenius is `π ^ d` (`mem_Lc_K`).
Restated over `K`: `picBarEquivK`, `pic0BarEquivK`, `picBaseEquivK`, `pic0BaseEquivK`, `classNumber_barK`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places ZetaSB

section Rebase

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

noncomputable instance fintype_constField : Fintype (constField Fq F) :=
  @Fintype.ofFinite _ (Module.finite_of_finite Fq)

section Descent

-- `Algebra K Ω` and `IsScalarTower K F Ω` are Mathlib's intermediate-field instances (through `F`).
variable {Ω : Type*} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]

end Descent

end Rebase

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_Lefschetz_PtData =====
section

/-!
# S4-Lefschetz, L6b: the point data of the trace formula

* `finite_homs_of_adjoin`: ring maps `R → Ω` out of a finitely generated `k`-algebra, with fixed restriction to `k`
  and values in a finite set, form a finite set.
* `finite_ptSet`: the `F_{q^m}`-points of `U` (ring maps `u : R → Ω` with prescribed restriction to `F_q` and
  `Fr ∘ u = u`, `Fr = (·)^(q^m)`) form a finite set.
* **`exists_ptData`**: a finite set `S` of these points together with normalized Frobenius elements `F_u`: exactly the
  hypotheses `hS`, `hFu` of `lefschetz_twist`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover

section PtDataGen

end PtDataGen

section PtData

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

/-- `R_fin = O_K` is a finitely generated `F_q`-algebra. -/
theorem finiteType_RfinFq : Algebra.FiniteType Fq (Rfin Fq K) :=
  Algebra.FiniteType.trans (S := Fq[X]) inferInstance inferInstance

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e)

end PtData

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_GOS_B_Cot =====
section

/-!
# S4-GOS-B, part Cot: abstract cotrace data between two `RR.Data` (Riemann-Hurwitz, O2a)

A `Cotrace dK dL` packages the place map `pr : ιL → ιK` (with a section), ramification indices `e`,
the different exponents `d ≥ 0`, a `K`-linear trace `tr : L → K`, and the local facts
F2 (`trace_le`), F4 (`trace_sharp`), R (`resid`) and fibrewise approximation (`approx`).
Here: the conorm `con`, the semilocal adeles `S` (constant on fibres), the trace `Tfun` on them, and
* `Tfun_mem_AD`: `α ∈ S ∩ A_L(con D + d) → T α ∈ A_K(D)`;
* `Tfun_mem_adeles`: `α ∈ S → T α ∈ adeles_K`;
* `exists_S_sub_mem_AD` (F1): every adele of `L` is `s + a` with `s ∈ S`, `a ∈ A_L(E)`.
-/

set_option autoImplicit false

noncomputable section

open WithZero RamanujanPetersson.RR

namespace RamanujanPetersson.GOS

variable {Fq K L ιK ιL : Type*} [Field Fq] [Field K] [Field L] [Algebra Fq K] [Algebra Fq L]
  [Algebra K L]

/-- Abstract cotrace data for an extension `L / K` of function fields given by `RR.Data`. -/
structure Cotrace (dK : Data Fq K ιK) (dL : Data Fq L ιL) where
  pr : ιL → ιK
  sec : ιK → ιL
  pr_sec : ∀ P, pr (sec P) = P
  fib_finite : ∀ P, {Q | pr Q = P}.Finite
  e : ιL → ℕ
  d : ιL →₀ ℤ
  d_nonneg : 0 ≤ d
  tr : L →ₗ[K] K
  v_algebraMap : ∀ Q (c : K), dL.v Q (algebraMap K L c) = dK.v (pr Q) c ^ e Q
  trace_le : ∀ P (n : ℤ) (y : L), (∀ Q, pr Q = P → dL.v Q y ≤ exp ((e Q : ℤ) * n + d Q)) →
    dK.v P (tr y) ≤ exp n
  trace_sharp : ∀ Q0 (n : ℤ), ∃ y : L, (∀ Q, pr Q = pr Q0 →
    dL.v Q y ≤ exp ((e Q : ℤ) * n + d Q + Finsupp.single Q0 1 Q)) ∧ dK.v (pr Q0) (tr y) = exp (n + 1)
  resid : ∀ P (n : ℤ) (z w : K), dK.v P z ≤ exp (n + 1) → dK.v P w = exp (n + 1) →
    ∃ c : K, dK.v P c ≤ 1 ∧ dK.v P (z - c * w) ≤ exp n
  approx : ∀ P (α : ιL → L) (E : ιL → ℤ), ∃ y : L, ∀ Q, pr Q = P → dL.v Q (α Q - y) ≤ exp (E Q)

namespace Cotrace

variable {dK : Data Fq K ιK} {dL : Data Fq L ιL} (c : Cotrace dK dL)

/-- The conorm of a divisor: `(con D)(Q) = e_Q D(pr Q)`. -/
def con (D : ιK →₀ ℤ) : ιL →₀ ℤ :=
  Finsupp.ofSupportFinite (fun Q => (c.e Q : ℤ) * D (c.pr Q)) (by
    apply (D.support.finite_toSet.biUnion fun P _ => c.fib_finite P).subset
    intro Q hQ
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hQ
    exact Set.mem_biUnion (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hQ.2)) rfl)

theorem con_apply (D : ιK →₀ ℤ) (Q : ιL) : c.con D Q = (c.e Q : ℤ) * D (c.pr Q) := rfl

/-- Semilocal adeles: adeles of `L` constant on the fibres of `pr`. -/
def S : Submodule Fq (ιL → L) where
  carrier := {α | α ∈ dL.adeles ∧ ∀ Q, α Q = α (c.sec (c.pr Q))}
  add_mem' {a b} ha hb := ⟨dL.adeles.add_mem ha.1 hb.1, fun Q => by
    show a Q + b Q = a _ + b _
    rw [← ha.2 Q, ← hb.2 Q]⟩
  zero_mem' := ⟨dL.adeles.zero_mem, fun _ => rfl⟩
  smul_mem' r a ha := ⟨dL.adeles.smul_mem r ha.1, fun Q => by
    show r • a Q = r • a _
    rw [← ha.2 Q]⟩

theorem mem_S {α : ιL → L} : α ∈ c.S ↔ α ∈ dL.adeles ∧ ∀ Q, α Q = α (c.sec (c.pr Q)) := Iff.rfl

/-- **F1.** Every adele of `L` is a semilocal adele plus an element of `A_L(E)`. -/
theorem exists_S_sub_mem_AD {α : ιL → L} (hα : α ∈ dL.adeles) (E : ιL →₀ ℤ) :
    ∃ s ∈ c.S, α - s ∈ dL.AD E := by
  choose y hy using fun P => c.approx P α E
  have hsub : α - (fun Q => y (c.pr Q)) ∈ dL.AD E := dL.mem_AD.2 fun Q => hy (c.pr Q) Q rfl
  refine ⟨fun Q => y (c.pr Q), ⟨?_, fun Q => by simp only [c.pr_sec]⟩, hsub⟩
  have := dL.adeles.sub_mem hα (dL.AD_le_adeles E hsub)
  rwa [sub_sub_cancel] at this

variable [IsScalarTower Fq K L]

/-- The trace on functions `ιL → L`: `(T α)(P) = tr (α (sec P))`. -/
def Tfun : (ιL → L) →ₗ[Fq] (ιK → K) :=
  LinearMap.pi fun P => (c.tr.restrictScalars Fq).comp (LinearMap.proj (c.sec P))

@[simp] theorem Tfun_apply (α : ιL → L) (P : ιK) : c.Tfun α P = c.tr (α (c.sec P)) := rfl

theorem Tfun_mem_AD {α : ιL → L} (hα : α ∈ c.S) {D : ιK →₀ ℤ} (hD : α ∈ dL.AD (c.con D + c.d)) :
    c.Tfun α ∈ dK.AD D := by
  rw [dK.mem_AD]
  intro P
  rw [Tfun_apply]
  apply c.trace_le P (D P)
  intro Q hQ
  have h1 := dL.mem_AD.1 hD Q
  rw [hα.2 Q, Finsupp.add_apply, con_apply, hQ] at h1
  exact h1

theorem Tfun_mem_adeles {α : ιL → L} (hα : α ∈ c.S) : c.Tfun α ∈ dK.adeles := by
  rw [dK.mem_adeles]
  apply ((dL.mem_adeles.1 hα.1).image c.pr).subset
  intro P hP
  simp only [Set.mem_ofPred_eq, Tfun_apply] at hP
  by_contra h
  apply absurd hP (not_lt.2 _)
  have h0 := c.trace_le P 0 (α (c.sec P)) fun Q hQ => by
    have hQ' : ¬ 1 < dL.v Q (α Q) := fun h' => h ⟨Q, h', hQ⟩
    rw [hα.2 Q, hQ] at hQ'
    rw [mul_zero, zero_add]
    have hd0 : (0 : ℤ) ≤ c.d Q := c.d_nonneg Q
    exact (not_lt.1 hQ').trans (by rw [← exp_zero]; exact exp_le_exp.2 hd0)
  rwa [exp_zero] at h0

end Cotrace

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Inst =====
section

/-!
# S4-GOS-B, part Inst: the cotrace data of a two-chart extension

`ordDiv J`: the divisor `Q ↦ ord_Q J` of an ideal (`0` for `J = ⊥`).
`Cotrace.ofCharts`: for `Data` on `HOS A1 ⊕ HOS A2` (field `K`) and `HOS B1 ⊕ HOS B2` (field `L`) whose
valuations are the adic ones, and Dedekind charts `A_i → B_i` as in `Def_RP_GOS_B_Loc`, the `Cotrace` with
`pr = under`, `e = ramificationIdx'`, `d = ord (differentIdeal A_i B_i)`, `tr = Algebra.trace K L`.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero RamanujanPetersson.RR
open scoped nonZeroDivisors

namespace RamanujanPetersson.GOS

section OrdDiv

variable {S : Type*} [CommRing S] [IsDedekindDomain S]

end OrdDiv

section Builder

variable {Fq K L : Type*} [Field Fq] [Field K] [Field L] [Algebra Fq K] [Algebra Fq L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable {A1 B1 A2 B2 : Type*}
  [CommRing A1] [IsDedekindDomain A1] [CommRing B1] [IsDedekindDomain B1] [Algebra A1 B1]
  [Module.IsTorsionFree A1 B1] [Algebra A1 K] [IsFractionRing A1 K] [Algebra A1 L] [IsScalarTower A1 K L]
  [Algebra B1 L] [IsFractionRing B1 L] [IsScalarTower A1 B1 L] [Module.Finite A1 B1]
  [IsIntegralClosure B1 A1 L] [Algebra.IsIntegral A1 B1]
  [CommRing A2] [IsDedekindDomain A2] [CommRing B2] [IsDedekindDomain B2] [Algebra A2 B2]
  [Module.IsTorsionFree A2 B2] [Algebra A2 K] [IsFractionRing A2 K] [Algebra A2 L] [IsScalarTower A2 K L]
  [Algebra B2 L] [IsFractionRing B2 L] [IsScalarTower A2 B2 L] [Module.Finite A2 B2]
  [IsIntegralClosure B2 A2 L] [Algebra.IsIntegral A2 B2]
variable {dK : Data Fq K (HeightOneSpectrum A1 ⊕ HeightOneSpectrum A2)}
  {dL : Data Fq L (HeightOneSpectrum B1 ⊕ HeightOneSpectrum B2)}

/-- The cotrace data of a two-chart extension. -/
def Cotrace.ofCharts (hK1 : ∀ P : HeightOneSpectrum A1, dK.v (Sum.inl P) = P.valuation K)
    (hK2 : ∀ P : HeightOneSpectrum A2, dK.v (Sum.inr P) = P.valuation K)
    (hL1 : ∀ Q : HeightOneSpectrum B1, dL.v (Sum.inl Q) = Q.valuation L)
    (hL2 : ∀ Q : HeightOneSpectrum B2, dL.v (Sum.inr Q) = Q.valuation L) : Cotrace dK dL where
  pr := Sum.map (HeightOneSpectrum.under A1) (HeightOneSpectrum.under A2)
  sec := Sum.map (fun P => (exists_under_eq A1 (K := K) (L := L) (B := B1) P).choose)
    (fun P => (exists_under_eq A2 (K := K) (L := L) (B := B2) P).choose)
  pr_sec P := by
    rcases P with P | P
    · exact congrArg Sum.inl (exists_under_eq A1 (K := K) (L := L) (B := B1) P).choose_spec
    · exact congrArg Sum.inr (exists_under_eq A2 (K := K) (L := L) (B := B2) P).choose_spec
  fib_finite P := by
    rcases P with P | P
    · apply ((finite_under_eq A1 (B := B1) P).image Sum.inl).subset
      rintro (Q | Q) hQ
      · exact ⟨Q, Sum.inl.inj hQ, rfl⟩
      · simp at hQ
    · apply ((finite_under_eq A2 (B := B2) P).image Sum.inr).subset
      rintro (Q | Q) hQ
      · simp at hQ
      · exact ⟨Q, Sum.inr.inj hQ, rfl⟩
  e := Sum.elim (fun Q => (Q.under A1).asIdeal.ramificationIdx' Q.asIdeal)
    (fun Q => (Q.under A2).asIdeal.ramificationIdx' Q.asIdeal)
  d := (ordDiv (differentIdeal A1 B1)).sumElim (ordDiv (differentIdeal A2 B2))
  d_nonneg Q := by
    rcases Q with Q | Q
    · exact ordDiv_nonneg _ Q
    · exact ordDiv_nonneg _ Q
  tr := Algebra.trace K L
  v_algebraMap Q c := by
    rcases Q with Q | Q
    · show dL.v (Sum.inl Q) _ = dK.v (Sum.inl (Q.under A1)) c ^ (Q.under A1).asIdeal.ramificationIdx' Q.asIdeal
      rw [hL1, hK1]; exact valuation_algebraMap_under A1 Q c
    · show dL.v (Sum.inr Q) _ = dK.v (Sum.inr (Q.under A2)) c ^ (Q.under A2).asIdeal.ramificationIdx' Q.asIdeal
      rw [hL2, hK2]; exact valuation_algebraMap_under A2 Q c
  trace_le P n y hy := by
    rcases P with P | P
    · rw [hK1]
      refine val_trace_le (B := B1) P n fun Q hQ => ?_
      have hu := (liesOver_iff_under_eq A1 P Q).1 hQ
      have h1 := hy (Sum.inl Q) (by show Sum.inl (Q.under A1) = Sum.inl P; rw [hu])
      rw [hL1] at h1
      simp only [Sum.elim_inl, Finsupp.sumElim_inl] at h1
      rwa [hu, ordDiv_apply (differentIdeal_ne_bot' (L := L) A1 K B1)] at h1
    · rw [hK2]
      refine val_trace_le (B := B2) P n fun Q hQ => ?_
      have hu := (liesOver_iff_under_eq A2 P Q).1 hQ
      have h1 := hy (Sum.inr Q) (by show Sum.inr (Q.under A2) = Sum.inr P; rw [hu])
      rw [hL2] at h1
      simp only [Sum.elim_inr, Finsupp.sumElim_inr] at h1
      rwa [hu, ordDiv_apply (differentIdeal_ne_bot' (L := L) A2 K B2)] at h1
  trace_sharp Q0 n := by
    classical
    rcases Q0 with Q0 | Q0
    · obtain ⟨y, hy, hTr⟩ := exists_val_trace_eq (K := K) (L := L) (Q0.under A1) Q0 ⟨rfl⟩ n
      refine ⟨y, ?_, ?_⟩
      · rintro (Q | Q) hQ
        · have hu : Q.under A1 = Q0.under A1 := Sum.inl.inj hQ
          have h1 := hy Q ((liesOver_iff_under_eq A1 _ Q).2 hu)
          rw [hL1]
          simp only [Sum.elim_inl, Finsupp.sumElim_inl]
          rw [hu, ordDiv_apply (differentIdeal_ne_bot' (L := L) A1 K B1)]
          by_cases hQQ : Q = Q0
          · subst hQQ
            rw [ordI_mul_asIdeal_self Q (differentIdeal_ne_bot' (L := L) A1 K B1)] at h1
            rw [Finsupp.single_eq_same]
            convert h1 using 2
            push_cast; ring
          · rw [ordI_mul_asIdeal_of_ne (differentIdeal_ne_bot' (L := L) A1 K B1) (Ne.symm hQQ)] at h1
            rw [Finsupp.single_apply, if_neg (fun h => hQQ (Sum.inl.inj h).symm), add_zero]
            exact h1
        · simp at hQ
      · show dK.v (Sum.inl (Q0.under A1)) _ = _
        rw [hK1]; exact hTr
    · obtain ⟨y, hy, hTr⟩ := exists_val_trace_eq (K := K) (L := L) (Q0.under A2) Q0 ⟨rfl⟩ n
      refine ⟨y, ?_, ?_⟩
      · rintro (Q | Q) hQ
        · simp at hQ
        · have hu : Q.under A2 = Q0.under A2 := Sum.inr.inj hQ
          have h1 := hy Q ((liesOver_iff_under_eq A2 _ Q).2 hu)
          rw [hL2]
          simp only [Sum.elim_inr, Finsupp.sumElim_inr]
          rw [hu, ordDiv_apply (differentIdeal_ne_bot' (L := L) A2 K B2)]
          by_cases hQQ : Q = Q0
          · subst hQQ
            rw [ordI_mul_asIdeal_self Q (differentIdeal_ne_bot' (L := L) A2 K B2)] at h1
            rw [Finsupp.single_eq_same]
            convert h1 using 2
            push_cast; ring
          · rw [ordI_mul_asIdeal_of_ne (differentIdeal_ne_bot' (L := L) A2 K B2) (Ne.symm hQQ)] at h1
            rw [Finsupp.single_apply, if_neg (fun h => hQQ (Sum.inr.inj h).symm), add_zero]
            exact h1
      · show dK.v (Sum.inr (Q0.under A2)) _ = _
        rw [hK2]; exact hTr
  resid P n z w hz hw := by
    rcases P with P | P
    · rw [hK1] at hz hw ⊢
      obtain ⟨c, hc⟩ := exists_sub_mul_val_le P n hz hw
      exact ⟨algebraMap A1 K c, by rw [HeightOneSpectrum.valuation_of_algebraMap]; exact P.intValuation_le_one c, hc⟩
    · rw [hK2] at hz hw ⊢
      obtain ⟨c, hc⟩ := exists_sub_mul_val_le P n hz hw
      exact ⟨algebraMap A2 K c, by rw [HeightOneSpectrum.valuation_of_algebraMap]; exact P.intValuation_le_one c, hc⟩
  approx P α E := by
    rcases P with P | P
    · obtain ⟨y, hy⟩ := exists_approx (finite_under_eq A1 (B := B1) P).toFinset
        (fun Q => α (Sum.inl Q)) (fun Q => E (Sum.inl Q))
      refine ⟨y, ?_⟩
      rintro (Q | Q) hQ
      · have hu : Q.under A1 = P := Sum.inl.inj hQ
        rw [hL1]; exact hy Q ((Set.Finite.mem_toFinset _).2 hu)
      · simp at hQ
    · obtain ⟨y, hy⟩ := exists_approx (finite_under_eq A2 (B := B2) P).toFinset
        (fun Q => α (Sum.inr Q)) (fun Q => E (Sum.inr Q))
      refine ⟨y, ?_⟩
      rintro (Q | Q) hQ
      · simp at hQ
      · have hu : Q.under A2 = P := Sum.inr.inj hQ
        rw [hL2]; exact hy Q ((Set.Finite.mem_toFinset _).2 hu)

end Builder

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Cot2 =====
section

/-!
# S4-GOS-B, part Cot2: the cotrace Weil differential and abstract Riemann-Hurwitz (O2b)

For `c : Cotrace dK dL` and a Weil differential `η ∈ Ω_K(W)`:
* `omega`: `α ↦ η (T s)` for any semilocal `s ≡ α mod A_L(con W + d)` (F1; F2 makes it well defined);
* `omega_apply`: `ω α = η (T s)` whenever `α - s ∈ A_L(con W + d)`, `s ∈ S`;
* `omega_mem_Omega`: `ω ∈ Ω_L(con W + d)`;
* `eta_mem_of_omega_mem`: F4 + R turn `ω ∈ Ω_L(con W + d + Q0)` into `η ∈ Ω_K(W + pr Q0)`;
* **`isCanonical_con`**: `W` canonical for `K` ⟹ `con W + d` canonical for `L`.
-/

set_option autoImplicit false

noncomputable section

open WithZero RamanujanPetersson.RR

namespace RamanujanPetersson.GOS

variable {Fq K L ιK ιL : Type*} [Field Fq] [Field K] [Field L] [Algebra Fq K] [Algebra Fq L]
  [Algebra K L] [IsScalarTower Fq K L]

namespace Cotrace

variable {dK : Data Fq K ιK} {dL : Data Fq L ιL} (c : Cotrace dK dL)
variable {W : ιK →₀ ℤ} {η : Module.Dual Fq dK.adeles}

/-- The trace of a semilocal adele, as an adele of `K`. -/
def Tad {s : ιL → L} (hs : s ∈ c.S) : dK.adeles := ⟨c.Tfun s, c.Tfun_mem_adeles hs⟩

@[simp] theorem coe_Tad {s : ιL → L} (hs : s ∈ c.S) : (c.Tad hs : ιK → K) = c.Tfun s := rfl

theorem eta_Tad_eq (hη : η ∈ dK.Omega W) {s s' : ιL → L} (hs : s ∈ c.S) (hs' : s' ∈ c.S)
    (h : s - s' ∈ dL.AD (c.con W + c.d)) : η (c.Tad hs) = η (c.Tad hs') := by
  have hss : s - s' ∈ c.S := c.S.sub_mem hs hs'
  have h1 : c.Tad hs - c.Tad hs' = c.Tad hss := Subtype.ext (by simp [map_sub])
  have h2 : η (c.Tad hss) = 0 :=
    dK.mem_Omega.1 hη _ (Submodule.mem_sup_left (c.Tfun_mem_AD hss h))
  rw [← sub_eq_zero, ← map_sub, h1, h2]

omit [IsScalarTower Fq K L] in
theorem exists_sel (α : dL.adeles) (E : ιL →₀ ℤ) :
    ∃ s : ιL → L, s ∈ c.S ∧ (α : ιL → L) - s ∈ dL.AD E := by
  obtain ⟨s, hs, h⟩ := c.exists_S_sub_mem_AD α.2 E
  exact ⟨s, hs, h⟩

/-- A chosen semilocal adele congruent to `α` modulo `A_L(E)` (F1). -/
def sel (E : ιL →₀ ℤ) (α : dL.adeles) : ιL → L := (c.exists_sel α E).choose

omit [IsScalarTower Fq K L] in
theorem sel_mem (E : ιL →₀ ℤ) (α : dL.adeles) : c.sel E α ∈ c.S := (c.exists_sel α E).choose_spec.1

omit [IsScalarTower Fq K L] in
theorem sub_sel_mem (E : ιL →₀ ℤ) (α : dL.adeles) : (α : ιL → L) - c.sel E α ∈ dL.AD E :=
  (c.exists_sel α E).choose_spec.2

/-- `α ↦ η (T (sel α))`. -/
def omegaFun (η : Module.Dual Fq dK.adeles) (E : ιL →₀ ℤ) (α : dL.adeles) : Fq :=
  η (c.Tad (c.sel_mem E α))

theorem omegaFun_eq (hη : η ∈ dK.Omega W) {α : dL.adeles} {s : ιL → L} (hs : s ∈ c.S)
    (h : (α : ιL → L) - s ∈ dL.AD (c.con W + c.d)) : c.omegaFun η (c.con W + c.d) α = η (c.Tad hs) := by
  apply c.eta_Tad_eq hη
  have := (dL.AD (c.con W + c.d)).sub_mem h (c.sub_sel_mem (c.con W + c.d) α)
  rwa [sub_sub_sub_cancel_left] at this

/-- The Weil differential `η ∘ T` of `L` (well defined on `adeles_L` by F1 and F2). -/
def omega (hη : η ∈ dK.Omega W) : Module.Dual Fq dL.adeles where
  toFun := c.omegaFun η (c.con W + c.d)
  map_add' α β := by
    have hα := c.sel_mem (c.con W + c.d) α
    have hβ := c.sel_mem (c.con W + c.d) β
    have hs := c.S.add_mem hα hβ
    have h : ((α + β : dL.adeles) : ιL → L) - (c.sel (c.con W + c.d) α + c.sel (c.con W + c.d) β) ∈ dL.AD (c.con W + c.d) := by
      have := (dL.AD (c.con W + c.d)).add_mem (c.sub_sel_mem (c.con W + c.d) α) (c.sub_sel_mem (c.con W + c.d) β)
      rwa [← add_sub_add_comm] at this
    rw [c.omegaFun_eq hη hs h]
    have h2 : c.Tad hs = c.Tad hα + c.Tad hβ := Subtype.ext (by simp [map_add])
    rw [h2, map_add]
    rfl
  map_smul' r α := by
    have hα := c.sel_mem (c.con W + c.d) α
    have hs := c.S.smul_mem r hα
    have h : ((r • α : dL.adeles) : ιL → L) - r • c.sel (c.con W + c.d) α ∈ dL.AD (c.con W + c.d) := by
      have := (dL.AD (c.con W + c.d)).smul_mem r (c.sub_sel_mem (c.con W + c.d) α)
      rwa [smul_sub] at this
    rw [c.omegaFun_eq hη hs h]
    have h2 : c.Tad hs = r • c.Tad hα := Subtype.ext (by simp [map_smul])
    rw [h2, map_smul]
    rfl

theorem omega_apply (hη : η ∈ dK.Omega W) {α : dL.adeles} {s : ιL → L} (hs : s ∈ c.S)
    (h : (α : ιL → L) - s ∈ dL.AD (c.con W + c.d)) : c.omega hη α = η (c.Tad hs) :=
  c.omegaFun_eq hη hs h

theorem omega_mem_Omega (hη : η ∈ dK.Omega W) : c.omega hη ∈ dL.Omega (c.con W + c.d) := by
  rw [dL.mem_Omega]
  intro α hα
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hα
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.1 hb
  have hfS : dL.const f ∈ c.S := ⟨dL.Fs_le_adeles ⟨f, rfl⟩, fun _ => rfl⟩
  rw [c.omega_apply hη hfS (by rw [← hab, add_sub_cancel_right]; exact ha)]
  exact dK.mem_Omega.1 hη _ (Submodule.mem_sup_right ⟨c.tr f, funext fun _ => rfl⟩)

/-- If `ω = η ∘ T` vanishes on `A_L(con W + d + Q0)`, then `η` vanishes on `A_K(W + pr Q0)`. -/
theorem eta_mem_of_omega_mem (hη : η ∈ dK.Omega W) (Q0 : ιL)
    (hω : c.omega hη ∈ dL.Omega (c.con W + c.d + Finsupp.single Q0 1)) :
    η ∈ dK.Omega (W + Finsupp.single (c.pr Q0) 1) := by
  classical
  set P := c.pr Q0 with hP_def
  obtain ⟨y, hy, hTy⟩ := c.trace_sharp Q0 (W P)
  have key : ∀ c' : K, dK.v P c' ≤ 1 → ∀ hm : (Pi.single P (c' * c.tr y) : ιK → K) ∈ dK.adeles,
      η ⟨_, hm⟩ = 0 := by
    intro c' hc' hm
    set α : ιL → L := fun Q => if c.pr Q = P then algebraMap K L c' * y else 0 with hα_def
    have hαAD : α ∈ dL.AD (c.con W + c.d + Finsupp.single Q0 1) := by
      rw [dL.mem_AD]
      intro Q
      by_cases hQ : c.pr Q = P
      · simp only [hα_def, hQ, if_true, map_mul, c.v_algebraMap, Finsupp.add_apply, con_apply]
        calc dK.v P c' ^ c.e Q * dL.v Q y ≤ 1 * dL.v Q y := by gcongr; exact pow_le_one' hc' _
          _ ≤ _ := by rw [one_mul]; exact hy Q hQ
      · simp only [hα_def, hQ, if_false, map_zero]; exact zero_le
    have hαS : α ∈ c.S := ⟨dL.AD_le_adeles _ hαAD, fun Q => by simp only [hα_def, c.pr_sec]⟩
    have h0 : c.omega hη ⟨α, hαS.1⟩ = 0 := dL.mem_Omega.1 hω _ (Submodule.mem_sup_left hαAD)
    rw [c.omega_apply hη hαS (by simp)] at h0
    rw [← h0]
    congr 1
    apply Subtype.ext
    funext P'
    simp only [coe_Tad, Tfun_apply, hα_def, c.pr_sec]
    by_cases hP' : P' = P
    · subst hP'
      simp only [Pi.single_eq_same, if_true]
      rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
    · simp only [hP', if_false, Pi.single_apply, map_zero]
  rw [dK.mem_Omega]
  intro β hβ
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hβ
  have hz : dK.v P (a P) ≤ exp (W P + 1) := by
    have := dK.mem_AD.1 ha P
    simpa [Finsupp.add_apply] using this
  obtain ⟨c', hc', hcz⟩ := c.resid P (W P) (a P) (c.tr y) hz hTy
  have hm1 : (Pi.single P (c' * c.tr y) : ιK → K) ∈ dK.adeles := by
    rw [dK.mem_adeles]
    apply (Set.finite_singleton P).subset
    intro i hi
    by_contra h
    rw [Set.mem_singleton_iff] at h
    simp [Pi.single_apply, h] at hi
  have hβ' : β = ⟨_, hm1⟩ + (β - ⟨_, hm1⟩) := (add_sub_cancel _ _).symm
  rw [hβ', map_add, key c' hc' hm1, zero_add]
  apply dK.mem_Omega.1 hη
  show (β : ιK → K) - Pi.single P (c' * c.tr y) ∈ _
  rw [← hab]
  have hsplit : a + b - Pi.single P (c' * c.tr y) = (a - Pi.single P (c' * c.tr y)) + b := by abel
  rw [hsplit]
  apply Submodule.add_mem_sup _ hb
  rw [dK.mem_AD]
  intro P'
  by_cases hP' : P' = P
  · subst hP'
    simpa using hcz
  · have := dK.mem_AD.1 ha P'
    simpa [Pi.single_apply, hP', Finsupp.single_apply, Ne.symm hP'] using this

/-- **Riemann-Hurwitz, abstract form.** `con W + d` is canonical for `L` if `W` is canonical for `K`. -/
theorem isCanonical_con (hW : dK.IsCanonical W) : dL.IsCanonical (c.con W + c.d) := by
  classical
  obtain ⟨η, hη0, hηW⟩ := hW
  have hη : η ∈ dK.Omega W := (hηW W).2 le_rfl
  have hmax : ∀ D, c.omega hη ∈ dL.Omega D ↔ D ≤ c.con W + c.d := by
    intro D
    refine ⟨fun hD => ?_, fun hD => dL.Omega_anti hD (c.omega_mem_Omega hη)⟩
    by_contra hle
    obtain ⟨Q0, hQ0⟩ : ∃ Q0, (c.con W + c.d) Q0 < D Q0 := by
      by_contra h
      push Not at h
      exact hle h
    have h1 : c.con W + c.d + Finsupp.single Q0 1 ≤ D ⊔ (c.con W + c.d) := by
      intro Q
      rw [Finsupp.add_apply, Finsupp.sup_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; exact le_sup_of_le_left (by omega)
      · rw [add_zero]; exact le_sup_right
    have h2 : c.omega hη ∈ dL.Omega (D ⊔ (c.con W + c.d)) := by
      rw [dL.Omega_sup]; exact ⟨hD, c.omega_mem_Omega hη⟩
    have h4 := (hηW _).1 (c.eta_mem_of_omega_mem hη Q0 (dL.Omega_anti h1 h2)) (c.pr Q0)
    simp at h4
  refine ⟨c.omega hη, fun h0 => ?_, hmax⟩
  have hne : Nonempty ιK := by
    by_contra h
    rw [not_nonempty_iff] at h
    apply hη0
    ext α
    have : α = 0 := Subtype.ext (funext fun i => isEmptyElim i)
    simp [this]
  obtain ⟨P0⟩ := hne
  have h5 := (hmax (c.con W + c.d + Finsupp.single (c.sec P0) 1)).1 (by rw [h0]; exact Submodule.zero_mem _)
    (c.sec P0)
  simp at h5

end Cotrace

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Cot3 =====
section

/-!
# S4-GOS-B, part Cot3: degree of the conorm and the abstract Riemann-Hurwitz formula

* `degD_con`: if `Σ_{Q | P} e_Q deg Q = n deg P` for every `P`, then `deg (con D) = n deg D`;
* **`riemannHurwitz_data`**: `2 g_L - 2 ℓ_L(0) = n (2 g_K - 2 ℓ_K(0)) + deg d`.
-/

set_option autoImplicit false

noncomputable section

open WithZero RamanujanPetersson.RR

namespace RamanujanPetersson.GOS

variable {Fq K L ιK ιL : Type*} [Field Fq] [Field K] [Field L] [Algebra Fq K] [Algebra Fq L]
  [Algebra K L]

namespace Cotrace

variable {dK : Data Fq K ιK} {dL : Data Fq L ιL} (c : Cotrace dK dL)

theorem con_zero : c.con 0 = 0 := by
  ext Q; simp [con_apply]

theorem con_add (D E : ιK →₀ ℤ) : c.con (D + E) = c.con D + c.con E := by
  ext Q; simp [con_apply, mul_add]

theorem con_single (P : ιK) (m : ℤ) :
    c.con (Finsupp.single P m) =
      ∑ Q ∈ (c.fib_finite P).toFinset, Finsupp.single Q ((c.e Q : ℤ) * m) := by
  classical
  ext Q'
  rw [con_apply, Finsupp.finsetSum_apply]
  by_cases h : c.pr Q' = P
  · rw [Finset.sum_eq_single Q']
    · rw [h, Finsupp.single_eq_same, Finsupp.single_eq_same]
    · intro Q _ hQ; rw [Finsupp.single_apply, if_neg hQ]
    · intro hQ'; exact absurd (by simpa using h) hQ'
  · rw [Finsupp.single_apply, if_neg (Ne.symm h), mul_zero, Finset.sum_eq_zero]
    intro Q hQ
    have hQ : c.pr Q = P := by simpa using hQ
    rw [Finsupp.single_apply, if_neg]
    rintro rfl; exact h hQ

theorem degD_finset_sum {ι' : Type*} (d : Data Fq L ιL) (s : Finset ι') (f : ι' → ιL →₀ ℤ) :
    d.degD (∑ i ∈ s, f i) = ∑ i ∈ s, d.degD (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, d.degD_add, ih]

/-- `deg (con D) = n deg D` when `Σ_{Q | P} e_Q deg Q = n deg P` for every `P`. -/
theorem degD_con {n : ℤ}
    (hdeg : ∀ P, ∑ Q ∈ (c.fib_finite P).toFinset, (c.e Q : ℤ) * dL.deg Q = n * dK.deg P)
    (D : ιK →₀ ℤ) : dL.degD (c.con D) = n * dK.degD D := by
  induction D using Finsupp.induction_linear with
  | zero => rw [con_zero, dL.degD_zero, dK.degD_zero, mul_zero]
  | add D E hD hE => rw [con_add, dL.degD_add, dK.degD_add, hD, hE, mul_add]
  | single P m =>
    rw [con_single, degD_finset_sum, dK.degD_single]
    simp only [dL.degD_single]
    calc ∑ Q ∈ (c.fib_finite P).toFinset, (c.e Q : ℤ) * m * dL.deg Q
        = m * ∑ Q ∈ (c.fib_finite P).toFinset, (c.e Q : ℤ) * dL.deg Q := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun Q _ => by ring
      _ = n * (m * dK.deg P) := by rw [hdeg]; ring

variable [IsScalarTower Fq K L] [Fintype Fq]

/-- **Riemann-Hurwitz, abstract form.** -/
theorem riemannHurwitz_data (hK : dK.Axioms) (hL : dL.Axioms) {n : ℤ}
    (hdeg : ∀ P, ∑ Q ∈ (c.fib_finite P).toFinset, (c.e Q : ℤ) * dL.deg Q = n * dK.deg P) :
    2 * (dL.genus : ℤ) - 2 * dL.ell 0 = n * (2 * (dK.genus : ℤ) - 2 * dK.ell 0) + dL.degD c.d := by
  obtain ⟨W, hW⟩ := dK.exists_isCanonical hK
  have h1 := dL.degD_canonical hL (c.isCanonical_con hW)
  rw [dL.degD_add, c.degD_con hdeg, dK.degD_canonical hK hW] at h1
  rw [← h1]

end Cotrace

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Deg =====
section

/-!
# S4-GOS-B, part Deg: the fundamental identity in degree form

For `A → B` as in `Def_RP_GOS_B_Loc` with compatible `Fq`-algebra structures and `P : HOS A`:
`Σ_{Q | P} e_Q deg Q = [L : K] deg P` (`deg` = `Places.deg Fq`, `e_Q = ramificationIdx'`).
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero

namespace RamanujanPetersson.GOS

section Deg

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (A : Type*) {K L : Type*} {B : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable [Module.Finite A B] [Algebra.IsIntegral A B]
variable [Algebra Fq A] [Algebra Fq B] [IsScalarTower Fq A B]

omit [Fintype Fq] [Module.IsTorsionFree A B] [Module.Finite A B] in
theorem deg_eq_mul_inertiaDeg (P : HeightOneSpectrum A) (Q : HeightOneSpectrum B) (hQ : Q.under A = P) :
    Places.deg Fq Q = Places.deg Fq P * Ideal.inertiaDeg' P.asIdeal Q.asIdeal := by
  have := P.isMaximal
  have := Q.isMaximal
  have hl : Q.asIdeal.LiesOver P.asIdeal := (liesOver_iff_under_eq A P Q).2 hQ
  rw [Ideal.inertiaDeg'_algebraMap]
  have : IsScalarTower Fq (A ⧸ P.asIdeal) (B ⧸ Q.asIdeal) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, IsScalarTower.algebraMap_apply Fq A B]
      rfl
  let : Field (A ⧸ P.asIdeal) := Ideal.Quotient.field _
  have : Module.Free (A ⧸ P.asIdeal) (B ⧸ Q.asIdeal) := Module.Free.of_divisionRing _ _
  exact (Module.finrank_mul_finrank Fq (A ⧸ P.asIdeal) (B ⧸ Q.asIdeal)).symm

end Deg

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_CupDuality_Cover =====
section

/-!
# Curve duality (unit S4-CurveDuality), finite covers of function fields: contraction of places

For a finite extension `Y / F` of function fields over `K` (both carrying the `K[X] ⊆ RatFunc K` package, with
`F → Y` compatible):
* generic Dedekind pairs: `eUnder A w` (ramification index of `w` over `w.under A`), `valuation_under`, `ord_under`;
* the ring maps `Rfin K F → Rfin K Y`, `Rinf K F → Rinf K Y` (integral, torsion free);
* `contr : Place K Y → Place K F`, `eQ F Q`, **`placeVal_contr`** (`v_Q` on `F` is `v_(contr Q) ^ eQ`), `ord_contr`,
  `evU_contr`;
* `placeVal_eq_of_ord`, `eq_of_ord_mul` (two places with `e' ord' = e ord` coincide) and **`contr_placeEquiv`**
  (contraction is invariant under `F`-automorphisms of `Y`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain
open scoped WithZero

namespace RamanujanPetersson.CupDuality

open RamanujanPetersson.Places (Place Divisor Rfin Rinf Oinf)

section Generic

variable {A B F Y : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B] [Field F] [Field Y] [Algebra F Y] [Algebra A F] [IsFractionRing A F] [Algebra A Y]
  [IsScalarTower A F Y] [Algebra B Y] [IsFractionRing B Y] [IsScalarTower A B Y] [Algebra.IsIntegral A B]

end Generic

section Package

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]
variable {Y : Type*} [Field Y] [Algebra K Y] [Algebra K[X] Y] [Algebra (RatFunc K) Y]
  [IsScalarTower K[X] (RatFunc K) Y] [IsScalarTower K K[X] Y] [FunctionField K Y]
  [Algebra.IsSeparable (RatFunc K) Y]
variable [Algebra F Y] [IsScalarTower K F Y] [IsScalarTower K[X] F Y] [IsScalarTower (RatFunc K) F Y]

instance isScalarTower_Oinf_cover : IsScalarTower (Oinf K) F Y :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply (Oinf K) (RatFunc K) F, IsScalarTower.algebraMap_apply (Oinf K) (RatFunc K) Y,
      ← IsScalarTower.algebraMap_apply (RatFunc K) F Y]

/-- The ring map `Rfin K F → Rfin K Y`. -/
noncomputable instance algRfin : Algebra (Rfin K F) (Rfin K Y) :=
  ((IsScalarTower.toAlgHom K[X] F Y).mapIntegralClosure).toRingHom.toAlgebra

/-- The ring map `Rinf K F → Rinf K Y`. -/
noncomputable instance algRinf : Algebra (Rinf K F) (Rinf K Y) :=
  ((IsScalarTower.toAlgHom (Oinf K) F Y).mapIntegralClosure).toRingHom.toAlgebra

theorem algebraMap_rfin (a : Rfin K F) :
    ((algebraMap (Rfin K F) (Rfin K Y) a : Rfin K Y) : Y) = algebraMap F Y a := rfl

theorem algebraMap_rinf (a : Rinf K F) :
    ((algebraMap (Rinf K F) (Rinf K Y) a : Rinf K Y) : Y) = algebraMap F Y a := rfl

instance isScalarTower_rfin_mid : IsScalarTower (Rfin K F) F Y := IsScalarTower.of_algebraMap_eq fun _ => rfl

instance isScalarTower_rinf_mid : IsScalarTower (Rinf K F) F Y := IsScalarTower.of_algebraMap_eq fun _ => rfl

instance isScalarTower_rfin_top : IsScalarTower (Rfin K F) (Rfin K Y) Y :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance isScalarTower_rinf_top : IsScalarTower (Rinf K F) (Rinf K Y) Y :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance isScalarTower_rfin_bot : IsScalarTower K[X] (Rfin K F) (Rfin K Y) :=
  IsScalarTower.of_algebraMap_eq fun p => Subtype.ext (IsScalarTower.algebraMap_apply K[X] F Y p)

instance isScalarTower_rinf_bot : IsScalarTower (Oinf K) (Rinf K F) (Rinf K Y) :=
  IsScalarTower.of_algebraMap_eq fun p => Subtype.ext (IsScalarTower.algebraMap_apply (Oinf K) F Y p)

instance isIntegral_rfin : Algebra.IsIntegral (Rfin K F) (Rfin K Y) :=
  ⟨fun b => by
    have hb : IsIntegral K[X] b := integralClosure.isIntegral (R := K[X]) (A := Y) b
    exact hb.tower_top⟩

instance isIntegral_rinf : Algebra.IsIntegral (Rinf K F) (Rinf K Y) :=
  ⟨fun b => by
    have hb : IsIntegral (Oinf K) b := integralClosure.isIntegral (R := Oinf K) (A := Y) b
    exact hb.tower_top⟩

instance isTorsionFree_rfin : Module.IsTorsionFree (Rfin K F) (Rfin K Y) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr fun _ _ h =>
    Subtype.ext ((algebraMap F Y).injective (congrArg Subtype.val h))

instance isTorsionFree_rinf : Module.IsTorsionFree (Rinf K F) (Rinf K Y) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr fun _ _ h =>
    Subtype.ext ((algebraMap F Y).injective (congrArg Subtype.val h))

end Package

end RamanujanPetersson.CupDuality


end

-- ===== S4.Def_RP_Swan_GlobC =====
section

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

end InfChart

section SwanInf

variable {A : Type} [CommRing A] [IsDomain A]
variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] [Algebra A (RatFunc Fq)]
  [IsFractionRing A (RatFunc Fq)]
variable (L : Type) [Field L] [Algebra (RatFunc Fq) L] [Algebra A L] [IsScalarTower A (RatFunc Fq) L]

variable [FiniteDimensional (RatFunc Fq) L] [Algebra.IsSeparable (RatFunc Fq) L] [Fintype Fq]

end SwanInf

end GalCover

end RamanujanPetersson

end

end

-- ===== S4.Def_RP_GOS_B_Shf =====
section

/-!
# S4-GOS-B, part Shf: integer linear recurrences through the shift operator (O6d, algebra)

* `shiftE R`: the shift `s ↦ (k ↦ s (k + 1))` on `ℕ → R`; `aeval_shiftE_apply`:
  `aeval (shiftE R) P s k = Σ_{j ≤ deg P} P_j s (k + j)`.
* closure: `aeval_add_of`, `aeval_sub_of`, `aeval_prod_sum` (a product annihilates a sum);
  annihilators: `aeval_X_sub_C_geom` (`c^k`), `aeval_X_pow_sub_one` (`n`-periodic), `aeval_prod_powsum`
  (power sums of a multiset); `aeval_int_of_complex` (descent from `ℂ` to `ℤ`).
* `dil d a m = [d ∣ m] d a(m/d)`; `aeval_expand_dil_eq_zero`: `P(X)` kills `a` ⟹ `P(X^d)` kills `dil d a`.
* **`exists_rec_weil`**: for `a k = 1 + Q^k - Σ_{α ∈ c} α^k` with `Π α = Q^g` and `Π (X - α) ∈ ℤ[X]`, the sequence
  `dil d a - Σ_i [n_i ∣ m] n_i` satisfies an integer recurrence with leading coefficient `± Q^(g+1)`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

section Shift

variable (R : Type) [CommRing R]

variable {R}

end Shift

section Dil

variable {R : Type} [CommRing R]

theorem aeval_expand_dil {d : ℕ} (hd : 0 < d) (P : R[X]) (a : ℕ → R) :
    aeval (shiftE R) (expand R d P) (dil d a) = dil d (aeval (shiftE R) P a) := by
  rw [expand_aeval]
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq, dil_add]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, pow_shiftE_pow_dil hd, dil_smul]

theorem aeval_expand_dil_eq_zero {d : ℕ} (hd : 0 < d) {P : R[X]} {a : ℕ → R} (h : aeval (shiftE R) P a = 0) :
    aeval (shiftE R) (expand R d P) (dil d a) = 0 := by
  rw [aeval_expand_dil hd, h, dil_zero]

end Dil

/-- **Weil recurrence.** `a k = 1 + Q^k - Σ_{α ∈ c} α^k` (all `k`), `Π α = Q^g`, `Π (X - α) = P0` over `ℤ`: the
sequence `dil d a - Σ_i [n_i ∣ m] n_i` satisfies an integer recurrence whose coefficient `P_0 = ± Q^(g+1)`. -/
theorem exists_rec_weil {d : ℕ} (hd : 0 < d) (Q g : ℕ) (c : Multiset ℂ) (hprod : c.prod = (Q : ℂ) ^ g)
    (P0 : ℤ[X]) (hP0 : P0.map (Int.castRingHom ℂ) = (c.map fun r => X - C r).prod) (a : ℕ → ℤ)
    (ha : ∀ k, (a k : ℂ) = 1 + (Q : ℂ) ^ k - (c.map (· ^ k)).sum) {ι : Type} [Fintype ι] (n : ι → ℕ)
    (hn : ∀ i, 0 < n i) :
    ∃ P : ℤ[X], (∃ σ : ℤ, σ ^ 2 = 1 ∧ P.coeff 0 = σ * (Q : ℤ) ^ (g + 1)) ∧
      aeval (shiftE ℤ) P (dil d a - ∑ i, fun m => if n i ∣ m then (n i : ℤ) else 0) = 0 := by
  refine ⟨expand ℤ d ((X - C 1) * (X - C (Q : ℤ)) * P0) * ∏ i, (X ^ n i - 1),
    ⟨(-1) ^ (Multiset.card c + Fintype.card ι), by rw [← pow_mul, mul_comm, pow_mul]; simp, ?_⟩, ?_⟩
  · have h0 : ((P0.eval 0 : ℤ) : ℂ) = (-1) ^ Multiset.card c * (Q : ℂ) ^ g := by
      have h1 := congrArg (eval (0 : ℂ)) hP0
      rw [eval_zero_map, eval_multiset_prod, Multiset.map_map] at h1
      simp only [Function.comp_def, eval_sub, eval_X, eval_C, zero_sub] at h1
      rw [Multiset.prod_map_neg, hprod] at h1
      simpa using h1
    have h0' : P0.eval 0 = (-1) ^ Multiset.card c * (Q : ℤ) ^ g := by exact_mod_cast h0
    have hprodn : ∏ i, ((X : ℤ[X]) ^ n i - 1).coeff 0 = (-1) ^ Fintype.card ι := by
      rw [Finset.prod_congr rfl fun i _ => (show ((X : ℤ[X]) ^ n i - 1).coeff 0 = -1 by
        rw [coeff_sub, coeff_X_pow, if_neg (hn i).ne, coeff_one_zero, zero_sub]), Finset.prod_const,
        Finset.card_univ]
    rw [mul_coeff_zero, coeff_zero_prod, hprodn, coeff_zero_eq_eval_zero, expand_eval,
      zero_pow hd.ne', eval_mul, eval_mul, h0']
    simp only [eval_sub, eval_X, eval_C, zero_sub]
    ring
  · have hA : aeval (shiftE ℤ) ((X - C 1) * (X - C (Q : ℤ)) * P0) a = 0 := by
      apply aeval_int_of_complex
      have hs : (fun k => (a k : ℂ)) = ((fun k => (1 : ℂ) ^ k) + fun k => (Q : ℂ) ^ k) -
          fun k => (c.map (· ^ k)).sum := by
        funext k
        simp [ha k]
      have hpol : ((X - C 1) * (X - C (Q : ℤ)) * P0).map (Int.castRingHom ℂ) =
          (X - C 1) * (X - C (Q : ℂ)) * (c.map fun r => X - C r).prod := by
        rw [Polynomial.map_mul, Polynomial.map_mul, hP0, Polynomial.map_sub, Polynomial.map_sub,
          Polynomial.map_X, Polynomial.map_C, Polynomial.map_C, eq_intCast, eq_intCast, Int.cast_one,
          Int.cast_natCast]
      rw [hpol, hs]
      exact aeval_sub_of _ _ (aeval_add_of _ _ (aeval_X_sub_C_geom 1) (aeval_X_sub_C_geom _))
        (aeval_prod_powsum c)
    have hB : aeval (shiftE ℤ) (∏ i ∈ Finset.univ, (X ^ n i - 1 : ℤ[X]))
        (∑ i ∈ Finset.univ, fun m => if n i ∣ m then (n i : ℤ) else 0) = 0 :=
      aeval_prod_sum Finset.univ (fun i => (X ^ n i - 1 : ℤ[X]))
        (fun i m => if n i ∣ m then (n i : ℤ) else 0) fun i _ => aeval_X_pow_sub_one fun k => by
          show (if n i ∣ k + n i then (n i : ℤ) else 0) = if n i ∣ k then (n i : ℤ) else 0
          simp only [Nat.dvd_add_self_right]
    exact aeval_sub_of _ _ (aeval_expand_dil_eq_zero hd hA) hB

/-- The recurrence in the `Fin` form used by `sum_chiPC_eq_of_rec`, with `b_0` prime to every `l ∤ Q`. -/
theorem exists_rec_weil_fin {d : ℕ} (hd : 0 < d) (Q g : ℕ) (c : Multiset ℂ) (hprod : c.prod = (Q : ℂ) ^ g)
    (P0 : ℤ[X]) (hP0 : P0.map (Int.castRingHom ℂ) = (c.map fun r => X - C r).prod) (a : ℕ → ℤ)
    (ha : ∀ k, (a k : ℂ) = 1 + (Q : ℂ) ^ k - (c.map (· ^ k)).sum) {ι : Type} [Fintype ι] (n : ι → ℕ)
    (hn : ∀ i, 0 < n i) (ê : ℕ → ℤ) (hê : ∀ m, ê m = dil d a m - ∑ i, if n i ∣ m then (n i : ℤ) else 0) :
    ∃ D : ℕ, ∃ b : Fin (D + 1) → ℤ, (∀ k, ∑ j, b j * ê (k + j) = 0) ∧
      ∀ l : ℕ, l.Prime → ¬ l ∣ Q → ¬ (l : ℤ) ∣ b 0 := by
  obtain ⟨P, ⟨σ, hσ, h0⟩, hP⟩ := exists_rec_weil hd Q g c hprod P0 hP0 a ha n hn
  have hê' : ê = dil d a - ∑ i, fun m => if n i ∣ m then (n i : ℤ) else 0 := by
    funext m
    rw [hê m, Pi.sub_apply, Finset.sum_apply]
  refine ⟨P.natDegree, fun j => P.coeff j, fun k => ?_, fun l hl hlQ hdvd => ?_⟩
  · have hk := congr_fun hP k
    rw [aeval_shiftE_apply, ← hê', Pi.zero_apply] at hk
    rw [← hk]
    exact Fin.sum_univ_eq_sum_range (fun j => P.coeff j * ê (k + j)) (P.natDegree + 1)
  · have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
    have h1 : (l : ℤ) ∣ σ * (Q : ℤ) ^ (g + 1) := by rw [← h0]; exact hdvd
    have h2 : (l : ℤ) ∣ (Q : ℤ) ^ (g + 1) := by
      have := dvd_mul_of_dvd_right h1 σ
      rwa [← mul_assoc, ← sq, hσ, one_mul] at this
    exact hlQ (Int.natCast_dvd_natCast.mp (hlp.dvd_of_dvd_pow h2))

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_Lvl =====
section

/-!
# S4-GOS-B, part Lvl: `𝔽_{q^m}`-points as Frobenius-fixed points (O6c, generic)

For an algebraically closed `𝔽_q`-algebra `Ω` and `m > 0`:
* `exists_prim_level_alg`: a primitive `(q^m - 1)`-th root of unity in `Ω`;
* `finrank_levelField_alg`, `finite_levelField_alg`: `[𝔽_{q^m} : 𝔽_q] = m` for `levelField 𝔽_q Ω m`;
* **`card_fixed_eq_card_algHom`**: `#{v : C → Ω | v|_{𝔽_q} = alg, v^{q^m} = v} = #Hom_{𝔽_q}(C, levelField 𝔽_q Ω m)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.GOS

noncomputable section

open CP4a

section Lvl

variable {Fq : Type} [Field Fq] [Fintype Fq] {Ω : Type} [Field Ω] [Algebra Fq Ω]

theorem exists_prim_level_alg [IsAlgClosed Ω] {m : ℕ} (hm : 0 < m) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ (Fintype.card Fq ^ m - 1) := by
  have hq1 : 1 ≤ Fintype.card Fq ^ m := Nat.one_le_pow _ _ Fintype.card_pos
  have hq0 : (Fintype.card Fq : Ω) = 0 := by
    rw [← map_natCast (algebraMap Fq Ω), FiniteField.cast_card_eq_zero, map_zero]
  have hne : NeZero (((Fintype.card Fq ^ m - 1 : ℕ) : Ω)) := by
    refine ⟨?_⟩
    rw [Nat.cast_sub hq1, Nat.cast_pow, hq0, zero_pow hm.ne', Nat.cast_one, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω (Fintype.card Fq ^ m - 1)

end Lvl

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_Pos =====
section

/-!
# S4-GOS-B, part Pos: subgroup sums of the character from an integer recurrence of the counts (O6a)

* `neg_sum_ite_pos`: `-Σ_{j>0} B_j (c E_j) = B_0 (c E_0)` when `Σ_j B_j E_j = 0`.
* `isUnit_intCast_of_not_dvd`: `l ∤ b ⇒ b` is a unit in `ℤ/l^n`.
* **`sum_chiPC_eq_of_rec`**: for a subgroup `H' ≤ Gf`, if `Σ_{h ∈ H'} ptSeq h m = |H'| ê m` for `m > 0` and an integer
  recurrence `Σ_j b_j ê (k + j) = 0` (all `k`) has `l ∤ b_0`, then `Σ_{h ∈ H'} chi^{l,n}(h) = |H'| ê 0` in `ℤ/l^n`
  (periodicity + `mul_zero_eq_of_periodic` at index `0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CP4a Representation Lefschetz

theorem neg_sum_ite_pos {R : Type*} [CommRing R] {D : ℕ} (B E : Fin (D + 1) → R) (c : R)
    (h : ∑ j, B j * E j = 0) :
    -∑ j : Fin (D + 1), (if (0 : Fin (D + 1)) < j then B j * (c * E j) else 0) = B 0 * (c * E 0) := by
  rw [Fin.sum_univ_succ] at h ⊢
  have hs : ∑ i : Fin D, (if (0 : Fin (D + 1)) < i.succ then B i.succ * (c * E i.succ) else 0) =
      c * ∑ i : Fin D, B i.succ * E i.succ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [if_pos (Fin.succ_pos i)]; ring
  rw [hs, if_neg (lt_irrefl _)]
  linear_combination (-c) * h

theorem isUnit_intCast_of_not_dvd {l : ℕ} (hl : l.Prime) (n : ℕ) {b : ℤ} (hb : ¬ (l : ℤ) ∣ b) :
    IsUnit (b : ZMod (l ^ n)) := by
  have hc : IsCoprime b (l : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime b.natAbs l := (Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hl).2
      (fun hd => hb (Int.natCast_dvd.2 hd)))
    exact this
  obtain ⟨u, v, huv⟩ := hc.pow_right (n := n)
  refine isUnit_iff_exists_inv.2 ⟨(u : ZMod (l ^ n)), ?_⟩
  have h1 := congrArg (Int.cast : ℤ → ZMod (l ^ n)) huv
  push_cast at h1
  rw [show ((l : ZMod (l ^ n)) ^ n) = ((l ^ n : ℕ) : ZMod (l ^ n)) by push_cast; rfl, ZMod.natCast_self,
    mul_zero, add_zero] at h1
  rw [mul_comm]
  exact h1

section Pos

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {Mf : IntermediateField K (AlgebraicClosure K)} {Gf : Type} [Group Gf] [Fintype Gf]

end Pos

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_C_B1a =====
section

/-!
# S4-GOS-C, part B1a: idempotents of `End(Y)[C]` and traces on projective modules (abelian `C`)

For a finite commutative group `C`, a free finite `Λ`-module `Y` with a `C`-representation `ρ` and a Higman element `E`
(`∑ c, ρ c ∘ E ∘ ρ c⁻¹ = id`):
* `tauC c x = Tr(x_c)` is a trace functional on `R = End(Y)[C]` (`tauC_mul_comm`, `tauC_conj`);
* `eRep ρ E = ∑ c, single c (E * ρ c⁻¹)` is idempotent (`eRep_idem`) and `Tr(ρ g) = |C| τ_{g⁻¹}(eRep)`
  (`trace_eq_card_tauC`);
* idempotents congruent modulo a central nilpotent are conjugate (`exists_unit_conj_of_idem`), and
  `single b 1 - 1` is nilpotent when `b` has `l`-power order and `l ^ N = 0` in `Λ` (`isNilpotent_z`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open MonoidAlgebra

section Ring

/-- Idempotents congruent modulo a central nilpotent element are conjugate. -/
theorem exists_unit_conj_of_idem {R : Type*} [Ring R] {e ε z w : R} (he : IsIdempotentElem e)
    (hε : IsIdempotentElem ε) (hz : IsNilpotent z) (hzc : ∀ r : R, Commute z r) (hk : e - ε = w * z) :
    ∃ u : Rˣ, (u : R) * ε = e * (u : R) := by
  set u0 : R := e * ε + (1 - e) * (1 - ε) with hu0
  have hu1 : u0 = 1 + (w * (ε + ε - 1)) * z := by
    have h1 : u0 = 1 + (e - ε) * (ε + ε - 1) := by
      have key : e * ε + (1 - e) * (1 - ε) =
          1 + (e - ε) * (ε + ε - 1) + (ε * ε - ε) + (ε * ε - ε) := by noncomm_ring
      rw [hu0, key, hε.eq, sub_self, add_zero, add_zero]
    rw [h1, hk, mul_assoc w z, (hzc (ε + ε - 1)).eq, ← mul_assoc w]
  have hnil : IsNilpotent ((w * (ε + ε - 1)) * z) := by
    obtain ⟨n, hn⟩ := hz
    refine ⟨n, ?_⟩
    rw [(hzc (w * (ε + ε - 1))).symm.mul_pow, hn, mul_zero]
  have hunit : IsUnit u0 := by rw [hu1]; exact hnil.isUnit_one_add
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, hu0]
  have h1 : ε * ε = ε := hε
  have h2 : e * e = e := he
  calc (e * ε + (1 - e) * (1 - ε)) * ε = e * (ε * ε) + (1 - e) * (ε - ε * ε) := by noncomm_ring
    _ = e * ε := by rw [h1, sub_self, mul_zero, add_zero]
    _ = e * e * ε + (e - e * e) * (1 - ε) := by rw [h2, sub_self, zero_mul, add_zero]
    _ = e * (e * ε + (1 - e) * (1 - ε)) := by noncomm_ring

theorem isNilpotent_sub_one_of_pow {R : Type*} [Ring R] {l a N : ℕ} (hl : l.Prime)
    (hN : ((l ^ N : ℕ) : R) = 0) {s : R} (hs : s ^ (l ^ a) = 1) : IsNilpotent (s - 1) := by
  have hcomm : Commute s (-1) := Commute.neg_one_right s
  obtain ⟨r, hr⟩ := hcomm.exists_add_pow_prime_pow_eq hl a
  have hw : ∃ w : R, (s - 1) ^ (l ^ a) = (l : R) * w := by
    rw [sub_eq_add_neg, hr, hs]
    rcases Nat.even_or_odd (l ^ a) with h | h
    · rw [h.neg_one_pow]
      have h3 : l = 2 := hl.even_iff.mp (Nat.even_pow.mp h).1
      refine ⟨1 + s * (-1) * r, ?_⟩
      rw [mul_add, mul_one, h3, Nat.cast_ofNat, one_add_one_eq_two]
      simp only [mul_assoc]
    · rw [h.neg_one_pow, add_neg_cancel, zero_add]
      exact ⟨s * (-1) * r, by simp only [mul_assoc]⟩
  obtain ⟨w, hw⟩ := hw
  refine ⟨l ^ a * N, ?_⟩
  rw [pow_mul, hw, (Nat.cast_commute l w).mul_pow, ← Nat.cast_pow, hN, zero_mul]

end Ring

section Alg

variable {Λ : Type*} [CommRing Λ] {Y : Type*} [AddCommGroup Y] [Module Λ Y] [Module.Free Λ Y]
  [Module.Finite Λ Y] {C : Type*} [Group C] [Fintype C]

/-- The trace functional `τ_c(x) = Tr(x_c)` on `End(Y)[C]`. -/
def tauC (c : C) (x : MonoidAlgebra (Module.End Λ Y) C) : Λ := LinearMap.trace Λ Y (x.coeff c)

theorem coeff_mul_fintype (x y : MonoidAlgebra (Module.End Λ Y) C) (c : C) :
    (x * y).coeff c = ∑ h : C, x.coeff h * y.coeff (h⁻¹ * c) := by
  rw [coeff_mul_apply_left, Finsupp.sum_fintype]
  intro h
  simp

theorem tauC_mul_comm (hC : ∀ a b : C, a * b = b * a) (c : C) (x y : MonoidAlgebra (Module.End Λ Y) C) :
    tauC c (x * y) = tauC c (y * x) := by
  unfold tauC
  rw [coeff_mul_fintype, coeff_mul_fintype, map_sum, map_sum]
  refine Fintype.sum_equiv (Equiv.mk (fun h => h⁻¹ * c) (fun h => c * h⁻¹) (fun h => by group)
    (fun h => by group)) _ _ (fun h => ?_)
  simp only [Equiv.coe_fn_mk]
  have hk : (h⁻¹ * c)⁻¹ * c = h := by rw [hC h⁻¹ c]; group
  rw [hk, LinearMap.trace_mul_comm]

theorem tauC_conj (hC : ∀ a b : C, a * b = b * a) (c : C) (u : (MonoidAlgebra (Module.End Λ Y) C)ˣ)
    (a : MonoidAlgebra (Module.End Λ Y) C) :
    tauC c ((u : MonoidAlgebra (Module.End Λ Y) C) * a * ((u⁻¹ : (MonoidAlgebra (Module.End Λ Y) C)ˣ) :
      MonoidAlgebra (Module.End Λ Y) C)) = tauC c a := by
  rw [mul_assoc, tauC_mul_comm hC, mul_assoc, Units.inv_mul, mul_one]

/-- The idempotent of `End(Y)[C]` attached to a Higman element. -/
def eRep (ρ : Representation Λ C Y) (E : Y →ₗ[Λ] Y) : MonoidAlgebra (Module.End Λ Y) C :=
  ∑ c : C, single c (E * ρ c⁻¹)

theorem eRep_coeff (ρ : Representation Λ C Y) (E : Y →ₗ[Λ] Y) (c : C) :
    (eRep ρ E).coeff c = E * ρ c⁻¹ := by
  classical
  unfold eRep
  rw [coeff_sum, Finset.sum_apply']
  simp [Finsupp.single_apply]

theorem single_commute (hC : ∀ a b : C, a * b = b * a) (b : C) (x : MonoidAlgebra (Module.End Λ Y) C) :
    Commute (single b (1 : Module.End Λ Y)) x := by
  unfold Commute SemiconjBy
  ext1
  ext1 c
  rw [coeff_single_mul_apply, coeff_mul_single_apply, one_mul, mul_one, hC b⁻¹ c]

theorem natCast_eq_zero {n : ℕ} (hΛ : (n : Λ) = 0) : (n : MonoidAlgebra (Module.End Λ Y) C) = 0 := by
  rw [← map_natCast (algebraMap Λ (MonoidAlgebra (Module.End Λ Y) C)), hΛ, map_zero]

theorem isNilpotent_z {l a N : ℕ} (hl : l.Prime) (hΛ : ((l ^ N : ℕ) : Λ) = 0) {b : C}
    (hb : b ^ (l ^ a) = 1) : IsNilpotent (single b (1 : Module.End Λ Y) - 1) := by
  refine isNilpotent_sub_one_of_pow (a := a) hl (natCast_eq_zero hΛ) ?_
  rw [single_pow, hb, one_pow, ← one_def]

end Alg

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_B1b =====
section

/-!
# S4-GOS-C, part B1b: the conjugation argument and restriction of Higman elements

* `exists_sub_mapDomain`: if `φ x = x b^{j(x)}` then `φ_* x - x ∈ R (single b 1 - 1)` in `R = End(Y)[C]`;
* `tauC_eq_tauC_map`: `τ_c(e) = τ_c(φ_* e)` for an idempotent `e` (conjugate idempotents, `exists_unit_conj_of_idem`);
* **`trace_eq_zero_of_proj`**: `Tr(ρ g) = 0` when `g⁻¹ ∉ range φ` (abelian `C`, Higman element `E`);
* `isHigman_res`: restriction of a Higman element to a subgroup (`E_C = ∑_{q ∈ G/C} ρ q⁻¹ ∘ E ∘ ρ q`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open MonoidAlgebra

section Alg

variable {Λ : Type*} [CommRing Λ] {Y : Type*} [AddCommGroup Y] [Module Λ Y] [Module.Free Λ Y]
  [Module.Finite Λ Y] {C : Type*} [Group C] [Fintype C]

theorem eq_sum_single (x : MonoidAlgebra (Module.End Λ Y) C) : x = ∑ c : C, single c (x.coeff c) := by
  conv_lhs => rw [← sum_coeff_single x]
  rw [Finsupp.sum_fintype]
  intro c
  simp

theorem exists_sub_mapDomain (φ : C →* C) {b : C} (hφ : ∀ x : C, ∃ j : ℕ, φ x = x * b ^ j)
    (x : MonoidAlgebra (Module.End Λ Y) C) :
    ∃ w, mapDomainRingHom (Module.End Λ Y) φ x - x = w * (single b (1 : Module.End Λ Y) - 1) := by
  choose j hj using hφ
  refine ⟨∑ c : C, single c (x.coeff c) * ∑ i ∈ Finset.range (j c), single b (1 : Module.End Λ Y) ^ i, ?_⟩
  conv_lhs => rw [eq_sum_single x]
  rw [map_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [mapDomainRingHom_apply, mapDomain_single, hj c, mul_assoc, geom_sum_mul, single_pow, one_pow,
    mul_sub, mul_one, single_mul_single, mul_one]

theorem tauC_eq_tauC_map {l a N : ℕ} (hl : l.Prime) (hC : ∀ a b : C, a * b = b * a)
    (hΛ : ((l ^ N : ℕ) : Λ) = 0) (φ : C →* C) {b : C} (hb : b ^ (l ^ a) = 1)
    (hφ : ∀ x : C, ∃ j : ℕ, φ x = x * b ^ j) {e : MonoidAlgebra (Module.End Λ Y) C}
    (he : IsIdempotentElem e) (c : C) : tauC c e = tauC c (mapDomainRingHom (Module.End Λ Y) φ e) := by
  obtain ⟨w, hw⟩ := exists_sub_mapDomain φ hφ e
  obtain ⟨u, hu⟩ := exists_unit_conj_of_idem (he.map (mapDomainRingHom (Module.End Λ Y) φ)) he
    (isNilpotent_z (C := C) (Y := Y) hl hΛ hb)
    (fun r => (single_commute hC b r).sub_left (Commute.one_left r)) hw
  have h : mapDomainRingHom (Module.End Λ Y) φ e = (u : MonoidAlgebra (Module.End Λ Y) C) * e *
      ((u⁻¹ : (MonoidAlgebra (Module.End Λ Y) C)ˣ) : MonoidAlgebra (Module.End Λ Y) C) := by
    rw [hu, mul_assoc, Units.mul_inv, mul_one]
  rw [h, tauC_conj hC c u e]

theorem tauC_map_eq_zero (φ : C →* C) (x : MonoidAlgebra (Module.End Λ Y) C) {c : C}
    (hc : c ∉ Set.range φ) : tauC c (mapDomainRingHom (Module.End Λ Y) φ x) = 0 := by
  unfold tauC
  rw [mapDomainRingHom_apply]
  unfold mapDomain
  rw [coeff_ofCoeff, Finsupp.mapDomain_of_notMem_range _ _ hc, map_zero]

end Alg

section Res

variable {Λ : Type*} [CommRing Λ] {Y : Type*} [AddCommGroup Y] [Module Λ Y] [Module.Free Λ Y]
  [Module.Finite Λ Y] {G : Type*} [Group G] [Fintype G]

/-- `(G ⧸ C) × C ≃ G`, `(q, c) ↦ q.out * c`. -/
def quotProdEquiv (C : Subgroup G) : (G ⧸ C) × C ≃ G where
  toFun p := p.1.out * p.2
  invFun g := ((g : G ⧸ C), ⟨(Quotient.out (g : G ⧸ C))⁻¹ * g,
    QuotientGroup.leftRel_apply.mp (@Quotient.exact' _ (QuotientGroup.leftRel C) _ _ <| Quotient.out_eq' _)⟩)
  left_inv p := by
    obtain ⟨q, c⟩ := p
    have h1 : ((q.out * c : G) : G ⧸ C) = q := by
      rw [QuotientGroup.mk_mul_of_mem _ c.2, QuotientGroup.out_eq']
    refine Prod.ext h1 (Subtype.ext ?_)
    dsimp only
    rw [h1, ← mul_assoc, inv_mul_cancel, one_mul]
  right_inv g := by simp

end Res

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_B1c =====
section

/-!
# S4-GOS-C, part B1c: characters of projective modules vanish on `l`-singular elements

**`trace_eq_zero_of_dvd_orderOf`**: for a finite group `G`, a free finite `Λ`-module `Y` with `l ^ N = 0` in `Λ` and a
projective (Higman) representation `ρ`, `Tr(ρ g) = 0` whenever `l ∣ orderOf g`. Proof: restrict to `C = ⟨g⟩`
(`isHigman_res`), project onto the `l'`-part by `x ↦ x ^ t`, `t = (l ^ α) ^ φ(m)` (`trace_eq_zero_of_proj`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

/-- `x ↦ x ^ t` on a group whose elements commute. -/
def powHom {C : Type*} [Group C] (hC : ∀ a b : C, a * b = b * a) (t : ℕ) : C →* C where
  toFun x := x ^ t
  map_one' := one_pow t
  map_mul' x y := (show Commute x y from hC x y).mul_pow t

theorem zpowers_comm {G : Type*} [Group G] (g : G) : ∀ a b : Subgroup.zpowers g, a * b = b * a := by
  rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
  exact Subtype.ext (zpow_mul_comm g i j)

variable {Λ : Type*} [CommRing Λ] {Y : Type*} [AddCommGroup Y] [Module Λ Y] [Module.Free Λ Y]
  [Module.Finite Λ Y] {G : Type*} [Group G] [Fintype G]

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_C0 =====
section

/-!
# S4-GOS-C, part C0: traces agree on two lifts of the same module

A *lift* of a `Λ`-module `Y` with `G`-action `σ` is a `G`-equivariant surjection `f : X → Y` with `ker f ⊆ t • X`
(`t` nilpotent). **`trace_eq_of_lifts`**: if `X₁`, `X₂` are free finite lifts and `X₁` is projective (Higman), then
`Tr(ρ₁ g) = Tr(ρ₂ g)` for every `g`: an equivariant lift `X₁ → X₂` of the identity of `Y` is bijective, since it is
invertible up to endomorphisms with range in `t • X` (nilpotent).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

section Nil

variable {Λ : Type*} [CommRing Λ] {X : Type*} [AddCommGroup X] [Module Λ X]

theorem pow_apply_mem_smul {t : Λ} {T : Module.End Λ X} (hT : ∀ x, ∃ y, T x = t • y) :
    ∀ (n : ℕ) (x : X), ∃ y, (T ^ n) x = t ^ n • y := by
  intro n
  induction n with
  | zero => intro x; exact ⟨x, by simp⟩
  | succ n ih =>
    intro x
    obtain ⟨y, hy⟩ := ih x
    obtain ⟨z, hz⟩ := hT y
    refine ⟨z, ?_⟩
    rw [pow_succ' T n, Module.End.mul_apply, hy, map_smul, hz, smul_smul, pow_succ t n]

theorem isNilpotent_of_range_smul {t : Λ} {N : ℕ} (ht : t ^ N = 0) {T : Module.End Λ X}
    (hT : ∀ x, ∃ y, T x = t • y) : IsNilpotent T := by
  refine ⟨N, LinearMap.ext fun x => ?_⟩
  obtain ⟨y, hy⟩ := pow_apply_mem_smul hT N x
  rw [hy, ht, zero_smul, LinearMap.zero_apply]

/-- A map between two lifts that lifts the identity, with a linear quasi-inverse, is bijective. -/
theorem bijective_of_lifts {X₁ X₂ Y : Type*} [AddCommGroup X₁] [Module Λ X₁] [AddCommGroup X₂] [Module Λ X₂]
    [AddCommGroup Y] [Module Λ Y] {t : Λ} {N : ℕ} (ht : t ^ N = 0) {f₁ : X₁ →ₗ[Λ] Y} {f₂ : X₂ →ₗ[Λ] Y}
    (hk₁ : ∀ x, f₁ x = 0 → ∃ y, x = t • y) (hk₂ : ∀ x, f₂ x = 0 → ∃ y, x = t • y)
    {φ : X₁ →ₗ[Λ] X₂} {ψ : X₂ →ₗ[Λ] X₁} (hφ : f₂ ∘ₗ φ = f₁) (hψ : f₁ ∘ₗ ψ = f₂) :
    Function.Bijective φ := by
  have h1 : IsUnit (ψ ∘ₗ φ : Module.End Λ X₁) := by
    have hn : IsNilpotent (ψ ∘ₗ φ - 1 : Module.End Λ X₁) := isNilpotent_of_range_smul ht (fun x => hk₁ _ (by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, Module.End.one_apply, map_sub]
      rw [← LinearMap.comp_apply f₁ ψ, hψ, ← LinearMap.comp_apply f₂ φ, hφ, sub_self]))
    simpa using hn.isUnit_one_add
  have h2 : IsUnit (φ ∘ₗ ψ : Module.End Λ X₂) := by
    have hn : IsNilpotent (φ ∘ₗ ψ - 1 : Module.End Λ X₂) := isNilpotent_of_range_smul ht (fun x => hk₂ _ (by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, Module.End.one_apply, map_sub]
      rw [← LinearMap.comp_apply f₂ φ, hφ, ← LinearMap.comp_apply f₁ ψ, hψ, sub_self]))
    simpa using hn.isUnit_one_add
  have hb1 := (Module.End.isUnit_iff _).mp h1
  have hb2 := (Module.End.isUnit_iff _).mp h2
  refine ⟨fun a b hab => hb1.1 ?_, fun y => ?_⟩
  · show ψ (φ a) = ψ (φ b)
    rw [hab]
  · obtain ⟨x, hx⟩ := hb2.2 y
    exact ⟨ψ x, hx⟩

end Nil

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] [Fintype G]

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_LIFTa =====
section

/-!
# S4-GOS-C, part LIFTa: permutation modules and reduction maps for lifting projective modules

* `leftAct`: `G` acts on `G × ι` by left multiplication on `G` (freely, `leftAct_free`);
* `permRepM`: the permutation representation on `X → M` over `Λ`;
* `red X : (X → Λ) → (X → Λ')` (coefficientwise `algebraMap`): equivariant, onto, kernel `t • _`;
* `pMap σ' b : (G × ι → Λ') → Y'`, `f ↦ ∑ f (h, i) • σ' h (b i)`: equivariant and onto for a basis `b`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

/-- `G` acts on `G × ι` by left multiplication on the first factor. -/
abbrev leftAct (G : Type*) [Group G] (ι : Type*) : MulAction G (G × ι) where
  smul g p := (g * p.1, p.2)
  one_smul p := Prod.ext (one_mul p.1) rfl
  mul_smul g h p := Prod.ext (mul_assoc g h p.1) rfl

attribute [local instance] leftAct

theorem leftAct_smul {G : Type*} [Group G] {ι : Type*} (g : G) (p : G × ι) : g • p = (g * p.1, p.2) := rfl

theorem leftAct_free {G : Type*} [Group G] {ι : Type*} (g : G) (p : G × ι) (h : g • p = p) : g = 1 := by
  rw [leftAct_smul] at h
  exact mul_eq_right.mp (congrArg Prod.fst h)

/-- The permutation representation on `X → M`. -/
def permRepM (Λ G : Type*) [CommRing Λ] [Group G] (X : Type*) [MulAction G X] (M : Type*) [AddCommGroup M]
    [Module Λ M] : Representation Λ G (X → M) where
  toFun g := LinearMap.funLeft Λ M (fun x => g⁻¹ • x)
  map_one' := LinearMap.ext fun f => funext fun x => by
    simp only [inv_one, one_smul, LinearMap.funLeft_apply, Module.End.one_apply]
  map_mul' g h := LinearMap.ext fun f => funext fun x => by
    simp only [Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev, mul_smul]

theorem permRepM_apply {Λ G : Type*} [CommRing Λ] [Group G] {X : Type*} [MulAction G X] {M : Type*}
    [AddCommGroup M] [Module Λ M] (g : G) (f : X → M) (x : X) : permRepM Λ G X M g f x = f (g⁻¹ • x) := rfl

section Red

variable {Λ Λ' : Type*} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ']

/-- Coefficientwise reduction `(X → Λ) → (X → Λ')`. -/
def red (X : Type*) : (X → Λ) →ₗ[Λ] (X → Λ') := LinearMap.compLeft (Algebra.linearMap Λ Λ') X

theorem red_apply (X : Type*) (f : X → Λ) (x : X) : red (Λ' := Λ') X f x = algebraMap Λ Λ' (f x) := rfl

theorem red_surjective (hsurj : Function.Surjective (algebraMap Λ Λ')) (X : Type*) :
    Function.Surjective (red (Λ := Λ) (Λ' := Λ') X) :=
  fun f => ⟨fun x => (hsurj (f x)).choose, funext fun x => (hsurj (f x)).choose_spec⟩

end Red

section PMap

variable {Λ' : Type*} [CommRing Λ'] {G : Type*} [Group G] [Fintype G] {Y' : Type*} [AddCommGroup Y']
  [Module Λ' Y'] {ι : Type*} [Fintype ι]

/-- `f ↦ ∑ f (h, i) • σ' h (b i)`. -/
def pMap (σ' : Representation Λ' G Y') (b : ι → Y') : (G × ι → Λ') →ₗ[Λ'] Y' :=
  Fintype.linearCombination Λ' (fun x : G × ι => σ' x.1 (b x.2))

theorem pMap_surjective (σ' : Representation Λ' G Y') (b : Module.Basis ι Λ' Y') :
    Function.Surjective (pMap σ' b) := by
  classical
  intro y
  refine ⟨fun x => if x.1 = 1 then b.repr y x.2 else 0, ?_⟩
  rw [pMap, Fintype.linearCombination_apply, Fintype.sum_prod_type, Finset.sum_eq_single (1 : G)]
  · simp only [if_true, map_one, Module.End.one_apply]
    exact b.sum_repr y
  · intro h _ hh
    simp only [hh, if_false, zero_smul, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end PMap

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_LIFTb =====
section

/-!
# S4-GOS-C, part LIFTb: lifting the idempotent of a projective module

For `Λ → Λ'` onto with kernel `t Λ`, `t ^ N = 0`, a free finite `Λ'`-module `Y'` with basis `b` and a projective
(Higman) `Λ'`-representation `σ'`: **`exists_idem_lift`** gives an equivariant section `s'` of `pMap σ' b` and an
equivariant idempotent `e` of the free permutation module `G × ι → Λ` with `red ∘ e = (s' ∘ pMap) ∘ red`
(lift `s' ∘ pMap` equivariantly, then correct it to an idempotent by `1 - (1 - x ^ n) ^ n`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

attribute [local instance] leftAct

section Int

variable {Λ Λ' : Type*} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {X : Type*}

theorem int_one : red (Λ' := Λ') X ∘ₗ (1 : Module.End Λ (X → Λ)) = (1 : Module.End Λ (X → Λ')) ∘ₗ red X :=
  LinearMap.ext fun _ => rfl

theorem int_mul {a b : Module.End Λ (X → Λ)} {a' b' : Module.End Λ (X → Λ')}
    (ha : red X ∘ₗ a = a' ∘ₗ red X) (hb : red X ∘ₗ b = b' ∘ₗ red X) :
    red X ∘ₗ (a * b) = (a' * b') ∘ₗ red X := LinearMap.ext fun f => by
  have h1 := LinearMap.congr_fun ha (b f)
  have h2 := LinearMap.congr_fun hb f
  simp only [LinearMap.comp_apply, Module.End.mul_apply] at h1 h2 ⊢
  rw [h1, h2]

theorem int_sub {a b : Module.End Λ (X → Λ)} {a' b' : Module.End Λ (X → Λ')}
    (ha : red X ∘ₗ a = a' ∘ₗ red X) (hb : red X ∘ₗ b = b' ∘ₗ red X) :
    red X ∘ₗ (a - b) = (a' - b') ∘ₗ red X := LinearMap.ext fun f => by
  have h1 := LinearMap.congr_fun ha f
  have h2 := LinearMap.congr_fun hb f
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub] at h1 h2 ⊢
  rw [h1, h2]

theorem int_pow {a : Module.End Λ (X → Λ)} {a' : Module.End Λ (X → Λ')} (ha : red X ∘ₗ a = a' ∘ₗ red X) :
    ∀ k : ℕ, red X ∘ₗ (a ^ k) = (a' ^ k) ∘ₗ red X
  | 0 => by rw [pow_zero, pow_zero]; exact int_one
  | k + 1 => by rw [pow_succ, pow_succ]; exact int_mul (int_pow ha k) ha

end Int

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {G : Type} [Group G] [Fintype G]
  {Y' : Type} [AddCommGroup Y'] [Module Λ' Y'] [Module.Free Λ' Y'] {ι : Type} [Fintype ι]

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_LIFTc =====
section

/-!
# S4-GOS-C, part LIFTc: projective modules lift

**`exists_proj_lift`**: for `Λ → Λ'` onto with kernel `t Λ`, `t ^ N = 0`, `Λ` local, every projective (Higman)
representation `σ'` on a free finite `Λ'`-module `Y'` has a *lift*: a free finite `Λ`-module `X` with a projective
representation `ρ` and an equivariant `Λ`-linear surjection `f : X → Y'` with `ker f ⊆ t • X`
(`X` = range of the lifted idempotent of `exists_idem_lift`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

attribute [local instance] leftAct

/-- The representation on the range of an endomorphism commuting with `ρ`. -/
def rangeRep {R : Type*} [CommRing R] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (e : Module.End R V) (he : ∀ g, Commute e (ρ g)) :
    Representation R G (LinearMap.range e) where
  toFun g := (ρ g).restrict (p := LinearMap.range e) (q := LinearMap.range e) (fun x hx => by
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    exact LinearMap.mem_range.mpr ⟨ρ g y, LinearMap.congr_fun (he g).eq y⟩)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [Module.End.mul_apply]

theorem rangeRep_coe {R : Type*} [CommRing R] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (e : Module.End R V) (he : ∀ g, Commute e (ρ g)) (g : G)
    (x : LinearMap.range e) : ((rangeRep ρ e he g x : LinearMap.range e) : V) = ρ g x := rfl

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {G : Type} [Group G] [Fintype G]
  {Y' : Type} [AddCommGroup Y'] [Module Λ' Y'] [Module.Free Λ' Y'] [Module Λ Y'] [IsScalarTower Λ Λ' Y']
  {ι : Type} [Fintype ι]

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_BETA =====
section

/-!
# S4-GOS-C, part BETA: the Brauer trace function `β`

* `isProj_of_card_unit`: `|G|` a unit ⇒ every representation is projective (Higman element `|G|⁻¹ • 1`);
* `isProj_tprod`: `P` projective ⇒ `P ⊗ M` projective;
* `resRep τ`: a `Λ'`-representation viewed as a `Λ`-representation;
* **`IsBeta t l τ β`**: `β g = 0` for `l`-singular `g`; for `l`-regular `g`, `β g` is the trace of `g` on every free
  finite lift of `τ|⟨g⟩` to `Λ` (well defined by C0);
* **`exists_beta`**: such a `β` exists (projective lifts of `τ|⟨g⟩` exist by LIFT, `|⟨g⟩|` a unit in `Λ'`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

section Gen

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module R V]

variable {M : Type*} [AddCommGroup M] [Module R M]

end Gen

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {G : Type} [Group G]
  {M : Type} [AddCommGroup M] [Module Λ' M] [Module Λ M] [IsScalarTower Λ Λ' M]

/-- A `Λ'`-representation viewed as a `Λ`-representation. -/
def resRep (τ : Representation Λ' G M) : Representation Λ G M where
  toFun g := (τ g).restrictScalars Λ
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [Module.End.mul_apply]

theorem resRep_apply (τ : Representation Λ' G M) (g : G) (x : M) : resRep (Λ := Λ) τ g x = τ g x := rfl

/-- **The Brauer trace function** of `τ` at level `Λ`. -/
def IsBeta (t : Λ) (l : ℕ) (τ : Representation Λ' G M) (β : G → Λ) : Prop :=
  ∀ g : G, (l ∣ orderOf g → β g = 0) ∧ (¬ l ∣ orderOf g → ∀ (X : Type) [AddCommGroup X] [Module Λ X]
    [Module.Free Λ X] [Module.Finite Λ X] (ρ : Representation Λ (Subgroup.zpowers g) X) (f : X →ₗ[Λ] M),
    Function.Surjective f → (∀ x, f x = 0 → ∃ y, x = t • y) → (∀ c x, f (ρ c x) = τ c (f x)) →
    LinearMap.trace Λ X (ρ ⟨g, Subgroup.mem_zpowers g⟩) = β g)

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_HSR =====
section

/-!
# S4-GOS-C, part HSR: the sum of the character of a projective module

For a projective (Higman) representation `ρ` of a finite group on a free finite module over a local ring,
the coinvariants are free finite (`coinv_free_finite_of_proj`, a retract via `[x] ↦ ∑_h E (ρ h x)`) and
**`sum_trace_eq_card_mul_finrank`**: `∑_g Tr(ρ g) = |G| · rank X_G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open Representation

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] [Fintype G]
  {X : Type*} [AddCommGroup X] [Module Λ X]

/-- The section `X_G → X`, `[x] ↦ ∑_h E (ρ h x)`, of a Higman element. -/
def coinvSecE (ρ : Representation Λ G X) (E : X →ₗ[Λ] X) : Coinvariants ρ →ₗ[Λ] X :=
  Coinvariants.lift ρ (∑ h : G, E ∘ₗ ρ h) (fun g => LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, LinearMap.sum_apply]
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => by simp [map_mul, Module.End.mul_apply]))

theorem coinvSecE_mk (ρ : Representation Λ G X) (E : X →ₗ[Λ] X) (x : X) :
    coinvSecE ρ E (Coinvariants.mk ρ x) = ∑ h : G, E (ρ h x) := by
  rw [coinvSecE, Coinvariants.lift_mk, LinearMap.sum_apply]
  rfl

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_HSR2 =====
section

/-!
# S4-GOS-C, part HSR2: coinvariants of a lift

For `Λ → Λ'` onto with kernel `t Λ` and a lift `f : X → Y'` (onto, kernel in `t • X`, equivariant) of a
`Λ'`-representation `σ'` by a projective `Λ`-representation `ρ` on a free finite module (`Λ` local):
**`finrank_coinv_lift`**: `finrank Λ' (Coinvariants σ') = finrank Λ (Coinvariants ρ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open Representation

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {G : Type} [Group G]
  {X Y' : Type} [AddCommGroup X] [Module Λ X] [AddCommGroup Y'] [Module Λ' Y'] [Module Λ Y']
  [IsScalarTower Λ Λ' Y']

/-- Every element of `Coinvariants.ker σ'` is the image of an element of `Coinvariants.ker ρ`. -/
theorem exists_ker_lift (hsurj : Function.Surjective (algebraMap Λ Λ')) {ρ : Representation Λ G X}
    {σ' : Representation Λ' G Y'} {f : X →ₗ[Λ] Y'} (hf : Function.Surjective f)
    (hfρ : ∀ g x, f (ρ g x) = σ' g (f x)) {v : Y'} (hv : v ∈ Coinvariants.ker σ') :
    ∃ x ∈ Coinvariants.ker ρ, f x = v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨g, y⟩, rfl⟩ := hv
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨ρ g x - x, Coinvariants.sub_mem_ker g x, by rw [map_sub, hfρ]⟩
  | zero => exact ⟨0, zero_mem _, map_zero f⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x + y, add_mem hx hy, map_add f x y⟩
  | smul c a _ ha =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨r, rfl⟩ := hsurj c
    exact ⟨r • x, Submodule.smul_mem _ r hx, by rw [map_smul, algebraMap_smul]⟩

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_TLIFT =====
section

/-!
# S4-GOS-C, part TLIFT: reductions, `1 ⊗ q = 0`, and tensor products of lifts

For `Λ → Λ'` onto with kernel `t Λ`:
* **`ker_one_tmul`**: `1 ⊗ₜ q = 0` in `Λ' ⊗[Λ] Q` forces `q ∈ t • Q` (via `Λ' ≅ Λ ⧸ ker`, `quotTensorEquivQuotSMul`);
* **`exists_tensor_lift`**: if `fP : P → P'`, `fM : M → M'` are onto with kernels in `t •`, there is a `Λ`-linear
  `T : P ⊗[Λ] M → P' ⊗[Λ'] M'` with `T (p ⊗ m) = fP p ⊗ fM m`, onto, with kernel in `t •`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.GOS

open TensorProduct

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ']

/-- `1 ⊗ₜ q = 0` in `Λ' ⊗[Λ] Q` forces `q ∈ t • Q` when `Λ → Λ'` is onto with kernel `t Λ`. -/
theorem ker_one_tmul (hsurj : Function.Surjective (algebraMap Λ Λ')) {t : Λ}
    (hker : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = t * s)
    {Q : Type} [AddCommGroup Q] [Module Λ Q] (q : Q) (h : (1 : Λ') ⊗ₜ[Λ] q = 0) : ∃ y, q = t • y := by
  let I : Ideal Λ := RingHom.ker (Algebra.ofId Λ Λ')
  let e : (Λ ⧸ I) ≃ₐ[Λ] Λ' := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId Λ Λ') hsurj
  have h1 : (1 : Λ ⧸ I) ⊗ₜ[Λ] q = 0 := by
    have h' := congrArg (LinearMap.rTensor Q e.symm.toLinearMap) h
    rwa [LinearMap.rTensor_tmul, map_zero, AlgEquiv.toLinearMap_apply, map_one] at h'
  have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul Q I) h1
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero] at h2
  have h3 : q ∈ I • (⊤ : Submodule Λ Q) := (Submodule.Quotient.mk_eq_zero _).mp h2
  refine Submodule.smul_induction_on (p := fun x => ∃ y, x = t • y) h3 (fun r hr n _ => ?_)
    (fun a b ha hb => ?_)
  · obtain ⟨s, rfl⟩ := hker r (RingHom.mem_ker.mp hr)
    exact ⟨s • n, mul_smul _ _ _⟩
  · obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', (smul_add _ _ _).symm⟩

variable {P P' M M' : Type} [AddCommGroup P] [Module Λ P] [AddCommGroup P'] [Module Λ' P'] [Module Λ P']
  [IsScalarTower Λ Λ' P'] [AddCommGroup M] [Module Λ M] [AddCommGroup M'] [Module Λ' M'] [Module Λ M']
  [IsScalarTower Λ Λ' M']

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_EUL =====
section

/-!
# S4-GOS-C, part EUL: the Euler characteristic of the perfect complex is `h²_c - h¹_c`

`finrank_euler3`: for a complex `K⁰ → K¹ → K²` of finite-dimensional spaces with `d⁰` injective,
`dim K⁰ - dim K¹ + dim K² = dim H² - dim H¹`. With the term isomorphisms `pcIso0/1/2`, `H¹ = H¹_c` (`hc1Equiv`) and
`H² ≅ H²_c` (`h2Equiv_lisse`): **`chi_eq_h2c_sub_h1c`**: `Σ_i (-1)^i dim (PC i ⊗ M)_{Gf} = h²_c(M) - h¹_c(M)` over `ℤ/l`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CP4a Representation Lefschetz

section Dim

variable {k : Type*} [Field k] {K0 K1 K2 : Type*} [AddCommGroup K0] [Module k K0] [AddCommGroup K1]
  [Module k K1] [AddCommGroup K2] [Module k K2] [FiniteDimensional k K0] [FiniteDimensional k K1]
  [FiniteDimensional k K2]

theorem alt_sum_three {b0 b1 b2 : ℕ} {c : ℤ} (f : ℕ → ℕ) (h0 : f 0 = b0) (h1 : f 1 = b1) (h2 : f 2 = b2)
    (hE : (b0 : ℤ) - b1 + b2 = c) : ∑ i ∈ Finset.range 3, (-1 : ℤ) ^ i * (f i : ℤ) = c := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, h2, ← hE]
  ring

end Dim

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_C_GOSF =====
section

/-!
# S4-GOS-C, part GOSF: the abstract GOS combination and integrality

* `int_eq_of_forall_zmod`: integers congruent modulo every `l ^ n` (`l ≥ 2`) are equal;
* **`sum_Phi_mul_beta`**: if `Φ g = Σ_Q Σ_{j<J} [g ∈ W Q j] deg Q` for `g ≠ 1`, `Σ_g Φ g = |G| c`, `β 1 = d₀` and
  `Σ_{g ∈ W Q j} β g = |W Q j| d Q j`, then `Σ_g Φ g β g = |G| c d₀ - Σ_Q Σ_j deg Q |W Q j| (d₀ - d Q j)`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.GOS

open Finset

/-- Integers congruent modulo all powers `l ^ n` (`l ≥ 2`) are equal. -/
theorem int_eq_of_forall_zmod {l : ℕ} (hl : 2 ≤ l) {a b : ℤ}
    (h : ∀ n : ℕ, 0 < n → ((a : ZMod (l ^ n)) = (b : ZMod (l ^ n)))) : a = b := by
  by_contra hab
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  set n := (b - a).natAbs + 1 with hn
  have hd : ((l ^ n : ℕ) : ℤ) ∣ b - a := (ZMod.intCast_eq_intCast_iff_dvd_sub a b (l ^ n)).mp (h n (by omega))
  have hdvd : l ^ n ∣ (b - a).natAbs := by
    have h' := Int.natAbs_dvd_natAbs.mpr hd
    rwa [Int.natAbs_natCast] at h'
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hdvd
  have hlt : n < l ^ n := Nat.lt_pow_self (by omega)
  omega

variable {G : Type*} [Group G] [Fintype G] {Λ : Type*} [CommRing Λ] {S : Type*} [Fintype S]

/-- **The abstract GOS combination.** -/
theorem sum_Phi_mul_beta [DecidableEq G] (Φ : G → ℤ) (deg : S → ℤ) (J : ℕ) (W : S → ℕ → Finset G)
    (hΦ : ∀ g, g ≠ 1 → Φ g = ∑ Q, ∑ j ∈ range J, if g ∈ W Q j then deg Q else 0)
    (c : ℤ) (hsum : ∑ g, Φ g = Fintype.card G * c) (β : G → Λ) (d0 : ℤ) (hβ1 : β 1 = d0) (d : S → ℕ → ℤ)
    (hβW : ∀ Q, ∀ j ∈ range J, ∑ g ∈ W Q j, β g = ((W Q j).card : Λ) * d Q j) :
    ∑ g, (Φ g : Λ) * β g = ((Fintype.card G * c * d0 -
      ∑ Q, ∑ j ∈ range J, deg Q * (W Q j).card * (d0 - d Q j) : ℤ) : Λ) := by
  set Φ' : G → ℤ := fun g => ∑ Q, ∑ j ∈ range J, if g ∈ W Q j then deg Q else 0 with hΦ'
  have hind : ∀ Q j, ∑ g : G, (if g ∈ W Q j then deg Q else 0) = deg Q * (W Q j).card := by
    intro Q j
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hindΛ : ∀ Q j, ∑ g : G, (((if g ∈ W Q j then deg Q else 0 : ℤ) : Λ) * β g) =
      (deg Q : Λ) * ∑ g ∈ W Q j, β g := by
    intro Q j
    simp only [apply_ite (Int.cast : ℤ → Λ), Int.cast_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  have hΦ'sum : ∑ g, Φ' g = ∑ Q, ∑ j ∈ range J, deg Q * (W Q j).card := by
    simp only [hΦ']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hind Q j
  have hΦ'β : ∑ g, (Φ' g : Λ) * β g = ∑ Q, ∑ j ∈ range J, (deg Q : Λ) * ((W Q j).card * d Q j) := by
    simp only [hΦ', Int.cast_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hindΛ, hβW Q j hj]
  have e1 : ∑ g, (Φ g - Φ' g) = Φ 1 - Φ' 1 := Finset.sum_eq_single 1
    (fun g _ hg => by rw [hΦ g hg, sub_self]) (fun h => absurd (Finset.mem_univ _) h)
  have e2 : ∑ g, ((Φ g : Λ) - Φ' g) * β g = ((Φ 1 : Λ) - Φ' 1) * β 1 := Finset.sum_eq_single 1
    (fun g _ hg => by rw [hΦ g hg, sub_self, zero_mul]) (fun h => absurd (Finset.mem_univ _) h)
  rw [Finset.sum_sub_distrib] at e1
  simp only [sub_mul, Finset.sum_sub_distrib] at e2
  have hsplit : ∑ g, (Φ g : Λ) * β g = ∑ g, (Φ' g : Λ) * β g + ((Φ 1 : Λ) - Φ' 1) * β 1 := by
    linear_combination e2
  have hΦ1 : Φ 1 - Φ' 1 = Fintype.card G * c - ∑ Q, ∑ j ∈ range J, deg Q * (W Q j).card := by
    rw [← e1, hsum, hΦ'sum]
  have hΦ1Λ : ((Φ 1 : Λ) - Φ' 1) = ((Fintype.card G * c - ∑ Q, ∑ j ∈ range J, deg Q * (W Q j).card : ℤ) : Λ) := by
    rw [← hΦ1]; push_cast; ring
  rw [hsplit, hΦ'β, hβ1, hΦ1Λ]
  have A : ∑ Q, ∑ j ∈ range J, (deg Q : Λ) * ((W Q j).card : Λ) * ((d0 : Λ) - d Q j) =
      (∑ Q, ∑ j ∈ range J, (deg Q : Λ) * (W Q j).card) * d0 -
        ∑ Q, ∑ j ∈ range J, (deg Q : Λ) * ((W Q j).card * d Q j) := by
    simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun Q _ => Finset.sum_congr rfl fun j _ => by ring
  push_cast
  rw [A]
  ring

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_Swan_Slope1a =====
section

/-!
# S4-Swan (K2), part 28: slope-1 local structure (abstract part)

* `mem_of_map_eq_one`: a homomorphism `Φ : G → Fq` mapping `U` onto `Fq` and killing `W ≤ U` with `|U/W| ≤ q`
  has kernel on `U` exactly `W`; then every character of `U` trivial on `W` is `ψ' ∘ Φ` (`exists_addChar_eq`).
* `exists_eigen`: a representation on which `W` acts trivially has, for a primitive `ψ`, a common eigenvector of
  `U` with eigencharacter `ψ(a Φ(·))`, so `fixd (ρ ⊗ ψ(b Φ)) U ≠ ⊥` for some `b` (`exists_fixd_twist_ne_bot`).
* `RamFn.swan_lt_of_fixd`: all breaks `≤ 1` and `V^{G^1} ≠ 0` give `Sw(ρ) < dim V`.
* `LocData.card_lower_quot_le`: `|G_m / G_{m+1}| ≤ |T|` for a residue map `L → T`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Swan

noncomputable section

open Module

section Group

variable {G : Type*} [Group G] {Fq : Type*} [Field Fq] [Fintype Fq]
variable {U W : Subgroup G} (Φ : G →* Multiplicative Fq)

section Sect

variable (hsurj : ∀ c : Fq, ∃ σ ∈ U, Φ σ = Multiplicative.ofAdd c)

end Sect

variable [Finite G] (hWU : W ≤ U) (hsurj : ∀ c : Fq, ∃ σ ∈ U, Φ σ = Multiplicative.ofAdd c)
  (hW : ∀ σ ∈ W, Φ σ = 1) (hcard : Nat.card (U ⧸ W.subgroupOf U) ≤ Nat.card Fq)
include hWU hsurj hW hcard

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

end Group

namespace RamFn

variable {G : Type*} [Group G] [Fintype G] (R : RamFn G)
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (ρ : Representation k G V)

end RamFn

namespace LocData

variable {G L : Type*} [Group G] [Field L] [MulSemiringAction G L] (D : LocData G L)

theorem le_of_natCast_le_toENat {n : ℕ} (hn : 1 ≤ n) {w : WithTop ℤ} (h : (n : ℕ∞) ≤ toENat w) :
    (n : WithTop ℤ) ≤ w := by
  induction w with
  | top => exact le_top
  | coe z =>
    rw [toENat_coe, Nat.cast_le] at h
    rw [← WithTop.coe_natCast, WithTop.coe_le_coe]
    omega

theorem ϖ_ne_zero : D.ϖ ≠ 0 := fun h0 => by
  have h := D.v_ϖ
  rw [h0, AddValuation.map_zero] at h
  exact WithTop.top_ne_coe h

/-- `x = (x ϖ^{-n}) ϖ^n` and the valuation shift. -/
theorem v_shift (x : L) (n : ℕ) : D.v x = D.v (x * (D.ϖ ^ n)⁻¹) + (n : WithTop ℤ) := by
  have h : x = x * (D.ϖ ^ n)⁻¹ * D.ϖ ^ n := by
    rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero n D.ϖ_ne_zero), mul_one]
  conv_lhs => rw [h]
  rw [AddValuation.map_mul, AddValuation.map_pow, D.v_ϖ, nsmul_one]

theorem nonneg_shift {x : L} {n : ℕ} (h : (n : WithTop ℤ) ≤ D.v x) : 0 ≤ D.v (x * (D.ϖ ^ n)⁻¹) := by
  rw [D.v_shift x n, ← WithTop.coe_natCast] at h
  have h' : (0 : WithTop ℤ) + ((n : ℤ) : WithTop ℤ) ≤ D.v (x * (D.ϖ ^ n)⁻¹) + ((n : ℤ) : WithTop ℤ) := by
    rwa [zero_add]
  exact (WithTop.add_le_add_iff_right WithTop.coe_ne_top).1 h'

end LocData

end

end Swan
end RamanujanPetersson


end

-- ===== S4.Def_RP_GOS_C_WILD =====
section

/-!
# S4-GOS-C, part WILD: wild ramification groups are `p`-groups

For local data `D` (valuation `v`, uniformizer `ϖ`, `G` acting with trivial residue action) on a field `L` of
characteristic `p`: if `i(σ) = k + 1 ≥ 2` then `σ^n ϖ - ϖ ≡ n (σ ϖ - ϖ)` modulo valuation `k + 2`, so `p ∣ orderOf σ`
(**`dvd_orderOf_of_mem_lower`**); hence **`not_dvd_card_lower`**: `l ∤ |G_u|` for `u ≥ 1` and primes `l ≠ p`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.GOS

open Swan

variable {G L : Type*} [Group G] [Field L] [MulSemiringAction G L] (D : LocData G L)

theorem v_natCast_nonneg (n : ℕ) : 0 ≤ D.v (n : L) := by
  induction n with
  | zero => rw [Nat.cast_zero, AddValuation.map_zero]; exact le_top
  | succ n ih =>
    rw [Nat.cast_succ]
    exact AddValuation.map_le_add _ ih (by rw [AddValuation.map_one])

theorem v_natCast_eq_zero {p : ℕ} [Fact p.Prime] [CharP L p] {m : ℕ} (hm : ¬ p ∣ m) : D.v (m : L) = 0 := by
  have hm0 : (m : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  set c : ZMod p := (m : ZMod p)⁻¹
  have h1 : (m : L) * ((c.val : ℕ) : L) = 1 := by
    have h2 := congrArg (ZMod.castHom (dvd_refl p) L) (mul_inv_cancel₀ hm0)
    rw [map_mul, map_natCast, map_one, ← ZMod.natCast_zmod_val (m : ZMod p)⁻¹, map_natCast] at h2
    exact h2
  have h3 := congrArg D.v h1
  rw [AddValuation.map_mul, AddValuation.map_one] at h3
  exact le_antisymm (h3 ▸ le_add_of_nonneg_right (v_natCast_nonneg D c.val)) (v_natCast_nonneg D m)

variable {σ : G} {k : ℕ} (hσ : ((k + 1 : ℕ) : WithTop ℤ) ≤ D.v (σ • D.ϖ - D.ϖ))
include hσ

theorem v_smul_pow_sub (j : ℕ) : ((j + k : ℕ) : WithTop ℤ) ≤ D.v (σ • D.ϖ ^ j - D.ϖ ^ j) := by
  induction j with
  | zero => rw [pow_zero, smul_one, sub_self, AddValuation.map_zero]; exact le_top
  | succ j ih =>
    have hdec : σ • D.ϖ ^ (j + 1) - D.ϖ ^ (j + 1) =
        σ • D.ϖ ^ j * (σ • D.ϖ - D.ϖ) + D.ϖ * (σ • D.ϖ ^ j - D.ϖ ^ j) := by
      rw [pow_succ, smul_mul']; ring
    rw [hdec]
    apply AddValuation.map_le_add
    · rw [AddValuation.map_mul, D.v_smul, AddValuation.map_pow, D.v_ϖ, nsmul_one,
        show ((j + 1 + k : ℕ) : WithTop ℤ) = (j : WithTop ℤ) + ((k + 1 : ℕ) : WithTop ℤ) by
          rw [← Nat.cast_add]; congr 1; omega]
      exact add_le_add le_rfl hσ
    · rw [AddValuation.map_mul, D.v_ϖ, show ((j + 1 + k : ℕ) : WithTop ℤ) = 1 + ((j + k : ℕ) : WithTop ℤ) by
          rw [show j + 1 + k = 1 + (j + k) by omega, Nat.cast_add, Nat.cast_one]]
      exact add_le_add le_rfl ih

theorem v_smul_sub_ge {x : L} {m : ℕ} (hx : (m : WithTop ℤ) ≤ D.v x) :
    ((m + k : ℕ) : WithTop ℤ) ≤ D.v (σ • x - x) := by
  set y := x * (D.ϖ ^ m)⁻¹ with hy
  have hy0 : 0 ≤ D.v y := D.nonneg_shift hx
  have hxy : x = y * D.ϖ ^ m := by rw [hy, inv_mul_cancel_right₀ (pow_ne_zero _ D.ϖ_ne_zero)]
  have hdec : σ • x - x = (σ • y - y) * σ • D.ϖ ^ m + y * (σ • D.ϖ ^ m - D.ϖ ^ m) := by
    rw [hxy, smul_mul']; ring
  rw [hdec]
  apply AddValuation.map_le_add
  · rw [AddValuation.map_mul, D.v_smul, AddValuation.map_pow, D.v_ϖ, nsmul_one,
      show ((m + k : ℕ) : WithTop ℤ) = ((k : ℕ) : WithTop ℤ) + (m : WithTop ℤ) by rw [← Nat.cast_add, add_comm]]
    refine add_le_add (le_trans ?_ (hσ.trans (D.lb_bot D.v_ϖ σ hy0))) le_rfl
    exact_mod_cast Nat.le_succ k
  · rw [AddValuation.map_mul]
    calc ((m + k : ℕ) : WithTop ℤ) = 0 + ((m + k : ℕ) : WithTop ℤ) := (zero_add _).symm
      _ ≤ _ := add_le_add hy0 (v_smul_pow_sub D hσ m)

theorem v_pow_smul_sub (hk : 1 ≤ k) : ∀ n : ℕ, ((k + 1 : ℕ) : WithTop ℤ) ≤ D.v (σ ^ n • D.ϖ - D.ϖ) ∧
    ((k + 2 : ℕ) : WithTop ℤ) ≤ D.v (σ ^ n • D.ϖ - D.ϖ - (n : L) * (σ • D.ϖ - D.ϖ))
  | 0 => by
    simp only [pow_zero, one_smul, sub_self, Nat.cast_zero, zero_mul, AddValuation.map_zero]
    exact ⟨le_top, le_top⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := v_pow_smul_sub hk n
    have h3 := v_smul_sub_ge D hσ h1
    have h3' : ((k + 2 : ℕ) : WithTop ℤ) ≤ D.v (σ • (σ ^ n • D.ϖ - D.ϖ) - (σ ^ n • D.ϖ - D.ϖ)) :=
      le_trans (by exact_mod_cast (by omega : k + 2 ≤ k + 1 + k)) h3
    have he : σ ^ (n + 1) • D.ϖ - D.ϖ = (σ • D.ϖ - D.ϖ) + (σ ^ n • D.ϖ - D.ϖ) +
        (σ • (σ ^ n • D.ϖ - D.ϖ) - (σ ^ n • D.ϖ - D.ϖ)) := by
      rw [pow_succ', mul_smul, smul_sub]; ring
    refine ⟨?_, ?_⟩
    · rw [he]
      refine AddValuation.map_le_add _ (AddValuation.map_le_add _ hσ h1) (le_trans ?_ h3')
      exact_mod_cast (by omega : k + 1 ≤ k + 2)
    · have he' : σ ^ (n + 1) • D.ϖ - D.ϖ - ((n + 1 : ℕ) : L) * (σ • D.ϖ - D.ϖ) =
          (σ ^ n • D.ϖ - D.ϖ - (n : L) * (σ • D.ϖ - D.ϖ)) +
            (σ • (σ ^ n • D.ϖ - D.ϖ) - (σ ^ n • D.ϖ - D.ϖ)) := by
        rw [he]; push_cast; ring
      rw [he']
      exact AddValuation.map_le_add _ h2 h3'

omit hσ

/-- Elements of `G_1 ∖ {1}` have order divisible by `p`. -/
theorem dvd_orderOf_of_mem_lower {p : ℕ} [Fact p.Prime] [CharP L p] {σ : G} (hσ : σ ∈ D.ramFn.lower 1)
    (hσ1 : σ ≠ 1) : p ∣ orderOf σ := by
  by_contra hm
  have hne : D.v (σ • D.ϖ - D.ϖ) ≠ ⊤ := by
    rw [AddValuation.ne_top_iff, sub_ne_zero]
    exact fun h => hσ1 (D.eq_one_of_fix_ϖ h)
  have h2 : ((2 : ℕ) : WithTop ℤ) ≤ D.v (σ • D.ϖ - D.ϖ) := by
    have := (RamFn.mem_lower D.ramFn).mp hσ
    rw [D.ramFn_i] at this
    exact LocData.le_of_natCast_le_toENat (by norm_num) this
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp hne
  have hz2 : 2 ≤ z := by
    rw [← hz, ← WithTop.coe_natCast] at h2
    have h2' : ((2 : ℕ) : ℤ) ≤ z := WithTop.coe_le_coe.mp h2
    simpa using h2'
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = ((k + 1 : ℕ) : ℤ) := ⟨(z - 1).toNat, by omega⟩
  have hk : 1 ≤ k := by omega
  have hσk : ((k + 1 : ℕ) : WithTop ℤ) ≤ D.v (σ • D.ϖ - D.ϖ) := by rw [← hz]; rfl
  obtain ⟨-, hB⟩ := v_pow_smul_sub D hσk hk (orderOf σ)
  rw [pow_orderOf_eq_one, one_smul, sub_self, zero_sub, AddValuation.map_neg, AddValuation.map_mul,
    v_natCast_eq_zero D hm, zero_add, ← hz] at hB
  rw [← WithTop.coe_natCast] at hB
  have : ((k + 2 : ℕ) : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := WithTop.coe_le_coe.mp hB
  omega

/-- **Wild ramification groups are `p`-groups**: `l ∤ |G_u|` for `u ≥ 1` and primes `l ≠ p`. -/
theorem not_dvd_card_lower [Finite G] {p : ℕ} [Fact p.Prime] [CharP L p] {u : ℕ} (hu : 1 ≤ u) {l : ℕ}
    (hl : l.Prime) (hlp : l ≠ p) : ¬ l ∣ Nat.card (D.ramFn.lower u) := by
  intro hd
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hd
  have hox : orderOf (x : G) = l := by rw [Subgroup.orderOf_coe, hx]
  have hx1 : (x : G) ≠ 1 := fun h => by rw [h, orderOf_one] at hox; exact hl.one_lt.ne' hox.symm
  have hmem : (x : G) ∈ D.ramFn.lower 1 := by
    have h := (RamFn.mem_lower D.ramFn).mp x.2
    exact (RamFn.mem_lower D.ramFn).mpr (le_trans (by exact_mod_cast (by omega : 1 + 1 ≤ u + 1)) h)
  have hp := dvd_orderOf_of_mem_lower D (p := p) hmem hx1
  rw [hox, Nat.prime_dvd_prime_iff_eq (Fact.out) hl] at hp
  exact hlp hp.symm

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_GOSI =====
section

/-!
# S4-GOS-C, part GOSI: the integer Grothendieck-Ogg-Shafarevich identity on the concrete cover

`K = RatFunc 𝔽_q`, `G = Gal(M_f/K) ≅ Gf` (via `iotaG`), `τ` a representation of `Gf` on a finite `ℤ/l`-module `M`
(`l ∤ q`). With `χ(τ) = Σ_i (-1)^i dim (PC i ⊗ M)_{Gf}`, `W_Q(j) = G_{Q,j+1}` and `d_{Q,j} = dim M_{ι W_Q(j)}`:
**`gos_int`**: `|Gf| χ(τ) = |G| χ_c(K) dim M - Σ_{Q | ∞} Σ_{j < J} deg Q |W_Q(j)| (dim M - d_{Q,j})` in `ℤ`,
from Brauer's formula at every level `ℤ/l^n` (`brauer_lev`), `chiPC_eq_Phi`, `Φ = Σ_Q Σ_j [· ∈ W_Q(j)] deg Q`,
`Σ Φ = |G| χ_c(K)` and the wild groups being `p`-groups.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CP4a Representation Lefschetz

section Transfer

variable {G Gf : Type*} [Group G] [Group Gf] [Fintype G] {Λ : Type*} [AddCommMonoid Λ]

theorem sum_finset_comp_map (e : G →* Gf) (he : Function.Injective e) (H : Subgroup G) [Fintype (H.map e)]
    (s : Finset G) (hs : ∀ g, g ∈ s ↔ g ∈ H) (f : Gf → Λ) :
    ∑ g ∈ s, f (e g) = ∑ h : H.map e, f h := by
  classical
  rw [Finset.sum_subtype s hs (fun g => f (e g))]
  exact Fintype.sum_equiv (H.equivMapOfInjective e he) _ _
    (fun x => congrArg f (Subgroup.coe_equivMapOfInjective_apply H e he x).symm)

theorem card_finset_eq_card_map (e : G →* Gf) (he : Function.Injective e) (H : Subgroup G) [Fintype (H.map e)]
    (s : Finset G) (hs : ∀ g, g ∈ s ↔ g ∈ H) : s.card = Fintype.card (H.map e) := by
  rw [Finset.card_eq_sum_ones, Fintype.card_eq_sum_ones]
  exact sum_finset_comp_map e he H s hs (fun _ => 1)

theorem cast_natCast_mul_eq {Λ : Type*} [CommRing Λ] {A : ℕ} {X B : ℤ} (h : (A : Λ) * (X : Λ) = (B : Λ)) :
    (((A : ℤ) * X : ℤ) : Λ) = (B : Λ) := by
  rw [Int.cast_mul, Int.cast_natCast]
  exact h

end Transfer

section GOSI

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {p e : ℕ} [Fact p.Prime] [CharP (RatFunc Fq) p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {Mf : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq))} [FiniteDimensional (RatFunc Fq) Mf] [IsGalois (RatFunc Fq) Mf] {Gf : Type} [Group Gf] [Fintype Gf]

theorem finrank_coinvariants_bot {l : ℕ} {M : Type} [AddCommGroup M] [Module (ZMod (l ^ 1)) M]
    (τ : Representation (ZMod (l ^ 1)) Gf M) :
    Module.finrank (ZMod (l ^ 1)) (Coinvariants (τ.comp (⊥ : Subgroup Gf).subtype)) =
      Module.finrank (ZMod (l ^ 1)) M := by
  have hker : Coinvariants.ker (τ.comp (⊥ : Subgroup Gf).subtype) = ⊥ := by
    rw [Representation.Coinvariants.ker, Submodule.span_eq_bot]
    rintro _ ⟨⟨g, x⟩, rfl⟩
    show τ (g : Gf) x - x = 0
    rw [Subgroup.mem_bot.mp g.2, map_one, Module.End.one_apply, sub_self]
  exact (Submodule.quotEquivOfEqBot _ hker).finrank_eq

end GOSI

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_C_MASCH =====
section

/-!
# S4-GOS-C, part MASCH: coinvariants and invariants for groups of invertible order

For a finite group `G` with `|G|` invertible in the field `k`: the averaging map kills exactly the coinvariant kernel
(`coinvariantsKer_eq_ker_averageMap`), so **`finrank_coinvariants_eq_invariants`**: `dim V_G = dim V^G`.
Also `invariants_comp_map`: the invariants of `H ≤ G` acting through `f : G →* Gf` are those of `f(H)`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.GOS

open Representation Module

section Masch

variable {k : Type*} [Field k] {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

theorem averageMap_comp_apply [Invertible (Fintype.card G : k)] (g : G) (v : V) :
    ρ.averageMap (ρ g v) = ρ.averageMap v := by
  rw [averageMap, ← asAlgebraHom_single_one, ← Module.End.mul_apply, ← map_mul (asAlgebraHom ρ),
    GroupAlgebra.mul_average_right]

theorem averageMap_eq_smul_sum [Invertible (Fintype.card G : k)] (v : V) :
    ρ.averageMap v = ⅟(Fintype.card G : k) • ∑ g : G, ρ g v := by
  rw [averageMap, GroupAlgebra.average, map_smul, map_sum, LinearMap.smul_apply,
    LinearMap.sum_apply]
  simp only [asAlgebraHom_of]

theorem mk_averageMap [Invertible (Fintype.card G : k)] (v : V) :
    Coinvariants.mk ρ (ρ.averageMap v) = Coinvariants.mk ρ v := by
  rw [averageMap_eq_smul_sum, map_smul, map_sum]
  simp only [Coinvariants.mk_self_apply, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, invOf_mul_self, one_smul]

theorem coinvariantsKer_eq_ker_averageMap [Invertible (Fintype.card G : k)] :
    Coinvariants.ker ρ = LinearMap.ker ρ.averageMap := by
  apply le_antisymm
  · rw [Coinvariants.ker, Submodule.span_le]
    rintro _ ⟨⟨g, x⟩, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, averageMap_comp_apply, sub_self]
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    have h := mk_averageMap ρ v
    rw [hv, map_zero] at h
    exact (Coinvariants.mk_eq_zero ρ).1 h.symm

theorem range_averageMap [Invertible (Fintype.card G : k)] :
    LinearMap.range ρ.averageMap = ρ.invariants := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact ρ.averageMap_invariant v
  · intro v hv
    exact ⟨v, ρ.averageMap_id v hv⟩

/-- **Maschke-type dimension count**: `dim V_G = dim V^G` when `|G|` is invertible. -/
theorem finrank_coinvariants_eq_invariants [FiniteDimensional k V] [Invertible (Fintype.card G : k)] :
    finrank k (Coinvariants ρ) = finrank k ρ.invariants := by
  have h1 : finrank k (Coinvariants ρ) + finrank k (Coinvariants.ker ρ) = finrank k V :=
    Submodule.finrank_quotient_add_finrank _
  have h2 := LinearMap.finrank_range_add_finrank_ker ρ.averageMap
  rw [coinvariantsKer_eq_ker_averageMap] at h1
  rw [range_averageMap] at h2
  omega

end Masch

section Sub

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] {G Gf : Type*} [Group G] [Group Gf]

/-- `dim (V|_H)_H = dim (V|_H)^H` for a subgroup of order invertible in `k`. -/
theorem finrank_coinv_subgroup [FiniteDimensional k V] (τ : Representation k Gf V) (H : Subgroup Gf)
    [Fintype H] (hH : (Fintype.card H : k) ≠ 0) :
    finrank k (Coinvariants (τ.comp H.subtype)) = finrank k (Representation.invariants (τ.comp H.subtype)) := by
  have := invertibleOfNonzero hH
  exact finrank_coinvariants_eq_invariants _

theorem invariants_comp_map (τ : Representation k Gf V) (f : G →* Gf) (H : Subgroup G) :
    Representation.invariants ((τ.comp f).comp H.subtype) =
      Representation.invariants (τ.comp (H.map f).subtype) := by
  ext v
  rw [mem_invariants, mem_invariants]
  constructor
  · intro h g
    obtain ⟨y, x, hx, rfl⟩ := g
    exact h ⟨x, hx⟩
  · intro h x
    exact h ⟨f x, Subgroup.mem_map_of_mem f x.2⟩

end Sub

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_Swan_GlobPc =====
section

/-!
# S4-Swan (K2), part 20: Swan conductors and breaks at `∞` do not depend on the place

If `τ • P = P'` for two height-one primes of a Dedekind domain with a Galois action, then
`v_{P'}(τ x) = v_P(x)` (`adicAdd_smul_eq`), conjugation `σ ↦ τ⁻¹ σ τ` maps the inertia group of `P'` onto that
of `P` (`conjInertia`), and the two inertia local data form a `LocData.Tower` along `τ` with trivial kernel
(`conjTower`). Isomorphic representations have equal Swan conductors and breaks (`RamFn.swan_equiv`,
`RamFn.allBrk_equiv`), so the Swan conductor and breaks of `ρ` restricted to inertia agree at `P` and `P'`.
At `∞` the base `O_∞` is local, so the cover group acts transitively on the places over `∞`
(`GalCover.exists_smul_inf`), giving `GalCover.swanInf_eq` and `GalCover.allBrkInf_eq`.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open scoped Pointwise

namespace RamanujanPetersson

namespace Swan

section AdicConj

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {L : Type*} [Field L] [Algebra S L]
  [IsFractionRing S L] {G : Type*} [Group G] [MulSemiringAction G S] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
include hc

end AdicConj

section ConjInertia

variable {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]

theorem conj_mem_inertia (τ : G) {Q Q' : Ideal S} (h : τ • Q = Q') {σ : G} (hσ : σ ∈ Q'.inertia G) :
    τ⁻¹ * σ * τ ∈ Q.inertia G := by
  rw [Ideal.inertia, AddSubgroup.mem_inertia] at hσ ⊢
  intro x
  have hx : σ • τ • x - τ • x ∈ τ • Q := by rw [h]; exact hσ (τ • x)
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, inv_smul_smul] at hx
  rw [mul_smul, mul_smul]
  exact hx

/-- Conjugation `σ ↦ τ⁻¹ σ τ` from the inertia group of `τ • Q` to the inertia group of `Q`. -/
def conjInertia (τ : G) {Q Q' : Ideal S} (h : τ • Q = Q') : Q'.inertia G →* Q.inertia G where
  toFun σ := ⟨τ⁻¹ * σ * τ, conj_mem_inertia τ h σ.2⟩
  map_one' := Subtype.ext (by show τ⁻¹ * 1 * τ = 1; group)
  map_mul' a b := Subtype.ext (by show τ⁻¹ * ((a : G) * b) * τ = (τ⁻¹ * a * τ) * (τ⁻¹ * b * τ); group)

theorem conjInertia_coe (τ : G) {Q Q' : Ideal S} (h : τ • Q = Q') (σ : Q'.inertia G) :
    (conjInertia τ h σ : G) = τ⁻¹ * σ * τ := rfl

theorem conjInertia_surjective (τ : G) {Q Q' : Ideal S} (h : τ • Q = Q') :
    Function.Surjective (conjInertia τ h) := by
  intro g
  have h' : τ⁻¹ • Q' = Q := by rw [← h, inv_smul_smul]
  have hm := conj_mem_inertia τ⁻¹ h' g.2
  rw [inv_inv] at hm
  exact ⟨⟨_, hm⟩, Subtype.ext (by show τ⁻¹ * (τ * (g : G) * τ⁻¹) * τ = g; group)⟩

theorem conjInertia_injective (τ : G) {Q Q' : Ideal S} (h : τ • Q = Q') :
    Function.Injective (conjInertia τ h) := by
  intro a b hab
  have : τ⁻¹ * (a : G) * τ = τ⁻¹ * b * τ := congrArg Subtype.val hab
  exact Subtype.ext (by simpa using this)

theorem card_ker_conjInertia (τ : G) {Q Q' : Ideal S} (h : τ • Q = Q') [Fintype (conjInertia τ h).ker] :
    Fintype.card (conjInertia τ h).ker = 1 := by
  rw [← Nat.card_eq_fintype_card, Subgroup.card_eq_one, MonoidHom.ker_eq_bot_iff]
  exact conjInertia_injective τ h

end ConjInertia

section ConjTower

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S] {G : Type*}
  [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (τ : G) {P P' : HeightOneSpectrum S} (h : τ • P.asIdeal = P'.asIdeal)
  [Finite (S ⧸ P.asIdeal)] [Finite (S ⧸ P'.asIdeal)]

end ConjTower

section RepEquiv

variable {G : Type*} [Group G] {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  (ρ₁ ρ₂ : Representation k G V) (e : V ≃ₗ[k] V) (he : ∀ g v, ρ₁ g (e v) = e (ρ₂ g v))
include he

theorem fixd_map_equiv (H : Subgroup G) : (fixd ρ₂ H).map (e : V →ₗ[k] V) = fixd ρ₁ H := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    refine (mem_fixd ρ₁).2 fun σ hσ => ?_
    rw [LinearEquiv.coe_coe, he, (mem_fixd ρ₂).1 hv σ hσ]
  · intro w hw
    refine Submodule.mem_map.2 ⟨e.symm w, (mem_fixd ρ₂).2 fun σ hσ => ?_, by simp⟩
    apply e.injective
    rw [← he, e.apply_symm_apply, (mem_fixd ρ₁).1 hw σ hσ]

theorem cod_equiv (H : Subgroup G) : cod ρ₁ H = cod ρ₂ H := by
  rw [cod, cod, ← fixd_map_equiv ρ₁ ρ₂ e he H, LinearEquiv.finrank_map_eq]

namespace RamFn

variable (R : RamFn G)

/-- Isomorphic representations have the same Swan conductor. -/
theorem swan_equiv [Fintype G] : R.swan ρ₁ = R.swan ρ₂ := by
  unfold swan
  exact Finset.sum_congr rfl fun u _ => by rw [cod_equiv ρ₁ ρ₂ e he]

end RamFn

end RepEquiv

section ConjRep

variable {G : Type*} [Group G] {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- `ρ τ` as a linear automorphism. -/
def repEquiv (τ : G) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinearMap (ρ τ) (ρ τ⁻¹) (LinearMap.ext fun v => ρ.self_inv_apply τ v)
    (LinearMap.ext fun v => ρ.inv_self_apply τ v)

variable {S : Type*} [CommRing S] [MulSemiringAction G S]

/-- `ρ` on the inertia of `τ • Q` is conjugate (by `ρ τ`) to `ρ` on the inertia of `Q` pulled back along
conjugation. -/
theorem conj_rep_intertwine (τ : G) {Q Q' : Ideal S} (h : τ • Q = Q') (g : Q'.inertia G) (v : V) :
    (ρ.comp (Q'.inertia G).subtype) g (repEquiv ρ τ v) =
      repEquiv ρ τ (((ρ.comp (Q.inertia G).subtype).comp (conjInertia τ h)) g v) := by
  show ρ (g : G) (ρ τ v) = ρ τ (ρ (τ⁻¹ * (g : G) * τ) v)
  rw [show (τ⁻¹ * (g : G) * τ : G) = τ⁻¹ * ((g : G) * τ) by group, map_mul, Module.End.mul_apply,
    ρ.self_inv_apply, map_mul, Module.End.mul_apply]

end ConjRep

section ConjSwan

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S] {G : Type*}
  [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (τ : G) {P P' : HeightOneSpectrum S} (h : τ • P.asIdeal = P'.asIdeal)
  [Finite (S ⧸ P.asIdeal)] [Finite (S ⧸ P'.asIdeal)]
  [Fintype (P.asIdeal.inertia G)] [Fintype (P'.asIdeal.inertia G)]
  {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

end ConjSwan

end Swan

namespace GalCover

section Place

variable {A : Type} [CommRing A] [IsDomain A]
variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] [Algebra A (RatFunc Fq)]
  [IsFractionRing A (RatFunc Fq)]
variable (L : Type) [Field L] [Algebra (RatFunc Fq) L] [Algebra A L] [IsScalarTower A (RatFunc Fq) L]
variable [FiniteDimensional (RatFunc Fq) L] [Algebra.IsSeparable (RatFunc Fq) L] [Fintype Fq]

end Place

end GalCover

end RamanujanPetersson

end

end

-- ===== S4.Def_RP_GOS_C_GOSF2 =====
section

/-!
# S4-GOS-C, part GOSF2: Grothendieck-Ogg-Shafarevich on `𝔸¹`

`K = 𝔽_q(x)`, `M_f/K` the trivialising cover with group `G ≅ Gf`, `τ` a representation of `Gf` on a finite
`ℤ/l`-module `M` (`l ∤ q`). From `gos_int`, `χ = h²_c - h¹_c` (`chi_eq_h2c_sub_h1c`), `|I_Q| Sw_Q = Σ_j ...`
(`card_mul_swanQ`), the places over `∞` being conjugate (one place of `K` over `∞`) and
`Σ_Q deg Q |I_Q| = |G|` (`χ_c(𝔸¹) = 1`, `chiC_rat`):
**`gos_A1`**: `h²_c(M) - h¹_c(M) = dim M - Sw_{Q₀}(M)` for any place `Q₀ | ∞` of `M_f`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial IsDedekindDomain
open scoped Pointwise

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CP4a Representation Lefschetz

/-- The algebra closing `gos_A1`. -/
theorem gos_alg {X chi S : ℤ} {h2 h1 dM cG cGf : ℕ} {sw : ℚ} (hE : X = (h2 : ℤ) - h1)
    (hG : (cGf : ℤ) * X = (cG : ℤ) * chi * dM - S) (hchi : chi = 1) (hS : (S : ℚ) = sw * cG)
    (hc : cGf = cG) (hpos : 0 < cG) : ((h2 : ℚ) - h1) = dM - sw := by
  subst hchi hE
  rw [hc] at hG
  have hG' := congrArg (Int.cast : ℤ → ℚ) hG
  push_cast at hG'
  rw [hS] at hG'
  have hc0 : (cG : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  apply mul_left_cancel₀ hc0
  linear_combination hG'

section GOSF2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {p e : ℕ} [Fact p.Prime] [CharP (RatFunc Fq) p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {Mf : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq))} [FiniteDimensional (RatFunc Fq) Mf] [IsGalois (RatFunc Fq) Mf] {Gf : Type} [Group Gf] [Fintype Gf]

end GOSF2

end

end RamanujanPetersson.GOS


end


