-- Prove2me | Definitions.Def_RPLib_S4_LefPack01
-- name    : RPLib_S4_LefPack01
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T18:21:39.483467+00:00
-- url     : https://prove2.me/theorems/49725b20-a7c1-4c7f-becc-24478f1ac904
-- title:
--   Lefschetz trace formula library (Grothendieck–Lefschetz trace formula mod ℓⁿ on curves over finite fields), part 1 of 32
-- statement:
--   Part 1 of 32 of the Lefschetz trace formula library: the following library modules, in dependency order.
--
--   * `Def_RP_CP4a_BdS`: S4-CP4a, part f3: the boundary data over `∞` exist, finite and nonempty
--   * `Def_RP_CP4a_HypA`: S4-CP4a, part g1: the function field of `y² = x⁵ + 1`
--   * `Def_RP_CP4a_HypB`: S4-CP4a, part g2: the integral closure of `Fq[x]` in the function field of `y² = x⁵ + 1`
--   * `Def_RP_CoreB_Pert`: Core B, O7: `charpoly(M) = P₀` from the norm identity for `deg F ≠ 0` only
--   * `Def_RP_Lefschetz_OinfInt`: S4-Lefschetz L4b, part 1: `O_∞(k)` is integral over `O_∞(𝔽_q)` for a finite extension `k / 𝔽_q`
--   * `Def_RP_Lefschetz_BlockGrp`: S4-Lefschetz, L3d3a: the block subgroup `H_ω`
--
--   **Formalization note.** Library package of a formalization of the Grothendieck–Lefschetz trace formula modulo $\ell^n$ for a lisse sheaf of free $\mathbb Z/\ell^n$-modules on an affine curve over a finite field, on the compactly supported cochain complex of the geometric fundamental group. The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Formule de Lefschetz et rationalité des fonctions L, Séminaire Bourbaki, exposé 279 (1964/65); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Rapport sur la formule des traces »; J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §13

import Mathlib
import Definitions.Def_RPLib_S4_CDPack14e
import Definitions.Def_RPLib_S4_CDPack15c
import Definitions.Def_RPLib_S4_CDPack70
import Definitions.Def_RPLib_S3_PlacesA
import Definitions.Def_RPLib_S4_CurveCohCurve

/-!
# Lefschetz trace formula library package, part 1 of 32

Library modules of the formalization of the Grothendieck-Lefschetz trace formula mod `l^n` for lisse sheaves on an
affine curve over a finite field (`RamanujanPetersson.Lefschetz.lefschetz_main`). Each module below is copied
verbatim (import lines removed) inside its own `section` ... `end`:

* `Def_RP_CP4a_BdS`: S4-CP4a, part f3: the boundary data over `∞` exist, finite and nonempty
* `Def_RP_CP4a_HypA`: S4-CP4a, part g1: the function field of `y² = x⁵ + 1`
* `Def_RP_CP4a_HypB`: S4-CP4a, part g2: the integral closure of `Fq[x]` in the function field of `y² = x⁵ + 1`
* `Def_RP_CoreB_Pert`: Core B, O7: `charpoly(M) = P₀` from the norm identity for `deg F ≠ 0` only
* `Def_RP_Lefschetz_OinfInt`: S4-Lefschetz L4b, part 1: `O_∞(k)` is integral over `O_∞(𝔽_q)` for a finite extension `k / 𝔽_q`
* `Def_RP_Lefschetz_BlockGrp`: S4-Lefschetz, L3d3a: the block subgroup `H_ω`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CP4a_BdS =====
section

/-!
# S4-CP4a, part f3: the boundary data over `∞` exist, finite and nonempty

* `bdrySetoid`, `BdryS`, `bdryData`: for any chart `R0`, the `π₁^geo`-orbits of nonzero primes of the pro-chart
  with chosen representatives form a `BdryData` whose `B` is exactly `IsBdryPrime` (`bdryData_B`).
* For `R0 = Rinf` of a function field `F/𝔽_q`: `piInf_mem` (`π_∞` lies under every boundary prime),
  `bres_pow_card` (all residues lie in `𝔽_{q^M}`, `M = (#Rinf/(π_∞))!`), `finite_bdry` (any boundary data over `∞`
  has finitely many points: `s ↦ sres s` factors through the finite ring `Rinf/(π_∞)` into `𝔽_{q^M}`) and
  `nonempty_bdry` (lying over a place at `∞`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer GalCover

noncomputable section

section Orb

variable {G X : Type*} [Group G] [MulAction G X] (H : Subgroup G) (P : X → Prop)

/-- The orbit relation of a subgroup `H` on a subtype `{x // P x}`. -/
def orbSetoid : Setoid {x // P x} where
  r x y := ∃ g ∈ H, y.1 = g • x.1
  iseqv := {
    refl := fun x => ⟨1, H.one_mem, (one_smul G x.1).symm⟩
    symm := fun {x y} ⟨g, hg, h⟩ => ⟨g⁻¹, H.inv_mem hg, by rw [h, inv_smul_smul]⟩
    trans := fun {x y z} ⟨g, hg, h⟩ ⟨g', hg', h'⟩ => ⟨g' * g, H.mul_mem hg' hg, by rw [h', h, mul_smul]⟩ }

theorem orbSetoid_r {x y : {x // P x}} : (orbSetoid H P).r x y ↔ ∃ g ∈ H, y.1 = g • x.1 := Iff.rfl

end Orb

section Setoid

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (q : ℕ)
  (R0 : Type) [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]

set_option synthInstance.maxHeartbeats 200000 in
/-- Two boundary primes are equivalent iff they lie in one `π₁^geo`-orbit. -/
abbrev bdrySetoid : Setoid {Q : Ideal (proChart A K R0) // IsBdryPrime A K R0 Q} :=
  orbSetoid (X := Ideal (proChart A K R0)) (pi1geo A K q) (IsBdryPrime A K R0)

/-- The geometric boundary points over the chart `R0`. -/
def BdryS : Type := Quotient (bdrySetoid A K q R0)

set_option synthInstance.maxHeartbeats 200000 in
/-- The canonical boundary data: all nonzero primes, one representative per `π₁^geo`-orbit. -/
def bdryData : BdryData A K q R0 (BdryS A K q R0) where
  B := IsBdryPrime A K R0
  B_smul := isBdryPrime_smul A K R0
  P s := (Quotient.out s).1
  mem s := (Quotient.out s).2
  cover Q hQ := by
    obtain ⟨g, hg, h⟩ := (orbSetoid_r _ _).1 (Quotient.mk_out (s := bdrySetoid A K q R0) ⟨Q, hQ⟩)
    exact ⟨Quotient.mk _ ⟨Q, hQ⟩, g, hg, h⟩
  disj s t g hg h := Quotient.out_equiv_out.1 ((orbSetoid_r _ _).2 ⟨g, hg, h⟩)

theorem bdryData_B (Q : Ideal (proChart A K R0)) : (bdryData A K q R0).B Q ↔ IsBdryPrime A K R0 Q := Iff.rfl

end Setoid

section Fin

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

set_option synthInstance.maxHeartbeats 200000 in
theorem under_ne_bot (Q : Ideal (proChart (Rfin Fq F) F (Rinf Fq F)))
    (hQ : IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) : Q.under (Rinf Fq F) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ.2
  exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)

set_option synthInstance.maxHeartbeats 200000 in
/-- `π_∞` lies under every boundary prime over `∞`. -/
theorem piInf_mem (Q : Ideal (proChart (Rfin Fq F) F (Rinf Fq F)))
    (hQ : IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) :
    algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq) ∈ Q.under (Rinf Fq F) := by
  have := hQ.1
  have hne' : (Q.under (Rinf Fq F)).under (Oinf Fq) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (under_ne_bot Q hQ)
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  have hmax : ((Q.under (Rinf Fq F)).under (Oinf Fq)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne'
  have hpi : piInf Fq ∈ IsLocalRing.maximalIdeal (Oinf Fq) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (span_piInf_isMaximal Fq).ne_top (Ideal.span_singleton_eq_top.2 hu)
  rw [← IsLocalRing.eq_maximalIdeal hmax] at hpi
  exact hpi

include hq he hζc in
set_option synthInstance.maxHeartbeats 200000 in
/-- All residues at boundary points over `∞` lie in `𝔽_{q^M}`, `M = (#Rinf/(π_∞))!`. -/
theorem bres_pow_card (Q : Ideal (proChart (Rfin Fq F) F (Rinf Fq F)))
    (hQ : IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (r : Rinf Fq F) :
    bres he hζc (good_inf hq) Q hQ r ^ (Fintype.card Fq ^
      (Nat.card (Rinf Fq F ⧸ Ideal.span {algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq)})).factorial) =
      bres he hζc (good_inf hq) Q hQ r := by
  set r0 := algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq)
  set Qs := Q.under (Rinf Fq F)
  have := hQ.1
  haveI hmax : Qs.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (under_ne_bot Q hQ)
  obtain ⟨hfin, d, hd⟩ := good_inf hq Q hQ
  letI : Field (Rinf Fq F ⧸ Qs) := Ideal.Quotient.field Qs
  letI : Fintype (Rinf Fq F ⧸ Qs) := Fintype.ofFinite _
  have hr0 : r0 ≠ 0 := fun h =>
    piInf_ne_zero Fq ((algebraMap_Oinf_Rinf_injective Fq F) (by rw [map_zero]; exact h))
  haveI : Finite (Rinf Fq F ⧸ Ideal.span {r0}) := FiniteQuot.finite r0 hr0
  have hle : Nat.card (Rinf Fq F ⧸ Qs) ≤ Nat.card (Rinf Fq F ⧸ Ideal.span {r0}) :=
    Nat.card_le_card_of_surjective _
      (Ideal.Quotient.factor_surjective ((Ideal.span_singleton_le_iff_mem _).2 (piInf_mem Q hQ)))
  have hcard : Fintype.card (Rinf Fq F ⧸ Qs) = Fintype.card Fq ^ d := by
    rw [← Nat.card_eq_fintype_card, hd, hq]
  have hq1 : 1 < Fintype.card Fq := Fintype.one_lt_card
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · have h1 := Fintype.one_lt_card (α := Rinf Fq F ⧸ Qs)
      rw [hcard, h, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h
  have hdM : d ∣ (Nat.card (Rinf Fq F ⧸ Ideal.span {r0})).factorial := by
    apply Nat.dvd_factorial hd0
    have h2 : d < Fintype.card Fq ^ d := Nat.lt_pow_self hq1
    rw [Nat.card_eq_fintype_card (α := Rinf Fq F ⧸ Qs), hcard] at hle
    exact (h2.trans_le hle).le
  obtain ⟨k, hk⟩ := hdM
  have hfr : Ideal.Quotient.mk Qs r ^ (Fintype.card Fq ^ d) = Ideal.Quotient.mk Qs r := by
    rw [← hcard]
    exact FiniteField.pow_card _
  have hmem : r ^ (Fintype.card Fq ^ d) - r ∈ Qs := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hfr, sub_self]
  have hb : bres he hζc (good_inf hq) Q hQ r ^ (Fintype.card Fq ^ d) = bres he hζc (good_inf hq) Q hQ r := by
    have h3 := (bres_ker he hζc (good_inf hq) Q hQ _).2 hmem
    rwa [map_sub, map_pow, sub_eq_zero] at h3
  rw [hk, pow_mul]
  exact pow_pow_iter hb k

include hq he hζc in
set_option synthInstance.maxHeartbeats 200000 in
/-- **Finitely many boundary points over `∞`.** -/
theorem finite_bdry {S : Type} (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) : Finite S := by
  set r0 := algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq)
  set M := (Nat.card (Rinf Fq F ⧸ Ideal.span {r0})).factorial
  have hM : 0 < M := Nat.factorial_pos _
  have hr0 : r0 ≠ 0 := fun h =>
    piInf_ne_zero Fq ((algebraMap_Oinf_Rinf_injective Fq F) (by rw [map_zero]; exact h))
  haveI : Finite (Rinf Fq F ⧸ Ideal.span {r0}) := FiniteQuot.finite r0 hr0
  obtain ⟨z, hz⟩ := exists_prim_level hq hζc M hM
  have hc := card_levelField hM hz
  have : Finite (levelField Fq (maxUnram (Rfin Fq F) F) M) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ Fintype.card_ne_zero)
  have hpow : ∀ s r, sres he hζc (good_inf hq) D hDB s r ∈ levelField Fq (maxUnram (Rfin Fq F) F) M :=
    fun s r => mem_levelField.2 (bres_pow_card hq he hζc _ _ r)
  have hker : ∀ s, sres he hζc (good_inf hq) D hDB s r0 = 0 := fun s =>
    (bres_ker he hζc (good_inf hq) _ _ r0).2 (piInf_mem _ ((hDB _).1 (D.mem s)))
  let g : S → (Rinf Fq F ⧸ Ideal.span {r0} → levelField Fq (maxUnram (Rfin Fq F) F) M) := fun s x =>
    ⟨sres he hζc (good_inf hq) D hDB s (Function.surjInv Ideal.Quotient.mk_surjective x), hpow s _⟩
  refine Finite.of_injective g fun s t hst => ?_
  apply sres_injective he hζc (good_inf hq) D hDB hq
  refine RingHom.ext fun r => ?_
  have hs := Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {r0})) (Ideal.Quotient.mk _ r)
  obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hs)
  have e1 : ∀ u, sres he hζc (good_inf hq) D hDB u r = sres he hζc (good_inf hq) D hDB u
      (Function.surjInv Ideal.Quotient.mk_surjective (Ideal.Quotient.mk (Ideal.span {r0}) r)) := by
    intro u
    have h0 := congrArg (sres he hζc (good_inf hq) D hDB u) hc'
    rw [map_mul, hker, mul_zero, map_sub] at h0
    exact (sub_eq_zero.1 h0.symm).symm
  rw [e1 s, e1 t]
  have h5 : ((g s (Ideal.Quotient.mk _ r) : levelField Fq (maxUnram (Rfin Fq F) F) M) : maxUnram (Rfin Fq F) F) =
      ((g t (Ideal.Quotient.mk _ r) : levelField Fq (maxUnram (Rfin Fq F) F) M) : maxUnram (Rfin Fq F) F) :=
    congrArg (fun x : levelField Fq (maxUnram (Rfin Fq F) F) M => (x : maxUnram (Rfin Fq F) F)) (congrFun hst _)
  exact h5

set_option synthInstance.maxHeartbeats 200000 in
/-- **Some boundary point over `∞` exists.** -/
theorem nonempty_bdry {S : Type} (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) : Nonempty S := by
  obtain ⟨P0⟩ := nonempty_infPlace Fq F
  have := P0.isPrime
  have hinj : Function.Injective (Algebra.ofId (Rinf Fq F) (proChart (Rfin Fq F) F (Rinf Fq F))) :=
    algebraMap_proChart_injective (A := Rfin Fq F) (K := F) (R0 := Rinf Fq F)
  obtain ⟨Q, hQ, hQP⟩ := exists_prime_comap_eq (R0 := Rinf Fq F) (R := Rinf Fq F)
    (S := proChart (Rfin Fq F) F (Rinf Fq F)) (Algebra.ofId (Rinf Fq F) (proChart (Rfin Fq F) F (Rinf Fq F))) hinj P0.asIdeal
  have hQB : IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q := by
    refine ⟨hQ, fun h => P0.ne_bot ?_⟩
    rw [← hQP, h]
    exact Ideal.comap_bot_of_injective _ hinj
  obtain ⟨s, -⟩ := D.cover Q ((hDB Q).2 hQB)
  exact ⟨s⟩

end Fin

end

end RamanujanPetersson.CP4a

end

-- ===== S4.Def_RP_CP4a_HypA =====
section

/-!
# S4-CP4a, part g1: the function field of `y² = x⁵ + 1`

`HypF Fq = Fq(x)[Y]/(Y² - (x⁵ + 1))`, the function field of the genus-2 curve `y² = x⁵ + 1` over a finite
field `Fq`. Here:
* `irreducible_hypPoly` (any characteristic: `x⁵ + 1` has odd degree, so it is not a square in `Fq(x)`),
  hence `HypF Fq` is a field, finite of degree `2` over `Fq(x)` (`finrank_hypF`), a `FunctionField`;
* separable over `Fq(x)` when `2 ≠ 0` in `Fq` (instance under `Fact ((2 : Fq) ≠ 0)`); `CharP` from `Fq`;
* `hy`: `y = root` satisfies `y² = x⁵ + 1`; every element is `a + b y` (`exists_coords`), uniquely (`coords_eq_zero`);
* `conjHom`: the `Fq(x)`-automorphism `y ↦ -y`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a.Hyp2

noncomputable section

variable (Fq : Type) [Field Fq]

/-- `x⁵ + 1 ∈ Fq[x]`. -/
abbrev f0 : Fq[X] := X ^ 5 + 1

/-- `x⁵ + 1 ∈ Fq(x)`. -/
abbrev f0K : RatFunc Fq := algebraMap Fq[X] (RatFunc Fq) (f0 Fq)

/-- The defining polynomial `Y² - (x⁵ + 1)` over `Fq(x)`. -/
abbrev hypPoly : (RatFunc Fq)[X] := X ^ 2 - C (f0K Fq)

theorem natDegree_f0 : (f0 Fq).natDegree = 5 := by
  have h : f0 Fq = X ^ 5 + C 1 := by rw [C_1]
  rw [h, natDegree_X_pow_add_C]

theorem f0_ne_zero : f0 Fq ≠ 0 := by
  intro h
  have := natDegree_f0 Fq
  rw [h, natDegree_zero] at this
  omega

theorem f0K_ne_zero : f0K Fq ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))]
  exact f0_ne_zero Fq

/-- `x⁵ + 1` is not a square in `Fq(x)` (odd degree). -/
theorem not_sq (b : RatFunc Fq) : b ^ 2 ≠ f0K Fq := by
  intro h
  have hb : b ≠ 0 := by
    rintro rfl
    apply f0K_ne_zero Fq
    rw [← h]
    ring
  have h1 := congrArg RatFunc.intDegree h
  rw [pow_two, RatFunc.intDegree_mul hb hb, RatFunc.intDegree_polynomial, natDegree_f0] at h1
  omega

theorem irreducible_hypPoly : Irreducible (hypPoly Fq) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two (not_sq Fq)

instance fact_irreducible : Fact (Irreducible (hypPoly Fq)) := ⟨irreducible_hypPoly Fq⟩

theorem monic_hypPoly : (hypPoly Fq).Monic := monic_X_pow_sub_C _ two_ne_zero

theorem hypPoly_ne_zero : hypPoly Fq ≠ 0 := (monic_hypPoly Fq).ne_zero

theorem natDegree_hypPoly : (hypPoly Fq).natDegree = 2 := natDegree_X_pow_sub_C

/-- The function field of `y² = x⁵ + 1`. -/
abbrev HypF : Type := AdjoinRoot (hypPoly Fq)

instance finiteDimensional_hypF : FiniteDimensional (RatFunc Fq) (HypF Fq) :=
  (AdjoinRoot.powerBasis (hypPoly_ne_zero Fq)).finite

instance functionField_hypF : FunctionField Fq (HypF Fq) := finiteDimensional_hypF Fq

theorem finrank_hypF : Module.finrank (RatFunc Fq) (HypF Fq) = 2 := by
  rw [(AdjoinRoot.powerBasis (hypPoly_ne_zero Fq)).finrank, AdjoinRoot.powerBasis_dim, natDegree_hypPoly]

theorem two_ne_zero_ratFunc (h2 : (2 : Fq) ≠ 0) : (2 : RatFunc Fq) ≠ 0 := by
  intro h
  apply h2
  apply (algebraMap Fq (RatFunc Fq)).injective
  rw [map_ofNat, h, map_zero]

theorem isSeparable_root (h2 : (2 : Fq) ≠ 0) :
    IsSeparable (RatFunc Fq) (AdjoinRoot.root (hypPoly Fq)) := by
  rw [IsSeparable, AdjoinRoot.minpoly_root (hypPoly_ne_zero Fq), (monic_hypPoly Fq).leadingCoeff, inv_one,
    C_1, mul_one]
  exact separable_X_pow_sub_C _ (by exact_mod_cast two_ne_zero_ratFunc Fq h2) (f0K_ne_zero Fq)

instance isSeparable_hypF [h2 : Fact ((2 : Fq) ≠ 0)] : Algebra.IsSeparable (RatFunc Fq) (HypF Fq) := by
  have h := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (RatFunc Fq) (HypF Fq)).2
    (isSeparable_root Fq h2.out)
  rw [IntermediateField.adjoin_root_eq_top] at h
  exact AlgEquiv.Algebra.isSeparable IntermediateField.topEquiv

instance charP_hypF (p : ℕ) [CharP Fq p] : CharP (HypF Fq) p :=
  charP_of_injective_algebraMap (algebraMap Fq (HypF Fq)).injective p

/-- The generator `y`. -/
abbrev yF : HypF Fq := AdjoinRoot.root (hypPoly Fq)

theorem hy : yF Fq ^ 2 = algebraMap (RatFunc Fq) (HypF Fq) (f0K Fq) := by
  have h := AdjoinRoot.eval₂_root (hypPoly Fq)
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
  rw [AdjoinRoot.algebraMap_eq]
  exact h

theorem yF_ne_zero : yF Fq ≠ 0 := by
  intro h
  have := hy Fq
  rw [h, zero_pow two_ne_zero, eq_comm, map_eq_zero_iff _ (algebraMap (RatFunc Fq) (HypF Fq)).injective] at this
  exact f0K_ne_zero Fq this

/-- Every element is `a + b y` with `a, b ∈ Fq(x)`. -/
theorem exists_coords (z : HypF Fq) :
    ∃ a b : RatFunc Fq, z = algebraMap (RatFunc Fq) (HypF Fq) a + algebraMap (RatFunc Fq) (HypF Fq) b * yF Fq := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
  have hz : AdjoinRoot.mk (hypPoly Fq) g = AdjoinRoot.mk (hypPoly Fq) (g %ₘ hypPoly Fq) := by
    have := AdjoinRoot.mk_leftInverse (monic_hypPoly Fq) (AdjoinRoot.mk _ g)
    rw [AdjoinRoot.modByMonicHom_mk] at this
    exact this.symm
  have hdeg : (g %ₘ hypPoly Fq).degree ≤ 1 := by
    have h1 := degree_modByMonic_lt g (monic_hypPoly Fq)
    have h2 : (hypPoly Fq).degree = ((2 : ℕ) : WithBot ℕ) := by
      rw [degree_eq_natDegree (hypPoly_ne_zero Fq), natDegree_hypPoly]
    rw [h2] at h1
    rw [degree_le_iff_coeff_zero]
    intro m hm
    have hm' : 1 < m := by exact_mod_cast hm
    exact (degree_lt_iff_coeff_zero _ 2).1 h1 m (by omega)
  set r := g %ₘ hypPoly Fq with hr
  refine ⟨r.coeff 0, r.coeff 1, ?_⟩
  rw [hz, congrArg (AdjoinRoot.mk (hypPoly Fq)) (eq_X_add_C_of_degree_le_one hdeg), map_add, map_mul,
    AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq]
  ring

/-- `a + b y = 0` forces `a = b = 0`. -/
theorem coords_eq_zero {a b : RatFunc Fq}
    (h : algebraMap (RatFunc Fq) (HypF Fq) a + algebraMap (RatFunc Fq) (HypF Fq) b * yF Fq = 0) :
    a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    rw [map_zero, zero_mul, add_zero, map_eq_zero_iff _ (algebraMap (RatFunc Fq) (HypF Fq)).injective] at h
    exact ⟨h, rfl⟩
  · exfalso
    have hy' : yF Fq = algebraMap (RatFunc Fq) (HypF Fq) (-a / b) := by
      rw [map_div₀, map_neg]
      have hb' : algebraMap (RatFunc Fq) (HypF Fq) b ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap (RatFunc Fq) (HypF Fq)).injective).2 hb
      field_simp
      linear_combination h
    apply not_sq Fq (-a / b)
    apply (algebraMap (RatFunc Fq) (HypF Fq)).injective
    rw [map_pow, ← hy', hy]

theorem coords_unique {a b a' b' : RatFunc Fq}
    (h : algebraMap (RatFunc Fq) (HypF Fq) a + algebraMap (RatFunc Fq) (HypF Fq) b * yF Fq =
      algebraMap (RatFunc Fq) (HypF Fq) a' + algebraMap (RatFunc Fq) (HypF Fq) b' * yF Fq) :
    a = a' ∧ b = b' := by
  have h0 := coords_eq_zero Fq (a := a - a') (b := b - b') (by rw [map_sub, map_sub]; linear_combination h)
  exact ⟨sub_eq_zero.1 h0.1, sub_eq_zero.1 h0.2⟩

theorem aeval_neg_y : aeval (-yF Fq) (hypPoly Fq) = 0 := by
  rw [map_sub, map_pow, aeval_X, aeval_C, neg_sq, hy, sub_self]

/-- The `Fq(x)`-automorphism `y ↦ -y`. -/
def conjHom : HypF Fq →ₐ[RatFunc Fq] HypF Fq :=
  AdjoinRoot.liftAlgHom (hypPoly Fq) (Algebra.ofId (RatFunc Fq) (HypF Fq)) (-yF Fq) (by
    rw [← aeval_neg_y Fq, aeval_def]; rfl)

theorem conjHom_y : conjHom Fq (yF Fq) = -yF Fq := AdjoinRoot.liftAlgHom_root _ _ _ _

theorem conjHom_coords (a b : RatFunc Fq) :
    conjHom Fq (algebraMap (RatFunc Fq) (HypF Fq) a + algebraMap (RatFunc Fq) (HypF Fq) b * yF Fq) =
      algebraMap (RatFunc Fq) (HypF Fq) a - algebraMap (RatFunc Fq) (HypF Fq) b * yF Fq := by
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, conjHom_y]
  ring

end

end RamanujanPetersson.CP4a.Hyp2

end

-- ===== S4.Def_RP_CP4a_HypB =====
section

/-!
# S4-CP4a, part g2: the integral closure of `Fq[x]` in the function field of `y² = x⁵ + 1`

When `2 ≠ 0` and `5 ≠ 0` in `Fq`, an element `z` of `HypF Fq` is integral over `Fq[x]` iff `z = a(x) + b(x) y`
with polynomials `a, b` (`isIntegral_iff`); the coordinates are unique (`cP_inj`).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a.Hyp2

noncomputable section

variable (Fq : Type) [Field Fq]

/-- `a(x) + b(x) y` for polynomials `a, b`. -/
abbrev cP (a b : Fq[X]) : HypF Fq := algebraMap Fq[X] (HypF Fq) a + algebraMap Fq[X] (HypF Fq) b * yF Fq

theorem algebraMap_poly (a : Fq[X]) : algebraMap Fq[X] (HypF Fq) a =
    algebraMap (RatFunc Fq) (HypF Fq) (algebraMap Fq[X] (RatFunc Fq) a) :=
  IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) (HypF Fq) a

theorem isIntegral_y : IsIntegral Fq[X] (yF Fq) := by
  refine ⟨X ^ 2 - C (f0 Fq), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, hy, algebraMap_poly, sub_self]

theorem isIntegral_cP (a b : Fq[X]) : IsIntegral Fq[X] (cP Fq a b) :=
  isIntegral_algebraMap.add (isIntegral_algebraMap.mul (isIntegral_y Fq))

theorem cP_inj {a b a' b' : Fq[X]} (h : cP Fq a b = cP Fq a' b') : a = a' ∧ b = b' := by
  simp only [cP, algebraMap_poly] at h
  have h' := coords_unique Fq h
  exact ⟨IsFractionRing.injective Fq[X] (RatFunc Fq) h'.1, IsFractionRing.injective Fq[X] (RatFunc Fq) h'.2⟩

/-- An element of `Fq(x)` that is integral over `Fq[x]` (inside `HypF`) is a polynomial. -/
theorem mem_poly_of_isIntegral {r : RatFunc Fq} (h : IsIntegral Fq[X] (algebraMap (RatFunc Fq) (HypF Fq) r)) :
    ∃ a : Fq[X], algebraMap Fq[X] (RatFunc Fq) a = r :=
  IsIntegrallyClosed.isIntegral_iff.1
    ((isIntegral_algebraMap_iff (algebraMap (RatFunc Fq) (HypF Fq)).injective).1 h)

theorem squarefree_f0 (h5 : (5 : Fq) ≠ 0) : Squarefree (f0 Fq) := by
  have e : f0 Fq = X ^ 5 - C (-1) := by rw [C_neg, C_1, sub_neg_eq_add]
  rw [e]
  exact (separable_X_pow_sub_C (-1) (by exact_mod_cast h5) (neg_ne_zero.2 one_ne_zero)).squarefree

/-- If `B² (x⁵ + 1)` is a polynomial then so is `B` (`x⁵ + 1` is squarefree). -/
theorem exists_poly_of_sq_mul (h5 : (5 : Fq) ≠ 0) {B : RatFunc Fq} {d : Fq[X]}
    (h : B ^ 2 * f0K Fq = algebraMap Fq[X] (RatFunc Fq) d) :
    ∃ b : Fq[X], algebraMap Fq[X] (RatFunc Fq) b = B := by
  have hden : B.denom ≠ 0 := B.denom_ne_zero
  have hd' : algebraMap Fq[X] (RatFunc Fq) B.denom ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))]
    exact hden
  have e := RatFunc.num_div_denom B
  rw [div_eq_iff hd'] at e
  have key : B.num ^ 2 * f0 Fq = d * B.denom ^ 2 := by
    apply IsFractionRing.injective Fq[X] (RatFunc Fq)
    rw [map_mul, map_mul, map_pow, map_pow, e, ← h]
    ring
  have hdvd : B.denom ^ 2 ∣ B.num ^ 2 * f0 Fq := ⟨d, by rw [key, mul_comm]⟩
  have hcop : IsCoprime (B.denom ^ 2) (B.num ^ 2) := (RatFunc.isCoprime_num_denom B).symm.pow
  have hdf : B.denom * B.denom ∣ f0 Fq := by
    rw [← pow_two]
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hu := squarefree_f0 Fq h5 _ hdf
  have h1 : B.denom = 1 := (RatFunc.monic_denom B).isUnit_iff.1 hu
  refine ⟨B.num, ?_⟩
  rw [e, h1, map_one, mul_one]

/-- **Integral closure**: `z` is integral over `Fq[x]` iff `z = a(x) + b(x) y` with polynomials `a, b`. -/
theorem isIntegral_iff (h2 : (2 : Fq) ≠ 0) (h5 : (5 : Fq) ≠ 0) (z : HypF Fq) :
    IsIntegral Fq[X] z ↔ ∃ a b : Fq[X], z = cP Fq a b := by
  refine ⟨fun hz => ?_, fun ⟨a, b, h⟩ => h ▸ isIntegral_cP Fq a b⟩
  obtain ⟨A, B, rfl⟩ := exists_coords Fq z
  have hσ := hz.map ((conjHom Fq).restrictScalars Fq[X])
  rw [AlgHom.coe_restrictScalars', conjHom_coords] at hσ
  have htr := hz.add hσ
  have hnm := hz.mul hσ
  rw [show algebraMap (RatFunc Fq) (HypF Fq) A + algebraMap (RatFunc Fq) (HypF Fq) B * yF Fq +
      (algebraMap (RatFunc Fq) (HypF Fq) A - algebraMap (RatFunc Fq) (HypF Fq) B * yF Fq) =
      algebraMap (RatFunc Fq) (HypF Fq) (2 * A) by rw [map_mul, map_ofNat]; ring] at htr
  rw [show (algebraMap (RatFunc Fq) (HypF Fq) A + algebraMap (RatFunc Fq) (HypF Fq) B * yF Fq) *
      (algebraMap (RatFunc Fq) (HypF Fq) A - algebraMap (RatFunc Fq) (HypF Fq) B * yF Fq) =
      algebraMap (RatFunc Fq) (HypF Fq) (A ^ 2 - B ^ 2 * f0K Fq) by
        rw [map_sub, map_mul, map_pow, map_pow, ← hy]; ring] at hnm
  obtain ⟨a2, ha2⟩ := mem_poly_of_isIntegral Fq htr
  obtain ⟨c, hc⟩ := mem_poly_of_isIntegral Fq hnm
  have h2K := two_ne_zero_ratFunc Fq h2
  have hA : algebraMap Fq[X] (RatFunc Fq) (C (2⁻¹ : Fq) * a2) = A := by
    rw [map_mul, ha2, RatFunc.algebraMap_C, map_inv₀, map_ofNat, inv_mul_cancel_left₀ h2K]
  have hB2 : B ^ 2 * f0K Fq = algebraMap Fq[X] (RatFunc Fq) ((C (2⁻¹ : Fq) * a2) ^ 2 - c) := by
    rw [map_sub, map_pow, hA, hc]
    ring
  obtain ⟨b, hb⟩ := exists_poly_of_sq_mul Fq h5 hB2
  exact ⟨C (2⁻¹ : Fq) * a2, b, by rw [cP, algebraMap_poly, algebraMap_poly, hA, hb]⟩

end

end RamanujanPetersson.CP4a.Hyp2

end

-- ===== S4.Def_RP_CoreB_Pert =====
section

/-!
# Core B, O7: `charpoly(M) = P₀` from the norm identity for `deg F ≠ 0` only

`DegreeData.charpoly_eq` asks for `‖deg F‖_l = ‖det F(M)‖_l` for every `F` with `p ∤ F(0)`. When `deg F = 0`
(so `Res(P₀, F) = 0`) we perturb: `F + C (l^K p k)` keeps `p ∤ F(0)`, has `deg ≠ 0` for some `k` (a monic polynomial
in `c` has finitely many roots), and moves both resultants by at most `l^-K`; hence `det F(M) = 0`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CoreB

open RamanujanPetersson.JacAlg

variable {l : ℕ} [hl : Fact l.Prime]

/-- Changing the constant term by a multiple of `l^K` moves a resultant by at most `l^-K`. -/
theorem norm_resultant_add_C_sub_le (S G : ℤ_[l][X]) {c : ℤ_[l]} {K : ℕ}
    (hc : PadicInt.toZModPow K c = 0) (m n : ℕ) :
    ‖resultant S (G + C c) m n - resultant S G m n‖ ≤ (l : ℝ) ^ (-(K : ℤ)) := by
  apply norm_sub_le_of_toZModPow_eq
  rw [← resultant_map_map, ← resultant_map_map, Polynomial.map_add, map_C, hc, C_0, add_zero]

omit hl in
theorem eq_zero_of_norm_le_pow [Fact l.Prime] {x : ℤ_[l]} (h : ∀ K : ℕ, ‖x‖ ≤ (l : ℝ) ^ (-(K : ℤ))) :
    x = 0 := by
  by_contra hx
  have := (PadicInt.norm_le_pow_iff_le_valuation x hx (x.valuation + 1)).mp (h _)
  omega

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ}

omit hl in
/-- Some `F + C (a k)` has nonzero degree (`a ≠ 0`). -/
theorem exists_deg_add_ne (D : DegreeData π g p) (F : ℤ[X]) (a : ℤ) (ha : a ≠ 0) :
    ∃ k : ℕ, D.deg (F + C (a * k)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set R : ℂ[X] := ((D.charPoly.map (algebraMap ℚ ℂ)).roots.map
    fun z => X + C ((F.map (Int.castRingHom ℂ)).eval z)).prod with hR_def
  have hR : R.Monic := monic_multiset_prod_of_monic _ _ fun z _ => monic_X_add_C _
  have hroot : ∀ k : ℕ, R.IsRoot ((a * k : ℤ) : ℂ) := by
    intro k
    have h := D.deg_eq_prod_roots (K := ℂ) (F + C (a * k))
    rw [hcon k, Nat.cast_zero] at h
    rw [Polynomial.IsRoot.def, hR_def, eval_multiset_prod, Multiset.map_map, h]
    congr 1
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply, eval_add, eval_X, eval_C, Polynomial.map_add, eq_intCast]
    rw [Polynomial.map_intCast, Polynomial.eval_intCast]
    exact add_comm _ _
  apply hR.ne_zero
  refine eq_zero_of_infinite_isRoot R
    (Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((a * k : ℤ) : ℂ)) ?_ hroot)
  intro k1 k2 h
  have h' : ((a * k1 : ℤ) : ℂ) = ((a * k2 : ℤ) : ℂ) := h
  exact_mod_cast mul_left_cancel₀ ha (Int.cast_injective h')

/-- **O7.** `DegreeData.charpoly_eq` with the norm identity required only when `deg F ≠ 0`. -/
theorem charpoly_eq_of_deg_ne (D : DegreeData π g p) (hp : p.Prime) (hpl : p ≠ l) {P0 : ℤ[X]}
    (hP0 : D.charPoly = P0.map (Int.castRingHom ℚ)) {T : Type*} [AddCommGroup T] [Module ℤ_[l] T]
    [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (M : Module.End ℤ_[l] T)
    (hkey : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 → D.deg F ≠ 0 →
      ‖((D.deg F : ℕ) : ℤ_[l])‖ = ‖LinearMap.det (aeval M (F.map (Int.castRingHom ℤ_[l])))‖) :
    M.charpoly = P0.map (Int.castRingHom ℤ_[l]) := by
  refine D.charpoly_eq hp hpl hP0 M fun F hF => ?_
  by_cases h0 : D.deg F = 0
  swap
  · exact hkey F hF h0
  rw [h0, Nat.cast_zero, norm_zero, eq_comm, norm_eq_zero, linearMap_det_aeval_eq_resultant]
  refine eq_zero_of_norm_le_pow fun K => ?_
  have ha : (l : ℤ) ^ K * p ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.out.ne_zero)) (Nat.cast_ne_zero.mpr hp.ne_zero)
  obtain ⟨k, hk⟩ := exists_deg_add_ne D F _ ha
  set c : ℤ := (l : ℤ) ^ K * p * k with hc_def
  have hpc : (p : ℤ) ∣ c := ⟨(l : ℤ) ^ K * k, by rw [hc_def]; ring⟩
  have hFc : ¬ (p : ℤ) ∣ (F + C c).coeff 0 := by
    rw [coeff_add, coeff_C_zero]
    exact fun h => hF ((dvd_add_left hpc).mp h)
  have hcK : PadicInt.toZModPow K (Int.castRingHom ℤ_[l] c) = 0 := by
    rw [eq_intCast, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨(p : ℤ) * k, by rw [hc_def]; push_cast; ring⟩
  have h1 := hkey (F + C c) hFc hk
  rw [linearMap_det_aeval_eq_resultant, Polynomial.map_add, map_C, natDegree_add_C] at h1
  have e1 := D.deg_eq_resultant hP0 (F + C c)
  rw [natDegree_add_C] at e1
  have e0 := D.deg_eq_resultant hP0 F
  rw [h0, Nat.cast_zero] at e0
  have r1 : ((D.deg (F + C c) : ℕ) : ℤ_[l]) =
      resultant (P0.map (Int.castRingHom ℤ_[l])) ((F.map (Int.castRingHom ℤ_[l])) + C (Int.castRingHom ℤ_[l] c))
        P0.natDegree F.natDegree -
      resultant (P0.map (Int.castRingHom ℤ_[l])) (F.map (Int.castRingHom ℤ_[l])) P0.natDegree F.natDegree := by
    rw [← map_C, ← Polynomial.map_add, resultant_map_map, resultant_map_map, ← map_sub, ← e1, ← e0, sub_zero,
      map_natCast]
  have hb1 : ‖resultant (LinearMap.charpoly M) ((F.map (Int.castRingHom ℤ_[l])) + C (Int.castRingHom ℤ_[l] c))
      (Module.finrank ℤ_[l] T) (F.map (Int.castRingHom ℤ_[l])).natDegree‖ ≤ (l : ℝ) ^ (-(K : ℤ)) := by
    rw [← h1, r1]
    exact norm_resultant_add_C_sub_le _ _ hcK _ _
  have h2 := norm_resultant_add_C_sub_le (LinearMap.charpoly M) (F.map (Int.castRingHom ℤ_[l])) hcK
    (Module.finrank ℤ_[l] T) (F.map (Int.castRingHom ℤ_[l])).natDegree
  calc _ = ‖-(resultant (LinearMap.charpoly M) ((F.map (Int.castRingHom ℤ_[l])) + C (Int.castRingHom ℤ_[l] c))
          (Module.finrank ℤ_[l] T) (F.map (Int.castRingHom ℤ_[l])).natDegree -
        resultant (LinearMap.charpoly M) (F.map (Int.castRingHom ℤ_[l])) (Module.finrank ℤ_[l] T)
          (F.map (Int.castRingHom ℤ_[l])).natDegree) +
        resultant (LinearMap.charpoly M) ((F.map (Int.castRingHom ℤ_[l])) + C (Int.castRingHom ℤ_[l] c))
          (Module.finrank ℤ_[l] T) (F.map (Int.castRingHom ℤ_[l])).natDegree‖ := by
        rw [neg_sub, sub_add_cancel]
    _ ≤ max ‖-(resultant (LinearMap.charpoly M) ((F.map (Int.castRingHom ℤ_[l])) +
          C (Int.castRingHom ℤ_[l] c)) (Module.finrank ℤ_[l] T) (F.map (Int.castRingHom ℤ_[l])).natDegree -
        resultant (LinearMap.charpoly M) (F.map (Int.castRingHom ℤ_[l])) (Module.finrank ℤ_[l] T)
          (F.map (Int.castRingHom ℤ_[l])).natDegree)‖
        ‖resultant (LinearMap.charpoly M) ((F.map (Int.castRingHom ℤ_[l])) + C (Int.castRingHom ℤ_[l] c))
          (Module.finrank ℤ_[l] T) (F.map (Int.castRingHom ℤ_[l])).natDegree‖ :=
        PadicInt.nonarchimedean _ _
    _ ≤ (l : ℝ) ^ (-(K : ℤ)) := max_le (by rw [norm_neg]; exact h2) hb1

end RamanujanPetersson.CoreB

end

-- ===== S4.Def_RP_Lefschetz_OinfInt =====
section

/-!
# S4-Lefschetz L4b, part 1: `O_∞(k)` is integral over `O_∞(𝔽_q)` for a finite extension `k / 𝔽_q`

* `frobK`, `mem_range_of_pow_card`: the elements of `k` fixed by `x ↦ x^q` are those of `𝔽_q`.
* `conjPoly`, `exists_rationalize`: every `Q ≠ 0` in `k[X]` has a multiple `Q N = R` with `R ∈ 𝔽_q[X]`
  (`R = ∏_j Q^{σ^j}`, the norm).
* `isIntegral_of_mem_Oinf`: for any algebra `𝔽_q(X) → k(X)` extending `𝔽_q[X] → k[X]`, every `f ∈ O_∞(k)`
  is integral over `O_∞(𝔽_q)` (`f = P N / R` with `deg (P N) ≤ deg R`, a sum of constants times `X^n / R`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

open Places

noncomputable section

section Frob

variable (Fq k : Type) [Field Fq] [Fintype Fq] [Field k] [Fintype k] [Algebra Fq k]

/-- The `q`-Frobenius of `k / 𝔽_q`. -/
def frobK : k ≃ₐ[Fq] k := FiniteField.frobeniusAlgEquivOfAlgebraic Fq k

theorem frobK_apply (x : k) : frobK Fq k x = x ^ Fintype.card Fq := rfl

theorem frobK_pow_finrank : frobK Fq k ^ Module.finrank Fq k = 1 := by
  rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (K := Fq) (L := k)]
  exact pow_orderOf_eq_one (FiniteField.frobeniusAlgEquivOfAlgebraic Fq k)

theorem mem_range_of_pow_card (x : k) (hx : x ^ Fintype.card Fq = x) :
    x ∈ Set.range (algebraMap Fq k) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro f
  obtain ⟨n, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (K := Fq) (L := k)).2 f
  show (FiniteField.frobeniusAlgEquivOfAlgebraic Fq k ^ n.1) x = x
  generalize n.1 = m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, AlgEquiv.mul_apply, show FiniteField.frobeniusAlgEquivOfAlgebraic Fq k x = x from hx, ih]

/-- The Frobenius conjugates `Q^{σ^j}` of a polynomial. -/
def conjPoly (Q : k[X]) (j : ℕ) : k[X] := Q.map ((frobK Fq k ^ j : k ≃ₐ[Fq] k) : k →+* k)

theorem conjPoly_coeff (Q : k[X]) (j n : ℕ) :
    (conjPoly Fq k Q j).coeff n = (frobK Fq k ^ j) (Q.coeff n) := by
  rw [conjPoly, Polynomial.coeff_map]
  rfl

theorem conjPoly_zero (Q : k[X]) : conjPoly Fq k Q 0 = Q := by
  ext n
  rw [conjPoly_coeff, pow_zero]
  rfl

theorem conjPoly_finrank (Q : k[X]) : conjPoly Fq k Q (Module.finrank Fq k) = Q := by
  ext n
  rw [conjPoly_coeff, frobK_pow_finrank]
  rfl

theorem conjPoly_succ (Q : k[X]) (j : ℕ) :
    (conjPoly Fq k Q j).map ((frobK Fq k : k ≃ₐ[Fq] k) : k →+* k) = conjPoly Fq k Q (j + 1) := by
  ext n
  rw [Polynomial.coeff_map, conjPoly_coeff, conjPoly_coeff, pow_succ', AlgEquiv.mul_apply]
  rfl

theorem conjPoly_ne_zero {Q : k[X]} (hQ : Q ≠ 0) (j : ℕ) : conjPoly Fq k Q j ≠ 0 :=
  (Polynomial.map_ne_zero_iff (RingHom.injective _)).2 hQ

theorem conjPoly_prod_fixed (Q : k[X]) (hQ : Q ≠ 0) :
    (∏ j ∈ Finset.range (Module.finrank Fq k), conjPoly Fq k Q j).map
        ((frobK Fq k : k ≃ₐ[Fq] k) : k →+* k) =
      ∏ j ∈ Finset.range (Module.finrank Fq k), conjPoly Fq k Q j := by
  rw [Polynomial.map_prod]
  simp only [conjPoly_succ]
  have h1 := Finset.prod_range_succ' (conjPoly Fq k Q) (Module.finrank Fq k)
  have h2 := Finset.prod_range_succ (conjPoly Fq k Q) (Module.finrank Fq k)
  have h3 := h1.symm.trans h2
  rw [conjPoly_zero, conjPoly_finrank] at h3
  exact mul_right_cancel₀ hQ h3

/-- Rationalizing a denominator: `Q * N ∈ 𝔽_q[X]`. -/
theorem exists_rationalize (Q : k[X]) (hQ : Q ≠ 0) :
    ∃ (N : k[X]) (R : Fq[X]), R ≠ 0 ∧ Q * N = R.map (algebraMap Fq k) := by
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank Fq k = d + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := Fq) (M := k)).ne'
  have hmem : (∏ j ∈ Finset.range (Module.finrank Fq k), conjPoly Fq k Q j) ∈
      (Polynomial.mapRingHom (algebraMap Fq k)).range := by
    rw [Polynomial.mem_map_range]
    intro n
    have h := congrArg (fun p : k[X] => p.coeff n) (conjPoly_prod_fixed Fq k Q hQ)
    simp only [Polynomial.coeff_map] at h
    obtain ⟨c, hc⟩ := mem_range_of_pow_card Fq k _ h
    exact ⟨c, hc⟩
  obtain ⟨R, hR⟩ := hmem
  have hne : (∏ j ∈ Finset.range (Module.finrank Fq k), conjPoly Fq k Q j) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => conjPoly_ne_zero Fq k hQ j
  have hR' : R.map (algebraMap Fq k) = ∏ j ∈ Finset.range (Module.finrank Fq k), conjPoly Fq k Q j := hR
  refine ⟨∏ j ∈ Finset.range d, conjPoly Fq k Q (j + 1), R, ?_, ?_⟩
  · rintro rfl
    apply hne
    rw [← hR', Polynomial.map_zero]
  · rw [hR', hd, Finset.prod_range_succ' (conjPoly Fq k Q) d, conjPoly_zero, mul_comm]

end Frob

section OinfInt

variable (Fq k : Type) [Field Fq] [Fintype Fq] [Field k] [Fintype k] [Algebra Fq k]
  [DecidableEq (RatFunc Fq)] [DecidableEq (RatFunc k)] [Algebra (RatFunc Fq) (RatFunc k)]
  (hι : ∀ p : Fq[X], algebraMap (RatFunc Fq) (RatFunc k) (algebraMap Fq[X] (RatFunc Fq) p) =
    algebraMap k[X] (RatFunc k) (p.map (algebraMap Fq k)))

theorem isIntegral_const (c : k) : IsIntegral (Oinf Fq) (algebraMap k (RatFunc k) c) := by
  refine ⟨X ^ Fintype.card k - X, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub (by rw [degree_X]; exact_mod_cast Fintype.one_lt_card)
  · rw [eval₂_sub, eval₂_X_pow, eval₂_X, ← map_pow, FiniteField.pow_card, sub_self]

include hι in
/-- **L4b core**: `O_∞(k)` is integral over `O_∞(𝔽_q)`. -/
theorem isIntegral_of_mem_Oinf (f : RatFunc k) (hf : f ∈ Oinf k) : IsIntegral (Oinf Fq) f := by
  classical
  by_cases h0 : f = 0
  · rw [h0]
    exact isIntegral_zero
  have hP0 : f.num ≠ 0 := RatFunc.num_ne_zero h0
  have hdeg : (f.num.natDegree : ℤ) - f.denom.natDegree ≤ 0 := by
    have h := (mem_Oinf_iff' k h0).1 hf
    rwa [← RatFunc.num_div_denom f, intDegree_div_polys k hP0 (RatFunc.denom_ne_zero f)] at h
  obtain ⟨N, R, hR0, hQN⟩ := exists_rationalize Fq k f.denom (RatFunc.denom_ne_zero f)
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hQN
    exact hR0 (Polynomial.map_injective _ (algebraMap Fq k).injective (by rw [← hQN, Polynomial.map_zero]))
  have h3 : (f.denom * N).natDegree = R.natDegree := by
    rw [hQN, natDegree_map_eq_of_injective (algebraMap Fq k).injective R]
  have hQNdeg : (f.denom * N).natDegree = f.denom.natDegree + N.natDegree :=
    natDegree_mul (RatFunc.denom_ne_zero f) hN0
  have hA : ∀ p : k[X], p ≠ 0 → algebraMap k[X] (RatFunc k) p ≠ 0 := fun p hp =>
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).2 hp
  have hf' : f = algebraMap k[X] (RatFunc k) (f.num * N) /
      algebraMap k[X] (RatFunc k) (R.map (algebraMap Fq k)) := by
    rw [← hQN, map_mul, map_mul, mul_div_mul_right _ _ (hA N hN0), RatFunc.num_div_denom]
  rw [hf', as_sum_support_C_mul_X_pow (f.num * N), map_sum, Finset.sum_div]
  refine IsIntegral.sum _ fun n hn => ?_
  have hn' : n ≤ R.natDegree := by
    have h1 := le_natDegree_of_mem_supp n hn
    have h2 := natDegree_mul_le (p := f.num) (q := N)
    omega
  rw [map_mul, mul_div_assoc]
  refine IsIntegral.mul ?_ ?_
  · have hc : algebraMap k[X] (RatFunc k) (C ((f.num * N).coeff n)) =
        algebraMap k (RatFunc k) ((f.num * N).coeff n) := by
      rw [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
    rw [hc]
    exact isIntegral_const Fq k _
  · have hXn : algebraMap Fq[X] (RatFunc Fq) (X ^ n) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).2 (pow_ne_zero n X_ne_zero)
    have hRn : algebraMap Fq[X] (RatFunc Fq) R ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).2 hR0
    have hz : algebraMap Fq[X] (RatFunc Fq) (X ^ n) / algebraMap Fq[X] (RatFunc Fq) R ∈ Oinf Fq := by
      rw [mem_Oinf_iff' Fq (div_ne_zero hXn hRn), intDegree_div_polys Fq (pow_ne_zero n X_ne_zero) hR0,
        natDegree_X_pow]
      omega
    have hz' : algebraMap k[X] (RatFunc k) (X ^ n) / algebraMap k[X] (RatFunc k) (R.map (algebraMap Fq k)) =
        algebraMap (Oinf Fq) (RatFunc k) ⟨_, hz⟩ := by
      rw [IsScalarTower.algebraMap_apply (Oinf Fq) (RatFunc Fq) (RatFunc k)]
      show _ = algebraMap (RatFunc Fq) (RatFunc k)
        (algebraMap Fq[X] (RatFunc Fq) (X ^ n) / algebraMap Fq[X] (RatFunc Fq) R)
      rw [map_div₀, hι, hι, Polynomial.map_pow, Polynomial.map_X]
    rw [hz']
    exact isIntegral_algebraMap

end OinfInt

end

end Lefschetz
end RamanujanPetersson

end

-- ===== S4.Def_RP_Lefschetz_BlockGrp =====
section

/-!
# S4-Lefschetz, L3d3a: the block subgroup `H_ω`

For `g` whose inverse acts on constants as `x ↦ x ^ (q ^ m)` (e.g. `g = c0⁻¹ (φ⁻¹)^m`, `ginv_apply`), a finite
quotient `π : π₁ → Gf` and a primitive `((q^m)^|Gf| - 1)`-th root of unity `ζ` in `K_U`:
`blkH π g ζ hζ = {x | ∃ k : ℤ, π x = π g ^ k ∧ x ζ = g ^ k ζ}` is an open subgroup (`isOpen_blkH`) containing `g`
(`g_mem_blkH`) with `blkH ⊓ π₁^geo = π₁^geo ⊓ ker π` (`mem_blkH_geo_iff`), and it fixes `𝔽_{q^m}` (`blkH_fix`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh GalCover

section BlockGrp

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

/-- Two automorphisms that agree on a primitive root `ζ` agree on every conjugate `τ ζ`. -/
theorem agree_apply_of_prim {ζ : maxUnram A K} {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N)
    {σ ρ : Pi1 A K} (h : σ ζ = ρ ζ) (τ : Pi1 A K) : σ (τ ζ) = ρ (τ ζ) := by
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  rw [← hi, map_pow, map_pow, h]

/-- A primitive `(Q - 1)`-th root of unity satisfies `ζ ^ Q = ζ`. -/
theorem prim_pow_fix {L : Type} [Field L] {ζ : L} {Q : ℕ} (hQ : 1 ≤ Q) (hζ : IsPrimitiveRoot ζ (Q - 1)) :
    ζ ^ Q = ζ :=
  calc ζ ^ Q = ζ ^ (Q - 1 + 1) := by rw [Nat.sub_add_cancel hQ]
  _ = ζ := by rw [pow_succ, hζ.pow_eq_one, one_mul]

/-- A Frobenius lift acts on constants as `x ↦ x ^ (q ^ n)` through its `n`-th power. -/
theorem frob_pow_apply {q : ℕ} {φ : Pi1 A K} (hφ : IsFrobLift A K q φ) {x : maxUnram A K} (hx : IsConst q x)
    (n : ℕ) : (φ ^ n) x = x ^ (q ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_one, AlgEquiv.one_apply]
  | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hφ x hx, ← pow_mul, ← pow_succ']

/-- For `g = c0⁻¹ (φ⁻¹)^m` (`c0` geometric, `φ` a Frobenius lift), `g⁻¹` acts on constants as `x ↦ x ^ (q ^ m)`. -/
theorem ginv_apply {q : ℕ} {φ c0 : Pi1 A K} (hφ : IsFrobLift A K q φ) (hc0 : c0 ∈ pi1geo A K q) (m : ℕ)
    (x : maxUnram A K) (hx : IsConst q x) : (c0⁻¹ * φ⁻¹ ^ m)⁻¹ x = x ^ (q ^ m) := by
  rw [mul_inv_rev, inv_inv, inv_pow, inv_inv, AlgEquiv.mul_apply, (mem_pi1geo A K q c0).1 hc0 x hx,
    frob_pow_apply hφ hx m]

variable {Gf : Type} [Group Gf] (π : Pi1 A K →* Gf) (g : Pi1 A K) (ζ : maxUnram A K)

/-- The block subgroup `H_ω`: `x` with `π x = π g ^ k` and `x ζ = g ^ k ζ` for one `k : ℤ`. -/
def blkH {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N) : Subgroup (Pi1 A K) where
  carrier := {x | ∃ k : ℤ, π x = π g ^ k ∧ x ζ = (g ^ k) ζ}
  one_mem' := by
    show ∃ k : ℤ, π 1 = π g ^ k ∧ (1 : Pi1 A K) ζ = (g ^ k) ζ
    exact ⟨0, by rw [map_one, zpow_zero], by rw [zpow_zero]⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨k, hk1, hk2⟩ := hx
    obtain ⟨k', hk1', hk2'⟩ := hy
    show ∃ k : ℤ, π (x * y) = π g ^ k ∧ (x * y) ζ = (g ^ k) ζ
    refine ⟨k + k', by rw [map_mul, hk1, hk1', zpow_add], ?_⟩
    rw [AlgEquiv.mul_apply, hk2', zpow_add, AlgEquiv.mul_apply]
    exact agree_apply_of_prim hζ hk2 _
  inv_mem' := by
    intro x hx
    obtain ⟨k, hk1, hk2⟩ := hx
    show ∃ k : ℤ, π x⁻¹ = π g ^ k ∧ x⁻¹ ζ = (g ^ k) ζ
    refine ⟨-k, by rw [map_inv, hk1, zpow_neg], ?_⟩
    have h := agree_apply_of_prim hζ hk2 (g ^ (-k))
    rw [← AlgEquiv.mul_apply (g ^ k), ← zpow_add, add_neg_cancel, zpow_zero, AlgEquiv.one_apply] at h
    apply (x : maxUnram A K ≃ₐ[K] maxUnram A K).injective
    rw [← AlgEquiv.mul_apply x x⁻¹, mul_inv_cancel, AlgEquiv.one_apply, h]

theorem mem_blkH {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N) {x : Pi1 A K} :
    x ∈ blkH π g ζ hζ ↔ ∃ k : ℤ, π x = π g ^ k ∧ x ζ = (g ^ k) ζ := Iff.rfl

theorem g_mem_blkH {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N) : g ∈ blkH π g ζ hζ :=
  (mem_blkH π g ζ hζ).2 ⟨1, by rw [zpow_one], by rw [zpow_one]⟩

theorem ker_inf_le_blkH {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N) :
    π.ker ⊓ fixElt A K ζ ≤ blkH π g ζ hζ := fun x hx =>
  (mem_blkH π g ζ hζ).2 ⟨0, by rw [zpow_zero]; exact hx.1, by rw [zpow_zero, AlgEquiv.one_apply]; exact hx.2⟩

/-- `H_ω` is open (it contains `ker π ∩ Stab ζ`). -/
theorem isOpen_blkH {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N) (hπ : IsOpen (π.ker : Set (Pi1 A K))) :
    IsOpen (blkH π g ζ hζ : Set (Pi1 A K)) :=
  Subgroup.isOpen_mono (ker_inf_le_blkH π g ζ hζ)
    (by rw [Subgroup.coe_inf]; exact hπ.inter (fixElt_isOpen A K ζ))

/-- `g ^ k ζ = ζ` forces `(g⁻¹) ^ |k| ζ = ζ`. -/
theorem gpow_fix_natAbs (k : ℤ) (h : (g ^ k) ζ = ζ) : (g⁻¹ ^ k.natAbs) ζ = ζ := by
  have h' : (g ^ (-k)) ζ = ζ := by
    conv_lhs => rw [← h]
    rw [← AlgEquiv.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, AlgEquiv.one_apply]
  rcases Int.natAbs_eq k with hk | hk
  · rw [hk, zpow_neg, zpow_natCast, ← inv_pow] at h'
    exact h'
  · rw [hk, zpow_neg, zpow_natCast, ← inv_pow] at h
    exact h

theorem ginv_pow_apply {q Q : ℕ} (hg : ∀ x : maxUnram A K, IsConst q x → g⁻¹ x = x ^ Q) (hζc : IsConst q ζ)
    (n : ℕ) : (g⁻¹ ^ n) ζ = ζ ^ (Q ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_one, AlgEquiv.one_apply]
  | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hg ζ hζc, map_pow, ih, ← pow_mul, ← pow_succ]

/-- `ζ ^ (Q ^ n) = ζ` for a primitive `(Q^r - 1)`-th root forces `r ∣ n`. -/
theorem dvd_of_pow_fix {L : Type} [Field L] {ζ : L} {Q r n : ℕ} (hQ : 2 ≤ Q) (hr : 0 < r)
    (hζ : IsPrimitiveRoot ζ (Q ^ r - 1)) (h : ζ ^ (Q ^ n) = ζ) : r ∣ n := by
  have hQr : 2 ≤ Q ^ r := le_trans hQ (Nat.le_self_pow hr.ne' Q)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have h1 : ζ ^ (Q ^ n - 1) = 1 := by
    have e : ζ ^ (Q ^ n - 1) * ζ = 1 * ζ := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega)), h, one_mul]
    exact mul_right_cancel₀ hζ0 e
  have h2 : Q ^ r - 1 ∣ Q ^ n - 1 := (hζ.pow_eq_one_iff_dvd _).1 h1
  have h3 : Nat.gcd (Q ^ r - 1) (Q ^ n - 1) = Q ^ r - 1 := Nat.gcd_eq_left h2
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at h3
  have h4 : Q ^ Nat.gcd r n = Q ^ r := by
    have a1 := Nat.one_le_pow (Nat.gcd r n) Q (by omega)
    have a2 := Nat.one_le_pow r Q (by omega)
    generalize Q ^ Nat.gcd r n = X at *
    generalize Q ^ r = Y at *
    omega
  have h5 : Nat.gcd r n = r := Nat.pow_right_injective hQ h4
  rw [← h5]
  exact Nat.gcd_dvd_right r n

variable [Fintype Gf]

/-- The primitive root is a constant. -/
theorem isConst_zeta {q m : ℕ} (hq2 : 2 ≤ q) (hm : 0 < m)
    {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ ((q ^ m) ^ Fintype.card Gf - 1)) : IsConst q ζ := by
  have hr : 0 < Fintype.card Gf := Fintype.card_pos
  refine ⟨m * Fintype.card Gf, Nat.mul_pos hm hr, ?_⟩
  rw [pow_mul]
  exact prim_pow_fix (Nat.one_le_pow _ _ (pow_pos (by omega) m)) hζ

/-- **`H_ω ⊓ π₁^geo = π₁^geo ⊓ ker π`** (`hHΓ` of BlockIso / BlockCone2). -/
theorem mem_blkH_geo_iff {q m : ℕ} (hq2 : 2 ≤ q) (hm : 0 < m)
    (hg : ∀ x : maxUnram A K, IsConst q x → g⁻¹ x = x ^ (q ^ m))
    [NeZero ((q ^ m) ^ Fintype.card Gf - 1)] (hζ : IsPrimitiveRoot ζ ((q ^ m) ^ Fintype.card Gf - 1))
    {x : Pi1 A K} (hx : x ∈ pi1geo A K q) : x ∈ blkH π g ζ hζ ↔ π x = 1 := by
  have hr : 0 < Fintype.card Gf := Fintype.card_pos
  have hζc : IsConst q ζ := isConst_zeta (Gf := Gf) hq2 hm hζ
  have hxζ : x ζ = ζ := (mem_pi1geo A K q x).1 hx ζ hζc
  constructor
  · intro hmem
    obtain ⟨k, hk1, hk2⟩ := (mem_blkH π g ζ hζ).1 hmem
    have h1 : (g ^ k) ζ = ζ := hk2.symm.trans hxζ
    have h2 := gpow_fix_natAbs g ζ k h1
    rw [ginv_pow_apply g ζ hg hζc] at h2
    have h3 : Fintype.card Gf ∣ k.natAbs :=
      dvd_of_pow_fix (le_trans hq2 (Nat.le_self_pow hm.ne' q)) hr hζ h2
    obtain ⟨t, ht⟩ := h3
    have hp : π g ^ k.natAbs = 1 := by rw [ht, pow_mul, pow_card_eq_one, one_pow]
    rw [hk1]
    rcases Int.natAbs_eq k with h | h
    · rw [h, zpow_natCast, hp]
    · rw [h, zpow_neg, zpow_natCast, hp, inv_one]
  · intro h1
    exact (mem_blkH π g ζ hζ).2 ⟨0, by rw [h1, zpow_zero], by rw [zpow_zero, AlgEquiv.one_apply, hxζ]⟩

/-- **`H_ω` fixes `𝔽_{q^m}`**: every `τ ∈ H_ω` fixes every `y` with `y ^ (q ^ m) = y`. -/
theorem blkH_fix {q m : ℕ} (hq2 : 2 ≤ q) (hm : 0 < m)
    (hg : ∀ x : maxUnram A K, IsConst q x → g⁻¹ x = x ^ (q ^ m))
    [NeZero ((q ^ m) ^ Fintype.card Gf - 1)] (hζ : IsPrimitiveRoot ζ ((q ^ m) ^ Fintype.card Gf - 1))
    {τ : Pi1 A K} (hτ : τ ∈ blkH π g ζ hζ) {y : maxUnram A K} (hy : y ^ (q ^ m) = y) : τ y = y := by
  obtain ⟨k, -, hk⟩ := (mem_blkH π g ζ hζ).1 hτ
  have hyc : IsConst q y := ⟨m, hm, hy⟩
  have hgi : g⁻¹ ∈ fixElt A K y := by
    show g⁻¹ y = y
    rw [hg y hyc, hy]
  have hgy : g ∈ fixElt A K y := by simpa using inv_mem hgi
  have hgk : (g ^ k) y = y := Subgroup.zpow_mem _ hgy k
  by_cases h0 : y = 0
  · rw [h0, map_zero]
  have hQ1 : 1 ≤ (q ^ m) ^ Fintype.card Gf := Nat.one_le_pow _ _ (pow_pos (by omega) m)
  have hyQ : ∀ j : ℕ, y ^ ((q ^ m) ^ j) = y := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_one]
    | succ j ih => rw [pow_succ, pow_mul, ih, hy]
  have hyr : y ^ ((q ^ m) ^ Fintype.card Gf - 1) = 1 := by
    have e : y ^ ((q ^ m) ^ Fintype.card Gf - 1) * y = 1 * y := by
      rw [← pow_succ, Nat.sub_add_cancel hQ1, hyQ, one_mul]
    exact mul_right_cancel₀ h0 e
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hyr
  rw [← hi, map_pow, hk, ← map_pow, hi]
  exact hgk

end BlockGrp

end

end Lefschetz
end RamanujanPetersson

end


