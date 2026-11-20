-- Prove2me | Definitions.Def_RPLib_F2_066
-- name    : RPLib_F2_066
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T22:22:09.760613+00:00
-- url     : https://prove2.me/theorems/ac6de3d3-611b-4e96-aacb-41d641d51247
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 066 of 70
-- statement:
--   File 066 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_CoreB_Key`: Core B, O6: `‖deg F‖_l = ‖det F(M)‖_l` through Tate coordinates (for `deg F ≠ 0`)
--   * `S4.Def_RP_CoreB`: Unit S4-CoreB (Core B final assembly, lemmas L43-L44 of `S4_COREB_ROUTE.md` section 3): umbrella
--   * `S4.Def_RP_CupDuality_KumPicDiv`: S4-CurveDuality, O5b (ii): `Pic⁰(X̄)` is `l^n`-divisible for `l ∤ q`
--   * `S4.Def_RP_Lefschetz_PDiv1`: S4-Lefschetz, L6e (1): a degree-zero divisor is `l^n`-divisible modulo principal divisors at a finite level
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_052
import Definitions.Def_RPLib_F2_064

/-!
# Ramanujan-Petersson curve library (flat edition), file 066 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_CoreB_Key`: Core B, O6: `‖deg F‖_l = ‖det F(M)‖_l` through Tate coordinates (for `deg F ≠ 0`)
* `S4.Def_RP_CoreB`: Unit S4-CoreB (Core B final assembly, lemmas L43-L44 of `S4_COREB_ROUTE.md` section 3): umbrella
* `S4.Def_RP_CupDuality_KumPicDiv`: S4-CurveDuality, O5b (ii): `Pic⁰(X̄)` is `l^n`-divisible for `l ∤ q`
* `S4.Def_RP_Lefschetz_PDiv1`: S4-Lefschetz, L6e (1): a degree-zero divisor is `l^n`-divisible modulo principal divisors at a finite level
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CoreB_Key =====
section

/-!
# Core B, O6: `‖deg F‖_l = ‖det F(M)‖_l` through Tate coordinates (for `deg F ≠ 0`)

* Tate matrices are closed under `0`, `-`, `+`, integer constants and polynomial evaluation (`isTateMat_aeval`).
* `h1inj_of_injective`, `h1span_of_card`: the basis hypotheses of CoreA from injectivity of `tateMap 1` and the count
  `#D[l] ≤ l^s`.
* `iotaG`: `D = l^k0 A ↪ Pic⁰(X̄)`, `π`-equivariant; `card_kerD`: `#ker F(π|D) = l ^ v_l(#ker F(π))`.
* `norm_deg_eq_norm_det` (hkey for `deg F ≠ 0`).
-/

set_option autoImplicit false

open Polynomial
open scoped Matrix

namespace RamanujanPetersson.CoreB

open RamanujanPetersson.JacAlg RamanujanPetersson.JacComplete RamanujanPetersson.JacFrob RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places RamanujanPetersson.CoreA

section Gen

variable {G : Type*} [AddCommGroup G] {l : ℕ} [Fact l.Prime]
variable (hdiv : ∀ y : G, ∃ z, l • z = y) {s : ℕ} (b1 : Fin s → G) (hb1 : ∀ i, l • b1 i = 0)

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

variable (l k0 : ℕ) [hl : Fact l.Prime]

/-- **hkey (`deg F ≠ 0`).** For CoreA Tate data with `tateMap` injective at every level and `s = 2g`,
`‖deg F‖_l = ‖det F(M)‖_l` whenever `p ∤ F(0)` and `deg F ≠ 0`. -/
theorem norm_deg_eq_norm_det (hlq : ¬ l ∣ Fintype.card Fq)
    (hdiv : ∀ y : (smulHom (Aℓ Ω hk l) (l ^ k0)).range, ∃ z, l • z = y) {s : ℕ}
    (b1 : Fin s → (smulHom (Aℓ Ω hk l) (l ^ k0)).range) (hb1 : ∀ i, l • b1 i = 0)
    (M : Matrix (Fin s) (Fin s) ℤ_[l]) (hinj : ∀ N, Function.Injective (tateMap hdiv b1 hb1 N))
    (hM : IsTateMat hdiv b1 hb1 (endD (piA Ω hk l) (l ^ k0)) M) {gD : ℕ}
    (D : DegreeData (piBar0 Fq F Ω hk) gD (ringChar Fq)) (hs : s = 2 * gD) (P : ℤ[X])
    (hP : ¬ ((ringChar Fq : ℕ) : ℤ) ∣ P.coeff 0) (hdeg : D.deg P ≠ 0) :
    ‖((D.deg P : ℕ) : ℤ_[l])‖ = ‖(aeval M P).det‖ := by
  have hlp : l.Prime := hl.out
  have h1inj := h1inj_of_injective hdiv b1 hb1 (hinj 1)
  let j : {x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range // l • x = 0} → Tors (PicBar0 Ω hk) l :=
    fun x => ⟨iotaG Fq F Ω hk l k0 x.1, by rw [← map_nsmul, x.2, map_zero]⟩
  have hj : Function.Injective j :=
    fun a b h => Subtype.ext (iotaG_injective Fq F Ω hk l k0 (congrArg Subtype.val h))
  have hT := D.card_tors l (not_ringChar_dvd Fq l hlq)
  have : Finite (Tors (PicBar0 Ω hk) l) :=
    Nat.finite_of_card_ne_zero (by rw [hT]; exact pow_ne_zero _ hlp.ne_zero)
  have : Finite {x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range // l • x = 0} := Finite.of_injective j hj
  have h1span := h1span_of_card hdiv b1 hb1 (hinj 1)
    (by rw [hs, ← hT]; exact Nat.card_le_card_of_injective j hj)
  have htors : ∀ x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range, ∃ k, l ^ k • x = 0 := fun x => by
    obtain ⟨k, hx⟩ := AddCommGroup.mem_primaryComponent.mp x.1.2
    exact ⟨k, Subtype.ext (Subtype.ext (by rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_nsmul]; exact hx))⟩
  have hψ := isTateMat_aeval hdiv b1 hb1 hM P
  have : Finite (LinearMap.ker (aeval (piBar0 Fq F Ω hk) P)) :=
    (Set.not_infinite.mp ((D.deg_eq_zero_iff P).not.mp hdeg)).to_subtype
  have hcard := card_kerD Fq F Ω hk l k0 (divisible_Aℓ Fq F Ω hk l hlq) P
  have : Finite {x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range //
      aeval (endD (piA Ω hk l) (l ^ k0)) P x = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hlp.ne_zero)
  have hdet := IsTateMat.det_ne_zero hdiv b1 hb1 h1inj hψ inferInstance
  have hc2 := IsTateMat.card_ker hdiv b1 hb1 h1inj h1span htors hψ hdet
  rw [hc2, ← D.deg_eq_card_ker P hP] at hcard
  have hv := Nat.pow_right_injective hlp.two_le hcard
  rw [PadicInt.norm_eq_zpow_neg_valuation hdet, PadicInt.norm_def, PadicInt.coe_natCast,
    Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr hdeg), Padic.valuation_natCast, hv]

end Spec

end RamanujanPetersson.CoreB


end

-- ===== S4.Def_RP_CoreB =====
section

/-!
# Unit S4-CoreB (Core B final assembly, lemmas L43-L44 of `S4_COREB_ROUTE.md` section 3): umbrella

For every function field `F/F_q` with `constField F_q F = F_q` (smooth projective geometrically connected `X/F_q`),
every prime `l ∤ q`, and `π` the arithmetic Frobenius on `Pic⁰(X̄)`:
* `exists_degreeData` (L43, `_Data`): `deg F := deg (F(π))` is a `DegreeData` for `ℤ[π]` on `Pic⁰(X̄)`; `zeta_link`
  (`_Zeta`): `g_D = g` and `P_π = Π (X - ω_i) ∈ ℤ[X]` for the zeta roots `ω`;
* `divisible_Aℓ` (CB1, `_Div`): `Pic(X̄)[l^∞]` is `l`-divisible;
* `norm_deg_eq_norm_det` (`_Key`), `charpoly_eq_of_deg_ne` (`_Pert`): `χ_M = P_π` for every CoreA Tate matrix `M`;
* `coreBHyp_proved` (CB1 + CB2): the hypothesis `CP4a.CoreBHyp` that S4-CP4a assumes, proved;
* `exists_trace_pow_of_charpoly`, `coreB_count`, `exists_tate_count` (CB3): `#X(F_(q^m)) = 1 + q^m - tr(M^m)`.
-/

set_option autoImplicit false

open Polynomial
open scoped Matrix

namespace RamanujanPetersson.CoreB

open RamanujanPetersson.JacAlg RamanujanPetersson.JacComplete RamanujanPetersson.JacFrob RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places RamanujanPetersson.CoreA RamanujanPetersson.ZetaSB

section Trace

variable {R : Type*} [CommRing R] [Nontrivial R] {n : Type*} [Fintype n] [DecidableEq n]

end Trace

section Main

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- **Core B (CB1 + CB2), proved**: the hypothesis `CP4a.CoreBHyp` holds for every `X/F_q` with
`constField F_q F = F_q` and every prime `l ∤ q`. -/
theorem coreBHyp_proved (hk : constField Fq F = ⊥) (l : ℕ) [Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq) :
    CP4a.CoreBHyp hk l := by
  refine ⟨divisible_Aℓ Fq F (AlgebraicClosure F) hk l hlq, ?_⟩
  intro k0 hdiv b1 hb1 M hinj hM c hc hN
  obtain ⟨gD, ⟨D⟩⟩ := exists_degreeData Fq F (AlgebraicClosure F) hk
  obtain ⟨hg, hz⟩ := zeta_link Fq F (AlgebraicClosure F) hk D
  obtain ⟨P0, hP0c, hP0⟩ := hz c hc hN
  refine ⟨P0, hP0c, ?_⟩
  have hp : (ringChar Fq).Prime := CharP.char_is_prime Fq (ringChar Fq)
  have hpl : ringChar Fq ≠ l := fun h => not_ringChar_dvd Fq l hlq (by rw [h])
  have key := charpoly_eq_of_deg_ne D hp hpl hP0 (Matrix.toLin' M) fun P hP hd => by
    rw [aeval_toLin', LinearMap.det_toLin']
    exact norm_deg_eq_norm_det Fq F (AlgebraicClosure F) hk l k0 hlq hdiv b1 hb1 M hinj hM D (by rw [hg]) P hP hd
  rwa [Matrix.charpoly_toLin'] at key

end Main

end RamanujanPetersson.CoreB


end

-- ===== S4.Def_RP_CupDuality_KumPicDiv =====
section

/-!
# S4-CurveDuality, O5b (ii): `Pic⁰(X̄)` is `l^n`-divisible for `l ∤ q`

CB1 (`CoreB.divisible_Aℓ`) divides only the `l`-primary part. Here:
* `exists_pow_smul_of_torsion` (generic): in an abelian group whose `l`-primary part is `l`-divisible, a torsion element
  of a subgroup `H ⊇ G[l^∞]` is `l^n`-divisible inside `H`;
* `ofBar_mem_fixedBar`, **`torsion_PicBar0`**: `Pic⁰(X̄)` is torsion (each class lies in the finite `Pic⁰(X̄)^(π^m)`);
* **`pic0Bar_divisible`**, **`pic0K_divisible`**: every class of `Pic⁰(X̄)`, resp. of `Pic⁰(F̄ / k̄)`, is `l^n`-divisible.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.CupDuality

open RamanujanPetersson.JacAlg RamanujanPetersson.JacComplete RamanujanPetersson.JacFrob RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places RamanujanPetersson.CoreA

section Gen

variable {G : Type*} [AddCommGroup G]

end Gen

section Pic

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

/-- **`Pic⁰(X̄)` is `l^n`-divisible** (`l ∤ q`): torsion + CB1. -/
theorem pic0Bar_divisible (l : ℕ) [hl : Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq) (n : ℕ)
    (x : PicBar Ω hk) (hx : x ∈ PicBar0 Ω hk) : ∃ z ∈ PicBar0 Ω hk, l ^ n • z = x := by
  obtain ⟨m, hm, hmx⟩ := torsion_PicBar0 Fq F Ω hk x hx
  exact exists_pow_smul_of_torsion hl.out (CoreB.divisible_Aℓ Fq F Ω hk l hlq) (PicBar0 Ω hk)
    (primary_le_PicBar0 hk hl.out.ne_zero) hx hm hmx n

end Pic

end RamanujanPetersson.CupDuality


end

-- ===== S4.Def_RP_Lefschetz_PDiv1 =====
section

/-!
# S4-Lefschetz, L6e (1): a degree-zero divisor is `l^n`-divisible modulo principal divisors at a finite level

* `exists_div_level`: for `D` of degree `0` on `F_m = F · 𝔽_{q^m}` and `l ∤ q`, at some level `(j+1)!` (`m ≤ j`) the
  conorm of `D` is `l^n • z + div f` (`Pic⁰(X̄)` is `l^n`-divisible, `CupDuality.pic0Bar_divisible`, and the direct
  limit `Pic(X̄)` is reached at a finite level).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open PicDescent Places ZetaSB

section PicLevel

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

include hk in
/-- **A degree-zero divisor is `l^n`-divisible modulo principal divisors** at a finite level `(j+1)!` (`m ≤ j`). -/
theorem exists_div_level (l : ℕ) [Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq) (n : ℕ) (m : ℕ) [NeZero m]
    (D : Divisor (Lc Fq Ω m) (Fc Fq F Ω m)) (hD : Divisor.deg D = 0) :
    ∃ j : ℕ, ∃ hj : m ≤ j,
      haveI : Fact (m ∣ lev j) := ⟨dvd_lev (NeZero.pos m) hj⟩
      ∃ z : Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)), ∃ f : Fc Fq F Ω (lev j), f ≠ 0 ∧
        conormNN Ω hk m (lev j) D = l ^ n • z + (Places.div f : Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) := by
  have hx0 : toBar Ω hk m (QuotientAddGroup.mk D) ∈ PicBar0 Ω hk := by
    rw [mem_PicBar0, degBar_toBar, degPic_mk]
    exact hD
  obtain ⟨z', -, hz'⟩ := CupDuality.pic0Bar_divisible Fq F Ω hk l hlq n _ hx0
  obtain ⟨j1, y, hy⟩ := Kummer.exists_lev_toBar hk z'
  have hmJ : m ≤ m + lev j1 := Nat.le_add_right _ _
  have hj1J : lev j1 ≤ m + lev j1 := Nat.le_add_left _ _
  haveI : Fact (m ∣ lev (m + lev j1)) := ⟨dvd_lev (NeZero.pos m) hmJ⟩
  haveI : Fact (lev j1 ∣ lev (m + lev j1)) := ⟨dvd_lev (NeZero.pos _) hj1J⟩
  rw [toBar_eq hk m hmJ, ← hy, toBar_eq hk (lev j1) hj1J, ← map_nsmul] at hz'
  have hP := ofBar_injective hk (m + lev j1) hz'
  obtain ⟨zd, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [conNN_mk, conNN_mk, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq] at hP
  obtain ⟨f, hf, hdiv⟩ := (mem_princ _ _).1 hP
  refine ⟨m + lev j1, hmJ, conormNN Ω hk (lev j1) (lev (m + lev j1)) zd, f, hf, ?_⟩
  rw [hdiv]
  abel

end PicLevel

end

end Lefschetz
end RamanujanPetersson


end


