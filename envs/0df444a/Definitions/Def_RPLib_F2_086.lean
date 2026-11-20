-- Prove2me | Definitions.Def_RPLib_F2_086
-- name    : RPLib_F2_086
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T22:44:55.046279+00:00
-- url     : https://prove2.me/theorems/52cc96df-63bc-4920-984b-8c84a430376b
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 086 (part 1 of file 067 of 70)
-- statement:
--   File 086 (part 1 of file 067 of 70) of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_CP4`: S4-CP4: the unconditional Lefschetz point count (Core B discharged)
--   * `S4.Def_RP_Lefschetz_H1Les`: S4-Lefschetz, L3e2d1: `H¹_c` with constant coefficients is finite free
--   * `S4.Def_RP_Lefschetz_H1Sub`: S4-Lefschetz, L3e2d2: `H¹_c` of the ambient `G'`-cone is finite free
--   * `S4.Def_RP_Lefschetz_PDiv1b`: S4-Lefschetz, L6e (1b): any divisor is `l^n`-divisible modulo principal divisors at the finite places
--   * `S4.Def_RP_Lefschetz_PDiv1c`: S4-Lefschetz, L6e (1c): divisibility of base divisors at a finite constant level
--   * `S4.Def_RP_Lefschetz_ZFin2`: S4-Lefschetz, L6z (2): `Z¹(π₁^geo, ℤ/N)` is finite (full constant field)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_042
import Definitions.Def_RPLib_F2_054
import Definitions.Def_RPLib_F2_063
import Definitions.Def_RPLib_F2_066

/-!
# Ramanujan-Petersson curve library (flat edition), file 086 (part 1 of file 067 of 70)

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_CP4`: S4-CP4: the unconditional Lefschetz point count (Core B discharged)
* `S4.Def_RP_Lefschetz_H1Les`: S4-Lefschetz, L3e2d1: `H¹_c` with constant coefficients is finite free
* `S4.Def_RP_Lefschetz_H1Sub`: S4-Lefschetz, L3e2d2: `H¹_c` of the ambient `G'`-cone is finite free
* `S4.Def_RP_Lefschetz_PDiv1b`: S4-Lefschetz, L6e (1b): any divisor is `l^n`-divisible modulo principal divisors at the finite places
* `S4.Def_RP_Lefschetz_PDiv1c`: S4-Lefschetz, L6e (1c): divisibility of base divisors at a finite constant level
* `S4.Def_RP_Lefschetz_ZFin2`: S4-Lefschetz, L6z (2): `Z¹(π₁^geo, ℤ/N)` is finite (full constant field)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CP4 =====
section

/-!
# S4-CP4: the unconditional Lefschetz point count (Core B discharged)

The CP4 checkpoint. S4-CP4a proved the constant-coefficient Lefschetz trace formula for the affine chart
`U = Spec Rfin` of every function field `F/𝔽_q` with full constant field (a smooth geometrically connected curve)
ASSUMING Core B (`CP4a.CoreBHyp hk l`); S4-CoreB proved that hypothesis (`CoreB.coreBHyp_proved`). Here the two are
combined, so no hypothesis is left:
* `lefschetz_point_count`: for every Frobenius lift `φ` to `π₁(U)` and every `m ≥ 1`,
  `Tr(F^m | H²_c(Ū, ℤ/lⁿ)) - Tr(F^m | H¹_c(Ū, ℤ/lⁿ)) = #U(𝔽_{q^m})` in `ℤ/lⁿ` (`F` = geometric Frobenius `φ⁻¹`);
* `cp4_lefschetz`: the same, with a Frobenius lift that exists;
* `cp4_hyp`, `cp4_hyp_Fp`: the genus 2 curve `y² = x⁵ + 1` over `𝔽_q` (`2, 5 ≠ 0`) and over `𝔽_p` (`p ≠ 2, 5`),
  with `#U(𝔽_{q^m}) = #{(u, v) ∈ L² | v² = u⁵ + 1}`, `[L : 𝔽_q] = m`, and no curve-specific counting.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer GalCover CP4a

noncomputable section

section Main

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hk hq he in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **Lefschetz point count for `U`** (unconditional), for every Frobenius lift `φ`. -/
theorem lefschetz_point_count [Fintype (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F))]
    [DecidableEq (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F))]
    (l n : ℕ) [Fact l.Prime] (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq)
    (φ : Pi1 (Rfin Fq F) F) (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ)
    (m : ℕ) (hm : 1 ≤ m) (L : Type) [Field L] [Algebra Fq L] [Finite L] (hL : Module.finrank Fq L = m) :
    LinearMap.trace (ZMod N) (curveH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N))
        (geomFrobH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ ^ m) -
      LinearMap.trace (ZMod N) (curveH1c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) (bdryInf Fq F))
        (frobH1c (triv F (maxUnram (Rfin Fq F) F) N) (pi1geo (Rfin Fq F) F (Fintype.card Fq))
          (bdryInf Fq F).inertia φ⁻¹ (trueTau (bdryInf Fq F) φ⁻¹) (trueH (bdryInf Fq F) φ⁻¹)
          (trueCompat (bdryInf Fq F) φ⁻¹) ^ m) =
      (Nat.card (Rfin Fq F →ₐ[Fq] L) : ZMod N) :=
  CP4a.lefschetz_point_count hk hq he l n hn hN hlq (CoreB.coreBHyp_proved hk l hlq) φ hφ m hm L hL

end Main

section Hyp

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)] [Fact ((2 : Fq) ≠ 0)]

end Hyp

end

end RamanujanPetersson.CP4


end

-- ===== S4.Def_RP_Lefschetz_H1Les =====
section

/-!
# S4-Lefschetz, L3e2d1: `H¹_c` with constant coefficients is finite free

* `free_finite_of_les`: in an exact `0 → H₀ → B → C → P → 0` with `B` finite, `B / H₀` free and `P` finite free,
  `C` is finite free (`C ≅ B / H₀ × P`: the sequence splits since `P` is projective).
* `free_H1c_triv`: `H¹_c(Γ, {I_s}; Λ)` is finite free when `H¹_par` is (`0 → H⁰ → ⊕_s Λ → H¹_c → H¹_par → 0`).
* `free_curveH1c`: for a curve `U/𝔽_q` with full constant field, `H¹_c(Ū, ℤ/l^n)` is finite free (CP4a's
  `free_curveH1par` with Core B discharged by `CoreB.coreBHyp_proved`, as in `CP4.lefschetz_point_count`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer GalCover CP4a

section Les

variable {R : Type*} [CommRing R]

end Les

section Pair

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)

end Pair

section Curve

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hk hq he in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **`H¹_c(Ū, ℤ/l^n)` is finite free** (unconditional: Core B from `CoreB.coreBHyp_proved`). -/
theorem free_curveH1c [Fintype (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F))]
    [DecidableEq (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F))]
    (l n : ℕ) [Fact l.Prime] {N : ℕ} [NeZero N] (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq) :
    Module.Free (ZMod N) (H1c (Representation.trivial (ZMod N) (Pi1 (Rfin Fq F) F) (ZMod N))
        (pi1geo (Rfin Fq F) F (Fintype.card Fq)) (bdryInf Fq F).inertia) ∧
      Module.Finite (ZMod N) (H1c (Representation.trivial (ZMod N) (Pi1 (Rfin Fq F) F) (ZMod N))
        (pi1geo (Rfin Fq F) F (Fintype.card Fq)) (bdryInf Fq F).inertia) := by
  have hNF : (N : F) ≠ 0 := by
    rw [hN]
    exact cast_ne_zero_of_not_dvd hq he hlq n
  obtain ⟨ζ, hζ, hζΓ⟩ := exists_zeta_geo hq he hNF
  have := nonempty_bdryS (Fq := Fq) (F := F)
  exact free_H1c_triv (pi1geo (Rfin Fq F) F (Fintype.card Fq)) (bdryInf Fq F).inertia
    (free_curveH1par hk hq he (isUnit_cast_Rfin hNF) (isUnit_cast_Rinf hNF) hζ hζΓ (bdryInf Fq F)
      (bdryData_B _ _ _ _) bdryLift hNF l n hN hlq (CoreB.coreBHyp_proved hk l hlq))

end Curve

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_H1Sub =====
section

/-!
# S4-Lefschetz, L3e2d2: `H¹_c` of the ambient `G'`-cone is finite free

For `H = range thetaE ≤ G'` and `G' = H·Γ`: Shapiro inside `G'` (`shapiroH1cEquiv` with the `_sub` data), the ambient
transport (`h1cTr (intw_sub ..)`) and the chart (`h1cTr (intwE ..)`) give
`h1cSubEquiv : H¹_c(Γ ∩ G'; Ind_{H}^{G'} Λ) ≃ H¹_c(E, Λ)` (the linear equivalence behind `trace_cover_sub`), so
`free_h1cSub`: the left side is finite free over `ℤ/l^n` (`free_curveH1c` for `E` over its constant field).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a CupDuality Representation

section H1Sub

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **`H¹_c(Γ ∩ G'; Ind_H^{G'} ℤ/l^n)` is finite free** (`H = range thetaE`, `G' = H·Γ`). -/
theorem free_h1cSub (l n : ℕ) [Fact l.Prime] {N : ℕ} [NeZero N] (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq)
    {G' : Subgroup (Pi1 (Rfin Fq K) K)}
    (hΓ : pi1geo (Rfin Fq K) K (Fintype.card Fq) ≤ G') (hH : (thetaE Fq K E hE).range ≤ G')
    (hcov' : ∀ x ∈ G', ∃ a ∈ (thetaE Fq K E hE).range, ∃ b ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq), x = a * b)
    (R : CosetReps (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (thetaE Fq K E hE).range) :
    Module.Free (ZMod N) (H1c (pushRep ((thetaE Fq K E hE).range.subgroupOf G')
        ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
          (downH (thetaE Fq K E hE).range G')))
      (geoU (pi1geo (Rfin Fq K) K (Fintype.card Fq)) G') (fun s => ((bdryInf Fq K).inertia s).subgroupOf G')) ∧
    Module.Finite (ZMod N) (H1c (pushRep ((thetaE Fq K E hE).range.subgroupOf G')
        ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
          (downH (thetaE Fq K E hE).range G')))
      (geoU (pi1geo (Rfin Fq K) K (Fintype.card Fq)) G') (fun s => ((bdryInf Fq K).inertia s).subgroupOf G')) := by
  have : CharP E p := charP_of_injective_algebraMap (algebraMap K E).injective p
  have hc := card_Kc Fq E p
  obtain ⟨e', he', hqE⟩ := hc
  have := finite_bdryS (Fq := Kc Fq E) (F := E) hqE he'
  let := Fintype.ofFinite (BdryS (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) (Rinf (Kc Fq E) E))
  let : DecidableEq (BdryS (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) (Rinf (Kc Fq E) E)) :=
    Classical.decEq _
  have hF := free_curveH1c (Fq := Kc Fq E) (F := E) (constField_eq_bot Fq E) hqE he' l n hN (hlq_Kc Fq K E l hlq)
  obtain ⟨_, _⟩ := hF
  let eq := h1cSubEquiv Fq K E hE hq he N hΓ hH hcov' R
  exact ⟨Module.Free.of_equiv eq.symm, Module.Finite.equiv eq.symm⟩

end H1Sub

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PDiv1b =====
section

/-!
# S4-Lefschetz, L6e (1b): any divisor is `l^n`-divisible modulo principal divisors at the finite places

* `exists_fin_div_level`: for any divisor `D` on `F_m` and `l ∤ q`, at some level `(j+1)!` (`m ≤ j`) the conorm of
  `D` agrees with `l^n • z + div f` at every finite place. A degree-one place at infinity (at a large level,
  `JacFrob.degOne`) absorbs the degree of `D`, and `exists_div_level` handles the degree-zero remainder.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open PicDescent Places ZetaSB

section PicFin

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

include hk in
/-- **Any divisor is `l^n`-divisible modulo principal divisors at the finite places** of a finite level. -/
theorem exists_fin_div_level (l : ℕ) [Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq) (n : ℕ) (m : ℕ) [NeZero m]
    (D : Divisor (Lc Fq Ω m) (Fc Fq F Ω m)) :
    ∃ j : ℕ, ∃ hj : m ≤ j,
      haveI : Fact (m ∣ lev j) := ⟨dvd_lev (NeZero.pos m) hj⟩
      ∃ z : Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)), ∃ f : Fc Fq F Ω (lev j), f ≠ 0 ∧
        ∀ v : IsDedekindDomain.HeightOneSpectrum (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))),
          conormNN Ω hk m (lev j) D (Sum.inl v) =
            (l ^ n • z + (Places.div f : Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)))) (Sum.inl v) := by
  obtain ⟨M0, Q, hQr, hQdeg⟩ := exists_inf_degOne Fq F Ω hk
  have hmJ : m ≤ m + M0 := Nat.le_add_right _ _
  have hM0J : M0 ≤ m + M0 := Nat.le_add_left _ _
  haveI : Fact (m ∣ lev (m + M0)) := ⟨dvd_lev (NeZero.pos m) hmJ⟩
  haveI : Fact (lev M0 ∣ lev (m + M0)) := ⟨lev_dvd hM0J⟩
  have hWdeg : Divisor.deg (conormNN Ω hk (lev M0) (lev (m + M0)) (Finsupp.single Q 1)) = 1 := by
    have h1 := deg_conorm (isConstExt_pair Fq F Ω hk (n := lev M0) (N := lev (m + M0))) (Finsupp.single Q 1)
    refine h1.trans ?_
    rw [Divisor.deg_single, hQdeg]
    norm_num
  have hWinl : ∀ c : IsDedekindDomain.HeightOneSpectrum (Rfin (Lc Fq Ω (lev (m + M0))) (Fc Fq F Ω (lev (m + M0)))),
      conormNN Ω hk (lev M0) (lev (m + M0)) (Finsupp.single Q 1) (Sum.inl c) = 0 := by
    intro c
    classical
    rw [conormNN_apply, Finsupp.single_apply, if_neg]
    intro hc
    have h1 : (contractNN Ω hk (lev M0) (lev (m + M0)) (Sum.inl c)).isLeft = true := by
      rw [isLeft_contractNN]
      rfl
    rw [← hc, hQr] at h1
    exact Bool.false_ne_true h1
  have hD2 : Divisor.deg (conormNN Ω hk m (lev (m + M0)) D -
      Divisor.deg (conormNN Ω hk m (lev (m + M0)) D) •
        conormNN Ω hk (lev M0) (lev (m + M0)) (Finsupp.single Q 1)) = 0 := by
    rw [Divisor.deg_sub, ZetaSB.deg_zsmul, hWdeg, mul_one, sub_self]
  obtain ⟨j, hj, z, f, hf, heq⟩ := exists_div_level Fq F Ω hk l hlq n (lev (m + M0)) _ hD2
  have hmj : m ≤ j :=
    le_trans hmJ (le_trans (le_trans (Nat.le_succ _) (Nat.self_le_factorial _)) hj)
  have : Fact (m ∣ lev j) := ⟨dvd_lev (NeZero.pos m) hmj⟩
  refine ⟨j, hmj, z, f, hf, fun v => ?_⟩
  have : Fact (lev (m + M0) ∣ lev j) := ⟨dvd_lev (NeZero.pos _) hj⟩
  have hc := JacFrob.contractNN_inl Fq F Ω hk (n := lev (m + M0)) (N := lev j) v
  rw [← heq, conormNN_apply, conormNN_apply, Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_smul, Pi.smul_apply,
    hc, hWinl, smul_zero, sub_zero, ← hc, conormNN_apply, contractNN_trans]

end PicFin

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PDiv1c =====
section

/-!
# S4-Lefschetz, L6e (1c): divisibility of base divisors at a finite constant level

For a divisor `D` on the base `F` (constant field `Fq`, `hk`) and `l ∤ q`, at some level `(j+1)!`:
* `exists_base_fin_div`: `D ∘ contract = l^n • z + div f` at every finite place of `F_{(j+1)!}`;
* `exists_base_div0`: if `deg D = 0`, `D ∘ contract = l^n • z + div f` at every place.
Here `contract` is the contraction of the constant field extension `F_N / F` (`isConstExt_Fc`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open PicDescent Places ZetaSB

section PicBase

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)

variable [IsAlgClosed Ω]

include hk in
/-- **Any base divisor is `l^n`-divisible modulo principal divisors at the finite places** of a finite level. -/
theorem exists_base_fin_div (l : ℕ) [Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq) (n : ℕ) (D : Divisor Fq F) :
    ∃ j : ℕ, ∃ z : Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)), ∃ f : Fc Fq F Ω (lev j), f ≠ 0 ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))),
        D (contract (isConstExt_Fc Fq F Ω hk (lev j)) (Sum.inl v)) =
          (l ^ n • z + (Places.div f : Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)))) (Sum.inl v) := by
  obtain ⟨j, hj, z, f, hf, h⟩ := exists_fin_div_level Fq F Ω hk l hlq n 1 (conorm (isConstExt_Fc Fq F Ω hk 1) D)
  have : Fact (1 ∣ lev j) := ⟨one_dvd _⟩
  refine ⟨j, z, f, hf, fun v => ?_⟩
  rw [← h v, conormNN_apply, conorm_apply, contract_Fc_trans]

include hk in
/-- **A degree-zero base divisor is `l^n`-divisible modulo principal divisors** at a finite level. -/
theorem exists_base_div0 (l : ℕ) [Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq) (n : ℕ) (D : Divisor Fq F)
    (hD : Divisor.deg D = 0) :
    ∃ j : ℕ, ∃ z : Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)), ∃ f : Fc Fq F Ω (lev j), f ≠ 0 ∧
      ∀ P : Place (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)),
        D (contract (isConstExt_Fc Fq F Ω hk (lev j)) P) =
          (l ^ n • z + (Places.div f : Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)))) P := by
  have hD1 : Divisor.deg (conorm (isConstExt_Fc Fq F Ω hk 1) D) = 0 := by
    rw [deg_conorm, hD]
  obtain ⟨j, hj, z, f, hf, h⟩ := exists_div_level Fq F Ω hk l hlq n 1 _ hD1
  have : Fact (1 ∣ lev j) := ⟨one_dvd _⟩
  refine ⟨j, z, f, hf, fun P => ?_⟩
  rw [← h, conormNN_apply, conorm_apply, contract_Fc_trans]

end PicBase

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ZFin2 =====
section

/-!
# S4-Lefschetz, L6z (2): `Z¹(π₁^geo, ℤ/N)` is finite (full constant field)

* `finite_homLC_of_gen`: locally constant homomorphisms `J → ℤ/N` determined by their value at `τ` form a finite set.
* `finite_Z1_triv_of_eq`, `finite_homLC_of_Z1`: `Z¹(Δ, Λ)` (trivial action) and `Hom_lc(Δ, Λ)` are the same set.
* `finite_Z1_geo`: for a curve `U/𝔽_q` with full constant field, `Z¹(π₁^geo, ℤ/l^n)` is finite: `H¹_c` is finite
  (`free_curveH1c`) and each inertia group has a tame generator (`exists_norm_tau_fin` with `π = 1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places CurveCoh Kummer GalCover CP4a Residue PerfectCx

section Gen

variable {G : Type} [Group G] [TopologicalSpace G]

variable {Λ : Type} [CommRing Λ]

end Gen

section Base

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hk hq he in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **`Z¹(π₁^geo, ℤ/l^n)` is finite** for a curve with full constant field. -/
theorem finite_Z1_geo [Fintype (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F))]
    [DecidableEq (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F))]
    (l n : ℕ) [Fact l.Prime] {N : ℕ} [NeZero N] (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq) :
    Finite (Z1 (Representation.trivial (ZMod N) (Pi1 (Rfin Fq F) F) (ZMod N))
      (pi1geo (Rfin Fq F) F (Fintype.card Fq))) := by
  have hNF : (N : F) ≠ 0 := by
    rw [hN]
    exact cast_ne_zero_of_not_dvd hq he hlq n
  obtain ⟨_, hfin⟩ := free_curveH1c hk hq he l n hN hlq
  have hH := Module.finite_of_finite (ZMod N) (M := H1c (Representation.trivial (ZMod N) (Pi1 (Rfin Fq F) F)
    (ZMod N)) (pi1geo (Rfin Fq F) F (Fintype.card Fq)) (bdryInf Fq F).inertia)
  exact finite_Z1_triv _ _ hH (finite_Z1_triv_inertia hq he hNF)

include hk hq he in
/-- `Hom_lc(π₁^geo, ℤ/l^n)` is finite for a curve with full constant field. -/
theorem finite_homLC_geo [Fintype (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F))]
    [DecidableEq (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F))]
    (l n : ℕ) [Fact l.Prime] {N : ℕ} [NeZero N] (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq) :
    Finite (HomLC (pi1geo (Rfin Fq F) F (Fintype.card Fq)) (ZMod N)) :=
  finite_homLC_of_Z1 _ (finite_Z1_geo hk hq he l n hN hlq)

end Base

end

end Lefschetz
end RamanujanPetersson


end


