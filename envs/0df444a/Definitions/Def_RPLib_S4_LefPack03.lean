-- Prove2me | Definitions.Def_RPLib_S4_LefPack03
-- name    : RPLib_S4_LefPack03
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T20:50:21.037205+00:00
-- url     : https://prove2.me/theorems/e62d5874-1abe-4026-857e-9bf413c7cb8a
-- title:
--   Lefschetz trace formula library (Grothendieck–Lefschetz trace formula mod ℓⁿ on curves over finite fields), part 3 of 32
-- statement:
--   Part 3 of 32 of the Lefschetz trace formula library: the following library modules, in dependency order.
--
--   * `Def_RP_CP4a_HypE`: S4-CP4a, part g5: the affine points of `y² = x⁵ + 1`
--   * `Def_RP_CP4a`: S4-CP4a: the Lefschetz point count for `y² = x⁵ + 1` (Core B as a hypothesis)
--
--   **Formalization note.** Library package of a formalization of the Grothendieck–Lefschetz trace formula modulo $\ell^n$ for a lisse sheaf of free $\mathbb Z/\ell^n$-modules on an affine curve over a finite field, on the compactly supported cochain complex of the geometric fundamental group. The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Formule de Lefschetz et rationalité des fonctions L, Séminaire Bourbaki, exposé 279 (1964/65); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Rapport sur la formule des traces »; J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §13

import Mathlib
import Definitions.Def_RPLib_S4_LefPack02

/-!
# Lefschetz trace formula library package, part 3 of 32

Library modules of the formalization of the Grothendieck-Lefschetz trace formula mod `l^n` for lisse sheaves on an
affine curve over a finite field (`RamanujanPetersson.Lefschetz.lefschetz_main`). Each module below is copied
verbatim (import lines removed) inside its own `section` ... `end`:

* `Def_RP_CP4a_HypE`: S4-CP4a, part g5: the affine points of `y² = x⁵ + 1`
* `Def_RP_CP4a`: S4-CP4a: the Lefschetz point count for `y² = x⁵ + 1` (Core B as a hypothesis)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CP4a_HypE =====
section

/-!
# S4-CP4a, part g5: the affine points of `y² = x⁵ + 1`

`Rfin = 𝔽_q[x, y]/(y² - x⁵ - 1)` (`eRfin`, from the integral closure `isIntegral_iff` of part g2), so for every
`𝔽_q`-algebra `L`, `Hom_{𝔽_q}(Rfin, L) ≃ {(u, v) ∈ L² | v² = u⁵ + 1}` (`homEquiv`, `card_hom_hyp`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.CP4a.Hyp2

open Places

noncomputable section

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)] [Fact ((2 : Fq) ≠ 0)]

/-- The defining polynomial `Y² - (x⁵ + 1)` over `Fq[x]`. -/
abbrev gY : Fq[X][X] := X ^ 2 - C (f0 Fq)

theorem monic_gY : (gY Fq).Monic := monic_X_pow_sub_C _ two_ne_zero

theorem natDegree_gY : (gY Fq).natDegree = 2 := natDegree_X_pow_sub_C

/-- Every element of `Fq[x][Y]/(gY)` is `a + b Y`. -/
theorem exists_ab (z : AdjoinRoot (gY Fq)) :
    ∃ a b : Fq[X], z = AdjoinRoot.of (gY Fq) a + AdjoinRoot.of (gY Fq) b * AdjoinRoot.root (gY Fq) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  have hm : AdjoinRoot.mk (gY Fq) (p %ₘ gY Fq) = AdjoinRoot.mk (gY Fq) p := by
    rw [← AdjoinRoot.modByMonicHom_mk (monic_gY Fq)]
    exact AdjoinRoot.mk_leftInverse (monic_gY Fq) _
  have hd : (p %ₘ gY Fq).natDegree ≤ 1 := by
    have h1 : gY Fq ≠ 1 := by
      intro h
      have := natDegree_gY Fq
      rw [h, natDegree_one] at this
      exact absurd this (by norm_num)
    have := natDegree_modByMonic_lt p (monic_gY Fq) h1
    rw [natDegree_gY] at this
    omega
  refine ⟨(p %ₘ gY Fq).coeff 0, (p %ₘ gY Fq).coeff 1, ?_⟩
  conv_lhs => rw [← hm, eq_X_add_C_of_natDegree_le_one hd]
  rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  ring

theorem eval_gY_yF : (gY Fq).eval₂ (algebraMap Fq[X] (HypF Fq)) (yF Fq) = 0 := by
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, hy, algebraMap_poly, sub_self]

/-- `Fq[x][Y]/(gY) → HypF`, `Y ↦ y`. -/
abbrev toF : AdjoinRoot (gY Fq) →ₐ[Fq[X]] HypF Fq :=
  AdjoinRoot.liftAlgHom (gY Fq) (Algebra.ofId Fq[X] (HypF Fq)) (yF Fq) (eval_gY_yF Fq)

theorem toF_of (r : Fq[X]) : toF Fq (AdjoinRoot.of (gY Fq) r) = algebraMap Fq[X] (HypF Fq) r :=
  AdjoinRoot.liftAlgHom_of _ _ _ _ r

theorem toF_root : toF Fq (AdjoinRoot.root (gY Fq)) = yF Fq :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem toF_ab (a b : Fq[X]) :
    toF Fq (AdjoinRoot.of (gY Fq) a + AdjoinRoot.of (gY Fq) b * AdjoinRoot.root (gY Fq)) = cP Fq a b := by
  rw [map_add, map_mul, toF_of, toF_of, toF_root]

theorem toF_mem (z : AdjoinRoot (gY Fq)) : toF Fq z ∈ FunctionField.ringOfIntegers Fq (HypF Fq) := by
  obtain ⟨a, b, rfl⟩ := exists_ab Fq z
  rw [toF_ab]
  exact (mem_integralClosure_iff _ _).mpr (isIntegral_cP Fq a b)

/-- `Fq[x][Y]/(gY) → Rfin`. -/
abbrev toRfin : AdjoinRoot (gY Fq) →ₐ[Fq[X]] Rfin Fq (HypF Fq) :=
  (toF Fq).codRestrict (FunctionField.ringOfIntegers Fq (HypF Fq)) (toF_mem Fq)

theorem toRfin_bijective (h5 : (5 : Fq) ≠ 0) : Function.Bijective (toRfin Fq) := by
  refine ⟨fun z₁ z₂ h => ?_, fun z => ?_⟩
  · obtain ⟨a, b, rfl⟩ := exists_ab Fq z₁
    obtain ⟨a', b', rfl⟩ := exists_ab Fq z₂
    have h' := congrArg (fun r : Rfin Fq (HypF Fq) => (r : HypF Fq)) h
    simp only [AlgHom.coe_codRestrict] at h'
    rw [toF_ab, toF_ab] at h'
    obtain ⟨rfl, rfl⟩ := cP_inj Fq h'
    rfl
  · obtain ⟨a, b, hab⟩ := (isIntegral_iff Fq Fact.out h5 (z : HypF Fq)).mp ((mem_integralClosure_iff _ _).mp z.2)
    refine ⟨AdjoinRoot.of (gY Fq) a + AdjoinRoot.of (gY Fq) b * AdjoinRoot.root (gY Fq), Subtype.ext ?_⟩
    simp only [AlgHom.coe_codRestrict]
    rw [toF_ab, hab]

/-- **`Rfin = Fq[x, y]/(y² - x⁵ - 1)`** (over `Fq[x]`). -/
def eRfin (h5 : (5 : Fq) ≠ 0) : AdjoinRoot (gY Fq) ≃ₐ[Fq[X]] Rfin Fq (HypF Fq) :=
  AlgEquiv.ofBijective (toRfin Fq) (toRfin_bijective Fq h5)

/-- `Rfin = Fq[x, y]/(y² - x⁵ - 1)` over `Fq`. -/
def eRfinFq (h5 : (5 : Fq) ≠ 0) : AdjoinRoot (gY Fq) ≃ₐ[Fq] Rfin Fq (HypF Fq) :=
  (eRfin Fq h5).restrictScalars Fq

theorem root_sq : AdjoinRoot.root (gY Fq) ^ 2 = AdjoinRoot.of (gY Fq) (f0 Fq) := by
  have h := AdjoinRoot.eval₂_root (gY Fq)
  rwa [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h

/-- **`L`-points**: `Hom_{Fq}(Fq[x][Y]/(gY), L) ≃ {(u, v) | v² = u⁵ + 1}`. -/
def homEquiv (L : Type) [CommRing L] [Algebra Fq L] :
    (AdjoinRoot (gY Fq) →ₐ[Fq] L) ≃ {q : L × L // q.2 ^ 2 = q.1 ^ 5 + 1} where
  toFun ψ := ⟨(ψ (AdjoinRoot.of (gY Fq) X), ψ (AdjoinRoot.root (gY Fq))), by
    have h := congrArg ψ (root_sq Fq)
    simpa [f0, map_pow, map_add, map_one] using h⟩
  invFun q := AdjoinRoot.liftAlgHom (gY Fq) (aeval q.1.1) q.1.2 (by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, q.2]
    simp [f0])
  left_inv ψ := by
    dsimp only
    refine AdjoinRoot.algHom_ext' (Polynomial.algHom_ext ?_) ?_
    · simp
    · simp
  right_inv q := by
    apply Subtype.ext
    simp

/-- **Point count**: `#Hom_{Fq}(Rfin, L) = #{(u, v) ∈ L² | v² = u⁵ + 1}`. -/
theorem card_hom_hyp (h5 : (5 : Fq) ≠ 0) (L : Type) [Field L] [Algebra Fq L] :
    Nat.card (Rfin Fq (HypF Fq) →ₐ[Fq] L) = Nat.card {q : L × L // q.2 ^ 2 = q.1 ^ 5 + 1} :=
  Nat.card_congr (((eRfinFq Fq h5).arrowCongr (AlgEquiv.refl : L ≃ₐ[Fq] L)).symm.trans (homEquiv Fq L))

end

end RamanujanPetersson.CP4a.Hyp2

end

-- ===== S4.Def_RP_CP4a =====
section

/-!
# S4-CP4a: the Lefschetz point count for `y² = x⁵ + 1` (Core B as a hypothesis)

The CP4a milestone. The generic part (`cp4a_lefschetz`, `lefschetz_point_count` in `Def_RP_CP4a_Main`) proves, for
every function field `F/𝔽_q` with full constant field and its affine chart `U = Spec Rfin`, ASSUMING Core B
(`CoreBHyp`, a Prop argument):
`Tr(F^m | H²_c(Ū, ℤ/lⁿ)) - Tr(F^m | H¹_c(Ū, ℤ/lⁿ)) = #U(𝔽_{q^m})` for all `m ≥ 1`.

Here it is instantiated for the genus 2 curve `y² = x⁵ + 1` over any finite field of characteristic `≠ 2, 5`
(`cp4a_hyp`), and over `𝔽_p`, `p ≠ 2, 5` (`cp4a_hyp_Fp`), with NO curve-specific counting:
* `constField_hyp` (part g3): the full constant field is `𝔽_q` (unique place at infinity, of degree 1);
* `genus_hyp` (part g4): the genus is 2 (S3 Riemann-Roch on `L(2k P_∞)`);
* `card_hom_hyp` (part g5): `U(L) = {(u, v) ∈ L² | v² = u⁵ + 1}` (`Rfin = 𝔽_q[x, y]/(y² - x⁵ - 1)`).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a.Hyp2

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer GalCover

noncomputable section

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)] [Fact ((2 : Fq) ≠ 0)]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **CP4a for `y² = x⁵ + 1`** (Core B as a hypothesis): over `𝔽_q` with `2, 5 ≠ 0`, the curve has genus 2, a
Frobenius lift `φ` exists, and for every `m ≥ 1` and every `L/𝔽_q` of degree `m`,
`Tr(F^m | H²_c) - Tr(F^m | H¹_c) = #{(u, v) ∈ L² | v² = u⁵ + 1}` in `ℤ/lⁿ`. -/
theorem cp4a_hyp {p e : ℕ} [Fact p.Prime] [CharP Fq p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
    (h5 : (5 : Fq) ≠ 0)
    (l n : ℕ) [Fact l.Prime] (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq)
    (hB : CoreBHyp (constField_hyp Fq) l) :
    genusF Fq (HypF Fq) = 2 ∧
    ∃ φ : Pi1 (Rfin Fq (HypF Fq)) (HypF Fq), IsFrobLift (Rfin Fq (HypF Fq)) (HypF Fq) (Fintype.card Fq) φ ∧
      ∀ m : ℕ, 1 ≤ m → ∀ (L : Type) [Field L] [Algebra Fq L] [Finite L], Module.finrank Fq L = m →
      LinearMap.trace (ZMod N)
          (curveH2c (Fintype.card Fq) (triv (HypF Fq) (maxUnram (Rfin Fq (HypF Fq)) (HypF Fq)) N))
          (geomFrobH2c (Fintype.card Fq) (triv (HypF Fq) (maxUnram (Rfin Fq (HypF Fq)) (HypF Fq)) N) φ ^ m) -
        LinearMap.trace (ZMod N)
          (curveH1c (Fintype.card Fq) (triv (HypF Fq) (maxUnram (Rfin Fq (HypF Fq)) (HypF Fq)) N)
            (bdryInf Fq (HypF Fq)))
          (frobH1c (triv (HypF Fq) (maxUnram (Rfin Fq (HypF Fq)) (HypF Fq)) N)
            (pi1geo (Rfin Fq (HypF Fq)) (HypF Fq) (Fintype.card Fq))
            (bdryInf Fq (HypF Fq)).inertia φ⁻¹ (trueTau (bdryInf Fq (HypF Fq)) φ⁻¹)
            (trueH (bdryInf Fq (HypF Fq)) φ⁻¹) (trueCompat (bdryInf Fq (HypF Fq)) φ⁻¹) ^ m) =
        (Nat.card {q : L × L // q.2 ^ 2 = q.1 ^ 5 + 1} : ZMod N) := by
  refine ⟨genus_hyp Fq h5, ?_⟩
  haveI hfin := finite_bdryS (Fq := Fq) (F := HypF Fq) hq he
  letI := @Fintype.ofFinite _ hfin
  classical
  have key := cp4a_lefschetz (constField_hyp Fq) hq he l n hn hN hlq hB
  obtain ⟨φ, hφ, h⟩ := key
  exact ⟨φ, hφ, fun m hm L _ _ _ hL =>
    (h m hm L hL).trans (congrArg (fun k : ℕ => (k : ZMod N)) (card_hom_hyp Fq h5 L))⟩

/-- `2 ≠ 0` in `𝔽_p` for `p ≠ 2`. -/
instance fact_two_ne_zero_zmod (p : ℕ) [Fact p.Prime] [Fact (p ≠ 2)] : Fact ((2 : ZMod p) ≠ 0) :=
  ⟨fun h => by
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact (Fact.out : p ≠ 2) ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2)⟩

theorem five_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp5 : p ≠ 5) : (5 : ZMod p) ≠ 0 := fun h => by
  have h2 : ((5 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).1 h2)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **CP4a for `y² = x⁵ + 1` over `𝔽_p`, `p ≠ 2, 5`** (Core B as a hypothesis). -/
theorem cp4a_hyp_Fp (p : ℕ) [Fact p.Prime] [Fact (p ≠ 2)] (hp5 : p ≠ 5) [DecidableEq (RatFunc (ZMod p))]
    (l n : ℕ) [Fact l.Prime] (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = l ^ n) (hlp : l ≠ p)
    (hB : CoreBHyp (constField_hyp (ZMod p)) l) :
    genusF (ZMod p) (HypF (ZMod p)) = 2 ∧
    ∃ φ : Pi1 (Rfin (ZMod p) (HypF (ZMod p))) (HypF (ZMod p)),
      IsFrobLift (Rfin (ZMod p) (HypF (ZMod p))) (HypF (ZMod p)) (Fintype.card (ZMod p)) φ ∧
      ∀ m : ℕ, 1 ≤ m → ∀ (L : Type) [Field L] [Algebra (ZMod p) L] [Finite L], Module.finrank (ZMod p) L = m →
      LinearMap.trace (ZMod N)
          (curveH2c (Fintype.card (ZMod p)) (triv (HypF (ZMod p)) (maxUnram (Rfin (ZMod p) (HypF (ZMod p)))
            (HypF (ZMod p))) N))
          (geomFrobH2c (Fintype.card (ZMod p)) (triv (HypF (ZMod p)) (maxUnram (Rfin (ZMod p) (HypF (ZMod p)))
            (HypF (ZMod p))) N) φ ^ m) -
        LinearMap.trace (ZMod N)
          (curveH1c (Fintype.card (ZMod p)) (triv (HypF (ZMod p)) (maxUnram (Rfin (ZMod p) (HypF (ZMod p)))
            (HypF (ZMod p))) N) (bdryInf (ZMod p) (HypF (ZMod p))))
          (frobH1c (triv (HypF (ZMod p)) (maxUnram (Rfin (ZMod p) (HypF (ZMod p))) (HypF (ZMod p))) N)
            (pi1geo (Rfin (ZMod p) (HypF (ZMod p))) (HypF (ZMod p)) (Fintype.card (ZMod p)))
            (bdryInf (ZMod p) (HypF (ZMod p))).inertia φ⁻¹ (trueTau (bdryInf (ZMod p) (HypF (ZMod p))) φ⁻¹)
            (trueH (bdryInf (ZMod p) (HypF (ZMod p))) φ⁻¹) (trueCompat (bdryInf (ZMod p) (HypF (ZMod p))) φ⁻¹) ^ m) =
        (Nat.card {q : L × L // q.2 ^ 2 = q.1 ^ 5 + 1} : ZMod N) := by
  have hq : Fintype.card (ZMod p) = p ^ 1 := by rw [ZMod.card, pow_one]
  have hlq : ¬ l ∣ Fintype.card (ZMod p) := by
    rw [ZMod.card]
    intro hd
    exact hlp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1 hd)
  exact cp4a_hyp (ZMod p) hq one_pos (five_ne_zero_zmod p hp5) l n hn hN hlq hB

end

end RamanujanPetersson.CP4a.Hyp2

end


