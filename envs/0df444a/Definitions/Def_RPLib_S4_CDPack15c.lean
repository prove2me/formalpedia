-- Prove2me | Definitions.Def_RPLib_S4_CDPack15c
-- name    : RPLib_S4_CDPack15c
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:45:22.6482+00:00
-- url     : https://prove2.me/theorems/c48b38a9-d3f7-434e-80b5-1ac4ac47096c
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 15c of 71
-- statement:
--   Part 15c of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_CP4a_FrobLift`: S4-CP4a, part f1 + f2: the constants and an arithmetic Frobenius lift exist
--   * `Def_RP_CupDuality_GysD`: S4-CurveDuality O4G-4: `π₁(U) = φ^ℕ · π₁^geo · N` for every open `N`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack14b
import Definitions.Def_RPLib_S4_CP4aLift
import Definitions.Def_RPLib_S4_CDPack09c

/-!
# Curve-duality library package, part 15c of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_CP4a_FrobLift`: S4-CP4a, part f1 + f2: the constants and an arithmetic Frobenius lift exist
* `Def_RP_CupDuality_GysD`: S4-CurveDuality O4G-4: `π₁(U) = φ^ℕ · π₁^geo · N` for every open `N`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CP4a_FrobLift =====
section

/-!
# S4-CP4a, part f1 + f2: the constants and an arithmetic Frobenius lift exist

For a function field `F/𝔽_q` (`q = p ^ e`) with `constField = 𝔽_q`:
* `cast_ne_zero_of_not_dvd`, `isUnit_cast_Rfin`, `isUnit_cast_Rinf`: `N = l ^ n` with `l ∤ q` is a unit;
* `exists_zeta_geo`: a primitive `N`-th root of unity `ζ ∈ K_U` fixed by `π₁^geo`;
* `exists_zeta_level`: primitive `(q ^ a - 1)`-th roots of unity in `K_U`;
* `exists_frobLift`: there is `φ ∈ π₁(U)` with `φ x = x ^ q` on all constants (a compactness argument over the
  closed sets `T_m = {σ | σ x = x ^ q whenever x ^ (q ^ m) = x}`, each nonempty by lifting `frobF` on `F_m`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.CP4a

open Places PicDescent CurveCoh Kummer GalCover

noncomputable section

section FrobSet

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

theorem pow_pow_iter {M : Type*} [Monoid M] {x : M} {n : ℕ} (h : x ^ n = x) (b : ℕ) : x ^ n ^ b = x := by
  induction b with
  | zero => rw [pow_zero, pow_one]
  | succ b ih => rw [pow_succ, pow_mul, ih, h]

/-- `{σ | σ x = y}` is closed in `π₁(U)`. -/
theorem isClosed_setOf_apply_eq (x y : maxUnram A K) : IsClosed {σ : Pi1 A K | σ x = y} := by
  by_cases h : ∃ σ0 : Pi1 A K, σ0 x = y
  · obtain ⟨σ0, hσ0⟩ := h
    have hs : {σ : Pi1 A K | σ x = y} = (fun σ => σ0⁻¹ * σ) ⁻¹' (fixElt A K x : Set (Pi1 A K)) := by
      ext σ
      show σ x = y ↔ σ0.symm (σ x) = x
      rw [AlgEquiv.symm_apply_eq, hσ0]
    rw [hs]
    exact (Subgroup.isClosed_of_isOpen _ (fixElt_isOpen A K x)).preimage (continuous_mul_left _)
  · push_neg at h
    have hs : {σ : Pi1 A K | σ x = y} = ∅ := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact h σ
    rw [hs]
    exact isClosed_empty

/-- `T_m`: the automorphisms acting as `x ↦ x ^ q` on `𝔽_{q^m}`. -/
def frobSet (q m : ℕ) : Set (Pi1 A K) := {σ | ∀ x : maxUnram A K, x ^ q ^ m = x → σ x = x ^ q}

theorem isClosed_frobSet (q m : ℕ) : IsClosed (frobSet (A := A) (K := K) q m) := by
  have hs : frobSet (A := A) (K := K) q m =
      ⋂ (x : maxUnram A K) (_ : x ^ q ^ m = x), {σ : Pi1 A K | σ x = x ^ q} := by
    ext σ
    simp only [frobSet, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hs]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_setOf_apply_eq x (x ^ q)

theorem frobSet_mono (q a b : ℕ) : frobSet (A := A) (K := K) q (a * b) ⊆ frobSet q a := by
  intro σ hσ x hx
  exact hσ x (by rw [pow_mul]; exact pow_pow_iter hx b)

end FrobSet

section Exist

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
theorem cast_ne_zero_of_not_dvd {l : ℕ} [hl : Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq) (n : ℕ) :
    ((l ^ n : ℕ) : F) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff F p] at h
  have hpl : p ∣ l := (Fact.out : p.Prime).dvd_of_dvd_pow h
  have hpl' : p = l := (Nat.prime_dvd_prime_iff_eq Fact.out hl.out).1 hpl
  apply hlq
  rw [hq, ← hpl']
  exact dvd_pow_self p he.ne'

theorem isUnit_cast_Rfin {N : ℕ} (hN : (N : F) ≠ 0) : IsUnit (N : Rfin Fq F) := by
  have h : (N : Fq) ≠ 0 := by
    intro h0
    apply hN
    rw [← map_natCast (algebraMap Fq F), h0, map_zero]
  have h1 := (Ne.isUnit h).map (algebraMap Fq (Rfin Fq F))
  rwa [map_natCast] at h1

theorem isUnit_cast_Rinf {N : ℕ} (hN : (N : F) ≠ 0) : IsUnit (N : Rinf Fq F) := by
  have h : (N : Fq) ≠ 0 := by
    intro h0
    apply hN
    rw [← map_natCast (algebraMap Fq F), h0, map_zero]
  have h1 := (Ne.isUnit h).map (algebraMap Fq (Rinf Fq F))
  rwa [map_natCast] at h1

include hq he in
theorem exists_zeta_geo {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0) :
    ∃ ζ : maxUnram (Rfin Fq F) F, IsPrimitiveRoot ζ N ∧
      ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ := by
  obtain ⟨ζ, hζ, hc⟩ := exists_zeta (Rfin Fq F) F p he N hN
  refine ⟨ζ, hζ, ?_⟩
  rw [hq]
  exact zeta_fixed hc

include he in
theorem exists_zeta_level : ∀ a, 0 < a → ∃ z : maxUnram (Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1) := by
  intro a ha
  have h1 : 1 < (p ^ e) ^ a := Nat.one_lt_pow ha.ne' (Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt)
  have : NeZero ((p ^ e) ^ a - 1) := ⟨by omega⟩
  have hN : (((p ^ e) ^ a - 1 : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_sub h1.le, Nat.cast_pow, Nat.cast_pow, CharP.cast_eq_zero, zero_pow he.ne', zero_pow ha.ne',
      Nat.cast_one, zero_sub, neg_ne_zero]
    exact one_ne_zero
  obtain ⟨ζ, hζ, -⟩ := exists_zeta (Rfin Fq F) F p he _ hN
  exact ⟨ζ, hζ⟩

include hk hq he in
/-- `T_m ≠ ∅`: lift `frobF` on `F_m ⊆ K_U` to `K_U`. -/
theorem frobSet_nonempty (m : ℕ) [NeZero m] :
    (frobSet (A := Rfin Fq F) (K := F) (Fintype.card Fq) m).Nonempty := by
  have hle := Fc_le_maxUnram (F := F) hq he m
  have : IsGalois F (Fc Fq F (AlgebraicClosure F) m) := (Fc_mem_unramSet (F := F) hq he m).2.1
  obtain ⟨g, hg⟩ := exists_lift_level hle (frobF (isConstExt_Fc Fq F (AlgebraicClosure F) hk m))
  refine ⟨g, fun x hx => ?_⟩
  have hxL : (x : AlgebraicClosure F) ∈ Lc Fq (AlgebraicClosure F) m := by
    rw [mem_Lc]
    have h2 := congrArg Subtype.val hx
    rwa [SubmonoidClass.coe_pow] at h2
  have h1 := hg (algebraMap (Lc Fq (AlgebraicClosure F) m) (Fc Fq F (AlgebraicClosure F) m) ⟨x, hxL⟩)
  rw [frobF_algebraMap_L] at h1
  have hy : IntermediateField.inclusion hle
      (algebraMap (Lc Fq (AlgebraicClosure F) m) (Fc Fq F (AlgebraicClosure F) m) ⟨x, hxL⟩) = x :=
    Subtype.ext rfl
  rw [hy] at h1
  rw [h1]
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  show ((frobL Fq (Lc Fq (AlgebraicClosure F) m) ⟨x, hxL⟩ : Lc Fq (AlgebraicClosure F) m) : AlgebraicClosure F) =
    (x : AlgebraicClosure F) ^ Fintype.card Fq
  rw [frobL, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  rfl

include hk hq he in
/-- **An arithmetic Frobenius lift exists** in `π₁(U)`. -/
theorem exists_frobLift : ∃ φ : Pi1 (Rfin Fq F) F, IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ := by
  let T : ℕ → Set (Pi1 (Rfin Fq F) F) := fun k => frobSet (Fintype.card Fq) (k + 1)
  have hdir : Directed (· ⊇ ·) T := by
    intro i j
    have hpos : 1 ≤ (i + 1) * (j + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    refine ⟨(i + 1) * (j + 1) - 1, ?_, ?_⟩
    · show T _ ⊆ T _
      simp only [T, Nat.sub_add_cancel hpos]
      exact frobSet_mono _ _ _
    · show T _ ⊆ T _
      simp only [T, Nat.sub_add_cancel hpos]
      rw [mul_comm]
      exact frobSet_mono _ _ _
  have hne : (⋂ k, T k).Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed T hdir
      (fun k => frobSet_nonempty hk hq he (k + 1)) (fun k => (isClosed_frobSet _ _).isCompact)
      (fun k => isClosed_frobSet _ _)
  obtain ⟨φ, hφ⟩ := hne
  refine ⟨φ, fun x hx => ?_⟩
  obtain ⟨n, hn, hxn⟩ := hx
  have h := Set.mem_iInter.1 hφ (n - 1)
  exact h x (by rw [Nat.sub_add_cancel hn]; exact hxn)

end Exist

end

end RamanujanPetersson.CP4a

end

-- ===== S4.Def_RP_CupDuality_GysD =====
section

/-!
# S4-CurveDuality O4G-4: `π₁(U) = φ^ℕ · π₁^geo · N` for every open `N`

Route G (session 44). `Γ_L` (`fixLev`) fixes the constants of level `L`; these sets are closed, directed, and
`⋂ Γ_L = π₁^geo`, so by compactness some `Γ_L` lies in the open set `π₁^geo · N` (`exists_fixLev_sub`). Any `ψ`
acts on `𝔽_{q^L} ⊆ K_U` as a power `x ↦ x^{q^j}` (`exists_pow_lev`, CP4a's `exists_frob_pow_of_finite`), as does `φ^j`
for a Frobenius lift `φ`; hence `(φ^j)⁻¹ ψ ∈ Γ_L` and `ψ = φ^j γ n` (`exists_frobPow_mul`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open Places PicDescent CurveCoh Kummer GalCover CP4a
open scoped Pointwise Polynomial

noncomputable section

section Gen

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

/-- `Γ_L`: the automorphisms fixing the constants of level `L`. -/
def fixLev (q L : ℕ) : Set (Pi1 A K) := {σ | ∀ x : maxUnram A K, x ^ q ^ L = x → σ x = x}

theorem isClosed_fixLev (q L : ℕ) : IsClosed (fixLev (A := A) (K := K) q L) := by
  have hs : fixLev (A := A) (K := K) q L =
      ⋂ (x : maxUnram A K) (_ : x ^ q ^ L = x), {σ : Pi1 A K | σ x = x} := by
    ext σ
    simp only [fixLev, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hs]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_setOf_apply_eq x x

theorem fixLev_mono (q a b : ℕ) : fixLev (A := A) (K := K) q (a * b) ⊆ fixLev q a := by
  intro σ hσ x hx
  exact hσ x (by rw [pow_mul]; exact pow_pow_iter hx b)

/-- A Frobenius lift acts as `x ↦ x^{q^j}` through `φ^j` on the constants of level `L`. -/
theorem frob_pow_apply {q : ℕ} {φ : Pi1 A K} (hφ : IsFrobLift A K q φ) {L : ℕ} (hL : 0 < L) (j : ℕ) :
    ∀ x : maxUnram A K, x ^ q ^ L = x → (φ ^ j) x = x ^ q ^ j := by
  induction j with
  | zero => intro x _; simp
  | succ j ih =>
    intro x hx
    have hxq : (x ^ q) ^ q ^ L = x ^ q := by rw [← pow_mul, mul_comm, pow_mul, hx]
    rw [pow_succ φ j, AlgEquiv.mul_apply, hφ x ⟨L, hL, hx⟩, ih _ hxq, ← pow_mul, pow_succ' q j]

/-- Compactness: some `Γ_L` lies in a given open neighbourhood of `π₁^geo`. -/
theorem exists_fixLev_sub (q : ℕ) {U : Set (Pi1 A K)} (hU : IsOpen U)
    (hsub : (pi1geo A K q : Set (Pi1 A K)) ⊆ U) : ∃ L, 0 < L ∧ fixLev (A := A) (K := K) q L ⊆ U := by
  let T : ℕ → Set (Pi1 A K) := fun m => fixLev q (m + 1) ∩ Uᶜ
  have hdir : Directed (· ⊇ ·) T := by
    intro i j
    have hpos : 1 ≤ (i + 1) * (j + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    refine ⟨(i + 1) * (j + 1) - 1, ?_, ?_⟩
    · show T _ ⊆ T _
      simp only [T, Nat.sub_add_cancel hpos]
      exact Set.inter_subset_inter_left _ (fixLev_mono _ _ _)
    · show T _ ⊆ T _
      simp only [T, Nat.sub_add_cancel hpos]
      rw [mul_comm]
      exact Set.inter_subset_inter_left _ (fixLev_mono _ _ _)
  have hclosed : ∀ m, IsClosed (T m) := fun m => (isClosed_fixLev _ _).inter hU.isClosed_compl
  have hempty : (Set.univ ∩ ⋂ m, T m) = ∅ := by
    refine Set.subset_empty_iff.1 fun σ hσ => ?_
    have hT : ∀ m, σ ∈ T m := Set.mem_iInter.1 hσ.2
    have hgeo : σ ∈ pi1geo A K q := (mem_pi1geo A K q σ).2 fun x hx => by
      obtain ⟨n, hn, hxn⟩ := hx
      exact (hT (n - 1)).1 x (by rw [Nat.sub_add_cancel hn]; exact hxn)
    exact (hT 0).2 (hsub hgeo)
  obtain ⟨m, hm⟩ := isCompact_univ.elim_directed_family_closed T hclosed hempty hdir
  refine ⟨m + 1, Nat.succ_pos m, fun σ hσ => ?_⟩
  by_contra hσU
  have h : σ ∈ Set.univ ∩ T m := ⟨trivial, hσ, hσU⟩
  rw [hm] at h
  exact h

end Gen

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- Every `ψ ∈ π₁(U)` acts on the constants of level `L` as a power of the `q`-Frobenius. -/
theorem exists_pow_lev (ψ : Pi1 (Rfin Fq F) F) (L : ℕ) [NeZero L] :
    ∃ j : ℕ, ∀ x : maxUnram (Rfin Fq F) F, x ^ Fintype.card Fq ^ L = x →
      ψ x = x ^ Fintype.card Fq ^ j := by
  let f : Lc Fq (maxUnram (Rfin Fq F) F) L →+* maxUnram (Rfin Fq F) F :=
    (Lc Fq (maxUnram (Rfin Fq F) F) L).val.toRingHom
  let g : Lc Fq (maxUnram (Rfin Fq F) F) L →+* maxUnram (Rfin Fq F) F := ψ.toAlgHom.toRingHom.comp f
  have hfg : ∀ a : Fq, f (algebraMap Fq (Lc Fq (maxUnram (Rfin Fq F) F) L) a) =
      g (algebraMap Fq (Lc Fq (maxUnram (Rfin Fq F) F) L) a) := by
    intro a
    have h1 : f (algebraMap Fq (Lc Fq (maxUnram (Rfin Fq F) F) L) a) =
        algebraMap Fq (maxUnram (Rfin Fq F) F) a := (Lc Fq (maxUnram (Rfin Fq F) F) L).val.commutes a
    rw [show g (algebraMap Fq (Lc Fq (maxUnram (Rfin Fq F) F) L) a) =
      ψ (f (algebraMap Fq (Lc Fq (maxUnram (Rfin Fq F) F) L) a)) from rfl, h1,
      IsScalarTower.algebraMap_apply Fq F (maxUnram (Rfin Fq F) F) a, AlgEquiv.commutes]
  obtain ⟨j, hj⟩ := exists_frob_pow_of_finite f g hfg
  refine ⟨j, fun x hx => ?_⟩
  exact hj ⟨x, mem_Lc.2 hx⟩

/-- **O4G-4.** `ψ = φ^j γ n` with `γ ∈ π₁^geo`, `n ∈ N`, for a Frobenius lift `φ` and an open `N`. -/
theorem exists_frobPow_mul {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ)
    (N : Subgroup (Pi1 (Rfin Fq F) F)) (hN : IsOpen (N : Set (Pi1 (Rfin Fq F) F))) (ψ : Pi1 (Rfin Fq F) F) :
    ∃ j : ℕ, ∃ γ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), ∃ n ∈ N, ψ = φ ^ j * γ * n := by
  obtain ⟨L, hL, hsub⟩ := exists_fixLev_sub (A := Rfin Fq F) (K := F) (Fintype.card Fq)
    (U := (pi1geo (Rfin Fq F) F (Fintype.card Fq) : Set (Pi1 (Rfin Fq F) F)) * (N : Set (Pi1 (Rfin Fq F) F)))
    hN.mul_left (fun σ hσ => Set.mem_mul.2 ⟨σ, hσ, 1, N.one_mem, mul_one σ⟩)
  have : NeZero L := ⟨hL.ne'⟩
  obtain ⟨j, hj⟩ := exists_pow_lev ψ L
  have hmem : (φ ^ j)⁻¹ * ψ ∈ fixLev (A := Rfin Fq F) (K := F) (Fintype.card Fq) L := by
    simp only [fixLev, Set.mem_ofPred_eq]
    intro x hx
    show (φ ^ j).symm (ψ x) = x
    rw [hj x hx, ← frob_pow_apply hφ hL j x hx]
    exact (φ ^ j).symm_apply_apply x
  obtain ⟨γ, hγ, n, hn, hγn⟩ := Set.mem_mul.1 (hsub hmem)
  exact ⟨j, γ, hγ, n, hn, by rw [mul_assoc, hγn, mul_inv_cancel_left]⟩

end S3

end

end CupDuality
end RamanujanPetersson

end


