-- Prove2me | Definitions.Def_RPLib_S4_CDPack14b
-- name    : RPLib_S4_CDPack14b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:28:52.072107+00:00
-- url     : https://prove2.me/theorems/585c5d32-f0fb-4a96-a844-69303b82bc48
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 14b of 71
-- statement:
--   Part 14b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Kummer_Frob`: S4-Kummer K5e: Frobenius equivariance of `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack14

/-!
# Curve-duality library package, part 14b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Kummer_Frob`: S4-Kummer K5e: Frobenius equivariance of `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Kummer_Frob =====
section

/-!
# S4-Kummer K5e: Frobenius equivariance of `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`

* `geomFrobH1_mem_curveH1par`: the geometric Frobenius preserves `H¹_par`.
* `piBar_toBar`, `divN_frobF`, `psiAt_frobF`: the arithmetic Frobenius `π` on `Pic(X̄)` and `[div(a)/N]`.
* `frobLift_Fc`: an arithmetic Frobenius lift `φ ∈ π₁(U)` restricts to `frobF` on every constant level `F_m`.
* `Psi_frob`: `Ψ(φ α) = π Ψ(α)`.
* `exists_kummerPicEquiv_frob` (**K5e**): `Φ : H¹_par ≃+ Pic⁰(X̄)[N]` with `Φ[kchar α] = Ψ α` and
  `π (Φ (F x)) = q • Φ x` for the geometric Frobenius `F` (the `μ_N⁻¹` twist, review R4).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh IsDedekindDomain Polynomial PicDescent Places

noncomputable section

section Generic

theorem units_map_aut_inv {K E : Type} [Field K] [Field E] [Algebra K E] (φ : E ≃ₐ[K] E) (α : Eˣ) :
    Units.map (φ : E →* E) (Units.map ((φ⁻¹ : E ≃ₐ[K] E) : E →* E) α) = α :=
  Units.ext (φ.apply_symm_apply (α : E))

theorem exists_inv_of_coprime {r N : ℕ} (hcop : Nat.Coprime r N) : ∃ q' : ZMod N, (r : ZMod N) * q' = 1 :=
  ⟨((ZMod.unitOfCoprime _ hcop)⁻¹ : (ZMod N)ˣ), by rw [← ZMod.coe_unitOfCoprime _ hcop, Units.mul_inv]⟩

end Generic

section ParFrob

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q : ℕ} {R0 : Type} [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)] {S : Type}
  {Λ : Type} [CommRing Λ] {M : Type} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ (Pi1 A K) M)
  (D : BdryData A K q R0 S)

/-- The geometric Frobenius preserves `H¹_par`. -/
theorem geomFrobH1_mem_curveH1par (φ : Pi1 A K) {x : curveH1 q ρ} (hx : x ∈ curveH1par q ρ D) :
    geomFrobH1 q ρ φ x ∈ curveH1par q ρ D := by
  have hx' : x ∈ LinearMap.range (h1cToH1 ρ (pi1geo A K q) D.inertia) := by
    rw [range_h1cToH1]; exact hx
  obtain ⟨y, rfl⟩ := hx'
  show _ ∈ H1par ρ (pi1geo A K q) D.inertia
  rw [← range_h1cToH1]
  exact ⟨geomFrobH1c q ρ D φ y, h1cToH1_frobH1c ρ (pi1geo A K q) D.inertia φ⁻¹ (D.frobTau φ⁻¹) (D.frobH φ⁻¹)
    (D.frob_compat φ⁻¹) y⟩

end ParFrob

section DivFrob

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
variable (h : RR.IsConstExt Fq F L F' c)

/-- `div(π f) / N = π (div(f) / N)`. -/
theorem divN_frobF (N : ℕ) (f : F') : divN L N (frobF h f) = actD h (frobL Fq L) (divN L N f) := by
  ext P
  have h1 : (Places.div (frobF h f) : Divisor L F') P = actD h (frobL Fq L) (Places.div f) P := by
    rw [div_frobF]
  rw [actD_apply] at h1
  rw [actD_apply, divN_apply, divN_apply, ← Places.div_apply, ← Places.div_apply, h1]

end DivFrob

section FrobPic

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)

/-- `π` on `Pic(X̄)` restricts to `frobN m` on `Pic(F_m)`. -/
theorem piBar_toBar (m : ℕ) [NeZero m] (x : Pic (Lc Fq Ω m) (Fc Fq F Ω m)) :
    piBar Ω hk (toBar Ω hk m x) = toBar Ω hk m (frobN Ω hk m x) := by
  have : Fact (m ∣ lev m) := ⟨dvd_lev (NeZero.pos m) le_rfl⟩
  rw [toBar_apply hk m x, toBar_apply hk m (frobN Ω hk m x), piBar_of, frobN_conNN]

/-- `[div(π a)/N] = π [div(a)/N]`. -/
theorem psiAt_frobF (N m : ℕ) [NeZero m] (a : Fc Fq F Ω m) :
    psiAt Ω hk N m (frobF (isConstExt_Fc Fq F Ω hk m) a) = piBar Ω hk (psiAt Ω hk N m a) := by
  unfold psiAt
  rw [piBar_toBar, divN_frobF, ← frobN_mk]

end FrobPic

section Curve

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
theorem Fc_le_maxUnram (m : ℕ) [NeZero m] : Fc Fq F (AlgebraicClosure F) m ≤ maxUnram (Rfin Fq F) F := by
  rw [maxUnram_eq_sSup]; exact le_sSup (Fc_mem_unramSet hq he m)

include hq he in
/-- An arithmetic Frobenius lift restricts to `frobF = π ⊗ id` on `F_m`. -/
theorem frobLift_Fc {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ) (m : ℕ)
    [NeZero m] (a : Fc Fq F (AlgebraicClosure F) m) :
    ((φ ⟨(a : AlgebraicClosure F), Fc_le_maxUnram hq he m a.2⟩ : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) =
      ((frobF (isConstExt_Fc Fq F (AlgebraicClosure F) hk m) a : Fc Fq F (AlgebraicClosure F) m) :
        AlgebraicClosure F) := by
  have hle : Fc Fq F (AlgebraicClosure F) m ≤ maxUnram (Rfin Fq F) F := Fc_le_maxUnram hq he m
  let f : Fc Fq F (AlgebraicClosure F) m →ₐ[F] AlgebraicClosure F :=
    (maxUnram (Rfin Fq F) F).val.comp (φ.toAlgHom.comp (IntermediateField.inclusion hle))
  let g : Fc Fq F (AlgebraicClosure F) m →ₐ[F] AlgebraicClosure F :=
    (Fc Fq F (AlgebraicClosure F) m).val.comp (frobF (isConstExt_Fc Fq F (AlgebraicClosure F) hk m)).toAlgHom
  have hfg : f.toLinearMap = g.toLinearMap := by
    refine LinearMap.ext_on_range (eq_top_iff.2 (isConstExt_Fc Fq F (AlgebraicClosure F) hk m).span) fun j => ?_
    have hc : IsConst (Fintype.card Fq) (IntermediateField.inclusion hle (algebraMap (Lc Fq (AlgebraicClosure F) m)
        (Fc Fq F (AlgebraicClosure F) m) ((pbL Fq (AlgebraicClosure F) m).basis j))) :=
      ⟨m, NeZero.pos m, Subtype.ext (by
        rw [SubmonoidClass.coe_pow]; exact mem_Lc.1 ((pbL Fq (AlgebraicClosure F) m).basis j).2)⟩
    show ((φ (IntermediateField.inclusion hle (algebraMap (Lc Fq (AlgebraicClosure F) m)
        (Fc Fq F (AlgebraicClosure F) m) ((pbL Fq (AlgebraicClosure F) m).basis j))) : maxUnram (Rfin Fq F) F) :
          AlgebraicClosure F) =
      ((frobF (isConstExt_Fc Fq F (AlgebraicClosure F) hk m) (algebraMap (Lc Fq (AlgebraicClosure F) m)
        (Fc Fq F (AlgebraicClosure F) m) ((pbL Fq (AlgebraicClosure F) m).basis j)) :
          Fc Fq F (AlgebraicClosure F) m) : AlgebraicClosure F)
    rw [hφ _ hc, frobF_algebraMap_L, SubmonoidClass.coe_pow]
    show (((pbL Fq (AlgebraicClosure F) m).basis j : Lc Fq (AlgebraicClosure F) m) : AlgebraicClosure F) ^
        Fintype.card Fq =
      ((frobL Fq (Lc Fq (AlgebraicClosure F) m) ((pbL Fq (AlgebraicClosure F) m).basis j) :
        Lc Fq (AlgebraicClosure F) m) : AlgebraicClosure F)
    rw [frobL, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    exact (SubmonoidClass.coe_pow _ _).symm
  exact LinearMap.congr_fun hfg a

section PsiFrob

variable {N : ℕ} [NeZero N]

include hq he in
/-- **`Ψ(φ α) = π Ψ(α)`** for an arithmetic Frobenius lift `φ`. -/
theorem Psi_frob {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ)
    {α : (maxUnram (Rfin Fq F) F)ˣ} (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N) :
    Psi hk N (Units.map (φ : maxUnram (Rfin Fq F) F →* maxUnram (Rfin Fq F) F) α) =
      piBar (AlgebraicClosure F) hk (Psi hk N α) := by
  obtain ⟨m, hm, h1⟩ := exists_Fc_of_rad hq he hα
  have : NeZero m := ⟨hm.ne'⟩
  have hfa := frobLift_Fc hk hq he hφ m ⟨_, h1⟩
  rw [Psi_eq hk α ⟨_, h1⟩ rfl, ← psiAt_frobF hk N m]
  refine Psi_eq hk _ _ ?_
  have hx : (⟨((⟨_, h1⟩ : Fc Fq F (AlgebraicClosure F) m) : AlgebraicClosure F), Fc_le_maxUnram hq he m h1⟩ :
      maxUnram (Rfin Fq F) F) = (α : maxUnram (Rfin Fq F) F) ^ N :=
    Subtype.ext (SubmonoidClass.coe_pow _ _).symm
  rw [← hfa, hx, map_pow, SubmonoidClass.coe_pow]
  rfl

include hq in
/-- An arithmetic Frobenius lift acts on a primitive `N`-th root of unity (`p ∤ N`) by `ζ ↦ ζ ^ q`. -/
theorem frobLift_zeta_card (hNF : (N : F) ≠ 0) {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
    {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ) :
    φ ζ = epow ζ ((Fintype.card Fq : ℕ) : ZMod N) := by
  have hcop : Nat.Coprime (p ^ e) N := coprime_q F p N hNF
  have hcζ : IsConst (p ^ e) ζ := by
    rw [← hq]
    exact isConst_of_pow_eq Fintype.one_lt_card one_pos (by rw [hq]; exact hcop) (one_pow _) one_ne_zero
      hζ.pow_eq_one
  have hφ' : IsFrobLift (Rfin Fq F) F (p ^ e) φ := by rw [← hq]; exact hφ
  rw [hq]
  exact frobLift_zeta hζ hcζ hφ'

variable (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)

/-- `kchar (φ⁻¹ α)` is parabolic when `kchar α` is (`F [kchar α] = q • [kchar (φ⁻¹ α)]`, `q` invertible). -/
theorem kclass_rad_map_mem_par {φ : Pi1 (Rfin Fq F) F} (hφζ : φ ζ = epow ζ ((Fintype.card Fq : ℕ) : ZMod N))
    {q' : ZMod N} (hq' : ((Fintype.card Fq : ℕ) : ZMod N) * q' = 1) {α : (maxUnram (Rfin Fq F) F)ˣ}
    (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N) (hx : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) :
    kclass hζ hζΓ (rad_map φ⁻¹ hα) ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D := by
  have hF := geomFrobH1_kclass hζ hζΓ hφζ hq' hα
  have h2 := Submodule.smul_mem _ q' (geomFrobH1_mem_curveH1par (triv F (maxUnram (Rfin Fq F) F) N) D φ hx)
  rw [hF, smul_smul, mul_comm, hq', one_smul] at h2
  exact h2

theorem geomFrob_kclass_par {φ : Pi1 (Rfin Fq F) F} (hφζ : φ ζ = epow ζ ((Fintype.card Fq : ℕ) : ZMod N))
    {q' : ZMod N} (hq' : ((Fintype.card Fq : ℕ) : ZMod N) * q' = 1) {α : (maxUnram (Rfin Fq F) F)ˣ}
    (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N) (hx : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) :
    (⟨geomFrobH1 (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ (kclass hζ hζΓ hα),
        geomFrobH1_mem_curveH1par _ D φ hx⟩ : curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) =
      Fintype.card Fq • (⟨kclass hζ hζΓ (rad_map φ⁻¹ hα), kclass_rad_map_mem_par hζ hζΓ D hφζ hq' hα hx⟩ : curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_nsmul]
  show geomFrobH1 (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ (kclass hζ hζΓ hα) =
    Fintype.card Fq • kclass hζ hζΓ (rad_map φ⁻¹ hα)
  rw [geomFrobH1_kclass hζ hζΓ hφζ hq' hα, Nat.cast_smul_eq_nsmul]

include hk hq he in
theorem Psi_rad_map_inv {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ) {α : (maxUnram (Rfin Fq F) F)ˣ}
    (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N) :
    Psi hk N α = piBar (AlgebraicClosure F) hk
      (Psi hk N (Units.map ((φ⁻¹ : Pi1 (Rfin Fq F) F) : maxUnram (Rfin Fq F) F →* maxUnram (Rfin Fq F) F) α)) := by
  have hPsi := Psi_frob hk hq he hφ (rad_map φ⁻¹ hα)
  rw [units_map_aut_inv] at hPsi
  exact hPsi

include hk hq he hNF in
set_option maxHeartbeats 1000000 in
/-- The Frobenius identity for any `Φ` with `Φ [kchar α] = Ψ α`. -/
theorem frob_of_kummerPicEquiv (Φ : curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D ≃+ PicBar0N (AlgebraicClosure F) hk N)
    (hΦ : ∀ (α : (maxUnram (Rfin Fq F) F)ˣ) (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
        (hpar : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D),
        (Φ ⟨kclass hζ hζΓ hα, hpar⟩ : PicBar (AlgebraicClosure F) hk) = Psi hk N α)
    {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ)
    {x : curveH1 (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N)} (hx : x ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) :
    piBar (AlgebraicClosure F) hk
        (Φ ⟨geomFrobH1 (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ x,
          geomFrobH1_mem_curveH1par _ D φ hx⟩ : PicBar (AlgebraicClosure F) hk) =
      Fintype.card Fq • (Φ ⟨x, hx⟩ : PicBar (AlgebraicClosure F) hk) := by
  have hφζ := frobLift_zeta_card hq hNF hζ hφ
  have hcop : Nat.Coprime (Fintype.card Fq) N := by rw [hq]; exact coprime_q F p N hNF
  obtain ⟨q', hq'⟩ := exists_inv_of_coprime hcop
  obtain ⟨α, hα, rfl⟩ := kclass_surjective hζ hζΓ x
  have hsub := geomFrob_kclass_par hζ hζΓ D hφζ hq' hα hx
  have hPsi := Psi_rad_map_inv hk hq he hφ hα
  have hβ := hΦ _ (rad_map φ⁻¹ hα) (kclass_rad_map_mem_par hζ hζΓ D hφζ hq' hα hx)
  rw [hsub, map_nsmul]
  rw [AddSubmonoidClass.coe_nsmul, map_nsmul]
  rw [hβ, ← hPsi, hΦ α hα hx]

include hk hq he hNf hNi hDB hlift hNF in
/-- **K5e**: `Φ : H¹_par(π₁^geo, Z/N) ≃+ Pic⁰(X̄)[N]` (`[kchar α] ↦ [div(α ^ N) / N]`) intertwines the geometric
Frobenius with `q⁻¹ • π`: `π (Φ (F x)) = q • Φ x` (`H¹(X̄, Z/N) ≅ Pic⁰(X̄)[N] ⊗ μ_N⁻¹` equivariantly, review R4). -/
theorem exists_kummerPicEquiv_frob :
    ∃ Φ : curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D ≃+ PicBar0N (AlgebraicClosure F) hk N,
      (∀ (α : (maxUnram (Rfin Fq F) F)ˣ) (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
        (hpar : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D),
        (Φ ⟨kclass hζ hζΓ hα, hpar⟩ : PicBar (AlgebraicClosure F) hk) = Psi hk N α) ∧
      ∀ φ : Pi1 (Rfin Fq F) F, IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ →
        ∀ (x : curveH1 (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N)) (hx : x ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D),
          piBar (AlgebraicClosure F) hk
              (Φ ⟨geomFrobH1 (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ x,
                geomFrobH1_mem_curveH1par _ D φ hx⟩ : PicBar (AlgebraicClosure F) hk) =
            Fintype.card Fq • (Φ ⟨x, hx⟩ : PicBar (AlgebraicClosure F) hk) := by
  have key := exists_kummerPicEquiv hk hq he hNf hNi hζ hζΓ D hDB hlift hNF
  obtain ⟨Φ, hΦ⟩ := key
  exact ⟨Φ, hΦ, fun φ hφ x hx => frob_of_kummerPicEquiv hk hq he hζ hζΓ D hNF Φ hΦ hφ hx⟩

end PsiFrob

end Curve

end

end Kummer
end RamanujanPetersson

end


