-- Prove2me | Definitions.Def_RPLib_S4_CDPack14e
-- name    : RPLib_S4_CDPack14e
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:26:45.154074+00:00
-- url     : https://prove2.me/theorems/838a4842-3a4f-4e58-86cb-59da2f2b28ed
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 14e of 71
-- statement:
--   Part 14e of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_CP4a_BdryInf`: S4-CP4a, part e3c: the boundary count over `∞` and Lefschetz with `#U(𝔽_{q^m})`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack09c
import Definitions.Def_RPLib_S4_CDPack14d

/-!
# Curve-duality library package, part 14e of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_CP4a_BdryInf`: S4-CP4a, part e3c: the boundary count over `∞` and Lefschetz with `#U(𝔽_{q^m})`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CP4a_BdryInf =====
section

/-!
# S4-CP4a, part e3c: the boundary count over `∞` and Lefschetz with `#U(𝔽_{q^m})`

For the chart `Rinf` at infinity of a function field `F/𝔽_q`, with `𝔽_{q^m} ⊆ K_U` for all `m` (`hζc`):
* `good_inf`: residue rings of boundary primes are finite of `q`-power order.
* `card_fix_inf`: `#{s | τ^m s = s} = #Hom_{𝔽_q}(Rinf, 𝔽_{q^m})` for the true boundary permutation `τ` of `φ⁻¹`.
* `numPoints_eq_add_fix`: `N_m = #U(𝔽_{q^m}) + #{s | τ^m s = s}`, `#U(L) := #Hom_{𝔽_q}(Rfin, L)`, `[L : 𝔽_q] = m`.
* `lefschetz_count`: `Tr(F^m | H²_c) - Tr(F^m | H¹_c) = #U(𝔽_{q^m})` in `ℤ/l^n` (Core B as a hypothesis).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer GalCover

noncomputable section

section BdryInf

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

omit [Fintype Fq] [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F] in
theorem algebraMap_Fq_maxUnram (a : Fq) : algebraMap Fq (maxUnram (Rfin Fq F) F) a =
    algebraMap (Rinf Fq F) (maxUnram (Rfin Fq F) F) (algebraMap Fq (Rinf Fq F) a) := by
  rw [IsScalarTower.algebraMap_apply (Rinf Fq F) F (maxUnram (Rfin Fq F) F),
    IsScalarTower.algebraMap_apply Fq F (maxUnram (Rfin Fq F) F),
    ← IsScalarTower.algebraMap_apply Fq (Rinf Fq F) F]

/-- `#Hom_{𝔽_q}(Rfin, L)` depends only on `[L : 𝔽_q]`. -/
theorem card_algHom_Rfin_congr (L L' : Type) [Field L] [Algebra Fq L] [Finite L] [Field L'] [Algebra Fq L']
    [Finite L'] (h : Module.finrank Fq L = Module.finrank Fq L') :
    Nat.card (Rfin Fq F →ₐ[Fq] L) = Nat.card (Rfin Fq F →ₐ[Fq] L') := by
  have key : ∀ (n n' : ℕ) (hn : n ≠ 0) (hn' : n' ≠ 0), n = n' →
      ∑ P ∈ (finite_deg_dvd_of Fq (fun N hN => X_pow_ne_self Fq F hN) hn).toFinset, deg Fq P =
        ∑ P ∈ (finite_deg_dvd_of Fq (fun N hN => X_pow_ne_self Fq F hN) hn').toFinset, deg Fq P := by
    rintro n _ hn hn' rfl
    rfl
  have : Module.Finite Fq L := Module.Finite.of_finite
  have : Module.Finite Fq L' := Module.Finite.of_finite
  rw [card_algHom_Rfin Fq F L, card_algHom_Rfin Fq F L']
  exact key _ _ (Module.finrank_pos (R := Fq) (M := L)).ne' (Module.finrank_pos (R := Fq) (M := L')).ne' h

variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {N : ℕ} [NeZero N] (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

include hq in
/-- Residue rings at boundary primes over `∞` are finite of `q`-power order. -/
theorem good_inf (Q : Ideal (proChart (Rfin Fq F) F (Rinf Fq F)))
    (hQ : IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) :
    Finite (Rinf Fq F ⧸ Q.under (Rinf Fq F)) ∧
      ∃ d, Nat.card (Rinf Fq F ⧸ Q.under (Rinf Fq F)) = (p ^ e) ^ d := by
  have := hQ.1
  have hne : Q.under (Rinf Fq F) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ.2
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  let P : IsDedekindDomain.HeightOneSpectrum (Rinf Fq F) := ⟨Q.under (Rinf Fq F), inferInstance, hne⟩
  refine ⟨Places.finite_residue P, deg Fq P, ?_⟩
  rw [← hq]
  exact card_residue_eq Fq P

include hq hζc in
theorem exists_prim_level (m : ℕ) (hm : 0 < m) :
    ∃ z : maxUnram (Rfin Fq F) F, IsPrimitiveRoot z (Fintype.card Fq ^ m - 1) := by
  rw [hq]
  exact hζc m hm

include hq he hζc hDB in
set_option synthInstance.maxHeartbeats 200000 in
/-- **Fixed boundary points over `∞`**: `#{s | τ^m s = s} = #Hom_{𝔽_q}(Rinf, 𝔽_{q^m})`. -/
theorem card_fix_inf {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ)
    [Fintype S] [DecidableEq S] (m : ℕ) (hm : 0 < m) :
    (Finset.univ.filter fun s => (trueTau D φ⁻¹)^[m] s = s).card =
      Nat.card (Rinf Fq F →ₐ[Fq] levelField Fq (maxUnram (Rfin Fq F) F) m) :=
  card_fix_eq he hζc (good_inf hq) D hDB hq hφ rfl algebraMap_Fq_maxUnram
    (algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq)) (fun _ hN => piInf_pow_ne_self Fq F hN) m hm

include hq he hζc hDB in
/-- **`N_m = #U(L) + #{s | τ^m s = s}`** with `#U(L) := #Hom_{𝔽_q}(Rfin, L)` for any finite `L`, `[L : 𝔽_q] = m`. -/
theorem numPoints_eq_add_fix {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ)
    [Fintype S] [DecidableEq S] (m : ℕ) (hm : 0 < m) (L : Type) [Field L] [Algebra Fq L] [Finite L]
    (hL : Module.finrank Fq L = m) :
    numPoints Fq F m = Nat.card (Rfin Fq F →ₐ[Fq] L) +
      (Finset.univ.filter fun s => (trueTau D φ⁻¹)^[m] s = s).card := by
  obtain ⟨z, hz⟩ := exists_prim_level hq hζc m hm
  have hfin := finrank_levelField hm hz
  have hc := card_levelField hm hz
  have : Finite (levelField Fq (maxUnram (Rfin Fq F) F) m) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ Fintype.card_ne_zero)
  rw [card_fix_inf hq he D hDB hζc hφ m hm,
    card_algHom_Rfin_congr L (levelField Fq (maxUnram (Rfin Fq F) F) m) (hL.trans hfin.symm)]
  have h := numPoints_eq_card_algHom Fq F (levelField Fq (maxUnram (Rfin Fq F) F) m)
  rw [hfin] at h
  exact h

include hk hq he hNf hNi hζ hζΓ hDB hlift hNF hζc in
set_option maxHeartbeats 1000000 in
/-- **Lefschetz with the point count** (Core B as a hypothesis): for the true boundary-compatible geometric
Frobenius and every `m ≥ 1`, `Tr(F^m | H²_c) - Tr(F^m | H¹_c) = #U(𝔽_{q^m})` in `ℤ/l^n`. -/
theorem lefschetz_count [Fintype S] [DecidableEq S] [Nonempty S] (l n : ℕ) [Fact l.Prime] (hn : 0 < n)
    (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq) (hB : CoreBHyp hk l) (φ : Pi1 (Rfin Fq F) F)
    (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ) (m : ℕ) (hm : 1 ≤ m)
    (L : Type) [Field L] [Algebra Fq L] [Finite L] (hL : Module.finrank Fq L = m) :
    LinearMap.trace (ZMod N) (curveH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N))
        (geomFrobH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ ^ m) -
      LinearMap.trace (ZMod N) (curveH1c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D)
        (frobH1c (triv F (maxUnram (Rfin Fq F) F) N) (pi1geo (Rfin Fq F) F (Fintype.card Fq)) D.inertia φ⁻¹
          (trueTau D φ⁻¹) (trueH D φ⁻¹) (trueCompat D φ⁻¹) ^ m) =
      (Nat.card (Rfin Fq F →ₐ[Fq] L) : ZMod N) := by
  refine (lefschetz_triv hk hq he hNf hNi hζ hζΓ D hDB hlift hNF l n hn hN hlq hB φ hφ (trueTau D φ⁻¹)
    (trueH D φ⁻¹) (trueCompat D φ⁻¹) m hm).trans ?_
  rw [numPoints_eq_add_fix hq he D hDB hζc hφ m (by omega) L hL, Nat.cast_add, add_sub_cancel_right]

end BdryInf

end

end RamanujanPetersson.CP4a

end


