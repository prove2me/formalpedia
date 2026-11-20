-- Prove2me | Definitions.Def_RPLib_F2_067
-- name    : RPLib_F2_067
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T22:50:20.972456+00:00
-- url     : https://prove2.me/theorems/8efa630f-5d7e-49b3-9323-cd99ce4efe87
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 067 of 70
-- statement:
--   File 067 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_ZFin3`: S4-Lefschetz, L6z (3): `Z¹(π₁^geo, Λ[Gf])` and `Z¹(π₁^geo ∩ I_s, Λ[Gf])` are finite
--   * `S4.Def_RP_Lefschetz_PDiv4`: S4-Lefschetz, L6e (4): the divisibility hypothesis `PicDivU` holds
--   * `S4.Def_RP_Lefschetz_PDiv6`: S4-Lefschetz, L6e (6): the divisibility hypothesis `PicDivX` holds
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_042
import Definitions.Def_RPLib_F2_054
import Definitions.Def_RPLib_F2_063
import Definitions.Def_RPLib_F2_066
import Definitions.Def_RPLib_F2_086

/-!
# Ramanujan-Petersson curve library (flat edition), file 067 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_ZFin3`: S4-Lefschetz, L6z (3): `Z¹(π₁^geo, Λ[Gf])` and `Z¹(π₁^geo ∩ I_s, Λ[Gf])` are finite
* `S4.Def_RP_Lefschetz_PDiv4`: S4-Lefschetz, L6e (4): the divisibility hypothesis `PicDivU` holds
* `S4.Def_RP_Lefschetz_PDiv6`: S4-Lefschetz, L6e (6): the divisibility hypothesis `PicDivX` holds
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_ZFin3 =====
section

/-!
# S4-Lefschetz, L6z (3): `Z¹(π₁^geo, Λ[Gf])` and `Z¹(π₁^geo ∩ I_s, Λ[Gf])` are finite

For `π : π₁(U) → Gf` cut out by a finite unramified `M` (`ker π = Gal(K_U/M)`), `Λ = ℤ/l^n`:
* `finite_homLC_cover`: `Hom_lc(π₁^geo ∩ range thetaE, Λ)` is finite: pull back along `thetaE` to `π₁^geo` of the
  cover `E` over its constant field (`finite_homLC_geo` there).
* `finite_Z1_regRep_geo`: `Z¹(π₁^geo, Λ[Gf])` is finite (`finite_Z1_regRep` with `K = π₁^geo ∩ ker π`).
* `finite_Z1_regRep_inertia`: `Z¹(π₁^geo ∩ I_s, Λ[Gf])` is finite (`finite_Z1_regRep` with the normalised tame
  generators of `exists_norm_tau_fin` at the cover points `cosQA`; no `PicDiv` needed).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a Residue PerfectCx

section Cover

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- `Hom_lc(π₁^geo ∩ range thetaE, ℤ/l^n)` is finite (pull back to the cover `E` over its constant field). -/
theorem finite_homLC_cover (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    [Algebra.IsSeparable K E] (hE : E ≤ maxUnram Fq[X] K)
    (l n : ℕ) [Fact l.Prime] {N : ℕ} [NeZero N] (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq)
    (Kk : Subgroup (Pi1 (Rfin Fq K) K))
    (hKk : ∀ g, g ∈ Kk ↔ g ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq) ∧ g ∈ (thetaE Fq K E hE).range) :
    Finite (HomLC Kk (ZMod N)) := by
  have : CharP E p := charP_of_injective_algebraMap (algebraMap K E).injective p
  obtain ⟨e', he', hqE⟩ := card_Kc Fq E p
  have := finite_bdryS (Fq := Kc Fq E) (F := E) hqE he'
  let := Fintype.ofFinite (BdryS (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) (Rinf (Kc Fq E) E))
  let : DecidableEq (BdryS (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) (Rinf (Kc Fq E) E)) :=
    Classical.decEq _
  have hF := finite_homLC_geo (Fq := Kc Fq E) (F := E) (constField_eq_bot Fq E) hqE he' l n hN
    (hlq_Kc Fq K E l hlq)
  have hmem : ∀ σ : pi1geo (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)), thetaE Fq K E hE σ ∈ Kk := fun σ =>
    (hKk _).2 ⟨(thetaE_mem_pi1geo_iff Fq K E hE σ).2 σ.2, MonoidHom.mem_range.2 ⟨σ, rfl⟩⟩
  let ι : pi1geo (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) → Kk := fun σ => ⟨thetaE Fq K E hE σ, hmem σ⟩
  have hιc : Continuous ι := ((thetaE_continuous Fq K E hE).comp continuous_subtype_val).subtype_mk _
  have hιm : ∀ a b, ι (a * b) = ι a * ι b := fun a b =>
    Subtype.ext (map_mul (thetaE Fq K E hE) (a : Pi1 (Rfin (Kc Fq E) E) E) (b : Pi1 (Rfin (Kc Fq E) E) E))
  have hιs : Function.Surjective ι := by
    intro g
    obtain ⟨hg1, hg2⟩ := (hKk g).1 g.2
    obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.1 hg2
    have hσg : σ ∈ pi1geo (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) := by
      rw [← thetaE_mem_pi1geo_iff Fq K E hE σ, hσ]
      exact hg1
    exact ⟨⟨σ, hσg⟩, Subtype.ext hσ⟩
  refine Finite.of_injective (fun f : HomLC Kk (ZMod N) =>
    (⟨f.1 ∘ ι, f.2.1.comp_continuous hιc, fun a b => by
      show f.1 (ι (a * b)) = f.1 (ι a) + f.1 (ι b)
      rw [hιm]
      exact f.2.2 _ _⟩ : HomLC (pi1geo (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E))) (ZMod N)))
    fun f1 f2 h => ?_
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨σ, rfl⟩ := hιs g
  exact congrFun (congrArg Subtype.val h) σ

end Cover

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PDiv4 =====
section

/-!
# S4-Lefschetz, L6e (4): the divisibility hypothesis `PicDivU` holds

`picDivU`: for `K` a function field over `𝔽_q` with full constant field and `l ∤ q`, `CdOne.PicDivU (Rfin Fq K) K p l`:
every divisor `D` on the finite places of a finite `M ⊆ K_U` becomes `l`-divisible up to `div a` at some constant level
`M ⊔ constLevel K p m`. Proof: view `M` as a function field over its constant field `k'` (`PDiv3`), apply
`exists_base_fin_div` (`Pic⁰(X̄_M)` is `l`-divisible, a degree-one place at infinity absorbs the degree) and transport
places and valuations along `eBase`, `eLev`, `levEquiv`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open PicDescent Places Kummer CdOne

section GenA

variable {K : Type} [Field K] (A : Type) [CommRing A] [Algebra A K]

end GenA

section PicU

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (M : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K M] [Algebra.IsSeparable K M]

variable {p : ℕ} [Fact p.Prime] [CharP K p]

end PicU

section PicU2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

set_option maxHeartbeats 1600000 in
/-- **`PicDivU` holds** for a function field with full constant field and `l ∤ q`. -/
theorem picDivU (l : ℕ) [Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq) : PicDivU (Rfin Fq K) K p l := by
  intro M hMfin hMU _ _ D hD
  haveI : Algebra.IsSeparable K M := isSeparable_of_le_maxUnram (Rfin Fq K) K M hMU
  haveI : CharP M p := charP_of_injective_algebraMap (algebraMap K M).injective p
  obtain ⟨e', he', hqM⟩ := card_Kc Fq M p
  classical
  have hτ : Function.Injective (fun u : HeightOneSpectrum (Rfin (Kc Fq M) M) =>
      HeightOneSpectrum.comap (eBaseG Fq K M : IC (Rfin Fq K) M →+* Rfin (Kc Fq M) M)
        (eBaseG Fq K M).surjective u) := by
    intro u1 u2 h12
    apply HeightOneSpectrum.ext
    exact Ideal.comap_injective_of_surjective _ (eBaseG Fq K M).surjective (congrArg HeightOneSpectrum.asIdeal h12)
  let D0 : HeightOneSpectrum (Rfin (Kc Fq M) M) →₀ ℤ := Finsupp.ofSupportFinite
    (fun u => D (HeightOneSpectrum.comap (eBaseG Fq K M : IC (Rfin Fq K) M →+* Rfin (Kc Fq M) M)
      (eBaseG Fq K M).surjective u)) (hD.preimage hτ.injOn)
  have hD0 : ∀ u, D0 u = D (HeightOneSpectrum.comap (eBaseG Fq K M : IC (Rfin Fq K) M →+*
      Rfin (Kc Fq M) M) (eBaseG Fq K M).surjective u) := fun u => rfl
  obtain ⟨j, z, f, hf, hdiv⟩ := exists_base_fin_div (Kc Fq M) M (AlgebraicClosure K) (constField_eq_bot Fq M) l
    (hlq_Kc Fq K M l hlq) 1 (Finsupp.sumElim D0 0)
  have hn : 0 < e' * lev j := Nat.mul_pos he' (NeZero.pos _)
  refine ⟨e' * lev j, hn, levEquiv Fq K M hqM (lev j) hn f, fun h0 => hf ((levEquiv Fq K M hqM (lev j) hn).injective
    (h0.trans (map_zero _).symm)), fun w => ?_⟩
  have h1 := hdiv (HeightOneSpectrum.comap (eLevG Fq K M hqM (lev j) hn : Rfin (Lc (Kc Fq M) (AlgebraicClosure K) (lev j))
    (Fc (Kc Fq M) M (AlgebraicClosure K) (lev j)) →+* IC (Rfin Fq K) (M ⊔ constLevel K p (e' * lev j)))
    (eLevG Fq K M hqM (lev j) hn).surjective w)
  have hval := valuation_comap_equiv (eLevG Fq K M hqM (lev j) hn) (levEquiv Fq K M hqM (lev j) hn)
    (algebraMap_eLevG Fq K M hqM (lev j) hn) w f
  rw [PicDescent.contract, Sum.map_inl, Finsupp.sumElim_inl, hD0, Finsupp.add_apply, Finsupp.smul_apply, div_apply,
    Place.ord_inl, Places.ord, hval] at h1
  rw [underI_eq_contFin Fq K M hqM (lev j) hn w, h1]
  rw [neg_add_cancel_right, nsmul_eq_mul, pow_one]
  exact Dvd.intro _ rfl

end PicU2

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PDiv6 =====
section

/-!
# S4-Lefschetz, L6e (6): the divisibility hypothesis `PicDivX` holds

`picDivX`: for `K` a function field over `𝔽_q` with full constant field and `l ∤ q`,
`Residue.PicDivX (Rfin Fq K) K (Rinf Fq K) p (l ^ m)` for every `m`: a degree-`0` divisor `D` on the places over `∞`
of a finite `M ⊆ K_U` (all of one residue size) becomes `l^m`-divisible up to `div a` at some constant level, with
`l^m ∣ v(a)` at every finite place. Proof (`exists_D0`): the places over `∞` of `M` all have the same degree `d`, so
`D` extended by `0` is a degree-`0` divisor on `M / k'`; apply `exists_base_div0` (`Pic⁰(X̄_M)` is `l^m`-divisible)
and transport with `dvd_fin_of`, `dvd_inf_of` (PDiv5).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open PicDescent Places Kummer CdOne

section PicX1

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (M : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K M] [Algebra.IsSeparable K M]

end PicX1

section PicX2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **`PicDivX` holds** at every level `l ^ m`, for a function field with full constant field and `l ∤ q`. -/
theorem picDivX (l : ℕ) [Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq) (m : ℕ) :
    Residue.PicDivX (Rfin Fq K) K (Rinf Fq K) p (l ^ m) := by
  intro M hMfin hMU _ _ r hr D hD hD0
  haveI : Algebra.IsSeparable K M := isSeparable_of_le_maxUnram (Rfin Fq K) K M hMU
  haveI : CharP M p := charP_of_injective_algebraMap (algebraMap K M).injective p
  obtain ⟨e', he', hqM⟩ := card_Kc Fq M p
  obtain ⟨D0, hD0', hdeg1⟩ := exists_D0 Fq K M hr D hD hD0
  obtain ⟨j, z, f, hf, hdiv⟩ := exists_base_div0 (Kc Fq M) M (AlgebraicClosure K) (constField_eq_bot Fq M) l
    (hlq_Kc Fq K M l hlq) m (Finsupp.sumElim 0 D0) hdeg1
  have hn : 0 < e' * lev j := Nat.mul_pos he' (NeZero.pos _)
  refine ⟨e' * lev j, hn, levEquiv Fq K M hqM (lev j) hn f, fun h0 => hf ((levEquiv Fq K M hqM (lev j) hn).injective
    (h0.trans (map_zero _).symm)), fun y => dvd_fin_of Fq K M hqM (lev j) hn (l ^ m) f (fun v => ?_) y,
    fun w => dvd_inf_of Fq K M hqM (lev j) hn (l ^ m) f D (fun v => ?_) w⟩
  · have h1 := hdiv (Sum.inl v)
    rw [PicDescent.contract, Sum.map_inl, Finsupp.sumElim_inl, Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply,
      Finsupp.smul_apply, div_apply, Place.ord_inl, eq_comm, add_eq_zero_iff_eq_neg] at h1
    rw [← dvd_neg, ← h1, nsmul_eq_mul]
    exact Dvd.intro _ rfl
  · have h1 := hdiv (Sum.inr v)
    rw [PicDescent.contract, Sum.map_inr, Finsupp.sumElim_inr, hD0', Finsupp.add_apply, Finsupp.smul_apply,
      div_apply, Place.ord_inr] at h1
    rw [h1, add_sub_cancel_right, nsmul_eq_mul]
    exact Dvd.intro _ rfl

end PicX2

end

end Lefschetz
end RamanujanPetersson


end


