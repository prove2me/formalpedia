-- Prove2me | Definitions.Def_RPLib_FX_EtP1_37
-- name    : RPLib_FX_EtP1_37
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T06:43:58.308092+00:00
-- url     : https://prove2.me/theorems/1fdaa718-d9c2-5aad-976a-59ea5e3ad399
-- title:
--   Étale cohomology of the projective line, library file 37 (an extra file from a re-cut)
-- statement:
--   File 37 (an extra file from a re-cut) of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_PicDescent_D2`: S4-PicDescent, part D2: unramified Dedekind extensions, generic
--   * `S4.Def_RP_EtCompact_PtCd`: S4-EtCompact, part 38: `H^(n+2)` of a point vanishes when `cd ≤ 1` (CC2c)
--   * `S4.Def_RP_EtCompact_GenPt`: S4-EtCompact, part 39: `H^(n+2)` of `C₁` points and of the generic point of `A¹` (CC2d)
--   * `S4.Def_RP_EtCompact_MV`: S4-EtCompact: the Mayer-Vietoris sequence for a Zariski cover (O8c, file M1)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_15

/-!
# Étale cohomology of the projective line, library file 37 (extra file from a re-cut)

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_PicDescent_D2`: S4-PicDescent, part D2: unramified Dedekind extensions, generic
* `S4.Def_RP_EtCompact_PtCd`: S4-EtCompact, part 38: `H^(n+2)` of a point vanishes when `cd ≤ 1` (CC2c)
* `S4.Def_RP_EtCompact_GenPt`: S4-EtCompact, part 39: `H^(n+2)` of `C₁` points and of the generic point of `A¹` (CC2d)
* `S4.Def_RP_EtCompact_MV`: S4-EtCompact: the Mayer-Vietoris sequence for a Zariski cover (O8c, file M1)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_PicDescent_D2 =====
section

/-!
# S4-PicDescent, part D2: unramified Dedekind extensions, generic

* `A → B` Dedekind, finite, torsion free, formally unramified (`B ≅ A ⊗ L` for a separable `L`):
  every place `w` of `B` has ramification index `1` over `w.under A`, so
  `valuation_under : (w.under A).valuation K x = w.valuation L x'` (orders agree);
  the fibre over `v` is finite and nonempty, `Σ_{w | v} f(w|v) = [B : A]`, `#(A/v)^f = #(B/w)`.
* `pullH σ w = σ⁻¹(w)` for a ring automorphism `σ` of `B`: `valuation_pullH`
  (`(σ⁻¹ w).valuation x = w.valuation (σ x)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

namespace RamanujanPetersson.PicDescent

section Unram

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]

end Unram

section Equiv

variable {B : Type*} [CommRing B] [IsDedekindDomain B]

/-- `σ⁻¹(w)` for a ring automorphism `σ`. -/
def pullH (σ : B ≃+* B) (w : HeightOneSpectrum B) : HeightOneSpectrum B :=
  HeightOneSpectrum.comap (σ : B →+* B) σ.surjective w

theorem pullH_asIdeal (σ : B ≃+* B) (w : HeightOneSpectrum B) :
    (pullH σ w).asIdeal = w.asIdeal.comap (σ : B →+* B) := rfl

theorem mem_pullH (σ : B ≃+* B) (w : HeightOneSpectrum B) (b : B) :
    b ∈ (pullH σ w).asIdeal ↔ σ b ∈ w.asIdeal := Iff.rfl

theorem pow_pullH (σ : B ≃+* B) (w : HeightOneSpectrum B) (n : ℕ) :
    (pullH σ w).asIdeal ^ n = (w.asIdeal ^ n).comap (σ : B →+* B) := by
  change (w.asIdeal.comap σ) ^ n = (w.asIdeal ^ n).comap σ
  rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]

theorem intValuation_pullH (σ : B ≃+* B) (w : HeightOneSpectrum B) (b : B) :
    (pullH σ w).intValuation b = w.intValuation (σ b) := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hσb : σ b ≠ 0 := fun h => hb (σ.injective (h.trans (map_zero σ).symm))
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hb,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hσb]
  congr 3
  apply multiplicity_eq_of_emultiplicity_eq
  rw [emultiplicity_eq_emultiplicity_iff]
  intro n
  rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.span_le, Ideal.span_le, Set.singleton_subset_iff,
    Set.singleton_subset_iff, pow_pullH]
  exact Iff.rfl

/-- **Transport of valuations**: `(σ⁻¹ w)(x) = w(σ x)`. -/
theorem valuation_pullH {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L] (σ : B ≃+* B)
    (σL : L ≃+* L) (hσ : ∀ b, algebraMap B L (σ b) = σL (algebraMap B L b))
    (w : HeightOneSpectrum B) (x : L) :
    (pullH σ w).valuation L x = w.valuation L (σL x) := by
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  rw [map_div₀, map_div₀, map_div₀, ← hσ, ← hσ, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_pullH, intValuation_pullH]

end Equiv

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_EtCompact_PtCd =====
section

/-!
# S4-EtCompact, part 38: `H^(n+2)` of a point vanishes when `cd ≤ 1` (CC2c)

`X ≅ Spec κ(x0)` (`IsIso (X.fromSpecResidueField x0)`), `G = Gal x0`.

* `PtH2 x0 F`: every locally constant 2-cocycle of `G` in `F_x̄` is the coboundary of a locally constant cochain;
* `coboundary_of_coker`: if `PtH2 x0 F`, every locally constant 1-cocycle in `(I/F)_x̄` (`F ↪ I` injective) is a
  coboundary (lift it to `I_x̄`, correct the lift by a cochain in `F_x̄`, use `coboundary_of_injective`);
* `h1_coker_eq_zero`: then `H¹(X, I/F) = 0` (an extension of `Λ_X` by `I/F` splits on stalks, hence as sheaves);
* **`pt_H_eq_zero`**: if `PtH2 x0 F` for all `F`, then `H^(n+2)(X, F) = 0` (dimension shifting);
* **`pt_H_eq_zero_of_hypL`**: the same when `Gal x0` satisfies `HypL ℓ` and `ℓ^k = 0` in `Λ` (`h2_lcCob`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Topology

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne

universe u

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] {Λ : Type u} [CommRing Λ]

/-- **`H^(n+2)(X, F) = 0`** on `X ≅ Spec κ(x0)` when `H²(Gal x0, -)` vanishes on all stalks. -/
theorem pt_H_eq_zero (hF : ∀ F : EtSh Λ X, PtH2 x0 F) (n : ℕ) (F : EtSh Λ X) (e : H Λ F (n + 2)) : e = 0 :=
  ext_eq_zero_of_coker (unitSh Λ X) (fun F e => h1_coker_eq_zero x0 F (hF F) e) n F e

/-- **`H^(n+2)(Spec κ, F) = 0`** when `Gal(κ^sep/κ)` satisfies `HypL ℓ` and `ℓ^k = 0` in `Λ`. -/
theorem pt_H_eq_zero_of_hypL (l : ℕ) [Fact l.Prime] (hL : HypL l (Gal x0)) (k : ℕ) (hΛ : ((l ^ k : ℕ) : Λ) = 0)
    (n : ℕ) (F : EtSh Λ X) (e : H Λ F (n + 2)) : e = 0 :=
  pt_H_eq_zero x0 (ptH2_of_hypL x0 l hL k hΛ) n F e

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_GenPt =====
section

/-!
# S4-EtCompact, part 39: `H^(n+2)` of `C₁` points and of the generic point of `A¹` (CC2d)

* `isC1_of_ringEquiv`: `C₁` transfers along ring isomorphisms;
* **`pt_H_eq_zero_of_C1`**: on `X ≅ Spec κ` with `κ` a `C₁` field containing a primitive `ℓ`-th root of unity
  (`ℓ ≠ char κ`) and `ℓ^m = 0` in `Λ`: `H^(n+2)(X, F) = 0` (`hypL_gal` + `pt_H_eq_zero_of_hypL`);
* `H_ptOf_eq_zero_of_C1`: the same on `Spec κ(y)` for a point `y` with `C₁` residue field;
* `isC1_genField_polynomial`: `κ(η)` of `A¹_k = Spec k[X]` is `C₁` (Tsen, `κ(η) ≅ k(X)`), and
  **`H_genPt_eq_zero`**: `H^(n+2)(Spec κ(η), F) = 0` for `k` algebraically closed, `ℓ ≠ char k`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne RamanujanPetersson.Tsen

universe u

section Point

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] {Λ : Type u} [CommRing Λ]

/-- **`H^(n+2)(Spec κ, F) = 0`** for a `C₁` field `κ` with a primitive `ℓ`-th root of unity, `ℓ^m = 0` in `Λ`. -/
theorem pt_H_eq_zero_of_C1 (hC1 : IsC1 (X.residueField x0)) (l : ℕ) [Fact l.Prime]
    (hl : (l : X.residueField x0) ≠ 0) {ζ : X.residueField x0} (hζ : IsPrimitiveRoot ζ l) (m : ℕ)
    (hΛ : ((l ^ m : ℕ) : Λ) = 0) (n : ℕ) (F : EtSh Λ X) (e : H Λ F (n + 2)) : e = 0 :=
  pt_H_eq_zero_of_hypL x0 l (hypL_gal _ hC1 l hl hζ) m hΛ n F e

end Point

/-- **`H^(n+2)(Spec κ(y), F) = 0`** when `κ(y)` is `C₁` with a primitive `ℓ`-th root of unity. -/
theorem H_ptOf_eq_zero_of_C1 {Y : Scheme.{u}} (y : Y) {Λ : Type u} [CommRing Λ] (hC1 : IsC1 (Y.residueField y))
    (l : ℕ) [Fact l.Prime] (hl : (l : Y.residueField y) ≠ 0) {ζ : Y.residueField y} (hζ : IsPrimitiveRoot ζ l)
    (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0) (n : ℕ) (F : EtSh Λ (Spec (Y.residueField y))) (e : H Λ F (n + 2)) :
    e = 0 := by
  let φ := (ptResidueIso y).commRingCatIsoToRingEquiv
  refine pt_H_eq_zero_of_C1 (ptOf y) (isC1_of_ringEquiv φ hC1) l ?_ (hζ.map_of_injective φ.injective) m hΛ n F e
  rw [← map_natCast φ]
  exact (_root_.map_ne_zero φ).2 hl

section Generic

variable (k : Type) [Field k] [IsAlgClosed k]

/-- **`H^(n+2)(Spec κ(η), F) = 0`** at the generic point `η` of `A¹_k`, `k` algebraically closed, `ℓ ≠ char k`,
`ℓ^m = 0` in `Λ`. -/
theorem H_genPt_eq_zero {Λ : Type} [CommRing Λ] (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0) (m : ℕ)
    (hΛ : ((l ^ m : ℕ) : Λ) = 0) (n : ℕ) (F : EtSh Λ (Spec ((Spec (CommRingCat.of k[X])).residueField (GenBr.genPt k[X])))) (e : H Λ F (n + 2)) :
    e = 0 := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_ne k hl
  refine H_ptOf_eq_zero_of_C1 (GenBr.genPt k[X]) (isC1_genField_polynomial k) l ?_
    (hζ.map_of_injective (genConst_injective k)) m hΛ n F e
  rw [← map_natCast (genConst k)]
  exact (_root_.map_ne_zero (genConst k)).2 hl

end Generic

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_MV =====
section

/-!
# S4-EtCompact: the Mayer-Vietoris sequence for a Zariski cover (O8c, file M1)

* `mvS F U V`: the short complex `j_{U⊓V!}F ⟶ j_{U!}F ⊞ j_{V!}F ⟶ F`; **`mvS_shortExact`** when `U ∪ V = X`.
* `subsingleton_ext_biprod`, **`precomp_extClass_bijective`**: `Ext` out of a biproduct; the connecting map of the
  contravariant `Ext` sequence is bijective when the middle terms vanish.
* `cutExt j G n : Ext^n(j_{U!}Λ_U, G) ≃ H^n(U, G|_U)`, `cutH j n`, `cutHOpen W n`.
* **`P1.h2Equiv`**: `H^2(P^1, Λ) ≃ H^1(U ⊓ V, Λ)` for the two standard charts, when `H^1(A^1, Λ) = H^2(A^1, Λ) = 0`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe w v u

section ExtGen

variable {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{u} C]

end ExtGen

section MV

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end MV

section Cut

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

/-- `Ext^n_X(j_{U!}Λ_U, G) ≃ H^n(U, G|_U)` with `j_{U!}Λ_U` written as the cut `openCut (range j) Λ_X`. -/
def cutExt (G : EtSh Λ X) (n : ℕ) :
    Ext (openCut Λ j.opensRange (unitSh Λ X)) G n ≃+ H Λ ((res j Λ).obj G) n :=
  (extIsoLeft ((lsh j Λ).mapIso (resUnitIsoOf (Λ := Λ) j).symm ≪≫ lshResIso j (unitSh Λ X)) G n).trans
    (openH Λ j G n)

end Cut

section CutOpen

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end CutOpen

section ExtIface

variable {C : Type v} [Category.{w} C] [Abelian C]

variable [HasExt.{u} C]

end ExtIface

section P1

variable (K : Type u) [Field K] {Λ : Type u} [CommRing Λ]

end P1

end RamanujanPetersson.EtCompact

end

end


