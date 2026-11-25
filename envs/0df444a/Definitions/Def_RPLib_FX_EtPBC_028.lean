-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_028
-- name    : RPLib_FX_EtPBC_028
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:57:11.554187+00:00
-- url     : https://prove2.me/theorems/421b230e-845c-57c2-9d03-6fd9a1cc4148
-- title:
--   Proper base change for the projective line, library file 028
-- statement:
--   File 028 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovLim1`: S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers
--   * `S4.Def_RP_EtPBC_A_CovHat1`: S4-EtPBC-A, R4-T2 (A2c-3a): the completed chart rings as subrings of products of localizations
--   * `S4.Def_RP_EtPBC_A_EGeoB`: S4-EtPBC-A, M4(E), EGeoB: a splitting neighbourhood of a geometric point and its sections
--   * `S4.Def_RP_EtPBC_A_NagB`: S4-EtPBC-A, M4(N2): integral closures of finite type domains over a perfect field are finite
--   * `S4.Def_RP_EtPBC_A_NagC`: S4-EtPBC-A, M4(N3): the relative normalization of a finite field point is finite
--   * `S4.Def_RP_EtPBC_A_EIdem`: S4-EtPBC-A, M4(E), EIdem: clopen sets, idempotents, and lifting clopens to a relative normalization
--   * `S4.Def_RP_EtPBC_A_O2M2`: S4-EtPBC-A, O2 (MV route), M2: local vanishing of cohomology classes
--   * `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
--   * `S4.Def_RP_EtPBC_A_O2R3`: S4-EtPBC-A, O2 (MV route), M6a (3): the multi-point MV complex maps to each one-point complex
--   * `S4.Def_RP_EtPBC_A_O2Km2`: S4-EtPBC-A, O2 M6 (O2Km2): splitting `H¹(X, Λ)` along a finite clopen decomposition
--   * `S4.Def_RP_EtPBC_A_O2E5`: S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)
--   * `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2E6b`: S4-EtPBC-A, O2 C-plan S4d1 (part 2): `extFreeU` is natural in the etale object
--   * `S4.Def_RP_EtPBC_A_O2Km7`: S4-EtPBC-A, O2 M6 (O2Km7): Kummer decomposition of an unramified character
--   * `S4.Def_RP_EtPBC_A_O2KapP`: S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map
--   * `S4.Def_RP_EtPBC_A_O2E7`: S4-EtPBC-A, O2 C-plan S4d2: purity on `W₁ = Spec B_t` with the chart Kummer class
--   * `S4.Def_RP_EtPBC_A_O2T1`: S4-EtPBC-A, O2 S5a: restriction of a free sheaf, graphs and section maps
--   * `S4.Def_RP_EtPBC_A_O2UK2a`: S4-EtPBC-A, O2 M6 (O2UK2a): a good chart through a geometric point
--   * `S4.Def_RP_EtPi1_FunA`: S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change
--   * `S4.Def_RP_EtPBC_A_O2PPTa`: S4-EtPBC-A, O2 GLOB (O2PPTa): moving a Kummer radical along a map of fields
--   * `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_019
import Definitions.Def_RPLib_FX_EtPBC_021
import Definitions.Def_RPLib_FX_EtPBC_022
import Definitions.Def_RPLib_FX_EtPBC_023

/-!
# Proper base change for the projective line, library file 028

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovLim1`: S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers
* `S4.Def_RP_EtPBC_A_CovHat1`: S4-EtPBC-A, R4-T2 (A2c-3a): the completed chart rings as subrings of products of localizations
* `S4.Def_RP_EtPBC_A_EGeoB`: S4-EtPBC-A, M4(E), EGeoB: a splitting neighbourhood of a geometric point and its sections
* `S4.Def_RP_EtPBC_A_NagB`: S4-EtPBC-A, M4(N2): integral closures of finite type domains over a perfect field are finite
* `S4.Def_RP_EtPBC_A_NagC`: S4-EtPBC-A, M4(N3): the relative normalization of a finite field point is finite
* `S4.Def_RP_EtPBC_A_EIdem`: S4-EtPBC-A, M4(E), EIdem: clopen sets, idempotents, and lifting clopens to a relative normalization
* `S4.Def_RP_EtPBC_A_O2M2`: S4-EtPBC-A, O2 (MV route), M2: local vanishing of cohomology classes
* `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
* `S4.Def_RP_EtPBC_A_O2R3`: S4-EtPBC-A, O2 (MV route), M6a (3): the multi-point MV complex maps to each one-point complex
* `S4.Def_RP_EtPBC_A_O2Km2`: S4-EtPBC-A, O2 M6 (O2Km2): splitting `H¹(X, Λ)` along a finite clopen decomposition
* `S4.Def_RP_EtPBC_A_O2E5`: S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)
* `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
* `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
* `S4.Def_RP_EtPBC_A_O2E6b`: S4-EtPBC-A, O2 C-plan S4d1 (part 2): `extFreeU` is natural in the etale object
* `S4.Def_RP_EtPBC_A_O2Km7`: S4-EtPBC-A, O2 M6 (O2Km7): Kummer decomposition of an unramified character
* `S4.Def_RP_EtPBC_A_O2KapP`: S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map
* `S4.Def_RP_EtPBC_A_O2E7`: S4-EtPBC-A, O2 C-plan S4d2: purity on `W₁ = Spec B_t` with the chart Kummer class
* `S4.Def_RP_EtPBC_A_O2T1`: S4-EtPBC-A, O2 S5a: restriction of a free sheaf, graphs and section maps
* `S4.Def_RP_EtPBC_A_O2UK2a`: S4-EtPBC-A, O2 M6 (O2UK2a): a good chart through a geometric point
* `S4.Def_RP_EtPi1_FunA`: S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change
* `S4.Def_RP_EtPBC_A_O2PPTa`: S4-EtPBC-A, O2 GLOB (O2PPTa): moving a Kummer radical along a map of fields
* `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovLim1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers

* `dep_choice`, `seq_choice`: sequences by choice along `ℕ`;
* `ker_ρ₀`, `ker_ρ₁`: the kernels of a transition are `p^(k+1)` on the charts; `mem_of_ρ₀`, `mem_of_ρ₁`: an element whose
  image has entries in `p^n` (`n ≤ k+1`) has entries in `p^n`;
* **`Gam C H d`**: compatible families of sections of `O(d)` along a tower `C`, `H`; **`exists_gam`**: every level-`0`
  section lifts when all transitions are surjective on sections.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Ker

end Ker

section Fam

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

theorem mem_gam {d : ℕ} (x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)) : x ∈ Gam C H d ↔
    ∀ k, (H k).ρ₀ (x.1 (k + 1)) = x.1 k ∧ (H k).ρ₁ (x.2 (k + 1)) = x.2 k ∧
      (C k).ψ₀ (x.1 k) = (C k).u ^ d * (C k).ψ₁ (x.2 k) :=
  Iff.rfl

end Fam

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3a): the completed chart rings as subrings of products of localizations

For a tower `C`, `H` of level covers:
* `fB₀`, `fB₁`: `Bᵢ → ∏ₖ Eᵢ(k)`; `tFm = fB₀ t₀`, `sFm = fB₁ t₁`; `L₀ = (∏ E₀(k))[1/t]`, `L₁ = (∏ E₁(k))[1/s]`;
* `gam_cast`, `gam_one`, `gam_mul`, `gam_pow`; `gT₀ = (1, s)`, `gT₁ = (t, 1)` with `gT₀_mem`, `gT₁_mem`;
* **`hE₀`** `⊆ ∏ E₀(k) × L₁` (fractions `x / T₀ᵈ`), **`hE₁`** `⊆ L₀ × ∏ E₁(k)` (fractions `x / T₁ᵈ`),
  **`hE`** `⊆ L₀ × L₁` (fractions `x / T₁ᵃ T₀ᵇ`); **`hψ₀ : hE₀ →+* hE`**, **`hψ₁ : hE₁ →+* hE`**.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Hat

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

theorem gam_cast {d e : ℕ} (h : d = e) {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d) :
    x ∈ Gam C H e := h ▸ hx

end Hat

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_EGeoB =====
section

/-!
# S4-EtPBC-A, M4(E), EGeoB: a splitting neighbourhood of a geometric point and its sections

* `exists_common_nbhd`: finitely many etale neighbourhoods of `t` have a common affine refinement;
* `FibPts x W := Σ j, fibre of W j over x̄`, finite (`finite_fibPts`); **`exists_split`**: an affine `T` with a point
  `t` over `x̄` and maps `τ p : T ⟶ W p.1` sending `t` to `p.2`, for all `p : FibPts x W`;
* `exists_opens_unique`, `specializes_of_unique`: shrinking `T` so that `fpt t` is its only point over `x`; then every
  point of `T` over a specialisation of `x` is a specialisation of `fpt t`;
* `prd W T` (`W ×_P T`), `prW`, `prT`, `sec τ` (the section of `prT` given by `τ : T ⟶ W`), `pair a t`;
* **`exists_eq_tau`**: if every point of `W` over `x̄` is `τ b (t)` and `fpt t ⤳ fpt t'` (`t'` over `ȳ`), every point
  `a` of `W` over `ȳ` is `τ b (t')` for some `b`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech

universe u

variable {P : Scheme.{u}}

theorem finite_fibPts (x : P) {J : Type u} [Finite J] (W : J → P.Etale) [∀ j, QuasiCompact (W j).hom] :
    Finite (FibPts x W) := by
  have : ∀ j, Finite ((geomPtAt x).point.fiber.obj (W j)) := fun j => finite_fiber (W j) x
  infer_instance

section Prd

end Prd

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_NagB =====
section

/-!
# S4-EtPBC-A, M4(N2): integral closures of finite type domains over a perfect field are finite

* `isLocalization_of_finite`: for a domain `D` integral over a domain `A ⊆ D`, `Frac D` is the localization of `D`
  at the image of `A⁰`;
* **`finite_integralClosure`**: `D` a domain of finite type over a perfect field `K`, `F = Frac D`, `L` finite over
  `F` ⇒ the integral closure of `D` in `L` is a finite `D`-module (Noether normalization + `NagA`).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Nagata

/-- **Finiteness of integral closures** of finite type domains over a perfect field. -/
theorem finite_integralClosure (K D F L : Type*) [Field K] [CommRing D] [IsDomain D] [Algebra K D]
    [Algebra.FiniteType K D] [Field F] [Algebra D F] [IsFractionRing D F] [Field L] [Algebra F L] [Algebra D L]
    [IsScalarTower D F L] [FiniteDimensional F L] (p : ℕ) [ExpChar K p] [PerfectRing K p] :
    Module.Finite D (integralClosure D L) := by
  obtain ⟨s, g, hg, hgf⟩ := exists_finite_inj_algHom_of_fg K D
  let : Algebra (MvPolynomial (Fin s) K) D := g.toRingHom.toAlgebra
  have hAD : Module.Finite (MvPolynomial (Fin s) K) D := hgf
  let : Algebra (MvPolynomial (Fin s) K) F := ((algebraMap D F).comp g.toRingHom).toAlgebra
  let : Algebra (MvPolynomial (Fin s) K) L := ((algebraMap D L).comp g.toRingHom).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin s) K) D F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (MvPolynomial (Fin s) K) D L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hinjAD : Function.Injective (algebraMap (MvPolynomial (Fin s) K) D) := hg
  have hinjAF : Function.Injective (algebraMap (MvPolynomial (Fin s) K) F) := (IsFractionRing.injective D F).comp hg
  have : FaithfulSMul (MvPolynomial (Fin s) K) F := (faithfulSMul_iff_algebraMap_injective _ F).2 hinjAF
  let : Algebra (FractionRing (MvPolynomial (Fin s) K)) F := FractionRing.liftAlgebra _ F
  have : Algebra.IsIntegral (MvPolynomial (Fin s) K) D := Algebra.IsIntegral.of_finite _ D
  have : IsLocalization (Algebra.algebraMapSubmonoid D (nonZeroDivisors (MvPolynomial (Fin s) K))) F :=
    isLocalization_of_finite _ D F hinjAD
  have : Module.Finite (FractionRing (MvPolynomial (Fin s) K)) F :=
    Module.Finite.of_isLocalization (MvPolynomial (Fin s) K) D (nonZeroDivisors (MvPolynomial (Fin s) K))
  let : Algebra (FractionRing (MvPolynomial (Fin s) K)) L :=
    ((algebraMap F L).comp (algebraMap (FractionRing (MvPolynomial (Fin s) K)) F)).toAlgebra
  have : IsScalarTower (FractionRing (MvPolynomial (Fin s) K)) F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (MvPolynomial (Fin s) K) (FractionRing (MvPolynomial (Fin s) K)) L :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap D L (g a) = algebraMap F L (algebraMap (FractionRing (MvPolynomial (Fin s) K)) F
        (algebraMap (MvPolynomial (Fin s) K) (FractionRing (MvPolynomial (Fin s) K)) a))
      rw [← IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) K) (FractionRing (MvPolynomial (Fin s) K)) F]
      exact IsScalarTower.algebraMap_apply D F L (g a)
  have : FiniteDimensional (FractionRing (MvPolynomial (Fin s) K)) L := Module.Finite.trans F L
  have hAL : Module.Finite (MvPolynomial (Fin s) K) (integralClosure (MvPolynomial (Fin s) K) L) :=
    finite_integralClosure_of_isIntegrallyClosed K (MvPolynomial (Fin s) K) (FractionRing (MvPolynomial (Fin s) K)) L p
  let θ : integralClosure D L →ₗ[MvPolynomial (Fin s) K] integralClosure (MvPolynomial (Fin s) K) L :=
    { toFun := fun x => ⟨x, isIntegral_trans (R := MvPolynomial (Fin s) K) (x : L) x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have : Module.Finite (MvPolynomial (Fin s) K) (integralClosure D L) :=
    Module.Finite.of_injective θ fun x y h => Subtype.ext (congrArg (fun z : integralClosure (MvPolynomial (Fin s) K) L => (z : L)) h)
  exact Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin s) K) D (integralClosure D L)

end RamanujanPetersson.EtPBC.Nagata

end

end

-- ===== S4.Def_RP_EtPBC_A_NagC =====
section

/-!
# S4-EtPBC-A, M4(N3): the relative normalization of a finite field point is finite

* `finite_integralClosure_of_gen`: `A` of finite type over a perfect field `K`, `F` a field generated (as a field)
  by the image of `A`, `L` finite over `F` ⇒ the integral closure of `A` in `L` is a finite `A`-module (via `NagB`
  for the domain `A ⧸ ker`);
* **`isFinite_fromNormalization`**: `X` locally of finite type over a perfect field, `y : X`, `φ : κ(y) ⟶ κ(ξ)` a
  finite extension ⇒ the relative normalization of `Spec κ(ξ) ⟶ Spec κ(y) ⟶ X` is finite over `X`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace RamanujanPetersson.EtPBC.Nagata

universe u

/-- **N3a**: finiteness of the integral closure of a finite type algebra in a finite extension of a field that
the algebra generates. -/
theorem finite_integralClosure_of_gen (K A F L : Type*) [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] [Field F] [Algebra A F]
    (hF : ∀ x : F, ∃ a b : A, algebraMap A F b ≠ 0 ∧ x * algebraMap A F b = algebraMap A F a)
    [Field L] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [FiniteDimensional F L]
    (p : ℕ) [ExpChar K p] [PerfectRing K p] :
    Module.Finite A (integralClosure A L) := by
  let g : A →+* F := algebraMap A F
  let I := RingHom.ker g
  let D := A ⧸ I
  have hinj : Function.Injective (RingHom.kerLift g) := RingHom.kerLift_injective g
  have : IsDomain D := hinj.isDomain _
  let : Algebra D F := (RingHom.kerLift g).toAlgebra
  let : Algebra D L := ((algebraMap F L).comp (RingHom.kerLift g)).toAlgebra
  have : IsScalarTower D F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hmk : ∀ a : A, algebraMap D F (Ideal.Quotient.mk I a) = g a := fun a => RingHom.kerLift_mk g a
  have : IsScalarTower A D L := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap A L a = algebraMap F L (algebraMap D F (Ideal.Quotient.mk I a))
    rw [hmk]; exact IsScalarTower.algebraMap_apply A F L a
  have : IsFractionRing D F := by
    refine ⟨?_, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
    · rintro ⟨d, hd⟩
      refine isUnit_iff_ne_zero.2 ?_
      show RingHom.kerLift g d ≠ 0
      rw [map_ne_zero_iff _ hinj]
      exact nonZeroDivisors.ne_zero hd
    · obtain ⟨a, b, hb, hab⟩ := hF z
      have hb' : (Ideal.Quotient.mk I b) ≠ 0 := by
        intro h0; apply hb; rw [← hmk, h0, map_zero]
      refine ⟨⟨Ideal.Quotient.mk I a, ⟨Ideal.Quotient.mk I b, mem_nonZeroDivisors_of_ne_zero hb'⟩⟩, ?_⟩
      show z * algebraMap D F (Ideal.Quotient.mk I b) = algebraMap D F (Ideal.Quotient.mk I a)
      rw [hmk, hmk]; exact hab
    · simp [hinj h]
  have hD : Module.Finite D (integralClosure D L) := finite_integralClosure K D F L p
  have heq : Subalgebra.toSubmodule (integralClosure A L) =
      (Subalgebra.toSubmodule (integralClosure D L)).restrictScalars A := by
    ext x
    show IsIntegral A x ↔ IsIntegral D x
    exact ⟨fun hx => hx.tower_top, fun hx => isIntegral_trans (A := D) x hx⟩
  show Module.Finite A (Subalgebra.toSubmodule (integralClosure A L))
  rw [Module.Finite.iff_fg, heq]
  exact (Module.Finite.iff_fg.1 hD).restrictScalars_of_surjective Ideal.Quotient.mk_surjective

end RamanujanPetersson.EtPBC.Nagata

namespace RamanujanPetersson.EtPBC.Nagata

universe v

end RamanujanPetersson.EtPBC.Nagata

end

end

-- ===== S4.Def_RP_EtPBC_A_EIdem =====
section

/-!
# S4-EtPBC-A, M4(E), EIdem: clopen sets, idempotents, and lifting clopens to a relative normalization

* `exists_idem`: a clopen open `C ⊆ X` is `X.basicOpen e` for an idempotent `e ∈ Γ(X, ⊤)`;
* `isClopen_basicOpen`: the basic open of an idempotent global section is clopen;
* **`exists_clopen_lift`**: for `h : X ⟶ W` (qcqs, `W` affine) and a clopen `C ⊆ X` there is a clopen `C'` of the relative
  normalization with `h.toNormalization ⁻¹ᵁ C' = C`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

universe u

/-- **Lifting clopen sets to the relative normalization** over an affine base. -/
theorem exists_clopen_lift {X W : Scheme.{u}} (h : X ⟶ W) [QuasiCompact h] [QuasiSeparated h] [IsAffine W]
    (C : X.Opens) (hC : IsClosed (C : Set X)) :
    ∃ C' : h.normalization.Opens, IsClopen (C' : Set h.normalization) ∧ h.toNormalization ⁻¹ᵁ C' = C := by
  obtain ⟨e, he, heC⟩ := exists_idem C hC
  let := (h.app ⊤).hom.toAlgebra
  let e₁ : Γ(X, h ⁻¹ᵁ ⊤) := X.presheaf.map (homOfLE le_top : h ⁻¹ᵁ ⊤ ⟶ ⊤).op e
  have he₁ : IsIdempotentElem e₁ := he.map (X.presheaf.map (homOfLE le_top : h ⁻¹ᵁ ⊤ ⟶ ⊤).op).hom
  have hT : ∀ V : X.Opens, V ≤ h ⁻¹ᵁ ⊤ := fun V x _ => Set.mem_univ (h.base x)
  have hb₁ : X.basicOpen e₁ = C := by
    rw [X.basicOpen_res, heC]
    exact inf_eq_right.2 (hT C)
  let iso := h.normalizationObjIso (isAffineOpen_top W)
  let e₂ : Γ(h.normalization, h.fromNormalization ⁻¹ᵁ ⊤) := iso.inv ⟨e₁, isIntegral_of_idem e₁ he₁⟩
  have he₂ : IsIdempotentElem e₂ := by
    have : IsIdempotentElem (⟨e₁, isIntegral_of_idem e₁ he₁⟩ : integralClosure Γ(W, ⊤) Γ(X, h ⁻¹ᵁ ⊤)) :=
      Subtype.ext he₁
    exact this.map iso.inv.hom
  have hval : h.toNormalization.appLE (h.fromNormalization ⁻¹ᵁ ⊤) (h ⁻¹ᵁ ⊤)
      (by simp [← Scheme.Hom.comp_preimage]) e₂ = e₁ := by
    have key := ConcreteCategory.congr_hom (h.normalizationObjIso_hom_val (isAffineOpen_top W))
      (iso.inv ⟨e₁, isIntegral_of_idem e₁ he₁⟩)
    refine key.symm.trans ?_
    rw [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    rfl
  let e₃ : Γ(h.normalization, ⊤) :=
    h.normalization.presheaf.map (homOfLE le_top : (⊤ : h.normalization.Opens) ⟶ h.fromNormalization ⁻¹ᵁ ⊤).op e₂
  have he₃ : IsIdempotentElem e₃ := he₂.map (h.normalization.presheaf.map
    (homOfLE le_top : (⊤ : h.normalization.Opens) ⟶ h.fromNormalization ⁻¹ᵁ ⊤).op).hom
  refine ⟨h.normalization.basicOpen e₃, isClopen_basicOpen e₃ he₃, ?_⟩
  have hb₃ : h.normalization.basicOpen e₃ = h.normalization.basicOpen e₂ := by
    rw [Scheme.basicOpen_res]
    exact inf_eq_right.2 le_top
  rw [hb₃, ← hb₁, ← hval]
  exact ((Scheme.basicOpen_appLE _ _ _ _ _).trans (inf_eq_right.2 (hT _))).symm

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_O2M2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M2: local vanishing of cohomology classes

* `exists_local_lift`: a section of the target of an epimorphism lifts on an etale neighbourhood of any point of
  the geometric fibre;
* `vanish_one`, `vanish_succ`, **`local_vanish`**: every `β ∈ Ext^{q+1}(Λ[Z], F)` dies on an etale neighbourhood
  `a : N ⟶ Z` of any point `z` of the geometric fibre of `Z` over `x` (dimension shifting along the injective
  presentation `0 → F → I → I/F → 0`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

variable (x : P) {Z : P.Etale} (z : (geomPtAt x).point.fiber.obj Z)

/-- **Local vanishing**: every class of `Ext^{q+1}(Λ[Z], F)` dies on an etale neighbourhood `a : N ⟶ Z` of any
point `z` of the geometric fibre of `Z` over `x`. -/
theorem local_vanish (q : ℕ) :
    ∀ (F : EtSh Λ P) (β : Ext.{u} (freeSh Λ Z) F (q + 1)),
      ∃ (N : P.Etale) (a : N ⟶ Z) (n : (geomPtAt x).point.fiber.obj N), (geomPtAt x).point.fiber.map a n = z ∧
        (Ext.mk₀ (freeMap Λ a)).comp β (zero_add (q + 1)) = 0 := by
  induction q with
  | zero => exact vanish_one x z
  | succ k ih => exact vanish_succ x z ih

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Fl2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`

* `extAdjMap_mk₀_comp`: the adjunction map on `Ext` is natural in the source;
* `lshFreeHom_natural`, `lshFreeInv_natural`: `Λ[e ∘ V] ≅ e_! Λ[V]` is natural in `V`;
* `toW W V : e ∘ V ⟶ W` (`e = W.hom`, `V : W.left.Etale`), `extFreeV : Ext_P(Λ[e ∘ V], F) ≃ Ext_W(Λ[V], F|_W)`;
* **`extFreeV_restrict`**: restricting `β ∈ Ext_P(Λ[W], F)` along `toW W V` is restricting `extFree β ∈ H(W, F|_W)`
  to `V`; **`restrict_eq_zero`**: if `extFree β` dies on `V`, then `β` dies on `e ∘ V`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

universe w v v' u₁ u₂ u

section Adj

end Adj

variable {Λ : Type u} [CommRing Λ]

section Nat

end Nat

section Obj

variable {P : Scheme.{u}}

theorem lshFreeInv_toW (W : P.Etale) (V : W.left.Etale) :
    lshFreeInv Λ W.hom V ≫ freeMap Λ (toW W V) =
      (lsh W.hom Λ).map (freeMap Λ (toTop V) ≫ (unitIso Λ W.left).hom) ≫ (freeLshIso Λ W).inv := by
  have hc : (lsh W.hom Λ).map (unitIso Λ W.left).hom ≫ (lsh W.hom Λ).map (unitIso Λ W.left).inv = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [freeLshIso_inv, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((lsh W.hom Λ).map (unitIso Λ W.left).hom), hc, Category.id_comp, toW, freeMap_comp,
    ← Category.assoc, lshFreeInv_natural, Category.assoc]

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2R3 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M6a (3): the multi-point MV complex maps to each one-point complex

For `k : ι`, an open `Uz ⊇ U₀` containing every point of every `S j` (`j ≠ k`):
* `copDescF` (maps out of `Λ[cop S]` from maps on the summands), `copι_copDescF`;
* `restSec`, `locτ₂`: the middle map `Λ[cop S] ⊞ Λ[U₀] ⟶ Λ[S k] ⊞ Λ[Uz]`;
* `loc_comm₁₂`, `loc_comm₂₃`, **`mvLocHom`**: a morphism of short complexes `mvCop ⟶ locC (S k)` with
  `τ₁ = copPr k` and `τ₃ = 𝟙`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
  (S : ι → P.Etale)

variable (U₀ : P.Opens) (k : ι) {Uz : P.Opens} (h : U₀ ≤ Uz)
  (hrng : ∀ j, j ≠ k → ∀ v : (S j).left, (S j).hom v ∈ Uz)

theorem loc_comm₁₂_fst :
    copPr Λ (fun j => prd (S j) (opEt U₀)) k ≫ freeMap Λ (prW (S k) (opEt U₀)) =
      freeMap Λ (copP₁ S U₀) ≫ copPr Λ S k := by
  refine freeCop_hom_ext _ (fun j => ?_)
  rw [← Category.assoc, ← Category.assoc, copι_copPr, ← freeMap_comp, copι_copP₁, freeMap_comp,
    Category.assoc, copι_copPr]
  by_cases hj : j = k
  · subst hj
    rw [copPrSec_self, copPrSec_self, Category.id_comp, Category.comp_id]
  · rw [copPrSec_ne _ hj, copPrSec_ne _ hj, Limits.zero_comp, Limits.comp_zero]

theorem loc_comm₂₃ :
    locτ₂ Λ S U₀ k h hrng ≫ biprod.desc (freeMap Λ (toTop (S k))) (freeMap Λ (toTop (opEt Uz))) =
      biprod.desc (freeMap Λ (toTop (cop S))) (freeMap Λ (toTop (opEt U₀))) ≫ 𝟙 _ := by
  rw [Category.comp_id, locτ₂_eq]
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc_assoc, biprod.inl_desc, biprod.lift_desc]
    exact loc_comm₂₃_inl (Λ := Λ) S k hrng
  · simp only [biprod.inr_desc_assoc, biprod.inr_desc, biprod.lift_desc, Limits.zero_comp, zero_add]
    rw [← freeMap_comp, toTop_ext (opEtMap h ≫ toTop (opEt Uz)) (toTop (opEt U₀))]

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Km2 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km2): splitting `H¹(X, Λ)` along a finite clopen decomposition

`S : ι → X.Etale` a finite family with `∐ S k ⟶ X` an isomorphism.
* `copIso : cop S ≅ etId X` (when `(cop S).hom` is an isomorphism);
* `toId`, `copι_copIso`; `splitPr k : Λ_X ⟶ Λ[S k]`, `splitIn k : Λ[S k] ⟶ Λ_X`, `sum_split : Σ_k pr_k ≫ in_k = 𝟙`;
* **`h1_split`**: every `c ∈ H¹(X, Λ)` is `Σ_k pr_k^* ((in_k)^* c)` with `(in_k)^* c ∈ Ext¹(Λ[S k], Λ_X)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV

universe u

section Split

variable {X : Scheme.{u}} {ι : Type u} (S : ι → X.Etale) [IsIso (cop S).hom]

variable (Λ : Type u) [CommRing Λ] [Fintype ι] [DecidableEq ι]

theorem sum_split : ∑ k, splitPr S Λ k ≫ splitIn S Λ k = 𝟙 _ := by
  calc ∑ k, splitPr S Λ k ≫ splitIn S Λ k
      = ((unitIso Λ X).inv ≫ freeMap Λ (copIso S).inv) ≫
          (∑ k, copPr Λ S k ≫ freeMap Λ (copι S k)) ≫
            (freeMap Λ (copIso S).hom ≫ (unitIso Λ X).hom) := by
        rw [Preadditive.sum_comp, Preadditive.comp_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [splitPr, splitIn, ← copι_copIso S k, freeMap_comp, Category.assoc]
    _ = 𝟙 _ := by
        rw [sum_copPr, Category.id_comp, Category.assoc, ← Category.assoc (freeMap Λ (copIso S).inv),
          ← freeMap_comp, Iso.inv_hom_id, freeMap_id, Category.id_comp, Iso.inv_hom_id]

/-- **`H¹` splits along a clopen decomposition.** -/
theorem h1_split (c : H Λ (unitSh Λ X) 1) :
    c = ∑ k, (Ext.mk₀ (splitPr S Λ k)).comp ((Ext.mk₀ (splitIn S Λ k)).comp c (zero_add 1))
      (zero_add 1) := by
  conv_lhs => rw [← Ext.mk₀_id_comp c, ← sum_split S Λ, ext_mk₀_sum, ext_sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Ext.mk₀_comp_mk₀_assoc]

end Split

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E5 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)

* generic: **`mapExact_comp_iso`**: for exact `Φ`, `Ψ`, `Φ'` and `τ : Φ ⋙ Ψ ≅ Φ'`, `Ψ(Φ ξ) ∘ τ_B = τ_A ∘ Φ' ξ`
  on `Ext¹` (enough injectives);
* for `m : W' ⟶ W` in `P.Etale`: `Etale m.left`, `etCompCompIso m`, `resCompIso Λ m : res W ⋙ res m ≅ res W'`;
* `diagSec Λ W : Λ_W ⟶ Λ[W]|_W` with `extFree_eq` (`extFree β = diagSec ∘ β|_W`) and `diagSec_sec`;
* **`diagSec_natural`**: `diagSec W' ≫ Λ[m]|_W' = unitRes m.left ≫ (diagSec W)|_W' ≫ (resCompIso m)_{Λ[W]}`.
`extFree_natural` is in O2E5b.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

section Gen

universe w v₁ u₁ v₂ u₂ v₃ u₃

end Gen

section Nat

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {W W' : P.Etale} (m : W' ⟶ W)

theorem diagSec_one (W : P.Etale) :
    ((diagSec Λ W).hom.app (op (etId W.left))).hom (oneSec Λ W.left) =
      ((freeSh Λ W).obj.map (etCompTop W).hom.op).hom (taut Λ W) := by
  rw [← diagSec_sec, freeEquiv_comp, unitIso_hom, freeToUnit, AddEquiv.apply_symm_apply]

end Nat

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Sh1 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree

* `shObj s`, `shι s`: a map `s : N ⟶ W` of etale `P`-schemes gives a sheet `N ⟶ N ×_P W` over `W`.
* `sheet_cover`: sheets that biject onto every geometric fibre cover `N ×_P W`; `sheet_sep`: distinct sheets
  do not meet; `shι_cancel`.
* **`push_epi`**: if `W` is quasi-compact separated etale over `P` with `n` points in every geometric fibre, then
  `push W.hom` preserves epimorphisms (stalk lifts on a splitting neighbourhood, glued over the sheets), and
  **`push_preservesFiniteColimits_of_deg`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtTr

universe u

variable {P : Scheme.{u}}

section Sheet

variable {W N : P.Etale}

theorem bij_of [QuasiCompact W.hom] {T L M₀ : P.Etale} (n : ℕ)
    (hn : ∀ y : P, Nat.card ((geomPtAt y).point.fiber.obj W) = n) (x : P)
    (τ : (geomPtAt x).point.fiber.obj W → (T ⟶ W))
    (hinj : ∀ (y : P) (v : (geomPtAt y).point.fiber.obj T) (p q : (geomPtAt x).point.fiber.obj W),
      (geomPtAt y).point.fiber.map (τ p) v = (geomPtAt y).point.fiber.map (τ q) v → p = q)
    (c : L ⟶ M₀) (e : M₀ ⟶ T) (y : P) (v : (geomPtAt y).point.fiber.obj L) :
    Function.Bijective fun p => (geomPtAt y).point.fiber.map (c ≫ e ≫ τ p) v := by
  have := finite_fiber W y
  refine Function.Injective.bijective_of_nat_card_le (fun p q hpq => hinj y
    ((geomPtAt y).point.fiber.map e ((geomPtAt y).point.fiber.map c v)) p q ?_) ((hn y).trans (hn x).symm).le
  simpa only [Functor.map_comp_apply] using hpq

end Sheet

section Lift

end Lift

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Sh2 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree

* `dg W`: the diagonal of `W ×_P W` (clopen: `isClopen_dg`); `dsec Λ W`: its indicator section of `Λ_W`;
* `shapφ Λ W : Λ[W] ⟶ π_* Λ_W` is the map given by `dsec` (`shapφ_taut`);
* `cval_S`: values of `Σ_a l_a · τ_a^* dsec` along a sheet;
* **`isIso_shapφ`**, **`shapIso`**: `shapφ` is an isomorphism (stalkwise: `stalk_inj`, `stalk_surj`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtTr

universe u

variable {P : Scheme.{u}}

section Dg

end Dg

section Iso

variable (Λ : Type u) [CommRing Λ] (W : P.Etale) [IsSeparated W.hom]

/-- **Values of `Σ_a l_a · τ_a^* dsec` along the sheet of `s`.** -/
theorem cval_S {T N : P.Etale} {ι : Type*} [Fintype ι] (τ : ι → (T ⟶ W)) (l : ι → Λ) (g : N ⟶ T)
    (s : N ⟶ W) (v : N.left) (q : ι) (hq : ∀ a, v ∈ agr (g ≫ τ a) s ↔ a = q) :
    cval (((unitSh Λ W.left).obj.map (shι s).op).hom (((unitSh Λ W.left).obj.map ((etPull W.hom).map g).op).hom
      (∑ a, l a • ((unitSh Λ W.left).obj.map ((etPull W.hom).map (τ a)).op).hom (dsec Λ W)))) v = l q := by
  classical
  refine (cval_map _ _ _).trans ((cval_map _ _ _).trans ?_)
  rw [cval_sum, Finset.sum_eq_single q]
  · rw [GenAlg.cval_smul, cval_map, cval_dsec, ind_dg Λ W (g ≫ τ q) s v _ (pt_eq W g (τ q) s v),
      Set.indicator_of_mem ((hq q).2 rfl)]
    exact mul_one (l q)
  · intro b _ hb
    rw [GenAlg.cval_smul, cval_map, cval_dsec, ind_dg Λ W (g ≫ τ b) s v _ (pt_eq W g (τ b) s v),
      Set.indicator_of_notMem (fun h => hb ((hq b).1 h)), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ q) h

end Iso

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E6b =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d1 (part 2): `extFreeU` is natural in the etale object

* `resHE_comp_mk₀`, `freeEquiv_unitRes`, `unitRes_one`;
* `unitRes_comp`: `1 ↦ 1` along `m.left`, then along `W.hom`, is `1 ↦ 1` along `W'.hom`; `resCompIso_unit`;
* **`extFreeU_natural`**: `extFreeU W' (ξ ∘ Λ[m]) = resLE m.left (extFreeU W ξ)` in degree `1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

/-- **`1 ↦ 1` is compatible with composition of etale maps.** -/
theorem unitRes_comp {W W' : P.Etale} (m : W' ⟶ W) :
    unitRes m.left Λ ≫ (res m.left Λ).map (unitRes W.hom Λ) ≫ (resCompIso Λ m).hom.app (unitSh Λ P) =
      unitRes W'.hom Λ := by
  rw [← cancel_epi (unitIso Λ W'.left).hom]
  apply (freeEquiv Λ (etId W'.left) _).injective
  have h1 : ((unitRes W.hom Λ).hom.app (op (etId W.left))).hom (oneSec Λ W.left) =
      ((unitSh Λ P).obj.map (toTop ((etComp W.hom).obj (etId W.left))).op).hom (oneSec Λ P) :=
    unitRes_one W.hom
  have hL : freeEquiv Λ (etId W'.left) _ ((unitIso Λ W'.left).hom ≫ unitRes m.left Λ ≫
      (res m.left Λ).map (unitRes W.hom Λ) ≫ (resCompIso Λ m).hom.app (unitSh Λ P)) =
      ((unitSh Λ P).obj.map ((etCompCompIso m).inv.app (etId W'.left) ≫
        (etComp W.hom).map (toTop ((etComp m.left).obj (etId W'.left))) ≫
          toTop ((etComp W.hom).obj (etId W.left))).op).hom (oneSec Λ P) := by
    rw [← Category.assoc, ← Category.assoc, freeEquiv_comp, freeEquiv_comp, freeEquiv_unitRes, resCompIso_app,
      oneRes]
    have hn := NatTrans.naturality_apply (φ := (unitRes W.hom Λ).hom)
      (toTop ((etComp m.left).obj (etId W'.left))).op (oneSec Λ W.left)
    simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [← h1]
    exact congrArg (fun z => ((unitSh Λ P).obj.map ((etCompCompIso m).inv.app (etId W'.left)).op).hom z) hn
  refine hL.trans (Eq.trans ?_ (freeEquiv_unitRes W'.hom).symm)
  exact congrArg (fun x => ((unitSh Λ P).obj.map x.op).hom (oneSec Λ P)) (toTop_ext _ _)

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Km7 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km7): Kummer decomposition of an unramified character

`ζ ∈ maxUnram A K` a primitive `N`-th root of unity fixed by `π₁(A)`, `N • Λ = 0`.
* `primd`: `ζ ^ (N / d)` is a primitive `d`-th root of unity for `d ∣ N`;
* **`exists_kum_dec`**: every `χ ∈ ChL A K Λ` is `Σ_i kumChi_{d_i}(α_i) g_i` with `α_i ^ {d_i} = u_i ∈ K`
  (cyclic decomposition `exists_cdec`, then Hilbert 90 `exists_kchar_eq` on each cyclic factor).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtPi1
  RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section KumDec

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {Λ : Type} [AddCommGroup Λ] {N : ℕ} [NeZero N]
  {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N)

variable (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 A K)), σ ζ = ζ) (hΛ : ∀ x : Λ, N • x = 0)

include hζΓ hΛ in
/-- **Kummer decomposition**: `χ = Σ_i kumChi_{d_i}(α_i) g_i`, `α_i ^ {d_i} = u_i ∈ K`. -/
theorem exists_kum_dec (χ : ChL A K Λ) :
    ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (_ : ∀ i, NeZero (d i)) (hdN : ∀ i, d i ∣ N) (g : ι → Λ)
      (α : ι → (maxUnram A K)ˣ) (u : ι → K), (∀ i, d i • g i = 0) ∧
      (∀ i, α i ∈ rad (⊤ : Subgroup (Pi1 A K)) (d i)) ∧
      (∀ i, (α i : maxUnram A K) ^ d i = algebraMap K (maxUnram A K) (u i)) ∧
      ∀ σ, (χ : Pi1 A K → Λ) σ = ∑ i, kumChi (primd hζ (hdN i)) (α i) (g i) σ := by
  classical
  obtain ⟨hχ, hl⟩ := mem_ChL.1 χ.2
  obtain ⟨ι, hι, d, hd, g, c, hdN, hg, hcl, hhom, hsum⟩ := exists_cdec hΛ χ.1 hχ hl hl.range_finite
  have hk : ∀ i, ∃ α : (maxUnram A K)ˣ, α ∈ rad (⊤ : Subgroup (Pi1 A K)) (d i) ∧
      ∀ σ : (⊤ : Subgroup (Pi1 A K)), kchar (primd hζ (hdN i)) α σ = c i σ := by
    intro i
    have := hd i
    have hζdΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 A K)), σ (ζ ^ (N / d i)) = ζ ^ (N / d i) := fun σ hσ => by
      rw [map_pow, hζΓ σ hσ]
    exact exists_kchar_eq (primd hζ (hdN i)) hζdΓ (fun σ : (⊤ : Subgroup (Pi1 A K)) => c i σ)
      ((hcl i).comp_continuous continuous_subtype_val) (fun σ τ => hhom i σ τ)
  choose α hα hαc using hk
  have hu : ∀ i, ∃ u : K, algebraMap K (maxUnram A K) u = (α i : maxUnram A K) ^ d i := fun i =>
    (InfiniteGalois.mem_bot_iff_fixed (k := K) (K := maxUnram A K) ((α i : maxUnram A K) ^ d i)).2
      (fun σ => hα i σ (Subgroup.mem_top σ))
  choose u hu using hu
  refine ⟨ι, hι, d, hd, hdN, g, α, u, hg, hα, fun i => (hu i).symm, fun σ => ?_⟩
  rw [hsum σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hd i
  unfold kumChi
  rw [hαc i]

end KumDec

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2KapP =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map

For `f : X₁ ⟶ X` etale between affine schemes whose rings are finite products of Dedekind domains, and a Kummer
class `kapS p (kumD α)` on the piece `p` of `X` (`α^d = u`):
* `kerMap f p₁ : Γ(X) → Γ(X₁) ⧸ p₁`, `exists_minimalPrime_le_ker`, `kerLift`, **`piHom_comp_eq`**
  (the piece `p₁` of `X₁` maps into the piece `q` of `X` through `Spec (Γ(X₁) ⧸ p₁) ⟶ Spec (Γ(X) ⧸ q)`),
  `injective_of_etale` (an etale map of domains is injective), `resLE_congr`, `resLE_kapS_self`, `resLE_kapS_ne`;
* **`resLE_kapS_kumD_eq_zero`**: if `u` becomes a `d`-th power in the fraction field of every piece of `X₁` lying
  over `p`, then `resLE f 1 (kapS p (kumD α)) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.GalTrE

universe u

section Fac

variable {X X₁ : Scheme.{0}} [IsAffine X] [IsAffine X₁] [IsNoetherianRing Γ(X, ⊤)] [IsNoetherianRing Γ(X₁, ⊤)]
  (h : ∀ (m : Ideal Γ(X, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (h₁ : ∀ (m : Ideal Γ(X₁, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (f : X₁ ⟶ X)

/-- **The piece `p₁` of `X₁` maps into the piece `q` of `X`.** -/
theorem piHom_comp_eq (p₁ : minimalPrimes Γ(X₁, ⊤)) (q : minimalPrimes Γ(X, ⊤))
    (hq : (q : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁)) :
    piHom (piEquiv h₁) p₁ ≫ f = Spec.map (CommRingCat.ofHom (kerLift hq)) ≫ piHom (piEquiv h) q := by
  have hr : f.appTop ≫ CommRingCat.ofHom (piEquiv h₁).toRingHom ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun p : minimalPrimes Γ(X₁, ⊤) => Γ(X₁, ⊤) ⧸ (p : Ideal Γ(X₁, ⊤))) p₁) =
      CommRingCat.ofHom (piEquiv h).toRingHom ≫
        CommRingCat.ofHom (Pi.evalRingHom (fun p : minimalPrimes Γ(X, ⊤) => Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) q) ≫
          CommRingCat.ofHom (kerLift hq) := by
    ext a
    rfl
  have e2 := congrArg (fun φ => Spec.map φ ≫ X.isoSpec.inv) hr
  simp only [Spec.map_comp, Category.assoc] at e2
  unfold piHom
  rw [Category.assoc, Category.assoc, ← Scheme.isoSpec_inv_naturality]
  exact e2

end Fac

section KappaRes

end KappaRes

section Red

end Red

section KapP

end KapP

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E7 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d2: purity on `W₁ = Spec B_t` with the chart Kummer class

* `LA k a = k[X]_{X-a}` (Dedekind, fraction field `RatFunc k`); `zetaA`, `gamA` (`gamA ^ N = X - a`);
* `xiA a hN Λ hΛ c : H¹(Spec k[X]_{X-a}, Λ)`: the Kummer class of `(X - a)^{1/N}` with coefficient `c`;
* `Wa c a = Spec k[X]_{X-a}` over `P` (the punctured chart neighbourhood), `phiA`, `toWa c a φ : W1 c φ a ⟶ Wa c a`;
* **`purity_W1`**: every `κ ∈ H¹(Spec B_t, Λ)` is `res_{toD1} κ₀ + res_{toWa} (xiA c')`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.Kummer
  RamanujanPetersson.EtPi1 RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtPBC.EtDed

section LA

variable (k : Type) [Field k] (a : k)

variable {k} [IsAlgClosed k] {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0)

include hN in
theorem exists_gamA : ∃ γ : (maxUnram (LA k a) (RatFunc k))ˣ, (γ : maxUnram (LA k a) (RatFunc k)) ^ N =
    algebraMap (RatFunc k) (maxUnram (LA k a) (RatFunc k))
      (algebraMap (LA k a) (RatFunc k) (algebraMap k[X] (LA k a) (X - C a))) := by
  obtain ⟨τ, hτ⟩ := exists_tau (B := k[X]) (t := X - C a) (LA k a) (RatFunc k) (isUnit_natCast_poly hN)
  exact ⟨τ, by rw [hτ, LA.algebraMap_algebraMap]⟩

/-- An `N`-th root of `X - a`, a unit of `maxUnram k[X]_{X-a} k(X)`. -/
def gamA : (maxUnram (LA k a) (RatFunc k))ˣ := Classical.choose (exists_gamA a hN)

include hN in
theorem gamA_pow : (gamA a hN : maxUnram (LA k a) (RatFunc k)) ^ N =
    algebraMap (RatFunc k) (maxUnram (LA k a) (RatFunc k))
      (algebraMap (LA k a) (RatFunc k) (algebraMap k[X] (LA k a) (X - C a))) :=
  Classical.choose_spec (exists_gamA a hN)

end LA

section Obj

end Obj

section Pur

end Pur

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T1 =====
section

/-!
# S4-EtPBC-A, O2 S5a: restriction of a free sheaf, graphs and section maps

* `resFreeIso Λ e T : Λ_U[e⁻¹T] ≅ (Λ[T])|_U` for etale `e : U ⟶ X` (`pullFreeIso` + `pullIsoRes`);
* `resFreeIso_taut`: its value on the tautological section is the pullback of `taut T` along the counit;
* `graph m : etId W.left ⟶ e⁻¹T` for `m : W ⟶ T` in `P.Etale` (adjoint to `W ≅ etComp (etId) ⟶ T`);
* `secMap Λ m := diagSec Λ W ≫ (res W.hom Λ).map Λ[m] : Λ_W ⟶ (Λ[T])|_W`, `secMap_comp`;
* **`secMap_graph`**: `unitIso.hom ≫ secMap m = Λ[graph m] ≫ resFreeIso.hom`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

universe u

section Res

end Res

section Graph

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}} {W T : P.Etale}

theorem secMap_sec (m : W ⟶ T) :
    freeEquiv Λ (etId W.left) _ ((unitIso Λ W.left).hom ≫ secMap Λ m) =
      ((freeSh Λ T).obj.map ((etCompTop W).hom ≫ m).op).hom (taut Λ T) := by
  rw [secMap, ← Category.assoc, freeEquiv_comp, diagSec_sec]
  have hu := NatTrans.naturality_apply (φ := (freeMap Λ m).hom) (etCompTop W).hom.op (taut Λ W)
  have ht := freeMap_taut (Λ := Λ) m
  have hc := congrArg (fun z => ((freeSh Λ T).obj.map (etCompTop W).hom.op).hom z) ht
  refine hu.trans (hc.trans ?_)
  first
    | exact (congrArg (fun φ => ConcreteCategory.hom φ (taut Λ T))
        ((freeSh Λ T).obj.map_comp m.op (etCompTop W).hom.op)).symm
    | (rw [op_comp, Functor.map_comp]; rfl)

end Graph

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2UK2a =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2UK2a): a good chart through a geometric point

For `N : P.Etale` lying over the chart `c : 𝔸¹ ⟶ P`, a closed Galois-trivial point `z` and a geometric point `n` of
`N` over `z`:
* **`exists_goodChart`**: there are `φ₁ : k[X] ⟶ B₁` (`Spec B₁ ⟶ 𝔸¹ ⟶ P` etale) and `d : chEt c φ₁ ⟶ N` such that
  `chEt c φ₁` has exactly one geometric point over `z`, and every point of `chEt c φ₁` maps into `Uo ∪ {z}` when
  every point of `N` does (the data of `locC_shortExact`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

section GoodChart

variable {k : Type u} [Field k] {P : Scheme.{u}} (c : A1 k ⟶ P) [IsOpenImmersion c]

/-- **A good chart through a geometric point.** -/
theorem exists_goodChart {z : P} (hzc : IsClosed ({z} : Set P)) (hG : Subsingleton (Gal z)) {Uo : P.Opens}
    (N : P.Etale) (hNc : ∀ v : N.left, N.hom v ∈ Set.range c) (n : (geomPtAt z).point.fiber.obj N)
    (hNr : ∀ v : N.left, N.hom v ∈ Uo ∨ N.hom v = z) :
    ∃ (B₁ : CommRingCat.{u}) (φ₁ : CommRingCat.of k[X] ⟶ B₁) (_ : Etale (Spec.map φ₁ ≫ c)) (_ : chEt c φ₁ ⟶ N),
      Subsingleton ((geomPtAt z).point.fiber.obj (chEt c φ₁)) ∧
      Nonempty ((geomPtAt z).point.fiber.obj (chEt c φ₁)) ∧
      ∀ v : (chEt c φ₁).left, (chEt c φ₁).hom v ∈ Uo ∨ (chEt c φ₁).hom v = z := by
  obtain ⟨V', hsub, ⟨n'⟩, -⟩ := exists_opn_pt z hzc hG N n
  have hN'c : ∀ v : (opn N V').left, (opn N V').hom v ∈ Set.range c := fun v => hNc (V'.ι v)
  obtain ⟨V, hVa, hwV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (Scheme.isBasis_affineOpens (opn N V').left)) (show fpt z n' ∈ (⊤ : (opn N V').left.Opens) from trivial)
  have hV : IsAffineOpen V := hVa
  have hVc : ∀ v ∈ V, (opn N V').hom v ∈ Set.range c := fun v _ => hN'c v
  let q := hV.primeIdealOf ⟨fpt z n', hwV⟩
  have hqw : hV.fromSpec q = fpt z n' := hV.fromSpec_primeIdealOf _
  have hq1 : (1 : Γ((opn N V').left, V)) ∉ q.asIdeal := fun h => q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hdisj : Disjoint (Submonoid.powers (1 : Γ((opn N V').left, V)) : Set Γ((opn N V').left, V))
      (q.asIdeal : Set Γ((opn N V').left, V)) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime 1).2 hq1
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (1 : Γ((opn N V').left, V)))
    (Localization.Away (1 : Γ((opn N V').left, V))) q.asIdeal q.isPrime hdisj
  have hD₁ : Subsingleton ((geomPtAt z).point.fiber.obj (D1 c hV hVc (1 : Γ((opn N V').left, V)))) :=
    ⟨fun b b' => fib_injective_of_mono (d1 c hV hVc 1) _ (Subsingleton.elim _ _)⟩
  let v₁ : Spec (CommRingCat.of (Localization.Away (1 : Γ((opn N V').left, V)))) :=
    ⟨q.asIdeal.map (algebraMap Γ((opn N V').left, V) (Localization.Away (1 : Γ((opn N V').left, V)))), hprime⟩
  have hv₁ : (d1 c hV hVc 1).left v₁ = fpt z n' := by
    show hV.fromSpec (Spec.map (locG (1 : Γ((opn N V').left, V))) v₁) = fpt z n'
    have : Spec.map (locG (1 : Γ((opn N V').left, V))) v₁ = q := PrimeSpectrum.ext
      (IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers 1) (Localization.Away 1) q.isPrime hdisj)
    rw [this, hqw]
  obtain ⟨b, -, -⟩ := exists_lift_fib (d1 c hV hVc 1) _ n' v₁ hv₁
  refine ⟨CommRingCat.of (Localization.Away (1 : Γ((opn N V').left, V))), phiG c hV hVc 1, inferInstance,
    d1 c hV hVc 1 ≫ opnι N V', hD₁, ⟨b⟩, fun v => ?_⟩
  have e := d1_apply c hV hVc 1 v
  have e2 : (opn N V').hom ((d1 c hV hVc 1).left v) = N.hom ((opnι N V').left ((d1 c hV hVc 1).left v)) := rfl
  rcases hNr ((opnι N V').left ((d1 c hV hVc 1).left v)) with h1 | h1
  · exact Or.inl ((congrArg (· ∈ Uo) (e.trans e2)).mpr h1)
  · exact Or.inr ((e.trans e2).trans h1)

end GoodChart

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPi1_FunA =====
section

/-!
# S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change

`A → A'`, `K → K'` compatible (`A → K → K'`, `A → A' → K'`), `ι : K̄ →ₐ[K] K̄'` any `K`-embedding.

* `bcField f = K'(roots of f)` in `K̄'` (splitting field, finite, Galois when `f` is separable);
* `rootSet_bc`: the roots of `f` in `K̄'` are the `ι`-images of its roots in `K̄`;
* `icMap`: `integralClosure A L → integralClosure A' L'` induced by `ι`;
* `bcField_unram`: for `L ∈ unramSet A K` the splitting field of `L` over `K'` has trivial inertia over `A'`
  (an inertia element restricts, via `ι`, to an inertia element of `Gal(L/K)`, which is trivial);
* `map_mem_maxUnram`: `ι (K_U(A)) ⊆ K_U(A')`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace EtPi1

open GalCover Lefschetz Polynomial

noncomputable section

section FunA

variable {A K A' K' : Type} [CommRing A] [Field K] [Algebra A K]
  [CommRing A'] [Field K'] [Algebra A' K'] [Algebra K K'] [Algebra A A'] [Algebra A K']
  [IsScalarTower A K K'] [IsScalarTower A A' K']
  (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure K')

/-- **`ι` maps `K_U(A)` into `K_U(A')`.** -/
theorem map_mem_maxUnram {y : AlgebraicClosure K} (hy : y ∈ maxUnram A K) : ι y ∈ maxUnram A' K' := by
  obtain ⟨L, hL, hyL⟩ := (Lefschetz.mem_maxUnram_iff A K y).1 hy
  have := hL.1
  have := hL.2.1
  obtain ⟨f, hsep, hspl⟩ := IsGalois.is_separable_splitting_field (F := K) (E := L)
  have : IsGalois K' (bcField (K' := K') f) := bcField_isGalois hsep
  exact (Lefschetz.mem_maxUnram_iff A' K' _).2 ⟨bcField f, ⟨inferInstance, inferInstance, bcField_unram hL f⟩,
    map_mem_bcField ι f ⟨y, hyL⟩⟩

end FunA

end

end EtPi1
end RamanujanPetersson


end

-- ===== S4.Def_RP_EtPBC_A_O2PPTa =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2PPTa): moving a Kummer radical along a map of fields

GLOB/REL PLAN v1 (5), field part. For `K → K'` (with `A → A'` compatible) and a radical `α ∈ K_U(A)` with
`α ^ d = u`, **`exists_rad_map`** gives a radical `γ ∈ K_U(A')` with `γ ^ d = u` in `K'` (`γ = ι α` for an
embedding `ι : K̄ →ₐ[K] K̄'`, which maps `K_U(A)` into `K_U(A')` by `map_mem_maxUnram`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section Rad

variable {A K A' K' : Type} [CommRing A] [Field K] [Algebra A K]
  [CommRing A'] [Field K'] [Algebra A' K'] [Algebra K K'] [Algebra A A'] [Algebra A K']
  [IsScalarTower A K K'] [IsScalarTower A A' K']

/-- **Moving a radical along `K → K'`**. -/
theorem exists_rad_map {d : ℕ} {α : (maxUnram A K)ˣ} {u : K}
    (hu : (α : maxUnram A K) ^ d = algebraMap K (maxUnram A K) u) :
    ∃ γ : (maxUnram A' K')ˣ, γ ∈ rad (⊤ : Subgroup (Pi1 A' K')) d ∧
      (γ : maxUnram A' K') ^ d = algebraMap K' (maxUnram A' K') (algebraMap K K' u) := by
  let ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure K' :=
    IsAlgClosed.lift (R := K) (S := AlgebraicClosure K) (M := AlgebraicClosure K')
  have hy : ι ((α : maxUnram A K) : AlgebraicClosure K) ∈ maxUnram A' K' :=
    map_mem_maxUnram (A := A) (A' := A') ι ((α : maxUnram A K)).2
  let γ₀ : maxUnram A' K' := ⟨_, hy⟩
  have hγ₀ : γ₀ ≠ 0 := by
    intro h0
    have h1 : ι ((α : maxUnram A K) : AlgebraicClosure K) = 0 := congrArg Subtype.val h0
    have h1' := (map_eq_zero_iff ι (fun a b h => ι.toRingHom.injective h)).1 h1
    exact α.ne_zero (Subtype.ext h1')
  have hpow : γ₀ ^ d = algebraMap K' (maxUnram A' K') (algebraMap K K' u) := by
    apply Subtype.ext
    have h2 : (((α : maxUnram A K) ^ d : maxUnram A K) : AlgebraicClosure K) =
        algebraMap K (AlgebraicClosure K) u := by
      rw [hu]; rfl
    have h3 : ι ((((α : maxUnram A K) ^ d : maxUnram A K)) : AlgebraicClosure K) =
        algebraMap K' (AlgebraicClosure K') (algebraMap K K' u) := by
      rw [h2, AlgHom.commutes, IsScalarTower.algebraMap_apply K K' (AlgebraicClosure K')]
    have h4 : ι (((α : maxUnram A K) : AlgebraicClosure K) ^ d) =
        algebraMap K' (AlgebraicClosure K') (algebraMap K K' u) := h3
    rw [map_pow] at h4
    exact h4
  refine ⟨Units.mk0 γ₀ hγ₀, mem_rad_of_pow _ (x := algebraMap K K' u) ?_, ?_⟩ <;> exact hpow

end Rad

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB2b =====
section

/-!
# S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

section TB2b

variable {Λ : Type u} [CommRing Λ]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Etale)

theorem rhoO_eqG (V : X.Etale) (fV : V.left ⟶ W.left) (sq : V.hom ≫ f = fV ≫ W.hom) {T : Y.Etale} (m : W ⟶ T)
    (m' : V ⟶ (etPull f).obj T) (hm : m'.left ≫ pullback.fst T.hom f = fV ≫ m.left) :
    ((etPullCompIso fV W.hom).hom.app T).op ≫ (etPullCongr sq T).op ≫
      ((etPullCompIso V.hom f).inv.app T).op ≫ (graph m').op =
    ((etPull fV).map (graph m)).op ≫ (etIdPull fV).hom.op :=
  Quiver.Hom.unop_inj (rhoT_eqG f W V fV sq m m' hm)

end TB2b

end RamanujanPetersson.EtPBC.EtMV

end

end


