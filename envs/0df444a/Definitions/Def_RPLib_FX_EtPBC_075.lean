-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_075
-- name    : RPLib_FX_EtPBC_075
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:14:40.960508+00:00
-- url     : https://prove2.me/theorems/9ffb10f6-2b60-5bd7-8b8a-a7b2817bffe8
-- title:
--   Proper base change for the projective line, library file 075
-- statement:
--   File 075 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Km4b`: S4-EtPBC-A, O2 M6 (O2Km4b): `H¹` of an affine scheme whose ring is a product of Dedekind domains
--   * `S4.Def_RP_EtPBC_A_O2N4`: S4-EtPBC-A, O2 M5 P0: `resMapX` on ring elements (the bridge to field-level Kummer data)
--   * `S4.Def_RP_EtPBC_A_O2KapF`: S4-EtPBC-A, O2 M6 (O2KapF): functoriality of `resLE` and the field-level Kummer kill
--   * `S4.Def_RP_EtPBC_A_O2K1`: S4-EtPBC-A, O2 M5 N2: the Kummer class `ξ` on `Spec A0[1/s]` restricts to `κ_t` on `Spec B[1/t]`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_036
import Definitions.Def_RPLib_FX_EtPBC_067
import Definitions.Def_RPLib_FX_EtPBC_068
import Definitions.Def_RPLib_FX_EtPBC_069

/-!
# Proper base change for the projective line, library file 075

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Km4b`: S4-EtPBC-A, O2 M6 (O2Km4b): `H¹` of an affine scheme whose ring is a product of Dedekind domains
* `S4.Def_RP_EtPBC_A_O2N4`: S4-EtPBC-A, O2 M5 P0: `resMapX` on ring elements (the bridge to field-level Kummer data)
* `S4.Def_RP_EtPBC_A_O2KapF`: S4-EtPBC-A, O2 M6 (O2KapF): functoriality of `resLE` and the field-level Kummer kill
* `S4.Def_RP_EtPBC_A_O2K1`: S4-EtPBC-A, O2 M5 N2: the Kummer class `ξ` on `Spec A0[1/s]` restricts to `κ_t` on `Spec B[1/t]`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2Km4b =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km4b): `H¹` of an affine scheme whose ring is a product of Dedekind domains

**`h1_exists_kappa`**: if `Γ = Γ(X, ⊤)` is noetherian, its localizations at maximal ideals are domains and its
quotients by minimal primes are Dedekind, every `c ∈ H¹(X, Λ)` is `Σ_p kapS h Λ p (χ_p)` with `χ_p` a character of
`π₁(Γ ⧸ p)` (`kappaLH_surj` on each piece, `h1_split`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur

section Kappa

variable {X : Scheme.{0}} [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
  (h : ∀ (m : Ideal Γ(X, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [∀ p : minimalPrimes Γ(X, ⊤), IsDedekindDomain (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))]
  [Fintype (minimalPrimes Γ(X, ⊤))] [DecidableEq (minimalPrimes Γ(X, ⊤))] (Λ : Type) [CommRing Λ]

theorem kapS_eq_eS (p : minimalPrimes Γ(X, ⊤))
    (χ : ChL (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) Λ) :
    kapS h Λ p χ = (Ext.mk₀ (splitPr (piS (piEquiv h)) Λ p)).comp ((h1_eS h Λ p).symm
      (kappaLH (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) Λ χ))
      (zero_add 1) :=
  kapS_apply h Λ p χ

end Kappa

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N4 =====
section

/-!
# S4-EtPBC-A, O2 M5 P0: `resMapX` on ring elements (the bridge to field-level Kummer data)

* `algebraMap_residueFieldIso_inv_residueFieldMap` (category level): for `φ : R ⟶ S` and `y : Spec S`,
  `R → κ(φ y) → κ(y)` equals `R → S → κ(y)`;
* `resMapX_spec`, `resMapX_toGen`: `resMapX (Spec.map φ) h (toGen A a) = toGen A' (φ a)`;
* `resMapX_fracIso`: for `ψ : K → K'` extending `φ`, `resMapX (fracIso A K k) = fracIso A' K' (ψ k)`;
* `sepX_genEmb_algebraMap`: `sepX (genEmb (k)) = genEmb (ψ k)` for `k ∈ K`;
* **`resLE_kappaL_kum_field`**: NAT for Kummer classes along `Spec.map φ` when `ζ` and `γ^N` come from `K`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer

section Cat

universe u

end Cat

section Gen

variable {A K A' K' : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing A'] [IsDomain A'] [Field K'] [Algebra A' K'] [IsFractionRing A' K']
  (φ : CommRingCat.of A ⟶ CommRingCat.of A') [Etale (Spec.map φ)] (h : Spec.map φ (genPt A') = genPt A)

variable [IsIntegrallyClosed A] [IsNoetherianRing A] [IsIntegrallyClosed A'] [IsNoetherianRing A']
  {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N] {ζ : maxUnram A K} {ζ' : maxUnram A' K'}
  (hζ : IsPrimitiveRoot ζ N) (hζ' : IsPrimitiveRoot ζ' N) (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 A K)), σ ζ = ζ)
  (hζΓ' : ∀ σ ∈ (⊤ : Subgroup (Pi1 A' K')), σ ζ' = ζ')

include h in
/-- **NAT for Kummer classes, field form**: along `Spec.map φ` (etale, `η' ↦ η`) with `ψ : K → K'` extending
`φ`, the class of `kchar γ` restricts to the class of `kchar γ'` when `ζ = z`, `ζ' = ψ z`, `γ^N = u`,
`γ'^N = ψ u` for `z u ∈ K`. -/
theorem resLE_kappaL_kum_field (ψ : K →+* K')
    (hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (φ.hom a)) {z u : K}
    (hz : ζ = algebraMap K (maxUnram A K) z) (hz' : ζ' = algebraMap K' (maxUnram A' K') (ψ z))
    {γ : (maxUnram A K)ˣ} (hγ : γ ∈ rad (⊤ : Subgroup (Pi1 A K)) N)
    {γ' : (maxUnram A' K')ˣ} (hγ' : γ' ∈ rad (⊤ : Subgroup (Pi1 A' K')) N) {c : Λ} (hc : N • c = 0)
    (hu : (γ : maxUnram A K) ^ N = algebraMap K (maxUnram A K) u)
    (hu' : (γ' : maxUnram A' K') ^ N = algebraMap K' (maxUnram A' K') (ψ u)) :
    resLE (Spec.map φ) 1 (kappaL A K Λ (kumChi_mul hζ hζΓ hγ hc) (kumChi_isLocallyConstant hζ γ c)) =
      kappaL A' K' Λ (kumChi_mul hζ' hζΓ' hγ' hc) (kumChi_isLocallyConstant hζ' γ' c) :=
  resLE_kappaL_kum (Spec.map φ) h hζ hζ' hζΓ hζΓ' hγ hγ' hc
    (by rw [hz, hz', sepX_genEmb_algebraMap φ h ψ hψ])
    (by rw [hu, hu', sepX_genEmb_algebraMap φ h ψ hψ])

end Gen

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2KapF =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2KapF): functoriality of `resLE` and the field-level Kummer kill

* **`resLE_comp g' g c`**: `resLE (g' ≫ g) 1 c = resLE g' 1 (resLE g 1 c)` (from `extFreeU_natural` over `X`);
* **`resLE_kumD_eq_zero`**: along an etale `Spec.map φ` (`η' ↦ η`) with `ψ : K → K'` extending `φ`, the class
  `κ(kumD α)` with `α^d = u` dies once `ψ u = v^d` in `K'` (`resLE_kappaL_kum_field`, then `kchar_of_fix`).
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

section ResComp

variable {Λ : Type u} [CommRing Λ]

/-- **`resLE` is functorial** (degree `1`). -/
theorem resLE_comp {X₂ X₁ X : Scheme.{u}} (g' : X₂ ⟶ X₁) (g : X₁ ⟶ X) [Etale g'] [Etale g]
    (c : H Λ (unitSh Λ X) 1) : resLE (g' ≫ g) 1 c = resLE g' 1 (resLE g 1 c) := by
  obtain ⟨ξ, rfl⟩ := (extFreeU Λ (etId X) 1).surjective c
  let V : X.Etale := Scheme.Etale.mk g
  let V' : X.Etale := Scheme.Etale.mk (g' ≫ g)
  let m' : V' ⟶ V := MorphismProperty.Over.homMk g' rfl
  have h4 : m' ≫ toTop V = toTop V' := MorphismProperty.Over.Hom.ext (by exact rfl)
  have e : (Ext.mk₀ (freeMap Λ m')).comp ((Ext.mk₀ (freeMap Λ (toTop V))).comp ξ (zero_add 1)) (zero_add 1) =
      (Ext.mk₀ (freeMap Λ (toTop V'))).comp ξ (zero_add 1) := by
    rw [Ext.mk₀_comp_mk₀_assoc, ← freeMap_comp, h4]
  have h1 := extFreeU_natural (Λ := Λ) (toTop V) ξ
  have h3 := extFreeU_natural (Λ := Λ) (toTop V') ξ
  have h2 := extFreeU_natural (Λ := Λ) m' ((Ext.mk₀ (freeMap Λ (toTop V))).comp ξ (zero_add 1))
  rw [e, h3, h1] at h2
  exact h2

end ResComp

section KapF

end KapF

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2K1 =====
section

/-!
# S4-EtPBC-A, O2 M5 N2: the Kummer class `ξ` on `Spec A0[1/s]` restricts to `κ_t` on `Spec B[1/t]`

`A0 → B` etale, `s ∈ A0`, `As = A0[1/s]`, `t = s|_B`, `Bt = B[1/t]` (so `Spec Bt → Spec As` is etale).

* `etale_as`: `Spec Bt → Spec As` is etale; `map_genPt_of_injective`: an injective map of domains sends generic point
  to generic point;
* `resLE_kum_as` (N2): `res (κ(kumChi ζ γ c)) = κ(kumChi ψζ τ c)` for `γ ^ N = s` over `As`, `τ ^ N = s` over `Bt`;
* **`purity_xi`**: every `κ ∈ H¹(Spec Bt, Λ)` is `res_B κ₀ + res_As ξ(c)`, `ξ(c) = κ(kumChi ζ γ c)` the global Kummer
  class of `s^{1/N}` on `Spec As` (`B` Dedekind, `(t)` prime, `N` invertible in `B`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer RamanujanPetersson.EtPi1
  RamanujanPetersson.EtCompact.GalTrE

section Kas

variable {A0 As F Bt K : Type} [CommRing A0] {s : A0}
  [CommRing As] [IsDomain As] [IsIntegrallyClosed As] [IsNoetherianRing As] [Algebra A0 As]
  [Field F] [Algebra As F] [IsFractionRing As F]
  [CommRing Bt] [IsDomain Bt] [IsIntegrallyClosed Bt] [IsNoetherianRing Bt] [Algebra As Bt]
  [Field K] [Algebra Bt K] [IsFractionRing Bt K]
  [Etale (Spec.map (CommRingCat.ofHom (algebraMap As Bt)))]
  (ψ : F →+* K) (hψ : ∀ a : As, ψ (algebraMap As F a) = algebraMap Bt K (algebraMap As Bt a))
  {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N] {z : F} (hz : IsPrimitiveRoot z N)

include hψ in
/-- **N2**: the Kummer class of `s^{1/N}` on `Spec As` restricts to the Kummer class of `s^{1/N}` on `Spec Bt`. -/
theorem resLE_kum_as {u : As} {γ : (maxUnram As F)ˣ}
    (hγ : (γ : maxUnram As F) ^ N = algebraMap F (maxUnram As F) (algebraMap As F u))
    {τ : (maxUnram Bt K)ˣ} (hτ : (τ : maxUnram Bt K) ^ N = algebraMap K (maxUnram Bt K) (ψ (algebraMap As F u)))
    {c : Λ} (hc : N • c = 0) :
    resLE (Spec.map (CommRingCat.ofHom (algebraMap As Bt))) 1
        (kappaL As F Λ (kumChi_mul (zetaE_prim As hz) (zetaE_fix As z) (mem_rad_of_pow_eq hγ) hc)
          (kumChi_isLocallyConstant (zetaE_prim As hz) γ c)) =
      kappaL Bt K Λ (kumChi_mul (zetaE_prim Bt (hz.map_of_injective ψ.injective)) (zetaE_fix Bt (ψ z))
          (mem_rad_of_pow_eq hτ) hc)
        (kumChi_isLocallyConstant (zetaE_prim Bt (hz.map_of_injective ψ.injective)) τ c) := by
  have hinj : Function.Injective (algebraMap As Bt) := fun a b hab =>
    IsFractionRing.injective As F (ψ.injective (by rw [hψ, hψ, hab]))
  exact resLE_kappaL_kum_field (CommRingCat.ofHom (algebraMap As Bt)) (map_genPt_of_injective _ hinj)
    (zetaE_prim As hz) (zetaE_prim Bt (hz.map_of_injective ψ.injective)) (zetaE_fix As z) (zetaE_fix Bt (ψ z))
    ψ hψ rfl rfl (mem_rad_of_pow_eq hγ) (mem_rad_of_pow_eq hτ) hc hγ hτ

end Kas

section PurXi

end PurXi

end RamanujanPetersson.EtCompact.Pur

end

end


