-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_178
-- name    : RPLib_FX_EtPBC_178
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:12:47.183857+00:00
-- url     : https://prove2.me/theorems/108e932e-8ad6-539a-93f5-aa532ccc9052
-- title:
--   Proper base change for the projective line, library file 178
-- statement:
--   File 178 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2E7`: S4-EtPBC-A, O2 C-plan S4d2: purity on `W₁ = Spec B_t` with the chart Kummer class
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_170

/-!
# Proper base change for the projective line, library file 178

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2E7`: S4-EtPBC-A, O2 C-plan S4d2: purity on `W₁ = Spec B_t` with the chart Kummer class
-/

set_option autoImplicit false

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

end LA

section Obj

end Obj

section Pur

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P)
  [IsOpenImmersion c] {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)
  {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) (hΛ : ∀ x : Λ, N • x = 0)

include hN hΛ in
/-- **Purity at `W₁`**: `H¹(Spec B_t, Λ) = res_{toD1} H¹(Spec B, Λ) + res_{toWa} ξ_a(Λ)`. -/
theorem purity_W1 (hφ : φ.hom.Etale) [IsDedekindDomain B] (ht : φ.hom (X - C a) ≠ 0)
    (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime) (κ : H Λ (unitSh Λ (W1 c φ a).left) 1) :
    ∃ (κ0 : H Λ (unitSh Λ (chEt c φ).left) 1) (c' : Λ),
      κ = resLE (toD1 c φ a).left 1 κ0 + resLE (toWa c a φ).left 1 (xiA a hN Λ hΛ c') := by
  classical
  letI : Algebra k[X] B := φ.hom.toAlgebra
  haveI : Algebra.Etale k[X] B := RingHom.etale_algebraMap.1 hφ
  haveI : IsLocalization.Away (algebraMap k[X] B (X - C a)) (Localization.Away (φ.hom (X - C a))) :=
    Localization.isLocalization
  have hle : Submonoid.powers (φ.hom (X - C a)) ≤ nonZeroDivisors B :=
    powers_le_nonZeroDivisors_of_noZeroDivisors ht
  haveI : IsDomain (Localization.Away (φ.hom (X - C a))) := IsLocalization.isDomain_localization hle
  haveI : IsDedekindDomain (Localization.Away (φ.hom (X - C a))) :=
    IsLocalization.isDedekindDomain B hle (Localization.Away (φ.hom (X - C a)))
  letI : Algebra (LA k a) (Localization.Away (φ.hom (X - C a))) := (phiA a φ).hom.toAlgebra
  haveI : IsScalarTower k[X] (LA k a) (Localization.Away (φ.hom (X - C a))) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (IsScalarTower.algebraMap_apply k[X] B (Localization.Away (φ.hom (X - C a))) x).trans (phiA_apply a φ x).symm
  have htK : IsUnit (algebraMap B (FractionRing B) (φ.hom (X - C a))) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective B (FractionRing B))).2 ht)
  letI : Algebra (Localization.Away (φ.hom (X - C a))) (FractionRing B) :=
    (Localization.awayLift (algebraMap B (FractionRing B)) _ htK).toAlgebra
  haveI : IsScalarTower B (Localization.Away (φ.hom (X - C a))) (FractionRing B) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq (hg := htK) (a := x)).symm
  haveI : IsFractionRing (Localization.Away (φ.hom (X - C a))) (FractionRing B) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (φ.hom (X - C a)))
      (Localization.Away (φ.hom (X - C a))) (FractionRing B)
  haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap (LA k a) (Localization.Away (φ.hom (X - C a)))))) :=
    etale_as k[X] B (X - C a)
  haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (φ.hom (X - C a)))))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2
      (RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway (φ.hom (X - C a))))
  have hφi : Function.Injective (algebraMap k[X] B) := algebraMap_injective_of_flat
  have hinjA : Function.Injective (Localization.awayMap φ.hom (X - C a)) :=
    Localization.awayMap_injective_iff.2 fun x hx =>
      ⟨0, by rw [(injective_iff_map_eq_zero _).1 hφi x hx, mul_zero]⟩
  have hinj : Function.Injective ((algebraMap (Localization.Away (φ.hom (X - C a))) (FractionRing B)).comp
      (algebraMap (LA k a) (Localization.Away (φ.hom (X - C a))))) :=
    (IsFractionRing.injective _ (FractionRing B)).comp hinjA
  let ψ : RatFunc k →+* FractionRing B := IsFractionRing.lift hinj
  have hψ : ∀ x : LA k a, ψ (algebraMap (LA k a) (RatFunc k) x) =
      algebraMap (Localization.Away (φ.hom (X - C a))) (FractionRing B)
        (algebraMap (LA k a) (Localization.Away (φ.hom (X - C a))) x) :=
    fun x => IsFractionRing.lift_algebraMap hinj x
  have hNB : IsUnit (N : B) := by
    have h := (isUnit_iff_ne_zero.2 hN).map (φ.hom.comp C)
    rwa [map_natCast] at h
  obtain ⟨κ0, c', hκ⟩ := purity_xi (A0 := k[X]) (s := X - C a) (B := B) ψ hψ ht hP hNB hΛ (zetaA_prim hN)
    (gamA_pow a hN) κ
  exact ⟨κ0, c', hκ⟩

end Pur

end RamanujanPetersson.EtPBC.EtMV

end

end


