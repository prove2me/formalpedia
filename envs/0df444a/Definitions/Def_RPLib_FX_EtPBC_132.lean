-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_132
-- name    : RPLib_FX_EtPBC_132
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:19:31.150775+00:00
-- url     : https://prove2.me/theorems/2abcddd0-39e3-5c46-8322-5e4721e0b8b2
-- title:
--   Proper base change for the projective line, library file 132
-- statement:
--   File 132 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2P3b`: S4-EtPBC-A, O2 M5 P3b: purity for `H¹(Spec B[1/t], Λ)`
--   * `S4.Def_RP_EtPBC_A_O2T4b`: S4-EtPBC-A, O2 S5d (O2T4b): `thetaM_res`, classes with coefficients `clsD`
--   * `S4.Def_RP_EtPBC_A_O2T4d`: S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_075
import Definitions.Def_RPLib_FX_EtPBC_124

/-!
# Proper base change for the projective line, library file 132

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2P3b`: S4-EtPBC-A, O2 M5 P3b: purity for `H¹(Spec B[1/t], Λ)`
* `S4.Def_RP_EtPBC_A_O2T4b`: S4-EtPBC-A, O2 S5d (O2T4b): `thetaM_res`, classes with coefficients `clsD`
* `S4.Def_RP_EtPBC_A_O2T4d`: S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2P3b =====
section

/-!
# S4-EtPBC-A, O2 M5 P3b: purity for `H¹(Spec B[1/t], Λ)`

`B` Dedekind, `Bt = B[1/t]` with `(t)` prime, `K = Frac B`, `N` invertible in `B`, `N • Λ = 0`, `ζ₀ ∈ K` a primitive
`N`-th root of unity, `τ ∈ maxUnram Bt K` with `τ ^ N = t`.

* `etale_away`, `map_genPt_away`: `Spec Bt → Spec B` is etale and maps generic point to generic point;
* `cyc_mem`: the class of a cyclic character `σ ↦ (c σ).val • g` lies in `res H¹(Spec B) + κ(kumChi τ Λ)`;
* **`purity`**, **`purity_exists`**: every `κ ∈ H¹(Spec Bt, Λ)` is `res κ₀ + κ(kumChi τ c)` with `κ₀ ∈ H¹(Spec B, Λ)`,
  `c ∈ Λ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer RamanujanPetersson.EtPi1
  RamanujanPetersson.EtCompact.GalTrE

section Away

end Away

section Pur

variable {B Bt K : Type} [CommRing B] [IsDedekindDomain B] [CommRing Bt] [IsDedekindDomain Bt] [Algebra B Bt]
  {t : B} [IsLocalization.Away t Bt] (ht : t ≠ 0) (hP : (Ideal.span {t}).IsPrime)
  [Field K] [Algebra B K] [Algebra Bt K] [IsScalarTower B Bt K] [IsFractionRing B K] [IsFractionRing Bt K]
  [Etale (Spec.map (CommRingCat.ofHom (algebraMap B Bt)))]
  {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N] (hN : IsUnit (N : B)) (hΛ : ∀ x : Λ, N • x = 0)
  {ζ0 : K} (hζ0 : IsPrimitiveRoot ζ0 N) {τ : (maxUnram Bt K)ˣ}
  (hτ : (τ : maxUnram Bt K) ^ N = algebraMap K (maxUnram Bt K) (algebraMap B K t))

include ht hP hN in
/-- **Purity for a cyclic character.** -/
theorem cyc_mem {d : ℕ} [NeZero d] (hdN : d ∣ N) (c : Pi1 Bt K → ZMod d) (hc : IsLocallyConstant c)
    (hhom : ∀ a b, c (a * b) = c a + c b) {g : Λ} (hg : d • g = 0) :
    kappaLH Bt K Λ ⟨fun σ => (c σ).val • g, chl_cyc inferInstance hc hhom hg⟩ ∈
      (resLEHom (Λ := Λ) (Spec.map (CommRingCat.ofHom (algebraMap B Bt))) 1).range ⊔
        ((kappaLH Bt K Λ).comp (kumTau (zetaE_prim Bt hζ0) (zetaE_fix Bt ζ0) (mem_rad_of_pow_eq hτ) hΛ)).range := by
  have hq0 : N / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdN)
    (Nat.pos_of_ne_zero (NeZero.ne d))).ne'
  have hz0 : IsPrimitiveRoot (ζ0 ^ (N / d)) d := by
    have h := hζ0.pow_of_dvd hq0 (Nat.div_dvd_of_dvd hdN)
    rwa [Nat.div_div_self hdN (NeZero.ne N)] at h
  have hζd : IsPrimitiveRoot ((algebraMap K (maxUnram Bt K) ζ0) ^ (N / d)) d := by
    rw [← map_pow]
    exact zetaE_prim Bt hz0
  have hζdΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 Bt K)),
      σ ((algebraMap K (maxUnram Bt K) ζ0) ^ (N / d)) = (algebraMap K (maxUnram Bt K) ζ0) ^ (N / d) := by
    rw [← map_pow]
    exact zetaE_fix Bt (ζ0 ^ (N / d))
  obtain ⟨α, m, u, hα, hαu, ⟨γ, hγu⟩, hfor⟩ :=
    cyc_twist ht hP hN hdN (zetaE_prim Bt hζ0) hζd (zetaE_fix Bt ζ0) hτ c hc hhom hg
  have hγ : γ ∈ rad (⊤ : Subgroup (Pi1 B K)) d := mem_rad_of_pow_eq hγu
  have e : (⟨fun σ => (c σ).val • g, chl_cyc inferInstance hc hhom hg⟩ : ChL Bt K Λ) =
      ⟨kumChi hζd α g, mem_ChL.2 ⟨kumChi_mul hζd hζdΓ hα hg, kumChi_isLocallyConstant hζd α g⟩⟩ +
        kumTau (zetaE_prim Bt hζ0) (zetaE_fix Bt ζ0) (mem_rad_of_pow_eq hτ) hΛ ((-m) • g) :=
    Subtype.ext (funext hfor)
  rw [e, map_add]
  refine AddSubgroup.add_mem_sup (AddMonoidHom.mem_range.2 ⟨kappaL B K Λ
    (kumChi_mul (zetaE_prim B hz0) (zetaE_fix B _) hγ hg) (kumChi_isLocallyConstant (zetaE_prim B hz0) γ g), ?_⟩)
    (AddMonoidHom.mem_range.2 ⟨(-m) • g, rfl⟩)
  rw [resLEHom_apply, kappaLH_apply]
  exact resLE_kappaL_kum_field (CommRingCat.ofHom (algebraMap B Bt)) (map_genPt_away t ht) (zetaE_prim B hz0) hζd
    (zetaE_fix B _) hζdΓ (RingHom.id K) (fun a => IsScalarTower.algebraMap_apply B Bt K a) rfl
    (by rw [RingHom.id_apply, map_pow]) hγ hα hg hγu hαu

end Pur

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T4b =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4b): `thetaM_res`, classes with coefficients `clsD`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section Theta

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- **`thetaM` commutes with restriction** along `w : W' ⟶ W`. -/
theorem thetaM_res {W' W T : P.Etale} (w : W' ⟶ W) (m : W ⟶ T) (κ : H Λ (unitSh Λ W.left) 1) :
    thetaM Λ (w ≫ m) 1 (resLE w.left 1 κ) = (Ext.mk₀ (freeMap Λ w)).comp (thetaM Λ m 1 κ) (zero_add 1) := by
  apply (extFree Λ W' (freeSh Λ T) 1).injective
  rw [extFree_natural, extFree_thetaM, extFree_thetaM, resHE_comp_mk₀, resLE_apply,
    Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀,
    secMap_res, ← unitResIso_hom, Iso.inv_hom_id_assoc]
  rfl

end Theta

section ClsD

end ClsD

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T4d =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section Pc

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P)
  [IsOpenImmersion c] {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)
  {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) (hΛ : ∀ x : Λ, N • x = 0)
  {Uz : P.Opens} (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact)

set_option backward.isDefEq.respectTransparency false in
theorem clsD_sec_ta {T : P.Etale} (s : chEt c φ ⟶ T) (κ0 : H Λ (unitSh Λ (chEt c φ).left) 1) :
    (hS.extClass.comp (Ext.mk₀ (freeMap Λ (isoT c φ hUz).inv)) (add_zero 1)).comp
      (thetaM Λ (toD1 c φ a ≫ s) 1 (resLE (toD1 c φ a).left 1 κ0)) (show 1 + 1 = 2 from rfl) = 0 := by
  rw [thetaM_res, locT_res_D c φ hUz (le_refl Uz) hS]

end Pc

end RamanujanPetersson.EtPBC.EtMV

end

end


