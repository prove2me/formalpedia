-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_192
-- name    : RPLib_FX_EtPBC_192
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:48:29.627717+00:00
-- url     : https://prove2.me/theorems/a58fd37f-89c6-5392-b529-f4f2b33f02e4
-- title:
--   Proper base change for the projective line, library file 192
-- statement:
--   File 192 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_SecExt`: S4-EtPBC-A, L1c (part 3): cohomology of sections of an injective resolution is `Ext` from a free sheaf
--   * `S4.Def_RP_EtPBC_A_SecNat`: S4-EtPBC-A, L1c': naturality of `secExt` in the etale object
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_185

/-!
# Proper base change for the projective line, library file 192

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_SecExt`: S4-EtPBC-A, L1c (part 3): cohomology of sections of an injective resolution is `Ext` from a free sheaf
* `S4.Def_RP_EtPBC_A_SecNat`: S4-EtPBC-A, L1c': naturality of `secExt` in the etale object
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_SecExt =====
section

/-!
# S4-EtPBC-A, L1c (part 3): cohomology of sections of an injective resolution is `Ext` from a free sheaf

`secExt Λ I W p : H^(p+1)(I^•(W)) ≃+ Ext^(p+1)(Λ[W], F)` (`Λ[W] = freeSh Λ W`), from Mathlib's cocycle
description of `Ext` (`InjectiveResolution.extMk`) and `freeEquiv : Hom(Λ[W], G) ≃+ G(W)`. The homology is that of
the short complex `sc (p+1)`, which is `(secCx Λ I.cocomplex W).homology (p+1)` by definition.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} {F : EtSh Λ X} (I : InjectiveResolution F)

/-- **`H^(p+1)(I^•(W)) ≃+ Ext^(p+1)(Λ[W], F)`**. -/
def secExt (W : X.Etale) (p : ℕ) : (secSc Λ I W p).homology ≃+ Ext.{u} (freeSh Λ W) F (p + 1) :=
  (secSc Λ I W p).moduleCatHomologyIso.toLinearEquiv.toAddEquiv.trans
    (AddEquiv.ofBijective (quotExt Λ I W p) (quotExt_bijective Λ I W p))

theorem secExt_apply (W : X.Etale) (p : ℕ) (x : (secSc Λ I W p).homology) :
    secExt Λ I W p x = quotExt Λ I W p ((secSc Λ I W p).moduleCatHomologyIso.hom x) := rfl

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_SecNat =====
section

/-!
# S4-EtPBC-A, L1c': naturality of `secExt` in the etale object

`secExt_π`: `secExt` of the class of a cycle `c` is `cocExt c`. `secExt_nat`: for `w : W' ⟶ W` and a morphism of short
complexes `φ : I^•(W)_(p+1) ⟶ I^•(W')_(p+1)` that restricts along `w` in the middle,
`secExt W' (H(φ) x) = Λ[w]^* (secExt W x)`. `germExt`: the presheaf `V ↦ H^(p+1)(I^•(g⁻¹ V))` at `V` is
`Ext^(p+1)(Λ[g⁻¹ V], F)`, naturally in `V` (`germExt_map`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves

universe u

section Sec

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} {F : EtSh Λ X} (I : InjectiveResolution F)

theorem secExt_π (W : X.Etale) (p : ℕ) (c : (secSc Λ I W p).cycles) :
    secExt Λ I W p ((secSc Λ I W p).homologyπ c) = cocExt Λ I W p (cycKer Λ I W p c) := by
  rw [secExt_apply]
  have h := ConcreteCategory.congr_hom (secSc Λ I W p).π_moduleCatCyclesIso_hom c
  simp only [CategoryTheory.comp_apply] at h
  rw [h]
  rfl

/-- **Naturality of `secExt`** in the etale object. -/
theorem secExt_nat {W' W : X.Etale} (w : W' ⟶ W) (p : ℕ) (φ : secSc Λ I W p ⟶ secSc Λ I W' p)
    (hφ : ∀ y : (I.cocomplex.X (p + 1)).val.obj (op W), φ.τ₂ y = (I.cocomplex.X (p + 1)).val.map w.op y)
    (x : (secSc Λ I W p).homology) :
    secExt Λ I W' p (ShortComplex.homologyMap φ x) =
      (Ext.mk₀ (freeMap Λ w)).comp (secExt Λ I W p x) (zero_add _) := by
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (secSc Λ I W p).homologyπ).1 inferInstance x
  have h1 := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality φ) c
  have h2 := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i φ) c
  simp only [CategoryTheory.comp_apply] at h1 h2
  rw [h1, secExt_π, secExt_π, cocExt_apply, cocExt_apply, I.mk₀_comp_extMk]
  refine extMk_congr Λ I ?_ _ _ _
  apply (freeEquiv Λ W' (I.cocomplex.X (p + 1))).injective
  rw [AddEquiv.apply_symm_apply, freeEquiv_freeMap, AddEquiv.apply_symm_apply, cocSec_cycles, cocSec_cycles, h2]
  exact hφ _

end Sec

section Germ

end Germ

end RamanujanPetersson.EtPBC

end

end


