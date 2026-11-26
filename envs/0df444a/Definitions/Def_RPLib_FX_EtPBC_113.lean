-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_113
-- name    : RPLib_FX_EtPBC_113
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:06:46.024413+00:00
-- url     : https://prove2.me/theorems/0b0ff7a2-89e4-42f2-b614-cf10024285e0
-- title:
--   Proper base change for the projective line, library file 113
-- statement:
--   File 113 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2L8b`: S4-EtPBC-A, O2 L8b: `TrG` is onto and natural; `BCSurj 2` for `FGT` sheaves; killing degree-1 classes
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_104

/-!
# Proper base change for the projective line, library file 113

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2L8b`: S4-EtPBC-A, O2 L8b: `TrG` is onto and natural; `BCSurj 2` for `FGT` sheaves; killing degree-1 classes
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2L8b =====
section

/-!
# S4-EtPBC-A, O2 L8b: `TrG` is onto and natural; `BCSurj 2` for `FGT` sheaves; killing degree-1 classes
* `TrG_surjective`, **`TrG_natural`** (`TrG G (x ∘ ιP^*m) = TrG H x ∘ ι^*m`);
* **`bcSurj_two_fgt`**: `BCSurj 2` for every `FGT` sheaf on `P¹_S` (`surjAt_coprod`, `bcSurj_two_free`, `bcSurj_two_of_epi`);
* `NT`, **`kill_lift`**: for `T` affine over `P¹_K`, every `κ ∈ Ext¹(Λ[T], ιP^*G)` is `κH ∘ ιP^*m` with `m : H ⟶ G`,
  `H` an `FGT` sheaf (`exists_kill` on `T`, `extFree_comp_mk₀`, the covariant exact sequence).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE
  RamanujanPetersson.EtCompact.PushBC

universe u

section GenSurjG

universe w v₁ u₁ v₂ u₂

end GenSurjG

section TrG

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]

/-- **Killing a degree-1 class**: for `T` affine over `P¹_K`, every `κ ∈ Ext¹(Λ[T], ιP^*G)` comes from an `FGT`
subsheaf of `G`. -/
theorem kill_lift (T : (P1 K).Etale) [IsAffine T.left] (G : EtSh Λ (PV K gS))
    (κ : Ext.{0} (freeSh Λ T) ((pull (ιP gS s) Λ).obj G) 1) :
    ∃ (H : EtSh Λ (PV K gS)) (_ : FGT Λ H) (m : H ⟶ G)
      (κH : Ext.{0} (freeSh Λ T) ((pull (ιP gS s) Λ).obj H) 1),
      κH.comp (Ext.mk₀ ((pull (ιP gS s) Λ).map m)) (add_zero 1) = κ := by
  let ιT : T.left ⟶ PV K gS := T.hom ≫ ιP gS s
  have hA : ∀ {Z : Scheme.{0}} (h : Z ⟶ T.left), IsAffine Z → IsAffineHom h := fun h hZ => by
    have := hZ
    exact isAffineHom_of_isAffine h
  obtain ⟨t, ht, W, hW, φ, hφ⟩ := EtPBC.exists_kill ιT hA G
    ((extFree Λ T _ 1 κ).comp (Ext.mk₀ ((NT gS s Λ T).hom.app G)) (add_zero 1))
  let SK := ShortComplex.mk (kernel.ι (cokernel.π φ)) (cokernel.π φ) (kernel.condition _)
  have hSK : SK.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
      mono_f := mono_kerι _
      epi_g := epi_cokπ φ }
  have hn : (res T.hom Λ).map ((pull (ιP gS s) Λ).map (cokernel.π φ)) ≫ (NT gS s Λ T).hom.app (cokernel φ) =
      (NT gS s Λ T).hom.app G ≫ (pull ιT Λ).map (cokernel.π φ) := (NT gS s Λ T).hom.naturality (cokernel.π φ)
  have hmor : (NT gS s Λ T).hom.app G ≫ (pull ιT Λ).map (cokernel.π φ) ≫ (NT gS s Λ T).inv.app (cokernel φ) =
      (res T.hom Λ).map ((pull (ιP gS s) Λ).map (cokernel.π φ)) := by
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  have h0 : κ.comp (Ext.mk₀ ((pull (ιP gS s) Λ).map (cokernel.π φ))) (add_zero 1) = 0 := by
    apply (extFree Λ T _ 1).injective
    rw [map_zero, extFree_comp_mk₀, ← hmor, ← Ext.mk₀_comp_mk₀, ← Ext.mk₀_comp_mk₀,
      ← Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ ((NT gS s Λ T).hom.app G)),
      ← Ext.comp_assoc_of_third_deg_zero (extFree Λ T _ 1 κ),
      ← Ext.comp_assoc_of_third_deg_zero (extFree Λ T _ 1 κ), hφ, Ext.zero_comp]
  obtain ⟨κH, hκH⟩ := Ext.covariant_sequence_exact₂ (X := freeSh Λ T)
    (hS := hSK.map_of_exact (pull (ιP gS s) Λ)) κ h0
  exact ⟨kernel (cokernel.π φ), ⟨t, ht, W, hW, Abelian.factorThruImage φ, epi_fti φ⟩, kernel.ι _, κH, hκH⟩

end TrG

end RamanujanPetersson.EtPBC.EtMV

end

end


