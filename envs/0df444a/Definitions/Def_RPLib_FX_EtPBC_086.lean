-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_086
-- name    : RPLib_FX_EtPBC_086
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:39:47.594908+00:00
-- url     : https://prove2.me/theorems/9ea66001-5c65-5636-9245-cbf33aa50c03
-- title:
--   Proper base change for the projective line, library file 086
-- statement:
--   File 086 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Coh`: S4-EtPBC-A, O2 M6 (O2Coh): restriction to an etale `W` as `Λ[W ⟶ X]^*`, and restriction to pieces
--   * `S4.Def_RP_EtPBC_A_O2KapF`: S4-EtPBC-A, O2 M6 (O2KapF): functoriality of `resLE` and the field-level Kummer kill
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_075
import Definitions.Def_RPLib_FX_EtPBC_076

/-!
# Proper base change for the projective line, library file 086

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Coh`: S4-EtPBC-A, O2 M6 (O2Coh): restriction to an etale `W` as `Λ[W ⟶ X]^*`, and restriction to pieces
* `S4.Def_RP_EtPBC_A_O2KapF`: S4-EtPBC-A, O2 M6 (O2KapF): functoriality of `resLE` and the field-level Kummer kill
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2Coh =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Coh): restriction to an etale `W` as `Λ[W ⟶ X]^*`, and restriction to pieces

* **`unitRes_eq_adj W`**: `Λ_W ⟶ W^* Λ_X` (`1 ↦ 1`) is the adjunction unit followed by
  `W^*(Λ[W] ⟶ Λ[X] ≅ Λ_X)`;
* **`resLE_eq_extFreeU W c`**: `resLE W.hom 1 c = extFreeU W 1 (Λ[W ⟶ X]^* c)`;
* `extFreeU_splitIn`, **`h1_eq_zero_of_pieces`** (a class vanishing on every piece of a clopen decomposition is `0`),
  `splitIn_splitPr`, `resLE_splitPr(_self/_ne)`, **`resLE_kapS_self`**, **`resLE_kapS_ne`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtCompact.GalTrE

universe u

section Coh

end Coh

section Pieces

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} {ι : Type u} (S : ι → X.Etale) [IsIso (cop S).hom]
  [Fintype ι] [DecidableEq ι]

variable (Λ) in
theorem resLE_splitPr (k z : ι) (y : Ext.{u} (freeSh Λ (S z)) (unitSh Λ X) 1) :
    resLE (S k).hom 1 ((Ext.mk₀ (splitPr S Λ z)).comp y (zero_add 1)) =
      extFreeU Λ (S k) 1 ((Ext.mk₀ (freeMap Λ (copι S k) ≫ copPr Λ S z)).comp y (zero_add 1)) := by
  rw [← extFreeU_splitIn, Ext.mk₀_comp_mk₀_assoc, splitIn_splitPr]

end Pieces

end RamanujanPetersson.EtPBC.EtKum

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

end ResComp

section KapF

variable {A K A' K' : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing A'] [IsDomain A'] [Field K'] [Algebra A' K'] [IsFractionRing A' K']
  [IsIntegrallyClosed A] [IsNoetherianRing A] [IsIntegrallyClosed A'] [IsNoetherianRing A']
  (φ : CommRingCat.of A ⟶ CommRingCat.of A') [Etale (Spec.map φ)]
  (h : Spec.map φ (GenBr.genPt A') = GenBr.genPt A)
  {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N] {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 A K)), σ ζ = ζ) {d : ℕ} [NeZero d] (hdN : d ∣ N)
  {α : (maxUnram A K)ˣ} (hα : α ∈ rad (⊤ : Subgroup (Pi1 A K)) d) {g : Λ} (hg : d • g = 0)

include h in
/-- **A Kummer class dies where its radicand becomes a `d`-th power.** -/
theorem resLE_kumD_eq_zero (ψ : K →+* K')
    (hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (φ.hom a)) {z₀ u : K}
    (hz : ζ = algebraMap K (maxUnram A K) z₀)
    (hu : (α : maxUnram A K) ^ d = algebraMap K (maxUnram A K) u) {v : K'} (hv : v ^ d = ψ u) :
    resLE (Spec.map φ) 1 (kappaLH A K Λ (kumD hζ hζΓ hdN hα hg)) = 0 := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu
    exact pow_ne_zero d α.ne_zero hu
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne d)] at hv
    exact hu0 ((map_eq_zero ψ).1 hv.symm)
  obtain ⟨ζ', hζ'def⟩ : ∃ ζ' : maxUnram A' K', ζ' = algebraMap K' (maxUnram A' K') (ψ (z₀ ^ (N / d))) :=
    ⟨_, rfl⟩
  have hz1 : IsPrimitiveRoot (z₀ ^ (N / d)) d := by
    have h5 := primd hζ hdN
    rw [hz, ← map_pow] at h5
    exact h5.of_map_of_injective (algebraMap K (maxUnram A K)).injective
  have hζ' : IsPrimitiveRoot ζ' d := by
    rw [hζ'def]
    exact (hz1.map_of_injective ψ.injective).map_of_injective (algebraMap K' (maxUnram A' K')).injective
  have hζΓ' : ∀ σ ∈ (⊤ : Subgroup (Pi1 A' K')), σ ζ' = ζ' := fun σ _ => by
    rw [hζ'def]
    exact AlgEquiv.commutes σ _
  obtain ⟨γ', hγ'def⟩ : ∃ γ' : (maxUnram A' K')ˣ, (γ' : maxUnram A' K') = algebraMap K' (maxUnram A' K') v :=
    ⟨Units.mk0 _ ((map_ne_zero (algebraMap K' (maxUnram A' K'))).2 hv0), rfl⟩
  have hu' : (γ' : maxUnram A' K') ^ d = algebraMap K' (maxUnram A' K') (ψ u) := by
    rw [hγ'def, ← map_pow, hv]
  have hγ' : γ' ∈ rad (⊤ : Subgroup (Pi1 A' K')) d := mem_rad_of_pow_eq hu'
  have hfix : γ' ∈ fixUnits (⊤ : Subgroup (Pi1 A' K')) := (mem_fixUnits _ γ').2 fun σ _ => by
    rw [hγ'def]
    exact AlgEquiv.commutes σ v
  have e := resLE_kappaL_kum_field φ h (primd hζ hdN) hζ' (fix_pow hζΓ) hζΓ' ψ hψ (z := z₀ ^ (N / d)) (u := u)
    (by rw [hz, map_pow]) (by rw [hζ'def]) hα hγ' hg hu hu'
  have h0 : (⟨kumChi hζ' γ' g, mem_ChL.2 ⟨kumChi_mul hζ' hζΓ' hγ' hg, kumChi_isLocallyConstant hζ' γ' g⟩⟩ :
      ChL A' K' Λ) = 0 := by
    apply Subtype.ext
    funext σ
    show kumChi hζ' γ' g σ = 0
    unfold kumChi
    rw [kchar_of_fix hζ' hfix, ZMod.val_zero, zero_smul]
  calc resLE (Spec.map φ) 1 (kappaLH A K Λ (kumD hζ hζΓ hdN hα hg))
      = kappaLH A' K' Λ
          ⟨kumChi hζ' γ' g, mem_ChL.2 ⟨kumChi_mul hζ' hζΓ' hγ' hg, kumChi_isLocallyConstant hζ' γ' g⟩⟩ := e
    _ = 0 := by rw [h0, map_zero]

end KapF

end RamanujanPetersson.EtPBC.EtKum

end

end


