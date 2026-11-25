-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_059
-- name    : RPLib_FX_EtPBC_059
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:29:45.016326+00:00
-- url     : https://prove2.me/theorems/0a7028ee-e2a4-5413-865d-b2808f6d7f0b
-- title:
--   Proper base change for the projective line, library file 059
-- statement:
--   File 059 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2N2`: S4-EtPBC-A, O2 M5 N2: constant coefficients (`κ` of characters and their restriction)
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_040
import Definitions.Def_RPLib_FX_EtPBC_049

/-!
# Proper base change for the projective line, library file 059

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2N2`: S4-EtPBC-A, O2 M5 N2: constant coefficients (`κ` of characters and their restriction)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2N2 =====
section

/-!
# S4-EtPBC-A, O2 M5 N2: constant coefficients (`κ` of characters and their restriction)

* `unitCoc χ : τ ↦ χ τ • 1` (a cocycle for the trivial action on `(Λ_X)_η̄` when `χ` is additive),
  `fibRep_unitSh'`, `unitCoc_isCocycle`, `unitCoc_isLocallyConstant`;
* `kappaL A K Λ hχ hl : H¹(Spec A, Λ)`, the class of an additive locally constant `χ : π₁(A) → Λ`;
* `resLE g n : H^n(X, Λ) → H^n(U, Λ)` for an etale `g : U ⟶ X` (`resHE` and `unitResIso`);
* **`resLE_kappaL`** (NAT for constant coefficients): for `g : Spec A' ⟶ Spec A` etale with `g η' = η`,
  `resLE g 1 (κ χ) = κ χ'` whenever `χ' (σ|) = χ ((galTrX σ)|)` for all `σ ∈ Gal(η')`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec

section Unit

end Unit

section ResL

universe u

end ResL

section NatL

variable {A K A' K' : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] [IsNoetherianRing A]
  [CommRing A'] [IsDomain A'] [Field K'] [Algebra A' K'] [IsFractionRing A' K'] [IsIntegrallyClosed A']
  [IsNoetherianRing A'] {Λ : Type} [CommRing Λ]
  (g : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A)) [Etale g] (hg : g (genPt A') = genPt A)

/-- **NAT for constant coefficients**: `resLE g 1 (κ χ) = κ χ'` when `χ'` is `χ` transported by `galTrX`. -/
theorem resLE_kappaL {χ : Pi1 A K → Λ} (hχ : ∀ a b, χ (a * b) = χ a + χ b) (hl : IsLocallyConstant χ)
    {χ' : Pi1 A' K' → Λ} (hχ' : ∀ a b, χ' (a * b) = χ' a + χ' b) (hl' : IsLocallyConstant χ')
    (hrel : ∀ σ : Gal (genPt A'), χ' (genToPi1 A' K' σ) = χ (genToPi1 A K (galTrX g hg σ))) :
    resLE g 1 (kappaL A K Λ hχ hl) = kappaL A' K' Λ hχ' hl' := by
  have hG' : IsLisse Λ ((res g Λ).obj (unitSh Λ (Spec (CommRingCat.of A)))) := PushBC.isLisse_res g isLisse_unitSh
  set v : stalk Λ ((res g Λ).obj (unitSh Λ (Spec (CommRingCat.of A)))) (genPt A') :=
    gs A' (unitRes g Λ) (oneStalk Λ (genPt A')) with hv
  have hc' : IsCocycle (EssSurj.fibRep A' K' _ hG') (fun τ => χ' τ • v) := by
    intro a b
    show χ' (a * b) • v = χ' a • v + EssSurj.fibRep A' K' _ hG' a (χ' b • v)
    rw [map_smul, hv, fibRep_unitRes g, hχ', add_smul]
  have hcl' : IsLocallyConstant (fun τ => χ' τ • v) := hl'.comp (fun a : Λ => a • v)
  have h1 := resHE_kappa g hg (G := unitSh Λ (Spec (CommRingCat.of A))) isLisse_unitSh
    (unitCoc_isCocycle A K Λ hχ) (unitCoc_isLocallyConstant A K Λ hl) hG' hc' hcl' (fun σ => by
      show (trIso g hg Λ _).hom.hom (χ' (genToPi1 A' K' σ) • v) =
        χ (genToPi1 A K (galTrX g hg σ)) • oneStalk Λ (genPt A)
      rw [map_smul, hrel σ, hv, trIso_unitRes g hg Λ])
  have h2 := kappa_comp A' K' hG' isLisse_unitSh hc' hcl' (unitCoc_isCocycle A' K' Λ hχ')
    (unitCoc_isLocallyConstant A' K' Λ hl') (unitResIso g Λ).inv (fun τ => by
      show gs A' (unitResIso g Λ).inv (χ' τ • v) = χ' τ • oneStalk Λ (genPt A')
      rw [map_smul, hv, ← gs_comp_apply, ← unitResIso_hom, Iso.hom_inv_id, gs_id_apply])
  exact (congrArg (fun e => e.comp (Ext.mk₀ (unitResIso g Λ).inv) (add_zero 1)) h1).trans h2

end NatL

end RamanujanPetersson.EtCompact.GalTrE

end

end


