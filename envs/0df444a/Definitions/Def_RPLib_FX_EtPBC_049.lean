-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_049
-- name    : RPLib_FX_EtPBC_049
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:27:10.49124+00:00
-- url     : https://prove2.me/theorems/90072f9f-7188-5b42-bd6b-0e50a958deef
-- title:
--   Proper base change for the projective line, library file 049
-- statement:
--   File 049 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2N1c`: S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_038
import Definitions.Def_RPLib_FX_EtPBC_039

/-!
# Proper base change for the projective line, library file 049

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2N1c`: S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2N1c =====
section

/-!
# S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)

* `trIso g h Λ F : (g^* F)_ȳ ≅ F_x̄` and `galTrX g h : Gal y → Gal x` for `h : g y = x` (`resTrIsoE`, `galTrE`
  transported along `h`), `galRep_trIso`, `trIso_natural`, `trIso_hom_injective`, `trIso_inv_natural`,
  `trIso_unitRes`, `isoHomInv`, `isoInvHom`;
* **`resHE_kappa`** (NAT): for `g : Spec A' ⟶ Spec A` etale between noetherian integrally closed domains with
  `g η' = η`, `resHE g (κ_A c) = κ_{A'} c'` whenever `trIso (c' (σ|)) = c ((galTrX σ)|)` for all `σ ∈ Gal(η')`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec

universe u

section Pt

end Pt

section Kappa

variable {A K A' K' : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] [IsNoetherianRing A]
  [CommRing A'] [IsDomain A'] [Field K'] [Algebra A' K'] [IsFractionRing A' K'] [IsIntegrallyClosed A']
  [IsNoetherianRing A'] {Λ : Type} [CommRing Λ]
  (g : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A)) [Etale g] (hg : g (genPt A') = genPt A)

/-- **NAT: restriction of `κ`-classes along an etale map.** -/
theorem resHE_kappa {G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)
    {c : Pi1 A K → stalk Λ G (genPt A)} (hc : IsCocycle (EssSurj.fibRep A K G hG) c) (hcl : IsLocallyConstant c)
    (hG' : IsLisse Λ ((res g Λ).obj G)) {c' : Pi1 A' K' → stalk Λ ((res g Λ).obj G) (genPt A')}
    (hc' : IsCocycle (EssSurj.fibRep A' K' _ hG') c') (hcl' : IsLocallyConstant c')
    (hrel : ∀ σ : Gal (genPt A'), (trIso g hg Λ G).hom.hom (c' (genToPi1 A' K' σ)) =
      c (genToPi1 A K (galTrX g hg σ))) :
    resHE g G 1 (kappa A K hG c hc hcl) = kappa A' K' hG' c' hc' hcl' := by
  let R := Classical.choice (nonempty_realExt A K hG hc hcl)
  change resHE g G 1 R.se.extClass = _
  rw [resHE_extClass]
  refine kappa_eq A' K' hG' hc' hcl' (resSE g R.se) (w := (trIso g hg Λ R.P).inv.hom R.w) ⟨?_, fun σ => ?_⟩
  · rw [gs_comp_apply, trIso_inv_natural, R.real.one, ← trIso_unitRes g hg Λ, isoHomInv,
      ← gs_comp_apply, ← unitResIso_hom, Iso.hom_inv_id, gs_id_apply]
  · apply trIso_hom_injective g hg Λ R.P
    rw [map_sub, galRep_trIso, isoInvHom, R.real.coc, trIso_natural, hrel]

end Kappa

end RamanujanPetersson.EtCompact.GalTrE

end

end


