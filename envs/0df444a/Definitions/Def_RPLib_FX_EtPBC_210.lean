-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_210
-- name    : RPLib_FX_EtPBC_210
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T01:33:27.632829+00:00
-- url     : https://prove2.me/theorems/acc2138d-d318-5668-a856-9895249fa825
-- title:
--   Proper base change for the projective line, library file 210
-- statement:
--   File 210 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_PBCStk`: S4-EtPBC-A, L1g: proper base change on stalks from the germ conditions
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_199
import Definitions.Def_RPLib_FX_EtPBC_205

/-!
# Proper base change for the projective line, library file 210

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_PBCStk`: S4-EtPBC-A, L1g: proper base change on stalks from the germ conditions
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_PBCStk =====
section

/-!
# S4-EtPBC-A, L1g: proper base change on stalks from the germ conditions

For `g : P ⟶ S` and a geometric point `s` of `S` (fibre `ι : P_s ⟶ P`):
* `pbcEquivSucc`: `(R^(p+1) g_* F)_s ≃+ H^(p+1)(P_s, ι^* F)` (from `stalkRDIso`, `germExt`, `stalkEquiv`);
* `pbcEquivZero`: `(R^0 g_* F)_s ≃+ H^0(P_s, ι^* F)` (from `rightDerivedZeroIsoSelf`, `freeEquiv`, `Ext.addEquiv₀`);
both given that base change is injective and surjective on germs in that degree for `F`.
**`pbc_of_germs`**: if base change is injective on germs in degree `0` and surjective on germs in every degree, for all
sheaves, then `(R^q g_* F)_s ≃+ H^q(P_s, ι^* F)` for all `q` and `F` (δ-lemma `Delta.injAt_all`).
(`pbcEquivZero` and `pbc_of_germs` are in `PBCStkb`, split off for the file time limit.)
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **Degree `p + 1`.** -/
def pbcEquivSucc {F : EtSh Λ P} (I : InjectiveResolution F) (p : ℕ) (hI : BCInj Λ g s (p + 1) F)
    (hS : BCSurj Λ g s (p + 1) F) :
    ToType ((s.stalkF Λ).obj (((push g Λ).rightDerived (p + 1)).obj F)) ≃+
      H Λ ((pull (fibι g s) Λ).obj F) (p + 1) :=
  (stalkRDIso Λ g s I (p + 1)).toLinearEquiv.toAddEquiv.trans
    (stalkEquiv s (Q := (preCx Λ g I.cocomplex).homology (p + 1)) (germExt_map Λ g I p) hI hS)

end RamanujanPetersson.EtPBC

end

end


