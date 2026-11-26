-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_169
-- name    : RPLib_FX_EtPBC_169
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:58:37.551692+00:00
-- url     : https://prove2.me/theorems/945dc79f-cfb8-539f-9e43-d3822da98fe2
-- title:
--   Proper base change for the projective line, library file 169
-- statement:
--   File 169 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_StkBCc0`: S4-EtPBC-A, L1f part 3a: `stalkBC` is additive (`stalkBCHom`)
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_162

/-!
# Proper base change for the projective line, library file 169

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_StkBCc0`: S4-EtPBC-A, L1f part 3a: `stalkBC` is additive (`stalkBCHom`)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_StkBCc0 =====
section

/-!
# S4-EtPBC-A, L1f part 3a: `stalkBC` is additive (`stalkBCHom`)
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

variable (F : EtSh Λ P) (n : ℕ) (Q : (S.Etale)ᵒᵖ ⥤ ModuleCat.{u} Λ)
  (e : ∀ V : S.Etale, Q.obj (op V) ≃+ Ext.{u} (freeSh Λ ((etPull g).obj V)) F n)

variable {Λ g s F n Q e}

variable (s)

/-- `stalkBC` as an additive map. -/
def stalkBCHom (he : GermNat Λ g F n Q e) :
    ToType (s.point.presheafFiber.obj Q) →+ Ext.{u} (unitSh Λ (fib g s)) ((pull (fibι g s) Λ).obj F) n :=
  AddMonoidHom.mk' (stalkBC s he) (stalkBC_add s he)

end RamanujanPetersson.EtPBC

end

end


