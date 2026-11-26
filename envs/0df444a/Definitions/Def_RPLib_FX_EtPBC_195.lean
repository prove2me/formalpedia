-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_195
-- name    : RPLib_FX_EtPBC_195
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:51:40.15196+00:00
-- url     : https://prove2.me/theorems/55e344f5-f69c-5551-a713-d446b180b7df
-- title:
--   Proper base change for the projective line, library file 195
-- statement:
--   File 195 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_StkBCd0`: S4-EtPBC-A, L1f part 4a: `stalkBC` is bijective; the bare equivalence `stalkEquivE`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_189

/-!
# Proper base change for the projective line, library file 195

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_StkBCd0`: S4-EtPBC-A, L1f part 4a: `stalkBC` is bijective; the bare equivalence `stalkEquivE`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_StkBCd0 =====
section

/-!
# S4-EtPBC-A, L1f part 4a: `stalkBC` is bijective; the bare equivalence `stalkEquivE`

(Split from `StkBCd` for the file time limit: each declaration mentioning these types costs 10-30 s of kernel time.)
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

/-- The stalk base change map as an equivalence of types. -/
def stalkEquivE (he : GermNat Λ g F n Q e) (hI : BCInj Λ g s n F) (hS : BCSurj Λ g s n F) :
    ToType (s.point.presheafFiber.obj Q) ≃ H Λ ((pull (fibι g s) Λ).obj F) n :=
  Equiv.ofBijective (stalkBC s he) (stalkBC_bijective s he hI hS)

end RamanujanPetersson.EtPBC

end

end


