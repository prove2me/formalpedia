-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_193
-- name    : RPLib_FX_EtPBC_193
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T01:01:20.221457+00:00
-- url     : https://prove2.me/theorems/06b1a052-22f4-56b8-9ec2-1b13b20c3e1d
-- title:
--   Proper base change for the projective line, library file 193
-- statement:
--   File 193 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_Inj0e`: S4-EtPBC-A, G1d part 2: the shrunken neighbourhood `goodNbhd` and `goodHom` (`res0_eq_zero` is in `Inj0d1`)
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_189

/-!
# Proper base change for the projective line, library file 193

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_Inj0e`: S4-EtPBC-A, G1d part 2: the shrunken neighbourhood `goodNbhd` and `goodHom` (`res0_eq_zero` is in `Inj0d1`)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_Inj0e =====
section

/-!
# S4-EtPBC-A, G1d part 2: the shrunken neighbourhood `goodNbhd` and `goodHom` (`res0_eq_zero` is in `Inj0d1`)
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- The arrow `(V', v') ⟶ (V, v)`. -/
def goodHom [UniversallyClosed g] (j : Nbhd s) (G : EtSh Λ P) (α : Ext.{u} ((nbhdSys Λ g s).obj j) G 0)
    (h : Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j G 0 α = 0) :
    goodNbhd Λ g s j G α h ⟶ j :=
  ⟨opnι j.1 (good Λ g s j G α), fiber_ext s ((liftOf_map_left' s (opnι j.1 (good Λ g s j G α))
    (goodNbhd Λ g s j G α h).2).trans ((congrArg (fun φ => φ ≫ (opnι j.1 (good Λ g s j G α)).left)
    ((liftOf_elementsMk_left' s (opn j.1 (good Λ g s j G α)) (Over.homMk (goodPt Λ g s j G α h) (goodPt_w Λ g s j G α h) :
      CategoryTheory.Over.mk s.pt ⟶ (Scheme.Etale.forget S).obj (opn j.1 (good Λ g s j G α)))).trans
      (Over.homMk_left _ _))).trans ((congrArg (fun φ => goodPt Λ g s j G α h ≫ φ)
      (opnι_left' j.1 (good Λ g s j G α))).trans (goodPt_fac Λ g s j G α h))))⟩

end RamanujanPetersson.EtPBC

end

end


