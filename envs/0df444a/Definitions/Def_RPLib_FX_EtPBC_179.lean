-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_179
-- name    : RPLib_FX_EtPBC_179
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:36:16.322282+00:00
-- url     : https://prove2.me/theorems/2f60600a-6f31-5392-beb5-2023b424055d
-- title:
--   Proper base change for the projective line, library file 179
-- statement:
--   File 179 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_StkBCc`: S4-EtPBC-A, L1f part 3c: `stalkBC` is injective from `BCInj`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_169

/-!
# Proper base change for the projective line, library file 179

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_StkBCc`: S4-EtPBC-A, L1f part 3c: `stalkBC` is injective from `BCInj`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_StkBCc =====
section

/-!
# S4-EtPBC-A, L1f part 3c: `stalkBC` is injective from `BCInj`
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

theorem stalkBC_injective (he : GermNat Λ g F n Q e) (hI : BCInj Λ g s n F) :
    Function.Injective (stalkBCHom s he) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨X, x', z, rfl⟩ := s.point.toPresheafFiber_jointly_surjective x
  have hx' : Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s)
      (s.point.fiber.elementsMk X x') F n (e X z) = 0 := (stalkBC_germ s he X x' z).symm.trans hx
  obtain ⟨j', a, ha⟩ := hI _ _ hx'
  have h1 : Q.map a.1.op z = 0 :=
    (e j'.1).injective (((he a.1 z).trans ha).trans (map_zero (e j'.1)).symm)
  have h3 : s.point.toPresheafFiber X x' Q z = s.point.toPresheafFiber j'.1 j'.2 Q (Q.map a.1.op z) :=
    (congrArg (fun y => s.point.toPresheafFiber X y Q z) a.2.symm).trans
      (GrothendieckTopology.Point.toPresheafFiber_w_apply s.point a.1 j'.2 Q z).symm
  rw [h3, h1, map_zero]

end RamanujanPetersson.EtPBC

end

end


