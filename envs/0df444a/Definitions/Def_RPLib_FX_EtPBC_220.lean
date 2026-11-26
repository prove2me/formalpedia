-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_220
-- name    : RPLib_FX_EtPBC_220
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T04:12:47.43739+00:00
-- url     : https://prove2.me/theorems/30c81855-48f2-5b90-99c6-6059f090e681
-- title:
--   Proper base change for the projective line, library file 220
-- statement:
--   File 220 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2L7c`: S4-EtPBC-A, O2 L7c: degree-2 base change for free sheaves `Λ[W]`, `W` affine, on `P¹_S`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_196
import Definitions.Def_RPLib_FX_EtPBC_219

/-!
# Proper base change for the projective line, library file 220

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2L7c`: S4-EtPBC-A, O2 L7c: degree-2 base change for free sheaves `Λ[W]`, `W` affine, on `P¹_S`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2L7c =====
section

/-!
# S4-EtPBC-A, O2 L7c: degree-2 base change for free sheaves `Λ[W]`, `W` affine, on `P¹_S`
**`bcSurj_two_free`**: for `W` affine, `BCSurj 2 Λ[W]` (`Λ` killed by `l ^ m`, `l` invertible in `K`): every class
`TrE x` is a germ (`TrE_surjective`; `gen_free` writes `x` in the span of point classes, `ptCls_bcImg`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

section L7c

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]

/-- **Degree-2 base change for `Λ[W]`, `W` affine.** -/
theorem bcSurj_two_free (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0) (m : ℕ) [NeZero (l ^ m)]
    (hN : ((l ^ m : ℕ) : K) ≠ 0) (hΛ : ∀ x : Λ, (l ^ m) • x = 0) (W : (PV K gS).Etale) [IsAffine W.left] :
    BCSurj Λ (qV K gS) s 2 (freeSh Λ W) := by
  have hA : IsAffine ((etPull (ιP gS s)).obj W).left := isAffine_ιPW gS s W
  have hTa : IsAffineHom ((etPull (ιP gS s)).obj W).hom :=
    @isAffineHom_of_isAffine_source ((etPull (ιP gS s)).obj W).left (P1 K) hA _ ((etPull (ιP gS s)).obj W).hom
  have : IsSeparated ((etPull (ιP gS s)).obj W).hom := IsSeparated.of_isAffineHom _
  have key : genT Λ hN hΛ ((etPull (ιP gS s)).obj W) ≤
      (Delta.bcImg (pull (fibι (qV K gS) s) Λ) (nbhdSys Λ (qV K gS) s) (unitSh Λ (fib (qV K gS) s))
        (bcUnit Λ (qV K gS) s) (bcUnit_comp Λ (qV K gS) s) (freeSh Λ W) 2).comap (TrEh gS s Λ W) :=
    (AddSubgroup.closure_le _).2 fun x ⟨c, _, hx⟩ => ptCls_bcImg gS s Λ hN hΛ W c x hx
  intro β
  obtain ⟨x, rfl⟩ := TrE_surjective gS s Λ W β
  exact key (gen_free K l hl m hN hΛ _ hTa (fun z => finite_fiber _ z) x)

end L7c

end RamanujanPetersson.EtPBC.EtMV

end

end


