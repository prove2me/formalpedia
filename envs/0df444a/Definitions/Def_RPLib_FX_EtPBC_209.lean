-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_209
-- name    : RPLib_FX_EtPBC_209
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T03:38:37.302508+00:00
-- url     : https://prove2.me/theorems/d626c9bc-1958-548e-8a46-d62e71ca302a
-- title:
--   Proper base change for the projective line, library file 209
-- statement:
--   File 209 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2T9b`: S4-EtPBC-A, O2 S6a (O2T9b): the residual of a one-point class is a one-point class with EMPTY fibre
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_186
import Definitions.Def_RPLib_FX_EtPBC_203

/-!
# Proper base change for the projective line, library file 209

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2T9b`: S4-EtPBC-A, O2 S6a (O2T9b): the residual of a one-point class is a one-point class with EMPTY fibre
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2T9b =====
section

/-!
# S4-EtPBC-A, O2 S6a (O2T9b): the residual of a one-point class is a one-point class with EMPTY fibre

* `PtCls Λ c hN hΛ T x`: `x = pcD c' ∘ Λ[s]` for an affine Dedekind presentation `Spec B` of a point `c (X = a)`;
* **`isLoc_free_res`**: a one-point class `β` at `z = c (X = a)` with coefficients `Λ[T]` (`T` separated, finite fibre)
  is `β' ∘ Λ[r]` modulo point classes, `r : R ⟶ T`, `β'` a one-point class at `z` for `Λ[R]` and `R` with EMPTY fibre
  over `z`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk RamanujanPetersson.EtPBC.EtDed

section PtCls

end PtCls

section Emp

end Emp

section Res

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P)
  [IsOpenImmersion c] (a : k) {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) (hΛ : ∀ x : Λ, N • x = 0)

set_option backward.isDefEq.respectTransparency false in
include hN hΛ in
/-- **The residual is a one-point class with empty fibre**, pushed along `Λ[r]`. -/
theorem isLoc_free_res {T : P.Etale} [IsSeparated T.hom]
    [Finite ((geomPtAt (c (A1pt k a))).point.fiber.obj T)] (hG : Subsingleton (Gal (c (A1pt k a))))
    {β : Ext.{0} (freeSh Λ (etId P)) (freeSh Λ T) 2} (hβ : IsLoc Λ (freeSh Λ T) (c (A1pt k a)) β) :
    ∃ (R : P.Etale) (r : R ⟶ T) (β' : Ext.{0} (freeSh Λ (etId P)) (freeSh Λ R) 2),
      IsLoc Λ (freeSh Λ R) (c (A1pt k a)) β' ∧ IsEmpty ((geomPtAt (c (A1pt k a))).point.fiber.obj R) ∧
      (IsAffineHom T.hom → IsAffine R.left) ∧
      β - β'.comp (Ext.mk₀ (freeMap Λ r)) (add_zero 2) ∈
        AddSubgroup.closure {x | PtCls Λ c hN hΛ T x} := by
  obtain ⟨B, φ, hφE, Uz, hUz, hS, R, g, YR, hφ, hded, ht, hP, hz, hD, hDn, -, -, hRa, hres, hmem⟩ :=
    isLoc_free_decomp c a hN hΛ hG hβ
  obtain ⟨r, hr⟩ : ∃ r : (etComp (chEt c φ).hom).obj R ⟶ T,
      (etCompAdj (chEt c φ).hom).homEquiv R T r = g := ⟨_, Equiv.apply_symm_apply _ _⟩
  have hg : g = (etCompAdj (chEt c φ).hom).unit.app R ≫ (etPull (chEt c φ).hom).map r := by
    rw [← hr, Adjunction.homEquiv_unit]
  have hE := isEmpty_fib_etComp (chEt c φ).hom R (c (A1pt k a)) hres
  refine ⟨(etComp (chEt c φ).hom).obj R, r, clsD c φ a hUz hS (freeMap Λ ((etCompAdj (chEt c φ).hom).unit.app R) ≫
      (resFreeIso Λ (chEt c φ).hom ((etComp (chEt c φ).hom).obj R)).hom) YR,
    clsD_isLoc c φ a hUz hS hz hD hDn _ YR, hE, hRa, ?_⟩
  rw [← clsD_natF, Category.assoc, resFreeIso_natural, ← Category.assoc, ← freeMap_comp, ← hg]
  refine AddSubgroup.closure_mono ?_ hmem
  rintro x ⟨s, c', rfl⟩
  exact ⟨a, B, φ, hφE, Uz, hUz, hS, s, c', hφ, hded, ht, hP, hz, rfl⟩

end Res

end RamanujanPetersson.EtPBC.EtMV

end

end


