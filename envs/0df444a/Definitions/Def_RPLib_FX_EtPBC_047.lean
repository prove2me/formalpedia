-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_047
-- name    : RPLib_FX_EtPBC_047
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:12:39.609228+00:00
-- url     : https://prove2.me/theorems/2c1e4ca8-6cab-53a3-83a0-82de26d115c9
-- title:
--   Proper base change for the projective line, library file 047
-- statement:
--   File 047 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2D2`: S4-EtPBC-A, O2 (MV route), M3 steps (2) and (4): every class of `H²(Spec A, F)` dies on a basic open
--   * `S4.Def_RP_EtPBC_A_O2T4a00`: S4-EtPBC-A, O2 S5d (O2T4a00): section class map `thetaM` and `thetaM_eq` (split from O2T4a0 for the 150 user-s cap)
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_037

/-!
# Proper base change for the projective line, library file 047

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2D2`: S4-EtPBC-A, O2 (MV route), M3 steps (2) and (4): every class of `H²(Spec A, F)` dies on a basic open
* `S4.Def_RP_EtPBC_A_O2T4a00`: S4-EtPBC-A, O2 S5d (O2T4a00): section class map `thetaM` and `thetaM_eq` (split from O2T4a0 for the 150 user-s cap)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2D2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M3 steps (2) and (4): every class of `H²(Spec A, F)` dies on a basic open

* `ext_eq_zero_of_comp`: dévissage along `φ : F ⟶ G` (`Ext^(n+2)(A, ker φ) = Ext^(n+1)(A, coker φ) = 0`): a class
  `e ∈ Ext^(n+2)(A, F)` with `e ∘ φ = 0` is zero;
* `isAffineOpen_bOpen`; **`acyc_bOpen`** (step (2)): `Ext^(n+1)(Λ[D(f)], Q) = 0` when `Q` has zero generic stalk,
  closed points of `Spec A` have algebraically closed residue fields and `D(f)` has a non-generic point;
* **`two_dies`** (step (4)): every `β ∈ H²(Spec A, F)` dies on some `D(f)`, `f ≠ 0` (unit `F ⟶ g_* g^* F`, its kernel
  and cokernel are acyclic on `D(f)`, and `push_two_dies`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.EtCompact.CurveHn

section Devissage

universe w v u

end Devissage

variable {A : Type} [CommRing A] [IsDomain A] {Λ : Type} [CommRing Λ]

variable [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

/-- **Step (2): acyclicity on `D(f)`** of sheaves with zero generic stalk. -/
theorem acyc_bOpen
    (hcl : ∀ y : Spec (CommRingCat.of A), IsClosed ({y} : Set (Spec (CommRingCat.of A))) →
      IsAlgClosed ((Spec (CommRingCat.of A)).residueField y))
    (f : A) (hm : ∃ m : Spec (CommRingCat.of A), m ∈ bOpen f ∧ m ≠ GenBr.genPt A)
    (Q : EtSh Λ (Spec (CommRingCat.of A))) (h0 : IsZero (stalk Λ Q (GenBr.genPt A))) (n : ℕ)
    (e : Ext (freeSh Λ (opEt (bOpen f))) Q (n + 1)) : e = 0 := by
  have : IsAffine (opEt (bOpen f)).left := isAffineOpen_bOpen f
  have : IsLocallyNoetherian (opEt (bOpen f)).left := inferInstanceAs (IsLocallyNoetherian (bOpen f).toScheme)
  have : IsAffine ((𝟭 Scheme).obj (opEt (bOpen f)).left) := isAffineOpen_bOpen f
  have : IsLocallyNoetherian ((𝟭 Scheme).obj (opEt (bOpen f)).left) :=
    inferInstanceAs (IsLocallyNoetherian (bOpen f).toScheme)
  refine ext_free_eq_zero _ _ _ (fun c => ?_) e
  refine Cech.H_eq_zero_of_closed _ (fun y hy => ?_) (fun y hy => ?_) n c
  · have hy' : ¬ IsClosed ({(opEt (bOpen f)).hom y} : Set (Spec (CommRingCat.of A))) := by
      intro hc
      apply hy
      have hpre := hc.preimage (opEt (bOpen f)).hom.continuous
      have hs : (opEt (bOpen f)).hom ⁻¹' {(opEt (bOpen f)).hom y} = {y} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact (opEt (bOpen f)).hom.isOpenEmbedding.injective.eq_iff
      rwa [hs] at hpre
    have hg := R1Gen.eq_genPt _ hy'
    refine StkTr.isZero_res (opEt (bOpen f)).hom Q y ?_
    rw [hg]
    exact h0
  · have hne := ne_genPt_of_closed f hm y hy
    have hc : IsClosed ({(opEt (bOpen f)).hom y} : Set (Spec (CommRingCat.of A))) := by
      by_contra h
      exact hne (R1Gen.eq_genPt _ h)
    have := hcl _ hc
    have : IsAlgClosed (((𝟭 Scheme).obj (opEt (bOpen f)).left).residueField y) :=
      IsAlgClosed.of_ringEquiv ((Spec (CommRingCat.of A)).residueField ((opEt (bOpen f)).hom y)) _
        (asIso ((opEt (bOpen f)).hom.residueFieldMap y)).commRingCatIsoToRingEquiv
    exact gal_subsingleton y

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T4a00 =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4a00): section class map `thetaM` and `thetaM_eq` (split from O2T4a0 for the 150 user-s cap)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section Theta

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}}

/-- **The section class map** `H^n(W, Λ) → Ext^n_P(Λ[W], Λ[T])` of `m : W ⟶ T`. -/
def thetaM {W T : P.Etale} (m : W ⟶ T) (n : ℕ) (κ : H Λ (unitSh Λ W.left) n) : Ext.{u} (freeSh Λ W) (freeSh Λ T) n :=
  (extFree Λ W (freeSh Λ T) n).symm (κ.comp (Ext.mk₀ (secMap Λ m)) (add_zero n))

end Theta

end RamanujanPetersson.EtPBC.EtMV

end

end


