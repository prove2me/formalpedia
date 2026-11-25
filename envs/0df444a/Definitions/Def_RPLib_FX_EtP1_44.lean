-- Prove2me | Definitions.Def_RPLib_FX_EtP1_44
-- name    : RPLib_FX_EtP1_44
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T12:49:24.273314+00:00
-- url     : https://prove2.me/theorems/bed7a92f-24cb-5c11-8313-58577c847c05
-- title:
--   Étale cohomology of the projective line, library file 44 (an extra file from a re-cut)
-- statement:
--   File 44 (an extra file from a re-cut) of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_R1Gen`: S4-EtCompact, B1: `R¹g_* N` has vanishing generic stalk, hence no higher cohomology on a curve
--   * `S4.Def_RP_EtCompact_CurveHn`: S4-EtCompact, A5: `H^(n+3) = 0` on `A¹`, `G_m` and `P¹` over an algebraically closed field (O8c, rest)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_28

/-!
# Étale cohomology of the projective line, library file 44 (extra file from a re-cut)

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_R1Gen`: S4-EtCompact, B1: `R¹g_* N` has vanishing generic stalk, hence no higher cohomology on a curve
* `S4.Def_RP_EtCompact_CurveHn`: S4-EtCompact, A5: `H^(n+3) = 0` on `A¹`, `G_m` and `P¹` over an algebraically closed field (O8c, rest)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_R1Gen =====
section

/-!
# S4-EtCompact, B1: `R¹g_* N` has vanishing generic stalk, hence no higher cohomology on a curve

`A` a noetherian integrally closed domain of dimension `≤ 1`, `g = gen A : Spec κ(η) ⟶ Spec A`.

* **`isZero_R1_gen`**: the stalk of `R¹g_* N` at `η` vanishes (`GenStalk.epi_push` + `GPtIso.isZero_stalk_cokernel`);
* `eq_genPt`: the only non-closed point of `Spec A` is `η`; `hF_R1`;
* **`H_R1_eq_zero`**: `H^(n+1)(Spec A, R¹g_* N) = 0` when the closed points have trivial Galois groups
  (`Cech.H_eq_zero_of_closed`);
* **`H_push_gen_eq_zero`**: `H^(n+3)(Spec A, g_* N) = 0` given `H²(η, -) = 0` and `R²g_* = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.R1Gen

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac

variable {A : Type} [CommRing A] [IsDomain A] {Λ : Type} [CommRing Λ]

/-- **`H^(n+3)(Spec A, g_* N) = 0`** given `H²(η, -) = 0` and `R²g_* = 0`. -/
theorem H_push_gen_eq_zero [IsNoetherianRing A] [IsIntegrallyClosed A] [Ring.KrullDimLE 1 A]
    (hG : ∀ y : Spec (CommRingCat.of A), IsClosed ({y} : Set (Spec (CommRingCat.of A))) → Subsingleton (Gal y))
    (hη : ∀ (M : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))) (e : H Λ M 2), e = 0)
    (hR : ∀ M : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))),
      IsZero (R1 (gen A) Λ (Qt Λ M)))
    (N : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))) (n : ℕ)
    (e : H Λ ((push (gen A) Λ).obj N) (n + 3)) : e = 0 :=
  H_push_eq_zero_of_R1 hη hR n N (H_R1_eq_zero hG N n) e

end RamanujanPetersson.EtCompact.R1Gen

end

end

-- ===== S4.Def_RP_EtCompact_CurveHn =====
section

/-!
# S4-EtCompact, A5: `H^(n+3) = 0` on `A¹`, `G_m` and `P¹` over an algebraically closed field (O8c, rest)

* `gal_closed`: closed points of a finite type `k`-algebra (`k` algebraically closed) have trivial Galois groups
  (Mathlib `residueFieldIsoBase`);
* **`H_add_three_eq_zero`**: `H^(n+3)(Spec A, Λ) = 0` for a noetherian integrally closed domain of dimension `≤ 1`
  with `H²(η, -) = 0`, `R²g_* = 0` and Galois-trivial closed points (`R1Gen.H_push_gen_eq_zero` +
  `SgUnit.unitIsoPush`);
* **`A1.H_add_three_eq_zero`**, **`Gm.H_add_three_eq_zero`**: the hypotheses hold for `k[X]`, `k[X]_X` (Tsen +
  `R2Gen.isZero_R1_qt_of_C1`);
* **`P1.H_add_three_eq_zero`**: `H^(n+3)(P¹, Λ) = 0` (`P1.subsingleton_h_add_three`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtCompact.CurveHn

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne RamanujanPetersson.EtCompact RamanujanPetersson.Tsen
  RamanujanPetersson.EtCompact.GenFrac

section Closed

variable (k : Type) [Field k] [IsAlgClosed k] (A : Type) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

include k

/-- Closed points of `Spec A`, `A` of finite type over `k = k̄`, have trivial Galois groups. -/
theorem gal_closed (y : Spec (CommRingCat.of A)) (hy : IsClosed ({y} : Set (Spec (CommRingCat.of A)))) :
    Subsingleton (Gal y) := by
  have := isAlgClosed_residue k A y hy
  exact gal_subsingleton y

end Closed

/-- **`H^(n+3)(Spec A, Λ) = 0`** for a noetherian integrally closed domain of dimension `≤ 1`. -/
theorem H_add_three_eq_zero (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Ring.KrullDimLE 1 A] {Λ : Type} [CommRing Λ]
    (hG : ∀ y : Spec (CommRingCat.of A), IsClosed ({y} : Set (Spec (CommRingCat.of A))) → Subsingleton (Gal y))
    (hη : ∀ (M : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))) (e : H Λ M 2), e = 0)
    (hR : ∀ M : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))),
      IsZero (R1 (gen A) Λ (Qt Λ M)))
    (n : ℕ) (e : H Λ (unitSh Λ (Spec (CommRingCat.of A))) (n + 3)) : e = 0 := by
  have h0 := R1Gen.H_push_gen_eq_zero hG hη hR (unitSh Λ _) n
    (e.comp (Abelian.Ext.mk₀ (SgUnit.unitIsoPush A (Λ := Λ)).hom) (add_zero _))
  have he : e = (e.comp (Abelian.Ext.mk₀ (SgUnit.unitIsoPush A (Λ := Λ)).hom) (add_zero _)).comp
      (Abelian.Ext.mk₀ (SgUnit.unitIsoPush A (Λ := Λ)).inv) (add_zero _) := by
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
      Abelian.Ext.comp_mk₀_id]
  rw [he, h0, Abelian.Ext.zero_comp]

section Curves

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0)
  (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)

include hl hΛ

/-- `R²g_* = 0` at the generic point of `A¹`. -/
theorem A1.isZero_R1_qt (M : EtSh Λ (Spec ((Spec (CommRingCat.of k[X])).residueField (GenBr.genPt k[X])))) :
    IsZero (R1 (gen k[X]) Λ (Qt Λ M)) := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_ne k hl
  refine R2Gen.isZero_R1_qt_of_C1 (GenBr.genPt k[X]) (isC1_genField_polynomial k) l ?_
    (hζ.map_of_injective (genConst_injective k)) m hΛ (gen k[X]) M
  rw [← map_natCast (genConst k)]
  exact (_root_.map_ne_zero (genConst k)).2 hl

end Curves

end RamanujanPetersson.EtCompact.CurveHn

end

end


