-- Prove2me | Definitions.Def_RPLib_FX_EtP1_29
-- name    : RPLib_FX_EtP1_29
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T12:55:30.998145+00:00
-- url     : https://prove2.me/theorems/b56b3412-b9d0-548f-81f5-2391fa2fbb5c
-- title:
--   Étale cohomology of the projective line, library file 29 of 34
-- statement:
--   File 29 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_CurveHn`: S4-EtCompact, A5: `H^(n+3) = 0` on `A¹`, `G_m` and `P¹` over an algebraically closed field (O8c, rest)
--   * `S4.Def_RP_EtCompact_CurveAll`: S4-EtCompact, D2 (O7, curve part): `H^(n+3) = 0` on `A¹`, `G_m` for every sheaf; `H^(n+4)(P¹, -) = 0`
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_44

/-!
# Étale cohomology of the projective line, library file 29 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_CurveHn`: S4-EtCompact, A5: `H^(n+3) = 0` on `A¹`, `G_m` and `P¹` over an algebraically closed field (O8c, rest)
* `S4.Def_RP_EtCompact_CurveAll`: S4-EtCompact, D2 (O7, curve part): `H^(n+3) = 0` on `A¹`, `G_m` for every sheaf; `H^(n+4)(P¹, -) = 0`
-/

set_option autoImplicit false

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

end Closed

section Curves

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0)
  (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)

include hl hΛ

/-- **`H^(n+3)(A¹, Λ) = 0`**. -/
theorem A1.H_add_three_eq_zero (n : ℕ) (e : H Λ (unitSh Λ (Spec (CommRingCat.of k[X]))) (n + 3)) : e = 0 :=
  CurveHn.H_add_three_eq_zero k[X] (fun y hy => gal_closed k k[X] y hy)
    (fun M e => H_genPt_eq_zero k l hl m hΛ 0 M e) (A1.isZero_R1_qt k l hl m hΛ) n e

theorem A1.subsingleton_h_add_two (n : ℕ) : Subsingleton (H Λ (unitSh Λ (A1 k)) (n + 2)) := by
  refine ⟨fun a b => ?_⟩
  cases n with
  | zero => rw [H2Pid.H_A1_two_eq_zero k l hl m hΛ a, H2Pid.H_A1_two_eq_zero k l hl m hΛ b]
  | succ n => rw [A1.H_add_three_eq_zero k l hl m hΛ n a, A1.H_add_three_eq_zero k l hl m hΛ n b]

/-- `R²g_* = 0` at the generic point of `G_m`. -/
theorem Gm.isZero_R1_qt (M : EtSh Λ (Spec ((Spec (CommRingCat.of (LX k))).residueField (GenBr.genPt (LX k))))) :
    IsZero (R1 (gen (LX k)) Λ (Qt Λ M)) := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_ne k hl
  refine R2Gen.isZero_R1_qt_of_C1 (GenBr.genPt (LX k)) (LX.isC1_genField k) l ?_
    (hζ.map_of_injective (LX.genConst_injective k)) m hΛ (gen (LX k)) M
  rw [← map_natCast (LX.genConst k)]
  exact (_root_.map_ne_zero (LX.genConst k)).2 hl

/-- **`H^(n+3)(G_m, Λ) = 0`**. -/
theorem Gm.H_add_three_eq_zero (n : ℕ) (e : H Λ (unitSh Λ (Gm k)) (n + 3)) : e = 0 :=
  CurveHn.H_add_three_eq_zero (LX k) (fun y hy => gal_closed k (LX k) y hy)
    (fun M e => LX.H_genPt_eq_zero k l hl m hΛ 0 M e) (Gm.isZero_R1_qt k l hl m hΛ) n e

theorem Gm.subsingleton_h_add_two (n : ℕ) : Subsingleton (H Λ (unitSh Λ (Gm k)) (n + 2)) := by
  cases n with
  | zero => exact Gm.subsingleton_h2 k l hl m hΛ
  | succ n =>
    exact ⟨fun a b => by rw [Gm.H_add_three_eq_zero k l hl m hΛ n a, Gm.H_add_three_eq_zero k l hl m hΛ n b]⟩

end Curves

end RamanujanPetersson.EtCompact.CurveHn

end

end

-- ===== S4.Def_RP_EtCompact_CurveAll =====
section

/-!
# S4-EtCompact, D2 (O7, curve part): `H^(n+3) = 0` on `A¹`, `G_m` for every sheaf; `H^(n+4)(P¹, -) = 0`

* `s1`, `s2`, **`ext_eq_zero_of_map`**: for `φ : F ⟶ G` with `Ext^(n+2)(A, ker φ) = Ext^(n+1)(A, coker φ) =
  Ext^(n+2)(A, G) = 0`, `Ext^(n+2)(A, F) = 0` (`0 → ker φ → F → im φ → 0`, `0 → im φ → G → coker φ → 0`);
* **`affine_H_add_three_eq_zero_all`**: `H^(n+3)(Spec A, F) = 0` for EVERY `F` (`A` noetherian integrally closed of
  dimension `≤ 1`, `H²(η, -) = 0`, `R²g_* = 0`, Galois-trivial closed points): `u = η_F : F ⟶ g_* g^* F` has kernel
  and cokernel supported on closed points (`GenUnit`), which are acyclic (`Cech.H_eq_zero_of_closed`);
* **`A1.H_add_three_eq_zero_all`**, **`Gm.H_add_three_eq_zero_all`** (`k = k̄`, `ℓ ≠ char k`, `ℓ^m Λ = 0`);
* **`P1.H_add_four_eq_zero_all`**: `H^(n+4)(P¹, G) = 0` for every `G` (Mayer-Vietoris).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtCompact.CurveHn

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne RamanujanPetersson.EtCompact RamanujanPetersson.Tsen
  RamanujanPetersson.EtCompact.GenFrac

universe u

section Devissage

universe w v

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {F G : C} (φ : F ⟶ G)

/-- `0 → ker φ → F → im φ → 0`. -/
abbrev s1 : ShortComplex C :=
  ShortComplex.mk (kernel.ι φ) (Abelian.factorThruImage φ) (by
    rw [← cancel_mono (Abelian.image.ι φ), Category.assoc, Abelian.image.fac, Limits.zero_comp, kernel.condition])

/-- `0 → im φ → G → coker φ → 0`. -/
abbrev s2 : ShortComplex C :=
  ShortComplex.mk (Abelian.image.ι φ) (cokernel.π φ) (by
    rw [← cancel_epi (Abelian.factorThruImage φ), ← Category.assoc, Abelian.image.fac, cokernel.condition,
      Limits.comp_zero])

theorem s2_shortExact : (s2 φ).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)

end Devissage

section Curves

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0)
  (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)

include hl hΛ

end Curves

end RamanujanPetersson.EtCompact.CurveHn

end

end


