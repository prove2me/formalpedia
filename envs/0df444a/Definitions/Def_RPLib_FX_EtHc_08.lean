-- Prove2me | Definitions.Def_RPLib_FX_EtHc_08
-- name    : RPLib_FX_EtHc_08
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:08:01.166838+00:00
-- url     : https://prove2.me/theorems/4d291e66-5f42-47fa-ab3b-ac0731ac4bc3
-- title:
--   Compactly supported étale cohomology of the affine line, extension file 08 of 11
-- statement:
--   Extension file 08 of 11 for the compactly supported cohomology of the affine line, stacked on the projective-line library files it imports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_P1Exc`: S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)
--   * `S4.Def_RP_EtCompact_P1H0`: S4-EtCompact, part 30: `H^0_c(A^1, Λ) = 0` and `H^1_c(A^1, Λ) ≃ H^1(P^1, Λ)` (O8a, file 4)
--
--   **Formalization note.** Extension of the `RPLib_FX_EtP1` library (étale cohomology of the projective line) to the compactly supported cohomology of the affine line $\mathbf A^1_k = D_+(X_0) \subseteq \mathbf P^1_k$ over an algebraically closed field $k$, with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): the cut sheaves $F_S$ for locally closed $S$, the excision sequence $0 \to F_{S \cap O} \to F_S \to F_{S \setminus O} \to 0$ and its long exact sequence, the vanishing of the higher cohomology of a separably closed point, and the resulting comparison $H^n_c(\mathbf A^1, \Lambda) \to H^n(\mathbf P^1, \Lambda)$ (injective for $n = 1$, bijective for $n \ge 2$) with $H^0_c(\mathbf A^1, \Lambda) = 0$. The declarations of each library module are re-hosted verbatim, except that the three excision exactness proofs `exc_exact₁/₂/₃` are re-proved element-wise (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter II, §3 (extension by zero) and Chapter VI, §1-§3 (cohomology of curves, cohomology with compact support); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapters IV-V

import Mathlib
import Definitions.Def_RPLib_FX_EtHc_07

/-!
# Compactly supported étale cohomology of the affine line, extension file 08 of 11

Declarations of the formalization of the compactly supported étale cohomology of the affine line
`A¹ = D₊(X₀) ⊆ P¹` over an algebraically closed field (the excision sequence for `j_! Λ ⊆ Λ ↠ i_* Λ`
and its consequences), stacked on the `RPLib_FX_EtP1` files it imports and re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_P1Exc`: S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)
* `S4.Def_RP_EtCompact_P1H0`: S4-EtCompact, part 30: `H^0_c(A^1, Λ) = 0` and `H^1_c(A^1, Λ) ≃ H^1(P^1, Λ)` (O8a, file 4)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_P1Exc =====
section

/-!
# S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)

General facts:
* `Hmap_zero_injective`: `H^0(X, -)` sends monomorphisms to injections; so `extO` is injective in degree 0.
* `cutUnivIso : cut univ F ≅ F`; `cutRangeIso i F : cut (range i) F ≅ i_* i^* F` for a closed immersion `i`
  (from the EtSheaves cut sequence), hence `hcRangeEquiv : H^n_c(range i, F) ≃+ H^n(Z, i^* F)`.
* The point scheme `Spec κ(y)` of a point `y`: `Spec κ(y) ⟶ Spec κ(y)`'s residue map is an isomorphism and
  `κ(pt) ≅ κ(y)`; for `κ(y)` algebraically closed, `H^(n+1)(Spec κ(y), -) = 0` (`H_ptOf_eq_zero`), so
  `H^(n+1)_c({y}, F) = 0` for every closed point `y` with algebraically closed residue field (`hc_closedPt_eq_zero`).

On `P^1_K` (`K` algebraically closed), with `S = univ` and `O = A^1 = D₊(X₀)` (`S \ O = {∞}`), the excision sequence
gives: `extO : H^m_c(A^1 ⊆ P^1, F) → H^m(P^1, cut univ F)` is bijective for `m ≥ 2`, surjective for `m = 1` and
injective for `m = 0` (`P1.extO_bijective`, `P1.extO_one_surjective`, `extO_zero_injective`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section General

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

section Closed

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

end Closed

end General

section Point

variable {Y : Scheme.{u}} (y : Y)

variable (Λ : Type u) [CommRing Λ]

/-- **`H^(n+1)_c({y}, F) = 0`** for a closed point `y` with algebraically closed residue field. -/
theorem hc_closedPt_eq_zero [IsAlgClosed (Y.residueField y)] (hy : IsClosed ({y} : Set Y)) (F : EtSh Λ Y)
    (n : ℕ) (e : HcSet Λ {y} F (n + 1)) : e = 0 := by
  have : IsClosedImmersion (Y.fromSpecResidueField y) := isClosed_singleton_iff_isClosedImmersion.mp hy
  revert e
  rw [← Scheme.range_fromSpecResidueField y]
  intro e
  apply (hcRangeEquiv (Y.fromSpecResidueField y) F (n + 1)).injective
  rw [map_zero]
  exact H_ptOf_eq_zero y Λ _ n _

end Point

section P1

variable (K : Type u) [Field K] [IsAlgClosed K] (Λ : Type u) [CommRing Λ]

theorem P1.hc_inf_eq_zero (F : EtSh Λ (P1 K)) (n : ℕ) (e : HcSet Λ {P1.infPt K} F (n + 1)) : e = 0 :=
  hc_closedPt_eq_zero (P1.infPt K) Λ (P1.isClosed_infPt K) F n e

theorem P1.hc_diff_eq_zero (F : EtSh Λ (P1 K)) (n : ℕ)
    (e : HcSet Λ (Set.univ \ ((chartA1 K).opensRange : Set (P1 K))) F (n + 1)) : e = 0 := by
  revert e
  rw [P1.univ_diff_range_chartA1]
  exact P1.hc_inf_eq_zero K Λ F n

end P1

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_P1H0 =====
section

/-!
# S4-EtCompact, part 30: `H^0_c(A^1, Λ) = 0` and `H^1_c(A^1, Λ) ≃ H^1(P^1, Λ)` (O8a, file 4)

* `smulEnd r F : F ⟶ F` (multiplication by `r : Λ`); its stalk maps are `r • 𝟙` (`stalk_smulEnd`).
* `exists_lift_unitSh`: if `ρ : A ⟶ B` is epi, `A ≅ Λ_X` and `B` has zero stalks off one point `x0`, every
  `ψ : Λ_X ⟶ B` lifts through `ρ` (stalk at `x0` is cyclic on `1`).
* `resC_zero_surjective`: `H^0_c(S) → H^0_c(S \ O)` is onto when `cut S F ≅ Λ_X` and `S \ O` is at most a point;
  hence `extO` is injective in degree `1` (`extO_one_injective_of`).
* `P1.hcA1_zero_eq_zero`, **`A1.hc_zero_eq_zero`**: `H^0_c(A^1, Λ) = 0` (any field).
* **`A1.hcEquivP1One`**: `H^1_c(A^1, Λ) ≃+ H^1(P^1, Λ)` (`K` algebraically closed).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section Smul

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end Smul

section Lift

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

end Lift

section Res

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

theorem resC_apply' (F : EtSh Λ X) {S : Set X} (hS : IsLocallyClosed S) (O : X.Opens) (n : ℕ)
    (x : HcSet Λ S F n) :
    resC F hS O n x = (hcSetEquiv F (wvSet_Z hS O) n).symm
      (Hmap Λ (excComplex (cutOpen S) (le_sup_left : cutCompl S ≤ cutCompl S ⊔ O) F).g n
        (hcSetEquiv F (wvSet_cut hS) n x)) :=
  rfl

end Res

section P1

variable (K : Type u) [Field K] (Λ : Type u) [CommRing Λ]

variable [IsAlgClosed K]

end P1

end RamanujanPetersson.EtCompact

end

end


