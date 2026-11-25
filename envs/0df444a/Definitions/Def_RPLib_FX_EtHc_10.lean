-- Prove2me | Definitions.Def_RPLib_FX_EtHc_10
-- name    : RPLib_FX_EtHc_10
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:37:01.934256+00:00
-- url     : https://prove2.me/theorems/7e5e44fc-e970-5114-8d74-71c21a3ac914
-- title:
--   Compactly supported étale cohomology of the affine line, extension file 10 of 11
-- statement:
--   Extension file 10 of 11 for the compactly supported cohomology of the affine line, stacked on the projective-line library files it imports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_P1H0`: S4-EtCompact, part 30: `H^0_c(A^1, Λ) = 0` and `H^1_c(A^1, Λ) ≃ H^1(P^1, Λ)` (O8a, file 4)
--
--   **Formalization note.** Extension of the `RPLib_FX_EtP1` library (étale cohomology of the projective line) to the compactly supported cohomology of the affine line $\mathbf A^1_k = D_+(X_0) \subseteq \mathbf P^1_k$ over an algebraically closed field $k$, with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): the cut sheaves $F_S$ for locally closed $S$, the excision sequence $0 \to F_{S \cap O} \to F_S \to F_{S \setminus O} \to 0$ and its long exact sequence, the vanishing of the higher cohomology of a separably closed point, and the resulting comparison $H^n_c(\mathbf A^1, \Lambda) \to H^n(\mathbf P^1, \Lambda)$ (injective for $n = 1$, bijective for $n \ge 2$) with $H^0_c(\mathbf A^1, \Lambda) = 0$. The declarations of each library module are re-hosted verbatim, except that the three excision exactness proofs `exc_exact₁/₂/₃` are re-proved element-wise (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter II, §3 (extension by zero) and Chapter VI, §1-§3 (cohomology of curves, cohomology with compact support); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapters IV-V

import Mathlib
import Definitions.Def_RPLib_FX_EtHc_09

/-!
# Compactly supported étale cohomology of the affine line, extension file 10 of 11

Declarations of the formalization of the compactly supported étale cohomology of the affine line
`A¹ = D₊(X₀) ⊆ P¹` over an algebraically closed field (the excision sequence for `j_! Λ ⊆ Λ ↠ i_* Λ`
and its consequences), stacked on the `RPLib_FX_EtP1` files it imports and re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_P1H0`: S4-EtCompact, part 30: `H^0_c(A^1, Λ) = 0` and `H^1_c(A^1, Λ) ≃ H^1(P^1, Λ)` (O8a, file 4)
-/

set_option autoImplicit false

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

/-- ... hence extension by zero is injective in degree `1`. -/
theorem extO_one_injective_of (F : EtSh Λ X) {S : Set X} (hS : IsLocallyClosed S) (O : X.Opens)
    (e : unitSh Λ X ≅ cut Λ S F) (x0 : X) (hSO : S \ (O : Set X) ⊆ {x0}) :
    Function.Injective (extO F hS O 1) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨b, rfl⟩ := (bdSet_extO_exact F hS O 0 a).1 ha
  obtain ⟨c, rfl⟩ := resC_zero_surjective F hS O e x0 hSO b
  exact (resC_bdSet_exact F hS O 0 _).2 ⟨c, rfl⟩

end Res

section P1

variable (K : Type u) [Field K] (Λ : Type u) [CommRing Λ]

theorem P1.extO_one_injective :
    Function.Injective (extO (unitSh Λ (P1 K)) (P1.isLocallyClosed_univ K) (chartA1 K).opensRange 1) :=
  extO_one_injective_of _ _ _ (cutUnivIso _).symm (P1.infPt K) (P1.univ_diff_range_chartA1 K).subset

variable [IsAlgClosed K]

end P1

end RamanujanPetersson.EtCompact

end

end


