-- Prove2me | Definitions.Def_RPLib_FX_EtHc_09
-- name    : RPLib_FX_EtHc_09
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:31:18.042671+00:00
-- url     : https://prove2.me/theorems/b4b4f21a-6ee7-5666-9bf2-9644ea2d0cd9
-- title:
--   Compactly supported étale cohomology of the affine line, extension file 09 of 11
-- statement:
--   Extension file 09 of 11 for the compactly supported cohomology of the affine line, stacked on the projective-line library files it imports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_P1Exc`: S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)
--   * `S4.Def_RP_EtCompact_P1H0`: S4-EtCompact, part 30: `H^0_c(A^1, Λ) = 0` and `H^1_c(A^1, Λ) ≃ H^1(P^1, Λ)` (O8a, file 4)
--
--   **Formalization note.** Extension of the `RPLib_FX_EtP1` library (étale cohomology of the projective line) to the compactly supported cohomology of the affine line $\mathbf A^1_k = D_+(X_0) \subseteq \mathbf P^1_k$ over an algebraically closed field $k$, with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): the cut sheaves $F_S$ for locally closed $S$, the excision sequence $0 \to F_{S \cap O} \to F_S \to F_{S \setminus O} \to 0$ and its long exact sequence, the vanishing of the higher cohomology of a separably closed point, and the resulting comparison $H^n_c(\mathbf A^1, \Lambda) \to H^n(\mathbf P^1, \Lambda)$ (injective for $n = 1$, bijective for $n \ge 2$) with $H^0_c(\mathbf A^1, \Lambda) = 0$. The declarations of each library module are re-hosted verbatim, except that the three excision exactness proofs `exc_exact₁/₂/₃` are re-proved element-wise (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter II, §3 (extension by zero) and Chapter VI, §1-§3 (cohomology of curves, cohomology with compact support); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapters IV-V

import Mathlib
import Definitions.Def_RPLib_FX_EtHc_08

/-!
# Compactly supported étale cohomology of the affine line, extension file 09 of 11

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

end Point

section P1

variable (K : Type u) [Field K] [IsAlgClosed K] (Λ : Type u) [CommRing Λ]

/-- **`H^m_c(A^1 ⊆ P^1, F) ≅ H^m(P^1, cut univ F)` for `m ≥ 2`** (excision at `∞`). -/
theorem P1.extO_bijective (F : EtSh Λ (P1 K)) (n : ℕ) :
    Function.Bijective (extO F (P1.isLocallyClosed_univ K) (chartA1 K).opensRange (n + 2)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨b, rfl⟩ := (bdSet_extO_exact F (P1.isLocallyClosed_univ K) (chartA1 K).opensRange (n + 1) a).mp ha
    rw [P1.hc_diff_eq_zero K Λ F n b, map_zero]
  · intro a
    exact (extO_resC_exact F (P1.isLocallyClosed_univ K) (chartA1 K).opensRange (n + 2) a).mp
      (P1.hc_diff_eq_zero K Λ F (n + 1) _)

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

/-- `H^0_c(S) → H^0_c(S \ O)` is onto when `cut S F ≅ Λ_X` and `S \ O ⊆ {x0}`. -/
theorem resC_zero_surjective (F : EtSh Λ X) {S : Set X} (hS : IsLocallyClosed S) (O : X.Opens)
    (e : unitSh Λ X ≅ cut Λ S F) (x0 : X) (hSO : S \ (O : Set X) ⊆ {x0}) :
    Function.Surjective (resC F hS O 0) := by
  intro y
  obtain ⟨g, hg⟩ := (Ext.mk₀_bijective _ _).2 (hcSetEquiv F (wvSet_Z hS O) 0 y)
  have hB : ∀ x : X, x ≠ x0 →
      IsZero (((geomPtAt x).stalkF Λ).obj (cutWV Λ (cutOpen S) (cutCompl S ⊔ O) F)) :=
    fun x hx => (isZero_stalk_cut (S \ (O : Set X)) F (geomPtAt x)
      (by rw [center_geomPtAt]; exact fun h => hx (hSO h))).of_iso
        (((geomPtAt x).stalkF Λ).mapIso (cutIsoCutWV F (wvSet_Z hS O))).symm
  have := epi_excComplex_g (cutOpen S) (le_sup_left : cutCompl S ≤ cutCompl S ⊔ O) F
  obtain ⟨f, hf⟩ : ∃ f : unitSh Λ X ⟶ cutWV Λ (cutOpen S) (cutCompl S) F,
      f ≫ (excComplex (cutOpen S) (le_sup_left : cutCompl S ≤ cutCompl S ⊔ O) F).g = g :=
    exists_lift_unitSh Λ (excComplex (cutOpen S) (le_sup_left : cutCompl S ≤ cutCompl S ⊔ O) F).g
      (e ≪≫ cutIsoCutWV F (wvSet_cut hS)) x0 hB g
  have key : Hmap Λ (excComplex (cutOpen S) (le_sup_left : cutCompl S ≤ cutCompl S ⊔ O) F).g 0
      (hcSetEquiv F (wvSet_cut hS) 0 ((hcSetEquiv F (wvSet_cut hS) 0).symm (Ext.mk₀ f))) = Ext.mk₀ g :=
    (congrArg (Hmap Λ (excComplex (cutOpen S) (le_sup_left : cutCompl S ≤ cutCompl S ⊔ O) F).g 0)
      (AddEquiv.apply_symm_apply _ _)).trans ((Ext.mk₀_comp_mk₀ f _).trans (congrArg Ext.mk₀ hf))
  refine ⟨(hcSetEquiv F (wvSet_cut hS) 0).symm (Ext.mk₀ f),
    (resC_apply' F hS O 0 _).trans ((congrArg (hcSetEquiv F (wvSet_Z hS O) 0).symm key).trans ?_)⟩
  rw [hg, AddEquiv.symm_apply_apply]

end Res

section P1

variable (K : Type u) [Field K] (Λ : Type u) [CommRing Λ]

variable [IsAlgClosed K]

end P1

end RamanujanPetersson.EtCompact

end

end


