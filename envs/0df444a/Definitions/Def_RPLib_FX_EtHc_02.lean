-- Prove2me | Definitions.Def_RPLib_FX_EtHc_02
-- name    : RPLib_FX_EtHc_02
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T13:40:38.148338+00:00
-- url     : https://prove2.me/theorems/5e06553b-0ba1-5feb-9e45-1aa3ee28d957
-- title:
--   Compactly supported étale cohomology of the affine line, extension file 02 of 11
-- statement:
--   Extension file 02 of 11 for the compactly supported cohomology of the affine line, stacked on the projective-line library files it imports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
--   * `S4.Def_RP_EtCompact_Pres`: S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`
--
--   **Formalization note.** Extension of the `RPLib_FX_EtP1` library (étale cohomology of the projective line) to the compactly supported cohomology of the affine line $\mathbf A^1_k = D_+(X_0) \subseteq \mathbf P^1_k$ over an algebraically closed field $k$, with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): the cut sheaves $F_S$ for locally closed $S$, the excision sequence $0 \to F_{S \cap O} \to F_S \to F_{S \setminus O} \to 0$ and its long exact sequence, the vanishing of the higher cohomology of a separably closed point, and the resulting comparison $H^n_c(\mathbf A^1, \Lambda) \to H^n(\mathbf P^1, \Lambda)$ (injective for $n = 1$, bijective for $n \ge 2$) with $H^0_c(\mathbf A^1, \Lambda) = 0$. The declarations of each library module are re-hosted verbatim, except that the three excision exactness proofs `exc_exact₁/₂/₃` are re-proved element-wise (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter II, §3 (extension by zero) and Chapter VI, §1-§3 (cohomology of curves, cohomology with compact support); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapters IV-V

import Mathlib
import Definitions.Def_RPLib_FX_EtHc_01

/-!
# Compactly supported étale cohomology of the affine line, extension file 02 of 11

Declarations of the formalization of the compactly supported étale cohomology of the affine line
`A¹ = D₊(X₀) ⊆ P¹` over an algebraically closed field (the excision sequence for `j_! Λ ⊆ Λ ↠ i_* Λ`
and its consequences), stacked on the `RPLib_FX_EtP1` files it imports and re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim (except that the excision exactness proofs
`exc_exact₁/₂/₃` are re-proved element-wise, which the kernel checks faster) with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
* `S4.Def_RP_EtCompact_Pres`: S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_Exc =====
section

/-!
# S4-EtCompact, part 5: the excision sequence (compact supports, subset model)

On an ambient scheme `P` (the compactification), cohomology with compact supports of the
locally closed set `W ∩ Vᶜ` (`W, V` open) is `HcWV W V F n := H^n(P, cutWV W V F)`.
For opens `V ≤ V'` the set `S = W ∩ Vᶜ` splits into the relatively open `U = (W ⊓ V') ∩ Vᶜ`
and the relatively closed `Z = W ∩ V'ᶜ`, and
`0 ⟶ cutWV (W ⊓ V') V F ⟶ cutWV W V F ⟶ cutWV W V' F ⟶ 0`
is short exact (checked on stalks). Hence the **excision long exact sequence**
`… ⟶ H^n_c(U) ⟶ H^n_c(S) ⟶ H^n_c(Z) ⟶ H^(n+1)_c(U) ⟶ …` (E0Probe P2a).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

variable {Λ} (W : X.Opens) {V V' : X.Opens} (h : V ≤ V') (F : EtSh Λ X)

/-- The boundary map `H^n_c(Z) → H^(n+1)_c(U)` of the excision sequence. -/
def excδ (n : ℕ) : HcWV Λ W V' F n →+ HcWV Λ (W ⊓ V') V F (n + 1) :=
  (excComplex_shortExact W h F).extClass.postcomp _ rfl

/-- **Excision, exactness at `H^(n+1)_c(U)`**: `H^n_c(Z) → H^(n+1)_c(U) → H^(n+1)_c(S)`. -/
theorem exc_exact₁ (n : ℕ) :
    Function.Exact (excδ W h F n) (Hmap Λ (excComplex W h F).f (n + 1)) := by
  -- element-wise (`Ext.covariant_sequence_exact₁`): the `AddCommGrpCat` form costs the kernel ~2x more
  intro y
  constructor
  · intro hy
    exact Ext.covariant_sequence_exact₁ (unitSh Λ X) (excComplex_shortExact W h F) y hy rfl
  · rintro ⟨x, rfl⟩
    have h0 : (excComplex_shortExact W h F).extClass.comp (Ext.mk₀ (excComplex W h F).f) (add_zero 1) = 0 :=
      (excComplex_shortExact W h F).extClass_comp
    calc _ = (x : H Λ (excComplex W h F).X₃ n).comp
          ((excComplex_shortExact W h F).extClass.comp (Ext.mk₀ (excComplex W h F).f) (add_zero 1)) rfl :=
            Ext.comp_assoc_of_third_deg_zero _ _ _ _
      _ = 0 := by rw [h0]; exact Ext.comp_zero _ _ _ _ _

end RamanujanPetersson.EtCompact


end

-- ===== S4.Def_RP_EtCompact_Pres =====
section

/-!
# S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`

`cutWV W V F` only depends on the locally closed set `W ∩ Vᶜ` (up to a canonical chain of stalkwise
isomorphisms). So `HcSet S F n := H^n(X, cut S F)` (`cut` from `Def_RP_EtSheaves_CutSet`, which is
`cutWV (cutOpen S) (cutCompl S)`) is computed by any presentation `S = W ∩ Vᶜ`, and the excision
long exact sequence holds for every locally closed `S` and open `O`:
`… → H^n_c(S ∩ O) → H^n_c(S) → H^n_c(S \ O) → H^(n+1)_c(S ∩ O) → …` (E0Probe P2 in subset form).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

section Pres

variable (F : EtSh Λ X)

variable {W₁ V₁ W₂ V₂ : X.Opens} (hS : wvSet W₁ V₁ = wvSet W₂ V₂)

end Pres

section HcSet

variable (F : EtSh Λ X)

end HcSet

section SetExc

theorem exact_conj {A B C A' B' C' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C'] (e₁ : A' ≃+ A) (e₂ : B' ≃+ B)
    (e₃ : C' ≃+ C) {f : A →+ B} {g : B →+ C} (h : Function.Exact f g) :
    Function.Exact (fun x => e₂.symm (f (e₁ x))) (fun y => e₃.symm (g (e₂ y))) := by
  intro y
  constructor
  · intro hy
    have h0 : g (e₂ y) = 0 := by
      have := congrArg e₃ hy
      rwa [AddEquiv.apply_symm_apply, map_zero] at this
    obtain ⟨a, ha⟩ := (h (e₂ y)).1 h0
    refine ⟨e₁.symm a, ?_⟩
    show e₂.symm (f (e₁ (e₁.symm a))) = y
    rw [AddEquiv.apply_symm_apply, ha, AddEquiv.symm_apply_apply]
  · rintro ⟨x, rfl⟩
    show e₃.symm (g (e₂ (e₂.symm (f (e₁ x))))) = 0
    rw [AddEquiv.apply_symm_apply, h.apply_apply_eq_zero, map_zero]

variable (F : EtSh Λ X) {S : Set X} (hS : IsLocallyClosed S) (O : X.Opens)

end SetExc

end RamanujanPetersson.EtCompact

end

end


