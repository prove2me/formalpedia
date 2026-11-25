-- Prove2me | Definitions.Def_RPLib_FX_EtHc_07
-- name    : RPLib_FX_EtHc_07
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:34:34.620003+00:00
-- url     : https://prove2.me/theorems/c0362ba3-368e-59fa-b95d-f7202715c88d
-- title:
--   Compactly supported étale cohomology of the affine line, extension file 07 of 11
-- statement:
--   Extension file 07 of 11 for the compactly supported cohomology of the affine line, stacked on the projective-line library files it imports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Pres`: S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`
--   * `S4.Def_RP_EtCompact_P1Exc`: S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)
--
--   **Formalization note.** Extension of the `RPLib_FX_EtP1` library (étale cohomology of the projective line) to the compactly supported cohomology of the affine line $\mathbf A^1_k = D_+(X_0) \subseteq \mathbf P^1_k$ over an algebraically closed field $k$, with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): the cut sheaves $F_S$ for locally closed $S$, the excision sequence $0 \to F_{S \cap O} \to F_S \to F_{S \setminus O} \to 0$ and its long exact sequence, the vanishing of the higher cohomology of a separably closed point, and the resulting comparison $H^n_c(\mathbf A^1, \Lambda) \to H^n(\mathbf P^1, \Lambda)$ (injective for $n = 1$, bijective for $n \ge 2$) with $H^0_c(\mathbf A^1, \Lambda) = 0$. The declarations of each library module are re-hosted verbatim, except that the three excision exactness proofs `exc_exact₁/₂/₃` are re-proved element-wise (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter II, §3 (extension by zero) and Chapter VI, §1-§3 (cohomology of curves, cohomology with compact support); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapters IV-V

import Mathlib
import Definitions.Def_RPLib_FX_EtHc_04
import Definitions.Def_RPLib_FX_EtHc_06

/-!
# Compactly supported étale cohomology of the affine line, extension file 07 of 11

Declarations of the formalization of the compactly supported étale cohomology of the affine line
`A¹ = D₊(X₀) ⊆ P¹` over an algebraically closed field (the excision sequence for `j_! Λ ⊆ Λ ↠ i_* Λ`
and its consequences), stacked on the `RPLib_FX_EtP1` files it imports and re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Pres`: S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`
* `S4.Def_RP_EtCompact_P1Exc`: S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)
-/

set_option autoImplicit false

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

variable (F : EtSh Λ X) {S : Set X} (hS : IsLocallyClosed S) (O : X.Opens)

/-- **Excision (sets), exactness at `H^n_c(S \ O)`.** -/
theorem resC_bdSet_exact (n : ℕ) : Function.Exact (resC F hS O n) (bdSet F hS O n) :=
  exact_conj (hcSetEquiv F (wvSet_cut hS) n) (hcSetEquiv F (wvSet_Z hS O) n)
    (hcSetEquiv F (wvSet_U hS O) (n + 1)) (exc_exact₃ (cutOpen S) le_sup_left F n)

/-- **Excision (sets), exactness at `H^(n+1)_c(S ∩ O)`.** -/
theorem bdSet_extO_exact (n : ℕ) : Function.Exact (bdSet F hS O n) (extO F hS O (n + 1)) :=
  exact_conj (hcSetEquiv F (wvSet_Z hS O) n) (hcSetEquiv F (wvSet_U hS O) (n + 1))
    (hcSetEquiv F (wvSet_cut hS) (n + 1)) (exc_exact₁ (cutOpen S) le_sup_left F n)

end SetExc

end RamanujanPetersson.EtCompact

end

end

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

/-- `H^n_c(range i, F) ≃+ H^n(Z, i^* F)` for a closed immersion `i`. -/
def hcRangeEquiv (F : EtSh Λ X) (n : ℕ) : HcSet Λ (Set.range i) F n ≃+ H Λ ((pull i Λ).obj F) n :=
  (Hiso Λ (cutRangeIso i F) n).trans (closedH Λ i _ n)

end Closed

end General

section Point

variable {Y : Scheme.{u}} (y : Y)

variable (Λ : Type u) [CommRing Λ]

end Point

section P1

variable (K : Type u) [Field K] [IsAlgClosed K] (Λ : Type u) [CommRing Λ]

end P1

end RamanujanPetersson.EtCompact

end

end


