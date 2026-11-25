-- Prove2me | Definitions.Def_RPLib_FX_EtHc_06
-- name    : RPLib_FX_EtHc_06
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:28:44.286096+00:00
-- url     : https://prove2.me/theorems/86cdfb0f-63c7-54d9-869c-8a33d3085c22
-- title:
--   Compactly supported étale cohomology of the affine line, extension file 06 of 11
-- statement:
--   Extension file 06 of 11 for the compactly supported cohomology of the affine line, stacked on the projective-line library files it imports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Pres`: S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`
--
--   **Formalization note.** Extension of the `RPLib_FX_EtP1` library (étale cohomology of the projective line) to the compactly supported cohomology of the affine line $\mathbf A^1_k = D_+(X_0) \subseteq \mathbf P^1_k$ over an algebraically closed field $k$, with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): the cut sheaves $F_S$ for locally closed $S$, the excision sequence $0 \to F_{S \cap O} \to F_S \to F_{S \setminus O} \to 0$ and its long exact sequence, the vanishing of the higher cohomology of a separably closed point, and the resulting comparison $H^n_c(\mathbf A^1, \Lambda) \to H^n(\mathbf P^1, \Lambda)$ (injective for $n = 1$, bijective for $n \ge 2$) with $H^0_c(\mathbf A^1, \Lambda) = 0$. The declarations of each library module are re-hosted verbatim, except that the three excision exactness proofs `exc_exact₁/₂/₃` are re-proved element-wise (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter II, §3 (extension by zero) and Chapter VI, §1-§3 (cohomology of curves, cohomology with compact support); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapters IV-V

import Mathlib
import Definitions.Def_RPLib_FX_EtHc_05

/-!
# Compactly supported étale cohomology of the affine line, extension file 06 of 11

Declarations of the formalization of the compactly supported étale cohomology of the affine line
`A¹ = D₊(X₀) ⊆ P¹` over an algebraically closed field (the excision sequence for `j_! Λ ⊆ Λ ↠ i_* Λ`
and its consequences), stacked on the `RPLib_FX_EtP1` files it imports and re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Pres`: S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`
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

/-- Restriction `H^n_c(S) → H^n_c(S \ O)`. -/
def resC (n : ℕ) : HcSet Λ S F n →+ HcSet Λ (S \ (O : Set X)) F n :=
  ((hcSetEquiv F (wvSet_Z hS O) n).symm.toAddMonoidHom.comp (Hmap Λ (excComplex (cutOpen S) (le_sup_left : cutCompl S ≤ cutCompl S ⊔ O) F).g n)).comp
    (hcSetEquiv F (wvSet_cut hS) n).toAddMonoidHom

/-- **Excision (sets), exactness at `H^n_c(S)`.** -/
theorem extO_resC_exact (n : ℕ) : Function.Exact (extO F hS O n) (resC F hS O n) :=
  exact_conj (hcSetEquiv F (wvSet_U hS O) n) (hcSetEquiv F (wvSet_cut hS) n)
    (hcSetEquiv F (wvSet_Z hS O) n) (exc_exact₂ (cutOpen S) le_sup_left F n)

end SetExc

end RamanujanPetersson.EtCompact

end

end


