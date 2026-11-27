-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC3_007
-- name    : RPLib_FX_EtPBCC3_007
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-27T06:04:15.349957+00:00
-- url     : https://prove2.me/theorems/ac8f2cd0-efa7-5d0e-ae66-0fd3fdd86b8b
-- title:
--   Compactly supported étale cohomology of affine space with Tate twists, library file 007
-- statement:
--   File 007 of the library for compactly supported étale cohomology of affine space with Tate twists: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology with compact supports of affine space over an algebraically closed field $K$ with Tate-twisted coefficients: for $\Lambda$ a finite ring with $\ell^m \Lambda = 0$ ($\ell$ invertible in $K$) and $\Lambda(k)$ the constant sheaf $(\Lambda \otimes \mu_{\ell^m})^{\otimes k}$, $H^q_c(\mathbb{A}^{n+1}_K, \Lambda(k)) = 0$ for $q \ne 2n+2$ and $H^{2n+2}_c(\mathbb{A}^{n+1}_K, \Lambda(n+1)) \cong \Lambda$ $\Lambda$-linearly, via $R^q \mathrm{pr}_!$ of the relative affine line and induction on the dimension. It builds on the proper base change libraries (`RPLib_FX_EtPBC_*`, `RPLib_FX_EtPBCB_*`, `RPLib_FX_EtPBCC1_*`, `RPLib_FX_EtPBCC2_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XVII (P. Deligne, cohomologie à supports propres) and Exposé XVIII, 2.9 (P. Deligne, morphisme trace), Lecture Notes in Math. 305, Springer (1973); P. Deligne, SGA 4 1/2, [Arcata], Lecture Notes in Math. 569 (1977); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC3_001

/-!
# Compactly supported étale cohomology of affine space with Tate twists, library file 007

Declarations of the formalization of compactly supported étale cohomology of affine space over an
algebraically closed field with Tate-twisted coefficients: H^q_c(A^(n+1), Λ(k)) = 0 for q ≠ 2n+2 and
H^(2n+2)_c(A^(n+1), Λ(n+1)) ≃ Λ, Λ-linearly, re-hosted declaration by declaration from the library
modules below, on top of the proper base change libraries RPLib_FX_EtPBC, RPLib_FX_EtPBCB,
RPLib_FX_EtPBCC1 and RPLib_FX_EtPBCC2. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
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

/-- **Excision, exactness at `H^n_c(Z)`**: `H^n_c(S) → H^n_c(Z) → H^(n+1)_c(U)`. -/
theorem exc_exact₃ (n : ℕ) :
    Function.Exact (Hmap Λ (excComplex W h F).g n) (excδ W h F n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.covariant_sequence_exact₃' (unitSh Λ X) (excComplex_shortExact W h F) n (n + 1) rfl)

end RamanujanPetersson.EtCompact

end

end


