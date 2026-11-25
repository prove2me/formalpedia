-- Prove2me | Definitions.Def_RPLib_FX_EtHc_04
-- name    : RPLib_FX_EtHc_04
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:27:44.164984+00:00
-- url     : https://prove2.me/theorems/746c3858-c74f-512f-b0dc-a27fa3c1b18f
-- title:
--   Compactly supported étale cohomology of the affine line, extension file 04 of 11
-- statement:
--   Extension file 04 of 11 for the compactly supported cohomology of the affine line, stacked on the projective-line library files it imports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
--   * `S4.Def_RP_EtCompact_P1Exc`: S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)
--
--   **Formalization note.** Extension of the `RPLib_FX_EtP1` library (étale cohomology of the projective line) to the compactly supported cohomology of the affine line $\mathbf A^1_k = D_+(X_0) \subseteq \mathbf P^1_k$ over an algebraically closed field $k$, with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): the cut sheaves $F_S$ for locally closed $S$, the excision sequence $0 \to F_{S \cap O} \to F_S \to F_{S \setminus O} \to 0$ and its long exact sequence, the vanishing of the higher cohomology of a separably closed point, and the resulting comparison $H^n_c(\mathbf A^1, \Lambda) \to H^n(\mathbf P^1, \Lambda)$ (injective for $n = 1$, bijective for $n \ge 2$) with $H^0_c(\mathbf A^1, \Lambda) = 0$. The declarations of each library module are re-hosted verbatim, except that the three excision exactness proofs `exc_exact₁/₂/₃` are re-proved element-wise (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter II, §3 (extension by zero) and Chapter VI, §1-§3 (cohomology of curves, cohomology with compact support); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapters IV-V

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_41
import Definitions.Def_RPLib_FX_EtHc_02
import Definitions.Def_RPLib_FX_EtHc_03

/-!
# Compactly supported étale cohomology of the affine line, extension file 04 of 11

Declarations of the formalization of the compactly supported étale cohomology of the affine line
`A¹ = D₊(X₀) ⊆ P¹` over an algebraically closed field (the excision sequence for `j_! Λ ⊆ Λ ↠ i_* Λ`
and its consequences), stacked on the `RPLib_FX_EtP1` files it imports and re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim (except that the excision exactness proofs
`exc_exact₁/₂/₃` are re-proved element-wise, which the kernel checks faster) with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
* `S4.Def_RP_EtCompact_P1Exc`: S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)
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
    Function.Exact (Hmap Λ (excComplex W h F).g n) (excδ W h F n) := by
  -- element-wise (`Ext.covariant_sequence_exact₃`): the `AddCommGrpCat` form costs the kernel ~2x more
  intro y
  constructor
  · intro hy
    exact Ext.covariant_sequence_exact₃ (unitSh Λ X) (excComplex_shortExact W h F) y rfl hy
  · rintro ⟨x, rfl⟩
    change (x.comp (Ext.mk₀ (excComplex W h F).g) (add_zero n)).comp
      (excComplex_shortExact W h F).extClass rfl = 0
    rw [Ext.comp_assoc_of_second_deg_zero, (excComplex_shortExact W h F).comp_extClass, Ext.comp_zero]

end RamanujanPetersson.EtCompact


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

/-- **`cut (range i) F ≅ i_* i^* F`** for a closed immersion `i`. -/
def cutRangeIso (F : EtSh Λ X) : cut Λ (Set.range i) F ≅ (push i Λ).obj ((pull i Λ).obj F) :=
  haveI := (cut_exact Λ i F).epi_g
  cutClosedIso i.isClosedEmbedding.isClosed_range F ≪≫ eqToIso (congrArg (fun V => quotCut Λ V F) (cutCompl_range i)) ≪≫
    IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (cutComplex Λ i (complOpens i).ι (disjoint_complOpens i) F).f)
      (cut_exact Λ i F).exact.gIsCokernel

end Closed

end General

section Point

variable {Y : Scheme.{u}} (y : Y)

variable (Λ : Type u) [CommRing Λ]

/-- **`H^(n+1)(Spec κ(y), G) = 0`** for algebraically closed `κ(y)`. -/
theorem H_ptOf_eq_zero [IsAlgClosed (Y.residueField y)] (G : EtSh Λ (Spec (Y.residueField y))) (n : ℕ)
    (e : H Λ G (n + 1)) : e = 0 :=
  have := gal_subsingleton (ptOf y)
  H_eq_zero_of_point (ptOf y) Λ G n e

end Point

section P1

variable (K : Type u) [Field K] [IsAlgClosed K] (Λ : Type u) [CommRing Λ]

end P1

end RamanujanPetersson.EtCompact

end

end


