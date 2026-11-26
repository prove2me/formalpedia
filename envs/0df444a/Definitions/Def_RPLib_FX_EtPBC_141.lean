-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_141
-- name    : RPLib_FX_EtPBC_141
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:00:57.822156+00:00
-- url     : https://prove2.me/theorems/3630293f-7372-5ab5-9123-7763c82e1b17
-- title:
--   Proper base change for the projective line, library file 141
-- statement:
--   File 141 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2D3`: S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_067
import Definitions.Def_RPLib_FX_EtPBC_131

/-!
# Proper base change for the projective line, library file 141

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2D3`: S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2D3 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`

* `A1.exists_closed_mem`: a nonzero `f ∈ k[X]` is a unit at some closed point (`k` infinite);
* `two_dies_A1`: the `k[X]` instance of `two_dies` (`k = k̄`, `ℓ ≠ char k`, `ℓ^m Λ = 0`);
* `chartEt k`: the chart `A¹ ⟶ P¹` as an étale object; `chart_dies`: `β ∈ Ext²(Λ_{P¹}, F)` dies on
  `chart ∘ D(f)` (restrict to the chart with `extFree`, apply `two_dies_A1`, come back with `restrict_eq_zero`);
* `U' k f := chart ''ᵁ D(f)`, `toU'`: `opEt (U' k f) ⟶ chart ∘ D(f)` (open immersion lift);
* **`claimD`**: every `β ∈ Ext²(Λ[P¹], F)` dies on the open `U' k f` of `P¹` for some `f ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.EtCompact.CurveHn

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ]

section GenDies

universe w₁ v₁ u₁

end GenDies

variable (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)

include hl hΛ

/-- `β` restricted to the chart dies on `D(f)` for some `f ≠ 0`. -/
theorem chart_dies_ex (F : EtSh Λ (P1 k)) (β : Ext (freeSh Λ (etId (P1 k))) F 2) :
    ∃ f : k[X], f ≠ 0 ∧ (Ext.mk₀ (freeMap Λ (toW (chartEt k) (opEt (bOpen f))))).comp
      ((Ext.mk₀ (freeMap Λ (toTop (chartEt k)))).comp β (zero_add 2)) (zero_add 2) = 0 := by
  obtain ⟨f, hf0, hf⟩ := two_dies_A1 k l hl m hΛ _ (extFree Λ (chartEt k) F 2
    ((Ext.mk₀ (freeMap Λ (toTop (chartEt k)))).comp β (zero_add 2)))
  exact ⟨f, hf0, restrict_eq_zero (chartEt k) (opEt (bOpen f)) F _ hf⟩

/-- `β` dies on `chart ∘ D(f)` for some `f ≠ 0`. -/
theorem chart_dies (F : EtSh Λ (P1 k)) (β : Ext (freeSh Λ (etId (P1 k))) F 2) :
    ∃ f : k[X], f ≠ 0 ∧
      (Ext.mk₀ (freeMap Λ (toTop ((etComp (chartEt k).hom).obj (opEt (bOpen f)))))).comp β (zero_add 2) = 0 := by
  obtain ⟨f, hf0, hf⟩ := chart_dies_ex k l hl m hΛ F β
  exact ⟨f, hf0, dies_gen β _ _ (chart_toTop_eq k f) hf⟩

end RamanujanPetersson.EtPBC.EtMV

end

end


