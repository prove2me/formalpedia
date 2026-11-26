-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_221
-- name    : RPLib_FX_EtPBC_221
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T04:15:21.813973+00:00
-- url     : https://prove2.me/theorems/a0c594a0-c378-5a43-8d9a-e9535b46340c
-- title:
--   Proper base change for the projective line, library file 221
-- statement:
--   File 221 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2L8b`: S4-EtPBC-A, O2 L8b: `TrG` is onto and natural; `BCSurj 2` for `FGT` sheaves; killing degree-1 classes
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_220

/-!
# Proper base change for the projective line, library file 221

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2L8b`: S4-EtPBC-A, O2 L8b: `TrG` is onto and natural; `BCSurj 2` for `FGT` sheaves; killing degree-1 classes
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2L8b =====
section

/-!
# S4-EtPBC-A, O2 L8b: `TrG` is onto and natural; `BCSurj 2` for `FGT` sheaves; killing degree-1 classes
* `TrG_surjective`, **`TrG_natural`** (`TrG G (x ∘ ιP^*m) = TrG H x ∘ ι^*m`);
* **`bcSurj_two_fgt`**: `BCSurj 2` for every `FGT` sheaf on `P¹_S` (`surjAt_coprod`, `bcSurj_two_free`, `bcSurj_two_of_epi`);
* `NT`, **`kill_lift`**: for `T` affine over `P¹_K`, every `κ ∈ Ext¹(Λ[T], ιP^*G)` is `κH ∘ ιP^*m` with `m : H ⟶ G`,
  `H` an `FGT` sheaf (`exists_kill` on `T`, `extFree_comp_mk₀`, the covariant exact sequence).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE
  RamanujanPetersson.EtCompact.PushBC

universe u

section GenSurjG

universe w v₁ u₁ v₂ u₂

end GenSurjG

section TrG

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]

/-- **`BCSurj 2` for every `FGT` sheaf on `P¹_S`.** -/
theorem bcSurj_two_fgt (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0) (m : ℕ) [NeZero (l ^ m)]
    (hN : ((l ^ m : ℕ) : K) ≠ 0) (hΛ : ∀ x : Λ, (l ^ m) • x = 0) (H : EtSh Λ (PV K gS)) (hH : FGT Λ H) :
    BCSurj Λ (qV K gS) s 2 H := by
  obtain ⟨t, ht, W, hW, e, he⟩ := hH
  have hΛ' : ((l ^ m : ℕ) : Λ) = 0 := (nsmul_one (l ^ m)).symm.trans (hΛ 1)
  have h1 : BCSurj Λ (qV K gS) s 2 (∐ fun j => freeSh Λ (W j)) :=
    Delta.surjAt_coprod (bcUnit_comp Λ (qV K gS) s) 2 _ fun j => by
      have := hW j
      exact bcSurj_two_free gS s Λ l hl m hN hΛ (W j)
  exact bcSurj_two_of_epi K l hl m hΛ' gS s e h1

end TrG

end RamanujanPetersson.EtPBC.EtMV

end

end


