-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
-- name    : Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:52.518158+00:00
-- url     : https://prove2.me/theorems/82c1b1eb-5cda-424b-9fb8-d3184a0ebc70
-- title:
--   Norm One Row Invariant
-- statement:
--   Definitions and structural lemmas for Norm One Row Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowInvariant.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
section Atom
variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]
def keyL (ℓ : Letter T r n) : T × ℕ × Fin n := (ℓ.1, ℓ.2.1.val, ℓ.2.2)
end Atom
section Fam
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → Fin 2 → ZMod d → T} {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (IIof r tau o) (J o)} {F : ∀ o, Flag (X o)} {Z : Finset Orb}
  {ga : Orb → Fin 2 → ZMod d → ℕ → ℕ} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n}
def psiL (r : T → ℕ) (tau : Orb → Fin 2 → ZMod d → T) (n : ℕ) (o : Orb) {N : ℕ} (col : Fin N → Fin n)
    (x : Fin N × WV (IIof r tau o)) : Letter T r n := phiL r tau n (col x.1, ⟨o, x.2⟩)
end Fam
end Formalism.L2.FormalSeriesBounds.RF


