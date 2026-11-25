-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:53:11.30043+00:00
-- url     : https://prove2.me/theorems/f968363e-76d3-41cd-a55b-312e569e17b7
-- title:
--   Row Tie Mem CInv
-- statement:
--   Definitions and structural lemmas for Row Tie Mem CInv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCInv.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
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
variable {N N' : ℕ} (Φ : MvPolynomial (Fin N × Fin N') C →ₐ[C] MvPolynomial (Letter T r n) C) (σ0 : T)
  (w : Fin N → Fin 2 → C) (lt : Fin N × Fin N' → Fin 2 → Letter T r n) (colf : Fin N → Fin 2 → Fin n)
end Atom
section Fam
variable {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
  {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N} {n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
def trueT (g : Fin 2) (s : ZMod 2) : ZMod 2 := if g = 0 then s else s + 1
variable (r tau gm) in

def PsiS (o : Orb) {M : ℕ} (col : Fin M → Fin N) :
    MvPolynomial (Fin M × WV fun _ => IIs r tau o) C →ₐ[C] MvPolynomial (Letter T r n) C :=
  (subG r tau gm plc).comp (rename fun x : Fin M × WV fun _ => IIs r tau o =>
    ((col x.1, (⟨o, x.2⟩ : WVO fun o (_ : Fin 2) => IIs r tau o))))
end Fam
end Formalism.L2.FormalSeriesBounds.RF


