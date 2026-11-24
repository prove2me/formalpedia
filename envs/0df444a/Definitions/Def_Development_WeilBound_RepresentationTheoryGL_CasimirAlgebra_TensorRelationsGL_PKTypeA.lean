-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:54.681525+00:00
-- url     : https://prove2.me/theorems/992a7f1d-e584-4673-96d0-1a22699e0377
-- title:
--   PKType A
-- statement:
--   Definitions and structural lemmas for PKType A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
namespace PositivityTheory.Rg.Cz
namespace KTy
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
abbrev Bx (nu : ι → Fin n → ℕ) : Type := Σ τ : ι, Σ i : Fin n, Fin (nu τ i)
abbrev Pr (H : Finset ι) (n : ℕ) : Type := Σ _ : H, Σ i : Fin n, Fin i.val
def eB (nu : ι → Fin n → ℕ) : Fin (Fintype.card (Bx nu)) ≃ Bx nu := (Fintype.equivFin _).symm
def eP (H : Finset ι) (n : ℕ) : Fin (Fintype.card (Pr H n)) ≃ Pr H n := (Fintype.equivFin _).symm
section
variable (nu : ι → Fin n → ℕ) (H : Finset ι)
def labQ (p : Fin (Fintype.card (Bx nu))) : ι := (eB nu p).1
def bQ (p : Fin (Fintype.card (Bx nu))) : Fin n := (eB nu p).2.1
def colQ (p : Fin (Fintype.card (Bx nu))) : ℕ := Nat.pair (Fintype.equivFin ι (eB nu p).1) (eB nu p).2.2
def tl (k : Fin (Fintype.card (Pr H n))) : ι := (eP H n k).1
def rI (k : Fin (Fintype.card (Pr H n))) : Fin n := (eP H n k).2.1
def cI (k : Fin (Fintype.card (Pr H n))) : Fin n :=
  ⟨(eP H n k).2.2, lt_trans (eP H n k).2.2.isLt (eP H n k).2.1.isLt⟩
abbrev Pos : Type := Fin (Fintype.card (Bx nu)) ⊕ (Fin (Fintype.card (Pr H n)) ⊕ Fin (Fintype.card (Pr H n)))
abbrev Col (ι : Type) (n : ℕ) : Type := ℕ ⊕ ((ι × Fin n) ⊕ (ι × Fin n))
def colF : Pos nu H → Col ι n
  | .inl p => .inl (colQ nu p)
  | .inr (.inl k) => .inr (.inl (tl H k, cI H k))
  | .inr (.inr k) => .inr (.inr (tl H k, rI H k))
def bF : Pos nu H → Fin n
  | .inl p => bQ nu p
  | .inr (.inl k) => rI H k
  | .inr (.inr k) => Fin.rev (cI H k)
end
end KTy
end PositivityTheory.Rg.Cz
end


