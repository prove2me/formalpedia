-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
-- name    : QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T13:28:03.532443+00:00
-- url     : https://prove2.me/theorems/327c4d47-38be-4cf2-a8cc-d1bd339dcce1
-- title:
--   XLocal Grid Parity
-- statement:
--   Definitions and structural lemmas for XLocal Grid Parity, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalGridParity.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
set_option autoImplicit false
namespace QEC.Coding.BDL26XLocalGridParity
open BDL26TannerLocalRegularity
open BDL26FiniteAlternatingCore
abbrev StripVertex (m : ℕ) := Fin m
abbrev StripEdge (m : ℕ) := Fin (m - 1)
def stripStart (m : ℕ) (e : StripEdge m) : StripVertex m :=
  ⟨e.val, by have := e.isLt; omega⟩
def stripEnd (m : ℕ) (e : StripEdge m) : StripVertex m :=
  ⟨e.val + 1, by have := e.isLt; omega⟩
def stripPrefix (m : ℕ) (hm : 0 < m) :
    (k : ℕ) → (hk : k < m) →
      UndirectedPath (stripStart m) (stripEnd m) ⟨0, hm⟩ ⟨k, hk⟩
  | 0, _ => .nil
  | k + 1, hk => by
      exact .step (stripPrefix m hm k (by omega))
        ⟨k, by omega⟩ (Or.inl ⟨rfl, rfl⟩)
noncomputable def stripPath (m : ℕ) (hm : 0 < m)
    (root target : StripVertex m) :
    UndirectedPath (stripStart m) (stripEnd m) root target :=
  (stripPrefix m hm root.val root.isLt).reverse.append
    (stripPrefix m hm target.val target.isLt)
abbrev GridVertex (m : ℕ) := Fin m × Fin m
abbrev GridEdge (m : ℕ) :=
  (Fin (m - 1) × Fin m) ⊕ (Fin m × Fin (m - 1))
def gridStart (m : ℕ) : GridEdge m → GridVertex m
  | .inl e => (stripStart m e.1, e.2)
  | .inr e => (e.1, stripStart m e.2)
def gridEnd (m : ℕ) : GridEdge m → GridVertex m
  | .inl e => (stripEnd m e.1, e.2)
  | .inr e => (e.1, stripEnd m e.2)
noncomputable def gridPath (m : ℕ) (hm : 0 < m)
    (root target : GridVertex m) :
    UndirectedPath (gridStart m) (gridEnd m) root target := by
  have row : UndirectedPath (gridStart m) (gridEnd m)
      root (target.1, root.2) :=
    UndirectedPath.map (edgeStart := stripStart m) (edgeEnd := stripEnd m)
      (edgeStart' := gridStart m) (edgeEnd' := gridEnd m) (fun i => (i, root.2))
      (fun i => Sum.inl (i, root.2)) (fun _ => rfl) (fun _ => rfl)
      (stripPath m hm root.1 target.1)
  have column : UndirectedPath (gridStart m) (gridEnd m)
      (target.1, root.2) target :=
    UndirectedPath.map (edgeStart := stripStart m) (edgeEnd := stripEnd m)
      (edgeStart' := gridStart m) (edgeEnd' := gridEnd m) (fun j => (target.1, j))
      (fun j => Sum.inr (target.1, j)) (fun _ => rfl) (fun _ => rfl)
      (stripPath m hm root.2 target.2)
  exact row.append column
end QEC.Coding.BDL26XLocalGridParity


