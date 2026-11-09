-- Prove2me | Definitions.Def_AgnosticTNS_encTTN
-- name    : AgnosticTNS_encTTN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:41.820944+00:00
-- url     : https://prove2.me/theorems/55a3e17f-34b5-4713-9481-65dd9836ae6d
-- title:
--   Binary description of a TTN
-- statement:
--   The output description of the learners: the number of nodes, the parent of every node, the node of every qudit, the bond dimensions (all in self-delimiting binary), then all tensor entries as Gaussian rationals, in a fixed enumeration of each tensor's index set.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Proposition 3.8, p.24; Proposition 3.10, p.26

import Mathlib
import Definitions.Def_AgnosticTNS_TTN
import Definitions.Def_AgnosticTNS_encC
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
open QAlgorithms.LocalHamiltonian

namespace AgnosticTNS

/-- **The binary description of a TTN**, the output format of the learners (Proposition 3.8,
p.24; Proposition 3.10, p.26) (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): the node count `m`, the parent of every node (`0` for the
root, `k + 1` for parent `k`), the node of every qudit, the bond dimensions, then every tensor entry
as a Gaussian rational, all numbers in the published self-delimiting binary code `encBin`.

**Formalization Note** The entries of the tensor at node `k` are listed in the order of the fixed
enumeration `Fintype.equivFin` of its index type. -/
noncomputable def encTTN {n d : ℕ} (D : Σ m, TTN m n d) : QAlgorithms.Complexity.Str :=
  encBin D.1 ++
  ((List.finRange D.1).map fun k =>
    match D.2.parent k with
    | none => encBin 0
    | some k' => encBin (k'.val + 1)).flatten ++
  ((List.finRange n).map fun v => encBin (D.2.site v).val).flatten ++
  ((List.finRange D.1).map fun k => encBin (D.2.bond k)).flatten ++
  ((List.finRange D.1).map fun k =>
    ((List.finRange (Fintype.card (({v // D.2.site v = k} → Fin d) × Fin (D.2.bond k) ×
        ((c : {c // D.2.parent c = some k}) → Fin (D.2.bond c.1))))).map fun t =>
      let a := (Fintype.equivFin _).symm t
      encC (D.2.tensor k a.1 a.2.1 a.2.2)).flatten).flatten

end AgnosticTNS


