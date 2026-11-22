-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
-- name    : Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:12:38.17937+00:00
-- url     : https://prove2.me/theorems/1bd4491e-4589-48fd-bf2d-0c75c17423f9
-- title:
--   Walk Sharp
-- statement:
--   Definitions and structural lemmas for Walk Sharp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean

import Definitions.Def_Formalism_SubspaceCounting_Statement
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
namespace Formalism.G0
namespace WalkSharpP
section Ops
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ}
def lp (y : Fin V → Module.End R X) (l : List (Fin V)) (e : Fin V → ℕ) : Module.End R X :=
  (l.map fun u => y u ^ e u).prod
end Ops
def top {V : ℕ} (B : Finset (Fin V)) : ℕ := B.sup fun u => (u : ℕ)
def expo {V : ℕ} (m : ℕ) (B : Finset (Fin V)) (i : Fin V → ℕ) (u : Fin V) : ℕ :=
  if (u : ℕ) < top B ∧ u ∉ B then m else if u ∈ B then i u else 0
def accT {V : ℕ} (a b c : Fin V → ℕ) (m c₀ : ℕ) (B : Finset (Fin V)) (i : Fin V → ℕ)
    (u : Fin V) : ℕ :=
  if (u : ℕ) < top B ∧ u ∉ B then a u + b u + (m - 1) * c u + m * c₀
  else if u ∈ B then b u + i u * (c u + c₀) else 0
def acc {V : ℕ} (a b c : Fin V → ℕ) (m c₀ : ℕ) (B : Finset (Fin V)) (i : Fin V → ℕ) : ℕ :=
  ∑ u, accT a b c m c₀ B i u
def idx {V : ℕ} (m : ℕ) (B : Finset (Fin V)) : Finset (Fin V → ℕ) :=
  Fintype.piFinset fun u => if u ∈ B then Finset.range m else {0}
end WalkSharpP
end Formalism.G0


