-- Prove2me | Definitions.Def_FasterDistributedMatching_ApproximateMatching_StageData
-- name    : FasterDistributedMatching_ApproximateMatching_StageData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:11:03.812962+00:00
-- url     : https://prove2.me/theorems/c8b8a909-9fca-446d-8080-6cb4bfad7482
-- title:
--   Permitted physical inputs for virtual rounding stages
-- statement:
--   Each physical processor receives its neighbor identifiers and incident edge values, its own list of paired active-edge groups, and, when supplied, its own copies' block-leader names, colors, cut marks and bipartition bit. Remote blocks, routes and the complete network are not initial inputs. A block output names the leader of each local copy's block; a cut output marks the selected local copies.
--
--   $$a\ne b,\quad \operatorname{dist}_G(\operatorname{creator}(a),\operatorname{creator}(b))\le256\ell
--   \quad\Longrightarrow\quad \chi(a)\ne\chi(b)$$
--
--   specifies reusable colors, including distinct copies at the same creator. All colors lie in the supplied palette. Missing optional data have fixed empty defaults.
--
--   These records connect the virtual combinatorial objects to physical LOCAL execution, charging all communication between creators to actual network rounds.
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), §§3.1–3.3, printed pp.8–12, PDF pp.10–14; Appendix A, printed p.22, PDF p.24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Virtual

namespace FasterDistributedMatching.ApproximateMatching

/-! LOCAL inputs for the virtual construction. Each physical node receives its own groups,
local colors, leader names and cut marks. No graph carrier index or remote block is exposed. -/
abbrev Key := ℕ × ℕ
structure StageParameters extends Bounds where
  ell : ℕ
  zeta : ℕ
  q : ℝ

structure StageInput where
  neighbors : Finset ℕ
  edgeValue : ℕ → ℝ
  groups : List (Finset ℕ)
  leader : ℕ → Option Key
  color : ℕ → ℕ
  cut : ℕ → Bool
  side : Option Bool

open Classical in
noncomputable def stageInput {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (x : Sym2 (Fin N) → ℝ) (p : Pairing N) (B : Option (BlockAssignment p))
    (col : Option (Copy p → ℕ)) (cut : Copy p → Bool) (side : Fin N → Option Bool)
    (v : Fin N) : StageInput where
  neighbors := neighborIDs G ids v
  edgeValue := (weightInput G ids x v).2
  groups := (p v).map (Finset.image ids)
  leader := fun i => if h : i < (p v).length then
    (B.bind fun f => (f ⟨v, ⟨i,h⟩⟩).map (copyKey ids)) else none
  color := fun i => if h : i < (p v).length then
    (col.map fun f => f ⟨v, ⟨i,h⟩⟩).getD 0 else 0
  cut := fun i => if h : i < (p v).length then cut ⟨v, ⟨i,h⟩⟩ else false
  side := side v

/- Copy-output naming the leader of each block. -/
def ReportsBlocks {N : ℕ} {p : Pairing N} (ids : Fin N → ℕ)
    (out : Fin N → ℕ → Option Key) (B : BlockAssignment p) : Prop :=
  ∀ a, out a.1 a.2.val = (B a).map (copyKey ids)

/- The output bit at each copy says whether that copy was selected. -/
def ReportsCuts {N : ℕ} {p : Pairing N} (out : Fin N → ℕ → Bool)
    (B : BlockAssignment p) (s : Copy p → Copy p) : Prop :=
  ∀ a, out a.1 a.2.val = true ↔ ∃ b, B b = some b ∧ s b = a

open Classical in
noncomputable def cutMarks {N : ℕ} {p : Pairing N} (B : BlockAssignment p)
    (s : Copy p → Copy p) (a : Copy p) : Bool :=
  decide (∃ b, B b = some b ∧ s b = a)

/- Published reusable colors distinguish even different copies at a common creator. -/
def ReusableColors {N : ℕ} (G : SimpleGraph (Fin N)) {p : Pairing N}
    (ell zeta : ℕ) (col : Copy p → ℕ) : Prop :=
  (∀ a, col a < zeta) ∧ ∀ a b, a ≠ b → Close G (256 * ell) a.1 b.1 → col a ≠ col b

end FasterDistributedMatching.ApproximateMatching


