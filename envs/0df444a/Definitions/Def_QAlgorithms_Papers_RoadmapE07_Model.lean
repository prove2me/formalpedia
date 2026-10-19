-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapE07_Model
-- name    : QAlgorithms_Papers_RoadmapE07_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:30:58.981474+00:00
-- url     : https://prove2.me/theorems/18d724cd-f63c-4d67-a5b4-c4d8ad75eb5d
-- title:
--   Quantum Expander Codes: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Quantum Expander Codes, arXiv:1504.00822v1, https://arxiv.org/abs/1504.00822v1. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_ClassicalDecoderMachines
/-!
# Quantum Expander Codes: adversarial decoding

Leverrier, Tillich and Zemor, arXiv:1504.00822v1, Theorem 2, PDF p.6
(printed p.5); standing graph conventions on PDF p.4 and the algorithm on pp.7-8.
The self hypergraph product and exact syndrome are computed from the frozen graph definitions.
The local contracts below certify source-valid execution; they add no progress assumptions.
-/

namespace QAlgorithms.Papers.RoadmapE07

open QAlgorithms.ExpanderCodes

attribute [local instance] Classical.propDecidable

/-- A finite execution certificate for Section 3, arXiv:1504.00822v1, PDF pp.7-8.
Each flip belongs to the frozen set of strictly improving opposite-generator subsets.
The ratio comparison is cross-multiplied over positive flip cardinalities; natural
subtraction is used only for strictly decreasing syndrome weights. The source allows
arbitrary ties. The certificate records the choices made by a concrete deterministic machine,
without requiring it to compute the noncomputable enumeration in frozen `chooseFlip`.
The terminal syndrome has no improving flip; zero means success and otherwise failure. -/
def IsMaxRatioTrace {R Q : Type*} [Fintype R] [Fintype Q]
    (H : Matrix R Q (ZMod 2)) (gens : Finset (Finset Q))
    (s : R → ZMod 2) (out : Option (Q → ZMod 2)) : Prop :=
  ∃ (k : ℕ) (flips : Fin k → Finset Q) (states : Fin (k + 1) → R → ZMod 2),
    states 0 = s ∧
    (∀ i : Fin k,
      flips i ∈ improvingFlips H gens (states i.castSucc) ∧
      states i.succ = states i.castSucc + H.mulVec (flipVector (flips i)) ∧
      ∀ F ∈ improvingFlips H gens (states i.castSucc),
        (hammingNorm (states i.castSucc) -
          hammingNorm (states i.castSucc + H.mulVec (flipVector F))) * (flips i).card ≤
        (hammingNorm (states i.castSucc) - hammingNorm (states i.succ)) * F.card) ∧
    improvingFlips H gens (states (Fin.last k)) = ∅ ∧
    out = if states (Fin.last k) = 0 then some (∑ i, flipVector (flips i)) else none

/-- Realization certificate for the two independent decoding procedures, Section 3,
arXiv:1504.00822v1, PDF pp.7-8. Partial successes are kept separately before combining
outputs: if either component fails, the pair decoder fails. Generator supports are matrix
rows, so Equation (6)'s mixed coordinate names are corrected by Equation (1) and PDF p.5's
incidence rules: the HX support is {alpha a : a adjacent beta} union
{b beta : alpha adjacent b}, not the printed {a beta} union {alpha b}. -/
def IsDecoderTrace {nA nB : ℕ} (G : BipartiteData nA nB)
    (s : ((Fin nA × Fin nB) → ZMod 2) × ((Fin nB × Fin nA) → ZMod 2))
    (out : Option (Error ((Fin nA × Fin nA) ⊕ (Fin nB × Fin nB)))) : Prop :=
  ∃ outX outZ,
    IsMaxRatioTrace (checks G).1 (generatorSupports (checks G).2) s.1 outX ∧
    IsMaxRatioTrace (checks G).2 (generatorSupports (checks G).1) s.2 outZ ∧
    out = outX.bind (fun x => outZ.map (fun z => (x, z)))

/- Definition sanity check: zero syndrome terminates with zero correction. -/
example {R Q : Type*} [Fintype R] [Fintype Q]
    (H : Matrix R Q (ZMod 2)) (gens : Finset (Finset Q)) :
    IsMaxRatioTrace H gens 0 (some 0) := by
  refine ⟨0, Fin.elim0, fun _ => 0, rfl, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · simp [improvingFlips]
  · simp


end QAlgorithms.Papers.RoadmapE07


