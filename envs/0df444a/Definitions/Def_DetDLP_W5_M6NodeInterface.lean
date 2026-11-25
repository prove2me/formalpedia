-- Prove2me | Definitions.Def_DetDLP_W5_M6NodeInterface
-- name    : DetDLP_W5_M6NodeInterface
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T00:23:39.031809+00:00
-- url     : https://prove2.me/theorems/7ca404bd-6518-4f8d-ae2b-5d858dfa1271
-- title:
--   M6 Node Interface
-- statement:
--   A normalized divisor-node service uses four distinct tape ports for the current word, right child, pending stack and emitted leaves. A service call preserves the last two ports, restores a blank work area, and bounds both the step count and the increase in visited cells.

import Definitions.Def_DetDLP_M89_MachineComp

set_option autoImplicit false
namespace DetDLP.w5_M6RecursiveDriver
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP.MachineComposition

abbrev BitTape := Turing.Tape (Option Bool)
def dataTape (bits : List Bool) : BitTape := Turing.Tape.mk₁ (bits.map some)

/-- Four physical ports: current node, right child, suspended nodes, output leaves. -/
structure Ports (t : ℕ) where
  get : Fin 4 → Fin t
  inj : Function.Injective get

/-- Canonical physical layout at node boundaries. Work tapes other than the four
ports are genuinely blank. The monitor is independent of this layout. -/
def layout {t : ℕ} (p : Ports t) (words : Fin 4 → List Bool) (i : Fin t) : BitTape :=
  if i = p.get 0 then dataTape (words 0) else if i = p.get 1 then dataTape (words 1)
  else if i = p.get 2 then dataTape (words 2) else if i = p.get 3 then dataTape (words 3)
  else dataTape []

abbrev words (a b c d : List Bool) : Fin 4 → List Bool := ![a,b,c,d]

/-- The only service assumed by the DFS controller is ONE normalized node
operation, on the actual submachine. This is not implied merely by knowing
which word was left on the divisor-output tape. -/
def NodeService (A : PrimitiveMachine) (p : Ports A.tapeCount) (f : ℕ → ℕ)
    (τ σ : ℕ → ℝ) : Prop :=
  ∀ (x : ℕ), 2 ≤ x → ∀ (pending leaves : List Bool) (a : LocatedCfg A),
    a.config.tapes = layout p (words (countWord x) [] pending leaves) →
    LocatedWellFormed a → ∃ (m : ℕ) (b : LocatedCfg A),
      Computation.Trace (locatedStep A) m (cyclicStartSub A a) b ∧
      (∃ answer, b.config.state = .inl answer) ∧
      b.config.tapes = (if 2 ≤ f x ∧ f x < x ∧ f x ∣ x
        then layout p (words (countWord (f x)) (countWord (x / f x)) pending leaves)
        else layout p (words (countWord x) [] pending leaves)) ∧
      (m : ℝ) ≤ τ x ∧ (visitedSpace b : ℝ) ≤ (visitedSpace a : ℝ) + σ x

end DetDLP.w5_M6RecursiveDriver


