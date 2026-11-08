-- Prove2me | Definitions.Def_AvoidPlast_Machine
-- name    : AvoidPlast_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:55.567961+00:00
-- url     : https://prove2.me/theorems/91d7e2d5-ae7d-4c71-9880-2eb82cc6f131
-- title:
--   The machine model
-- statement:
--   A deterministic multitape machine with $r$ read-only input tapes: finitely many states with a start state, halting states and an accept flag; $w+r$ work tapes over the fixed alphabet $\{\sqcup,0,1\}$, where tape $w+j$ is the *index tape* of read-only tape $j$; and a write-only output tape. One step reads the state, the scanned work symbols and the symbol under every read-only head, and returns a new state, a symbol and a move for each work tape, a move or a jump for each read-only head, and optionally one output bit.
--
--   Every class of the mission is a predicate on this one model: polynomial time, space-bounded computation, promise classes with persistent randomness, PCP and PCPP verifiers.
--
--   **Formalization Note** The paper works in "the RAM model" without fixing one (reading R5). The read-only tapes and the output tape never count as work space; the index tapes do. The module also gives machines a fixed computable `Encodable` code, used for machine descriptions.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, machine model, p.13

import Mathlib
import Definitions.Def_AvoidPlast_Move
import Definitions.Def_AvoidPlast_HeadAct

namespace AvoidPlast

/-- A deterministic multitape machine with `r` read-only input tapes (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.13: "The machine
model throughout the paper is the RAM model").

* States are `Fin (q + 1)`; the start state is `0`. `halting` marks the halting states and
  `accepting` the accept flag read off a halting state (for deciders).
* There are `w + r` work tapes over the alphabet {blank, 0, 1} (`Option Bool`, `none` = blank).
  Work tape `w + j` is the *index tape* of read-only tape `j`.
* One step reads the state, the scanned symbol of every work tape, and the symbol under every
  read-only head (`none` when the head is past the end of the input string). It returns the new
  state, for every work tape a symbol to write and a move, for every read-only head a
  `HeadAct` (a move, or a jump to the number written on its index tape), and optionally one bit
  appended to the write-only output tape.

**Formalization Note** Machine model (reading R5): the paper does not fix a RAM model; read-only
tapes with index jumps are a standard random-access Turing machine. Work space counts the visited
work cells (index tapes included); the read-only inputs and the write-only output are never work
space (see `workSpace`). The work alphabet is fixed to {blank, 0, 1}. -/
structure Machine (r : ℕ) where
  /-- states are `Fin (q + 1)`, start state `0` -/
  q : ℕ
  /-- number of ordinary work tapes; tapes `w, …, w + r - 1` are the index tapes -/
  w : ℕ
  /-- halting states -/
  halting : Fin (q + 1) → Bool
  /-- accept flag of a state (read at halting) -/
  accepting : Fin (q + 1) → Bool
  /-- the transition function -/
  δ : Fin (q + 1) → (Fin (w + r) → Option Bool) → (Fin r → Option Bool) →
      Fin (q + 1) × (Fin (w + r) → Option Bool × Move) × (Fin r → HeadAct) × Option Bool

namespace Machine

/-- The fixed bijection {blank, 0, 1} ≃ `Fin 3` used by the description code. -/
def symEquiv : Option Bool ≃ Fin 3 where
  toFun
    | none => 0
    | some false => 1
    | some true => 2
  invFun := ![none, some false, some true]
  left_inv := by intro o; rcases o with _ | _ | _ <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- Functions of a tuple of tape symbols are encodable, through the base-3 code of the tuple. -/
instance encodableSymArrow {k : ℕ} {β : Type} [Encodable β] :
    Encodable ((Fin k → Option Bool) → β) :=
  Encodable.ofEquiv (Fin (3 ^ k) → β)
    ((Equiv.arrowCongr (Equiv.arrowCongr (Equiv.refl _) symEquiv) (Equiv.refl β)).trans
      (Equiv.arrowCongr finFunctionFinEquiv (Equiv.refl β)))

/-- The underlying data of a machine, as a sigma type. -/
def equivSigma (r : ℕ) : Machine r ≃ Σ p : ℕ × ℕ, (Fin (p.1 + 1) → Bool) × (Fin (p.1 + 1) → Bool) ×
    (Fin (p.1 + 1) → (Fin (p.2 + r) → Option Bool) → (Fin r → Option Bool) →
      Fin (p.1 + 1) × (Fin (p.2 + r) → Option Bool × Move) × (Fin r → HeadAct) × Option Bool) where
  toFun M := ⟨(M.q, M.w), M.halting, M.accepting, M.δ⟩
  invFun s := ⟨s.1.1, s.1.2, s.2.1, s.2.2.1, s.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Machines are encodable (a fixed computable code, used for the descriptions of `U`). -/
instance encodable (r : ℕ) : Encodable (Machine r) :=
  Encodable.ofEquiv _ (equivSigma r)

end Machine

end AvoidPlast


