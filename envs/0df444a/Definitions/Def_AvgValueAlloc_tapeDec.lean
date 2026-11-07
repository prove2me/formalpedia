-- Prove2me | Definitions.Def_AvgValueAlloc_tapeDec
-- name    : AvgValueAlloc_tapeDec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:31.881314+00:00
-- url     : https://prove2.me/theorems/4b32ad76-1fde-4e50-891d-084818ed4eb2
-- title:
--   Decisions of a polynomial-time randomized learner
-- statement:
--   Let $\mathrm{alg}$ be a deterministic map from an observation and a string of coin bits to an output code, and $p$ a polynomial. The learner decides live item $t$ by running $\mathrm{alg}$ on its observation $x_t$ and the first $p(|\mathrm{enc}(x_t)|)$ bits of one fair coin tape $\omega$; output $0$ (or an out-of-range code) rejects and $k+1$ assigns buyer $k$.
--
--   This is the learner class of Theorem 1.1: one physical execution with consistent randomness, causal by construction, using polynomially many coins in what it has observed.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), Theorem 1.1, p.3; Appendix A.2, p.14

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_LearnerInput
import Definitions.Def_AvgValueAlloc_encIn

namespace AvgValueAlloc

/-- A vector as the list of its rational coordinates. -/
def vecList {n : ℕ} (v : Vec n) : List ℚ := List.ofFn fun j => (v j : ℚ)

/-- The observation at a live position. -/
def tapeInput {n S : ℕ} (ρ : Fin n → ℚ) (T : ℕ) (hist : Fin S → Vec n) (past : List (Vec n))
    (cur : Vec n) : LearnerInput :=
  ⟨List.ofFn ρ, T, S, List.ofFn fun s => vecList (hist s), past.map vecList, vecList cur⟩

/-- The output code: `0` rejects, `k + 1` assigns buyer `k`, and an out-of-range code rejects. -/
def toBuyer (n k : ℕ) : Option (Fin n) :=
  if h : 1 ≤ k ∧ k - 1 < n then some ⟨k - 1, h.2⟩ else none

/-- **The decisions of a polynomial-time randomized learner given by a deterministic map.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), Theorem 1.1, p.3: "One randomized polynomial-time
learner"; Appendix A.2, p.14: "Two fair bits choose the branch … Precision is polynomial in the full
observed encoding".

For a map `alg` from an observation and coin bits to an output code, and a polynomial `p`, the
learner's decision at live position `t` is `alg` applied to the observation `x_t` (thresholds,
`T`, `S`, history, past live vectors, current vector) and the first `p(|encInput x_t|)` bits of
one fair coin tape `ω`, read through `toBuyer`.

**Formalization Note.** The decision at `t` sees only the past and current live vectors (causal
by construction). All positions read prefixes of the same tape, so one physical execution with
consistent randomness is modeled; the number of coins read is polynomial in what has been
observed. -/
def tapeDec {n : ℕ} (alg : LearnerInput × List Bool → ℕ) (p : Polynomial ℕ) (ρ : Fin n → ℚ)
    (T S : ℕ) (hist : Fin S → Vec n) (vs : Fin T → Vec n) (ω : ℕ → Bool) :
    Fin T → Option (Fin n) :=
  fun t =>
    let x := tapeInput ρ T hist (List.ofFn fun s : Fin t.val => vs ⟨s.val, lt_trans s.isLt t.isLt⟩)
      (vs t)
    toBuyer n (alg (x, List.ofFn fun i : Fin (p.eval (encInput x).length) => ω i.val))

end AvgValueAlloc


