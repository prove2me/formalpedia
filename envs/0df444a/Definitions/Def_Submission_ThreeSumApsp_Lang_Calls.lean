-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
-- name    : Submission_ThreeSumApsp_Lang_Calls
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:32:36.332675+00:00
-- url     : https://prove2.me/theorems/80a6c4ff-d9ad-425d-9f37-36e9adf0ac7b
-- title:
--   Calls
-- statement:
--   Definitions and structural lemmas for Calls, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Calls.lean

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
set_option autoImplicit false
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
def Meets (lim : Limits) (P : Program) (p d : ℕ) (vals : List ℤ) (μ : ℕ → ℤ) (T : ℕ)
    (R : ℤ → (ℕ → ℤ) → Prop) : Prop :=
  ∃ body, P[p]? = some body ∧ Ends lim P d body ⟨frame vals, μ⟩ T fun σ' => R (σ'.loc 0) σ'.mem
section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}
end
section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}
end
end Light


