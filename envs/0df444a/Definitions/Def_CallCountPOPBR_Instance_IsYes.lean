-- Prove2me | Definitions.Def_CallCountPOPBR_Instance_IsYes
-- name    : CallCountPOPBR_Instance_IsYes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:06:17.886716+00:00
-- url     : https://prove2.me/theorems/eb60b276-5178-43f0-af95-b964b27184e5
-- title:
--   Yes-instance of POPBR
-- statement:
--   A POPBR instance is a **yes-instance** when it is well formed and there exist an admissible rule $(a_r,b_r)_{r<p}$ and a completion $C_0,\dots,C_N$ of the instance under that rule.
--
--   POPBR asks to decide this existence question.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), Definition 2.1, p.4

import Definitions.Def_CallCountPOPBR_Instance_IsValid
import Definitions.Def_CallCountPOPBR_IsAdmissibleRule
import Definitions.Def_CallCountPOPBR_IsCompletion

set_option autoImplicit false

namespace CallCountPOPBR

/-- **Yes-instance of POPBR** (Definition 2.1). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Definition 2.1, p.4: "We seek a
sequence C_0, …, C_N and unordered pairs (a_r, b_r) for r ∈ {0, …, p − 1} such that (2), (3) …
where 1 ≤ a_r ≤ b_r ≤ d, and C_n = Obs(n) at every observed index n. The task is to decide
existence".

A well-formed instance is a yes-instance when some admissible rule has a completion. -/
def Instance.IsYes (I : Instance) : Prop :=
  I.IsValid ∧ ∃ (rule : ℕ → ℕ × ℕ) (C : ℕ → ℕ), IsAdmissibleRule I.d I.p rule ∧ IsCompletion I rule C

end CallCountPOPBR


