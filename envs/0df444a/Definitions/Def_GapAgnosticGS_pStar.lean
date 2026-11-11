-- Prove2me | Definitions.Def_GapAgnosticGS_pStar
-- name    : GapAgnosticGS_pStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:31.767187+00:00
-- url     : https://prove2.me/theorems/06cbf8ae-2d3b-459b-b60d-05587782b6a4
-- title:
--   Best reward $p_\star=\max_j p_j$
-- statement:
--   For a hidden-basis environment with rewards $p_0,\dots,p_{n-1}$, the **best reward** is $p_\star:=\max_j p_j$. An arm attaining it is a best arm.
--
--   **Formalization Note** Written as the real supremum over the finite index set (a maximum for $n\ge1$).
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Definition 1.4, p.4 (PDF p.5): "p⋆ := max_j p_j"

import Definitions.Def_GapAgnosticGS_reward

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Definition 1.4, p.4 (PDF p.5): "p⋆ := max_j p_j", the largest reward.

**Formalization Note.** The maximum over the finite index set `Fin n` is the real supremum
`⨆ j, p_j` (a maximum for `n ≥ 1`; every statement has `n ≥ 2`). -/
noncomputable def pStar {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {a₀ : A}
    {Prj : Matrix A A ℂ} (Env : HidEnv n A a₀ Prj) : ℝ :=
  ⨆ j, reward Env j

end GapAgnosticGS


