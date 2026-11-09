-- Prove2me | Definitions.Def_CompDesign_IsStrictImprovement
-- name    : CompDesign_IsStrictImprovement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:55:26.530208+00:00
-- url     : https://prove2.me/theorems/a4b19dcb-fce8-40bd-bedd-f86d48ac482f
-- title:
--   Switching participation and strict better responses in $\Gamma^{mc}$
-- statement:
--   For a participating set $S\subseteq N$ and an agent $i$, **switching** $i$'s participation decision gives $S\setminus\{i\}$ if $i\in S$ (opting out) and $S\cup\{i\}$ if $i\notin S$ (opting in).
--
--   A move from $S$ to $S'$ is a **strict better response** (a strict unilateral improvement) in $\Gamma^{mc}$ if there is an agent $i$ such that $S'$ is obtained from $S$ by switching $i$'s participation decision and
--   $$u_i(S') > u_i(S),$$
--   where $u_i$ is the utility of $\Gamma^{mc}$. Only the deviating agent's own utility is compared.
--
--   Theorem 4.1 asserts that every sequence of such moves terminates; its terminal states are the pure Nash equilibria of Definition 3.1.
--
--   **Formalization Note** `switch S i` is `S.erase i` if `i ∈ S` and `insert i S` otherwise. The definition compares utilities only; the potential of the proof of Theorem 4.1 does not enter it.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Definition 3.1, p.14 (PDF 17) (switching participation); Theorem 4.1, p.17 (PDF 20) (strict better responses)

import Mathlib
import Definitions.Def_CompDesign_util

namespace CompDesign

/-- Agent `i` switches its participation decision (Definition 3.1, p.14 (PDF 17) of Anagnostides
et al., *Compensation Design*, arXiv:2607.14438, version of November 3, 2026, sha256 3d305d4d…):
an agent in `S` opts out, giving `S ∖ {i}`, and an agent outside `S` opts in, giving `S ∪ {i}`. -/
def switch {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : Finset (Fin n) :=
  if i ∈ S then S.erase i else insert i S

/-- A strict better response (strict unilateral improvement) in the game `Γ^mc` (Theorem 4.1, p.17
(PDF 20) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438, version of November 3,
2026, sha256 3d305d4d…): the move from `S` to `S'` is made by one agent `i` switching its
participation decision, and it strictly raises that agent's own utility `u_i`.

**Formalization Note.** The utilities are those of `Γ^mc` (`CompDesign.util`), evaluated at the old
set `S` and at the new set `S'`. Nothing about the potential enters the definition. -/
def IsStrictImprovement {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ)
    (S S' : Finset (Fin n)) : Prop :=
  ∃ i, S' = switch S i ∧ util v B c S i < util v B c S' i

end CompDesign


