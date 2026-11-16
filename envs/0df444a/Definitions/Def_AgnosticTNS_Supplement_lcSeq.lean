-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_lcSeq
-- name    : AgnosticTNS_Supplement_lcSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:25:27.925521+00:00
-- url     : https://prove2.me/theorems/6d05210a-7f8b-4ca6-bc0f-74e031a3c617
-- title:
--   Learning complexity $\mathrm{lc}(\mathcal L)=\max_i(a_i+q_i)$ of a learning sequence
-- statement:
--   For a learning sequence $\mathcal L$ and rank bounds $r_i$, with $q_i=\lceil\log_d r_i\rceil$ and $a_i$ the realisable active size, the **learning complexity** of $\mathcal L$ is
--   $$
--   \mathrm{lc}(\mathcal L) := \max_{i\in[L]} (a_i+q_i).
--   $$
--   With the uniform bounds $r_i=\chi^{|\mathrm{cut}_G(S_i)|}$ this is $\mathrm{lc}_{d,\chi}(\mathcal L)$ (4.45); with the weighted bounds $r_i=\prod_{e\in\mathrm{cut}_G(S_i)}w(e)$ it is $\mathrm{lc}_{d,w}(\mathcal L)$ (4.46). It controls the copy complexity of the realisable learner through $r_i d^{a_i}\le d^{a_i+q_i}$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 4.2, Eqs. (4.45)–(4.46), p.32; Eq. (1.4), p.4

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_aR

namespace AgnosticTNS.Supplement

/-- **The learning complexity of a learning sequence** `lc(L) = max_{i ∈ [L]} (a_i + q_i)`,
Eqs. (4.45)–(4.46), p.32 (also (1.4), p.4) (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)), for given
rank bounds `r_i`: `lc_{d,χ}(L)` with the uniform bounds (4.41), `lc_{d,w}(L)` with the weighted
bounds (4.42).

**Formalization Note** `q_i = Nat.clog d r_i` and `a_i` is `aR`. -/
def lcSeq {n : ℕ} (d : ℕ) (Ls : LearningSequence n) (r : Fin Ls.L → ℕ) : ℕ :=
  Finset.univ.sup fun i => aR d Ls r i + Nat.clog d (r i)

end AgnosticTNS.Supplement


