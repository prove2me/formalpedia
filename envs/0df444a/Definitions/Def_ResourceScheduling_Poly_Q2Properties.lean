-- Prove2me | Definitions.Def_ResourceScheduling_Poly_Q2Properties
-- name    : ResourceScheduling_Poly_Q2Properties
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:29:31.917698+00:00
-- url     : https://prove2.me/theorems/68f09bcd-4c4c-4529-b8a9-66f08a49509d
-- title:
--   Properties (a), (b), (c) of two-machine one-resource schedules (proof of Theorem 5)
-- statement:
--   Consider an instance with two uniform machines $M_1,M_2$ (speeds $q_1,q_2$) and one resource $R_1$ with requirements $r_{1j}$. The proof of Theorem 5 singles out the schedules satisfying the following properties:
--
--   1. (a) "the jobs $J_j$ on $M_1$ are executed in order of nonincreasing $r_{1j}$ without machine idle time": if $c$ jobs are on $M_1$, their start times are exactly $0,\,1/q_1,\,2/q_1,\dots,(c-1)/q_1$, each used once, and a job starting later on $M_1$ never has a larger requirement;
--   2. (b) "the jobs $J_k$ on $M_2$ are executed in order of nondecreasing $r_{1k}$": a job starting later on $M_2$ never has a smaller requirement;
--   3. (c) "$r_{1j}\ge r_{1k}$ for all $J_j$ on $M_1$ and all $J_k$ on $M_2$".
--
--   The definition also names the machines $M_1,M_2$ of a two-machine instance and the resource $R_1$ of a one-resource instance.
--
--   These properties describe the shape of the schedules the algorithm of Theorem 5 produces; the proof shows that restricting to them loses nothing.
--
--   **Formalization Note** $M_1$ and $M_2$ are the machines of index $0$ and $1$, and $R_1$ is the resource of index $0$. Property (a) is stated as: every job on $M_1$ starts at some $p/q_1$ with $p$ less than the number of jobs on $M_1$, distinct jobs on $M_1$ have distinct start times, and start order on $M_1$ is nonincreasing in requirement. The properties do not include feasibility.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 16, proof of Theorem 5, properties (a), (b), (c)

import Mathlib
import Definitions.Def_ResourceScheduling_Poly_Model

/-!
# Two uniform machines with one resource: the machines `M_1`, `M_2`, the resource `R_1`, and the
properties (a), (b), (c) of the proof of Theorem 5

Błażewicz, Lenstra & Rinnooy Kan, Discrete Appl. Math. 5 (1983), p. 16, proof of Theorem 5.
-/

namespace ResourceScheduling.Poly

namespace Instance

variable (I : Instance)

/-- The first machine `M_1` of a two-machine instance (index `0`). -/
def M₁ (hm : I.m = 2) : Fin I.m := ⟨0, by omega⟩

/-- The second machine `M_2` of a two-machine instance (index `1`). -/
def M₂ (hm : I.m = 2) : Fin I.m := ⟨1, by omega⟩

/-- The single resource `R_1` of a one-resource instance (index `0`). -/
def R₁ (hl : I.l = 1) : Fin I.l := ⟨0, by omega⟩

end Instance

namespace Schedule

variable {I : Instance} (hm : I.m = 2) (hl : I.l = 1)

/-- Properties (a), (b), (c) of the proof of Theorem 5 (p. 16), for a schedule on two machines
with one resource, `r_{1j}` being the requirement of `J_j` for `R_1`:

(a) the jobs on `M_1` are executed in order of nonincreasing `r_{1j}` without machine idle time:
their start times are `0, 1/q_1, 2/q_1, …, (c-1)/q_1`, each used once, where `c` is the number
of jobs on `M_1`, and a later job on `M_1` never has a larger requirement;
(b) the jobs on `M_2` are executed in order of nondecreasing `r_{1k}`;
(c) `r_{1j} ≥ r_{1k}` for all `J_j` on `M_1` and all `J_k` on `M_2`. -/
def SatisfiesABC (σ : Schedule I) : Prop :=
  -- (a)
  ((∀ j, σ.machine j = I.M₁ hm →
      ∃ p : ℕ, p < (Finset.univ.filter fun k => σ.machine k = I.M₁ hm).card ∧
        σ.start j = (p : ℝ) / I.q (I.M₁ hm)) ∧
    (∀ j k, σ.machine j = I.M₁ hm → σ.machine k = I.M₁ hm → j ≠ k → σ.start j ≠ σ.start k) ∧
    (∀ j k, σ.machine j = I.M₁ hm → σ.machine k = I.M₁ hm → σ.start j < σ.start k →
      I.r (I.R₁ hl) k ≤ I.r (I.R₁ hl) j)) ∧
  -- (b)
  (∀ j k, σ.machine j = I.M₂ hm → σ.machine k = I.M₂ hm → σ.start j < σ.start k →
      I.r (I.R₁ hl) j ≤ I.r (I.R₁ hl) k) ∧
  -- (c)
  (∀ j k, σ.machine j = I.M₁ hm → σ.machine k = I.M₂ hm → I.r (I.R₁ hl) k ≤ I.r (I.R₁ hl) j)

end Schedule

end ResourceScheduling.Poly


