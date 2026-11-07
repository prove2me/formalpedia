-- Prove2me | Definitions.Def_ReplicableDecisions_weakGraph
-- name    : ReplicableDecisions_weakGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:04:26.942371+00:00
-- url     : https://prove2.me/theorems/d44a4f37-0281-4738-a446-361f471811ac
-- title:
--   The Hellinger graphs $G_r$ and $G_{<r}$
-- statement:
--   For $r>0$, the graph $G_r$ joins distinct models with Hellinger distance at most $r$, and $G_{<r}$ joins distinct models with Hellinger distance strictly less than $r$.
--
--   The lower bound of the mission works on $G_{r_n}$ and the upper bound on $G_{<s_\rho}$; the paper keeps them apart to avoid a limiting argument.
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), §2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_ReplicableDecisions_hellinger
import Definitions.Def_ReplicableDecisions_Experiment

namespace ReplicableDecisions

/-- **The Hellinger graph `G_r`.** Chen, *Replicable Decisions in Finite Experiments*, STOC 2027
submission (sha256 52d181db…), §2, p.9 (PDF p.11): "let G_r join distinct models with Hellinger
distance at most r".

**Formalization Note.** Since `E.P` is injective, distinct indices are distinct models. -/
noncomputable def weakGraph {ι : Type*} {Z : Type} [Fintype Z] (E : Experiment ι Z) (r : ℝ) :
    SimpleGraph ι where
  Adj i j := i ≠ j ∧ hellinger (E.P i) (E.P j) ≤ r
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [hellinger_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **The strict Hellinger graph `G_{<r}`.** Chen, STOC 2027 submission (sha256 52d181db…), §2, p.9
(PDF p.11): "let G_{<r} use the strict inequality". -/
noncomputable def strictGraph {ι : Type*} {Z : Type} [Fintype Z] (E : Experiment ι Z) (r : ℝ) :
    SimpleGraph ι where
  Adj i j := i ≠ j ∧ hellinger (E.P i) (E.P j) < r
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [hellinger_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end ReplicableDecisions


