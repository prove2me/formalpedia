-- Prove2me | Definitions.Def_GapAgnosticGS_OracleAlg_Step
-- name    : GapAgnosticGS_OracleAlg_Step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:22.54437+00:00
-- url     : https://prove2.me/theorems/b6524353-5a19-44d7-ac79-459acdc04661
-- title:
--   Step kinds of an adaptive quantum oracle algorithm
-- statement:
--   After each classical history an adaptive oracle algorithm takes one of four kinds of step:
--
--   1. an **oracle-free isometry** (which may enlarge the workspace);
--   2. a **query**: one controlled use of the oracle $U$, or of $U^\dagger$;
--   3. a **measurement** of (part of) the workspace in the computational basis;
--   4. a **halt** with a classical output $o$.
--
--   These are the operations of the paper's access model ("access to $W_H$, $W_H^\dagger$, and controlled versions of both"). The paper does not define its algorithm model; this is the standard adaptive model, used by both the upper and the lower bound of the mission.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.1 (PDF p.2) (access model); Theorem 1.1, p.2 (PDF p.3)

import Mathlib

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.1 (PDF p.2): "We assume access to W_H, W_H†, and controlled versions of both; one
controlled use of W_H or W_H† counts as one query", and Theorem 1.1, p.2 (PDF p.3): "an algorithm
outputs … using … expected queries". The kinds of step of an adaptive oracle algorithm (the
paper does not define the model; see `OracleAlg`):

* `iso`: an oracle-free isometry (it may enlarge the workspace);
* `query adj`: one controlled use of the oracle `U` (`adj = false`) or of `U†` (`adj = true`);
* `measure`: a computational-basis measurement of (part of) the workspace;
* `halt o`: stop with classical output `o`. -/
inductive OracleAlg.Step (O : Type) : Type
  | iso
  | query (adj : Bool)
  | measure
  | halt (o : O)

end GapAgnosticGS


