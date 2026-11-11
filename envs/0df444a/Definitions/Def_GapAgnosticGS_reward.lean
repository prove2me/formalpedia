-- Prove2me | Definitions.Def_GapAgnosticGS_reward
-- name    : GapAgnosticGS_reward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:30:22.944121+00:00
-- url     : https://prove2.me/theorems/27aa4023-3e7a-43fe-b250-47d9cdb5b3fb
-- title:
--   Reward $p_j=\langle\mathrm{arm}_j|\Pi|\mathrm{arm}_j\rangle$ of a hidden arm
-- statement:
--   For a hidden-basis environment with reward projector $\Pi$, the **reward** of arm $j$ is
--
--   $$p_j:=\langle\mathrm{arm}_j|\,\Pi\,|\mathrm{arm}_j\rangle\in[0,1],$$
--
--   the probability of the reward-one outcome when arm $j$ is pulled.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Definition 1.4, p.4 (PDF p.5): "p_j := ⟨arm_j| Π |arm_j⟩"

import Definitions.Def_GapAgnosticGS_HidEnv
open QAlgorithms

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Definition 1.4, p.4 (PDF p.5): "p_j := ⟨arm_j| Π |arm_j⟩". The reward of arm `j`
(a real number in `[0, 1]`, since `Π` is an orthogonal projector and `arm j` a unit vector). -/
noncomputable def reward {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {a₀ : A}
    {Prj : Matrix A A ℂ} (Env : HidEnv n A a₀ Prj) (j : Fin n) : ℝ :=
  (inner ℂ (Env.arm j) (act Prj (Env.arm j))).re

end GapAgnosticGS


