-- Prove2me | Definitions.Def_FirstOrderFG_Alg4_condExp
-- name    : FirstOrderFG_Alg4_condExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:58:18.909586+00:00
-- url     : https://prove2.me/theorems/1d4c6c92-db44-4501-857b-9a3509379229
-- title:
--   Expectation over a run of Algorithm 4 conditional on a history
-- statement:
--   $\mathbb E[\Phi\mid h]$ is the expectation of a functional $\Phi$ of the full history (rounds $1,\dots,T$) conditional on the arms $h$ of the first $|h|$ rounds; with $h$ empty it is $\mathbb E[\Phi]$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3; Lemma B.6, p.33

import Mathlib
import Definitions.Def_FirstOrderFG_Alg4_play
import Definitions.Def_FirstOrderFG_treeExp

namespace FirstOrderFG

/-- **Expectation over the run of Algorithm 4, conditional on a history.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3, and
Lemma B.6, p.33 (`E_{t^start}`, "conditional on the history before `t^start`").

`Alg4.condExp E T ℓ q₀ h Φ` is the expectation of `Φ` on the full history (rounds `1, …, T`),
conditional on the arms `h` of rounds `1, …, |h|`; `Alg4.condExp … [] Φ` is `E[Φ]`. -/
noncomputable def Alg4.condExp {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (ℓ : ℕ → Fin K → ℝ)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (h : List (Fin K)) (Φ : List (Fin K) → ℝ) : ℝ :=
  treeExp (Alg4.play E T ℓ q₀) (T - h.length) h Φ

end FirstOrderFG


