-- Prove2me | Definitions.Def_ParetoNCSched_Fs
-- name    : ParetoNCSched_Fs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:23:44.19729+00:00
-- url     : https://prove2.me/theorems/fea80c1b-87cb-465e-9eaf-8203741e73ef
-- title:
--   Layer cost $F_s=\sum_{i:\,e_i(t)>s}N(\tau_i(s))$
-- statement:
--   At time $t$, the cost charged to layer $s$ is
--   $$F_s=\sum_{i:\ e_i(t)>s} N\big(\tau_i(s)\big),$$
--   the sum, over the jobs that have crossed layer $s$, of the number of unfinished jobs at the moment they crossed it.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Proof of Lemma D.2, p.22

import Mathlib
import Definitions.Def_ParetoNCSched_crossTime
import Definitions.Def_ParetoNCSched_stateAt

namespace ParetoNCSched

/-- **The layer cost `F_s` at time `t`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), proof of Lemma D.2, p.22: "F_s = Σ_{i : eᵢ(t) > s}
N(τᵢ(s)) is the sum, over the jobs that have crossed layer s, of the number of unfinished jobs at the
moment they crossed it."

**Formalization Note.** `eᵢ(t)` and `N` are those of the run of `MRC_R`; `N(τ)` is the number of
unfinished jobs of the run at time `τ`. -/
noncomputable def Fs {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (t s : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => s < elapsed (mrcRate R p σ) i t),
    ((unfinished p (stateAt R p σ (crossTime R p σ i s))).card : ℝ)

end ParetoNCSched


