-- Prove2me | Definitions.Def_PrivLittlestone_IsA2
-- name    : PrivLittlestone_IsA2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:43:31.396141+00:00
-- url     : https://prove2.me/theorems/5818213d-261f-4d71-b5fd-4bd77749ee2c
-- title:
--   Condition (A2): certified mistakes at every phase start, except with probability $\beta/(4K)$
-- statement:
--   **Condition (A2)** for an input strategy at failure level $\beta$: at every phase's sampling step, with $S$ the retained sequence at phase start, except with conditional probability at most $\beta/(4K)$ over the samples $h_1, \dots, h_m \sim Q_S$, every mistake of the aggregate $g = \mathrm{Agg}(h_1, \dots, h_m)$ on the relevant future inputs returns a record $u = \kappa(g, z_t)$ with
--   $$
--   \mathbb E_{h \sim Q_S}\, \ell_u(h) \ge \tfrac13 .
--   $$
--   The distribution $Q_S$ is frozen at phase start.
--
--   **Formalization Note** "Conditional probability at a phase's sampling step" is the probability over the phase's samples given the history, for almost every history; "relevant future inputs" are the records of the continuation in which $g$ is held fixed until the horizon (each actual phase is a prefix of it).
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (A2), p.7

import Mathlib
import Definitions.Def_PrivLittlestone_continualLearner
import Definitions.Def_PrivLittlestone_playRecords
import Definitions.Def_PrivLittlestone_contInput
import Definitions.Def_PrivLittlestone_gibbsExp
import Definitions.Def_PrivLittlestone_prodProb

namespace PrivLittlestone

open MeasureTheory

/-- **Condition (A2)** for an input strategy, at failure level `β` (He–He, *Private Online
Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), (A2), p.7): "Except with conditional probability at most `β/(4K)` at a phase's
sampling step, every mistake of its aggregate on the relevant future inputs returns `u` with
`E_{h∼Q_S} ℓ_u(h) ≥ 1/3`. The distribution in (A2) is frozen at phase start." Along almost every
run, at every round `t₀ < T` at which a phase starts (before the fallback), with `S` the retained
sequence at that moment: under `m` independent draws `h_1, …, h_m` from `Q_S`, with probability
at least `1 − β/(4K)` the aggregate `g = Agg(h_1, …, h_m)` has the property that on the
continuation in which `g` is held fixed to the horizon, every record `z_t`, `t ≥ t₀`, on which `g`
errs returns `κ(g, z_t) = u` with `E_{h∼Q_S} ℓ_u(h) ≥ 1/3`.

**Formalization Note** "Conditional probability at a phase's sampling step" is the probability
over the phase's samples given the history, for almost every history. "Relevant future inputs"
are the records of the continuation with `g` fixed (each actual phase is a prefix of it). -/
def IsA2 {X Z U : Type*} {D : ℕ} {B : ℝ} (P : Alg1Spec X Z U D B) (β : ℝ)
    (inp : InputStrategy X P.T) : Prop :=
  ∀ᵐ ω ∂(coinMeasure P), ∀ t₀ : Fin P.T,
    (algState P ω t₀
        (fun i => playRecords (continualLearner P) inp ω (Fin.castLE t₀.isLt.le i))).start = t₀ →
    (algState P ω t₀
        (fun i => playRecords (continualLearner P) inp ω (Fin.castLE t₀.isLt.le i))).fallback =
      false →
    1 - β / (4 * (P.K : ℝ)) ≤
      prodProb (P.sys.C (algState P ω t₀
          (fun i => playRecords (continualLearner P) inp ω (Fin.castLE t₀.isLt.le i))).retained)
        (gibbs P.sys P.η P.a (algState P ω t₀
          (fun i => playRecords (continualLearner P) inp ω (Fin.castLE t₀.isLt.le i))).retained)
        P.m
        (fun h => ∀ t : Fin P.T, (t₀ : ℕ) ≤ t →
          (P.agg h) (contInput inp (playClassifiers (continualLearner P) inp ω) t₀ (P.agg h) t).1 ≠
              (contInput inp (playClassifiers (continualLearner P) inp ω) t₀ (P.agg h) t).2 →
            ∃ u : Z, P.κ (P.agg h)
                (contInput inp (playClassifiers (continualLearner P) inp ω) t₀ (P.agg h) t) =
                some u ∧
              (1 : ℝ) / 3 ≤ gibbsExp P.sys P.η P.a (algState P ω t₀
                (fun i => playRecords (continualLearner P) inp ω (Fin.castLE t₀.isLt.le i))).retained
                (fun h' => (P.sys.loss u h' : ℝ)))

end PrivLittlestone


