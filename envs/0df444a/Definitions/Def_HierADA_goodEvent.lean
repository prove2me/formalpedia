-- Prove2me | Definitions.Def_HierADA_goodEvent
-- name    : HierADA_goodEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:04:47.620561+00:00
-- url     : https://prove2.me/theorems/71d5f839-6692-478a-91bb-e3e7cee4ccda
-- title:
--   Good event $E$
-- statement:
--   The **good event** $E$ is the set of pairs (sample blocks $S$, noise realization $z$) for which the auxiliary execution satisfies all conclusions of Proposition 3.2:
--
--   1. for every learned block $j<p$ there is a single $u_j\in W_j$ with $|\langle u_j,f_t(S_j)\rangle-Pf_t|\le\frac\tau{64}$ for every query $f_t$ of the execution and $R_j(u_j)\le\varepsilon_j^2$;
--   2. the uniform anchor satisfies $|\mu_p(f_t)-Pf_t|\le\frac\tau{32}$ for every query $f_t$;
--   3. every noise draw of the execution has magnitude at most $\frac\tau{64}$.
--
--   Here $Pf=\sum_xP(x)f(x)$ is the population mean. Propositions 3.4 and 3.5 hold for every point of $E$, and Theorem 3.7 shows $\Pr[E]\ge1-\xi$.
--
--   **Formalization Note** $W_j$ is the published `NondualOpt.cappedSimplex` with cap $8/n_j$. "Every $t\in[k]$" ranges over the queries the auxiliary execution received, which are fewer than $k$ if it stopped at a limit.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Proposition 3.2 (pp.18–19) and the definition of E, p.19

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_HierADA_auxRun
import Definitions.Def_NondualOpt_cappedSimplex
import Definitions.Def_HierADA_penalty

set_option autoImplicit false

open IsRandomnessNecessaryADA.Plain

namespace HierADA

/-- **The good event `E`** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, *Adaptive Data Analysis and
Adversarial Robustness on Insertion-Deletion Streams*, preprint (version of 2026-11-03, sha256
f220ae51…), Proposition 3.2 (pp.18–19) and p.19: "Let `E` denote the event that all conclusions of
Proposition 3.2 hold".

The set of (blocks `S`, noise `z`) such that, for the auxiliary execution on `S` and `z` with
distribution `P` and analyst `A`:
1. for every learned block `j < p` there is a single `u_j ∈ W_j` with
   `|⟨u_j, f_t(S_j)⟩ − D f_t| ≤ τ/64` for every query `f_t` of the execution and `R_j(u_j) ≤ ε_j²`;
2. the uniform anchor satisfies `|μ_p(f_t) − D f_t| ≤ τ/32` for every query `f_t`;
3. every noise draw of the execution has magnitude at most `τ/64`.

Here `D f = ∑_x P(x) f(x)` is the population mean (published `populationMean`).

**Formalization Note.** Indices are 0-based (learned blocks `j + 1 < p`, anchor `j + 1 = p`). "Every
`t ∈ [k]`" ranges over the queries the auxiliary execution received (fewer than `k` if it stopped at a
limit). The anchor's prediction is the uniform average `n_p^{-1} ∑_i f(X_{p,i})`. -/
def goodEvent {X : Type} [Fintype X] (prm : Params) (k : ℕ) (P : PMF X) (n : Fin prm.p → ℕ)
    (A : Analyst X) : Set (((j : Fin prm.p) → Fin (n j) → X) × Noise) :=
  {ω | (∀ j : Fin prm.p, j.val + 1 < prm.p →
          ∃ u ∈ NondualOpt.cappedSimplex (n j) 8,
            (∀ f ∈ (auxRun prm n ω.1 ω.2 A k).queries,
              |∑ i, u i * (f (ω.1 j i) : ℝ) - populationMean P f| ≤ prm.τ / 64) ∧
            penalty (n j) u ≤ prm.ε j ^ 2) ∧
       (∀ j : Fin prm.p, j.val + 1 = prm.p →
          ∀ f ∈ (auxRun prm n ω.1 ω.2 A k).queries,
            |(∑ i, (1 / (n j : ℝ)) * (f (ω.1 j i) : ℝ)) - populationMean P f| ≤ prm.τ / 32) ∧
       ∀ v ∈ (auxRun prm n ω.1 ω.2 A k).noiseUsed, |v| ≤ prm.τ / 64}

end HierADA


