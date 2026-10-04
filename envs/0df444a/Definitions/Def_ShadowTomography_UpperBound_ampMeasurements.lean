-- Prove2me | Definitions.Def_ShadowTomography_UpperBound_ampMeasurements
-- name    : ShadowTomography_UpperBound_ampMeasurements
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:13:10.252899+00:00
-- url     : https://prove2.me/theorems/791858cc-89ae-4c73-9567-97020656b5ce
-- title:
--   Threshold-amplified measurements: apply E to each of q registers, accept iff ≥ θq (or ≤ θq) accept
-- statement:
--   Let $E$ be a two-outcome measurement on a system with basis labels $n$, let $q\ge 0$ and let $\theta$ be a real threshold. Applying $E$ to each of $q$ registers produces an accept/reject pattern; the pattern "exactly the registers in $S\subseteq\{1,\dots,q\}$ accept" has POVM element
--
--   $$
--   \Pi_S = \bigotimes_{r=1}^{q} \begin{cases} E & r\in S,\\ \mathbb 1 - E & r\notin S.\end{cases}
--   $$
--
--   The **amplified measurements** are
--
--   $$
--   E^{\ge}_{q,\theta} = \sum_{S:\ |S| \ge \theta q} \Pi_S, \qquad E^{\le}_{q,\theta} = \sum_{S:\ |S|\le \theta q} \Pi_S ,
--   $$
--
--   which accept if and only if the number of accepting invocations of $E$ is at least, respectively at most, $\theta q$. In the proof of Theorem 2 they appear as $E^*_{i,t,+}$ and $E^*_{i,t,-}$ (thresholds $\mathrm{Tr}(E_i\rho_t)\pm 3\varepsilon/4$) and as the postselection measurement $F_t$ (thresholds $\mathrm{Tr}(E_j\rho_t)\pm\varepsilon/4$).
--
--   **Formalization Note** `acceptPattern E q S` is $\Pi_S$ (entrywise product over registers), `ampAtLeast E q θ` is $E^{\ge}_{q,\theta}$ and `ampAtMost E q θ` is $E^{\le}_{q,\theta}$. The threshold is real and compared with the cardinality cast to $\mathbb R$; it is never rounded.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 16 (E^*_{i,t,±}), p. 17 (F_t); also p. 14 (E_i^* in the proof of Lemma 14)

import Mathlib

namespace ShadowTomography.UpperBound

/-- The product operator on `q` registers that applies `E` on the registers in `S` and `1 - E`
on the others: its `(x, y)` entry is `∏ r, (if r ∈ S then E else 1 - E) (x r) (y r)`.
It is the POVM element of the outcome "exactly the invocations in `S` accept" when `E` is
applied to each of the `q` registers. -/
def acceptPattern {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n ℂ) (q : ℕ)
    (S : Finset (Fin q)) : Matrix (Fin q → n) (Fin q → n) ℂ :=
  fun x y => ∏ r, (if r ∈ S then E else 1 - E) (x r) (y r)

open Classical in
/-- The amplified two-outcome measurement on `q` registers that applies `E` to each register and
accepts iff the number of accepting invocations is at least `θ q` (a real threshold). -/
noncomputable def ampAtLeast {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n ℂ) (q : ℕ)
    (θ : ℝ) : Matrix (Fin q → n) (Fin q → n) ℂ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin q) => θ * (q : ℝ) ≤ (S.card : ℝ)),
    acceptPattern E q S

open Classical in
/-- The amplified two-outcome measurement on `q` registers that applies `E` to each register and
accepts iff the number of accepting invocations is at most `θ q` (a real threshold). -/
noncomputable def ampAtMost {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n ℂ) (q : ℕ)
    (θ : ℝ) : Matrix (Fin q → n) (Fin q → n) ℂ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin q) => (S.card : ℝ) ≤ θ * (q : ℝ)),
    acceptPattern E q S

end ShadowTomography.UpperBound


