-- Prove2me | Definitions.Def_CorrelatedLocalSearch_IsPotentialProcess
-- name    : CorrelatedLocalSearch_IsPotentialProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:30.965433+00:00
-- url     : https://prove2.me/theorems/455dd0c8-f160-4f05-b54c-28bb7782074b
-- title:
--   Processes with an integer potential (hypotheses of Lemma C.1)
-- statement:
--   A deterministic process driven by a tape in $[k]^{\mathbb N}$ is described by its **live** histories: after reading a word $w$ the process is still running when every prefix of $w$ (including $w$ and the empty word) is live; such a $w$ **survives**. Its stopping time is
--   $$
--   \tau(\omega)=\min\{t : \omega\!\restriction\! t \text{ is not live}\}\in\mathbb N\cup\{\infty\}.
--   $$
--   The process satisfies the **integer-potential hypotheses** of Lemma C.1 for $r$, with initial potential $h$, when a potential $\mathrm{pot}:[k]^*\to\mathbb N$ is given such that
--
--   1. $\mathrm{pot}(\varnothing)=h\ge1$;
--   2. every surviving history $w$ has potential $d=\mathrm{pot}(w)\ge 1$;
--   3. at every surviving $w$, at least $r$ of the $k$ next symbols $a$ either terminate ($wa$ not live) or give potential $\mathrm{pot}(wa)\le d-1$;
--   4. at every surviving $w$, every next symbol either terminates or gives potential $\mathrm{pot}(wa)\le d+1$.
--
--   The barrier bound of Lemma C.1 and its consequences hold for every such process; the promise-SAT walk with the Hamming distance to a strong witness is one.
--
--   **Formalization Note** The hypotheses are imposed only at surviving histories, the histories the process reaches. "Terminated histories have potential zero" is a convention of the proof, not a hypothesis: `pot` is unconstrained elsewhere. Counts of symbols use `Set.ncard`.
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, Lemma C.1, p.21 (PDF p.23); §2, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_SourceClass

set_option autoImplicit false

namespace CorrelatedLocalSearch

/-- A history `w` survives for the liveness predicate `live` when every prefix of `w`,
including `w` itself and the empty word, is live: the process reaches `w` without having
terminated (Xu, *Local Search with Correlated Randomness*, arXiv:2607.17469 (sha256 17e00d69…),
§2, p.6: "A prefix is live if the algorithm has not terminated after reading it"). -/
def Surv {k : ℕ} (live : List (Fin k) → Prop) (w : List (Fin k)) : Prop :=
  ∀ u : List (Fin k), u <+: w → live u

/-- The stopping time `τ` of a deterministic process driven by a tape, given by its live
histories: the least `t` such that the prefix `ω↾t` is not live (Xu, arXiv:2607.17469
(sha256 17e00d69…), §2, p.6: "`{τ > T}` is the event that the algorithm is still live after `T`
updates").

**Formalization Note** Valued in `ℕ∞`, `⊤` when every prefix is live. -/
noncomputable def hitTime {k : ℕ} (live : List (Fin k) → Prop) (ω : ℕ → Fin k) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : ¬ live (tapePrefix ω t)), (t : ℕ∞)

/-- The hypotheses of Lemma C.1 (Xu, arXiv:2607.17469 (sha256 17e00d69…), App. C.1,
Lemma C.1, p.21) on a deterministic process driven by symbols in `[k]`, described by its live
histories `live` and an integer potential `pot`: the initial potential is `h ≥ 1`; every
surviving history `w` has potential `d = pot w ≥ 1`; at least `r` of the `k` next symbols `a`
either terminate (`w ++ [a]` not live) or give a live potential at most `d − 1`; and every
symbol either terminates or gives a live potential at most `d + 1`.

**Formalization Note** "Live history" is read as a history the process reaches (`Surv`), and
the hypotheses are imposed only there. "Give every terminated history potential zero" is a
convention of the proof (`f(0) = 0` in (21)), not a hypothesis: `pot` is unconstrained at
non-surviving words. The count of symbols is `Set.ncard`. -/
structure IsPotentialProcess (k r : ℕ) (live : List (Fin k) → Prop)
    (pot : List (Fin k) → ℕ) (h : ℕ) : Prop where
  one_le_h : 1 ≤ h
  pot_nil : pot [] = h
  pos : ∀ w, Surv live w → 1 ≤ pot w
  down : ∀ w, Surv live w →
    r ≤ Set.ncard {a : Fin k | ¬ live (w ++ [a]) ∨ pot (w ++ [a]) + 1 ≤ pot w}
  up : ∀ w, Surv live w → ∀ a : Fin k, ¬ live (w ++ [a]) ∨ pot (w ++ [a]) ≤ pot w + 1

end CorrelatedLocalSearch


