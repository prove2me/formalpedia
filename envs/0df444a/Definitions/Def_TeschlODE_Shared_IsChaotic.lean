-- Prove2me | Definitions.Def_TeschlODE_Shared_IsChaotic
-- name    : TeschlODE_Shared_IsChaotic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:23:50.312806+00:00
-- url     : https://prove2.me/theorems/0353a836-945a-48bf-8a2d-179bc86fe388
-- title:
--   Chaotic dynamical system (Devaney's definition as used by Teschl)
-- statement:
--   A discrete dynamical system $(M, f)$, with $M$ a metric space and $f : M \to M$, is **chaotic** if $f$ is continuous, $M$ is infinite, $f$ is topologically transitive, and the set of periodic points
--   $$\mathrm{Per}(f) = \{\, x \in M : f^n(x) = x \text{ for some } n \ge 1 \,\}$$
--   is dense in $M$.
--
--   This is the definition Teschl adopts (p. 296), attributed to Devaney. Unlike Devaney's own book, it contains no sensitive-dependence clause; that property is a consequence (Lemma 11.3).
--
--   This one definition serves chunk 09-interval-maps (Lemma 11.3, p. 297; the strange repellor of §11.6, p. 307, and through it Theorem 11.20, p. 309) and chunk 11-horseshoe (Theorem 13.1, p. 333).
--
--   **Formalization Note.** Periodic points are Mathlib's `Function.periodicPts f` (some period $n > 0$). The continuity of $f$ and the infiniteness of $M$ are standing requirements of the book's definition and are part of the predicate.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 296, §11.3 (definition of chaos)

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsTopTransitive

namespace TeschlODE.Shared

/-- Teschl, §11.3, p. 296 (Devaney's definition as used in the book): a discrete dynamical
system `(M, f)` on a metric space `M`, with `f` continuous and `M` infinite, is chaotic if `f`
is topologically transitive and the periodic points `Per(f) = {x | fⁿ(x) = x for some n ≥ 1}`
are dense in `M`. There is no sensitivity clause (that is Lemma 11.3). -/
def IsChaotic {M : Type*} [MetricSpace M] (f : M → M) : Prop :=
  Continuous f ∧ Infinite M ∧ IsTopTransitive f ∧ Dense (Function.periodicPts f)

end TeschlODE.Shared


