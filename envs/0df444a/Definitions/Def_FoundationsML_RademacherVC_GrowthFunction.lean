-- Prove2me | Definitions.Def_FoundationsML_RademacherVC_GrowthFunction
-- name    : FoundationsML_RademacherVC_GrowthFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:11:44.745557+00:00
-- url     : https://prove2.me/theorems/5005ceca-979b-49c7-864e-d180be44226b
-- title:
--   Growth function (Definition 3.6)
-- statement:
--   **Definition 3.6 (Growth function), p. 34, PDF p. 51.** The growth function
--   $\Pi_H : \mathbb N \to \mathbb N$ for a hypothesis set $H$ is
--   $$\Pi_H(m) = \max_{\{x_1,\dots,x_m\}\subseteq X}\big|\{(h(x_1),\dots,h(x_m)) : h\in H\}\big|,$$
--   the maximum number of distinct dichotomies $m$ points can realize under $H$.
--
--   **Formalization Note.** Points are a tuple `x : Fin m → X` rather than a size-`m` subset;
--   allowing repeats never increases the dichotomy count, so the supremum over tuples matches
--   the book's supremum over size-`m` sets whenever `X` has ≥ `m` points (and is a harmless
--   generalization otherwise). `Fin m → Bool` is finite, so this `ℕ`-supremum is always
--   bounded (by `2^m`), with no vacuous/unbounded corner (trap 5 does not apply).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 34, Definition 3.6 (PDF p. 51)

import Mathlib

namespace FoundationsML.RademacherVC

/-- The growth function of a hypothesis set `H` of functions `X → Bool` (Mohri, Rostamizadeh
& Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 3.6,
p. 34, PDF p. 51): `Π_H(m)` is the maximum, over sets (here: tuples) of `m` points of `X`, of
the number of distinct dichotomies (labelings) `H` realizes on those points.

**Formalization Note.** Points are taken as a tuple `x : Fin m → X` rather than a size-`m`
subset of `X`; allowing repeated points never increases the dichotomy count (a repeated point
cannot add a new labeling), so the supremum over tuples equals the book's supremum over
size-`m` sets whenever `X` has at least `m` distinct points, and is a harmless generalization
otherwise. `Fin m → Bool` is finite, so the inner cardinality — and hence this supremum over
`ℕ` — is always bounded (by `2^m`), with no vacuous/unbounded-supremum corner. -/
noncomputable def GrowthFunction {X : Type*} (H : Set (X → Bool)) (m : ℕ) : ℕ :=
  ⨆ x : Fin m → X, Nat.card {t : Fin m → Bool // ∃ h ∈ H, t = h ∘ x}

end FoundationsML.RademacherVC


