-- Prove2me | Definitions.Def_LawLocalComp_lawOfW
-- name    : LawLocalComp_lawOfW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:12:21.613955+00:00
-- url     : https://prove2.me/theorems/5162d4cd-3769-4a0b-ac6a-56bf1a791fb5
-- title:
--   Law with given weights
-- statement:
--   Given a finitely supported weight function $w$ on $\mathbb R$, `lawOfW w` is the law with weights $w$ whenever $w$ is nonnegative, supported in $[0,\infty)$ and of total mass one. It is used to build the output of a cell replacement from its weights.
--
--   **Formalization Note** If $w$ is not a law the value is the point mass at $0$. Every use applies it to weights that form a law, so a statement about a map built with it fails, rather than holding vacuously, if the weights were invalid.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §3, p.5

import Mathlib
import Definitions.Def_LawLocalComp_dirac
open Classical

namespace LawLocalComp

/-- **The law with given weights.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §3, p.5 ("Each label retains its mass and conditional mean"): used to build the output law of a
cell replacement from its weights.

`lawOfW w` is the law whose weights are `w` when `w` is a valid law (nonnegative, supported in
`[0, ∞)`, total mass `1`), and the point mass at `0` otherwise.

**Formalization Note.** The fallback only makes the function total; every use in this mission
applies it to weights that form a law, and a statement about a map built with it fails (rather
than holds vacuously) if the weights were not a law. -/
noncomputable def lawOfW (w : ℝ →₀ ℝ) : Law :=
  if h : (∀ x, 0 ≤ w x) ∧ (∀ x ∈ w.support, x ∈ Set.Ici (0 : ℝ)) ∧ ∑ x ∈ w.support, w x = 1 then
    ⟨w, h.1, h.2.1, h.2.2⟩
  else dirac 0

end LawLocalComp


