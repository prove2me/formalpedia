-- Prove2me | Definitions.Def_LeGallBrownianMap_ghMeasurableSpace
-- name    : LeGallBrownianMap_ghMeasurableSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:57.0289+00:00
-- url     : https://prove2.me/theorems/f096db8a-c916-4b70-b520-148d68db0b9d
-- title:
--   Borel $\sigma$-algebra on the Gromov–Hausdorff space $\mathbb K$
-- statement:
--   Let $\mathbb K$ be the set of isometry classes of compact metric spaces, equipped with the Gromov–Hausdorff distance $d_{GH}$; $(\mathbb K, d_{GH})$ is a Polish space. Random compact metric spaces are random variables with values in $\mathbb K$, and their laws are measures on the **Borel $\sigma$-algebra** of $(\mathbb K, d_{GH})$, which is the $\sigma$-algebra fixed here.
--
--   This is the measurable structure under which "convergence in distribution in the space $\mathbb K$" (Theorem 1.1) and "random compact metric space" are meant throughout the mission.
--
--   **Formalization Note** $\mathbb K$ is Mathlib's `GromovHausdorff.GHSpace`, which carries the Gromov–Hausdorff metric but no measurable structure; the instance is `borel GHSpace`, with the matching `BorelSpace` instance.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §1, p.2 (the space K with d_GH)

import Mathlib

open GromovHausdorff

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §1, p.2:
"we view (m_n, d_gr) as a random variable taking values in the space K of isometry classes of
compact metric spaces. We equip K with the Gromov–Hausdorff distance d_GH […] and note that
(K, d_GH) is a Polish space." The space K is Mathlib's `GromovHausdorff.GHSpace` with its
Gromov–Hausdorff metric; random variables with values in K and their laws use the Borel
σ-algebra of that metric.

**Formalization Note.** Mathlib (rev 0df444a) puts no `MeasurableSpace` on `GHSpace`; this
instance is the Borel σ-algebra of the Gromov–Hausdorff topology, the σ-algebra under which
convergence in distribution in K is meant. The companion instance records `BorelSpace`. -/
noncomputable instance ghMeasurableSpace : MeasurableSpace GHSpace := borel GHSpace

instance ghBorelSpace : BorelSpace GHSpace := ⟨rfl⟩

end LeGallBrownianMap


