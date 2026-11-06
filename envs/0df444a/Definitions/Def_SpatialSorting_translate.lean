-- Prove2me | Definitions.Def_SpatialSorting_translate
-- name    : SpatialSorting_translate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:33.99907+00:00
-- url     : https://prove2.me/theorems/b2a36da5-61f5-46ef-9eef-43cf0f01ea58
-- title:
--   Translate of a contour
-- statement:
--   For a contour $\gamma$ and $a\in\mathbb Z^2$, $\gamma+a$ has support $\overline\gamma+a$ and colours $\omega_{\gamma+a}(x)=\omega_\gamma(x-a)$. Translation invariance of an activity means that it takes the same value on $\gamma$ and $\gamma+a$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 4.3 (translation invariance), p. 25 (PDF p. 26)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
open Classical Filter Topology

namespace SpatialSorting

/-- The translate `γ + a` of a contour by a lattice vector `a`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 4.3 (translation invariance), p. 25 (PDF p. 26). -/
noncomputable def translate {q : ℕ} [NeZero q] (γ : Contour q) (a : ℤ × ℤ) : Contour q where
  support := γ.support.image (· + a)
  color := fun x => γ.color (x - a)
  color_off := fun x hx => γ.color_off _ (fun h => hx (Finset.mem_image.2 ⟨x - a, h, by simp⟩))

end SpatialSorting


