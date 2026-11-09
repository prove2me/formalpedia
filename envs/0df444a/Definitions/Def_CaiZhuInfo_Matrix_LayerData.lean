-- Prove2me | Definitions.Def_CaiZhuInfo_Matrix_LayerData
-- name    : CaiZhuInfo_Matrix_LayerData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:11.002413+00:00
-- url     : https://prove2.me/theorems/75ed19f5-1cdc-4911-acd2-d19fa2a8207f
-- title:
--   Decreasing support enumeration, uniform layers and scales
-- statement:
--   Choose a decreasing enumeration $g_1,\dots,g_\ell$ of the positive support of a finitely supported probability law $Q$, writing $q_j=Q(g_j)$ and $q_{\ell+1}=0$. Define
--   $$A_j=\{g_1,\dots,g_j\},\qquad w_j=j(q_j-q_{j+1}),\qquad R=\lfloor\log_2J\rfloor.$$
--   Here $J$ has the computed layer weights $w_j$. The scale mass at $r$ is the sum of $w_j$ over indices with $\lfloor\log_2j\rfloor=r$, and its mean is the corresponding finite weighted sum. These quantities are computed from the enumeration; their normalization and mixture identity remain theorem targets. Ties may be ordered arbitrarily. The module also defines the clockwise cycle distance $c(s,r)=(r-s)\bmod n$, including zero distance when $n=1$. These definitions make the entropy-conversion milestones precise.
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), §4.1 and Appendix B, printed pp.11,27 / PDF pp.12,28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_conditionalInformation

namespace CaiZhuInfo.Matrix
noncomputable section
open scoped Classical

/-- A chosen decreasing enumeration of the positive support, §4.1,
printed p.11 / PDF p.12. It records only the ordering, not a decomposition. -/
structure LayerData (G : Type) where
  Q : PMF G
  length : ℕ
  point : Fin length → G
  injective : Function.Injective point
  covers : ∀ g, Q g ≠ 0 ↔ ∃ i, point i = g
  decreasing : ∀ i j, i ≤ j → Q (point j) ≤ Q (point i)

namespace LayerData
variable {G : Type} (L : LayerData G)

def weight (i : Fin L.length) : ℝ :=
  (i.val + 1 : ℕ) * (mass L.Q (L.point i) -
    if h : i.val + 1 < L.length then mass L.Q (L.point ⟨i.val + 1, h⟩) else 0)

def layer (i : Fin L.length) : Finset G :=
  (Finset.univ.filter fun j : Fin L.length => j ≤ i).image L.point

def layerMass (i : Fin L.length) (g : G) : ℝ :=
  if g ∈ L.layer i then 1 / (i.val + 1 : ℕ) else 0

/-- The scale law is computed from the weights, without assuming normalization. -/
def scaleMass (r : Fin (L.length + 1)) : ℝ :=
  ∑ i : Fin L.length, if Nat.log2 (i.val + 1) = r.val then L.weight i else 0

def scaleMean : ℝ := ∑ r : Fin (L.length + 1), L.scaleMass r * r.val

def supportEntropy : ℝ := FuchsVdGraaf.entropy (fun i => mass L.Q (L.point i))

end LayerData

/-- Clockwise distance, including the zero distance on the one-point cycle. -/
def cycleDistance {n : ℕ} (s r : Fin n) : ℕ := (r.val + n - s.val) % n

end
end CaiZhuInfo.Matrix


