-- Prove2me | Definitions.Def_RGGDetect_rggLaw
-- name    : RGGDetect_rggLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:54.579544+00:00
-- url     : https://prove2.me/theorems/31f57378-1bd5-4165-8d3b-d3f91064b937
-- title:
--   The random geometric graph law $P_{\mathrm{RGG}}$
-- statement:
--   Let $x_1,\dots,x_n$ be independent and uniform on $S^{d-1}$. The **hard-threshold spherical random geometric graph** $G(x)$ on the vertex set $[n]$ joins distinct vertices $i,j$ when $\langle x_i,x_j\rangle\ge\tau$. Its law is
--
--   $$
--   P_{\mathrm{RGG}}=\sum_{G}\ \mathbb P\{x: G(x)=G\}\,\delta_G ,
--   $$
--
--   the sum running over all simple graphs $G$ on $[n]$. When $\tau=\tau(d,p)$ solves $\mathbb P\{\langle x_1,x_2\rangle\ge\tau\}=p$, every single edge has probability $p$, as in $G(n,p)$; the question of the paper is whether the dependence created by the latent geometry is visible.
--
--   **Formalization Note** Graphs are `SimpleGraph (Fin n)`, a finite type, with every set of graphs measurable. The law is the finite sum of point masses above; for $d\ge1$ its total mass is $1$ (proved in the mission's sanity file), so it is not the zero measure.
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), §1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_RGGDetect_unifSphere

open MeasureTheory

namespace RGGDetect

/-- Graphs on `n` labelled vertices form a finite set; every set of graphs is an event. -/
instance graphMeasurableSpace (n : ℕ) : MeasurableSpace (SimpleGraph (Fin n)) := ⊤

instance graphDiscrete (n : ℕ) : DiscreteMeasurableSpace (SimpleGraph (Fin n)) :=
  ⟨fun _ => trivial⟩

/-- The hard-threshold spherical random geometric graph of a configuration: distinct vertices
`i, j` are adjacent when `⟨x_i, x_j⟩ ≥ τ` (arXiv:2610.08517, held version, §1, p.1). -/
def rggGraph {n d : ℕ} (τ : ℝ) (x : Config n d) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ τ ≤ ip (x i) (x j)
  symm := ⟨fun i j h => ⟨h.1.symm, by
    have : ip (x j) (x i) = ip (x i) (x j) := real_inner_comm _ _
    rw [this]; exact h.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- `P_RGG`, the law of the random geometric graph on `n` vertices with points independent and
uniform on `S^{d-1}` and threshold `τ` (arXiv:2610.08517, held version, §1, p.1).

**Formalization Note** The law is written as the finite sum `∑_G P{x : G(x) = G} δ_G` over all
graphs on `Fin n`, with every set of graphs measurable. For `d ≥ 1` it is a probability measure. -/
noncomputable def rggLaw (n d : ℕ) (τ : ℝ) : Measure (SimpleGraph (Fin n)) :=
  ∑ G : SimpleGraph (Fin n), prior n d {x | rggGraph τ x = G} • Measure.dirac G

end RGGDetect


