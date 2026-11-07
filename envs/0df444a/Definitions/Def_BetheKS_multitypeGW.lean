-- Prove2me | Definitions.Def_BetheKS_multitypeGW
-- name    : BetheKS_multitypeGW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:35:03.618237+00:00
-- url     : https://prove2.me/theorems/f2061e42-012c-4b1c-88eb-923d849b6d35
-- title:
--   The multitype Galton–Watson law $\widetilde\nu$ on labelled trees
-- statement:
--   $\widetilde\nu$ is the law of a multitype Galton–Watson tree with labels in $[r]$ (Definition 5.1): the root $o$ has type $\sigma(o)\sim\pi$, and each vertex of type $i$ independently has $\mathrm{Poi}(P_{ij}\pi_j)$ children of type $j$, for every $j\in[r]$. Its underlying unlabelled tree has law $\nu$.
--
--   **Formalization Note** The labelled tree is realized as the $\mathrm{Poi}(d)$ Galton–Watson tree with labels broadcast down the tree: the root label has law $\pi$ and each child of a type-$i$ vertex independently has type $j$ with probability $Q_{ij}/d$. Because every type has the same total $\sum_jQ_{ij}=d$ by (2.1), Poisson thinning gives exactly $\mathrm{Poi}(Q_{ij})$ children of type $j$, independently over $j$, which is Definition 5.1 (children ordered).
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Definition 5.1, p.9

import Mathlib
import Definitions.Def_BetheKS_SBMParams
import Definitions.Def_BetheKS_GWTree

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace BetheKS

variable {r : ℕ}

/-- The data of a labelled tree: an offspring function `K` (the unlabelled tree `T₀`), the root label
`σ(o)`, and for every word `w` and every parent label `i` a candidate child label. -/
abbrev LTData (r : ℕ) := Offspring × Fin r × (List ℕ → Fin r → Fin r)

/-- The labels of the vertices: `σ(o)` is the root label, and the child `j :: w` of `w` gets the
candidate label drawn at `j :: w` for the parent's label `σ(w)`. -/
def label (ω : LTData r) : List ℕ → Fin r
  | [] => ω.2.1
  | j :: w => ω.2.2 (j :: w) (label ω w)

/-- The law `π` on `[r]`. -/
noncomputable def piPMF (p : SBMParams r) : PMF (Fin r) :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p.pi a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (p.pi_pos a).le), p.pi_sum, ENNReal.ofReal_one])

/-- The child-label law `Q_{i·}/d` of a child of a type-`i` vertex. -/
noncomputable def kernelPMF (p : SBMParams r) (i : Fin r) : PMF (Fin r) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (signal p i j / p.d)) (by
    have hd : 0 < p.d := lt_trans zero_lt_one p.one_lt_d
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => div_nonneg (by
      simp only [signal, Matrix.mul_diagonal]
      exact mul_nonneg (p.P_nonneg i j) (p.pi_pos j).le) hd.le)]
    rw [← Finset.sum_div]
    simp only [signal, Matrix.mul_diagonal]
    rw [p.degree_eq i, div_self hd.ne', ENNReal.ofReal_one])

/-- **The multitype Galton–Watson law `ν̃`** — Dong, McKenzie, arXiv:2610.41802 (held version,
sha256 4da41e16…), Definition 5.1, p.9 (PDF p.10): the root has type `σ(o) ∼ π`, and each vertex of
type `i` independently has `Poi(P_{ij} π_j)` children of type `j` for every `j ∈ [r]`.

**Formalization Note.** The labelled tree is realized as the `Poi(d)` Galton–Watson tree `ν`
(`gwLaw d`) with labels broadcast down the tree: the root label has law `π` and, independently, each
child of a type-`i` vertex has type `j` with probability `Q_{ij}/d = P_{ij}π_j/d`. Because every type
has the same total `∑ⱼ Q_{ij} = d` (2.1), Poisson thinning gives exactly `Poi(Q_{ij})` children of
type `j`, independent over `j`: this is the law of Definition 5.1 (children ordered), and the
underlying unlabelled tree has law `ν`, as the paper observes after Definition 5.1. -/
noncomputable def mgwLaw (p : SBMParams r) : Measure (LTData r) :=
  (gwLaw p.d).prod ((piPMF p).toMeasure.prod
    (Measure.infinitePi (fun _ : List ℕ => Measure.pi (fun i : Fin r => (kernelPMF p i).toMeasure))))


end BetheKS


