-- Prove2me | Definitions.Def_IllCondRegMem_ColumnStrategy
-- name    : IllCondRegMem_ColumnStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:33.784123+00:00
-- url     : https://prove2.me/theorems/197f1a13-671f-4ce2-9304-0e3879a89501
-- title:
--   Column generation strategies, the spans $G_j,V_j$ and the event $P_GP_VP_G\not\succeq\rho P_G$
-- statement:
--   Fix $\ell,k\ge1$. In the **online column generation process**, for each $i\in[k]$ a unit vector $g_i\notin\mathrm{Span}(g_1,\dots,g_{i-1})$ is selected, possibly depending on $z_1,\dots,z_{\ell(i-1)}$, and then $\ell$ fresh Gaussian vectors $z_{\ell(i-1)+1},\dots,z_{\ell i}\sim\mathcal N(0,I_d)$ are drawn. For $j\le k$,
--   $$
--   G_j=\mathrm{Span}(g_1,\dots,g_j),\qquad V_j=\mathrm{Span}(z_1,\dots,z_{\ell j}),
--   $$
--   and $P_GP_VP_G\not\succeq\rho P_G$ means that the Loewner inequality $P_GP_VP_G\succeq\rho P_G$ fails, i.e. some $x\in G$ has $\langle x,P_Vx\rangle<\rho\|x\|^2$.
--
--   Lemma 7 shows that $G_k$ and $V_k$ are unlikely to be nearly orthogonal even though the $g_i$ may adapt to the earlier $z$'s; the masked adversary relies on this to keep its masking subspaces informative.
--
--   **Formalization Note** A strategy gives each $g_i$ as a measurable function of the whole Gaussian sequence that depends only on $z_t$ with $t<\ell i$ (rounds indexed from $0$); unit norm and $g_i\notin\mathrm{Span}(g_1,\dots,g_{i-1})$ hold for every realization.
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 7, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_IllCondRegMem_projMat

open MeasureTheory

namespace IllCondRegMem

/-- A **column generation strategy** for the online subspace generation process of Lemma 7.
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 7, p.9:
"For each i ∈ [k], select a unit vector g_i ∉ Span(g₁, …, g_{i−1}) possibly dependent on
z₁, …, z_{ℓ(i−1)}; then draw ℓ independent Gaussians z_{ℓ(i−1)+1}, …, z_{ℓi} iid∼ N(0, I_d)."

`g i z` is the `(i+1)`-st column (rounds indexed `0, …, k−1`), as a function of the whole Gaussian
sequence `z = (z_t)_{t < ℓk}`; it may depend only on `z_t` with `t < ℓ·i`.

**Formalization Note.** The non-anticipation field encodes "possibly dependent on
z₁, …, z_{ℓ(i−1)}"; each `g i` is measurable (so the events of Lemma 7 are events); the unit-norm
and `g_i ∉ Span(g₁, …, g_{i−1})` requirements hold for every realization. -/
structure ColumnStrategy (d ℓ k : ℕ) where
  /-- The selected unit vectors. -/
  g : Fin k → (Fin (ℓ * k) → Vec d) → Vec d
  /-- `g i` depends only on `z_t`, `t < ℓ·i`. -/
  nonanticipating : ∀ (i : Fin k) (z z' : Fin (ℓ * k) → Vec d),
    (∀ t : Fin (ℓ * k), t.val < ℓ * i.val → z t = z' t) → g i z = g i z'
  /-- Each selection is measurable. -/
  measurable : ∀ i, Measurable (g i)
  /-- Each selection is a unit vector. -/
  unit : ∀ i z, ‖g i z‖ = 1
  /-- Each selection is outside the span of the earlier ones. -/
  fresh : ∀ (i : Fin k) z, g i z ∉ Submodule.span ℝ {x | ∃ j : Fin k, j.val < i.val ∧ x = g j z}

/-- `G_j = Span(g₁, …, g_j)`. -/
def colSpanG {d ℓ k : ℕ} (S : ColumnStrategy d ℓ k) (z : Fin (ℓ * k) → Vec d) (j : ℕ) :
    Submodule ℝ (Vec d) :=
  Submodule.span ℝ {x | ∃ i : Fin k, i.val < j ∧ x = S.g i z}

/-- `V_j = Span(z₁, …, z_{ℓj})`. -/
def colSpanV {d ℓ k : ℕ} (z : Fin (ℓ * k) → Vec d) (j : ℕ) : Submodule ℝ (Vec d) :=
  Submodule.span ℝ {x | ∃ t : Fin (ℓ * k), t.val < ℓ * j ∧ x = z t}

/-- `P_G P_V P_G ⋡ ρ P_G`: the Loewner inequality `P_G P_V P_G ⪰ ρ P_G` fails, i.e. some
`x ∈ G` has `⟨x, P_V x⟩ < ρ‖x‖²`. -/
def NotDominates {d : ℕ} (G V : Submodule ℝ (Vec d)) (ρ : ℝ) : Prop :=
  ¬ ∀ x ∈ G, ρ * ‖x‖ ^ 2 ≤ inner ℝ x (V.starProjection x)

end IllCondRegMem


