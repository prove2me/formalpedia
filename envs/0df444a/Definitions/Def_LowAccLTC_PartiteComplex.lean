-- Prove2me | Definitions.Def_LowAccLTC_PartiteComplex
-- name    : LowAccLTC_PartiteComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:41.21446+00:00
-- url     : https://prove2.me/theorems/8165348e-e367-4cc2-96ad-50e62a5e09b9
-- title:
--   Weighted pure $r$-partite simplicial complexes, stars and induced measures
-- statement:
--   A **weighted pure $r$-partite simplicial complex** $(X,\mu)$ of rank $r$ is given by a finite set $X\langle r\rangle$ of **top faces**, a set of vertices with a **colour** map $\mathrm{col}$ to $[r]$, and for every top face $t$ and colour $i$ the vertex of $t$ of colour $i$; distinct top faces have distinct vertex sets. The faces of $X$ are the subsets of top faces, so $X$ is pure. The complex carries a probability measure $\mu$ on its top faces that is strictly positive.
--
--   For a face $s$, the **star** is $\mathrm{star}(s)=\{t\in X\langle r\rangle : s\subseteq t\}$, and $\mu_s$ is $\mu$ conditioned on $\mathrm{star}(s)$. The measure on $k$-faces is induced by sampling $t\sim\mu$ and a uniformly random $k$-subset of its vertices (equivalently of its colours):
--   $$\mu_k(s)=\binom{r}{k}^{-1}\sum_{t\supseteq s}\mu(t).$$
--   The module also defines the uniform average $\mathrm{avg}_A F$ over a finite set, the real indicator of a proposition, and, for a face $s$ and a top face $t\supseteq s$, the free colours of $t$ not used by $s$ and the ordered pairs of distinct free colours: these give the vertex and edge laws of the link $X_s$.
--
--   This is the ambient object of every result of the paper: HDX codes, the vertex test and the $j$-agreement test are all defined on it.
--
--   **Formalization Note** Colours are `Fin r`; the paper's colour $i$ is $i-1$. Elements of the vertex type that lie in no top face are not vertices of the complex and never appear in a face, star or measure.
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), §2.3, Definition 2.12 and 'Partite complexes', p.16 (PDF p.19)

import Mathlib

namespace LowAccLTC

/-- A weighted pure `r`-partite simplicial complex of rank `r`, given by its top faces
(Ben Yaacov–Dikstein–Liu, manuscript sha256 04242e17…, §2.3, p.16 = PDF p.19, Definition 2.12 and
"Partite complexes").

`T` is the (finite) set of top faces, `V` a carrier of vertices with colour map `col : V → Fin r`,
and `vert t i` is the vertex of colour `i` of the top face `t`. The faces of the complex are the
subsets of the vertex sets of top faces, so the complex is pure by construction. `μ` is the
strictly positive probability measure on top faces.

**Formalization Note.** Colours are `Fin r`; the paper's colour `i ∈ [r]` is `i - 1`.
`vert_inj` says that distinct top faces have distinct vertex sets (a simplicial complex, not a
multi-hypergraph). Elements of `V` that lie in no top face are not vertices of the complex; they
never occur in any face, star or induced measure. -/
structure PartiteComplex (r : ℕ) (V T : Type*) [Fintype T] where
  /-- colour of a vertex -/
  col : V → Fin r
  /-- the vertex of colour `i` of the top face `t` -/
  vert : T → Fin r → V
  col_vert : ∀ t i, col (vert t i) = i
  vert_inj : Function.Injective vert
  /-- probability measure on the top faces -/
  μ : T → ℝ
  μ_pos : ∀ t, 0 < μ t
  μ_sum : ∑ t, μ t = 1

/-- Real indicator of a proposition. -/
noncomputable def ind (P : Prop) : ℝ := by classical exact if P then 1 else 0

/-- Uniform average of `F` over a finite set `A` (`0` when `A = ∅`). -/
noncomputable def avg {α : Type*} (A : Finset α) (F : α → ℝ) : ℝ := (∑ a ∈ A, F a) / A.card

namespace PartiteComplex

variable {r : ℕ} {V T : Type*} [Fintype T] (X : PartiteComplex r V T)

/-- The face of the top face `t` with colour set `I`. -/
noncomputable def face (t : T) (I : Finset (Fin r)) : Finset V := by
  classical exact I.image (X.vert t)

/-- The vertex set of the top face `t`. -/
noncomputable def top (t : T) : Finset V := X.face t Finset.univ

/-- `s` is a face of the complex: it is contained in a top face. -/
def IsFace (s : Finset V) : Prop := ∃ t, s ⊆ X.top t

/-- The vertex set of the complex. -/
noncomputable def vertices : Finset V := by
  classical exact Finset.univ.biUnion X.top

/-- `star(s) = {t ∈ X⟨r⟩ : s ⊆ t}` (§2.3, p.16). -/
noncomputable def star (s : Finset V) : Finset T := by
  classical exact Finset.univ.filter (fun t => s ⊆ X.top t)

/-- `μ`-mass of a set of top faces. -/
noncomputable def mass (S : Finset T) : ℝ := ∑ t ∈ S, X.μ t

/-- Expectation over a top face `t ∼ μ`. -/
noncomputable def E (F : T → ℝ) : ℝ := ∑ t, X.μ t * F t

/-- Expectation over a top face `t ∼ μ` conditioned on `s ⊆ t` (the measure `μ_s` of the link,
§2.3, p.16). -/
noncomputable def Estar (s : Finset V) (F : T → ℝ) : ℝ :=
  (∑ t ∈ X.star s, X.μ t * F t) / X.mass (X.star s)

/-- The colours of the top face `t` not occupied by `s` (for `t ∈ star(s)`, the colours of
the link vertices of `s` inside `t`). -/
noncomputable def freeColors (s : Finset V) (t : T) : Finset (Fin r) := by
  classical exact Finset.univ.filter (fun i => X.vert t i ∉ s)

/-- Ordered pairs of distinct free colours. -/
noncomputable def freePairs (s : Finset V) (t : T) : Finset (Fin r × Fin r) := by
  classical exact (X.freeColors s t ×ˢ X.freeColors s t).filter (fun ij => ij.1 ≠ ij.2)

end PartiteComplex

end LowAccLTC


