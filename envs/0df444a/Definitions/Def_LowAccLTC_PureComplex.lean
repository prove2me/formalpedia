-- Prove2me | Definitions.Def_LowAccLTC_PureComplex
-- name    : LowAccLTC_PureComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:23.075473+00:00
-- url     : https://prove2.me/theorems/52f06b7d-af7b-413b-a3d7-7978966c96e3
-- title:
--   Weighted pure simplicial complexes (no colouring) and their spectral expansion
-- statement:
--   A **weighted pure simplicial complex** of rank $r$ is given by its top faces, each with a vertex set of size $r$ (distinct top faces having distinct vertex sets), and a strictly positive probability measure $\mu$ on the top faces; its faces are the subsets of top faces. Stars, conditional measures, weighted distances, distance of a code, induced local codes $C_s$ of $\mathrm{Tan}(X,C_0)$ and the $\lambda$-one-sided spectral HDX property are defined as for partite complexes, with the link $X_s$ inside a top face $t\supseteq s$ given by the vertices of $t\setminus s$. Every weighted partite complex gives a pure complex by forgetting the colouring.
--
--   This general setting is the one of Lemma 2.19, which does not assume partiteness.
--
--   **Formalization Note** $\lambda_2\le\lambda$ is written variationally, as for partite complexes.
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Definition 2.12 p.16 (PDF p.19), Definitions 2.16–2.17 pp.17–18 (PDF pp.20–21)

import Definitions.Def_LowAccLTC_PartiteComplex

namespace LowAccLTC

/-- A weighted pure simplicial complex of rank `r`, given by its top faces (Ben Yaacov–Dikstein–Liu,
manuscript sha256 04242e17…, Definition 2.12 and §2.3, p.16 = PDF p.19): `top t` is the vertex
set of the top face `t` (it has `r` vertices, and distinct top faces have distinct vertex sets),
and `μ` is a strictly positive probability measure on the top faces. The faces are the subsets of
top faces, so the complex is pure. No colouring is assumed. -/
structure PureComplex (r : ℕ) (V T : Type*) [Fintype T] where
  /-- vertex set of a top face -/
  top : T → Finset V
  card_top : ∀ t, (top t).card = r
  top_inj : Function.Injective top
  /-- probability measure on the top faces -/
  μ : T → ℝ
  μ_pos : ∀ t, 0 < μ t
  μ_sum : ∑ t, μ t = 1

namespace PureComplex

variable {r : ℕ} {V T A : Type*} [Fintype T] (X : PureComplex r V T)

/-- `s` is a face: it is contained in a top face. -/
def IsFace (s : Finset V) : Prop := ∃ t, s ⊆ X.top t

/-- `star(s) = {t ∈ X⟨r⟩ : s ⊆ t}` (p.16). -/
noncomputable def star (s : Finset V) : Finset T := by
  classical exact Finset.univ.filter (fun t => s ⊆ X.top t)

/-- `μ`-mass of a set of top faces. -/
noncomputable def mass (S : Finset T) : ℝ := ∑ t ∈ S, X.μ t

/-- Expectation over `t ∼ μ` conditioned on `s ⊆ t`. -/
noncomputable def Estar (s : Finset V) (F : T → ℝ) : ℝ :=
  (∑ t ∈ X.star s, X.μ t * F t) / X.mass (X.star s)

/-- Weighted relative distance on a set `S` of top faces (as `PartiteComplex.wdist`). -/
noncomputable def wdist (S : Finset T) (f g : T → A) : ℝ := by
  classical exact (∑ t ∈ S.filter (fun t => f t ≠ g t), X.μ t) / X.mass S

/-- The code `C` has distance at least `δ` on the view `S` (lower-bound semantics). -/
def HasDistAtLeast (S : Finset T) (C : Set (T → A)) (δ : ℝ) : Prop :=
  ∀ c ∈ C, ∀ c' ∈ C, (∃ t ∈ S, c t ≠ c' t) → δ ≤ X.wdist S c c'

/-- The induced local code `C_s` of `Tan(X, C₀)` (Definition 2.17, pp.17–18): words on `star(s)`
whose restriction to `star(u)` lies in `C₀(u)` for every co-rank-one face `u ⊇ s`. -/
def localCode (C₀ : (u : Finset V) → Set (X.star u → A)) (s : Finset V) : Set (T → A) :=
  {h | ∀ u, X.IsFace u → u.card + 1 = r → s ⊆ u → (fun x : X.star u => h x.1) ∈ C₀ u}

/-- Uniform average of `F` over the vertices of `t ∖ s` (the vertex law of the link `X_s` inside
the top face `t`). -/
noncomputable def linkVertAvg (s : Finset V) (t : T) (F : V → ℝ) : ℝ := by
  classical exact avg (X.top t \ s) F

/-- Uniform average of `F` over the ordered pairs of distinct vertices of `t ∖ s` (the ordered
edge law of the link `X_s` inside `t`). -/
noncomputable def linkPairAvg (s : Finset V) (t : T) (F : V → V → ℝ) : ℝ := by
  classical exact avg (X.top t \ s).offDiag (fun uv => F uv.1 uv.2)

/-- `X` is a `λ`-one-sided spectral HDX (Definition 2.16, p.17; Definition 2.7, p.15): for every
face `s` with `|s| ≤ r - 2`, the underlying graph of the link `X_s` with its induced measure
(vertex: `t ∼ μ` conditioned on `s ⊆ t`, then a uniform vertex of `t ∖ s`; ordered edge: a uniform
ordered pair of distinct vertices of `t ∖ s`) has `λ₂ ≤ λ`.

**Formalization Note.** `λ₂ ≤ λ` is written variationally: `E_{(u,v)} g(u) g(v) ≤ λ E_v g(v)²` for
every `g` of mean `0` under the vertex law (Courant–Fischer for the self-adjoint random-walk
operator). The condition `λ ∈ [0,1]` is not bundled. -/
def IsOneSidedLocalSpectral (lam : ℝ) : Prop :=
  ∀ s, X.IsFace s → s.card + 2 ≤ r → ∀ g : V → ℝ,
    X.Estar s (fun t => X.linkVertAvg s t g) = 0 →
    X.Estar s (fun t => X.linkPairAvg s t (fun u v => g u * g v))
      ≤ lam * X.Estar s (fun t => X.linkVertAvg s t (fun v => g v ^ 2))

end PureComplex

/-- A weighted pure `r`-partite complex, forgetting its colouring (the faces, stars and measure are
the same). -/
noncomputable def PartiteComplex.toPure {r : ℕ} {V T : Type*} [Fintype T]
    (X : PartiteComplex r V T) : PureComplex r V T where
  top := X.top
  card_top t := by
    classical
    unfold PartiteComplex.top PartiteComplex.face
    rw [Finset.card_image_of_injective _ (fun i j h => by
      have := congrArg X.col h; rwa [X.col_vert, X.col_vert] at this)]
    simp
  top_inj := by
    classical
    intro t t' h
    apply X.vert_inj
    funext c
    have hm : X.vert t c ∈ X.top t := by
      unfold PartiteComplex.top PartiteComplex.face; exact Finset.mem_image.mpr ⟨c, by simp, rfl⟩
    rw [h] at hm
    unfold PartiteComplex.top PartiteComplex.face at hm
    obtain ⟨c', _, hc'⟩ := Finset.mem_image.mp hm
    have hcol := congrArg X.col hc'
    rw [X.col_vert, X.col_vert] at hcol
    subst hcol
    exact hc'.symm
  μ := X.μ
  μ_pos := X.μ_pos
  μ_sum := X.μ_sum

end LowAccLTC


