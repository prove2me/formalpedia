-- Prove2me | Definitions.Def_SoftmaxAttnFD_Envelope
-- name    : SoftmaxAttnFD_Envelope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:36.053074+00:00
-- url     : https://prove2.me/theorems/36c6cfc2-a20c-4f45-aacb-4579b8af7213
-- title:
--   Envelope polytopes, general position and capped families
-- statement:
--   A source point is $y=(p,c)\in\mathbb Q^{d-1}\times\mathbb Q$, with affine function $f_y(u)=y\cdot(u,1)=u\cdot p+c$. A **family** consists of sources $\tilde y_s$ and $d$ cap points $\tilde c_h$. For a finite set $\Sigma'$ of sources, the **envelope polytope** is
--   $$P(\Sigma')=\{(u,z):\ f_{\tilde y_s}(u)\le z\ (s\in\Sigma'),\quad z\le f_{\tilde c_h}(u)\ (h\in[d])\},$$
--   and the envelope is $E_{\Sigma'}(u)=\max_{s\in\Sigma'}f_{\tilde y_s}(u)$.
--
--   Hyperplanes are in **general position** (Definition 6.1) if the normal vectors of any at most $d$ of them are linearly independent and no $d+1$ of them have a common point.
--
--   A family is **capped** over $\Sigma_0$ and the box $[-U,U]^{d-1}$ if:
--
--   1. the $|\Sigma_0|+d$ hyperplanes are in general position;
--   2. each nonempty $\Sigma'\subseteq\Sigma_0$ gives a bounded $P(\Sigma')$ with nonempty interior;
--   3. there is a height $Z$ strictly above all sources and strictly below all caps on the box.
--
--   These are the properties of the concrete perturbed family which Lemmas 6.7, 6.9 and 7.2 use. Lemma 6.5 shows that the concrete family has them.
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Definitions 5.2, 6.1, 6.4, pp.20, 23, 24; §A.7, p.44

import Mathlib

namespace SoftmaxAttnFD

/-- A source point `y = (p, c) ∈ ℚ^d` with `p ∈ ℚ^{d−1}` (arXiv:2611.06055, sha256 a60f7609…,
Definition 5.2, p.20: "For y = (p, c), we have f_y(u) = u · p + c"). -/
abbrev Src (d : ℕ) := (Fin (d - 1) → ℚ) × ℚ

/-- A point `(u, z)` of `ℝ^{d−1} × ℝ`. -/
abbrev Pt (d : ℕ) := (Fin (d - 1) → ℝ) × ℝ

/-- The affine function `y · (u, 1) = u · p + c`. -/
noncomputable def evalSrc {d : ℕ} (y : Src d) (u : Fin (d - 1) → ℝ) : ℝ :=
  ∑ i, u i * (y.1 i : ℝ) + (y.2 : ℝ)

/-- The rational family of an envelope: sources `src s` for natural indices `s`, and `d` caps. -/
structure Family (d : ℕ) where
  src : ℕ → Src d
  cap : Fin d → Src d

/-- A constraint index: a cap `h`, or a source `s`. -/
abbrev Con (d : ℕ) := Fin d ⊕ ℕ

/-- The point of a constraint. -/
def Family.con {d : ℕ} (F : Family d) : Con d → Src d
  | .inl h => F.cap h
  | .inr s => F.src s

/-- The constraint index is one of `P(Σ′)`: a cap, or a source in `Σ′`. -/
def IsConOf {d : ℕ} (S' : Finset ℕ) : Con d → Prop
  | .inl _ => True
  | .inr s => s ∈ S'

/-- The envelope polytope `P(Σ′) = {(u, z) : f̃_s(u) ≤ z (s ∈ Σ′), z ≤ g_h(u) (h ∈ [d])}`
(arXiv:2611.06055, §A.7, p.44). -/
def Family.polytope {d : ℕ} (F : Family d) (S' : Finset ℕ) : Set (Pt d) :=
  {x | (∀ s ∈ S', evalSrc (F.src s) x.1 ≤ x.2) ∧ ∀ h, x.2 ≤ evalSrc (F.cap h) x.1}

/-- The upper envelope `E_{Σ′}(u) = max_{s ∈ Σ′} f̃_s(u)` (Definition 6.4, p.24). -/
noncomputable def Family.envelope {d : ℕ} (F : Family d) (S' : Finset ℕ) (hS' : S'.Nonempty)
    (u : Fin (d - 1) → ℝ) : ℝ :=
  S'.sup' hS' fun s => evalSrc (F.src s) u

/-- The normal `(p, −1)` of the hyperplane `z = u · p + c`. -/
noncomputable def normalOf {d : ℕ} (y : Src d) : Pt d :=
  (fun i => (y.1 i : ℝ), -1)

/-- General position of the hyperplanes `z = y_t · (u, 1)` in `ℝ^d` (Definition 6.1, p.23): the normal
vectors of any at most `d` members are linearly independent, and no `d + 1` members have a common
point. -/
def GeneralPosition {d : ℕ} {ι : Type*} (y : ι → Src d) : Prop :=
  (∀ T : Finset ι, T.card ≤ d → LinearIndependent ℝ fun t : T => normalOf (y t)) ∧
    (∀ T : Finset ι, T.card = d + 1 →
      ¬ ∃ x : Pt d, ∀ t ∈ T, x.2 = evalSrc (y t) x.1)

/-- The sup-norm box `∥u∥_∞ ≤ U`. -/
def InBox {d : ℕ} (U : ℕ) (u : Fin (d - 1) → ℝ) : Prop := ∀ i, |u i| ≤ U

/-- A capped family over `Σ₀` and the box `[−U, U]^{d−1}`: the properties of the concrete perturbed
family of Definition 6.4 which Lemmas 6.7, 6.9 and 7.2 use.

1. The `|Σ₀| + d` hyperplanes are in general position (so every face is simple).
2. Every nonempty `Σ′ ⊆ Σ₀` gives a bounded `P(Σ′)` with nonempty interior.
3. A common height `Z` lies strictly above all sources and strictly below all caps on the box (so the
   lower boundary over the box is the graph of `E_{Σ′}`). -/
structure IsCappedFamily {d : ℕ} (F : Family d) (S₀ : Finset ℕ) (U : ℕ) : Prop where
  genPos : GeneralPosition fun t : Fin d ⊕ {s // s ∈ S₀} =>
    Sum.elim F.cap (fun s => F.src s.val) t
  bounded : ∀ S' : Finset ℕ, S'.Nonempty → S' ⊆ S₀ → Bornology.IsBounded (F.polytope S')
  interior_nonempty : ∀ S' : Finset ℕ, S'.Nonempty → S' ⊆ S₀ → (interior (F.polytope S')).Nonempty
  top : ∃ Z : ℝ, ∀ u : Fin (d - 1) → ℝ, InBox U u →
    (∀ s ∈ S₀, evalSrc (F.src s) u < Z) ∧ ∀ h, Z < evalSrc (F.cap h) u

end SoftmaxAttnFD


