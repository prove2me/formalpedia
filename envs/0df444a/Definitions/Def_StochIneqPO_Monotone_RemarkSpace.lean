-- Prove2me | Definitions.Def_StochIneqPO_Monotone_RemarkSpace
-- name    : StochIneqPO_Monotone_RemarkSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:10:35.579468+00:00
-- url     : https://prove2.me/theorems/f13eed12-fb74-4a1e-8298-24f7184db3e5
-- title:
--   Remarks after Theorem 6, p. 909 — the subset {xₙ} ∪ {z} ∪ {yₙ} of ℝ² with the linear order xₙ < yₙ < xₙ₊₁ < z
-- statement:
--   This is the "pathological example" of the Remarks following Theorem 6. Let
--
--   $$
--   E=\Bigl\{x_n=\bigl(1-\tfrac1n,0\bigr) : n=1,2,\dots\Bigr\}\cup\{z=(1,0)\}\cup\{y_n=(n,1) : n=1,2,\dots\}\subseteq\mathbb R^2,
--   $$
--
--   with the metric induced by that of $\mathbb R^2$ and the linear ordering
--
--   $$
--   x_n<y_n<x_{n+1}<z\qquad\text{for all } n .
--   $$
--
--   The ordering is realised by a rank $r:\mathbb R^2\to\mathbb R$, $r(a,0)=a$ and $r(b,1)=1-1/(b+\tfrac12)$, so that $r(x_n)=1-\tfrac1n$, $r(y_n)=1-\tfrac1{n+1/2}$, $r(z)=1$; $r$ is injective on $E$, and $p\le q$ is defined as $r(p)\le r(q)$. The points $x_n$, $y_n$, $z$ are also named as elements of the space.
--
--   The example shows that condition (17) can fail in a Polish space with a closed partial ordering, so that in Theorem 6 convergence in probability of a nondecreasing sequence does not in general imply its almost sure convergence.
--
--   **Formalization Note** The space is a type synonym of the subtype $E\subseteq\mathbb R\times\mathbb R$, so it does not inherit the coordinatewise order of $\mathbb R\times\mathbb R$; its order is pulled back along $r$ (the file contains the short injectivity proof needed to define it). Mathlib's metric on $\mathbb R\times\mathbb R$ is the maximum metric, not the Euclidean one; the two are equivalent and induce the same topology and the same Cauchy sequences, and every property of the example (closedness, completeness, closedness of the order, failure of (17)) is a property of the topology or the uniformity only. The Lean index $k\in\mathbb N$ corresponds to the paper's $n=k+1$. The Borel $\sigma$-algebra is also put on the space so that it meets the paper's standing assumption.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Remarks after Theorem 6, p. 909 (PDF p. 11)

import Mathlib

namespace StochIneqPO.Monotone

/-- The point `xₙ = (1 - 1/n, 0)` of the Remarks' example (p. 909); Lean index `k` is the paper's
`n = k + 1`. -/
noncomputable def remarkX (k : ℕ) : ℝ × ℝ := (1 - 1 / ((k : ℝ) + 1), 0)

/-- The point `yₙ = (n, 1)` of the Remarks' example (p. 909); Lean index `k` is the paper's
`n = k + 1`. -/
def remarkY (k : ℕ) : ℝ × ℝ := ((k : ℝ) + 1, 1)

/-- The point `z = (1, 0)` of the Remarks' example (p. 909). -/
def remarkZ : ℝ × ℝ := (1, 0)

/-- The set `E = {xₙ} ∪ {z} ∪ {yₙ} ⊆ ℝ²` of the Remarks' example (p. 909). -/
def remarkSet : Set (ℝ × ℝ) := Set.range remarkX ∪ {remarkZ} ∪ Set.range remarkY

/-- A rank on `ℝ²` whose restriction to `remarkSet` is injective and realizes the paper's linear
ordering `xₙ < yₙ < xₙ₊₁ < z`: `rank (a, 0) = a` (so `rank xₙ = 1 - 1/n`, `rank z = 1`) and
`rank (b, 1) = 1 - 1/(b + 1/2)` (so `rank yₙ = 1 - 1/(n + 1/2)`). -/
noncomputable def remarkRank (p : ℝ × ℝ) : ℝ := if p.2 = 0 then p.1 else 1 - 1 / (p.1 + 1 / 2)

theorem remarkRank_injOn : Set.InjOn remarkRank remarkSet := by
  have hy : ∀ k : ℕ, remarkRank (remarkY k) = 1 - 1 / ((k : ℝ) + 3 / 2) := by
    intro k; simp only [remarkRank, remarkY]; norm_num; ring_nf
  have hx : ∀ k : ℕ, remarkRank (remarkX k) = 1 - 1 / ((k : ℝ) + 1) := by
    intro k; simp [remarkRank, remarkX]
  have hz : remarkRank remarkZ = 1 := by simp [remarkRank, remarkZ]
  have pos1 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have pos2 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 3 / 2 := fun k => by positivity
  rintro p ((⟨k, rfl⟩ | rfl) | ⟨k, rfl⟩) q ((⟨m, rfl⟩ | rfl) | ⟨m, rfl⟩) h
  · rw [hx, hx] at h
    have h1 : (k : ℝ) + 1 = (m : ℝ) + 1 := by
      have := pos1 k; have := pos1 m; field_simp at h; linarith
    have : k = m := by exact_mod_cast (by linarith : (k : ℝ) = m)
    rw [this]
  · rw [hx, hz] at h; have := pos1 k; field_simp at h; linarith
  · exfalso; rw [hx, hy] at h
    have := pos1 k; have := pos2 m
    have h2 : (k : ℝ) + 1 = (m : ℝ) + 3 / 2 := by field_simp at h; linarith
    have h4 : 2 * k = 2 * m + 1 := by
      exact_mod_cast (by push_cast; linarith : ((2 * k : ℕ) : ℝ) = ((2 * m + 1 : ℕ) : ℝ))
    omega
  · rw [hz, hx] at h; have := pos1 m; field_simp at h; linarith
  · rfl
  · rw [hz, hy] at h; have := pos2 m; field_simp at h; linarith
  · exfalso; rw [hy, hx] at h
    have := pos1 m; have := pos2 k
    have h2 : (m : ℝ) + 1 = (k : ℝ) + 3 / 2 := by field_simp at h; linarith
    have h4 : 2 * m = 2 * k + 1 := by
      exact_mod_cast (by push_cast; linarith : ((2 * m : ℕ) : ℝ) = ((2 * k + 1 : ℕ) : ℝ))
    omega
  · rw [hy, hz] at h; have := pos2 k; field_simp at h; linarith
  · rw [hy, hy] at h
    have h1 : (k : ℝ) + 3 / 2 = (m : ℝ) + 3 / 2 := by
      have := pos2 k; have := pos2 m; field_simp at h; linarith
    have : k = m := by exact_mod_cast (by linarith : (k : ℝ) = m)
    rw [this]

/-- The Remarks' Polish space (p. 909): `remarkSet ⊆ ℝ²` with the subspace metric of `ℝ × ℝ`
and the linear ordering `xₙ < yₙ < xₙ₊₁ < z` pulled back along `remarkRank`. It is a type synonym
of the subtype, so the product order of `ℝ × ℝ` is **not** used. -/
def RemarkSpace : Type := remarkSet

noncomputable instance : MetricSpace RemarkSpace := inferInstanceAs (MetricSpace remarkSet)

instance : MeasurableSpace RemarkSpace := inferInstanceAs (MeasurableSpace remarkSet)

instance : BorelSpace RemarkSpace := inferInstanceAs (BorelSpace remarkSet)

noncomputable instance : LinearOrder RemarkSpace :=
  LinearOrder.lift' (fun p : remarkSet => remarkRank p.1)
    (fun p q h => Subtype.ext (remarkRank_injOn p.2 q.2 h))

/-- `xₙ` as a point of `RemarkSpace` (paper's `n = k + 1`). -/
noncomputable def RemarkSpace.x (k : ℕ) : RemarkSpace := ⟨remarkX k, Or.inl (Or.inl ⟨k, rfl⟩)⟩

/-- `yₙ` as a point of `RemarkSpace` (paper's `n = k + 1`). -/
def RemarkSpace.y (k : ℕ) : RemarkSpace := ⟨remarkY k, Or.inr ⟨k, rfl⟩⟩

/-- `z` as a point of `RemarkSpace`. -/
def RemarkSpace.z : RemarkSpace := ⟨remarkZ, Or.inl (Or.inr rfl)⟩

end StochIneqPO.Monotone


