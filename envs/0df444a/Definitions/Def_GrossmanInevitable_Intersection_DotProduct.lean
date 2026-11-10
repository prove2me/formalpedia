-- Prove2me | Definitions.Def_GrossmanInevitable_Intersection_DotProduct
-- name    : GrossmanInevitable_Intersection_DotProduct
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:02:55.436348+00:00
-- url     : https://prove2.me/theorems/b61f0461-7dfe-4087-9cfc-d9e866263f7d
-- title:
--   Intersection $a\cap b$, dot product $\langle a,b\rangle$, the relation Intersection, and $\mathrm{DP}_s$, $\mathrm{DP}_{\le s}$
-- statement:
--   Alice and Bob hold $a,b\in\{0,1\}^n$ (Lean: `Fin n → Bool`, `true` $=1$). Each vector is identified with the subset of $[n]$ of its $1$-entries (Lean: `Fin n`, indexed from $0$). Then
--   $$a\cap b=\{i\in[n]:a_i=b_i=1\},\qquad \langle a,b\rangle=\sum_{i=1}^n a_ib_i=|a\cap b|,$$
--   the dot product computed over the integers, not mod 2.
--
--   The relation $\mathrm{Intersection}=\{(a,b,i)\in\{0,1\}^n\times\{0,1\}^n\times[n]:a_i=b_i=1\}$ (Lean: `IntersectionRel n`) has as witnesses of $(a,b)$ the elements of $a\cap b$.
--
--   $\mathrm{DP}_s$ and $\mathrm{DP}_{\le s}$ are the decision problems whether $\langle a,b\rangle=s$ and whether $\langle a,b\rangle\le s$ (Lean: `dpEq n s`, `dpLe n s`, with values in `Bool`).
-- source:
--   Grossman, Grossman, Naor, Shulman, Inevitable Knowledge in Communication Complexity and the LOCAL Model, STOC 2027 submission (manuscript sha256 67c87783…), §1.2 'Highlight', pp. 4–5 (PDF 6–7); §3.2.1, p. 20 (PDF 22)

import Mathlib

namespace GrossmanInevitable.Intersection

/-- The intersection `a ∩ b = {i ∈ [n] : aᵢ = bᵢ = 1}` of `a, b ∈ {0, 1}ⁿ`, each vector identified
with the set of its `1`-entries (§1.2, printed p. 4 / PDF 6). `{0, 1}ⁿ` is `Fin n → Bool`
(`true` = 1) and `[n]` is `Fin n`, indexed from `0`. -/
def inter {n : ℕ} (a b : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a i = true ∧ b i = true)

/-- The dot product `⟨a, b⟩ = ∑ᵢ aᵢ bᵢ = |a ∩ b|`, over the integers (not mod 2)
(§1.2, printed pp. 4–5 / PDF 6–7). -/
def dot {n : ℕ} (a b : Fin n → Bool) : ℕ :=
  (inter a b).card

/-- The relation `Intersection = {(a, b, i) ∈ {0, 1}ⁿ × {0, 1}ⁿ × [n] : aᵢ = bᵢ = 1}` (§3.2.1,
printed p. 20 / PDF 22): the witnesses of `(a, b)` are the elements of `a ∩ b`. -/
def IntersectionRel (n : ℕ) : (Fin n → Bool) → (Fin n → Bool) → Fin n → Prop :=
  fun a b i => a i = true ∧ b i = true

/-- `DP_s`: the decision problem whether `⟨a, b⟩ = s` (§3.2.1, printed p. 20 / PDF 22). -/
def dpEq (n s : ℕ) : (Fin n → Bool) → (Fin n → Bool) → Bool :=
  fun a b => decide (dot a b = s)

/-- `DP_{≤s}`: the decision problem whether `⟨a, b⟩ ≤ s` (§3.2.1, printed p. 20 / PDF 22). -/
def dpLe (n s : ℕ) : (Fin n → Bool) → (Fin n → Bool) → Bool :=
  fun a b => decide (dot a b ≤ s)

end GrossmanInevitable.Intersection


