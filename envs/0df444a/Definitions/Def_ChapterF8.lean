-- Prove2me | Definitions.Def_ChapterF8
-- name    : ChapterF8
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T04:49:12.965186+00:00
-- url     : https://prove2.me/theorems/8c54064e-bcc8-4428-9f14-98a5d3774d5b
-- title:
--   Chapter F8
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterF8.lean`): generated def bundle for ChapterF8. See BookProof/ChapterF8.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterF8.lean

import Definitions.Def_ChapterF1
import Mathlib


/-!
# Chapter F8 — Tomographic Subspace Recovery: the offline compilation
(plan Part F.3, roadmap §10)

`QFM.tex` §10 describes the *Tomographic Subspace Recovery* pipeline.  Its
offline stage compiles the raw corpus into two objects that the online stage then
uses without ever touching the corpus again:

* a **two-level sketch** `S₂ ∘ S₁`, where `S₁ : ℝ^d → ℝ^k` hashes raw coordinates
  into `k ≪ d` features and `S₂ : ℝ^k → Fock(K₂)` places the features on `k`
  distinct modes of a `K₂`-mode Fock space (`K₂ > k`), producing a
  **single-excitation** state; and
* an **operator basis** of the reduced `m`-dimensional Krylov space, consisting
  of `m²` matrix units, into which all raw-coordinate observables are
  pre-projected.

The point of the construction is a cost statement: the corpus size `M` occurs
only in the offline stage, so the online cost carries **no** `M` term.

## Deliverables

* `featureHash` (`S₁`) and `fockEmbed` (`S₂`), `singleExcitation` — the
  single-excitation subspace of the `K₂`-mode Fock space;
* `fockEmbed_mem_singleExcitation`, `twoLevelHash_total` — `S₂ ∘ S₁` is a
  well-defined map of *every* raw vector into the single-excitation subspace;
* `featureHash_decodes` — the sketch is lossless on the feature layer: reading
  the mode `g j` of `S₂ y` returns the feature `y j` (for an injective mode
  assignment `g`), and `twoLevelHash_decodes` composes this with `S₁`;
* `offline_operatorBasis` — the `m²` pre-projected matrix units span the whole
  operator space `Hom(ℂ^m, ℂ^m)`, so the offline basis is complete;
* `online_cost_independent_of_M` — the corpus size enters only through the
  offline term: changing `M` changes the total cost exactly by the change of the
  offline cost;
* `tsr_offline_compiles` — **headline**: the offline stage produces the sketched
  single-excitation embedding *and* a complete `m²` operator basis, and the
  online cost is `M`-free.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

open scoped BigOperators

namespace BookProof.ChapterF8

/-! ## The two-level sketch -/

/-- Occupation vectors of a `K`-mode bosonic Fock space. -/
abbrev Occ (K : ℕ) := Fin K →₀ ℕ

/-- The `K`-mode Fock space, spanned by occupation-number basis states. -/
abbrev FockSpace (K : ℕ) := Occ K →₀ ℂ

/-- The **single-excitation subspace**: the span of the states `|1_a⟩` carrying
exactly one boson, in mode `a`. -/
def singleExcitation (K : ℕ) : Submodule ℂ (FockSpace K) :=
  Submodule.span ℂ {v | ∃ a : Fin K, v = Finsupp.single (Finsupp.single a 1) (1 : ℂ)}

/-- **`S₁` — the raw→feature hash.**  Raw coordinate `i` is added into feature
bucket `h i`; the feature dimension `k` is far below the raw dimension `d`. -/
def featureHash {d k : ℕ} (h : Fin d → Fin k) (x : Fin d → ℝ) : Fin k → ℝ :=
  fun j => ∑ i ∈ Finset.univ.filter (fun i => h i = j), x i

/-- **`S₂` — the feature→Fock embedding.**  Feature `j` is placed, with its own
amplitude, on the mode `g j` of the `K₂`-mode Fock space; `g` is injective, so
distinct features occupy distinct modes (`K₂ > k`). -/
def fockEmbed {k K : ℕ} (g : Fin k → Fin K) (y : Fin k → ℝ) : FockSpace K :=
  ∑ j : Fin k, (y j : ℂ) • Finsupp.single (Finsupp.single (g j) 1) (1 : ℂ)

/-- The composite two-level sketch `S₂ ∘ S₁`. -/
def twoLevelHash {d k K : ℕ} (h : Fin d → Fin k) (g : Fin k → Fin K)
    (x : Fin d → ℝ) : FockSpace K :=
  fockEmbed g (featureHash h x)









/-! ## The offline operator basis -/

/-- The `m²` matrix units of the reduced Krylov space — the operator basis into
which all raw-coordinate observables are pre-projected offline. -/
def operatorBasis (m : ℕ) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  Set.range fun p : Fin m × Fin m => Matrix.single p.1 p.2 (1 : ℂ)





/-! ## The cost split -/

/-- The offline cost: the only stage that touches the corpus of size `M`. -/
def offlineCost (M d k : ℕ) : ℕ := M * d * k

/-- The four online cost components of §10 — sketching `O(d·m²)`, hashing
`O(K₂ log k)`, Fock assembly `O(K₂·m²)` and the reduced generation `O(m²)`.
Note the absence of any `M`. -/
def onlineCost (d m K₂ k : ℕ) : ℕ :=
  d * m ^ 2 + K₂ * Nat.log 2 k + K₂ * m ^ 2 + m ^ 2

/-- The total pipeline cost. -/
def totalCost (M d m K₂ k : ℕ) : ℕ := offlineCost M d k + onlineCost d m K₂ k







end BookProof.ChapterF8

end


