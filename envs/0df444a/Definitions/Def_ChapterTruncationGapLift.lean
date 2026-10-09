-- Prove2me | Definitions.Def_ChapterTruncationGapLift
-- name    : ChapterTruncationGapLift
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-09T08:22:30.832295+00:00
-- url     : https://prove2.me/theorems/c0305dae-7568-4a0c-9375-e4ab0a226267
-- title:
--   Chapter TruncationGapLift
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterTruncationGapLift.lean`): generated def bundle for ChapterTruncationGapLift. See BookProof/ChapterTruncationGapLift.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterTruncationGapLift.lean

import Definitions.Def_ChapterYangMillsFockGapChain
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Mathlib


/-!
# Chapter TruncationGapLift — from a certified *truncated* gap to the *infinite* operator

`CONSOLIDATED_PLAN.md`, QYM-1 **task 2**: "Prove the finite/truncated one-particle gap
certified by the bands lifts to the infinite one-particle operator and then (via `dGamma`)
to the outer-enclosed final Hamiltonian — the current certificate proves only the truncated
gap; the bridge is the specialist's analytic input."

This chapter supplies exactly that bridge, and is careful about what it costs.

## The two halves of the lift

Write `Vₘ = galerkinSpan b m` for the order-`m` truncation and
`Wₘ = tailSpan b m = span {b i | m ≤ i}` for its tail inside the finite-mode core
`D = finiteModeDomain b`.  The two are orthogonal and together span `D`
(`galerkinSpan_sup_tailSpan`, `inner_eq_zero_of_mem_galerkin_tail`), so every core vector
splits as `v = x + w` with `x ∈ Vₘ`, `w ∈ Wₘ` and `‖v‖² = ‖x‖² + ‖w‖²`.

* **The cheap half.**  If the truncated gap holds *uniformly in `m`* — the same `μ` at
  every order — then the core form gap follows with no analytic input at all, because every
  core vector already lies in some `Vₘ` (`gap_of_uniform_truncated_gap`).  This is the
  honest statement of what "the Ritz values are all above `μ`" gives you.

* **The real half.**  A certificate proves the truncated gap at *finitely many* orders — in
  practice at a single order `m`.  Lifting that to the core needs two further inputs, and
  they are the analytic content:
  1. **tail coercivity** `⟪w, H w⟫ ≥ μ‖w‖²` for `w ∈ Wₘ`, and
  2. a **coupling bound** `|Re ⟪x, H w⟫| ≤ ε‖x‖‖w‖` across the split.

  Then `⟪v, H v⟫ ≥ (μ − ε)‖v‖²` on the whole core (`gap_of_level_gap_and_tail`), by the
  block estimate `2‖x‖‖w‖ ≤ ‖x‖² + ‖w‖²`.  The decoupled case `ε = 0` is
  `gap_of_level_gap_and_tail_decoupled`.

Both inputs are genuinely needed: `quadForm_add_of_symmetricOn` is an *identity*, so a
coupling of size `ε > μ` cancels the whole gap, and without the tail bound the certificate
says nothing about the modes it never saw.  Nothing here manufactures either input.

## Deliverables

* `tailSpan` and its structure lemmas: `tailSpan_le_finiteModeDomain`,
  `galerkinSpan_sup_tailSpan`, `inner_eq_zero_of_mem_galerkin_tail`,
  `norm_add_sq_of_galerkin_tail`, `exists_galerkin_tail_decomp`;
* `quadForm_add_of_symmetricOn` — the exact two-block expansion of the energy form;
* **`gap_of_uniform_truncated_gap`** — uniform truncated gap ⇒ core form gap;
* **`gap_of_level_gap_and_tail`** — one certified level + tail coercivity + coupling bound
  ⇒ core form gap `μ − ε`;
* `quadForm_ge_of_le_ritzInf_on` and `gap_of_le_ritzInf_and_tail` — the same with the
  truncated input in Ritz-value form, as a certificate delivers it;
* **`ym_fock_gap_of_truncated_gap_and_tail`** and
  **`ym_fock_mass_gap_of_truncated_gap_and_tail`** — the composition with the Yang–Mills
  `dΓ` chain: the certified order-`m` gap of the gauge-fixed one-particle Hamiltonian,
  together with the two analytic inputs, gives the nested-Fock conclusion for the final
  Hamiltonian `dΓ(H₁)`;
* `ym_fock_gap_of_band_and_tail` — the same starting from a certified band whose lower end
  is at least `μ`, so no displayed Ritz value is ever read as a lower bound.

## Honest boundary

The tail coercivity and the coupling bound are **hypotheses**, not conclusions: they are the
named analytic input QYM-1 task 3 refers to, and they are not proved for the gauge-fixed
Yang–Mills one-particle operator here.  What is proved is that the certificate's truncated
gap plus those two inputs is *sufficient*, with the explicit constant `μ − ε`, and that no
step of the chain reads a numerical Ritz value as a lower bound.  No mass gap of the
physical Yang–Mills Hamiltonian is claimed.

Everything in this module is `sorry`-free and `axiom`-free.
-/

noncomputable section

namespace BookProof.TruncationGapLift

open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.BandEnclosure
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-! ## 1. The tail of a truncation -/

/-- **The tail subspace** of the order-`m` truncation: the span of the basis vectors the
order-`m` Galerkin space does *not* see.  A finite certificate says nothing about it. -/
def tailSpan (b : HilbertBasis ℕ ℂ F) (m : ℕ) : Submodule ℂ F :=
  Submodule.span ℂ (b '' {i | m ≤ i})


theorem tailSpan_le_finiteModeDomain (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    tailSpan b m ≤ finiteModeDomain b :=
  Submodule.span_mono (by rintro x ⟨i, _, rfl⟩; exact ⟨i, rfl⟩)


/-! ## 2. The block expansion of the energy form -/

variable {D : Submodule ℂ F}


/-! ## 3. The lift -/


/-! ## 4. The truncated input in Ritz form

A certificate delivers a *Ritz* bound at level `m`, not a form bound.  These two lemmas
convert. -/


/-! ## 5. The Yang–Mills instantiation: truncated gap ⇒ final Hamiltonian -/

variable (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)


/-! ## 6. Axiom audit -/

section Audit


end Audit

end BookProof.TruncationGapLift

end


