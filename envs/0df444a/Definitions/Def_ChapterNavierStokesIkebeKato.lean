-- Prove2me | Definitions.Def_ChapterNavierStokesIkebeKato
-- name    : ChapterNavierStokesIkebeKato
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:40:54.18999+00:00
-- url     : https://prove2.me/theorems/336515a8-fa38-4d78-adc2-267536425fd1
-- title:
--   This module supplies the *analytic* input that the Faris–Lavine route to essential self-adjointness of the Navier–Stokes ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesIkebeKato`, source chapter `BookProof/ChapterNavierStokesIkebeKato.lean`).
--
--   This module supplies the *analytic* input that the Faris–Lavine route to essential self-adjointness of the Navier–Stokes Hamiltonian needs, and which was previously carried as a hypothesis: a comparison operator `N` which
--
--   * is self-adjoint on a natural maximal domain, * is positive (indeed `N ≥ I` for the Navier–Stokes symbol), * has `N + 1` surjective, and * admits the finite-mode states (the momentum-representation stand-in for `C_c^∞`) as an operator core in the graph norm.
--
--   In the momentum representation the one-particle comparison operator `n = ∑ᵢ πᵢ² + ∑ᵢ Vᵢ² + I` is multiplication by the classical symbol `σ(k) = ∑ᵢ pᵢ(k)² + ∑ᵢ qᵢ(k)² + 1` (`BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_eq`). This is the momentum-space form of the Ikebe–Kato theorem for `−Δ + V` with `V ≥ 0`: the operator is essentially self-adjoint on the compactly supported core, and self-adjoint on its maximal domain.
--
--   * `maxDom c` and `diagMax c` — multiplication by the real symbol `c` on its *maximal* domain in `ℓ²(ι)`, i.e. all states whose image is again square summable. * `diagMax_symmetricOn`, `diagMax_hasSum_quadForm`, `diagMax_quadForm_nonneg`, `diagMax_quadForm_ge_norm_sq` — symmetry and positivity of the quadratic form. * `diagMax_add_one_surjective` — `N + 1` maps the maximal domain **onto** `ℓ²(ι)` for a non-negative symbol; this is the one consequence of self-adjointness of `N` that the Faris–Lavine argument uses. * `exists_finiteModes_graph_approx` — the finite-mode states are a **core**: every state of the maximal domain is approximated in the graph norm of `N` by finite truncations. * `diagMax_essentiallySelfAdjointOn` — `N` is essentially self-adjoint on its maximal domain, and `ikebeKato_momentum` — **essentially self-adjoint already on the finite-mode core**. This is the Ikebe–Kato-type statement, proved here, not assumed. * `essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds` — the payoff: *any* symmetric operator `H` on the maximal domain of a non-negative symbol which is relatively bounded by `N` and whose form commutator with `N` is dominated by `N` is essentially self-adjoint on the finite-mode core. The Faris–Lavine criterion is **not** a hypothesis here: it is the theorem `BookProof.FarisLavine.essentiallySelfAdjointOn_core_of_farisLavine`, proved in this project. * `nsComparison_*` — the specialisation to the Navier–Stokes comparison symbol `∑ᵢ pᵢ² + ∑ᵢ qᵢ² + 1`, together with `nsComparison_restrict_eq` identifying the restriction of `diagMax` to the finite-mode core with the operator `ComparisonData.comparison` of `BookProof.ChapterNavierStokesFarisLavineLift`. * `ns_hamiltonian_essentiallySelfAdjointOn_core` — the assembled one-particle statement: the Navier–Stokes Hamiltonian of the fiber momentum representation is essentially self-adjoint on the finite-mode core as soon as it satisfies the two Faris–Lavine inequalities relative to `n`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesIkebeKato.lean

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDeficiency

/-!
# The Ikebe–Kato input in the momentum representation

This module supplies the *analytic* input that the Faris–Lavine route to
essential self-adjointness of the Navier–Stokes Hamiltonian needs, and which was
previously carried as a hypothesis: a comparison operator `N` which

* is self-adjoint on a natural maximal domain,
* is positive (indeed `N ≥ I` for the Navier–Stokes symbol),
* has `N + 1` surjective, and
* admits the finite-mode states (the momentum-representation stand-in for
  `C_c^∞`) as an operator core in the graph norm.

In the momentum representation the one-particle comparison operator
`n = ∑ᵢ πᵢ² + ∑ᵢ Vᵢ² + I` is multiplication by the classical symbol
`σ(k) = ∑ᵢ pᵢ(k)² + ∑ᵢ qᵢ(k)² + 1`
(`BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_eq`).  This is the
momentum-space form of the Ikebe–Kato theorem for `−Δ + V` with `V ≥ 0`: the
operator is essentially self-adjoint on the compactly supported core, and
self-adjoint on its maximal domain.

## Contents

* `maxDom c` and `diagMax c` — multiplication by the real symbol `c` on its
  *maximal* domain in `ℓ²(ι)`, i.e. all states whose image is again square
  summable.
* `diagMax_symmetricOn`, `diagMax_hasSum_quadForm`, `diagMax_quadForm_nonneg`,
  `diagMax_quadForm_ge_norm_sq` — symmetry and positivity of the quadratic form.
* `diagMax_add_one_surjective` — `N + 1` maps the maximal domain **onto** `ℓ²(ι)`
  for a non-negative symbol; this is the one consequence of self-adjointness of
  `N` that the Faris–Lavine argument uses.
* `exists_finiteModes_graph_approx` — the finite-mode states are a **core**: every
  state of the maximal domain is approximated in the graph norm of `N` by finite
  truncations.
* `diagMax_essentiallySelfAdjointOn` — `N` is essentially self-adjoint on its
  maximal domain, and `ikebeKato_momentum` — **essentially self-adjoint already on
  the finite-mode core**.  This is the Ikebe–Kato-type statement, proved here, not
  assumed.
* `essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds` — the payoff: *any*
  symmetric operator `H` on the maximal domain of a non-negative symbol which is
  relatively bounded by `N` and whose form commutator with `N` is dominated by `N`
  is essentially self-adjoint on the finite-mode core.  The Faris–Lavine criterion
  is **not** a hypothesis here: it is the theorem
  `BookProof.FarisLavine.essentiallySelfAdjointOn_core_of_farisLavine`, proved in
  this project.
* `nsComparison_*` — the specialisation to the Navier–Stokes comparison symbol
  `∑ᵢ pᵢ² + ∑ᵢ qᵢ² + 1`, together with `nsComparison_restrict_eq` identifying the
  restriction of `diagMax` to the finite-mode core with the operator
  `ComparisonData.comparison` of `BookProof.ChapterNavierStokesFarisLavineLift`.
* `ns_hamiltonian_essentiallySelfAdjointOn_core` — the assembled one-particle
  statement: the Navier–Stokes Hamiltonian of the fiber momentum representation
  is essentially self-adjoint on the finite-mode core as soon as it satisfies the
  two Faris–Lavine inequalities relative to `n`.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace IkebeKato

open LpNat FarisLavine

variable {ι : Type*}

/-- The Hilbert space `ℓ²(ι)` of the momentum representation. -/
noncomputable abbrev L2I (ι : Type*) := lp (fun _ : ι => ℂ) 2

/-! ## Square summability helpers -/







/-! ## The maximal domain of a multiplication operator -/

/-- **The maximal domain** of multiplication by the real symbol `c` in `ℓ²(ι)`:
the states whose product with the symbol is again square summable.  In the
momentum representation of a Schrödinger operator this is the natural (Sobolev)
domain of `−Δ + V`. -/
def maxDom (c : ι → ℝ) : Submodule ℂ (L2I ι) where
  carrier := {f : L2I ι | Memℓp (fun k => (c k : ℂ) * (f : ι → ℂ) k) 2}
  add_mem' := by
    intro f g hf hg
    have hfun : (fun k => (c k : ℂ) * ((f + g : L2I ι) : ι → ℂ) k)
        = (fun k => (c k : ℂ) * (f : ι → ℂ) k) + fun k => (c k : ℂ) * (g : ι → ℂ) k := by
      funext k
      simp only [lp.coeFn_add, Pi.add_apply]
      ring
    simp only [Set.mem_setOf_eq, hfun]
    exact hf.add hg
  zero_mem' := by
    have hfun : (fun k => (c k : ℂ) * ((0 : L2I ι) : ι → ℂ) k) = fun _ => (0 : ℂ) := by
      funext k
      simp
    simp only [Set.mem_setOf_eq, hfun]
    exact zero_memℓp
  smul_mem' := by
    intro a f hf
    have hfun : (fun k => (c k : ℂ) * ((a • f : L2I ι) : ι → ℂ) k)
        = a • fun k => (c k : ℂ) * (f : ι → ℂ) k := by
      funext k
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [Set.mem_setOf_eq, hfun]
    exact hf.const_smul a



/-- **The comparison operator on its maximal domain**: multiplication by `c`. -/
noncomputable def diagMax (c : ι → ℝ) : maxDom c →ₗ[ℂ] L2I ι where
  toFun f := ⟨fun k => (c k : ℂ) * ((f : L2I ι) : ι → ℂ) k, f.2⟩
  map_add' f g := by
    refine lp.ext (funext fun k => ?_)
    simp only [lp.coeFn_add, Pi.add_apply, Submodule.coe_add]
    ring
  map_smul' a f := by
    refine lp.ext (funext fun k => ?_)
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Submodule.coe_smul]
    ring

@[simp] theorem diagMax_coe (c : ι → ℝ) (f : maxDom c) (k : ι) :
    ((diagMax c f : L2I ι) : ι → ℂ) k = (c k : ℂ) * ((f : L2I ι) : ι → ℂ) k := rfl

/-- A finitely supported function lies in `ℓ²`. -/
theorem memLpTwo_of_finite_support {g : ι → ℂ} (h : (Function.support g).Finite) :
    Memℓp g 2 := by
  classical
  refine memLpTwo_of_summable_normSq (summable_of_ne_finset_zero (s := h.toFinset) ?_)
  intro k hk
  have : g k = 0 := by
    by_contra hne
    exact hk (h.mem_toFinset.mpr hne)
  simp [this]

/-! ## Symmetry and positivity -/









/-! ## Surjectivity of `N + 1` -/



/-! ## The finite-mode core -/

/-- Finitely supported states lie in every maximal domain. -/
theorem finiteModes_le_maxDom (c : ι → ℝ) : lpFiniteModes ι ≤ maxDom c := by
  intro f hf
  refine memLpTwo_of_finite_support (Set.Finite.subset (mem_lpFiniteModes.mp hf) ?_)
  intro k hk
  simp only [Function.mem_support] at hk ⊢
  intro h0
  exact hk (by rw [h0, mul_zero])









/-! ## Essential self-adjointness: the Ikebe–Kato input, proved -/







/-! ## The payoff: essential self-adjointness of the Hamiltonian -/



end IkebeKato

end BookProof.NavierStokesFlow


