-- Prove2me | solution 1 for Apery.normalization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T14:22:47.860993+00:00
-- url     : https://prove2.me/submissions/723fe858-e8fd-4484-9913-723796cdfe7c

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# Normalisation (Propositions 5.1 and 5.2) — reduction to integrality and growth

This file proves the platform theorem `Apery.normalization`:

$$\exists m : \mathbb N \to \mathbb Q,\quad
  (\forall n,\ 0 < m\,n) \;\wedge\;
  (\forall^{\mathrm{f}} n,\ \exists Q \in \mathbb Z[X],\ Q \mapsto \mathbb Q = C(m\,n)\cdot F_n)
  \;\wedge\;
  \forall \varepsilon > 0,\ \forall^{\mathrm{f}} n,\ \log(m\,n) \le (A_{\mathrm{eff}}+\varepsilon) K^2,$$

from the two imported children `Apery.integral_mN` (Proposition 5.1: `mN n · F_n ∈ ℤ[X]` for
`n ≥ 1`) and `Apery.growth_mN` (Proposition 5.2: growth of the normaliser), with the witness
`mN` of `Apery/Norm.lean` and its positivity `mN_pos` proved here. A faithful port of
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/MainEstimate.lean`
(`normalization`) and `Apery/Norm.lean` (`mN_pos`).
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceNorm
import Theorems.Thm_Apery_integral_mN
import Theorems.Thm_Apery_growth_mN

set_option autoImplicit false

section Port0
/-!
# Normalisation of the Hankel determinants — reduction to integrality and growth

This file proves the platform theorem `Apery.normalization`:

`∃ m : ℕ → ℚ, (∀ n, 0 < m n) ∧
  (∀ᶠ n, ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = C (m n) * F n) ∧
  ∀ ε > 0, ∀ᶠ n, log (m n) ≤ (A_eff + ε) K²`

from the two children `Apery.integral_mN` (Proposition 5.1: `mN n · F_n ∈ ℤ[X]` for `n ≥ 1`)
and `Apery.growth_mN` (Proposition 5.2: the growth of the normaliser), with the witness
`mN` of `Apery/Norm.lean` and its positivity `mN_pos`. Ported from
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/MainEstimate.lean` and
`Apery/Norm.lean`.
-/

open Polynomial Filter Topology

namespace Apery

/-- Positivity of the normaliser (`Apery/Norm.lean`). -/
lemma mN_pos (n : ℕ) : 0 < mN n := by
  unfold mN
  apply Finset.prod_pos
  intro p hp
  have : 0 < p := (Finset.mem_filter.mp hp).2.pos
  exact zpow_pos (by exact_mod_cast this) _

/-- **Propositions 5.1 and 5.2**: a positive rational normalisation `m_K` with
`m_K F_K ∈ ℤ[X]` for all `n ≥ 1`, and `log m_K ≤ (A_eff + ε) K²` eventually. -/
theorem normalization :
    ∃ m : ℕ → ℚ, (∀ n, 0 < m n) ∧
      (∀ᶠ n in atTop, ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = C (m n) * F n) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, Real.log (m n) ≤ ((Aeff : ℝ) + ε) * Kr n ^ 2 :=
  ⟨mN, mN_pos, (eventually_ge_atTop 1).mono fun _ hn => integral_mN hn, growth_mN⟩

end Apery
end Port0


open Polynomial Filter Topology in
/-- The platform target `Apery.normalization`, restated at top level as `solution`. -/
theorem solution :
    ∃ m : ℕ → ℚ, (∀ n, 0 < m n) ∧
      (∀ᶠ n in atTop, ∃ Q : ℤ[X],
        Q.map (Int.castRingHom ℚ) = C (m n) * Apery.F n) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        Real.log (m n) ≤ ((Apery.Aeff : ℝ) + ε) * Apery.Kr n ^ 2 :=
  Apery.normalization
