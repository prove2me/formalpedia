-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8InverseJet
-- name    : CK_GeneralCK_Certificates_E8InverseJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:58:03.036193+00:00
-- url     : https://prove2.me/theorems/48edef08-40c3-4f74-a01e-d0c36199fd44
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8InverseJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8InverseJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8InverseJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8InverseJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8InverseJet.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8InverseDerivatives

-- ===== source module GeneralCK.Certificates.E8InverseJet =====
section

/-!
# Exact finite inverse-jet checker for E8

Taylor coefficients are factorial-normalized.  Inverse differentiation is
therefore equivalent to checking that the finite composition coefficients of
`theta(q(x))` agree with `x`.  This rational kernel is executable at order 5
and order 17 without invoking native code.
-/

namespace GeneralCK.Certificates.E8InverseJet

def powCoeff (q : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n =>
      ∑ i ∈ Finset.range (n + 1), q i * powCoeff q k (n - i)

def composeCoeff (theta q : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), theta k * powCoeff q k n

def targetCoeff (k : ℕ) : ℚ := if k = 1 then 1 else 0

def coeffMatches (theta q : ℕ → ℚ) (k : ℕ) : Bool :=
  decide (composeCoeff theta q k = targetCoeff k)

def inverseJetCheck (order : ℕ) (theta q : ℕ → ℚ) : Bool :=
  (List.range (order + 1)).all (coeffMatches theta q)

/-- Acceptance exposes every checked composition coefficient. -/
theorem inverseJetCheck_sound {order : ℕ} {theta q : ℕ → ℚ}
    (h : inverseJetCheck order theta q = true) {k : ℕ} (hk : k ≤ order) :
    composeCoeff theta q k = targetCoeff k := by
  have hall := List.all_eq_true.mp h
  have hm : k ∈ List.range (order + 1) := List.mem_range.mpr (Nat.lt_succ_of_le hk)
  have := hall k hm
  simpa [coeffMatches, decide_eq_true_eq] using this

/-- Order-five specialization for the line-anchor jet. -/
theorem orderFiveCheck_sound {theta q : ℕ → ℚ}
    (h : inverseJetCheck 5 theta q = true) {k : ℕ} (hk : k ≤ 5) :
    composeCoeff theta q k = targetCoeff k :=
  inverseJetCheck_sound h hk

/-- The same checked kernel scales directly to the origin proof's order 17. -/
theorem orderSeventeenCheck_sound {theta q : ℕ → ℚ}
    (h : inverseJetCheck 17 theta q = true) {k : ℕ} (hk : k ≤ 17) :
    composeCoeff theta q k = targetCoeff k :=
  inverseJetCheck_sound h hk

end GeneralCK.Certificates.E8InverseJet

end


