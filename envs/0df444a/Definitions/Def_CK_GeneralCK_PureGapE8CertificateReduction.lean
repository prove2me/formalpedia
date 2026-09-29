-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8CertificateReduction
-- name    : CK_GeneralCK_PureGapE8CertificateReduction
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:50:20.863988+00:00
-- url     : https://prove2.me/theorems/130e9e6c-7e80-4bf3-ae17-5e6f872160e2
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8CertificateReduction` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8CertificateReduction` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8CertificateReduction` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8CertificateReduction (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8CertificateReduction.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8Inverse
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface

-- ===== source module GeneralCK.PureGapE8CertificateReduction =====
section

/-!
# Exact certificate reduction for equation (8)

This file formalizes the manuscript's no-gap first-quadrant case split.  The
analytic and interval sublemmas are exposed as seven precisely bounded owner
fields; satisfying those fields implies `E8StrictOnSlopeRange` and therefore
the smooth-interior exclusion.
-/

namespace GeneralCK

theorem e8Q_zero : e8Q 0 = 0 := by
  rw [e8Q]
  split_ifs with h
  · have hfalse : ¬ (0 : ℝ) < 0 := lt_irrefl 0
    exact False.elim (hfalse (by simpa using e8SlopeRange_subset_pos h))
  · rfl

theorem e8Delta_zero_left (t : ℝ) : e8Delta e8Q 0 t = 0 := by
  unfold e8Delta
  rw [e8Q_zero]
  ring

theorem e8Delta_zero_right (s : ℝ) : e8Delta e8Q s 0 = 0 := by
  unfold e8Delta
  rw [e8Q_zero]
  ring

/-- The stable large-`s` algebraic identity (83) from the manuscript. -/
theorem e8Delta_tail_identity (Q : ℝ → ℝ) (s t : ℝ) :
    e8Delta Q s t =
      Q (2 * s + t) * (Q (s + t) - Q s - 2 * Q t) +
        Q t * (Q (s + t) + Q s) := by
  unfold e8Delta
  ring








theorem deriv_e8Delta_right (Q : ℝ → ℝ) (s t : ℝ)
    (hB : DifferentiableAt ℝ Q (2 * s + t))
    (hC : DifferentiableAt ℝ Q (s + t))
    (hA : DifferentiableAt ℝ Q t) :
    deriv (fun u => e8Delta Q s u) t = e8DeltaDerivT Q s t := by
  have hBt := hB.hasDerivAt.comp t
    ((hasDerivAt_const t (2 * s)).add (hasDerivAt_id t))
  have hCt := hC.hasDerivAt.comp t
    ((hasDerivAt_const t s).add (hasDerivAt_id t))
  have hAt := hA.hasDerivAt
  have hD := hasDerivAt_const t (Q s)
  have h := ((hBt.sub hD).mul (hCt.sub hAt)).sub
    ((hBt.sub hCt).mul (hD.add hAt))
  have heq : (fun u => e8Delta Q s u) =ᶠ[nhds t]
      ((Q ∘ fun u => 2 * s + u) - fun _ => Q s) *
          ((Q ∘ fun u => s + u) - Q) -
        ((Q ∘ fun u => 2 * s + u) - (Q ∘ fun u => s + u)) *
          ((fun _ => Q s) + Q) := by
    filter_upwards with u
    rfl
  have hd := (h.congr_of_eventuallyEq heq).deriv
  convert hd using 1 <;> simp only [e8DeltaDerivT, Function.comp_apply,
    Pi.sub_apply, Pi.add_apply] <;> ring

/-- Exact first `s`-derivative used before the manuscript's repeated
`s`-integration steps. -/
noncomputable def e8DeltaDerivS (Q : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (2 * deriv Q (2 * s + t) - deriv Q s) * (Q (s + t) - Q t) +
    (Q (2 * s + t) - Q s) * deriv Q (s + t) -
    (2 * deriv Q (2 * s + t) - deriv Q (s + t)) * (Q s + Q t) -
    (Q (2 * s + t) - Q (s + t)) * deriv Q s

theorem deriv_e8Delta_left (Q : ℝ → ℝ) (s t : ℝ)
    (hB : DifferentiableAt ℝ Q (2 * s + t))
    (hC : DifferentiableAt ℝ Q (s + t))
    (hD : DifferentiableAt ℝ Q s) :
    deriv (fun u => e8Delta Q u t) s = e8DeltaDerivS Q s t := by
  have hBs := hB.hasDerivAt.comp s
    (((hasDerivAt_id s).const_mul 2).add_const t)
  have hCs := hC.hasDerivAt.comp s ((hasDerivAt_id s).add_const t)
  have hDs := hD.hasDerivAt
  have hA := hasDerivAt_const s (Q t)
  have h := ((hBs.sub hDs).mul (hCs.sub hA)).sub
    ((hBs.sub hCs).mul (hDs.add hA))
  have heq : (fun u => e8Delta Q u t) =ᶠ[nhds s]
      ((Q ∘ fun u => 2 * u + t) - Q) *
          ((Q ∘ fun u => u + t) - fun _ => Q t) -
        ((Q ∘ fun u => 2 * u + t) - (Q ∘ fun u => u + t)) *
          (Q + fun _ => Q t) := by
    filter_upwards with u
    rfl
  have hd := (h.congr_of_eventuallyEq heq).deriv
  convert hd using 1 <;> simp only [e8DeltaDerivS, Function.comp_apply,
    Pi.sub_apply, Pi.add_apply, id_eq] <;> ring








/-- An E8 positivity owner for a specified region of the first quadrant. -/
def E8PositiveOn (region : ℝ → ℝ → Prop) : Prop :=
  ∀ s t : ℝ, E8Admissible s t → region s t → 0 < e8Delta e8Q s t

/-- The seven analytic/certificate owners in the manuscript's exact global
case split.  All decimal endpoints are represented by exact rationals. -/
structure E8CertificateOwners : Prop where
  largeS : E8PositiveOn fun s _ => (63 / 20 : ℝ) ≤ s
  largeT : E8PositiveOn fun s t =>
    (119 / 10 : ℝ) ≤ t ∧ (1 / 200 : ℝ) ≤ s ∧ s ≤ 63 / 20
  smallSTail : E8PositiveOn fun s t =>
    (20 : ℝ) ≤ t ∧ s ≤ 1 / 200
  origin : E8PositiveOn fun s t => s + t ≤ 2 / 25
  sAxis : E8PositiveOn fun s t =>
    s ≤ 1 / 50 ∧ (3 / 50 : ℝ) ≤ t ∧ t ≤ 20
  tAxis : E8PositiveOn fun s t =>
    (3 / 50 : ℝ) ≤ s ∧ s ≤ 63 / 20 ∧ t ≤ 1 / 50
  compact : E8PositiveOn fun s t =>
    (1 / 50 : ℝ) ≤ s ∧ s ≤ 63 / 20 ∧
      (1 / 50 : ℝ) ≤ t ∧ t ≤ 12

/-- Exact rational coverage of the positive quadrant by the seven E8 owner
regions.  This is the formal no-gap audit behind the certificate split. -/
theorem e8_certificate_regions_cover {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (63 / 20 : ℝ) ≤ s ∨
    ((119 / 10 : ℝ) ≤ t ∧ (1 / 200 : ℝ) ≤ s ∧ s ≤ 63 / 20) ∨
    ((20 : ℝ) ≤ t ∧ s ≤ 1 / 200) ∨
    s + t ≤ 2 / 25 ∨
    (s ≤ 1 / 50 ∧ (3 / 50 : ℝ) ≤ t ∧ t ≤ 20) ∨
    ((3 / 50 : ℝ) ≤ s ∧ s ≤ 63 / 20 ∧ t ≤ 1 / 50) ∨
    ((1 / 50 : ℝ) ≤ s ∧ s ≤ 63 / 20 ∧
      (1 / 50 : ℝ) ≤ t ∧ t ≤ 12) := by
  by_cases hsLarge : (63 / 20 : ℝ) ≤ s
  · exact Or.inl hsLarge
  right
  have hsUpper : s ≤ (63 / 20 : ℝ) := (lt_of_not_ge hsLarge).le
  by_cases htTwenty : (20 : ℝ) ≤ t
  · by_cases hsTail : (1 / 200 : ℝ) ≤ s
    · exact Or.inl ⟨by linarith, hsTail, hsUpper⟩
    · exact Or.inr (Or.inl ⟨htTwenty, (lt_of_not_ge hsTail).le⟩)
  have htUpper20 : t ≤ (20 : ℝ) := (lt_of_not_ge htTwenty).le
  by_cases htTwelve : (12 : ℝ) ≤ t
  · by_cases hsTail : (1 / 200 : ℝ) ≤ s
    · exact Or.inl ⟨by linarith, hsTail, hsUpper⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by linarith, by linarith, htUpper20⟩)))
  have htUpper12 : t ≤ (12 : ℝ) := (lt_of_not_ge htTwelve).le
  by_cases hsAxis : s ≤ (1 / 50 : ℝ)
  · by_cases htOrigin : t < (3 / 50 : ℝ)
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hsAxis, le_of_not_gt htOrigin, by linarith⟩)))
  have hsLower : (1 / 50 : ℝ) ≤ s := le_of_not_ge hsAxis
  by_cases htAxis : t ≤ (1 / 50 : ℝ)
  · by_cases hsOrigin : s < (3 / 50 : ℝ)
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨le_of_not_gt hsOrigin, hsUpper, htAxis⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hsLower, hsUpper, le_of_not_ge htAxis, htUpper12⟩))))

/-- Kernel-checked assembly of the seven owner obligations into the complete
range-restricted equation-(8) theorem. -/
theorem E8CertificateOwners.e8StrictOnSlopeRange
    (h : E8CertificateOwners) : E8StrictOnSlopeRange := by
  intro s t hs ht hsR htR hstR h2stR
  have hadm : E8Admissible s t := ⟨hs, ht, hsR, htR, hstR, h2stR⟩
  rcases e8_certificate_regions_cover hs ht with
    hlargeS | hlargeT | hsmallTail | horigin | hsAxis | htAxis | hcompact
  · exact h.largeS s t hadm hlargeS
  · exact h.largeT s t hadm hlargeT
  · exact h.smallSTail s t hadm hsmallTail
  · exact h.origin s t hadm horigin
  · exact h.sAxis s t hadm hsAxis
  · exact h.tAxis s t hadm htAxis
  · exact h.compact s t hadm hcompact

/-- The precise certificate-level handoff to the fixed-entropy mean
reduction. -/
theorem not_localMin_of_e8CertificateOwners
    (h : E8CertificateOwners) {a c e f : ℝ}
    (hac : a < c) (hsum : a + c < 1)
    (ha : a < 1 / 2) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f) :
    ¬ IsLocalMin
      (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f) (a, c) :=
  not_localMin_of_e8SlopeRange h.e8StrictOnSlopeRange
    hac hsum ha hc he hf

end GeneralCK

end


