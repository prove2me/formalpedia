-- Prove2me | Definitions.Def_CK_GeneralCK_PsiScalarOwnerCore
-- name    : CK_GeneralCK_PsiScalarOwnerCore
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:50:52.008607+00:00
-- url     : https://prove2.me/theorems/eb10b47e-6613-41a2-b053-57fe7dbf88de
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiScalarOwnerCore` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiScalarOwnerCore` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiScalarOwnerCore` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiScalarOwnerCore (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiScalarOwnerCore.lean)

import Definitions.Def_CK_GeneralCK_PsiFeasibleImbalance

-- ===== source module GeneralCK.PsiScalarOwnerCore =====
section

/-!
# Three-variable reduction for the residual active-psi owners

On the canonical mean chamber, `H a ≤ H b`.  Consequently the feasible
imbalance correction depends only on the two means and the average child
entropy.  This removes the finite law and its individual entropy split from
all remaining chart certificates.
-/

namespace GeneralCK
open Set

theorem H_mono_on_canonical_means {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) (hsum : a + b ≤ 1) :
    H a ≤ H b := by
  by_cases hbhalf : b ≤ 1 / 2
  · exact H_strictMonoOn.monotoneOn
      ⟨ha, hab.trans hbhalf⟩ ⟨ha.trans hab, hbhalf⟩ hab
  · have hcomp0 : 0 ≤ 1 - b := by linarith
    have hcomphalf : 1 - b ≤ 1 / 2 := by linarith
    have hacomp : a ≤ 1 - b := by linarith
    rw [← H_complement b]
    exact H_strictMonoOn.monotoneOn
      ⟨ha, hacomp.trans hcomphalf⟩ ⟨hcomp0, hcomphalf⟩ hacomp

/-- The equation-(108) bound written only in `(a,b,E)`, where `E` is the
average child entropy. -/
noncomputable def residualPsiScalarBound (a b E : ℝ) : ℝ :=
  let s := (H a + H b) / 2 - E
  let r := max 0 (s - H a)
  Scalar.P (H ((a + b) / 2) - E) -
    (Scalar.P (s - r) + Scalar.P (s + r)) / 2

theorem InteriorLaw.capSensitiveSplitBound_eq_residualPsiScalarBound
    {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a ≤ μ.b) (hsum : μ.a + μ.b ≤ 1) :
    μ.capSensitiveSplitBound =
      residualPsiScalarBound μ.a μ.b μ.meanEntropy := by
  have hH : H μ.a ≤ H μ.b :=
    H_mono_on_canonical_means μ.a_interior.1.le hab μ.b_interior.2 hsum
  have hmin : min (H μ.a) (H μ.b) = H μ.a := min_eq_left hH
  have hs : μ.meanDeficit = (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    unfold meanDeficit meanEntropy
    ring
  have hI : μ.information = H ((μ.a + μ.b) / 2) - μ.meanEntropy := rfl
  unfold capSensitiveSplitBound forcedDeficitImbalance residualPsiScalarBound
  rw [hmin, hs, hI]

/-- Every residual chart can now certify a parent scalar inequality in three
real variables.  The feasible-imbalance theorem handles every compatible
individual child-entropy split and the log-sum theorem handles every law. -/
theorem InteriorLaw.gap_le_of_activePsi_of_residualPsiScalarBound
    {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a ≤ μ.b) (hsum : μ.a + μ.b ≤ 1)
    (hactive : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy)
    (hscalar : residualPsiScalarBound μ.a μ.b μ.meanEntropy ≤
      interiorCost μ.a μ.b) :
    μ.gap ≤ μ.cost := by
  apply μ.gap_le_of_activePsi_of_capSensitiveSplitBound_le_interiorCost hactive.le
  rw [μ.capSensitiveSplitBound_eq_residualPsiScalarBound hab hsum]
  exact hscalar

/-- A chart predicate on `(a,b,E)` can be discharged without quantifying
over finite laws or individual child entropies. -/
def ResidualPsiScalarOwner (region : ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ a b E : ℝ, 0 < a → a < b → b < 1 → a + b ≤ 1 →
    0 < E → E ≤ (H a + H b) / 2 →
    1 / 16 < a + b → 1 / 100 < H ((a + b) / 2) - E →
    region a b E →
    phi ((a + b) / 2) E < psi ((a + b) / 2) E →
    residualPsiScalarBound a b E ≤ interiorCost a b

theorem residualPsiOwner_of_scalarOwner {region : ℝ → ℝ → ℝ → Prop}
    (h : ResidualPsiScalarOwner region) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      region μ.a μ.b μ.meanEntropy →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost := by
  intro k μ hab hsum hmean hinfo hregion hactive
  have hEpos : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hEcap : μ.meanEntropy ≤ (H μ.a + H μ.b) / 2 := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_le_cap, μ.f_le_cap]
  have hinfo' : 1 / 100 < H ((μ.a + μ.b) / 2) - μ.meanEntropy := by
    simpa only [InteriorLaw.information, InteriorLaw.midpoint] using hinfo
  have hactive' :
      phi ((μ.a + μ.b) / 2) μ.meanEntropy <
        psi ((μ.a + μ.b) / 2) μ.meanEntropy := by
    simpa only [InteriorLaw.midpoint] using hactive
  exact μ.gap_le_of_activePsi_of_residualPsiScalarBound hab.le hsum hactive
    (h μ.a μ.b μ.meanEntropy μ.a_interior.1 hab μ.b_interior.2 hsum
      hEpos hEcap hmean hinfo' hregion hactive')

/-- Scalar chart predicates matching the six owners left after the ratio
tail. -/
def sameSideResidualRegion (a b _E : ℝ) : Prop :=
  b ≤ 1 / 2 ∧ 1 / 4294967296 < a / b

def oppositeCentralResidualRegion (a b _E : ℝ) : Prop :=
  1 / 2 ≤ b ∧ 1 / 10 ≤ a

def oppositeBoundaryResidualRegion (a b _E : ℝ) : Prop :=
  1 / 2 ≤ b ∧ a ≤ 1 / 268435456

def oppositeCornerResidualRegion (a b _E : ℝ) : Prop :=
  1 / 2 ≤ b ∧ a + 1 - b ≤ 1 / 8192

def oppositeLowEntropyResidualRegion (_a b E : ℝ) : Prop :=
  1 / 2 ≤ b ∧ E ≤ 1 / 1000000

def oppositeCompactResidualRegion (a b E : ℝ) : Prop :=
  1 / 2 ≤ b ∧ 1 / 268435456 < a ∧ a < 1 / 10 ∧
    1 / 8192 < a + 1 - b ∧ 1 / 1000000 < E

#print axioms residualPsiScalarBound
#print axioms ResidualPsiScalarOwner
#print axioms residualPsiOwner_of_scalarOwner

end GeneralCK

end


