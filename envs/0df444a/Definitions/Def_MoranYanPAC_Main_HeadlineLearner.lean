-- Prove2me | Definitions.Def_MoranYanPAC_Main_HeadlineLearner
-- name    : MoranYanPAC_Main_HeadlineLearner
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:07:30.356864+00:00
-- url     : https://prove2.me/theorems/0caea1f5-e16e-4f9a-a122-e034dd783cf7
-- title:
--   The fixed-witness learner from Algorithms 3 and 1
-- statement:
--   For a class $H$ and dimension $d$, choose a source witness assignment from the data $H,d$ once, independently of the input sample. Lemma 6 supplies its existence on valid instances. Use Algorithm 3 to form $C(S)$ and then sample by Algorithm 1 with
--
--   $$q_S(h)=|S|-\ell_S(h),\quad\Delta=1,\quad B=4(d+1),\quad\lambda=1+\frac2\varepsilon\log\frac{32(d+1)}\delta.$$
--
--   This defines the source's constructed learner. The definition takes no finiteness, coverage, privacy or accuracy certificate. A conditional finite-set conversion makes it total even outside the source's assumptions: if no source witness assignment exists use empty witnesses, and if the resulting candidate set is empty or infinite return the constant-zero predictor. On valid instances Lemmas 6, 10 and 11 must show that these fallback branches are never taken, for every input size. The existential headline target is free to select another learner in the logarithmic endpoint regime; it does not assert a stronger accuracy statement about this particular rule.
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Sections 7.2–7.4 and Algorithms 3 and 1, pp. 21–25 (PDF pp. 21–25)

import Mathlib
import Definitions.Def_MoranYanPAC_Main_Candidates
import Definitions.Def_MoranYanPAC_Main_EmpiricalLoss
import Definitions.Def_MoranYanPAC_Main_StructuralMechanism

set_option autoImplicit false

namespace MoranYanPAC.Main

/-- A public choice made from H and d once, before any sample. Lemma 6 supplies
existence on the source's instances. On other classes the empty assignment is a total default. -/
noncomputable def fixedWitnessAssignment {X : Type*} (H : Set (X → Bool)) (d : ℕ) :
    (X → Bool) → Finset X := by
  classical
  exact if h : ∃ Aw : (X → Bool) → Finset X, SourceWitnesses H d Aw then
    Classical.choose h else fun _ => ∅

/-- Sections 7.3–7.4, pp. 24–25: Algorithm 3 followed by Algorithm 1, with
Δ=1, B=4(d+1), q_S(h)=|S|−ℓ_S(h), and λ=1+(2/ε)log(32(d+1)/δ).
The conditional merely totalizes the definition outside the source's valid classes;
Lemmas 6, 10 and 11 must establish that the nonempty finite branch is taken on all samples.
No finiteness or coverage certificate is an input. -/
noncomputable def headlineLearner {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (ε δ : ℝ) (S : List (X × Bool)) : PMF (X → Bool) := by
  classical
  let C := candidates H d (fixedWitnessAssignment H d) S
  exact if hf : C.Finite then
    if hn : C.Nonempty then
      finiteGibbs hf.toFinset (by simpa using hn)
        (fun h => (ε / 2) * ((S.length : ℝ) - empiricalLoss S h +
          rankBonus ε δ 1 (4 * ((d : ℝ) + 1)) * PrivLittlestone.rankOf H d h))
    else PMF.pure (fun _ => false)
  else PMF.pure (fun _ => false)

end MoranYanPAC.Main


