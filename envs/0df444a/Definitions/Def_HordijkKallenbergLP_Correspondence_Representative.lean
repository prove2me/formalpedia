-- Prove2me | Definitions.Def_HordijkKallenbergLP_Correspondence_Representative
-- name    : HordijkKallenbergLP_Correspondence_Representative
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:31.065515+00:00
-- url     : https://prove2.me/theorems/f49f2fbb-b0a5-496c-86da-65d54ff8b7ed
-- title:
--   The class-wise representative of a stationary policy
-- statement:
--   Fix positive state weights $\beta_i$ that sum to one and a stationary randomized policy $\pi$. Let $P^*(\pi)$ be the Cesàro limit matrix of $P(\pi)$ and let $D(\pi)$ be its deviation matrix. For a transient state $l$, set $\gamma_l=0$; for a recurrent state $l$, let $E(l)$ be its ergodic class and set $\gamma_l$ to the maximum of the paper's ratio over $E(l)$. The representative of $\pi$ has coordinates
--
--   $$x_{ia}(\pi)=\bigl[\beta^T P^*(\pi)\bigr]_i\pi_{ia},\qquad y_{ia}(\pi)=\bigl[\beta^T D(\pi)+\gamma^T P^*(\pi)\bigr]_i\pi_{ia}.$$
--
--   The denominator of the maximum is restricted to the recurrent class; the printed formula sums over all states, while the paper’s nonnegativity calculation on the next page requires the class-restricted sum. The class-wise choice of $\gamma$ makes the representative a specific dual point and supplies the nonnegative $y$ coordinates needed in the feasibility claim. **Formalization Note** The maximum is taken over states accessible from the recurrent state; finite-chain facts identifying that set with its ergodic class and establishing positivity of the denominator belong to the theorem layer.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 359, §3.3, equation (6)

import Mathlib
import Definitions.Def_HordijkKallenbergLP_Correspondence_Model

namespace HordijkKallenbergLP.Correspondence

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- The Cesàro limit matrix `P*(π)` of §3.3, p. 359. Its existence for stochastic
matrices is Blackwell's Lemma 1(a), not part of this definition. -/
noncomputable def Pstar (M : StationaryMDP S A) (π : RandomizedPolicy M) : Matrix S S ℝ :=
  limitMatrix (policyMatrix M π)

/-- The deviation matrix `D(π)` of §3.3, p. 359. -/
noncomputable def D (M : StationaryMDP S A) (π : RandomizedPolicy M) : Matrix S S ℝ :=
  deviationMatrix (policyMatrix M π)

/-- The ergodic set containing a recurrent state `l`: the states accessible from `l`.
Hordijk and Kallenberg (1979), §3.3, p. 359. -/
noncomputable def ergodicClass (M : StationaryMDP S A) (π : RandomizedPolicy M) (l : S) : Finset S := by
  classical
  exact Finset.univ.filter (fun i => Accessible (policyMatrix M π) l i)

/-- The class-wise constant `γ_l` of (6), p. 359. It is zero on transient states;
on each recurrent class it is the maximum over that class of the ratio.
Formalization Note: the printed denominator sums over all states, but the
nonnegativity calculation on p. 360 uses a sum over the recurrent class. The
unrestricted printed denominator makes the feasibility claim false for the
two-state chain 1 → 2, 2 → 2 with positive β; the restricted sum is used here.
Its positivity is a finite-chain theorem. -/
noncomputable def gamma (M : StationaryMDP S A) (β : S → ℝ)
    (π : RandomizedPolicy M) (l : S) : ℝ := by
  classical
  exact if IsRecurrent (policyMatrix M π) l then
    (ergodicClass M π l).sup'
      (by
        refine ⟨l, ?_⟩
        simp only [ergodicClass, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Relation.ReflTransGen.refl)
      (fun i => -(∑ k, β k * D M π k i) /
        ((ergodicClass M π l).sum fun k => Pstar M π k i))
  else 0

/-- The x-coordinates of the representative (6), p. 359. -/
noncomputable def representativeX (M : StationaryMDP S A) (β : S → ℝ)
    (π : RandomizedPolicy M) : HordijkKallenbergLP.SingleLP.Pair M → ℝ :=
  fun p => (∑ k, β k * Pstar M π k p.1.1) * π.weight p.1.1 p.1.2

/-- The y-coordinates of the representative (6), p. 359. -/
noncomputable def representativeY (M : StationaryMDP S A) (β : S → ℝ)
    (π : RandomizedPolicy M) : HordijkKallenbergLP.SingleLP.Pair M → ℝ :=
  fun p => ((∑ k, β k * D M π k p.1.1) +
    (∑ l, gamma M β π l * Pstar M π l p.1.1)) * π.weight p.1.1 p.1.2

end HordijkKallenbergLP.Correspondence


