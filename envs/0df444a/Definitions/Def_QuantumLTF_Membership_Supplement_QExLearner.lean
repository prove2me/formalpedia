-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_QExLearner
-- name    : QuantumLTF_Membership_Supplement_QExLearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:36:37.510258+00:00
-- url     : https://prove2.me/theorems/5cb9b4a5-fa92-4552-86f3-b0d19b893d6a
-- title:
--   Quantum learner with access to $\mathsf{QEX}(f_w,\gamma_n)$ and its inverse
-- statement:
--   A $T$-query learner with the continuous example oracle acts on $\ell^2(\Omega;H_X)\cong H_X\otimes\ell^2(\Omega)$, for an arbitrary workspace index set $\Omega$. Its ingredients are:
--
--   1. a unit initial vector;
--   2. $T$ calls, each to $U\otimes I$ or to $U^\dagger\otimes I$, counted together (p. 10);
--   3. an arbitrary unitary after each call;
--   4. a final POVM whose outcome $o$ gives a classifier $h_o:\mathbb R^n\to\mathbb Z$.
--
--   It **succeeds for the oracle $U$, target $w$ and accuracy $\epsilon$** if some measurable set of outcomes, all of whose classifiers satisfy $d_{\gamma_n}(h_o,f_w)\le\epsilon$, has probability at least $2/3$.
--
--   **Formalization Note** Classifiers need not be measurable, which only enlarges the class of learners.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 5.12, p. 78 (PDF p. 79); §1.5, p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_Supplement_IsPOVM
import Definitions.Def_QuantumLTF_Membership_Supplement_IsQEXCont

namespace QuantumLTF.Membership.Supplement

open MeasureTheory QuantumLTF.Membership

/-- **A quantum learner with access to `QEX(f_w, γ_n)` and its inverse.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 5.12,
p. 78 (PDF p. 79). The state space is `ℓ²(Ω; H_X) ≅ H_X ⊗ ℓ²(Ω)` for an arbitrary workspace index type
`Ω`. A learner making `T` queries starts in a unit vector `init`, and for `t = 0, …, T − 1` applies the
oracle `U ⊗ I` (or `U† ⊗ I` if `adj t`) and then the unitary `V t`; the final state is measured by the
POVM `meas` with outcomes in `O`, outcome `o` giving the classifier `hyp o`.

**Formalization Note.** Calls to `U` and `U†` are counted together (p. 10: "each application of
either QEX(f, D) or QEX(f, D)† counted as one query"). Any measurement is allowed (`IsPOVM`); the
classifiers need not be measurable, which only enlarges the class of learners. -/
structure QExLearner (n : ℕ) where
  /-- The workspace index type. -/
  Ω : Type
  /-- The number of oracle calls (to `U` or `U†`). -/
  T : ℕ
  /-- The initial state. -/
  init : lp (fun _ : Ω => ExSpace n) 2
  init_norm : ‖init‖ = 1
  /-- The unitary applied after call `t`. -/
  V : ℕ → (lp (fun _ : Ω => ExSpace n) 2 ≃ₗᵢ[ℂ] lp (fun _ : Ω => ExSpace n) 2)
  /-- Call `t` is to `U†` iff `adj t`. -/
  adj : ℕ → Bool
  /-- The outcome space of the final measurement. -/
  O : Type
  [mO : MeasurableSpace O]
  /-- The final measurement. -/
  meas : lp (fun _ : Ω => ExSpace n) 2 → Measure O
  meas_povm : IsPOVM meas
  /-- The classifier output on outcome `o`. -/
  hyp : O → EuclideanSpace ℝ (Fin n) → ℤ

attribute [instance] QExLearner.mO

/-- `U ⊗ I` on `ℓ²(Ω; H_X)`: `U` applied to every component. -/
noncomputable def QExLearner.lift {n : ℕ} {Ω : Type} (U : ExSpace n ≃ₗᵢ[ℂ] ExSpace n)
    (f : lp (fun _ : Ω => ExSpace n) 2) : lp (fun _ : Ω => ExSpace n) 2 :=
  ⟨fun ω => U ((f : ∀ _ : Ω, ExSpace n) ω),
    (memℓp_gen_iff (by norm_num)).2 (by
      simpa [LinearIsometryEquiv.norm_map] using (memℓp_gen_iff (p := 2) (by norm_num)).1 f.2)⟩

/-- The state after the first `t` oracle calls (and the unitaries following them), oracle `U`. -/
noncomputable def QExLearner.stateAt {n : ℕ} (L : QExLearner n) (U : ExSpace n ≃ₗᵢ[ℂ] ExSpace n) :
    ℕ → lp (fun _ : L.Ω => ExSpace n) 2
  | 0 => L.init
  | t + 1 => L.V t (QExLearner.lift (if L.adj t then U.symm else U) (L.stateAt U t))

/-- **Success for target `w` and oracle `U`:** some measurable set of outcomes, all giving a
classifier `h` with `d_{γ_n}(h, f_w) ≤ ε`, has probability at least `2/3`. -/
def QExLearner.Succeeds {n : ℕ} (L : QExLearner n) (U : ExSpace n ≃ₗᵢ[ℂ] ExSpace n)
    (w : EuclideanSpace ℝ (Fin n)) (ε : ℝ) : Prop :=
  ∃ S : Set L.O, MeasurableSet S ∧ S ⊆ {o | disagree (L.hyp o) (ltf w 0) ≤ ε} ∧
    (2 / 3 : ENNReal) ≤ L.meas (L.stateAt U L.T) S

end QuantumLTF.Membership.Supplement


