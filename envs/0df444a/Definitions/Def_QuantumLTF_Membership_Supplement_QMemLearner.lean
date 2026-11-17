-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_QMemLearner
-- name    : QuantumLTF_Membership_Supplement_QMemLearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:35:03.171809+00:00
-- url     : https://prove2.me/theorems/eeb4be19-adb5-4d69-8281-d76191bf6cb3
-- title:
--   Quantum membership-query learner at arbitrary real points
-- statement:
--   A $T$-query learner with membership access to $f_w(x)=\mathrm{sign}(\langle w,x\rangle)$ acts on
--   $$H_\Omega=\ell^2\big((\mathbb R^n\times\{0,1\})\times\Omega\big),$$
--   with basis states $|x,b,\omega\rangle$: a query register holding any real point $x$, a target bit $b$, and a workspace index $\omega$ of an arbitrary set $\Omega$. Its ingredients are:
--
--   1. a unit initial vector;
--   2. $T$ oracle calls $|x,b,\omega\rangle\mapsto|x,b\oplus c_t(\omega)\bar f_w(x),\omega\rangle$, each possibly controlled by a workspace predicate $c_t$;
--   3. after each call, an arbitrary unitary on $H_\Omega$, so the algorithm is adaptive;
--   4. a final POVM whose outcome $o$ gives a hypothesis $h_o:\mathbb R^n\to\mathbb Z$ (any function, so improper hypotheses are allowed).
--
--   The learner **succeeds for $w$ at accuracy $\epsilon$** if some measurable set of outcomes, all of whose hypotheses satisfy $d_{\gamma_n}(h_o,f_w)\le\epsilon$, has probability at least $2/3$.
--
--   **Formalization Note** $O_f$ is an involution, so its inverse is itself. The success probability is read on a measurable event, since the set of good outcomes of an arbitrary hypothesis map need not be measurable.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.5, p. 38 (PDF p. 39); §3.2, pp. 34–38 (PDF pp. 35–39); Eq. (1), p. 4 (PDF p. 5)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_Supplement_IsPOVM

namespace QuantumLTF.Membership.Supplement

open MeasureTheory QuantumLTF.Membership

/-- **A quantum membership-query learner with queries at arbitrary real points.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331,
Theorem 3.5, p. 38 (PDF p. 39), and §3.2, pp. 34–38 (PDF pp. 35–39): "adaptive algorithms making
superposition queries at arbitrary real points and outputting improper hypotheses".

The state space is `H_Ω := ℓ²((ℝⁿ × {0,1}) × Ω)` (counting measure), with basis states `|x, b, ω⟩`:
a query register holding any real point `x`, a target bit `b`, and a workspace index `ω` of an
arbitrary type `Ω`. A learner making `T` queries starts in a unit vector `init`, and for
`t = 0, …, T − 1` applies a query and then the unitary `V t` (arbitrary, so adaptivity is coherent).
Query `t` is the oracle `O_f` (Eq. (1), p. 4: `|x⟩|b⟩ ↦ |x⟩|b ⊕ f̄(x)⟩`), controlled on the workspace:
it acts on `|x, b, ω⟩` iff `ctrl t ω`. The final state is measured by the POVM `meas` with outcomes
in `O`, and outcome `o` gives the hypothesis `hyp o : ℝⁿ → ℤ` (any function: improper hypotheses).

**Formalization Note.** `O_f` is an involution, so its inverse is itself; uncontrolled calls are
`ctrl t = fun _ => true`. `Ω` and `O` are arbitrary types, so finite or infinite workspaces and any
measurement are covered. -/
structure QMemLearner (n : ℕ) where
  /-- The workspace index type. -/
  Ω : Type
  /-- The number of membership queries. -/
  T : ℕ
  /-- The initial state. -/
  init : lp (fun _ : (EuclideanSpace ℝ (Fin n) × Bool) × Ω => ℂ) 2
  init_norm : ‖init‖ = 1
  /-- The unitary applied after query `t`. -/
  V : ℕ → (lp (fun _ : (EuclideanSpace ℝ (Fin n) × Bool) × Ω => ℂ) 2 ≃ₗᵢ[ℂ]
    lp (fun _ : (EuclideanSpace ℝ (Fin n) × Bool) × Ω => ℂ) 2)
  /-- Query `t` acts on the workspace states `ω` with `ctrl t ω`. -/
  ctrl : ℕ → Ω → Bool
  /-- The outcome space of the final measurement. -/
  O : Type
  [mO : MeasurableSpace O]
  /-- The final measurement: outcome distribution of a measured state. -/
  meas : lp (fun _ : (EuclideanSpace ℝ (Fin n) × Bool) × Ω => ℂ) 2 → Measure O
  meas_povm : IsPOVM meas
  /-- The hypothesis output on outcome `o`. -/
  hyp : O → EuclideanSpace ℝ (Fin n) → ℤ

attribute [instance] QMemLearner.mO

/-- The permutation of the basis `(x, b, ω) ↦ (x, b ⊕ [c ω] f̄_w(x), ω)`, `f_w = ltf w 0`: the basis
action of the (controlled) membership oracle. -/
noncomputable def QMemLearner.oraclePerm {n : ℕ} {Ω : Type} (w : EuclideanSpace ℝ (Fin n))
    (c : Ω → Bool) : (EuclideanSpace ℝ (Fin n) × Bool) × Ω ≃ (EuclideanSpace ℝ (Fin n) × Bool) × Ω :=
  Function.Involutive.toPerm
    (fun p => ((p.1.1, xor p.1.2 (c p.2 && decide (ltf w 0 p.1.1 = -1))), p.2))
    (fun p => by cases p; simp)

/-- The oracle call `O_f` (controlled by `c`) on `H_Ω`: `(O ψ)(x, b, ω) = ψ(x, b ⊕ [c ω] f̄_w(x), ω)`. -/
noncomputable def QMemLearner.oracle {n : ℕ} {Ω : Type} (w : EuclideanSpace ℝ (Fin n))
    (c : Ω → Bool) (ψ : lp (fun _ : (EuclideanSpace ℝ (Fin n) × Bool) × Ω => ℂ) 2) :
    lp (fun _ : (EuclideanSpace ℝ (Fin n) × Bool) × Ω => ℂ) 2 :=
  ⟨fun p => (ψ : _ → ℂ) (QMemLearner.oraclePerm w c p),
    (memℓp_gen_iff (by norm_num)).2 (((QMemLearner.oraclePerm w c).summable_iff
      (f := fun p => ‖(ψ : _ → ℂ) p‖ ^ (2 : ENNReal).toReal)).2
      ((memℓp_gen_iff (p := 2) (by norm_num)).1 ψ.2))⟩

/-- The state after the first `t` queries (and the unitaries following them) against `f_w`. -/
noncomputable def QMemLearner.stateAt {n : ℕ} (L : QMemLearner n) (w : EuclideanSpace ℝ (Fin n)) :
    ℕ → lp (fun _ : (EuclideanSpace ℝ (Fin n) × Bool) × L.Ω => ℂ) 2
  | 0 => L.init
  | t + 1 => L.V t (QMemLearner.oracle w (L.ctrl t) (L.stateAt w t))

/-- **Success for target `w`.** With probability at least `2/3` the learner outputs `h` with
`d_{γ_n}(h, f_w) ≤ ε`. **Formalization Note.** The probability is read on a measurable event: some
measurable set of outcomes, all of which give an `ε`-good hypothesis, has probability `≥ 2/3`
(the success set itself need not be measurable for an arbitrary `hyp`). -/
def QMemLearner.Succeeds {n : ℕ} (L : QMemLearner n) (w : EuclideanSpace ℝ (Fin n)) (ε : ℝ) : Prop :=
  ∃ S : Set L.O, MeasurableSet S ∧ S ⊆ {o | disagree (L.hyp o) (ltf w 0) ≤ ε} ∧
    (2 / 3 : ENNReal) ≤ L.meas (L.stateAt w L.T) S

end QuantumLTF.Membership.Supplement


