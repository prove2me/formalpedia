-- Prove2me | Definitions.Def_GMFGLearn_FiniteLayer
-- name    : GMFGLearn_FiniteLayer
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:14.405235+00:00
-- url     : https://prove2.me/theorems/ee303eb9-d7db-4b49-951b-e7ffe9fd9bd0
-- title:
--   Finite setting: $Q^\star_{\mathcal L}$ of $\mathcal M_{\mathcal L}$, $\Gamma_1(\mathcal L)_s=\mathrm{argmax\text{-}e}(Q^\star_{\mathcal L}(s,\cdot))$, smoothed policies
-- statement:
--   Let $\mathcal S$ and $\mathcal A$ be finite. For a GMFG and $\mathcal L\in\mathcal P(\mathcal S\times\mathcal A)$, the MDP $\mathcal M_{\mathcal L}=(\mathcal S,\mathcal A,P_{\mathcal L},r_{\mathcal L},\gamma)$ has $P_{\mathcal L}(s'\mid s,a)=P(s'\mid s,a,\mathcal L)$ and $r_{\mathcal L}(s,a)=r(s,a,\mathcal L)$, and $Q^\star_{\mathcal L}=Q^\star_{\mathcal M_{\mathcal L}}$ is its optimal Q-function.
--
--   1. **Selection in the finite setting.** $\Gamma_1(\mathcal L)$ is the policy $s\mapsto\mathrm{argmax\text{-}e}(Q^\star_{\mathcal L}(s,\cdot))$, the uniform law on the actions of maximal $Q^\star_{\mathcal L}(s,\cdot)$.
--   2. **Smoothed policy.** For $f$ mapping $\mathbb R^{\mathcal A}$ to probability distributions on $\mathcal A$ and $Q:\mathcal S\times\mathcal A\to\mathbb R$, the policy $\pi(s)=f(Q(s,\cdot))$.
--
--   These are the policies of Theorem 2: the equilibrium uses $\Gamma_1$, the algorithm uses $f_{c,c'}(\hat Q_k)$.
--
--   **Formalization Note** $P(s'\mid s,a,\mathcal L)$ is the mass of the measure $P(s,a,\mathcal L)$ at $s'$ and $r_{\mathcal L}$ the mean reward. argmax-e as a law is `PMF.uniformOfFinset` on the maximizing actions; its mass at $a$ equals the argmax-e vector's coordinate (proved in the verification file). On a finite state space with measurable singletons every policy is measurable.
-- source:
--   Guo, Hu, Xu, Zhang, A General Framework for Learning Mean-Field Games, arXiv:2003.06069v3, §4.1, pp.10–11; Algorithm 2 line 4, p.13; proof of Theorem 2, p.22

import Mathlib
import Definitions.Def_GMFGLearn_GMFG
import Definitions.Def_GMFGLearn_FiniteMDP
import Definitions.Def_GMFGLearn_Smoothing

open MeasureTheory

namespace GMFGLearn

/-- The maximizing set of a function on a finite nonempty type is nonempty. -/
theorem argmaxSet_nonempty {A : Type*} [Fintype A] [Nonempty A] (x : A → ℝ) : (argmaxSet x).Nonempty := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  exact ⟨i, by simpa [argmaxSet] using fun j => hi j (Finset.mem_univ j)⟩

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype S] [Fintype A]

/-- **argmax-e as a randomized action.** Guo–Hu–Xu–Zhang, *A General Framework for Learning
Mean-Field Games*, arXiv:2003.06069v3, §4.1, p.10: the uniform law on the actions with maximal
value ("actions with equal maximum Q-values would have equal probabilities to be selected").

**Formalization Note** `PMF.uniformOfFinset` on `argmaxSet x`, as a `ProbabilityMeasure A`; its
mass at `a` is the coordinate `argmaxE x a`. -/
noncomputable def argmaxPM [Nonempty A] (x : A → ℝ) : ProbabilityMeasure A :=
  ⟨(PMF.uniformOfFinset (argmaxSet x) (argmaxSet_nonempty x)).toMeasure, inferInstance⟩

/-- **The optimal Q-function `Q⋆_L` of the MDP `M_L`.** Guo–Hu–Xu–Zhang, arXiv:2003.06069v3, §4.1,
p.10: `M_L = (S, A, P_L, r_L, γ)` with `P_L(s′|s,a) = P(s′|s,a,L)` and `r_L(s,a) = r(s,a,L)`, and
`Q⋆_L = Q⋆_{M_L}` solves the Bellman equation.

**Formalization Note** `P(s′|s,a,L)` is the mass `(P(s,a,L)).real {s′}` and `E[r_L(s,a)]` the mean
reward `rbar(s,a,L)`. -/
noncomputable def GMFG.optQL [Nonempty A] (M : GMFG S A) (L : ProbabilityMeasure (S × A)) :
    S → A → ℝ :=
  optQ (fun s a s' => (M.P (s, a, L) : Measure S).real {s'}) (fun s a => M.rbar (s, a, L)) M.γ

/-- **`Γ₁` in the finite setting.** Guo–Hu–Xu–Zhang, arXiv:2003.06069v3, §4.1, pp.10–11:
"we specify Γ₁ as a mapping to the aforementioned choice of the optimal policy, i.e., the
s-component `Γ₁(L)_s = argmax-e(Q⋆_L(s,·))` for any `s ∈ S`".

**Formalization Note** On a finite state space with measurable singletons every map is measurable,
so the policy is admissible. -/
noncomputable def GMFG.finiteGamma1 [Nonempty A] [MeasurableSingletonClass S] (M : GMFG S A)
    (L : ProbabilityMeasure (S × A)) : Policy S A :=
  ⟨fun s => argmaxPM (M.optQL L s), Measurable.of_discrete⟩

/-- **The smoothed policy `π(s) = f(Q(s,·))`** (Algorithm 2, line 4, p.13; proof of Theorem 2,
p.22: "π = f_{c,c′}(Q_L) is understood as the policy π with π(s) = f_{c,c′}(Q_L(s,·))").

**Formalization Note** `f` takes values in `P(A)`, since `π(s)` is a randomized action. -/
noncomputable def smoothPolicy [MeasurableSingletonClass S] (f : (A → ℝ) → ProbabilityMeasure A)
    (Q : S → A → ℝ) : Policy S A :=
  ⟨fun s => f (Q s), Measurable.of_discrete⟩

end GMFGLearn


