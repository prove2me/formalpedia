-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
-- name    : OAI_Probability_ThorpShuffle_FiniteExpectation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:25:13.655861+00:00
-- url     : https://prove2.me/theorems/24e88c34-424c-47bf-8de0-d833e091f947
-- title:
--   Basic rules for uniform means and the step recursion for Thorp shuffle runs
-- statement:
--   For a finite set $\Omega$ and $f:\Omega\to\mathbb{R}$, let $\operatorname{mean}(f)=\frac{1}{|\Omega|}\sum_{\omega\in\Omega}f(\omega)$ be the uniform average. For the Thorp shuffle on positions $Q_d=\{0,1\}^d$, let $T_c\in\mathrm{Sym}(Q_d)$ be the shuffle step driven by a coin vector $c$. For a history $\omega=(\omega_0,\dots,\omega_{t-1})$ of coin vectors, let $\mathrm{run}_t(\omega)=T_{\omega_{t-1}}\circ\cdots\circ T_{\omega_0}$ be the resulting permutation. The module records the following facts.
--
--   1. *Congruence.* If $f(\omega)=g(\omega)$ for every $\omega\in\Omega$, then $\operatorname{mean}(f)=\operatorname{mean}(g)$.
--   2. *Zero.* The mean of the zero function is $0$.
--   3. *Empty run.* For the empty history, $\mathrm{run}_0$ is the identity permutation.
--   4. *Last-step recursion.* For every $d,t\in\mathbb{N}$ and every history $\omega$ of length $t+1$,
--   $$
--   \mathrm{run}_{t+1}(\omega_0,\dots,\omega_t)=T_{\omega_t}\circ\mathrm{run}_t(\omega_0,\dots,\omega_{t-1}).
--   $$
--
--   These rules let averages over histories be manipulated pointwise and let proofs about runs proceed by induction on the number of steps, peeling off the most recent step.
--
--   **Formalization Note** The lemmas are `Conditional.mean_congr`, `Conditional.mean_zero`, `run_zero` and `run_succ`. In `run_succ`, the shorter history is $\omega$ restricted along `Fin.castSucc`, the last coin vector is `ω (Fin.last t)`, and composition is the product in `Equiv.Perm`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/FiniteExpectation.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/FiniteExpectation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow

namespace OAI

universe uΩ uι uΩ'

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem mean_congr {Ω : Type uΩ} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ ω, f ω = g ω) :
    mean f = mean g := by
  unfold mean
  congr 1
  exact Finset.sum_congr rfl (fun ω _ => h ω)

theorem mean_zero {Ω : Type uΩ} [Fintype Ω] : mean (fun _ : Ω => (0 : ℝ)) = 0 := by
  simp [mean]

end Conditional

@[simp] theorem run_zero (d : ℕ) (ω : History d 0) : run d 0 ω = 1 := by
  simp [run]

theorem run_succ (d t : ℕ) (ω : History d (t + 1)) :
    run d (t + 1) ω = step d (ω (Fin.last t)) *
      run d t (fun i => ω i.castSucc) := by
  simp only [run, List.ofFn_succ']
  rw [List.concat_eq_append, List.reverse_concat', List.prod_cons]

namespace Conditional

end Conditional

end Thorp

end

end OAI


