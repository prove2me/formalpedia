-- Prove2me | Definitions.Def_OAI_Probability_Ising_Marginals
-- name    : OAI_Probability_Ising_Marginals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T21:59:36.210054+00:00
-- url     : https://prove2.me/theorems/53599d8e-873b-4465-b046-96df0d5e311f
-- title:
--   Restriction and extension of spin blocks and the extreme log-odds of the pinned two-block marginal
-- statement:
--   Let $G$ be a finite ferromagnetic graph on $V=\{0,\dots,n-1\}$ with Ising energy $H_h(\sigma)=\sum_eK_e\sigma_{l(e)}\sigma_{r(e)}+\sum_vh_v\sigma_v$ for a field $h\in\mathbb{R}^V$, let $I,J,F\subseteq V$ and $\tau\in\{-1,+1\}^V$, and let
--
--   $$W_{h,\tau}(a,b)=\sum_{\sigma:\ \sigma_I=a_I,\ \sigma_J=b_J,\ \sigma_F=\tau_F}e^{H_h(\sigma)}$$
--
--   be the joint weight of the blocks $(\sigma_I,\sigma_J)$ with the spins on $F$ pinned to $\tau$. The file introduces:
--
--   1. **Restriction** of a configuration $\sigma\in\{-1,+1\}^V$ to a block $I$, the block configuration $\sigma|_I\in\{-1,+1\}^I$.
--
--   2. **Extension** of a block configuration $\alpha\in\{-1,+1\}^I$ to $V$ by the value $-1$ off $I$, written $\operatorname{ext}_I(\alpha)$; it satisfies $\operatorname{ext}_I(\alpha)|_I=\alpha$.
--
--   3. **Extreme log-odds.** With $\mathbf{+}$ and $\mathbf{-}$ the all-plus and all-minus configurations,
--
--      $$\Lambda_{h,\tau}=\log W_{h,\tau}(\mathbf{+},\mathbf{+})+\log W_{h,\tau}(\mathbf{-},\mathbf{-})-\log W_{h,\tau}(\mathbf{+},\mathbf{-})-\log W_{h,\tau}(\mathbf{-},\mathbf{+}),$$
--
--      where the first argument prescribes $\sigma_I$ and the second prescribes $\sigma_J$.
--
--   $\Lambda_{h,\tau}$ is the logarithm of the cross-ratio of the joint weights of the four extreme block prescriptions ($I$ all plus or all minus, $J$ all plus or all minus). When $I,J,F$ are pairwise disjoint the pinned marginal is positive and log-supermodular, so $\Lambda_{h,\tau}$ dominates the absolute value of every mixed log-difference of $W_{h,\tau}$; it therefore bounds how much the conditional law of $\sigma_I$ can change when the prescription on $J$ is changed. Restriction and extension identify sums over block configurations $\alpha\in\{-1,+1\}^I$ with sums over full configurations.
--
--   **Formalization Note** The Lean names are `restrictSpin`, `extendSpin` (with the simp lemma `restrict_extend`) and `extremeLogOdds G h I J F τ`. The extreme configurations are the top and bottom elements `⊤`, `⊥` of `Fin n → Bool` in the pointwise order with `false < true`. The definition takes logarithms without any hypothesis; positivity of the joint weights, and hence the meaning of $\Lambda_{h,\tau}$ as a log cross-ratio, needs $I,J,F$ pairwise disjoint.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Marginals.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Marginals.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BufferedIsing mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

def restrictSpin {n : ℕ} (I : Finset (Fin n)) (σ : Spins n) : I → Bool := fun v => σ v.val

def extendSpin {n : ℕ} (I : Finset (Fin n)) (a : I → Bool) : Spins n :=
  fun v => if hv : v ∈ I then a ⟨v, hv⟩ else false

@[simp] lemma restrict_extend {n : ℕ} (I : Finset (Fin n)) (a : I → Bool) :
    restrictSpin I (extendSpin I a) = a := by
  funext v
  simp [restrictSpin, extendSpin, v.property]

noncomputable def extremeLogOdds {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ : Spins n) : ℝ :=
  Real.log (jointWeight G h I J F τ ⊤ ⊤) +
    Real.log (jointWeight G h I J F τ ⊥ ⊥) -
    Real.log (jointWeight G h I J F τ ⊤ ⊥) -
    Real.log (jointWeight G h I J F τ ⊥ ⊤)

end BufferedIsing

end OAI


