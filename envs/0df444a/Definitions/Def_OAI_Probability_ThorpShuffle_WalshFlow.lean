-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
-- name    : OAI_Probability_ThorpShuffle_WalshFlow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:26:41.214684+00:00
-- url     : https://prove2.me/theorems/9582a161-b4c6-4edc-91c3-e1cf719b7cb5
-- title:
--   Prefix-zero Walsh frequencies and band energies on the Boolean cube
-- statement:
--   Let $Q_d=\{0,1\}^d$ with coordinates indexed by $0,\dots,d-1$. For a weight $w:Q_d\to\mathbb{R}$ and a frequency $a\in Q_d$, let $\hat w(a)=\sum_{x\in Q_d}w(x)(-1)^{\sum_ia_ix_i}$ be the unnormalized Walsh coefficient.
--
--   1. *Prefix-zero frequencies.* For $j\in\mathbb{N}$, a frequency $a\in Q_d$ is $j$-prefix-zero if $a_i=0$ for every coordinate $i<j$. Every $a$ is $0$-prefix-zero, and $a$ is $d$-prefix-zero if and only if $a=0$.
--   2. *Band energy.* The band energy of $w$ at level $j$ is the total squared Walsh coefficient over $j$-prefix-zero frequencies:
--   $$
--   \mathcal B_j(w)=\sum_{\substack{a\in Q_d\\ a_0=\cdots=a_{j-1}=0}}\hat w(a)^2 .
--   $$
--   3. *Endpoints.* At the two extreme levels,
--   $$
--   \mathcal B_0(w)=2^d\sum_{x\in Q_d}w(x)^2,\qquad\mathcal B_d(w)=\Bigl(\sum_{x\in Q_d}w(x)\Bigr)^2 .
--   $$
--   The first identity is Parseval's identity; the second holds because only $a=0$ survives and $\hat w(0)$ is the total mass.
--
--   As $j$ increases, the band energies decrease from $2^d$ times the $\ell^2$ energy of $w$ to the square of its total mass, which is $0$ for a centered weight. They give a scale on which to measure how the energy of a weight evolving under the Thorp shuffle is distributed among Walsh frequencies.
--
--   **Formalization Note** `prefixZero j a` quantifies over `i : Fin d` with `i.val < j`. For $j\ge d$ it therefore requires $a=0$, so $\mathcal B_j=\mathcal B_d$ for all $j\ge d$. A `Decidable` instance makes the band sum computable as a filtered sum. The endpoint lemmas are `prefixZero_zero`, `prefixZero_full`, `bandEnergy_zero` (where $2^d$ appears as `Fintype.card (Position d)`) and `bandEnergy_full`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/WalshFlow.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/WalshFlow.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uΩ

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

end Conditional

namespace Conditional

def prefixZero {d : ℕ} (j : ℕ) (a : Position d) : Prop :=
  ∀ i : Fin d, i.val < j → a i = false

instance prefixZeroDecidable {d : ℕ} (j : ℕ) (a : Position d) :
    Decidable (prefixZero j a) := by
  unfold prefixZero
  infer_instance

@[simp] theorem prefixZero_zero {d : ℕ} (a : Position d) : prefixZero 0 a := by
  intro i hi
  omega

theorem prefixZero_full {d : ℕ} (a : Position d) :
    prefixZero d a ↔ a = fun _ => false := by
  constructor
  · intro h
    funext i
    exact h i i.isLt
  · intro h
    subst a
    intro i _
    rfl

def bandEnergy (d : ℕ) (w : Position d → ℝ) (j : ℕ) : ℝ := by
  classical
  exact ∑ a : Position d, if prefixZero j a then coefficient w a ^ 2 else 0

@[simp] theorem bandEnergy_zero (d : ℕ) (w : Position d → ℝ) :
    bandEnergy d w 0 = (Fintype.card (Position d) : ℝ) * ∑ x, w x ^ 2 := by
  have hp := parseval w
  unfold mean at hp
  have hc : (Fintype.card (Position d) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ a, coefficient w a ^ 2) =
      (Fintype.card (Position d) : ℝ) * ∑ x, w x ^ 2 := by
    rw [div_eq_iff hc] at hp
    linarith
  simpa [bandEnergy] using hsum

@[simp] theorem bandEnergy_full (d : ℕ) (w : Position d → ℝ) :
    bandEnergy d w d = (∑ x, w x) ^ 2 := by
  classical
  simp [bandEnergy, prefixZero_full]

end Conditional

end Thorp

end

end OAI


