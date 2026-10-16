-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalSets
-- name    : OAI_InformationTheory_AmplitudeDamping_TypicalSets
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:30:31.206994+00:00
-- url     : https://prove2.me/theorems/6d535a02-2d38-49ba-a02f-09adce90eb24
-- title:
--   Entropy-typical strings of an i.i.d. source
-- statement:
--   Let $\alpha$ be a finite alphabet, $q:\alpha\to\mathbb{R}$ a function (in applications a probability distribution), $n\in\mathbb{N}$, and $x=(x_1,\dots,x_n)\in\alpha^n$ a string. All logarithms are natural. The file defines:
--
--   1. **Product weight.** $q^{n}(x)=\prod_{j=1}^{n}q(x_j)$, the i.i.d. probability of $x$.
--
--   2. **Additive functional.** For $f:\alpha\to\mathbb{R}$, $S_nf(x)=\sum_{j=1}^{n}f(x_j)$.
--
--   3. **Shannon entropy.** $H(q)=\sum_{a\in\alpha}-q(a)\log q(a)$, with the convention $0\log0=0$.
--
--   4. **Centered information density.** $\ell_q(a)=-\log q(a)-H(q)$ for $a\in\alpha$.
--
--   5. **Varentropy.** $V(q)=\sum_{a\in\alpha}q(a)\,\ell_q(a)^2$, the variance of $-\log q$ under $q$.
--
--   6. **Typicality.** For $\delta\in\mathbb{R}$, a string $x\in\alpha^n$ is $\delta$-typical when
--   $$q^{n}(x)>0\qquad\text{and}\qquad\Bigl|\sum_{j=1}^{n}\bigl(-\log q(x_j)-H(q)\bigr)\Bigr|\le n\delta .$$
--
--   7. **Typical set.** $T^{n}_{q,\delta}\subseteq\alpha^n$ is the finite set of all $\delta$-typical strings.
--
--   For a probability distribution $q$, a string is $\delta$-typical exactly when $e^{-n(H(q)+\delta)}\le q^n(x)\le e^{-n(H(q)-\delta)}$. These definitions support the standard estimates $|T^{n}_{q,\delta}|\le e^{n(H(q)+\delta)}$ and, for $\delta>0$ and $n\ge1$, $q^n(\alpha^n\setminus T^{n}_{q,\delta})\le V(q)/(n\delta^2)$ (Chebyshev's inequality), which are used to build typical subspaces for coding over many channel uses.
--
--   **Formalization Note** Strings are functions `Fin n → α`. The Lean names are `iidWeight`, `iidSum`, `classicalEntropy` (a sum of `Real.negMulLog`), `centeredLog`, `logVariance`, `IsTypical` and `typicalSet` (a `Finset` obtained by filtering `Finset.univ`, using a local classical decidability instance). Since `Real.log 0 = 0`, one has $\ell_q(a)=-H(q)$ when $q(a)=0$; such symbols never occur in typical strings because of the positivity condition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/TypicalSets.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/TypicalSets.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AmplitudeDamping mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EntropyContinuity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_BlockFactors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Naimark
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_HolevoInformation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EnsembleBounds
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseStates
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseProducts
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CapacityConverse
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialMatrices

namespace OAI

noncomputable section

universe u_1 u_2

section
open scoped BigOperators
namespace GAD
variable {α : Type u_1} [Fintype α]

def iidWeight (q : α → ℝ) (n : ℕ) (x : Fin n → α) : ℝ := ∏ j, q (x j)
def iidSum (f : α → ℝ) (n : ℕ) (x : Fin n → α) : ℝ := ∑ j, f (x j)

end GAD

end

open scoped BigOperators
namespace GAD
variable {α : Type u_2} [Fintype α]
local instance instDecidablePred_oAI : DecidablePred (fun p : Prop ↦ p) := Classical.propDecidable

def classicalEntropy (q : α → ℝ) : ℝ := ∑ a, Real.negMulLog (q a)
def centeredLog (q : α → ℝ) (a : α) : ℝ := -Real.log (q a)-classicalEntropy q
def logVariance (q : α → ℝ) : ℝ := ∑ a, q a*(centeredLog q a)^2

def IsTypical (q : α → ℝ) (δ : ℝ) (n : ℕ) (x : Fin n → α) : Prop :=
  0 < iidWeight q n x ∧ |iidSum (centeredLog q) n x| ≤ (n:ℝ)*δ

def typicalSet (q : α → ℝ) (δ : ℝ) (n : ℕ) : Finset (Fin n → α) :=
  Finset.univ.filter (IsTypical q δ n)

end GAD

end

end OAI


