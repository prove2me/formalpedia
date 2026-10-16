-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputEntropy
-- name    : OAI_InformationTheory_AmplitudeDamping_OutputEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:16:53.809977+00:00
-- url     : https://prove2.me/theorems/28410c74-74d4-4447-8a3f-3b4444cd5d53
-- title:
--   Relabeling the sites of multi-qubit strings by a permutation
-- statement:
--   Let $n\ge0$, let $\alpha$ be any set, and let $e$ be a permutation of the set of sites $\{0,1,\dots,n-1\}$. The relabeling map
--   $$\tau_e:\alpha^n\to\alpha^n,\qquad(\tau_e\,i)_k=i_{e^{-1}(k)},$$
--   moves the entry at site $k$ to site $e(k)$. It is a bijection with inverse $(\tau_e^{-1}\,i)_k=i_{e(k)}$, and these two formulas are recorded as simplification rules.
--
--   Taking $\alpha=\{0,1\}$ (bit strings) or $\alpha=\{0,1,2,3\}$ (strings of single-qubit Kraus labels), $\tau_e$ permutes the tensor factors of $n$-qubit objects; an $n$-qubit matrix $P$ is relabeled to $P^{\tau_e}$ with $(P^{\tau_e})_{ab}=P_{\tau_e^{-1}a,\,\tau_e^{-1}b}$. The memoryless $n$-qubit generalized amplitude-damping channel $\mathcal N_n$ commutes with every such relabeling, and site populations $\pi_j(P)=\sum_{i:\,i_j=1}\operatorname{Re}P_{ii}$ transform as $\pi_j(P^{\tau_e})=\pi_{e^{-1}(j)}(P)$. This transports statements proved for the first qubit to an arbitrary qubit $j$; for instance, for $\gamma,\nu\in[0,1]$ and every density matrix $P$, $\pi_j(\mathcal N_n(P))=(1-\gamma)\,\pi_j(P)+\gamma\nu$.
--
--   **Formalization Note** `coordinatePerm e` is an `Equiv` on `Fin n → α` given by `i ↦ i ∘ e.symm`; the simp lemmas `coordinatePerm_apply` and `coordinatePerm_symm_apply` are the two coordinate formulas above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/OutputEntropy.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/OutputEntropy.lean by skeleton subtraction
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

namespace OAI

noncomputable section

universe u_1 u_2 u_3

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

/-- Relabeling the tensor sites. -/
def coordinatePerm {n : ℕ} {α : Type u_1} (e : Equiv.Perm (Fin n)) : (Fin n → α) ≃ (Fin n → α) where
  toFun i := i ∘ e.symm
  invFun i := i ∘ e
  left_inv i := by ext k; simp
  right_inv i := by ext k; simp

@[simp] theorem coordinatePerm_apply {n : ℕ} {α : Type u_2} (e : Equiv.Perm (Fin n))
    (i : Fin n → α) (k : Fin n) : coordinatePerm e i k = i (e.symm k) := rfl
@[simp] theorem coordinatePerm_symm_apply {n : ℕ} {α : Type u_3} (e : Equiv.Perm (Fin n))
    (i : Fin n → α) (k : Fin n) : (coordinatePerm e).symm i k = i (e k) := rfl

end GAD

end

end OAI


