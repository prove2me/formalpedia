-- Prove2me | Definitions.Def_OAI_Analysis_ModularRecovery_Model
-- name    : OAI_Analysis_ModularRecovery_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:10:00.305471+00:00
-- url     : https://prove2.me/theorems/cd0b7f8f-9f11-445b-9f47-c3b66d1378b7
-- title:
--   The vector state of standard modular data
-- statement:
--   These notions belong to a formal proof of a bounded recovery theorem in Tomita–Takesaki theory. Let $M$ be a von Neumann algebra on a Hilbert space $H$ with a cyclic and separating unit vector $\xi$, and let $\varphi(a)=\langle\xi,a\xi\rangle$. The modular data are encoded by a nondegenerate $*$-homomorphism $f\mapsto f(D)$ from bounded continuous functions on $\mathbb R$ to bounded operators, thought of as the functional calculus of $D=\log\Delta$. It comes with the unitary group $\Delta^{it}=e^{itD}$, the modular automorphisms $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$, and an antiunitary involution $J$. The Tomita relation requires the closure of $\{(a\xi,a^*\xi):a\in M\}$ to be the graph of $J\Delta^{1/2}$. The theorem says that when $\varphi$ has trivial centralizer, a vector in a narrow spectral band of $D$ on which an operator $T$ is not small can be replaced by $v\xi$, with $v\in M$ uniformly bounded and $v\xi$ in a comparable band.
--
--   1. **Vector state.** For standard modular data with cyclic separating vector $\xi$ and an operator $a$,
--   $$
--   \varphi(a)=\langle\xi,a\xi\rangle .
--   $$
--   On $M$ this is a faithful normal state. Its centralizer, the elements $a$ with $\varphi(ab)=\varphi(ba)$ for all $b\in M$, is assumed to consist of scalars in the theorem.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ModularRecovery/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ModularRecovery/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BoundedRecovery mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BoundedRecovery

namespace OAI

/-! Nondegenerate spectral calculus, the closed Tomita graph, and bounded recovery. -/

universe u

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace RealSpectralCalculus

end RealSpectralCalculus

namespace StandardModularData

end StandardModularData

namespace StandardModularData

def state (S : StandardModularData H) (a : H →L[ℂ] H) : ℂ :=
  inner ℂ S.xi (a S.xi)

end StandardModularData

end BoundedRecovery

end

end OAI


