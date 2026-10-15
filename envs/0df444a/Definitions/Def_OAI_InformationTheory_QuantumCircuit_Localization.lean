-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization
-- name    : OAI_InformationTheory_QuantumCircuit_Localization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:22:15.56335+00:00
-- url     : https://prove2.me/theorems/b3d9547d-b1c3-46d2-b383-95be6d1aba82
-- title:
--   Uniform localization at scales $(s,t)$ for depth-$d$ normal-form circuits
-- statement:
--   Fix a depth $d\in\mathbb{N}$ and real exponents $s,t$. The file defines the proposition $\mathrm{UL}(d,s,t)$: there is $N_0$ such that for every $N\ge N_0$, every normal-form circuit $U\in\mathrm{Circ}_d$ on $N$ qubits and every pair of counts $M,D$ on $N$ qubits,
--
--   $$
--   \bigl\|\,\Pi^M_{\ge N^{t}}\;U\,\Pi^D_0\,U^{*}\;\Pi^M_0\,\bigr\|\;\le\;e^{-N^{s}} .
--   $$
--
--   Here $\Pi^M_0$ is the product projection of $M$ (no mismatches), $\Pi^M_{\ge N^t}$ is the spectral projection onto at least $N^t$ mismatches of $M$, $\Pi^D_0$ is the product projection of $D$, and $\|\cdot\|$ is the operator norm. The threshold $N_0$ depends only on $(d,s,t)$, not on $N$, $U$, $M$ or $D$.
--
--   The localization statement for depth $d$ is exactly $\mathrm{UL}(d,s,t)$ for all $0\le s<t$. Formulating it as a property of a scale pair $(s,t)$ lets the proof run by induction on $d$ and, at fixed depth, by a bootstrap over finitely many scale pairs: $\mathrm{UL}(d+1,s,t)$ is deduced from $\mathrm{UL}(d+1,t,b)$ at a larger scale $b$, starting from the trivial range $t>1$, where $N^t>N$ exceeds every possible number of mismatches.
--
--   **Formalization Note** The Lean name is `UniformLocalization d s t`. The eventual quantifier is `∀ᶠ N : ℕ in Filter.atTop`, placed outside all circuit data; $U\Pi^D_0U^*$ is written `conjugate U D.zero`, and $N^t$ is the real power `(N:ℝ)^t`. The definition itself imposes no condition on $s$ and $t$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Localization.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Localization.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the QACParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

/-- The uniform estimate, with the eventual quantifier outside all circuit data. -/
def UniformLocalization (d : ℕ) (s t : ℝ) : Prop :=
  ∀ᶠ N : ℕ in Filter.atTop, ∀ U : Operator N, IsCircuit d U → ∀ M D : Count N,
    ‖M.high ((N:ℝ)^t)*conjugate U D.zero*M.zero‖ ≤ Real.exp (-((N:ℝ)^s))

end QAC

end

end OAI


