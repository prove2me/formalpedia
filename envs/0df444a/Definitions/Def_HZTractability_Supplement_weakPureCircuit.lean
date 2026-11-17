-- Prove2me | Definitions.Def_HZTractability_Supplement_weakPureCircuit
-- name    : HZTractability_Supplement_weakPureCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:27:17.194361+00:00
-- url     : https://prove2.me/theorems/ba47b12d-1aa5-4f1d-9b2f-88fd29d6e7b2
-- title:
--   Weak $\delta$-Pure-Circuit (Definitions 5.1–5.2), without the input-once restriction
-- statement:
--   A **Pure-Circuit instance** consists of a finite node set $V_C$ and a nonempty collection $\mathcal G$ of gates $(T,u,v,w)$ with pairwise distinct $u,v,w\in V_C$ and $T\in\{\mathrm{NOR},\mathrm{PURIFY}\}$. A NOR gate has inputs $u,v$ and output $w$; a PURIFY gate has input $u$ and outputs $v,w$. Every node is produced by exactly one gate.
--
--   An assignment is a map $\xi:V_C\to\{0,1,\bot\}$. A NOR gate is **satisfied** when
--   $$\xi_u=\xi_v=0\implies\xi_w=1,\qquad \xi_u=1\text{ or }\xi_v=1\implies\xi_w=0,$$
--   and its output is unrestricted otherwise. A PURIFY gate is satisfied when
--   $$\xi_u=b\in\{0,1\}\implies\xi_v=\xi_w=b,\qquad \xi_u=\bot\implies\{\xi_v,\xi_w\}\cap\{0,1\}\neq\emptyset.$$
--
--   For a parameter $\delta$, the search problem **weak $\delta$-Pure-Circuit** asks, given an instance, for an assignment that fails at most $\delta\,|\mathcal G|$ gates, each PURIFY gate counted once. No input-once restriction is imposed: a node may be the input of any number of gates.
--
--   This is the circuit problem through which the paper states the PCP-for-PPAD conjecture (hypothesis of Theorem 1.2).
--
--   **Formalization Note** Instances, well-formedness and the binary codes are the published Pure-Circuit layer `LpBallVI.Affine` (`PCInst`, `PCGate`, `PVal`, `PCInst.WellFormed`, `PCInst.code`, `assignCode`); $V_C=\{0,\dots,n-1\}$. Nonemptiness of $\mathcal G$ is added explicitly. Since every node is the output of exactly one gate, no gate is listed twice, so the list length is $|\mathcal G|$. Definition 5.2 has $\delta\in[0,1]$; that range is imposed where the problem is used.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Definition 5.1 and Definition 5.2, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_LpBallVI_Affine_PureCircuit

set_option autoImplicit false

namespace HZTractability.Supplement

open LpBallVI.Affine

/-- A gate is **satisfied** by an assignment `ξ : V_C → {0, 1, ⊥}` (Panageas–Shein–Taherijam–Vazirani,
*Exploring the Tractability Frontier of Hylland–Zeckhauser Models*, arXiv:2610.35848, held version,
sha256 74b7bf9f…, Definition 5.1, p.20 (PDF 22)). A NOR gate with inputs `u, v` and output `w`:
`ξu = ξv = 0 ⟹ ξw = 1` and `ξu = 1 or ξv = 1 ⟹ ξw = 0` (unrestricted otherwise). A PURIFY gate with
input `u` and outputs `v, w`: `ξu = b ∈ {0, 1} ⟹ ξv = ξw = b`, and `ξu = ⊥ ⟹ {ξv, ξw} ∩ {0, 1} ≠ ∅`.

**Formalization Note** Gates and values are the published `LpBallVI.Affine.PCGate` / `PVal`;
`nor u v w` is `w = NOR(u, v)` and `purify u v w` is `(v, w) = PURIFY(u)`. These are exactly the
per-gate clauses of the published `PCInst.IsSolution`. -/
def gateSat {n : ℕ} (ξ : Fin n → PVal) : PCGate n → Prop
  | .nor u v w =>
      (ξ u = .zero ∧ ξ v = .zero → ξ w = .one) ∧ (ξ u = .one ∨ ξ v = .one → ξ w = .zero)
  | .purify u v w =>
      (ξ u ≠ .bot → ξ v = ξ u ∧ ξ w = ξ u) ∧ (ξ u = .bot → ξ v ≠ .bot ∨ ξ w ≠ .bot)

open Classical in
/-- The number of gates of the instance that the assignment `ξ` **fails** (Definition 5.2, p.20
(PDF 22)): each gate is counted once, a PURIFY gate included. -/
noncomputable def failCount (I : PCInst) (ξ : Fin I.n → PVal) : ℕ :=
  (I.gates.filter (fun gt => decide (¬ gateSat ξ gt))).length

/-- **Weak δ-Pure-Circuit** (arXiv:2610.35848, held version, sha256 74b7bf9f…, Definitions 5.1 and
5.2, p.20 (PDF 22)): "An instance consists of a finite node set V_C and a nonempty collection G of
gates (T, u, v, w), with pairwise distinct u, v, w ∈ V_C and T ∈ {NOR, PURIFY}. … Every node is
produced by exactly one gate." "For δ ∈ [0, 1], a weak δ-Pure-Circuit solution fails at most δ|G|
gates, counting each PURIFY gate once."

Valid strings are the codes of well-formed instances (the three nodes of each gate pairwise distinct,
every node the output of exactly one gate) with a nonempty list of gates; an answer is the code of an
assignment `ξ : V_C → {0, 1, ⊥}` failing at most `δ · |G|` gates. There is **no** input-once
restriction.

**Formalization Note** Instances, the well-formedness condition and the codes (`PCInst.code`: `n`, the
number of gates, then each gate's type bit and three node indices in self-delimiting binary;
`assignCode`: two bits per node) are the published `LpBallVI.Affine` Pure-Circuit layer, so the
instance is recoverable from its code. `V_C = Fin n`. Since every node is the output of exactly one
gate, no gate occurs twice in the list, so the list length is `|G|`. The parameter `δ` is rational
and unconstrained here; Definition 5.2 has `δ ∈ [0, 1]`, imposed where it is used. -/
def weakPureCircuit (δ : ℚ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ I : PCInst, I.WellFormed ∧ I.gates ≠ [] ∧ s = I.code
  answer s t := ∃ I : PCInst, I.WellFormed ∧ I.gates ≠ [] ∧ s = I.code ∧
    ∃ ξ : Fin I.n → PVal, t = assignCode ξ ∧ ((failCount I ξ : ℕ) : ℚ) ≤ δ * I.gates.length

end HZTractability.Supplement


