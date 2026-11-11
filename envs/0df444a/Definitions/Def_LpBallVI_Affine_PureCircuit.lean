-- Prove2me | Definitions.Def_LpBallVI_Affine_PureCircuit
-- name    : LpBallVI_Affine_PureCircuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:10:28.156955+00:00
-- url     : https://prove2.me/theorems/9996dc6b-147b-4354-9fbf-ba7508db3f53
-- title:
--   PureCircuit: NOR/PURIFY instances, {0,1,⊥} solutions, its search problem, the threshold functions ϕ_NOR, ϕ_PURIFY, the operator T and the rounding of Lemma 2.3
-- statement:
--   A **PureCircuit instance** has nodes $V = \{0, \dots, n-1\}$ and a list of gates: $w = \mathrm{NOR}(u, v)$, or $(v, w) = \mathrm{PURIFY}(u)$. It is well formed when the three nodes of every gate are distinct and every node is the output of exactly one gate. An assignment $g : V \to \{0, 1, \bot\}$ is a **solution** when every NOR gate satisfies $g(u) = g(v) = 0 \Rightarrow g(w) = 1$ and ($g(u) = 1$ or $g(v) = 1$) $\Rightarrow g(w) = 0$, and every PURIFY gate satisfies $g(u) \in \{0,1\} \Rightarrow g(v) = g(w) = g(u)$ and $g(u) = \bot \Rightarrow$ at least one of $g(v), g(w)$ lies in $\{0,1\}$. The search problem **PureCircuit** has as valid inputs the codes of well-formed instances and as answers the codes of solutions.
--
--   The threshold functions are
--   $$\phi_{\rm NOR}(t) = \begin{cases} 1 & t \le 1/4\\ 2 - 4t & 1/4 \le t \le 1/2\\ 0 & t \ge 1/2\end{cases},\qquad \phi_{\rm PURIFY}(s) = \begin{cases} 0 & s \le 5/12\\ 6s - 5/2 & 5/12 \le s \le 7/12\\ 1 & s \ge 7/12.\end{cases}$$
--   For $x \in \mathbb R^n$ the scalar input of node $v$ is $s_v(x) = x_u + x_{u'}$ if $v = \mathrm{NOR}(u, u')$, and $x_u + 1/4$ (resp. $x_u - 1/4$) if $v$ is the first (resp. second) output of $\mathrm{PURIFY}(u)$; $T_v(x) = \phi_{\rm NOR}(s_v(x))$ for a NOR output and $\phi_{\rm PURIFY}(s_v(x))$ for a PURIFY output. The rounding of $x$ is $g(v) = 0$ if $x_v \le 1/8$, $1$ if $x_v \ge 7/8$, $\bot$ otherwise.
--
--   **Formalization Note** Code of an instance: $n$, the number of gates, then each gate as a type bit and its three nodes in self-delimiting binary; an assignment is 2 bits per node ($0 \mapsto 00$, $1 \mapsto 01$, $\bot \mapsto 10$). $T$ and $s_v$ read the gate of which $v$ is an output (unique in a well-formed instance).
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 13, §2.2 and Theorem 2.2; p. 14, (2)–(4) and Lemma 2.3

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix

set_option autoImplicit false

namespace LpBallVI.Affine

open QAlgorithms.LocalHamiltonian

/-- A gate of a `PureCircuit` instance on the nodes `Fin n` (Anagnostides–Panageas–Yan,
arXiv:2611.04151, §2.2, p. 13, after Deligkas–Fearnley–Hollender–Melissourgos 2024):
`nor u v w` is `w = NOR(u, v)`, and `purify u v w` is `(v, w) = PURIFY(u)`. -/
inductive PCGate (n : ℕ) where
  | nor (u v w : Fin n)
  | purify (u v w : Fin n)

/-- The output nodes of a gate. -/
def PCGate.outputs {n : ℕ} : PCGate n → List (Fin n)
  | .nor _ _ w => [w]
  | .purify _ v w => [v, w]

/-- The three nodes of a gate. -/
def PCGate.nodes {n : ℕ} : PCGate n → List (Fin n)
  | .nor u v w => [u, v, w]
  | .purify u v w => [u, v, w]

/-- A `PureCircuit` instance: `n` nodes and a list of gates. -/
structure PCInst where
  n : ℕ
  gates : List (PCGate n)

/-- A well-formed instance (p. 13): "The three nodes appearing in any gate are distinct, and each
node in the circuit is the output of exactly one gate" (counting gate occurrences in the list). -/
def PCInst.WellFormed (I : PCInst) : Prop :=
  (∀ g ∈ I.gates, g.nodes.Nodup) ∧
    ∀ v : Fin I.n, (I.gates.filter (fun g => decide (v ∈ g.outputs))).length = 1

/-- The values `{0, 1, ⊥}` of a `PureCircuit` assignment (p. 13). -/
inductive PVal where
  | zero
  | one
  | bot
  deriving DecidableEq

/-- `g : V → {0, 1, ⊥}` is a **solution** of the instance (p. 13). NOR, `w = NOR(u, v)`:
`g(u) = g(v) = 0 ⇒ g(w) = 1`, and `g(u) = 1` or `g(v) = 1 ⇒ g(w) = 0`. PURIFY, `(v, w) = PURIFY(u)`:
`g(u) ∈ {0, 1} ⇒ g(v) = g(w) = g(u)`, and `g(u) = ⊥ ⇒` at least one of `g(v), g(w)` lies in
`{0, 1}`. -/
def PCInst.IsSolution (I : PCInst) (g : Fin I.n → PVal) : Prop :=
  ∀ gt ∈ I.gates, match gt with
    | .nor u v w =>
        (g u = .zero ∧ g v = .zero → g w = .one) ∧ (g u = .one ∨ g v = .one → g w = .zero)
    | .purify u v w =>
        (g u ≠ .bot → g v = g u ∧ g w = g u) ∧ (g u = .bot → g v ≠ .bot ∨ g w ≠ .bot)

/-- Binary code of a gate: a type bit (`false` NOR, `true` PURIFY), then its three nodes in
self-delimiting binary. -/
def PCGate.code {n : ℕ} : PCGate n → List Bool
  | .nor u v w => false :: (encBin u.val ++ encBin v.val ++ encBin w.val)
  | .purify u v w => true :: (encBin u.val ++ encBin v.val ++ encBin w.val)

/-- Binary code of an instance: `n`, the number of gates, then the gates. -/
def PCInst.code (I : PCInst) : List Bool :=
  encBin I.n ++ encBin I.gates.length ++ I.gates.flatMap PCGate.code

/-- Binary code of a value: `0 ↦ 00`, `1 ↦ 01`, `⊥ ↦ 10`. -/
def PVal.code : PVal → List Bool
  | .zero => [false, false]
  | .one => [false, true]
  | .bot => [true, false]

/-- Binary code of an assignment `g : Fin n → {0, 1, ⊥}`: the values of nodes `0, …, n − 1`. -/
def assignCode {n : ℕ} (g : Fin n → PVal) : List Bool :=
  (List.finRange n).flatMap (fun v => (g v).code)

/-- **The search problem `PureCircuit`** (p. 13): valid strings are codes of well-formed
instances; an answer is the code of a solution `g : V → {0, 1, ⊥}`. -/
def PureCircuit : TetrisHard.Rows.SearchProblem where
  valid s := ∃ I : PCInst, I.WellFormed ∧ s = I.code
  answer s t := ∃ I : PCInst, I.WellFormed ∧ s = I.code ∧
    ∃ g : Fin I.n → PVal, t = assignCode g ∧ I.IsSolution g

/-- The threshold function `ϕ_NOR` (p. 13): `1` for `t ≤ 1/4`, `2 − 4t` on `[1/4, 1/2]`, `0` for
`t ≥ 1/2`. -/
noncomputable def phiNOR (t : ℝ) : ℝ :=
  if t ≤ 1 / 4 then 1 else if t ≤ 1 / 2 then 2 - 4 * t else 0

/-- The threshold function `ϕ_PURIFY` (p. 13): `0` for `s ≤ 5/12`, `6s − 5/2` on `[5/12, 7/12]`,
`1` for `s ≥ 7/12`. -/
noncomputable def phiPURIFY (s : ℝ) : ℝ :=
  if s ≤ 5 / 12 then 0 else if s ≤ 7 / 12 then 6 * s - 5 / 2 else 1

/-- The gate of which node `v` is an output (the first such gate in the list; it is the only one
when the circuit is well formed). -/
def PCInst.gateOf (I : PCInst) (v : Fin I.n) : Option (PCGate I.n) :=
  I.gates.find? (fun g => decide (v ∈ g.outputs))

/-- `v` is the output of a NOR gate. -/
def PCInst.IsNorOutput (I : PCInst) (v : Fin I.n) : Prop :=
  ∃ u u' w, I.gateOf v = some (.nor u u' w)

/-- The scalar input `s_v(x)` of node `v` (p. 14): `x_u + x_{u'}` if `v = NOR(u, u')`;
`x_u + 1/4` if `v` is the first and `x_u − 1/4` if it is the second output of `PURIFY(u)`. -/
noncomputable def PCInst.sIn (I : PCInst) (x : Fin I.n → ℝ) (v : Fin I.n) : ℝ :=
  match I.gateOf v with
  | some (.nor u u' _) => x u + x u'
  | some (.purify u v' _) => if v = v' then x u + 1 / 4 else x u - 1 / 4
  | none => 0

/-- The operator `T : ℝⁿ → [0, 1]ⁿ` of (2)–(4), p. 14: `T_v(x) = ϕ_NOR(s_v(x))` for a NOR output,
`T_v(x) = ϕ_PURIFY(s_v(x))` for a PURIFY output. -/
noncomputable def PCInst.T (I : PCInst) (x : Fin I.n → ℝ) (v : Fin I.n) : ℝ :=
  match I.gateOf v with
  | some (.nor _ _ _) => phiNOR (I.sIn x v)
  | some (.purify _ _ _) => phiPURIFY (I.sIn x v)
  | none => 0

/-- The rounding of Lemma 2.3 (p. 14): `g(v) = 0` if `x_v ≤ 1/8`, `1` if `x_v ≥ 7/8`, `⊥`
otherwise. -/
noncomputable def roundAssign {n : ℕ} (x : Fin n → ℝ) (v : Fin n) : PVal :=
  if x v ≤ 1 / 8 then .zero else if 7 / 8 ≤ x v then .one else .bot

end LpBallVI.Affine


