-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_RegularTreeCircuit
-- name    : PPADSIS_SubexpSIS_RegularTreeCircuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:46:46.231475+00:00
-- url     : https://prove2.me/theorems/2043180b-0fdf-4170-9b34-bf2a2318083a
-- title:
--   Regular tree circuits: node values, output, size, description; exhaustive-search output (Definition 3.8)
-- statement:
--   A **regular tree circuit** $C=(p,C_0,\dots,C_p)$ (Definition 3.8) consists of an address length $p$, a Boolean leaf circuit $C_0:\{0,1\}^p\to\{0,1\}^{v_0}$ and Boolean combining circuits $C_h:\{0,1\}^{2v_{h-1}}\to\{0,1\}^{v_h}$ for $h\in[p]$. The nodes of its tree are the strings $\eta\in\{0,1\}^{\le p}$; $\eta$ has children $\eta0,\eta1$ and height $p-|\eta|$; the root is $\varepsilon$ and the $P=2^p$ leaves are the addresses $a=a_{p-1}\cdots a_0\in\{0,1\}^p$, ordered lexicographically. Values are defined bottom-up:
--   $$u_a:=C_0(a),\qquad u_\eta:=C_h(u_{\eta0},u_{\eta1})\quad(\eta\text{ of height }h\ge1).$$
--   The **output** of $C$ is $u_\varepsilon$, and its **size** $|C|$ is the total size of $C_0,\dots,C_p$, where the size of a Boolean circuit counts its input wires as well as its gates. $C$ is **well formed** if it has $p$ combining circuits, all well formed, $C_0$ has $p$ inputs and $C_h$ has $2v_{h-1}$ inputs.
--
--   For a predicate $\varphi$ on $\{0,1\}^p$, the **exhaustive-search output** is $(1,a^*)$ for the lexicographically first $a^*\in\{0,1\}^p$ with $\varphi(a^*)$, and $(0,0^p)$ if there is none (Lemma 3.9).
--
--   **Formalization Note** A node is the list of branch bits from the root, so the first address bit is $a_{p-1}$. A pair $(s,w)$ is the string $s\,w$. Strings of length $p$ in lexicographic order are the numbers they write in big-endian binary, so $a^*$ is $\mathrm{bin}_p(k)$ for the least $k<2^p$ with $\varphi(\mathrm{bin}_p(k))$. The description is `encNat p`, the leaf circuit's description, `encNat` of the number of combining circuits and their descriptions.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 22, Definition 3.8 and Lemma 3.9

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Circuit

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

/-- The empty circuit (no inputs, gates or outputs), used as a default value. -/
def Circuit.empty : Circuit := ⟨0, [], []⟩

/-- A **regular tree circuit** `C = (p, C0, …, Cp)` (Choudhuri, *PPAD Hardness from SIS*, STOC 2027
submission (manuscript sha256 17abad73…), Definition 3.8, p. 22): an address length `p`, a Boolean
leaf circuit `C0 : {0,1}^p → {0,1}^{v0}`, and Boolean combining circuits
`Ch : {0,1}^{2 v_{h−1}} → {0,1}^{v_h}` for `h ∈ [p]`; `comb[h − 1]` is `Ch`. -/
structure RTC where
  p : ℕ
  leaf : Circuit
  comb : List Circuit

/-- The combining circuit `Ch` for `h ∈ [p]` (`comb[h − 1]`). -/
def RTC.combAt (C : RTC) (h : ℕ) : Circuit := C.comb.getD (h - 1) Circuit.empty

/-- The output width `v_h` of the circuit at height `h` (`v_0` for the leaf circuit). -/
def RTC.width (C : RTC) (h : ℕ) : ℕ :=
  if h = 0 then C.leaf.outs.length else (C.combAt h).outs.length

/-- The arities of Definition 3.8: there are `p` combining circuits, all circuits are well formed,
`C0` has `p` inputs, and `Ch` has `2 v_{h−1}` inputs for `h ∈ [p]`. -/
def RTC.WF (C : RTC) : Prop :=
  C.comb.length = C.p ∧ C.leaf.WF ∧ C.leaf.nIn = C.p ∧
  ∀ h, 1 ≤ h → h ≤ C.p → (C.combAt h).WF ∧ (C.combAt h).nIn = 2 * C.width (h - 1)

/-- The **value `u_η` at a node** `η ∈ {0,1}^{p−h}` of height `h`, defined bottom-up (Definition 3.8):
`u_a := C0(a)` at a leaf `a`, and `u_η := Ch(u_{η0}, u_{η1})` at height `h ≥ 1`. A node is the
string of branch bits from the root; the children of `η` are `η0` and `η1`, so the leaves
`a = a_{p−1} ⋯ a_0` are ordered lexicographically from left to right. -/
def RTC.nodeVal (C : RTC) : ℕ → List Bool → List Bool
  | 0, η => C.leaf.eval η
  | h + 1, η => (C.combAt (h + 1)).eval (C.nodeVal h (η ++ [false]) ++ C.nodeVal h (η ++ [true]))

/-- The **output** `u_ε` of the regular tree circuit: the value at the root `ε` (height `p`). -/
def RTC.output (C : RTC) : List Bool := C.nodeVal C.p []

/-- The **size** `|C|` (Definition 3.8): the total size of `C0, …, Cp`, where the size of a Boolean
circuit counts its input wires as well as its gates (`Circuit.size`). -/
def RTC.size (C : RTC) : ℕ := C.leaf.size + (C.comb.map Circuit.size).sum

/-- The **description** of a regular tree circuit: `encNat p`, the leaf circuit's description,
`encNat` of the number of combining circuits, and their descriptions in order of height. -/
def RTC.enc (C : RTC) : List Bool :=
  encNat C.p ++ C.leaf.enc ++ encNat C.comb.length ++ C.comb.flatMap Circuit.enc

open Classical in
/-- The **exhaustive-search output** for a predicate `φ` on `{0,1}^p` (Lemma 3.9, p. 22): `(1, a*)`,
written `true :: a*`, for the lexicographically first `a* ∈ {0,1}^p` with `φ(a*)`, and `(0, 0^p)`,
written `false :: 0^p`, if there is none. Strings of length `p` are compared lexicographically,
which is the order of the numbers they write in big-endian binary, so `a*` is `bitsBE p k` for the
least `k < 2^p` with `φ(bitsBE p k)`. -/
noncomputable def searchOutput (p : ℕ) (φ : List Bool → Prop) : List Bool :=
  if h : ∃ k, k < 2 ^ p ∧ φ (bitsBE p k) then true :: bitsBE p (Nat.find h)
  else false :: List.replicate p false

end PPADSIS.SubexpSIS


