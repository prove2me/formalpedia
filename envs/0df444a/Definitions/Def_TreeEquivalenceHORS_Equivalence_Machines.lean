-- Prove2me | Definitions.Def_TreeEquivalenceHORS_Equivalence_Machines
-- name    : TreeEquivalenceHORS_Equivalence_Machines
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:34.927825+00:00
-- url     : https://prove2.me/theorems/30208f87-523b-4cac-a2ea-4cdf62cd12f4
-- title:
--   Two-counter machines, zero-start halting, candidate executions, legal prefixes and guard weights
-- statement:
--   1. **Machines.** A program is a finite list $M=[\iota_1,\dots,\iota_L]$ of instructions $\mathrm{inc}\,A$, $\mathrm{inc}\,B$, $\mathrm{dec}\,A(j)$, $\mathrm{dec}\,B(j)$ with arbitrary $j\in\mathbb N$; positions $I_M=\{1,\dots,L\}$. On a configuration $(q,a,b)\in\mathbb N^3$ with $q\in I_M$: $\mathrm{inc}\,X$ adds one to $X$ and advances; $\mathrm{dec}\,X(j)$ advances if $X=0$ and otherwise subtracts one and jumps to $j$; the other counter is unchanged. **Zero-start halting** $M\!\downarrow$ means that $(1,0,0)\to_M^*(q,a,b)$ for some $q\notin I_M$. The empty program halts immediately.
--   2. **Candidates.** For an active virtual configuration $s=(i,a,b)\in\mathbb N\times\mathbb Z^2$ and a choice $e\in\{1,2\}$, the successor $\delta^M_e(s)$ of Equation (11) follows increments for both choices; at a test, $e=1$ advances and $e=2$ decrements the tested counter and jumps, without checking the guard. $C_M\subseteq\{1,2\}^*$ is the set of finite words, starting from $\varepsilon$ with $s_M(\varepsilon)=(1,0,0)$, that extend only prefixes whose program counter lies in $I_M$; $\mathrm{pc}_M(v)$ is the final program counter.
--   3. **Legality.** The guard $\gamma^M_e(s)$ is true at increments, $c=0$ for $e=1$ and $c>0$ for $e=2$ at a test of a counter of value $c$. $L_M\subseteq C_M$ is the set of candidates on which every guard holds.
--   4. **Weights.** With $Z_m(X)=\prod_{j=1}^m(X-j)$ ($Z_0=1$), the multiplier of Equation (12) at old clock $m$ is $1$ at an increment, $Z_m(c)$ for $e=1$ and $c$ for $e=2$, with $c$ the old value of the tested counter. $W_M(\varepsilon)=1$ and $W_M(ve)=W_M(v)\,\phi_{|v|}(\iota,e,c)$ (Equation (13)).
--
--   These are the source decision problem and the arithmetic witness of Section 4.
--
--   **Formalization Note** Choices are `Choice.one` ($1$) and `Choice.two` ($2$). Configurations, weights and the polynomial are computed by one left-to-right pass `go`; virtual counters are integers. Outside $I_M$, where the source leaves $\delta$ undefined, the Lean successor returns its argument; candidates never use it.
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Section 2.1 printed p. 4 / PDF p. 6; Section 3 "Source machines" printed p. 11 / PDF p. 13; Section 4.1–4.2, Equations (11)–(13), printed pp. 11–12 / PDF pp. 13–14

import Mathlib

namespace TreeEquivalenceHORS.Equivalence

/-! # Two-counter machines, candidate executions and guard weights
(Sections 2.1, 3, 4; PDF pp. 6, 13–14 / printed pp. 4, 11–12) -/

/-- Instructions `inc A | inc B | dec A (j) | dec B (j)`, with an arbitrary target `j ∈ ℕ`. -/
inductive Instr : Type where
  | incA : Instr
  | incB : Instr
  | decA (j : ℕ) : Instr
  | decB (j : ℕ) : Instr
  deriving DecidableEq, Encodable, Repr

/-- A program `M = [ι₁, …, ι_L]`, any finite list of instructions (possibly empty). -/
abbrev Machine : Type := List Instr

namespace Machine

/-- The one-based lookup `M(i) = ιᵢ`, defined exactly for `i ∈ I_M = {1, …, L}`. -/
def lookup (M : Machine) (i : ℕ) : Option Instr := if i = 0 then none else M[i - 1]?

/-- `i ∈ I_M = {1, …, |M|}`, the active instruction positions. -/
def Active (M : Machine) (i : ℕ) : Prop := 1 ≤ i ∧ i ≤ M.length

instance (M : Machine) (i : ℕ) : Decidable (M.Active i) := by unfold Active; infer_instance

/-- The source step relation `→_M` on configurations `(q, a, b) ∈ ℕ³` (Section 2.1): `inc X`
adds one to `X` and advances; `dec X (j)` advances when `X = 0`, and otherwise subtracts one from
`X` and jumps to `j`. The other counter is unchanged; positions outside `I_M` have no step. -/
inductive Step (M : Machine) : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → Prop where
  | incA {i a b : ℕ} : M.lookup i = some .incA → Step M (i, a, b) (i + 1, a + 1, b)
  | incB {i a b : ℕ} : M.lookup i = some .incB → Step M (i, a, b) (i + 1, a, b + 1)
  | decAZero {i b j : ℕ} : M.lookup i = some (.decA j) → Step M (i, 0, b) (i + 1, 0, b)
  | decAPos {i a b j : ℕ} : M.lookup i = some (.decA j) → Step M (i, a + 1, b) (j, a, b)
  | decBZero {i a j : ℕ} : M.lookup i = some (.decB j) → Step M (i, a, 0) (i + 1, a, 0)
  | decBPos {i a b j : ℕ} : M.lookup i = some (.decB j) → Step M (i, a, b + 1) (j, a, b)

/-- Zero-start halting `M↓`: from `(1, 0, 0)` the machine reaches a configuration whose position is
outside `I_M`. -/
def Halts (M : Machine) : Prop :=
  ∃ q a b : ℕ, Relation.ReflTransGen M.Step (1, 0, 0) (q, a, b) ∧ ¬ M.Active q

end Machine

/-- Candidate choices: `one` (`e = 1`, guess zero) and `two` (`e = 2`, guess positive). -/
inductive Choice : Type where
  | one : Choice
  | two : Choice
  deriving DecidableEq, Repr

/-- The polynomial `Z_m(X) = ∏_{j=1}^{m} (X − j)`, with `Z₀ = 1`. -/
def Zpoly (m : ℕ) (x : ℤ) : ℤ := ∏ j ∈ Finset.range m, (x - ((j : ℤ) + 1))

namespace Machine

/-- The candidate successor `δ_e^M(i, a, b)` of Equation (11) on virtual configurations
`(i, a, b) ∈ ℕ × ℤ × ℤ`. Both choices agree at an increment; at a test, choice `two` decrements
and jumps without checking the guard. (Outside `I_M` the source leaves `δ` undefined; the value
returned there is never used on candidates.) -/
def delta (M : Machine) (e : Choice) (s : ℕ × ℤ × ℤ) : ℕ × ℤ × ℤ :=
  match M.lookup s.1, e with
  | some .incA, _ => (s.1 + 1, s.2.1 + 1, s.2.2)
  | some .incB, _ => (s.1 + 1, s.2.1, s.2.2 + 1)
  | some (.decA _), .one => (s.1 + 1, s.2.1, s.2.2)
  | some (.decA j), .two => (j, s.2.1 - 1, s.2.2)
  | some (.decB _), .one => (s.1 + 1, s.2.1, s.2.2)
  | some (.decB j), .two => (j, s.2.1, s.2.2 - 1)
  | none, _ => s

/-- The branch condition `γ_e^M(s)`: true at an increment; `c = 0` for choice `one` and `c > 0`
for choice `two` at a test of the counter whose value is `c`. -/
def guard (M : Machine) (e : Choice) (s : ℕ × ℤ × ℤ) : Prop :=
  match M.lookup s.1, e with
  | some .incA, _ => True
  | some .incB, _ => True
  | some (.decA _), .one => s.2.1 = 0
  | some (.decA _), .two => 0 < s.2.1
  | some (.decB _), .one => s.2.2 = 0
  | some (.decB _), .two => 0 < s.2.2
  | none, _ => False

/-- The weight multiplier `φ_m(ι, e, c)` of Equation (12), at the old clock `m` and the old value
`c` of the selected counter: `1` at an increment, `Z_m(c)` for choice `one` and `c` for choice
`two` at a test. -/
def phi (M : Machine) (m : ℕ) (e : Choice) (s : ℕ × ℤ × ℤ) : ℤ :=
  match M.lookup s.1, e with
  | some .incA, _ => 1
  | some .incB, _ => 1
  | some (.decA _), .one => Zpoly m s.2.1
  | some (.decA _), .two => s.2.1
  | some (.decB _), .one => Zpoly m s.2.2
  | some (.decB _), .two => s.2.2
  | none, _ => 1

/-- Process a choice word from clock `m` and state `(s, W)`: each letter updates the virtual
configuration by Equation (11) and multiplies the weight by Equation (13), both using old
values, and advances the clock. -/
def go (M : Machine) : ℕ → (ℕ × ℤ × ℤ) × ℤ → List Choice → (ℕ × ℤ × ℤ) × ℤ
  | _, sw, [] => sw
  | m, (s, W), e :: v => go M (m + 1) (M.delta e s, W * M.phi m e s) v

/-- The virtual configuration `s_M(v)`, starting from `s_M(ε) = (1, 0, 0)`. -/
def conf (M : Machine) (v : List Choice) : ℕ × ℤ × ℤ := (M.go 0 ((1, 0, 0), 1) v).1

/-- The weight `W_M(v)`, with `W_M(ε) = 1`. -/
def weight (M : Machine) (v : List Choice) : ℤ := (M.go 0 ((1, 0, 0), 1) v).2

/-- The final program counter `pc_M(v)`. -/
def pc (M : Machine) (v : List Choice) : ℕ := (M.conf v).1

/-- `v ∈ C_M`: the candidate prefixes, generated from `ε` by extending only active prefixes
(every proper prefix has its program counter in `I_M`). -/
def IsCand (M : Machine) (v : List Choice) : Prop :=
  ∀ k < v.length, M.Active (M.pc (v.take k))

/-- `v ∈ L_M`: a candidate prefix on which every guessed guard holds. -/
def IsLegal (M : Machine) (v : List Choice) : Prop :=
  M.IsCand v ∧ ∀ (k : ℕ) (h : k < v.length), M.guard v[k] (M.conf (v.take k))

end Machine

end TreeEquivalenceHORS.Equivalence


