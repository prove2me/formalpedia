-- Prove2me | Definitions.Def_PathCount2k_Supplement_Circuit
-- name    : PathCount2k_Supplement_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:20:10.5542+00:00
-- url     : https://prove2.me/theorems/f10b725c-42db-44b5-bf9d-0129169763c2
-- title:
--   Def. 4.1 — normalized monotone arithmetic circuits and the multilinear coefficient sum $M_k(f)$
-- statement:
--   A **normalized monotone arithmetic circuit** over variables $x_1,\dots,x_n$ (Definition 4.1) is a directed acyclic computation with a distinguished output gate $o$. Each gate $v$ computes a polynomial $f_v$ and is
--
--   1. a leaf labelled by a variable $x_i$, or
--   2. a sum gate $f_v=\sum_{e=(v,u)}a_e f_u$ with real weights $a_e\ge 0$, parallel wires being distinguished, or
--   3. a product gate with two ordered inputs $u,w$, $f_v=f_uf_w$.
--
--   Each gate carries a positive integer **syntactic degree** $d_v$: leaves have degree one, all inputs of a sum gate have its degree, and the degrees of a product gate's inputs sum to its degree. The output polynomial is $f=f_o$, its syntactic degree is $k=d_o$, and the **size** $s$ is the number of gates plus wires. For $S\subseteq[n]$ let $x_S=\prod_{i\in S}x_i$ and let $[x_S]f$ be its coefficient in $f$; the **degree-$k$ multilinear coefficient sum** is
--
--   $$
--   M_k(f)=\sum_{S\subseteq[n],\ |S|=k}[x_S]f .
--   $$
--
--   For example $M_2((x_1+x_2)^2)=2$. This is the quantity estimated in Theorem 1.3, and footnote 2 of the paper fixes that its "monotone circuit" is this definition.
--
--   **Formalization Note** Gates are numbered $0,\dots,\mathrm{size}-1$ so that every input of a gate has a smaller number (a topological numbering, which every DAG admits). A sum gate stores its input wires as a list of (input gate, weight) pairs, so parallel wires are repeated entries; a product gate stores its two ordered inputs. $f_v$ is computed in gate order as an `MvPolynomial (Fin n) ℝ`, and $s$ = gates + one wire per listed sum input + two wires per product gate. Variables are 0-based.
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Definition 4.1, pp.27–28; footnote 2, p.2

import Mathlib

namespace PathCount2k.Supplement

/-! # Normalized monotone circuits and the multilinear coefficient sum `M_k(f)` (Definition 4.1)

Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026),
Definition 4.1, pp.27–28; footnote 2, p.2, fixes that the "monotone circuit" of Theorem 1.3 is this
definition.

**Formalization Note.** Gates are numbered `0, …, size − 1` so that every input of a gate has a
smaller number (a topological numbering of the directed acyclic computation; every DAG has one). A
sum gate lists its input wires as `(input gate, weight)` pairs; the list may repeat a gate
("parallel wires are distinguished"). A product gate has two ordered inputs. -/

/-- A gate over the variables `x₀, …, x_{n−1}` in a circuit with `g` gates: a leaf labelled by a
variable, a sum gate with weighted input wires, or a product gate with two ordered inputs. -/
inductive Gate (n g : ℕ)
  | leaf : Fin n → Gate n g
  | sum : List (Fin g × ℝ) → Gate n g
  | prod : Fin g → Fin g → Gate n g

/-- A circuit with gates `Fin size`, distinguished output gate `out`, and syntactic degrees `deg`
(Definition 4.1: "Each gate is assigned a positive integer syntactic degree `d_v`"). -/
structure Circuit (n : ℕ) where
  /-- the number of gates -/
  size : ℕ
  /-- the gates -/
  gate : Fin size → Gate n size
  /-- the output gate `o` -/
  out : Fin size
  /-- the syntactic degrees `d_v` -/
  deg : Fin size → ℕ

/-- **Normalized monotone arithmetic circuit**, Definition 4.1, pp.27–28: "a directed acyclic
computation with a distinguished output gate `o`. Each gate `v` computes a polynomial `f_v` and is
one of the following: 1. a leaf labeled by a variable `x_i`; 2. a sum gate computing
`f_v = ∑_{e=(v,u)} a_e f_u`, where `a_e ≥ 0`; 3. a product gate with two ordered inputs `u, w`,
computing `f_v = f_u f_w`. … Each gate is assigned a positive integer syntactic degree `d_v`: leaves
have degree one, all inputs of a sum gate have its degree, and the degrees of a product gate's
inputs sum to its degree." Acyclicity is the topological numbering (inputs have smaller numbers). -/
def Circuit.Normalized {n : ℕ} (C : Circuit n) : Prop :=
  (∀ v, 1 ≤ C.deg v) ∧
    ∀ v, match C.gate v with
      | .leaf _ => C.deg v = 1
      | .sum ws => ∀ e ∈ ws, e.1 < v ∧ 0 ≤ e.2 ∧ C.deg e.1 = C.deg v
      | .prod u w => u < v ∧ w < v ∧ C.deg u + C.deg w = C.deg v

/-- **The size** `s`, Definition 4.1: "the size `s` is the number of gates plus wires" (a sum gate
has one wire per listed input, a product gate two). -/
def Circuit.sizeS {n : ℕ} (C : Circuit n) : ℕ :=
  C.size + ∑ v : Fin C.size, match C.gate v with
    | .leaf _ => 0
    | .sum ws => ws.length
    | .prod _ _ => 2

/-- The polynomial of gate `v` from those of earlier gates. -/
noncomputable def Circuit.step {n : ℕ} (C : Circuit n) (F : Fin C.size → MvPolynomial (Fin n) ℝ)
    (v : Fin C.size) : MvPolynomial (Fin n) ℝ :=
  match C.gate v with
  | .leaf i => MvPolynomial.X i
  | .sum ws => (ws.map fun e => MvPolynomial.C e.2 * F e.1).sum
  | .prod u w => F u * F w

/-- The polynomials `f_v` of all gates, computed in gate order (each gate after its inputs). -/
noncomputable def Circuit.polys {n : ℕ} (C : Circuit n) : Fin C.size → MvPolynomial (Fin n) ℝ :=
  (List.finRange C.size).foldl (fun F v => Function.update F v (C.step F v)) 0

/-- The output polynomial `f = f_o`, Definition 4.1. -/
noncomputable def Circuit.poly {n : ℕ} (C : Circuit n) : MvPolynomial (Fin n) ℝ := C.polys C.out

/-- **The degree-`k` multilinear coefficient sum**, Definition 4.1, p.28: "For `S ⊆ [n]`, write
`x_S = ∏_{i∈S} x_i` and let `[x_S]f` denote its coefficient in `f`. … `M_k(f) = ∑_{S ⊆ [n], |S| = k}
[x_S]f`." -/
noncomputable def Mk {n : ℕ} (f : MvPolynomial (Fin n) ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.powersetCard k, f.coeff (∑ i ∈ S, Finsupp.single i 1)

end PathCount2k.Supplement


