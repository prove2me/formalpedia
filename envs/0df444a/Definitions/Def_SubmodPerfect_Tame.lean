-- Prove2me | Definitions.Def_SubmodPerfect_Tame
-- name    : SubmodPerfect_Tame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:50.858648+00:00
-- url     : https://prove2.me/theorems/4866d69e-26de-4ac2-98e6-d8a0690e8c00
-- title:
--   $(k,c,d,m)$-tame graph classes on a unit-cost RAM
-- statement:
--   A class $\mathcal G$ of finite graphs is **$(k,c,d,m)$-tame** if
--
--   1. every $G\in\mathcal G$ has a $(w,k,c,d)$-even set separator for every uniform weight function $w$; and
--   2. one fixed program of a unit-cost random-access machine and one constant $C$ construct such a separator: on input $n$, the adjacency matrix of $G$ (vertex set $\{0,\dots,n-1\}$), the weights $w(0),\dots,w(n-1)$ and the threshold $c$, the program halts within $C\,(n+1)^m$ steps, and its output cells describe a $k$-tuple of vertex sets that is a $(w,k,c,d)$-even set separator of $G$.
--
--   The machine is the published unit-cost RAM `WilliamsonShmoys.planarRAMRun` (natural and real registers, indirect addressing, addition, subtraction and comparison, one unit per instruction). The input layout puts $n$ in natural cell $0$, the adjacency bit of $(u,v)$ in natural cell $2+nu+v$, $w(v)$ in real cell $v$ and $c$ in real cell $n$; vertex $v$ is in the $i$-th output set ($0$-based) when natural cell $2+n^2+v$ holds $i+1$. The module also defines $1+\delta+\dots+\delta^{\delta+3}$.
--
--   This is the paper's "(k, c, d, m)-tame": separators for every uniform weight, constructible in $O(|V(G)|^m)$ time.
--
--   **Formalization Note** The RAM has no real constants other than $0$, so $c$ is part of the input. Tameness is stated for a class because an $O(\cdot)$ bound has content only uniformly over graphs.
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, §1, p.3 ((k, c, d, m)-tame); Theorems 1.3 and 1.5, pp.3–4 (1 + δ + … + δ^{δ+3})

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_SubmodPerfect_Graphs

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace SubmodPerfect

/-! # Running time and `(k, c, d, m)`-tame graph classes

Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*,
arXiv:2110.00108v2, §1, p.3: "A graph G is called (k, c, d, m)-tame if G has a
(w, k, c, d)-even set separator for every uniform weight function w, and such a separator can be
constructed in O(|V(G)|^m) time."

**Formalization Note.**
1. *Machine.* Running time is counted on the published unit-cost RAM
   `WilliamsonShmoys.planarRAMRun` (natural and real cells, indirect addressing, `+`, `−`, `≤`,
   one unit per instruction). Its instruction set has no real constants besides `0`, so the
   threshold `c` is part of the input (a program could not otherwise compare a weight with an
   arbitrary real `c`).
2. *Input layout* (`sepInput`): natural cell `0` holds `n`, natural cell `2 + n·u + v` holds `1`
   if `uv` is an edge and `0` otherwise (`u, v < n`), real cell `v` holds `w(v)` for `v < n`, and
   real cell `n` holds `c`; every other cell is `0`.
3. *Output* (`sepOutput`): vertex `v` belongs to the `i`-th set (`0`-based) iff natural cell
   `2 + n² + v` holds `i + 1`.
4. *Halting*: the run halts at step `t` when the instruction at the program counter is `halt`
   (the step function then stutters).
5. *O(n^m)*: at most `C · (n + 1)^m` steps, with one program and one constant `C` for every graph
   of the class; tameness of a single graph is read as tameness of the class the theorem is
   about, since `O(|V(G)|^m)` has no meaning for one graph. -/

/-- The RAM input encoding `n`, the adjacency matrix of `G`, the weights `w` and the threshold
`c`. -/
def sepInput (n : ℕ) (G : SimpleGraph (Fin n)) (w : Fin n → ℝ) (c : ℝ) :
    WilliamsonShmoys.PlanarRAMState where
  pc := 0
  natMem := fun a =>
    if a = 0 then n else
      if h : 2 ≤ a ∧ a < 2 + n * n then
        if G.Adj ⟨(a - 2) / n, by
              have h1 : a - 2 < n * n := by omega
              exact Nat.div_lt_of_lt_mul h1⟩
            ⟨(a - 2) % n, Nat.mod_lt _ (by
              rcases Nat.eq_zero_or_pos n with h0 | h0
              · subst h0; omega
              · exact h0)⟩ then 1 else 0
      else 0
  realMem := fun a => if h : a < n then w ⟨a, h⟩ else if a = n then c else 0

/-- The `k`-tuple of vertex sets decoded from a RAM state: `v` is in set `i` iff natural cell
`2 + n² + v` holds `i + 1`. -/
def sepOutput (n k : ℕ) (s : WilliamsonShmoys.PlanarRAMState) : Fin k → Finset (Fin n) :=
  fun i => Finset.univ.filter (fun v => s.natMem (2 + n * n + v.val) = i.val + 1)

/-- The program has halted at state `s`. -/
def RAMHalted (program : List WilliamsonShmoys.PlanarRAMInstruction)
    (s : WilliamsonShmoys.PlanarRAMState) : Prop :=
  program[s.pc]? = some WilliamsonShmoys.PlanarRAMInstruction.halt

/-- The class `𝒢` of finite graphs (on `Fin n`, all `n`) is `(k, c, d, m)`-tame (p.3): every
graph of the class has a `(w, k, c, d)`-even set separator for every uniform weight function
`w`, and one fixed RAM program constructs such a separator from `(n, G, w, c)` within
`C · (n + 1)^m` steps, for one constant `C`. A uniform weight function is `uniformWeight X` for
a nonempty `X`. -/
def IsTameClass (𝒢 : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) (k : ℕ) (c : ℝ) (d m : ℕ) : Prop :=
  (∀ n (G : SimpleGraph (Fin n)), 𝒢 n G → ∀ X : Finset (Fin n), X.Nonempty →
    ∃ L : Fin k → Finset (Fin n), IsEvenSetSeparator G (uniformWeight X) k c d L) ∧
  ∃ (program : List WilliamsonShmoys.PlanarRAMInstruction) (C : ℕ),
    ∀ n (G : SimpleGraph (Fin n)), 𝒢 n G → ∀ X : Finset (Fin n), X.Nonempty →
      ∃ t ≤ C * (n + 1) ^ m,
        RAMHalted program
            (WilliamsonShmoys.planarRAMRun program (sepInput n G (uniformWeight X) c) t) ∧
          IsEvenSetSeparator G (uniformWeight X) k c d
            (sepOutput n k
              (WilliamsonShmoys.planarRAMRun program (sepInput n G (uniformWeight X) c) t))

/-- `1 + δ + … + δ^{δ+3}` (Theorems 1.3 and 1.5, pp.3–4). -/
def tameBound (δ : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (δ + 4), δ ^ i

end SubmodPerfect


