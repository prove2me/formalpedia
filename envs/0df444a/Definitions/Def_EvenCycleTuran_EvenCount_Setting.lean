-- Prove2me | Definitions.Def_EvenCycleTuran_EvenCount_Setting
-- name    : EvenCycleTuran_EvenCount_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:53.152016+00:00
-- url     : https://prove2.me/theorems/052b9921-f335-470e-b412-413ce6dbca88
-- title:
--   p. 9 — the blow-up of C_{2l}, codegrees on unordered pairs, and distinct vertex pairs
-- statement:
--   The shared setting supplies cycle freeness, the generalized Turán number, the complete bipartite graph, and the codegree $f(a,b)$. This file defines the **blow-up of $C_{2l}$** on $n$ vertices. The vertices $0,\dots,l-1$ are kept vertices $x_0,\dots,x_{l-1}$; every other vertex $v\ge l$ belongs to class $i=(v-l)\bmod l$ and is joined exactly to $x_i$ and $x_{(i+1)\bmod l}$. Thus the $n-l$ copies are split as evenly as possible into $l$ classes.
--
--   It also defines $f(\{a,b\})=f(a,b)$ on unordered vertex pairs and the set of distinct unordered pairs over which the proof sums codegrees.
--
--   **Formalization Note** These definitions import `EvenCycleTuran.C4Count.Setting`; they do not redefine its objects. The blow-up represents the paper's construction when $l\ge4$ and $n\ge2l$, the parameter range of its milestone. Sums over $a\ne b$ use `Sym2` off the diagonal.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 9, proof of Theorem 10 (the blow-up of C_{2l} and f(a, b))

import Mathlib
import Definitions.Def_EvenCycleTuran_C4Count_Setting

namespace EvenCycleTuran.EvenCount
open Finset SimpleGraph

/-- The class of a blown-up vertex `v ≥ l` of `blowUp n l`: `(v − l) mod l`. -/
def blowClass (l : ℕ) (v : ℕ) : ℕ := (v - l) % l

/-- The blow-up of C_{2l} on `Fin n` (proof of Theorem 10, p. 9). The vertices `v < l` are the
kept vertices `x₀, …, x_{l−1}` of `C_{2l}`; a vertex `v ≥ l` is a copy of the vertex of `C_{2l}`
between `x_i` and `x_{(i+1) mod l}`, where `i = (v − l) mod l`, and is adjacent to exactly these two
kept vertices. Kept vertices are pairwise non-adjacent, and so are copies. -/
def blowUp (n l : ℕ) : SimpleGraph (Fin n) where
  Adj v w :=
    ((l ≤ (v : ℕ) ∧ (w : ℕ) < l ∧
        ((w : ℕ) = blowClass l v ∨ (w : ℕ) = (blowClass l v + 1) % l)) ∨
      (l ≤ (w : ℕ) ∧ (v : ℕ) < l ∧
        ((v : ℕ) = blowClass l w ∨ (v : ℕ) = (blowClass l w + 1) % l)))
  symm := ⟨fun v w h => by tauto⟩
  loopless := ⟨fun v h => by omega⟩

instance (n l : ℕ) : DecidableRel (blowUp n l).Adj :=
  fun v w => by unfold blowUp; infer_instance

/-- The `i`-th class of blown-up copies in `blowUp n l`: the vertices `v ≥ l` with
`(v − l) mod l = i`. -/
def blowClassSet (n l i : ℕ) : Finset (Fin n) :=
  univ.filter (fun v : Fin n => l ≤ (v : ℕ) ∧ blowClass l v = i)

/-- f on an unordered pair `{a, b}` (f is symmetric). -/
def codegPair {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : Sym2 V) : ℕ :=
  Sym2.lift ⟨fun a b => EvenCycleTuran.C4Count.codeg G a b, fun a b => by simp only [EvenCycleTuran.C4Count.codeg, Finset.inter_comm]⟩ p

/-- The unordered pairs `{a, b}` of distinct vertices. -/
def offDiagPairs (V : Type*) [Fintype V] [DecidableEq V] : Finset (Sym2 V) :=
  univ.filter (fun p : Sym2 V => ¬ p.IsDiag)

end EvenCycleTuran.EvenCount


