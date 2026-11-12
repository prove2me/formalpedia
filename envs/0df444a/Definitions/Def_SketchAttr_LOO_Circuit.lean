-- Prove2me | Definitions.Def_SketchAttr_LOO_Circuit
-- name    : SketchAttr_LOO_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:25:32.757456+00:00
-- url     : https://prove2.me/theorems/27aaf418-2f93-47d3-abc6-fab7c6221569
-- title:
--   Definition 3.1 — arithmetic circuits and their memory encoding
-- statement:
--   An **arithmetic circuit** with $n$ complex inputs and $p$ outputs is a finite directed acyclic graph. Its source gates carry input indices or complex constants; all other gates add or multiply a nonempty list of predecessor values. Input indices can be reused, fan-in and fan-out are unbounded, and every sink is an output. Output indices label distinct vertices. The circuit size is
--   $$\operatorname{size}(c)=\max\{n,p,\#\text{edges}\}.$$
--   Evaluation processes a topological ordering and works over any commutative complex algebra. A scalar circuit is real on the cube when its imaginary part vanishes at every real input in $[0,1]^n$; its constants need not be real.
--
--   The natural memory encoding starts with $n,p,V$, followed by each vertex's tag, payload, predecessor count and predecessor list, then the output indices. Tags $0,1,2,3$ mean input, constant, sum and product. A separate complex stream puts each constant at its vertex index and zero elsewhere. This provides a concrete input for the call implementation, rather than treating circuit evaluation as a primitive. For the goal's nonempty scalar inputs, the combined encoding has at most $13\operatorname{size}(c)$ cells.
-- source:
--   Liaw, Mehta, Velegkas, Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2), p. 9, Definition 3.1; Section 3.2; canonical PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/9.pdf

import Mathlib

namespace SketchAttr.LOO

/-- A topologically ordered vertex; predecessor lists retain repeated edges. -/
inductive Gate (n : ℕ) where
  | input (i : Fin n)
  | constant (z : ℂ)
  | add (parents : List ℕ)
  | mul (parents : List ℕ)

def Gate.parents {n : ℕ} : Gate n → List ℕ
  | .input _ | .constant _ => []
  | .add ps | .mul ps => ps

/-- Definition 3.1, including all sinks being labelled outputs. -/
structure Circuit (n p : ℕ) where
  gates : List (Gate n)
  output : Fin p → Fin gates.length
  output_injective : Function.Injective output
  earlier : ∀ (j : Fin gates.length) (a : ℕ), a ∈ (gates.get j).parents → a < j.val
  nonempty_fanin : ∀ j : Fin gates.length,
    match gates.get j with
    | .add ps | .mul ps => ps ≠ []
    | _ => True
  sinks_output : ∀ j : Fin gates.length,
    (¬ ∃ k : Fin gates.length, j.val ∈ (gates.get k).parents) → ∃ i, output i = j

def Circuit.size {n p : ℕ} (c : Circuit n p) : ℕ :=
  max (max n p) ((c.gates.map fun g => g.parents.length).sum)

noncomputable def Gate.eval {n : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R]
    (w : Fin n → R) (vs : List R) : Gate n → R
  | .input i => w i
  | .constant z => algebraMap ℂ R z
  | .add ps => (ps.map fun j => vs[j]?.getD 0).sum
  | .mul ps => (ps.map fun j => vs[j]?.getD 0).prod

noncomputable def Circuit.eval {n p : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R]
    (c : Circuit n p) (w : Fin n → R) : Fin p → R :=
  let vs := c.gates.foldl (fun vs g => vs ++ [g.eval w vs]) []
  fun i => vs[(c.output i).val]?.getD 0

noncomputable def Circuit.scalar {n : ℕ} (c : Circuit n 1) (w : Fin n → ℂ) : ℂ :=
  c.eval w 0

/-- The hypothesis is real-valuedness on the cube, not a restriction on literals. -/
def Circuit.RealOnCube {n : ℕ} (c : Circuit n 1) : Prop :=
  ∀ w : Fin n → ℝ, (∀ i, 0 ≤ w i ∧ w i ≤ 1) → (c.scalar fun i => (w i : ℂ)).im = 0

/-- Natural stream: n,p,vertex count; then gate records tag,payload,length,parents;
then the p output indices. Tags 0=input,1=constant,2=sum,3=product.
Constants occupy the complex stream at their vertex indices. -/
def Gate.encode {n : ℕ} : Gate n → List ℕ
  | .input i => [0, i.val, 0]
  | .constant _ => [1, 0, 0]
  | .add ps => [2, 0, ps.length] ++ ps
  | .mul ps => [3, 0, ps.length] ++ ps

def Circuit.natEncoding {n p : ℕ} (c : Circuit n p) : List ℕ :=
  [n, p, c.gates.length] ++ (c.gates.flatMap Gate.encode) ++
    (List.ofFn fun i => (c.output i).val)

def Circuit.complexEncoding {n p : ℕ} (c : Circuit n p) : List ℂ :=
  c.gates.map fun g => match g with | .constant z => z | _ => 0

end SketchAttr.LOO


