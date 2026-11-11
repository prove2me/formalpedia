-- Prove2me | Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Circuit
-- name    : SymmetricDepthHierarchy_ConstantDepth_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:01.677011+00:00
-- url     : https://prove2.me/theorems/b6334160-630f-4477-bfe8-9b769ac021dc
-- title:
--   Algebraic circuits over $X_n$, size, depth, matrix symmetry, orbit size, rigid and reduced circuits
-- statement:
--   We work over a field $K$ of characteristic zero and the variables $X_n=\{x_{i,j}: i,j\in[n]\}$.
--
--   An **algebraic circuit** is a finite directed acyclic multigraph whose input gates are labelled by variables or field constants and whose internal gates are labelled by $+$ or $\times$. Input gates with the same label are identified, fan-in is unbounded and parallel wires are allowed; a gate $g$ receives $m(g,h)\in\mathbb N$ wires from $h$. There is a unique output gate and every gate lies on a path to it. The gate $g$ computes $x_{i,j}$ or the constant $c$ if it is an input gate, and otherwise
--   $$\sum_h m(g,h)\,P_h \qquad\text{or}\qquad \prod_h P_h^{\,m(g,h)}$$
--   (empty sums are $0$, empty products $1$); the circuit **computes** $p$ if its output gate computes the polynomial $p$.
--
--   1. The **size** is the number of gates plus the number of wires counted with multiplicity.
--   2. The **depth** is the maximum number of wires on a path from an input gate to the output gate.
--   3. The **height** of a gate is the maximal number of wires on a path from it down to a gate without children.
--
--   The group $\Gamma_n=\mathrm{Sym}_n\times\mathrm{Sym}_n$ acts on $X_n$ by $(\sigma,\tau)x_{i,j}=x_{\sigma(i),\tau(j)}$, fixing constants. A permutation of the gates **extends** $\gamma\in\Gamma_n$ if it preserves the multiplicities of all wires and internal operation labels and maps every input gate labelled $\lambda$ to the input gate labelled $\gamma(\lambda)$. The circuit is **matrix-symmetric** if every $\gamma\in\Gamma_n$ extends to such an automorphism (Definition 2.1). With $\mathrm{Aut}_\Gamma(C)$ the group of *all* automorphisms extending some element of $\Gamma_n$, the **orbit size** is
--   $$\operatorname{maxOrb}(C)=\max_{v}\bigl|\{\sigma(v):\sigma\in\mathrm{Aut}_\Gamma(C)\}\bigr|.$$
--   A matrix-symmetric circuit is **rigid** if every element of $\Gamma_n$ extends to a unique automorphism, and **reduced** if no two distinct input gates have the same label and no two distinct internal gates have the same label and the same multiset of children (Definition 2.2).
--
--   These notions are the circuit model of every statement of the mission.
--
--   **Formalization Note.** A circuit on a finite gate type $V$ is the data of labels, wire multiplicities $m(g,h)$ and an output gate; `WellFormed` states that input gates have no incoming wires, the wire relation has no cycle, input labels are distinct and every gate reaches the output. $[n]$ is `Fin n`. The computed polynomial, depth and height are obtained by running the defining recursion $|V|$ times, which is exact on acyclic circuits. A circuit without input gates has depth $0$ (empty maximum). The height is measured to gates without children; it equals the source's height (Appendix A) whenever every internal gate has a child.
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), §2.1–§2.3, pp. 7–8 (PDF pp. 10–11), Definitions 2.1 and 2.2; Appendix A, p. 27 (PDF p. 30)

import Mathlib

open scoped Classical

noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth

/-!
# Algebraic circuits over the matrix variables, matrix symmetry and orbit size

Dawar, Dwivedi, Pago, Seppelt, *Depth Hierarchies for Symmetric Algebraic Circuits*,
STOC 2027 submission #1521, §2.1–§2.3 (printed pp. 7–8, PDF pp. 10–11), Definitions 2.1 and 2.2.

* The variables are `X_n = {x_{i,j} : i, j ∈ [n]}`, encoded as `Fin n × Fin n`
  (`Fin n` relabels `[n] = {1,…,n}`); polynomials live in `MvPolynomial (Fin n × Fin n) K`.
* A circuit on a finite gate type `V` is given by its labels, its wire multiplicities
  (`mult g h` is the number of parallel wires from `h` into `g`) and its output gate.
  `WellFormed` collects the conditions of §2.1: input gates have no incoming wires, the wire
  relation is acyclic, distinct input gates carry distinct labels ("input gates with the same
  label are identified"), and every gate lies on a path to the output.
* Recursively defined quantities (computed polynomial, depth, height) are computed by
  `Fintype.card V` rounds of the defining recursion; in an acyclic circuit every downward path
  has fewer than `Fintype.card V` wires, so this is the exact recursive value.
-/

/-- The two operations of internal gates. -/
inductive Op
  | add
  | mul
  deriving DecidableEq

/-- Gate labels: a variable `x_{i,j}`, a field constant, or an operation. -/
inductive GateLabel (K : Type) (n : ℕ)
  | var (i j : Fin n)
  | const (c : K)
  | op (o : Op)

/-- A circuit with gate set `V` over the variables `X_n`: `label g` is the label of gate `g`,
`mult g h` the multiplicity of the wire from `h` into `g` (so `h` is a child of `g` iff
`0 < mult g h`), and `out` is the output gate. -/
structure Circuit (K : Type) (n : ℕ) (V : Type) where
  label : V → GateLabel K n
  mult : V → V → ℕ
  out : V

namespace Circuit

variable {K : Type} [Field K] {n : ℕ} {V : Type} [Fintype V]

/-- `g` is an input gate (labelled by a variable or a constant). -/
def IsInput (C : Circuit K n V) (g : V) : Prop :=
  match C.label g with
  | .op _ => False
  | _ => True

/-- The wire relation: `Wire C h g` iff there is at least one wire from `h` into `g`. -/
def Wire (C : Circuit K n V) (h g : V) : Prop := 0 < C.mult g h

/-- The structural conditions of §2.1 on a finite directed acyclic multigraph circuit. -/
structure WellFormed (C : Circuit K n V) : Prop where
  /-- input gates have no incoming wires -/
  input_no_wire : ∀ g h, C.IsInput g → C.mult g h = 0
  /-- the circuit is acyclic -/
  acyclic : ∀ g, ¬ Relation.TransGen C.Wire g g
  /-- input gates with the same label are identified -/
  input_inj : ∀ g g', C.IsInput g → C.IsInput g' → C.label g = C.label g' → g = g'
  /-- every gate lies on a path to the output gate -/
  reach_out : ∀ g, Relation.ReflTransGen C.Wire g C.out

/-- One round of the evaluation recursion: input gates evaluate to their variable or constant,
a `+` gate to `∑_h mult(g,h) · val h`, a `×` gate to `∏_h (val h)^{mult(g,h)}` (wires counted
with multiplicity; the empty sum is `0` and the empty product is `1`). -/
def evalStep (C : Circuit K n V) (val : V → MvPolynomial (Fin n × Fin n) K) (g : V) :
    MvPolynomial (Fin n × Fin n) K :=
  match C.label g with
  | .var i j => MvPolynomial.X (i, j)
  | .const c => MvPolynomial.C c
  | .op .add => ∑ h, (C.mult g h : MvPolynomial (Fin n × Fin n) K) * val h
  | .op .mul => ∏ h, val h ^ C.mult g h

/-- `k` rounds of the evaluation recursion. -/
def valueAux (C : Circuit K n V) : ℕ → V → MvPolynomial (Fin n × Fin n) K
  | 0 => C.evalStep (fun _ => 0)
  | k + 1 => C.evalStep (C.valueAux k)

/-- The polynomial computed at gate `g` (exact for well-formed, i.e. acyclic, circuits). -/
def value (C : Circuit K n V) (g : V) : MvPolynomial (Fin n × Fin n) K :=
  C.valueAux (Fintype.card V) g

/-- `C` computes `p`: the output gate computes the polynomial `p` (equality of polynomials). -/
def Computes (C : Circuit K n V) (p : MvPolynomial (Fin n × Fin n) K) : Prop :=
  C.value C.out = p

/-- The size: the number of gates plus the number of wires, counted with multiplicity. -/
def size (C : Circuit K n V) : ℕ := Fintype.card V + ∑ g, ∑ h, C.mult g h

/-- `k` rounds of the recursion for the maximal number of wires on a path from an input gate
up to `g` (`⊥` if no input gate lies below `g`). -/
def inputDepthAux (C : Circuit K n V) : ℕ → V → WithBot ℕ
  | 0 => fun g => if C.IsInput g then 0 else ⊥
  | k + 1 => fun g => if C.IsInput g then 0 else
      Finset.univ.sup fun h => if C.Wire h g then C.inputDepthAux k h + 1 else ⊥

/-- The depth: the maximum number of wires on an input-to-output path
(`0` if there is no such path, i.e. the maximum of the empty set is read as `0`). -/
def depth (C : Circuit K n V) : ℕ :=
  (C.inputDepthAux (Fintype.card V) C.out).unbotD 0

/-- `k` rounds of the recursion for the length of a longest downward path from `g`. -/
def heightAux (C : Circuit K n V) : ℕ → V → ℕ
  | 0 => fun _ => 0
  | k + 1 => fun g => Finset.univ.sup fun h => if C.Wire h g then C.heightAux k h + 1 else 0

/-- The height of a gate: the maximal number of wires on a path from it down to a gate without
children. If every internal gate has a child (so every maximal downward path ends at an input gate)
this is the source's "maximal number of wires on a path from it to an input gate" (Appendix A). -/
def height (C : Circuit K n V) (g : V) : ℕ := C.heightAux (Fintype.card V) g

/-! ### Matrix symmetry -/

/-- The group `Γ_n = Sym_n × Sym_n` (row and column permutations). -/
abbrev Gamma (n : ℕ) := Equiv.Perm (Fin n) × Equiv.Perm (Fin n)

/-- The action of `Γ_n` on labels: `(σ, τ) x_{i,j} = x_{σ(i), τ(j)}`; constants and
operations are fixed. -/
def actLabel (γ : Gamma n) : GateLabel K n → GateLabel K n
  | .var i j => .var (γ.1 i) (γ.2 j)
  | .const c => .const c
  | .op o => .op o

/-- `σ` is a circuit automorphism extending `γ ∈ Γ_n`: it preserves the multiplicities (and
directions) of all wires, preserves the operation labels of internal gates, and
`λ(σ v) = γ(λ v)` for every input gate `v`. -/
def IsExtension (C : Circuit K n V) (γ : Gamma n) (σ : Equiv.Perm V) : Prop :=
  (∀ g h, C.mult (σ g) (σ h) = C.mult g h) ∧ ∀ g, C.label (σ g) = actLabel γ (C.label g)

/-- Definition 2.1: `C` is matrix-symmetric if every `γ ∈ Γ_n` extends to a circuit
automorphism. -/
def MatrixSymmetric (C : Circuit K n V) : Prop := ∀ γ : Gamma n, ∃ σ, C.IsExtension γ σ

/-- The orbit of `g` under the group `Aut_Γ(C)` of *all* automorphisms extending some element
of `Γ_n`. -/
def orbit (C : Circuit K n V) (g : V) : Finset V :=
  Finset.univ.filter fun g' => ∃ (γ : Gamma n) (σ : Equiv.Perm V), C.IsExtension γ σ ∧ σ g = g'

/-- The orbit size `maxOrb(C) = max_v |{σ(v) : σ ∈ Aut_Γ(C)}|`. -/
def maxOrb (C : Circuit K n V) : ℕ := Finset.univ.sup fun g => (C.orbit g).card

/-- Definition 2.2: `C` is rigid if every element of `Γ_n` extends to a unique automorphism. -/
def Rigid (C : Circuit K n V) : Prop := ∀ γ : Gamma n, ∃! σ, C.IsExtension γ σ

/-- Definition 2.2: `C` is reduced if no two distinct input gates have the same label and no two
distinct internal gates have the same label and the same multiset of children. -/
def Reduced (C : Circuit K n V) : Prop :=
  (∀ g g', C.IsInput g → C.IsInput g' → C.label g = C.label g' → g = g') ∧
  (∀ g g', ¬ C.IsInput g → ¬ C.IsInput g' → C.label g = C.label g' →
    (∀ h, C.mult g h = C.mult g' h) → g = g')

end Circuit

end SymmetricDepthHierarchy.ConstantDepth


