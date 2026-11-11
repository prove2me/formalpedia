-- Prove2me | Definitions.Def_PartialHomog_Threshold_Circuit
-- name    : PartialHomog_Threshold_Circuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:26:38.549225+00:00
-- url     : https://prove2.me/theorems/4b1dc793-987d-4cc9-84cb-c3610684b97c
-- title:
--   Arithmetic circuits with product gates of unbounded fan-in (straight-line programs), gate values, predecessors and the product-gate count (Definition A.1)
-- statement:
--   An **arithmetic circuit** over a commutative ring $R$ in the variables $z=(z_0,\dots,z_{N-1})$ with $K$ outputs is a directed acyclic graph whose leaves are labelled by variables or by elements of $R$; every internal gate is a **sum gate** of arbitrary fan-in with an element of $R$ on each incoming edge, or a **product gate** of arbitrary fan-in at least $2$. Every gate $v$ computes a polynomial $\hat v\in R[z]$:
--   $$\hat v=z_a,\qquad \hat v=c,\qquad \hat v=\sum_e c_e\,\hat g_e,\qquad \hat v=\prod_e \hat g_e .$$
--   The inputs of a product gate are unordered and counted with multiplicity. Some gates are output gates; the circuit **computes** $\phi=(\phi_0,\dots,\phi_{K-1})$ when its $s$-th output gate computes exactly the polynomial $\phi_s$. The **cost** of a circuit is its number of product gates, each counted once regardless of its fan-in. A gate $u$ is a **predecessor** of $v$ if there is a directed path from $u$ to $v$. There are no division gates.
--
--   **Formalization Note** The circuit is a straight-line program `Circuit R N K`: gates are numbered `0, …, size-1`, the instruction `gate t : Gate R N t` reads only gates in `Fin t` (earlier gates), so the gate order is a topological order. A sum gate is a list of pairs `(c_e, g_e)`; a product gate is a list `args` of earlier gates with `2 ≤ args.length` (repeats = multiplicity). `value` computes $\hat v$ in `MvPolynomial (Fin N) R`; `prodGates` is the set of product gates, `numProd` its cardinality; `inputs v`/`prodInputs v` list the inputs with multiplicity; `IsPredecessor` is the transitive closure of the input relation; `Computes Φ ϕ` is `∀ s, Φ.value (Φ.out s) = ϕ s`.
-- source:
--   Spiizer, Partial Homogenization and the Structure of Optimal Algebraic Algorithms, STOC 2027 submission (manuscript sha256 33096d05…), p. 13 (PDF 15), Definition A.1; p. 17 (PDF 19), Corollary B.2 (predecessors, topological order)

import Mathlib

/-!
# Arithmetic circuits with product gates of unbounded fan-in (Definition A.1)

Spiizer, *Partial Homogenization and the Structure of Optimal Algebraic Algorithms*,
STOC 2027 submission, §A.1, Definition A.1 (p. 13); Corollary B.2 (p. 17) for predecessors.

A division-free arithmetic circuit over a commutative ring `R` in the variables
`z_0, …, z_{N-1}` with `K` outputs, encoded as a straight-line program: gates are numbered
`0, …, size - 1` in a topological order, and gate `t` only reads gates with smaller numbers.
Gate `t` is
* a leaf labelled by a variable `z_a` or by a constant `c ∈ R`;
* a sum gate `∑_e c_e · g_e` of arbitrary fan-in over earlier gates `g_e`, with a scalar
  `c_e ∈ R` on each incoming edge;
* a product gate `∏_e g_e` of arbitrary fan-in at least two over earlier gates; the inputs form a
  list, so repeated inputs are counted with multiplicity, and their order is immaterial
  because `R[z]` is commutative.

Each output `s` is a designated gate `out s`. Every gate computes a polynomial in `R[z]`, and the
cost of a circuit is its number of product gates, each counted once regardless of its fan-in.
-/

namespace PartialHomog.Threshold

open MvPolynomial

universe u

/-- The instruction at gate number `t` of a straight-line program over `R` in `N` variables.
Its inputs are gate numbers `< t` (elements of `Fin t`). -/
inductive Gate (R : Type u) (N : ℕ) (t : ℕ) : Type u
  /-- a leaf labelled by the variable `z_a` -/
  | var (a : Fin N) : Gate R N t
  /-- a leaf labelled by the constant `c ∈ R` -/
  | const (c : R) : Gate R N t
  /-- a sum gate `∑ c_e · g_e`: one `(c_e, g_e)` per incoming edge, any fan-in -/
  | sum (terms : List (R × Fin t)) : Gate R N t
  /-- a product gate `∏ g_e` of fan-in at least two; inputs listed with multiplicity -/
  | prod (args : List (Fin t)) (h : 2 ≤ args.length) : Gate R N t

namespace Gate

variable {R : Type u} {N t : ℕ}

/-- Whether the gate is a product gate. -/
def isProd : Gate R N t → Bool
  | prod _ _ => true
  | _ => false

/-- The input gates (children) of a gate, with multiplicity: none for a leaf. -/
def children : Gate R N t → List (Fin t)
  | var _ => []
  | const _ => []
  | sum terms => terms.map Prod.snd
  | prod args _ => args

/-- The inputs of a product gate, with multiplicity (empty for every other gate). -/
def prodArgs : Gate R N t → List (Fin t)
  | prod args _ => args
  | _ => []

end Gate

/-- A division-free arithmetic circuit (straight-line program) over `R` in the variables
`z_0, …, z_{N-1}` with `K` output gates. -/
structure Circuit (R : Type u) (N K : ℕ) where
  /-- the number of gates -/
  size : ℕ
  /-- the instruction at each gate; gate `t` reads only gates `< t` -/
  gate : (t : Fin size) → Gate R N t.val
  /-- the output gates -/
  out : Fin K → Fin size

namespace Circuit

variable {R : Type u} [CommRing R] {N K : ℕ}

/-- The polynomial `v̂ ∈ R[z]` computed by gate `v`. -/
noncomputable def value (Φ : Circuit R N K) : Fin Φ.size → MvPolynomial (Fin N) R
  | ⟨t, ht⟩ =>
    match Φ.gate ⟨t, ht⟩ with
    | .var a => X a
    | .const c => C c
    | .sum terms =>
        (terms.map fun e => e.1 • Φ.value ⟨e.2.val, lt_trans e.2.isLt ht⟩).sum
    | .prod args _ =>
        (args.map fun u => Φ.value ⟨u.val, lt_trans u.isLt ht⟩).prod
termination_by t => t.val

/-- Gate `v` is a product gate. -/
def IsProdGate (Φ : Circuit R N K) (v : Fin Φ.size) : Prop :=
  (Φ.gate v).isProd = true

instance (Φ : Circuit R N K) (v : Fin Φ.size) : Decidable (Φ.IsProdGate v) :=
  inferInstanceAs (Decidable (_ = true))

/-- The product gates of `Φ`; listed by increasing gate number they are in a topological order. -/
def prodGates (Φ : Circuit R N K) : Finset (Fin Φ.size) :=
  Finset.univ.filter fun v => Φ.IsProdGate v

/-- The cost of `Φ`: its number of product gates, each counted once regardless of its fan-in. -/
def numProd (Φ : Circuit R N K) : ℕ :=
  Φ.prodGates.card

/-- The inputs of gate `v`, with multiplicity, as gates of `Φ`. -/
def inputs (Φ : Circuit R N K) (v : Fin Φ.size) : List (Fin Φ.size) :=
  (Φ.gate v).children.map fun u => ⟨u.val, lt_trans u.isLt v.isLt⟩

/-- The inputs of product gate `v`, with multiplicity (empty if `v` is not a product gate). -/
def prodInputs (Φ : Circuit R N K) (v : Fin Φ.size) : List (Fin Φ.size) :=
  (Φ.gate v).prodArgs.map fun u => ⟨u.val, lt_trans u.isLt v.isLt⟩

/-- There is an edge from gate `u` to gate `v`: `u` is an input of `v`. -/
def IsInput (Φ : Circuit R N K) (u v : Fin Φ.size) : Prop :=
  u ∈ Φ.inputs v

/-- `u` is a predecessor of `v`: there is a directed path (of length at least one) from `u`
to `v` along input edges (Corollary B.2). -/
def IsPredecessor (Φ : Circuit R N K) (u v : Fin Φ.size) : Prop :=
  Relation.TransGen Φ.IsInput u v

/-- The polynomials computed by the output gates. -/
noncomputable def outputs (Φ : Circuit R N K) : Fin K → MvPolynomial (Fin N) R :=
  fun s => Φ.value (Φ.out s)

/-- `Φ` computes `ϕ = (ϕ_0, …, ϕ_{K-1})`: its output gates compute exactly these polynomials
(equality in `R[z]`). -/
def Computes (Φ : Circuit R N K) (ϕ : Fin K → MvPolynomial (Fin N) R) : Prop :=
  ∀ s, Φ.value (Φ.out s) = ϕ s

end Circuit

end PartialHomog.Threshold


