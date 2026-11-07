-- Prove2me | Definitions.Def_SymCircMM_Circuit
-- name    : SymCircMM_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:29:38.176906+00:00
-- url     : https://prove2.me/theorems/dc9d40be-48ff-4b49-8c8b-564b0024ed46
-- title:
--   Algebraic circuits over $F$: gates, edge multiplicities, computed polynomials, size and automorphisms
-- statement:
--   Let $X$ be a finite set of variables and $F$ a field. An **algebraic circuit** $C$ over $F$ with variables $X$ is a finite directed acyclic multigraph whose gates are labelled as follows:
--
--   1. every source (a gate with no children) is an **input gate**, labelled by a variable $x\in X$ or by a constant $c\in F$;
--   2. every other gate is labelled $+$ or $\times$ and has fan-in at least one.
--
--   Each gate $g$ computes a polynomial $\hat g\in F[X]$: an input gate labelled $x$ computes $x$, one labelled $c$ computes $c$, a $+$-gate computes the sum of its children and a $\times$-gate their product, every child counted with the multiplicity of its edge. The **size** of $C$ is its number of edges counted with multiplicity, i.e. the total fan-in
--
--   $$\mathrm{size}(C)=\sum_{g}\sum_{c}\mathrm{wire}(g,c).$$
--
--   For a map $\pi$ of the variables, a bijection $\varphi$ of the gates **extends** $\pi$ when it preserves every edge multiplicity, sends each input gate labelled $x$ to an input gate labelled $\pi(x)$, fixes the labels of constant gates, and maps $+$-gates to $+$-gates and $\times$-gates to $\times$-gates; this is the automorphism $\hat\sigma$ of Definition 2.2.
--
--   This is the computational model of the whole mission: every lower bound counts edges of such circuits, with unbounded fan-in.
--
--   **Formalization Note** The gates form a type $\gamma$ (finite where the size or the values are used); $\mathrm{wire}(g,c)\in\mathbb N$ is the number of edges making $c$ a child of $g$. Acyclicity is the existence of a rank function strictly decreasing along edges. Output gates are not part of the structure: they are designated by the statements that use the circuit. Several input gates may carry the same label.
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Definition 2.1, p.3 (PDF p.4); Definition 2.2, p.3 (PDF p.4)

import Mathlib

set_option autoImplicit false

namespace SymCircMM

/-- The label of a gate of an algebraic circuit (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for
Matrix Multiplication*, manuscript (sha256 999a7eba…), Definition 2.1, p.3 (PDF p.4)): an input gate
is labelled by a variable `x ∈ X` or by a constant `c ∈ F`; an internal gate is labelled `+` or `×`. -/
inductive GateLabel (X F : Type) where
  /-- an input gate labelled by the variable `x` -/
  | input (x : X)
  /-- an input gate labelled by the constant `c` -/
  | const (c : F)
  /-- an addition gate -/
  | add
  /-- a multiplication gate -/
  | mul

namespace GateLabel

variable {X F : Type}

/-- The action of a map `π : X → X` of the variables on labels: `input x ↦ input (π x)`, while
constants, `+` and `×` are fixed (Definition 2.2, p.3 (PDF p.4): `g_x ↦ g_{σ·x}`, `g_c ↦ g_c`). -/
def map (π : X → X) : GateLabel X F → GateLabel X F
  | input x => input (π x)
  | const c => const c
  | add => add
  | mul => mul

/-- Whether the label is that of an input gate (a variable or a constant). -/
def isLeaf : GateLabel X F → Bool
  | input _ => true
  | const _ => true
  | add => false
  | mul => false

/-- Whether the label is `×`. -/
def isMul : GateLabel X F → Bool
  | mul => true
  | _ => false

end GateLabel

/-- An **algebraic circuit** over the field `F` with variables `X` and gate set `γ` (Dahan, Dawar, Kush,
Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), Definition 2.1,
p.3 (PDF p.4)): a directed acyclic multigraph whose sources are the input gates, labelled by an element
of `X ∪ F`, and whose internal gates are labelled `+` or `×` and have fan-in at least one.

**Formalization Note.** `wire g c : ℕ` is the multiplicity of the edge making `c` a child (an input) of
`g`. Acyclicity is the existence of a rank function strictly decreasing along every edge (for a finite
gate set this is the same as having no directed cycle). Input gates (variables and constants) have no
children, and `+`/`×` gates have at least one child, so the sources are exactly the input gates.
Several input gates may carry the same label. Output gates are not part of the structure: a circuit
computes a family of polynomials when some gates compute them (see `Circuit.ComputesMM`). -/
structure Circuit (F X γ : Type) [Field F] where
  /-- the label of each gate -/
  label : γ → GateLabel X F
  /-- `wire g c` is the number of edges from the child `c` into the gate `g` -/
  wire : γ → γ → ℕ
  /-- the multigraph is acyclic -/
  acyclic : ∃ rk : γ → ℕ, ∀ g c, wire g c ≠ 0 → rk c < rk g
  /-- input gates have no children -/
  leaf_no_child : ∀ g, (label g).isLeaf = true → ∀ c, wire g c = 0
  /-- `+` and `×` gates have fan-in at least one -/
  internal_has_child : ∀ g, (label g).isLeaf = false → ∃ c, wire g c ≠ 0

namespace Circuit

variable {F X γ : Type} [Field F]

/-- The child relation of a circuit is well founded (from the rank function). -/
theorem wf (C : Circuit F X γ) : WellFounded (fun c g => C.wire g c ≠ 0) := by
  obtain ⟨rk, h⟩ := C.acyclic
  exact Subrelation.wf (fun {c g} hcg => h g c hcg) (InvImage.wf rk wellFounded_lt)

/-- The polynomial `ĝ ∈ F[X]` computed by each gate (Definition 2.1, p.3 (PDF p.4)): an input gate
labelled `x` computes `x`, one labelled `c` computes the constant `c`, a `+`-gate computes the sum of
its children and a `×`-gate their product, each child counted with the multiplicity of its edge. -/
noncomputable def val [Fintype γ] (C : Circuit F X γ) : γ → MvPolynomial X F :=
  C.wf.fix fun g IH =>
    match C.label g with
    | .input x => MvPolynomial.X x
    | .const c => MvPolynomial.C c
    | .add => ∑ c, if h : C.wire g c = 0 then 0 else (C.wire g c : MvPolynomial X F) * IH c h
    | .mul => ∏ c, if h : C.wire g c = 0 then 1 else IH c h ^ C.wire g c

/-- The defining recursion of `val`, with sums and products over all gates (an absent edge has
multiplicity `0`). -/
theorem val_eq [Fintype γ] (C : Circuit F X γ) (g : γ) :
    C.val g = match C.label g with
      | .input x => MvPolynomial.X x
      | .const c => MvPolynomial.C c
      | .add => ∑ c, (C.wire g c : MvPolynomial X F) * C.val c
      | .mul => ∏ c, C.val c ^ C.wire g c := by
  rw [val, WellFounded.fix_eq]
  rcases C.label g with x | c | _ | _
  · rfl
  · rfl
  · refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with h
    · simp [h]
    · rfl
  · refine Finset.prod_congr rfl fun c _ => ?_
    split_ifs with h
    · simp [h]
    · rfl

/-- The **size** of a circuit: its number of edges counted with multiplicity, i.e. the total fan-in
(Definition 2.1, p.3 (PDF p.4)). -/
def size [Fintype γ] (C : Circuit F X γ) : ℕ := ∑ g, ∑ c, C.wire g c

/-- `φ` is an automorphism of the labelled multi-DAG `C` that extends the map `π` of the variables
(Definition 2.2, p.3 (PDF p.4)): `φ` preserves every edge multiplicity, sends an input gate labelled
`x` to one labelled `π x`, fixes the labels of constant gates and keeps `+`-gates and `×`-gates. -/
def Extends (C : Circuit F X γ) (π : X → X) (φ : γ ≃ γ) : Prop :=
  (∀ g c, C.wire (φ g) (φ c) = C.wire g c) ∧ ∀ g, C.label (φ g) = (C.label g).map π

end Circuit

end SymCircMM


