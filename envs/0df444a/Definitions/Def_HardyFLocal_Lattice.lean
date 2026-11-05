-- Prove2me | Definitions.Def_HardyFLocal_Lattice
-- name    : HardyFLocal_Lattice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:39:13.338259+00:00
-- url     : https://prove2.me/theorems/1c344ab8-dfa0-486f-b2c6-fbbb600771e8
-- title:
--   The qubit lattice and the lattice probability $\mathrm{prob}(Y_V\mid F_V)$
-- statement:
--   Let $m,n$ be natural numbers. There are $m$ right moving qubits $u$ and $n$ left moving qubits $v$, and each right mover crosses each left mover at the **vertex** $x=(u,v)$, the elementary region $R_{uv}$. A **label** at a vertex is a pair of an instrument and an outcome, with superoperator $\$_\alpha$; these are labels in the sense of the published experiment model.
--
--   Matrices on all the qubits are indexed by bit assignments to the $m+n$ qubits. A superoperator $\Phi$ on two qubits **acts at the vertex** $x$ as $\Phi$ on the two qubits meeting at $x$ and as the identity on all others. For a density matrix $\rho$ on all the qubits and a total label $t$, the **lattice probability** is
--   $$\mathrm{prob}(t)=\operatorname{Re}\operatorname{Tr}\Big[\$_{t(x_N)}\circ\cdots\circ\$_{t(x_1)}(\rho)\Big],$$
--   with $x_1,\dots,x_N$ the vertices in lexicographic order, each map acting at its vertex. An experiment model **is the model of the lattice** when its probability of each pair of a setting and an outcome family is the lattice probability of the corresponding total label.
--
--   This is the probability (6) of the paper for the setting of §5, and every later statement of the mission is about this model.
--
--   **Formalization Note** Lexicographic order extends the order along every qubit, since a right mover goes from $(u,v)$ to $(u,v+1)$ and a left mover from $(u,v)$ to $(u+1,v)$. Maps at vertices sharing no qubit commute, as the verification file proves, so any other extension gives the same number. The initial state is arbitrary because the paper names none, and labels are 0-based.
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §4.2, eq. (6), p.8; §5, p.12

import Mathlib
import Definitions.Def_HardyCausaloid_Model
import Definitions.Def_HardyFLocal_Superoperator
import Definitions.Def_HardyFLocal_Instrument

set_option autoImplicit false

namespace HardyFLocal

open scoped ComplexOrder

variable {m n : ℕ}

/-- **The qubits**, Hardy, arXiv:0804.0054v1, §5, p.12: right movers `Sum.inl u` and left movers
`Sum.inr v`.

**Formalization Note** "A large number" is read as every finite `m`, `n`, including small ones;
labels are 0-based. -/
abbrev Q (m n : ℕ) : Type := Fin m ⊕ Fin n

/-- **The vertices** `x ≡ uv`, arXiv:0804.0054v1, §5, p.12: every right mover `u` crosses every left
mover `v`, at the elementary region `R_uv`. -/
abbrev X (m n : ℕ) : Type := Fin m × Fin n

/-- **The knob settings at a vertex**: every instrument, arXiv:0804.0054v1, §5, p.12. -/
abbrev Setting (m n : ℕ) : X m n → Type := fun _ => Instrument

/-- **The outcomes on the display panel at a vertex**, arXiv:0804.0054v1, §5, p.12. -/
abbrev Outcome (m n : ℕ) : (x : X m n) → Setting m n x → Type := fun _ _ => ℕ

/-- **The superoperator `$_α` of a label** `α = ⟨f, y⟩`, arXiv:0804.0054v1, §5, p.12 ("we have a
superoperator $_{α_uv} associated with α_uv"). -/
def labelOp {x : X m n} (α : HardyCausaloid.Label (Setting m n) (Outcome m n) x) :
    Op (Fin 2 × Fin 2) :=
  α.1.op α.2

/-- **Matrices on all the qubits**, arXiv:0804.0054v1, §5, p.12: the `m + n` qubits have the tensor
product space with basis the bit assignments `Q m n → Fin 2`. -/
abbrev GlobalMat (m n : ℕ) : Type := Matrix (Q m n → Fin 2) (Q m n → Fin 2) ℂ

/-- A density matrix on all the qubits: positive semidefinite with trace `1`.

**Formalization Note** The paper names no initial state; every density matrix on all the qubits is
allowed, entangled or not, fixed once for the model. -/
def IsDensity (ρ : GlobalMat m n) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- The bit assignment `c` with the bits of the two qubits meeting at `x` replaced by `e`. -/
def setPair (x : X m n) (c : Q m n → Fin 2) (e : Fin 2 × Fin 2) : Q m n → Fin 2 :=
  Function.update (Function.update c (Sum.inl x.1) e.1) (Sum.inr x.2) e.2

/-- The two-qubit block of a global matrix at the qubits of `x`, with the bits of all other qubits
fixed by the row `c` and the column `d`. -/
def slice (x : X m n) (c d : Q m n → Fin 2) :
    GlobalMat m n →ₗ[ℂ] Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ where
  toFun A := Matrix.of fun e f => A (setPair x c e) (setPair x d f)
  map_add' A B := by
    ext e f
    simp
  map_smul' a A := by
    ext e f
    simp

/-- **A box acting at its vertex**, arXiv:0804.0054v1, §5, p.12: `embed x Φ` acts as `Φ` on the two
qubits `Sum.inl x.1`, `Sum.inr x.2` that meet at `x`, and as the identity on the others. -/
noncomputable def embed (x : X m n) (Φ : Op (Fin 2 × Fin 2)) : GlobalMat m n →ₗ[ℂ] GlobalMat m n where
  toFun A := Matrix.of fun c d =>
    Φ (slice x c d A) (c (Sum.inl x.1), c (Sum.inr x.2)) (d (Sum.inl x.1), d (Sum.inr x.2))
  map_add' A B := by
    ext c d
    simp
  map_smul' a A := by
    ext c d
    simp

/-- **The vertices in lexicographic order.** A right mover goes from `(u, v)` to `(u, v + 1)` and a
left mover from `(u, v)` to `(u + 1, v)`, arXiv:0804.0054v1, §5, pp.13–14, so this order extends the
order along every qubit.

**Formalization Note** Maps at vertices sharing no qubit commute, so any other extension gives the
same evaluation; this is checked in the mission's verification file. -/
def vertexList (m n : ℕ) : List (X m n) :=
  (List.finRange m).product (List.finRange n)

/-- **The state after all the boxes**, arXiv:0804.0054v1, §5, p.12: apply the superoperator of the
total label `t` at each vertex, in lexicographic order, starting from `ρ`. -/
noncomputable def evolve (ρ : GlobalMat m n)
    (t : ∀ x, HardyCausaloid.Label (Setting m n) (Outcome m n) x) : GlobalMat m n :=
  (vertexList m n).foldl (fun A x => embed x (labelOp (t x)) A) ρ

/-- **The lattice probability** `prob(Y_V | F_V)`, arXiv:0804.0054v1, §4.2, eq. (6), p.8, and §5,
p.12: the (real part of the) trace of the state after all the boxes. -/
noncomputable def latticeProb (ρ : GlobalMat m n)
    (t : ∀ x, HardyCausaloid.Label (Setting m n) (Outcome m n) x) : ℝ :=
  (evolve ρ t).trace.re

/-- **`M` is the experiment model of the qubit lattice with initial state `ρ`**, arXiv:0804.0054v1,
§4.2, eq. (6), p.8: `M.prob F Y` is the lattice probability of the total label `⟨F, Y⟩`. -/
def IsLatticeModel (ρ : GlobalMat m n) (M : HardyCausaloid.Model (Setting m n) (Outcome m n)) :
    Prop :=
  ∀ F Y, M.prob F Y = latticeProb ρ (fun x => ⟨F x, Y x⟩)

end HardyFLocal


