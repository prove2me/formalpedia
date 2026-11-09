-- Prove2me | Definitions.Def_InvariantMoneySecurity_Decomposition_FiniteScheme
-- name    : InvariantMoneySecurity_Decomposition_FiniteScheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:54:03.698297+00:00
-- url     : https://prove2.me/theorems/71d7cd59-e575-40ce-8b79-4e1310bd389f
-- title:
--   Finite move systems, orbit projectors, and the spectral gap
-- statement:
--   At object length $n$, fix a nonempty set $X\subseteq\{0,1\}^n$, a nonempty indexed set of distinct permutations $S$ of $X$, and an invariant $I:X\to\{0,1\}^{s}$. An inverse permutation of the indices witnesses $S=S^{-1}$, and $I(sx)=I(x)$ for every move. Reachability by a finite word defines the orbit $C(x)$. A serial level set is $P_p=\{x:I(x)=p\}$ and may contain several orbits.
--
--   On the valid object subspace the lazy walk is
--   $$\widehat B=\tfrac12\left(\mathrm{Id}+\frac1{|S|}\sum_{s\in S}P_s\right).$$
--   The fixed-space projector is blockwise averaging: its $(x,y)$ entry is $1/|C(x)|$ when $x,y$ belong to the same orbit, and zero otherwise. Multiplying by the serial projector gives $\Pi_1^{(p)}$, which includes every orbit of serial $p$. The accepted weight of $\rho$ is $\operatorname{Tr}(\Pi_1^{(p)}\rho)$. The banknote is the uniform vector on $P_p$.
--
--   The gap is $1-\max(\{0\}\cup\Lambda_{\mathrm{nonfixed}})$, where $\Lambda_{\mathrm{nonfixed}}$ consists of eigenvalues on the valid subspace orthogonal to all uniform orbit vectors. This equals the minimum orbit gap; adjoining zero gives gap one when every orbit is a singleton. The eigenvalue set is finite and lies in $[0,1]$, so no unbounded-supremum default is used. All matrices are extended by zero on invalid object encodings, which reject. Computational hypotheses are added separately in Scheme.
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), pp. 6–7, Definition 2.1 and words/orbits; p. 10, equation (6) and Definition 3.2

import Definitions.Def_InvariantMoneySecurity_Decomposition_QuantumModel
set_option autoImplicit false
noncomputable section

namespace InvariantMoneySecurity.Decomposition

attribute [local instance] Classical.propDecidable

/-- The finite combinatorial data, prior to any efficiency assumptions.
The inverse permutation on move indices makes the uniform move law inverse-closed. -/
structure FiniteScheme (n : ℕ) where
  ground : Finset (Bits n)
  ground_nonempty : ground.Nonempty
  moveCount : ℕ
  moves_nonempty : 0 < moveCount
  move : Fin moveCount → Equiv.Perm {x // x ∈ ground}
  distinct_moves : Function.Injective move
  inverseIndex : Equiv.Perm (Fin moveCount)
  inverse_eq : ∀ j, move (inverseIndex j) = (move j).symm
  serialBits : ℕ
  invariant : {x // x ∈ ground} → Bits serialBits
  invariant_move : ∀ j x, invariant (move j x) = invariant x

/-- The genuine object register, a subspace of the padded qubit register. -/
abbrev FiniteScheme.Object {n : ℕ} (D : FiniteScheme n) := {x // x ∈ D.ground}

/-- Reachability by a finite sequence of indexed moves; a zero-length word is allowed. -/
def FiniteScheme.Reaches {n : ℕ} (D : FiniteScheme n) (x y : D.Object) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ j, D.move j a = b) x y

/-- Orbit as a finite set in the physical basis, with no arbitrary orbit labels. -/
def FiniteScheme.orbit {n : ℕ} (D : FiniteScheme n) (x : D.Object) : Finset (Bits n) :=
  D.ground.filter fun y => ∃ h : y ∈ D.ground, D.Reaches x ⟨y, h⟩

/-- Level sets may contain more than one orbit; an invalid serial gives the empty set. -/
def FiniteScheme.level {n : ℕ} (D : FiniteScheme n) (p : Bits D.serialBits) : Finset (Bits n) :=
  D.ground.filter fun y => ∃ h : y ∈ D.ground, D.invariant ⟨y, h⟩ = p

/-- Uniform banknote, with zero assigned only to serials that are never minted. -/
def FiniteScheme.banknote {n : ℕ} (D : FiniteScheme n) (p : Bits D.serialBits) :=
  uniformVector (D.level p)

/-- The source's uniform orbit vector, embedded by zero outside the orbit. -/
def FiniteScheme.orbitVector {n : ℕ} (D : FiniteScheme n) (x : D.Object) :=
  uniformVector (D.orbit x)

/-- Projection onto valid object encodings. -/
def FiniteScheme.groundProjector {n : ℕ} (D : FiniteScheme n) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.diagonal fun x => if x ∈ D.ground then 1 else 0

/-- Coherent serial check, with invalid object encodings rejecting. -/
def FiniteScheme.serialProjector {n : ℕ} (D : FiniteScheme n) (p : Bits D.serialBits) :
    Matrix (Bits n) (Bits n) ℂ :=
  Matrix.diagonal fun x => if x ∈ D.level p then 1 else 0

/-- The indexed permutation, extended by zero on the rejected physical subspace. -/
def FiniteScheme.moveOperator {n : ℕ} (D : FiniteScheme n) (j : Fin D.moveCount) :
    Matrix (Bits n) (Bits n) ℂ :=
  fun y x => if h : x ∈ D.ground then if (D.move j ⟨x, h⟩).val = y then 1 else 0 else 0

/-- Equation (4), including the lazy factor one half. On invalid encodings it is zero. -/
def FiniteScheme.walk {n : ℕ} (D : FiniteScheme n) : Matrix (Bits n) (Bits n) ℂ :=
  (1 / 2 : ℂ) • (D.groundProjector +
    (D.moveCount : ℂ)⁻¹ • ∑ j, D.moveOperator j)

/-- Blockwise orbit averaging: the sum of all uniform-orbit projectors.
The kernel on one orbit is 1/|C|, and is zero between distinct orbits. -/
def FiniteScheme.fixedProjector {n : ℕ} (D : FiniteScheme n) : Matrix (Bits n) (Bits n) ℂ :=
  fun x y => if hx : x ∈ D.ground then
    if hy : y ∈ D.ground then
      if D.Reaches ⟨x, hx⟩ ⟨y, hy⟩ then ((D.orbit ⟨x, hx⟩).card : ℂ)⁻¹ else 0
    else 0
  else 0

/-- All orbit states with this serial, including every co-orbit. -/
def FiniteScheme.acceptedProjector {n : ℕ} (D : FiniteScheme n) (p : Bits D.serialBits) :=
  D.serialProjector p * D.fixedProjector

/-- Definition 3.2: accepted weight is a Born probability for the concrete orbit projector. -/
def FiniteScheme.acceptedWeight {n : ℕ} (D : FiniteScheme n) (p : Bits D.serialBits)
    (ρ : Matrix (Bits n) (Bits n) ℂ) : ℝ := born (D.acceptedProjector p) ρ

/-- Nonfixed eigenvalues of the actual walk on valid objects. -/
def FiniteScheme.nonfixedEigenvalues {n : ℕ} (D : FiniteScheme n) : Set ℝ :=
  {t | ∃ v : Bits n → ℂ, v ≠ 0 ∧
    (∀ x, x ∉ D.ground → v x = 0) ∧ D.fixedProjector.mulVec v = 0 ∧
    D.walk.mulVec v = (t : ℂ) • v}

/-- The set is finite and contained in [0,1]; adjoining zero handles singleton blocks.
Thus this is the minimum of the orbit gaps, and equals one when all orbits are singletons. -/
def FiniteScheme.gap {n : ℕ} (D : FiniteScheme n) : ℝ :=
  1 - sSup (insert 0 D.nonfixedEigenvalues)

end InvariantMoneySecurity.Decomposition


