-- Prove2me | Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Joint
-- name    : SymmetricDepthHierarchy_ConstantDepth_Supplement_Joint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:56:30.033755+00:00
-- url     : https://prove2.me/theorems/7b08a1d2-8fb9-4255-b72c-0dacc43202a3
-- title:
--   Circuits on joint variables, Boolean sums, symVNP, and symmetric permanent projections
-- statement:
--   Circuit labels, wire multiplicities and finite evaluation are extended to an arbitrary variable type, with the same acyclicity, identified inputs and output-path conditions as the published circuit. Specializing the variables to $X_n$ explicitly produces that published circuit without changing wires or output.
--
--   A homomorphism $\rho:\Gamma_n\to\mathrm{Sym}(Y)$ gives the joint action on $X_n\sqcup Y$. For a witness polynomial $g$ define
--   $$\mathcal B(g)=\sum_{e:Y\to\{0,1\}}g(X_n,e).$$
--   The class $\mathrm{symVNP}$ requires polynomially bounded $|Y_n|$, joint-symmetric circuit witnesses at every positive index, and eventual polynomial orbit bounds measured under all extensions. Neither output invariance nor witness degree nor total size is assumed.
--
--   The permanent sums permutation products. A symmetric projection is an existential matrix of affine forms of some dimension $A\ge1$, whose permanent equals the target and whose entries satisfy the source's equivariance under separately chosen row and column permutations for every $\gamma$. There is no bound on $A$, and no homomorphism requirement on those choices. Only the auxiliary-free projection is needed in the completeness theorem. These are semantic definitions independent of the theorems asserting existence of witnesses and projections.
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 16–20 (PDF p. 19–23), Definition 7.1, §§7.1–7.3, Definition 7.6; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Classes
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Branching

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement


/-- §2.1 circuit syntax with an arbitrary variable type, needed by Definition 7.1. -/
inductive VariableLabel (K X : Type)
  | var (x : X)
  | const (c : K)
  | op (o : Op)

structure VariableCircuit (K X V : Type) where
  label : V → VariableLabel K X
  mult : V → V → ℕ
  out : V

namespace VariableCircuit
variable {K X V : Type} [Field K] [Fintype V]
def isInput (C : VariableCircuit K X V) (v : V) : Prop :=
  match C.label v with | .op _ => False | _ => True

def wire (C : VariableCircuit K X V) (u v : V) : Prop := 0 < C.mult v u

def wellFormed (C : VariableCircuit K X V) : Prop :=
  (∀ v u, C.isInput v → C.mult v u = 0) ∧
  (∀ v, ¬ Relation.TransGen C.wire v v) ∧
  (∀ u v, C.isInput u → C.isInput v → C.label u = C.label v → u = v) ∧
  ∀ v, Relation.ReflTransGen C.wire v C.out

def evalStep (C : VariableCircuit K X V) (a : V → MvPolynomial X K) (v : V) : MvPolynomial X K :=
  match C.label v with
  | .var x => MvPolynomial.X x
  | .const c => MvPolynomial.C c
  | .op .add => ∑ u, (C.mult v u : MvPolynomial X K) * a u
  | .op .mul => ∏ u, a u ^ C.mult v u

def evalAux (C : VariableCircuit K X V) : ℕ → V → MvPolynomial X K
  | 0 => C.evalStep (fun _ => 0)
  | k+1 => C.evalStep (C.evalAux k)

def polynomial (C : VariableCircuit K X V) : MvPolynomial X K := C.evalAux (Fintype.card V) C.out

def extension (C : VariableCircuit K X V) (γ : Equiv.Perm X) (σ : Equiv.Perm V) : Prop :=
  (∀ u v, C.mult (σ u) (σ v) = C.mult u v) ∧
  ∀ v, C.label (σ v) = match C.label v with
    | .var x => .var (γ x) | .const c => .const c | .op o => .op o

def symmetric (C : VariableCircuit K X V) {H : Type} [Group H] (ρ : H →* Equiv.Perm X) : Prop :=
  ∀ γ, ∃ σ, C.extension (ρ γ) σ

def maxOrb (C : VariableCircuit K X V) {H : Type} [Group H] (ρ : H →* Equiv.Perm X) : ℕ :=
  Finset.univ.sup fun v => (Finset.univ.filter fun w =>
    ∃ γ σ, C.extension (ρ γ) σ ∧ σ v = w).card

def isFormula (C : VariableCircuit K X V) : Prop :=
  (∀ u v, C.mult u v ≤ 1) ∧ ∀ v, ¬ C.isInput v → (∑ u, C.mult u v) ≤ 1

/-- The X_n specialization is the published circuit, with unchanged wires and output. -/
def toMatrix {n : ℕ} (C : VariableCircuit K (Fin n × Fin n) V) : Circuit K n V where
  label v := match C.label v with
    | .var (i,j) => .var i j | .const c => .const c | .op o => .op o
  mult := C.mult
  out := C.out
end VariableCircuit

/-- Joint action: row/column permutations on X_n and the homomorphism rho on Y. -/
def jointAction {n : ℕ} {Y : Type} (ρ : Circuit.Gamma n →* Equiv.Perm Y) :
    Circuit.Gamma n →* Equiv.Perm ((Fin n × Fin n) ⊕ Y) where
  toFun γ := Equiv.sumCongr (matrixAction n γ) (ρ γ)
  map_one' := by ext x; cases x <;> simp [matrixAction]
  map_mul' γ δ := by ext x; cases x <;> simp [matrixAction]

/-- Boolean cube sum with the X variables left formal. -/
def booleanSum {K Y : Type} [Field K] [Fintype Y] {n : ℕ}
    (g : MvPolynomial ((Fin n × Fin n) ⊕ Y) K) : MvPolynomial (Fin n × Fin n) K :=
  ∑ e : Y → Bool, MvPolynomial.eval₂Hom MvPolynomial.C
    (fun x => match x with
      | .inl ij => MvPolynomial.X ij
      | .inr y => MvPolynomial.C (if e y then 1 else 0)) g

/-- All indices have symmetric witnesses; the auxiliary count and orbit bounds are eventual.
No invariance, degree, or total-size condition is assumed of the witness or output. -/
def symVNP (K : Type) [Field K] : Set (Family K) :=
  {f | ∃ q : ℕ → ℕ, pBounded q ∧ ∃ c N : ℕ, ∀ n, 1 ≤ n →
    ∃ ρ : Circuit.Gamma n →* Equiv.Perm (Fin (q n)),
    ∃ m, ∃ C : VariableCircuit K ((Fin n × Fin n) ⊕ Fin (q n)) (Fin m),
      C.wellFormed ∧ C.symmetric (jointAction ρ) ∧ booleanSum C.polynomial = f n ∧
      (N ≤ n → C.maxOrb (jointAction ρ) ≤ n ^ c)}

/-- Permanent, including the empty matrix convention. §7.3. -/
def permanent {K : Type} [CommSemiring K] {A : Type} [Fintype A] (M : Matrix A A K) : K :=
  ∑ π : Equiv.Perm A, ∏ i, M i (π i)

def permanentFamily (K : Type) [Field K] : Family K := fun n =>
  permanent (fun (i j : Fin n) => MvPolynomial.X (i,j))

/-- Definition 7.6, auxiliary-free case needed by Theorem 7.7.
The dimension is existential and unbounded. The row and column permutations are independent. -/
def symmetricProjection {K : Type} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin n × Fin n) K) : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ ∃ M : Matrix (Fin a) (Fin a) (BorderDiffEq.AffineForm K (Fin n × Fin n)),
    permanent (fun i j => (M i j).toPoly) = f ∧
    ∀ γ : Circuit.Gamma n, ∃ α β : Equiv.Perm (Fin a), ∀ i j,
      (M (α i) (β j)).toPoly = MvPolynomial.rename (matrixAction n γ) (M i j).toPoly

end SymmetricDepthHierarchy.ConstantDepth.Supplement


