-- Prove2me | Definitions.Def_SharpPauliEntanglement_Exact_PauliModel
-- name    : SharpPauliEntanglement_Exact_PauliModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:50:00.410205+00:00
-- url     : https://prove2.me/theorems/45a22ca7-d0ef-4fdf-b3c3-313c2210322e
-- title:
--   Finite-qubit Pauli Hamiltonians, Gibbs densities, and separability
-- statement:
--   A finite qubit register has computational basis $\{0,1\}^Q$, with complex matrices acting on that basis. The four single-qubit matrices are $I,X,Y,Z$, using the usual Hermitian $Y$; a Pauli word $P$ is their actual tensor product. A specified Hamiltonian is
--
--   $$H=\sum_{i\in V}J_iP_i,\qquad \rho_\beta(H)=\frac{e^{-\beta H}}{\operatorname{Tr}e^{-\beta H}}.$$
--
--   The coefficients are real and nonzero, each term is nonidentity, and repeated words are allowed. Empty term sets and empty qubit registers are permitted. The partition function is $Z_H(w)=\operatorname{Tr}e^{-wH}$ for complex $w$. Normalized trace is $\tau(M)=2^{-|Q|}\operatorname{Tr}M$, and the Pauli coefficient norm is $\|M\|_{P,1}=\sum_P|\tau(P^\dagger M)|$, over the complete unsigned tensor-Pauli basis.
--
--   Full separability is a finite convex combination of tensor products $v_qv_q^\dagger$ with $\sum_b|v_q(b)|^2=1$. Pauli separability is the convex hull of products of the six projectors $(I\pm X)/2,(I\pm Y)/2,(I\pm Z)/2$. The corresponding unnormalized Pauli cone requires nonnegative coefficients without a sum-one condition and contains zero. Signed Hermitian strings and their average over all permutations of occurrence slots define the symmetrized product; repetitions occupy distinct slots.
--
--   These definitions separate the actual Gibbs state from the decomposition to be proved and distinguish the stronger upper conclusion from the general entanglement predicate needed for sharpness.
--
--   **Formalization Note** The register and term labels are arbitrary finite types in the definitions; theorem statements use finite integer labels. Tensor products are defined by their computational-basis entries. Generic $X,Y,Z$ are imported from the published elementary-gates definitions. No positivity or separability certificate is stored in the Hamiltonian.
-- source:
--   Bobak T. Kiani, Sharp universal death of entanglement threshold for Pauli Hamiltonians, STOC 2027 submission #159 (October 2026), pp. 2, 8–11, Eq. (1.1), §2, Eqs. (2.1)–(2.3), symmetrized product before Lemma 3.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace SharpPauliEntanglement.Exact

/-- Computational basis and operators on a finite qubit register (§2, p. 8). -/
abbrev Op (Q : Type) := Matrix (Q → Bool) (Q → Bool) ℂ
abbrev PauliWord (Q : Type) := Q → Fin 4

/-- The unsigned Hermitian convention I,X,Y,Z; in particular Yᵀ = -Y. -/
def pauli1 (a : Fin 4) : Matrix Bool Bool ℂ :=
  if a = 0 then 1 else if a = 1 then QAlgorithms.pauliX
  else if a = 2 then QAlgorithms.pauliY else QAlgorithms.pauliZ

/-- Actual tensor product, entrywise in the computational basis. -/
def tensorOp {Q : Type} [Fintype Q] (M : Q → Matrix Bool Bool ℂ) : Op Q :=
  fun a b => ∏ q, M q (a q) (b q)

def pauliOp {Q : Type} [Fintype Q] (P : PauliWord Q) : Op Q :=
  tensorOp (fun q => pauli1 (P q))

def pauliSupport {Q : Type} [Fintype Q] (P : PauliWord Q) : Finset Q := by
  classical
  exact Finset.univ.filter (fun q => P q ≠ 0)

/-- A specified labelled decomposition; nonidentity terms, real nonzero coefficients (§2).
There is no distinctness, locality, or commutation requirement. Empty label sets are allowed. -/
structure PauliHamiltonian (Q V : Type) [Fintype Q] where
  term : V → PauliWord Q
  coeff : V → ℝ
  nonidentity : ∀ i, (pauliSupport (term i)).Nonempty
  nonzero : ∀ i, coeff i ≠ 0

def hamiltonian {Q V : Type} [Fintype Q] [Fintype V]
    (H : PauliHamiltonian Q V) : Op Q := ∑ i, (H.coeff i : ℂ) • pauliOp (H.term i)

/-- Eq. (1.1). No positivity or separability is stored in the model. -/
def gibbs {Q : Type} [Fintype Q] [DecidableEq Q] (H : Op Q) (β : ℝ) : Op Q :=
  let E := NormedSpace.exp ((-β : ℂ) • H)
  E.trace⁻¹ • E

def partitionFunction {Q : Type} [Fintype Q] [DecidableEq Q]
    (H : Op Q) (w : ℂ) : ℂ := (NormedSpace.exp ((-w) • H)).trace

def normalizedTrace {Q : Type} [Fintype Q] (M : Op Q) : ℂ :=
  ((2 : ℂ) ^ Fintype.card Q)⁻¹ * M.trace

/-- The coefficient in the complete unsigned tensor-Pauli basis, Eq. (2.2). -/
def pauliCoeff {Q : Type} [Fintype Q] (M : Op Q) (P : PauliWord Q) : ℂ :=
  normalizedTrace ((pauliOp P).conjTranspose * M)

def pauliNorm {Q : Type} [Fintype Q] (M : Op Q) : ℝ :=
  ∑ P : PauliWord Q, ‖pauliCoeff M P‖

/-- vv† for a normalized single-qubit vector. -/
def pureProjector (v : Bool → ℂ) : Matrix Bool Bool ℂ := fun a b => v a * star (v b)

def IsUnitQubit (v : Bool → ℂ) : Prop := ∑ b, ‖v b‖ ^ 2 = 1

/-- Full separability: arbitrary normalized single-qubit pure states, not just Paulis. -/
def FullySeparable {Q : Type} [Fintype Q] (M : Op Q) : Prop :=
  ∃ k : ℕ, ∃ w : Fin k → ℝ, ∃ v : Fin k → Q → Bool → ℂ,
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ (∀ i q, IsUnitQubit (v i q)) ∧
    M = ∑ i, (w i : ℂ) • tensorOp (fun q => pureProjector (v i q))

/-- The six single-qubit Pauli eigenprojectors (axis ∈ {X,Y,Z}, sign ∈ {±1}). -/
def pauliProjector (axis : Fin 3) (negative : Bool) : Matrix Bool Bool ℂ :=
  (1 / 2 : ℂ) • (1 + (if negative then (-1 : ℂ) else 1) • pauli1 ⟨axis.val + 1, by omega⟩)

def productPauliProjector {Q : Type} [Fintype Q]
    (axis : Q → Fin 3) (negative : Q → Bool) : Op Q :=
  tensorOp (fun q => pauliProjector (axis q) (negative q))

/-- Unnormalized cone; zero and empty combinations are included. -/
def PauliSeparableCone {Q : Type} [Fintype Q] (M : Op Q) : Prop :=
  ∃ k : ℕ, ∃ w : Fin k → ℝ, ∃ a : Fin k → Q → Fin 3, ∃ s : Fin k → Q → Bool,
    (∀ i, 0 ≤ w i) ∧ M = ∑ i, (w i : ℂ) • productPauliProjector (a i) (s i)

/-- The normalized convex hull used in the sufficient half of Theorem 1.1. -/
def PauliSeparable {Q : Type} [Fintype Q] (M : Op Q) : Prop :=
  ∃ k : ℕ, ∃ w : Fin k → ℝ, ∃ a : Fin k → Q → Fin 3, ∃ s : Fin k → Q → Bool,
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
    M = ∑ i, (w i : ℂ) • productPauliProjector (a i) (s i)

/-- Signed Hermitian strings for Lemma 3.4, allowing repetitions and identity. -/
structure SignedPauli (Q : Type) where
  word : PauliWord Q
  negative : Bool

def signedOp {Q : Type} [Fintype Q] (S : SignedPauli Q) : Op Q :=
  (if S.negative then (-1 : ℂ) else 1) • pauliOp S.word

/-- Slot permutations count repeated occurrences separately (p. 11). -/
def symmetrizedProduct {Q : Type} [Fintype Q] [DecidableEq Q] {M : ℕ}
    (S : Fin M → SignedPauli Q) : Op Q :=
  ((Nat.factorial M : ℂ)⁻¹) •
    ∑ π : Equiv.Perm (Fin M), (List.ofFn (fun i => signedOp (S (π i)))).prod

end SharpPauliEntanglement.Exact


