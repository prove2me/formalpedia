-- Prove2me | Definitions.Def_SharpPauliEntanglement_Exact_Polymers
-- name    : SharpPauliEntanglement_Exact_Polymers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:54:50.348492+00:00
-- url     : https://prove2.me/theorems/d6266a0a-5242-4f99-a69f-cafc9b90e6b1
-- title:
--   Inclusion-exclusion operators and arbitrary-shift Gibbs decomposition
-- statement:
--   For a specified Pauli Hamiltonian, let $z_i=\beta|J_i|$ and $S_i=-\operatorname{sgn}(J_i)P_i$. Define
--
--   $$F_U=\frac{\exp(\sum_{i\in U}z_iS_i)}{\prod_{i\in U}\cosh z_i},\qquad D_U=\sum_{B\subseteq U}(-1)^{|U|-|B|}F_B.$$
--
--   A polymer is a nonempty connected term set. A compatible family consists of polymers that neither intersect nor have an overlap edge between them; the empty family is included. For arbitrary real shifts $r_\gamma$, put
--
--   $$R_\gamma=r_\gamma I+D_\gamma,\qquad Q_G(S)=\sum_{\Gamma\text{ compatible},\ \gamma\subseteq S}\prod_{\gamma\in\Gamma}(-r_\gamma).$$
--
--   The decomposition expression sums $Q_G(V\setminus N_G[\bigcup\Gamma])\prod_{\gamma\in\Gamma}R_\gamma$ over compatible families. The threshold choice of shift is $r_\gamma=t^{|\gamma|}w_A(\gamma)$. These expressions are definitions, with no norm bound, positivity, or separability assumed; admissibility of arbitrary shifts is a theorem hypothesis in Proposition 3.2.
--
--   The operators retain their actual matrix exponentials and inclusion-exclusion signs. Their role is to connect the quantum density to finite graph polynomials.
--
--   **Formalization Note** The exponential is evaluated directly with exponent $-\beta\sum_{i\in U}J_iP_i$, equal to the signed form above. Finite matrix products use an enumeration; compatible factors commute, so this changes no source instance. For $B\subseteq U$ the natural subtraction $|U|-|B|$ is exact.
-- source:
--   Bobak T. Kiani, Sharp universal death of entanglement threshold for Pauli Hamiltonians, STOC 2027 submission #159 (October 2026), pp. 8–10, 13, Eqs. (2.1), (3.1), (3.5)–(3.6), (3.19)

import Definitions.Def_SharpPauliEntanglement_Exact_GraphWeights

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace SharpPauliEntanglement.Exact

/-- An arbitrary enumeration for a finite matrix product. Used only for commuting families. -/
def matrixProduct {Q V : Type} [Fintype Q] [DecidableEq V]
    (S : Finset V) (f : V → Op Q) : Op Q := (S.toList.map f).prod

def termZ {Q V : Type} [Fintype Q] (H : PauliHamiltonian Q V) (β : ℝ) (i : V) : ℝ :=
  β * |H.coeff i|

def termS {Q V : Type} [Fintype Q] (H : PauliHamiltonian Q V) (i : V) : SignedPauli Q :=
  ⟨H.term i, decide (0 < H.coeff i)⟩

/-- Eq. (3.1): signed reparameterization evaluated directly as -β times the restricted H. -/
def normalizedExp {Q V : Type} [Fintype Q] [DecidableEq Q] [DecidableEq V]
    (H : PauliHamiltonian Q V) (β : ℝ) (U : Finset V) : Op Q :=
  ((∏ i ∈ U, (Real.cosh (termZ H β i) : ℂ))⁻¹) •
    NormedSpace.exp (∑ i ∈ U, (-β * H.coeff i : ℂ) • pauliOp (H.term i))

/-- Inclusion-exclusion, retaining U = ∅. -/
def inclusionExclusion {Q V : Type} [Fintype Q] [DecidableEq Q] [DecidableEq V]
    (H : PauliHamiltonian Q V) (β : ℝ) (U : Finset V) : Op Q :=
  ∑ B ∈ U.powerset, ((-1 : ℂ) ^ (U.card - B.card)) • normalizedExp H β B

def compatible {V : Type} [DecidableEq V] (G : SimpleGraph V) (C D : Finset V) : Prop :=
  Disjoint C D ∧ ∀ i ∈ C, ∀ j ∈ D, ¬ G.Adj i j

/-- Includes the empty family. Polymers are nonempty connected induced sets. -/
def polymerFamilies {V : Type} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    Finset (Finset (Finset V)) :=
  (S.powerset.filter (ConnectedSet G)).powerset.filter (fun Γ => ∀ C ∈ Γ, ∀ D ∈ Γ, C ≠ D → compatible G C D)

def closedNeighborhood {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) : Finset V :=
  Finset.univ.filter (fun j => ∃ i ∈ U, j = i ∨ G.Adj i j)

/-- General arbitrary-shift polynomial of Eq. (3.5). -/
def polymerPolynomial {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (r : Finset V → ℝ) (S : Finset V) : ℝ :=
  ∑ Γ ∈ polymerFamilies G S, ∏ γ ∈ Γ, -r γ

def shiftedPolymer {Q V : Type} [Fintype Q] [DecidableEq Q] [DecidableEq V]
    (H : PauliHamiltonian Q V) (β : ℝ) (r : Finset V → ℝ) (γ : Finset V) : Op Q :=
  (r γ : ℂ) • 1 + inclusionExclusion H β γ

/-- The complete right-hand side of Eq. (3.6). -/
def polymerDecomposition {Q V : Type} [Fintype Q] [DecidableEq Q]
    [Fintype V] [DecidableEq V] (H : PauliHamiltonian Q V) (β : ℝ)
    (r : Finset V → ℝ) : Op Q :=
  ∑ Γ ∈ polymerFamilies (overlapGraph H) Finset.univ,
    (polymerPolynomial (overlapGraph H) r
      (Finset.univ \ closedNeighborhood (overlapGraph H) (Γ.biUnion id)) : ℂ) •
        matrixProduct Γ (shiftedPolymer H β r)

/-- Eq. (3.19), fixed at the original degree bound. -/
def thresholdShift {Q V : Type} [Fintype Q] [DecidableEq V]
    (H : PauliHamiltonian Q V) (Δ : ℕ) (γ : Finset V) : ℝ :=
  criticalT Δ ^ γ.card * redWeight (antiGraph H) Δ γ

end SharpPauliEntanglement.Exact


