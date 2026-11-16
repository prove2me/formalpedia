-- Prove2me | Definitions.Def_PauliMixedness_Randomized_Supplement_Measurements
-- name    : PauliMixedness_Randomized_Supplement_Measurements
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:52:56.993203+00:00
-- url     : https://prove2.me/theorems/7cb1912e-ac44-49aa-99df-08d85b32be39
-- title:
--   Finite POVMs, product single-qubit measurements, and Pauli weight
-- statement:
--   A finite measurement on any finite complex matrix space is an arbitrary family $(M_x)_{x=0}^{m-1}$ of positive semidefinite effects summing to the identity, using the published POVM predicate. The outcome count $m$ is unrestricted and zero effects are allowed. On $N$ qubits, a single-qubit measurement has effects
--
--   $$M_y=\bigotimes_{j=1}^N L^{(j)}_{y_j},$$
--
--   where each $L^{(j)}$ is an arbitrary finite POVM on one qubit, and the outcome set is the full Cartesian product of its local outcome sets. An equivalence enumerates this finite set. Effects are padded by zero when an outcome index is out of range. The Pauli weight $w(Q)$ is the number of nonidentity wires of $Q$, with $w(I)=0$.
--
--   This separates the general published POVM notion from this paper's product-measurement restriction. No purity, rank, reality, projectivity, Pauli-only, or finite-precision restriction is imposed.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, §1.1 p.2, §§3.2–3.3 pp.9–11

import Definitions.Def_PauliMixedness_Randomized_QuantumModel
import Definitions.Def_FuchsVdGraaf_IsPOVM

noncomputable section
open scoped BigOperators

namespace PauliMixedness.Randomized.Supplement

/-- A finite POVM on any finite matrix carrier, using the published predicate.
The outcome count is arbitrary; zero effects and more outcomes than dimensions are allowed. -/
structure FiniteMeasurement (ι : Type) [Fintype ι] [DecidableEq ι] where
  outcomes : ℕ
  effect : Fin outcomes → Matrix ι ι ℂ
  isPOVM : FuchsVdGraaf.IsPOVM effect

abbrev FinitePOVM (N : ℕ) := FiniteMeasurement (QAlgorithms.Qubits N)

/-- Arbitrary local finite POVMs, independently prepared on each wire (p.2).
The equivalence only enumerates their full Cartesian product of outcomes. -/
def IsSingleQubit {N : ℕ} (M : FinitePOVM N) : Prop :=
  ∃ L : Fin N → FiniteMeasurement Bool,
    ∃ e : Fin M.outcomes ≃ (∀ j : Fin N, Fin (L j).outcomes),
      ∀ x, M.effect x = QAlgorithms.kronAll (fun j => (L j).effect (e x j))

/-- Every effect is padded by zero outside its own finite outcome range. -/
def paddedEffect {N : ℕ} (M : FinitePOVM N) (x : ℕ) : Operator N :=
  if hx : x < M.outcomes then M.effect ⟨x, hx⟩ else 0

/-- Weight excludes identity wires, including weight zero for the identity word. -/
def wordWeight {N : ℕ} (Q : Word N) : ℕ :=
  (Finset.univ.filter (fun j => Q j ≠ 0)).card

end PauliMixedness.Randomized.Supplement


