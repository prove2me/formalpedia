-- Prove2me | Definitions.Def_SaglamGV_Circuit
-- name    : SaglamGV_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:47:42.665866+00:00
-- url     : https://prove2.me/theorems/79e9685b-4710-43fd-be5d-a7a35bfb1821
-- title:
--   Circuits in $B_d$, the kernel set $K$, the odd-circuit count $Z$, uniform random matrices
-- statement:
--   A **circuit** is an inclusion-minimal linearly dependent finite subset $S\subseteq\mathbb F_2^n$: $S$ is linearly dependent and every proper subset of $S$ is linearly independent. $\mathbb C_\ell$ denotes the collection of $\ell$-element circuits contained in $B_d$. For a matrix $M\in\mathbb F_2^{m\times n}$,
--
--   $$
--   K=\{x\in B_d : Mx=0\},
--   $$
--
--   and $Z$ is the number of **odd circuits** (circuits of odd cardinality) of $B_d$ contained in $K$. Expectations and probabilities over $M$ are taken with $M$ uniform on $\mathbb F_2^{m\times n}$, i.e. as averages over all $2^{mn}$ matrices. Finally, the code with parity check matrix $H$ is $\ker H$, and appending a row $v$ to $M$ gives the $(m+1)\times n$ matrix with last row $v$.
--
--   The proof chooses $m$ about $\lg(V/(cn))$, so that $K$ is typically nonempty, and shows that some $M$ has $Z=0$; one extra row then kills all of $K$.
--
--   **Formalization Note** `IsCircuit S` uses linear independence over `ZMod 2` of the elements of the finite set `S`. `circuits n d ℓ`, `kerSet d M`, `oddCircuitCount d M`, `avgM`, `probM`, `parityCode H := ker H`, `appendRow M v` (via `Fin.snoc`).
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §1, p.1 (parity check matrix); §2, pp.2–3 (K, circuits, C_ℓ, Z, uniform M, appending v)

import Mathlib
import Definitions.Def_SaglamGV_Code

namespace SaglamGV

open Matrix

/-- A **circuit**: an inclusion-minimal linearly dependent finite subset of `𝔽₂ⁿ`
(M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript
(held version, sha256 ac6f2bba…), §2, p.2: "A circuit in B_d is an inclusion-minimal linearly
dependent subset").

**Formalization Note** `S` is linearly dependent (as a set, i.e. the inclusion of `S` is not
linearly independent over `ZMod 2`) and every proper subset of `S` is linearly independent. A circuit
"in `B_d`" is a circuit `S` with `S ⊆ B_d`. -/
def IsCircuit {n : ℕ} (S : Finset (Fin n → ZMod 2)) : Prop :=
  ¬ LinearIndependent (ZMod 2) (Subtype.val : ↥(S : Set (Fin n → ZMod 2)) → Fin n → ZMod 2) ∧
    ∀ T ⊂ S, LinearIndependent (ZMod 2) (Subtype.val : ↥(T : Set (Fin n → ZMod 2)) → Fin n → ZMod 2)

open Classical in
/-- All circuits contained in `B_d`. -/
noncomputable def allCircuits (n d : ℕ) : Finset (Finset (Fin n → ZMod 2)) :=
  (ballP n d).powerset.filter IsCircuit

open Classical in
/-- `C_ℓ`, the collection of `ℓ`-element circuits in `B_d` (Saglam, §2, p.2: "If C_ℓ is the
collection of ℓ-element circuits in B_d"). -/
noncomputable def circuits (n d ℓ : ℕ) : Finset (Finset (Fin n → ZMod 2)) :=
  (allCircuits n d).filter (fun S => S.card = ℓ)

/-- `K = {x ∈ B_d | Mx = 0}` for a matrix `M ∈ 𝔽₂^{m×n}` (Saglam, §2, p.2: "put
K := {x ∈ B_d | Mx = 0}"). -/
def kerSet {m n : ℕ} (d : ℕ) (M : Matrix (Fin m) (Fin n) (ZMod 2)) : Finset (Fin n → ZMod 2) :=
  (ballP n d).filter (fun x => M *ᵥ x = 0)

open Classical in
/-- `Z`, the number of odd circuits in `B_d` contained in `K` (Saglam, §2, p.2: "Let Z be the number
of odd circuits contained in K"); odd means odd cardinality. -/
noncomputable def oddCircuitCount {m n : ℕ} (d : ℕ) (M : Matrix (Fin m) (Fin n) (ZMod 2)) : ℕ :=
  ((allCircuits n d).filter (fun S => S ⊆ kerSet d M ∧ Odd S.card)).card

/-- Expectation over a uniformly random matrix `M ∈ 𝔽₂^{m×n}` (Saglam, §2, p.2: "Choose M uniformly
from F_2^{m×n}"): the average of `f` over all `2^{mn}` matrices. -/
noncomputable def avgM {m n : ℕ} (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℝ) : ℝ :=
  (∑ M, f M) / (2 : ℝ) ^ (m * n)

open Classical in
/-- Probability of an event over a uniformly random matrix `M ∈ 𝔽₂^{m×n}`. -/
noncomputable def probM {m n : ℕ} (P : Matrix (Fin m) (Fin n) (ZMod 2) → Prop) : ℝ :=
  avgM (fun M => if P M then (1 : ℝ) else 0)

/-- The binary linear code with parity check matrix `H ∈ 𝔽₂^{r×n}`, i.e. `ker H`
(Saglam, §1, p.1: "a linear code of size 2^{n−r} may be specified through its parity check matrix"). -/
def parityCode {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2)) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.ker H.mulVecLin

/-- The matrix obtained by appending the row `v` to `M` as its last row (Saglam, §2, p.3:
"Appending v to M"). -/
def appendRow {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    Matrix (Fin (m + 1)) (Fin n) (ZMod 2) :=
  Matrix.of (Fin.snoc (α := fun _ => Fin n → ZMod 2) (fun i => M i) v)

end SaglamGV


