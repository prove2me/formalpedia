-- Prove2me | Definitions.Def_SingleInteraction_Supplement_Pinned
-- name    : SingleInteraction_Supplement_Pinned
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:02:59.868034+00:00
-- url     : https://prove2.me/theorems/0a9f0d42-b8e1-4747-b123-090143e6f573
-- title:
--   $p$-Pinned SIH$_k$ and DSIH$_k$ (Definitions 35–38)
-- statement:
--   A **$p$-pinned** single-interaction instance is an SIH$_k$ instance $(n,L,a,b)$ together with an ordered list $A=(a_1,\dots,a_p)$ of $p$ distinct physical qubits (the pinned register) and the description of a circuit $C_{\mathrm{pin}}$ over the gate set $\{H,T,\mathrm{CNOT}\}$ on $p$ qubits with at most $\mathrm{poly}(n)$ gates. The pinned state is $|\psi_{\mathrm{pin}}\rangle=C_{\mathrm{pin}}|0^p\rangle$; with $W$ the remaining $n-p$ qubits, the isometry $V_{\mathrm{pin}}|\phi\rangle=|\phi\rangle_W\otimes|\psi_{\mathrm{pin}}\rangle_A$ compresses the Hamiltonian $H=\sum_{e\in L}h_e$ to
--   $$H_{\mathrm{pin}}=V_{\mathrm{pin}}^\dagger H V_{\mathrm{pin}}.$$
--   YES: $\lambda_{\min}(H_{\mathrm{pin}})\le a$; NO: $\lambda_{\min}(H_{\mathrm{pin}})\ge b$. All other input conditions are those of SIH$_k$. For $p$-Pinned DSIH$_k$ the interaction is $h^{(n)}$ with $n$ the final number of physical qubits, pinned ones included. The stoquastic variants (Definitions 37, 38) are the same problems for a stoquastic interaction (family).
--
--   These are the problems of Theorems 69, 74 and 76.
--
--   **Formalization Note** Qubit $j$ of the pinned register is $a_{j+1}$; $W$ is the set of the other qubits in their natural order, so the split $W\otimes A$ is a reindexing of the register and not a move of $A$ to the end. The circuit has at most $(n+1)^c$ gates for the instance exponent $c$; gates act in list order. $p$ is a fixed parameter of the problem.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Definitions 35–38, pp.31–32

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_onTuple
import Definitions.Def_SingleInteraction_SIHInstance
import Definitions.Def_SingleInteraction_SIHInstance_Valid
import Definitions.Def_SingleInteraction_sihHam
import Definitions.Def_SingleInteraction_Supplement_Linalg

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding Matrix

namespace SingleInteraction

namespace Supplement

/-!
# Pinned single-interaction problems (Definitions 35–38)

Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version,
sha256 19ddc444…), Definitions 35–38, pp.31–32: in addition to an `SIH_k` (resp. `DSIH_k`) input,
"An ordered set `A = (a1, . . . , ap)` of `p` distinct physical qubits, called the pinned register,
together with a classical description of a polynomial-size quantum circuit `Cpin` over a fixed finite
gate set acting on `p` qubits. The pinned state is `|ψpin⟩A = Cpin |0p⟩A`. Let `W` denote the
remaining `n − p` qubits and define the isometry `Vpin |ϕ⟩ = |ϕ⟩W ⊗ |ψpin⟩A`. […]
`Hpin = V†pin H Vpin`. The promise is that exactly one of `λmin(Hpin) ≤ a` or `λmin(Hpin) ≥ b`
holds." The stoquastic variants (Definitions 37, 38) restrict the interaction (every `h^(n)`) to be
stoquastic; that restriction is a hypothesis/conclusion on `h` in the theorems (`IsStoquastic`).

**Formalization Note**
* The gate set of `Cpin` is the base gate set `{H, T, CNOT}` (the published `QMAGate`, with
  `qmaHadamard`, `qmaPhaseT`); qubit `j` of the pinned register is `a_{j+1}`. Gates are applied in
  list order. "Polynomial-size" is at most `(n+1)^c` gates, with the instance exponent `c`.
* `W` is the subtype of qubits of `{0, …, n−1}` not in `A`; `Vpin` places `ϕ` on `W` and `|ψpin⟩`
  on the qubits `a_1, …, a_p` in that order. No reordering "to the last `p` qubits" is made.
* `p` is a fixed constant of the problem, a parameter of `pinnedSihProblem`.
* The promise uses `lamMin` of the compressed Hamiltonian, as in Definition 35. -/

/-- The CNOT matrix on two qubits (control first, target second). -/
def cnotMatrix : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  fun s t => if s 0 = t 0 ∧ s 1 = (if t 0 = 1 then 1 - t 1 else t 1) then 1 else 0

/-- A gate of the base set `{H, T, CNOT}` as an operator on a `p`-qubit register (the identity if
its qubit indices are out of range or coincide). -/
noncomputable def pinGateMatrix (p : ℕ) : QMAGate → Matrix (Fin p → Fin 2) (Fin p → Fin 2) ℂ
  | .hadamard i => if h : i < p then onTuple (oneQ qmaHadamard) (fun _ : Fin 1 => (⟨i, h⟩ : Fin p)) else 1
  | .phaseT i => if h : i < p then onTuple (oneQ qmaPhaseT) (fun _ : Fin 1 => (⟨i, h⟩ : Fin p)) else 1
  | .controlledNot i j =>
      if h : i < p ∧ j < p ∧ i ≠ j then onTuple cnotMatrix (![⟨i, h.1⟩, ⟨j, h.2.1⟩] : Fin 2 → Fin p) else 1

/-- The pinned state `|ψpin⟩ = Cpin |0^p⟩`, gates applied in list order. -/
noncomputable def pinState (p : ℕ) (gates : List QMAGate) : EuclideanSpace ℂ (Fin p → Fin 2) :=
  Matrix.toEuclideanLin
    (gates.foldl (fun M g => pinGateMatrix p g * M) (1 : Matrix (Fin p → Fin 2) (Fin p → Fin 2) ℂ))
    (EuclideanSpace.single (fun _ : Fin p => (0 : Fin 2)) 1)

/-- A pinned instance: an `SIH`/`DSIH` instance, the pinned register `A = (a1, …, ap)` and the gate
list of `Cpin`. -/
structure PinnedInstance where
  base : SIHInstance
  pins : List ℕ
  gates : List QMAGate

/-- Equivalence used to build the pinned-instance code. -/
def pinnedInstanceEquiv : PinnedInstance ≃ SIHInstance × (List ℕ × List QMAGate) where
  toFun x := (x.base, x.pins, x.gates)
  invFun y := ⟨y.1, y.2.1, y.2.2⟩
  left_inv x := by cases x; rfl
  right_inv y := by rcases y with ⟨a, b, c⟩; rfl

/-- The code of a pinned instance: the `SIH` code, then the pinned qubits, then the gates. -/
def pinnedCodec : Codec PinnedInstance :=
  BinaryEncoding.equiv (pair sihCodec (pair (BinaryEncoding.list natural)
    (BinaryEncoding.list qmaGateCodec))) pinnedInstanceEquiv

/-- Validity of a `p`-pinned instance for locality `k` and exponent `c`: a valid `SIH_k` instance,
`p` distinct pinned qubits in range, and at most `(n+1)^c` well-formed gates on `p` qubits. -/
def PinnedInstance.Valid (k p c : ℕ) (x : PinnedInstance) : Prop :=
  x.base.Valid k c ∧ x.pins.length = p ∧ x.pins.Nodup ∧ (∀ a ∈ x.pins, a < x.base.n) ∧
    x.gates.length ≤ (x.base.n + 1) ^ c ∧ ∀ g ∈ x.gates, g.WellFormed p

/-- The unpinned register `W`: qubits not in `A`. -/
def PinnedInstance.W (x : PinnedInstance) : Type :=
  {i : Fin x.base.n // (i : ℕ) ∉ x.pins}

instance (x : PinnedInstance) : Fintype x.W := by unfold PinnedInstance.W; infer_instance

instance (x : PinnedInstance) : DecidableEq x.W := by unfold PinnedInstance.W; infer_instance

/-- The isometry `Vpin |ϕ⟩ = |ϕ⟩_W ⊗ |ψpin⟩_A` as a matrix. -/
noncomputable def PinnedInstance.Vpin (p : ℕ) (x : PinnedInstance) :
    Matrix (Fin x.base.n → Fin 2) (x.W → Fin 2) ℂ :=
  fun s w =>
    (if ∀ i : x.W, s i.1 = w i then 1 else 0) *
      (if hv : ∀ j : Fin p, x.pins.getD j 0 < x.base.n then
        pinState p x.gates (fun j => s ⟨x.pins.getD j 0, hv j⟩) else 0)

/-- `Hpin = V†pin H Vpin` for an `n`-qubit Hamiltonian `H`. -/
noncomputable def PinnedInstance.compress (p : ℕ) (x : PinnedInstance)
    (H : Matrix (Fin x.base.n → Fin 2) (Fin x.base.n → Fin 2) ℂ) :
    Matrix (x.W → Fin 2) (x.W → Fin 2) ℂ :=
  (x.Vpin p)ᴴ * H * x.Vpin p

/-- The promise problem of a pinned family: valid instances with `λmin(Hpin) ≤ a` (YES) or
`λmin(Hpin) ≥ b` (NO). -/
noncomputable def pinnedPromise (k p c : ℕ)
    (H : (x : PinnedInstance) → Matrix (Fin x.base.n → Fin 2) (Fin x.base.n → Fin 2) ℂ) :
    PromiseProblem PinnedInstance where
  yes := {x | x.Valid k p c ∧ lamMin (x.compress p (H x)) ≤ (x.base.a.value : ℝ)}
  no := {x | x.Valid k p c ∧ (x.base.b.value : ℝ) ≤ lamMin (x.compress p (H x))}
  disjoint := by
    rw [Set.disjoint_left]
    rintro x ⟨hv, hle⟩ ⟨-, hge⟩
    exact absurd (hge.trans hle) (not_le.mpr hv.1.2.2.lt)

/-- `p`-Pinned `SIH_k` with fixed interaction `h` (Definition 35; Definition 37 when `h` is
stoquastic). -/
noncomputable def pinnedSihProblem (k p : ℕ) (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
    (c : ℕ) : PromiseProblem PinnedInstance :=
  pinnedPromise k p c (fun x => sihHam k h x.base)

/-- `p`-Pinned `DSIH_k` with family `h^(n)`, `n` the final system size (Definition 36;
Definition 38 when every `h^(n)` is stoquastic). -/
noncomputable def pinnedDsihProblem (k p : ℕ)
    (hfam : ℕ → Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ) (c : ℕ) :
    PromiseProblem PinnedInstance :=
  pinnedPromise k p c (fun x => sihHam k (hfam x.base.n) x.base)

end Supplement

end SingleInteraction


