-- Prove2me | Definitions.Def_QNatProofs_IsAmplitudeOracle
-- name    : QNatProofs_IsAmplitudeOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:03:23.800208+00:00
-- url     : https://prove2.me/theorems/926df92a-f9ea-4fdc-952b-97794836e6fa
-- title:
--   Amplitude oracles, $|\hat v\rangle$, oracle templates with a fixed call count, and the loader repetition count
-- statement:
--   Let $v=(v_x)_{x\in\{0,1\}^n}$ with $v_x=r_xe^{2\pi i\theta_x}$, where $r_x,\theta_x\in\{0,1\}^q$ are $q$-bit binary fractions, and let $|\hat v\rangle=\frac1{\|v\|}\sum_xv_x|x\rangle$.
--
--   A unitary $U_v$ is an **amplitude oracle** for $v$ (Definition 4.1) if for every $x$,
--   $$
--   U_v|x\rangle|0\rangle=|x\rangle|r_x\rangle|\theta_x\rangle|\mathrm{junk}_x\rangle .
--   $$
--
--   To count oracle calls, an **oracle template** is a circuit with black-box steps. A template makes **exactly $t$ calls each** if it contains exactly $t$ uncontrolled calls to $U$, exactly $t$ to $U^\dagger$, and no other calls. A circuit $C$ **implements** a template with an oracle circuit $U$ if $C$ has the same unitary as the template with every call replaced by $U$ (or $U^\dagger$), and at most as many gates as that substitution.
--
--   $t=\lceil\gamma^{-2}\ln(1/\delta_{\mathrm{load}})\rceil$ is the number of parallel trials of the amplitude loader (§4.2.2).
--
--   These encode "uses one call each to $U_v$ and $U_v^\dagger$" and "$t$ parallel calls each" in Lemmas 4.5 and 4.6.
--
--   **Formalization Note** The wires of an amplitude oracle are $x$ ($n$ wires), $r_x$ ($q$), $\theta_x$ ($q$), then the workspace. The template is a published `QAlgorithms.OracleCircuit`; its elementary gates do not depend on the oracle.
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Definition 4.1, p.25–26; Lemma 4.5, p.26; §4.2.2, p.28; Lemma 4.6, p.30

import Mathlib
import Definitions.Def_QNatProofs_MHLevel
import Definitions.Def_QNatProofs_psiState

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms

/-- The amplitudes `v_x = r_x e^{2πiθ_x}` given by `q`-bit binary fractions `r_x, θ_x`. -/
noncomputable def ampOf {n q : ℕ} (rb θb : Qubits n → Fin q → Bool) : Qubits n → ℂ :=
  fun x => polarVal (rb x, θb x)

/-- The normalized state `|v̂⟩ = (1/‖v‖) Σ_x v_x |x⟩` (Definition 4.1, p.26). -/
noncomputable def vHat {n : ℕ} (v : Qubits n → ℂ) : EuclideanSpace ℂ (Qubits n) :=
  ((‖ampVec v‖ : ℂ))⁻¹ • ampVec v

/-- **Amplitude oracle** (Li, Parham, arXiv:2610.06826 (held copy sha256 b604fa11…),
Definition 4.1, p.25): `U_v |x⟩|0⟩ = |x⟩|r_x⟩|θ_x⟩|junk_x⟩` for every basis input `x`, where
`v_x = r_x e^{2πiθ_x}` and `r_x, θ_x ∈ {0,1}^q` are `q`-bit binary fractions; `junk_x` is a state of
the `j` workspace wires.

**Formalization Note** Wires: `x` on the first `n`, then `r_x` (`q` wires), `θ_x` (`q` wires), and
the workspace (`j` wires). The bits are most significant first. -/
def IsAmplitudeOracle {n q j : ℕ} (U : Matrix (Qubits (n + (q + q + j))) (Qubits (n + (q + q + j))) ℂ)
    (rb θb : Qubits n → Fin q → Bool) : Prop :=
  IsNoncleanEval (r := q + q) (w := j) U fun x => Fin.append (rb x) (θb x)

/-- Whether an oracle-circuit step is an uncontrolled call to the (single) oracle, plain
(`adj = false`) or inverse (`adj = true`). -/
def OracleStep.isCall {S : Set Gate} {a : Fin 1 → ℕ} {m : ℕ} (adj : Bool) :
    OracleStep S a m → Bool
  | .gate _ => false
  | .query _ adj' ctrl _ _ => (adj' == adj) && ctrl.isNone

/-- The number of uncontrolled calls to `U` (`adj = false`) or to `U†` (`adj = true`). -/
def callCount {S : Set Gate} {a : Fin 1 → ℕ} {m : ℕ} (T : OracleCircuit S a m) (adj : Bool) : ℕ :=
  T.countP (OracleStep.isCall adj)

/-- An **oracle template** making exactly `t` calls to `U` and `t` calls to `U†`, none of them
controlled, besides its elementary gates. -/
def IsCallTemplate {S : Set Gate} {a : Fin 1 → ℕ} {m : ℕ} (T : OracleCircuit S a m) (t : ℕ) :
    Prop :=
  callCount T false = t ∧ callCount T true = t ∧ T.queryCount 0 = 2 * t

/-- The circuit `C` **implements the template `T` with the oracle circuit `U`**: `C` has the same
unitary as `T` with every call replaced by `U` (or `U†`), and `C` has at most as many gates as that
substitution (the template's gates plus `size U` per call). -/
def ImplementsTemplate {m nU : ℕ} (C : Circuit allGates m)
    (T : OracleCircuit allGates (fun _ : Fin 1 => nU) m) (U : Circuit allGates nU) : Prop :=
  C.unitary = T.unitary (fun _ => U.unitary) ∧ C.size ≤ T.gateCount + T.queryCount 0 * U.size

/-- The number of parallel trials `t = ⌈γ^{-2} ln(1/δ_load)⌉` of the amplitude loader (Li, Parham,
arXiv:2610.06826 (held copy sha256 b604fa11…), §4.2.2, p.28; Lemma 4.6, p.30; Corollary 4.6.1
proof, p.33). -/
noncomputable def loadReps (γ δ : ℝ) : ℕ :=
  ⌈(γ ^ 2)⁻¹ * Real.log (1 / δ)⌉₊

end QNatProofs


