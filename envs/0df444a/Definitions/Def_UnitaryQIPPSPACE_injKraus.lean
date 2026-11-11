-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_injKraus
-- name    : UnitaryQIPPSPACE_injKraus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:30:35.675506+00:00
-- url     : https://prove2.me/theorems/67753f31-0b5c-4995-a331-caf4623b5937
-- title:
--   The phase-state injection procedure
-- statement:
--   Let $g:\{0,1\}^m\to\{0,1\}$ and let $Q$ be an $m$-qubit register holding $|\psi\rangle$. With $g_0:=g$, for each $j=1,\dots,m$: prepare a fresh $m$-qubit register $B_j$ in $|\varphi_{g_{j-1}}\rangle$; apply CNOT from the $k$-th qubit of $Q$ to the $k$-th qubit of $B_j$ for every $k$; measure $B_j$, record $a_j\in\{0,1\}^m$, discard $B_j$; set $g_j:=\Delta_{a_j}g_{j-1}$. After $m$ rounds, output $Q$.
--
--   The operator by which the procedure acts on $Q$ on the outcomes $a_1,\dots,a_j$ is the ordered product of the rounds' operators $(I_Q\otimes\langle a_i|)\,\mathrm{CNOT}^{\otimes m}\,(I_Q\otimes|\varphi_{g_{i-1}}\rangle)$, the first round rightmost.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), §4.3, phase-state injection procedure, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_boolPhaseGate

open Matrix

namespace UnitaryQIPPSPACE

/-- The layer `CNOT^{⊗m}` on `Q ⊗ B` (`m` qubits each) "from the `k`-th qubit of `Q` to the `k`-th
qubit of `B` for every `k ∈ [m]`": `|x⟩_Q |z⟩_B ↦ |x⟩_Q |z ⊕ x⟩_B`. -/
def cnotLayer (m : ℕ) : Matrix (Bits m × Bits m) (Bits m × Bits m) ℂ :=
  fun x' x => if x'.1 = x.1 ∧ x'.2 = Bits.xor x.2 x.1 then 1 else 0

/-- One round of the injection procedure with resource `|φ_f⟩` and outcome `a`, as an operator on
`Q`: `(I_Q ⊗ ⟨a|_B) CNOT^{⊗m} (I_Q ⊗ |φ_f⟩_B)`. -/
noncomputable def injStep {m : ℕ} (f : Bits m → Bool) (a : Bits m) : Matrix (Bits m) (Bits m) ℂ :=
  Matrix.of fun x' x => ∑ z : Bits m, cnotLayer m (x', a) (x, z) * boolPhaseState f z

/-- **The phase-state injection procedure** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, p. 28 (PDF p. 30)): "Let `g : {0,1}^m → {0,1}` be a
Boolean function, and let `Q` be an `m`-qubit register containing an arbitrary input state `|ψ⟩`.
Let `g₀ := g`. For each `j = 1, …, m`, perform the following steps:
1. Prepare a fresh `m`-qubit auxiliary register `B_j` in the state `|φ_{g_{j−1}}⟩`.
2. Apply CNOT from the `k`-th qubit of `Q` to the `k`-th qubit of `B_j` for every `k ∈ [m]`.
3. Measure `B_j` in the computational basis, record the outcome `a_j ∈ {0,1}^m`, and discard `B_j`.
Define `g_j := Δ_{a_j} g_{j−1}`. After `m` rounds, output register `Q`."

`injKraus g [a₁, …, a_j]` is the operator by which the procedure acts on `Q` on the outcomes
`a₁, …, a_j` (the Kraus operator of that branch): the ordered product of the rounds' operators
`injStep g_{i−1} a_i`, the first round rightmost, where `g_{i−1}` is determined by the earlier
outcomes. -/
noncomputable def injKraus {m : ℕ} (g : Bits m → Bool) (as : List (Bits m)) :
    Matrix (Bits m) (Bits m) ℂ :=
  (as.foldl (fun (st : Matrix (Bits m) (Bits m) ℂ × (Bits m → Bool)) a =>
    (injStep st.2 a * st.1, bdelta a st.2)) (1, g)).1

end UnitaryQIPPSPACE


