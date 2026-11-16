-- Prove2me | Definitions.Def_GeoQAC_Supplement_targetFidelity
-- name    : GeoQAC_Supplement_targetFidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:17:27.292198+00:00
-- url     : https://prove2.me/theorems/481af261-bfb2-4537-a060-e9c7aca8533d
-- title:
--   Target-marginal squared fidelity of a synthesized state
-- statement:
--   Let a circuit $C$ act on qubits initialized to $|0\cdots0\rangle$, with $n$ of them designated as the **target register** $T$, and let $\rho_T$ be the reduced state of $C|0\cdots0\rangle$ on $T$. For a vector $|\varphi\rangle$ on $n$ qubits, the **target-marginal squared fidelity** is
--   $$
--   \langle\varphi|\rho_T|\varphi\rangle=\sum_{z}\Big|\big(\langle\varphi|\otimes\langle z|\big)\,C|0\cdots0\rangle\Big|^2 ,
--   $$
--   the sum running over the computational-basis configurations $z$ of the non-target qubits. The circuit synthesizes $|\varphi\rangle$ with squared fidelity at least $p$ if this is at least $p$, and exactly if it equals $1$.
--
--   This is the synthesis notion of Theorems 3.8 and 4.7; the remaining registers are unrestricted.
--
--   **Formalization Note** The targets sit at any injective placement; the partial trace is written out as the sum over non-target configurations.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Definition 2.6, p.11; §2.2, pp.9–10

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit

namespace GeoQAC.Supplement

open GeoQAC Matrix

/-!
# Target-marginal squared fidelity of a synthesized state

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), Definition 2.6, p.11: "Let `C` act on
`n + a` qubits initialized to `|0^{n+a}⟩`, and let `ρ_T` be its reduced output on an `n`-qubit target
register `T`. It synthesizes `|ψ⟩` with squared fidelity at least `p` if `⟨ψ|ρ_T|ψ⟩ ≥ p`. … Taking
`p = 1` gives exact synthesis." §2.2, p.9–10: `ρ_R = Tr_{R^c} ρ`; squared fidelity with a pure target
is `F(ρ, |ψ⟩⟨ψ|) = ⟨ψ|ρ|ψ⟩`.

**Formalization Note.**
* The targets sit at any injective placement `tgt : Fin n ↪ V`; the other qubits are ancillas.
  A target vector `φ` is a function on `Fin n → Bool` (target `i` carries bit `t i`).
* With `ψ = C|0…0⟩`, the partial trace is written out: for a configuration `z` of the non-target
  qubits, `Σ_t conj(φ t) ψ(t on the targets, z elsewhere)` is the amplitude of `⟨φ| ⊗ ⟨z|` on `ψ`, and
  `⟨φ|ρ_T|φ⟩ = Σ_z |⟨φ, z|ψ⟩|²`. No partial-trace machinery is needed.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The qubits that are not targets. -/
abbrev OffTarget {n : ℕ} (tgt : Fin n ↪ V) : Type := {v : V // ∀ i, tgt i ≠ v}

/-- The configuration with `t` on the targets and `z` on the other qubits. -/
noncomputable def joinTargets {n : ℕ} (tgt : Fin n ↪ V) (t : Fin n → Bool)
    (z : OffTarget tgt → Bool) : V → Bool :=
  fun v => if h : ∃ i, tgt i = v then t h.choose else z ⟨v, fun i hi => h ⟨i, hi⟩⟩

/-- The target-marginal squared fidelity `⟨φ|ρ_T|φ⟩` of the output `C|0^{n+a}⟩` of a circuit `C` on
the target register `tgt` (Definition 2.6, p.11), with `ρ_T = Tr_{T^c} C|0⟩⟨0|C†`. -/
noncomputable def targetFidelity {d n : ℕ} (C : QACCircuit V d) (tgt : Fin n ↪ V)
    (φ : (Fin n → Bool) → ℂ) : ℝ :=
  ∑ z : OffTarget tgt → Bool,
    ‖∑ t : Fin n → Bool,
        star (φ t) * (C.matrix *ᵥ basisVec (fun _ => false)) (joinTargets tgt t z)‖ ^ 2

end GeoQAC.Supplement


