-- Prove2me | Definitions.Def_QPSpinProfile_maxEnergy
-- name    : QPSpinProfile_maxEnergy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:58.136824+00:00
-- url     : https://prove2.me/theorems/f773462c-44c1-4ebb-9794-56f982edf4a5
-- title:
--   Energies $E_{n,p}(\mathcal C_n)$, $\lambda_{\max}(H_{n,p})$ and the gaps $\Delta^{\mathrm{opt}}$, $\Delta^{\mathrm{ref}}$
-- statement:
--   At a disorder realization $g$, the **energy** of an $n$-qubit state $\rho$ is $\operatorname{Tr}(H_{n,p}\rho)$. For a class $\mathcal C_n$,
--   $$
--   E_{n,p}(\mathcal C_n)=\sup_{\rho\in\mathcal C_n}\operatorname{Tr}(H_{n,p}\rho),\qquad \lambda_{\max}(H_{n,p})=\sup_{\rho}\operatorname{Tr}(H_{n,p}\rho),
--   $$
--   the second supremum running over all $n$-qubit states (it equals the largest eigenvalue). For a reference class $\mathcal B_n$,
--   $$
--   \Delta^{\mathrm{opt}}_{n,p}(\mathcal C_n)=\lambda_{\max}(H_{n,p})-E_{n,p}(\mathcal C_n),\qquad \Delta^{\mathrm{ref}}_{n,p}(\mathcal C_n;\mathcal B_n)=\big[E_{n,p}(\mathcal C_n)-E_{n,p}(\mathcal B_n)\big]_+ ,
--   $$
--   with $[x]_+=\max\{x,0\}$ (displays (1) and (2)). The first measures how far the best energy in the class stays below the unrestricted maximum, the second how much it exceeds the benchmark.
--
--   **Formalization Note** $E_{n,p}$ is a real supremum; every statement using it assumes the class is nonempty and consists of states (the paper's standing assumption), so the supremum is of a nonempty bounded set. Traces are real for states; real parts are taken.
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), §1.2, p.3–4 (PDF p.6–7), displays (1), (2)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QPSpinProfile_hamiltonian

namespace QPSpinProfile

open Matrix

/-- The energy `Tr(H_{n,p} ρ)` of an `n`-qubit operator `ρ` at disorder `g` (arXiv:2610.02166,
held version sha256 a0a1ec89…, §1.2, p.3, PDF p.6). Real part taken (the trace is real for a
state). -/
noncomputable def energy {n p : ℕ} (ρ : Matrix (Qubits n) (Qubits n) ℂ)
    (g : PauliString n p → ℝ) : ℝ :=
  (Matrix.trace (hamiltonian n p g * ρ)).re

/-- The maximal energy `E_{n,p}(C_n) := sup_{ρ ∈ C_n} Tr(H_{n,p} ρ)` of a class (arXiv:2610.02166,
§1.2, p.3, PDF p.6).

**Formalization Note** A real `sSup`; every statement using it assumes the class is nonempty and
consists of states (the paper's standing assumption, p.3), so the set is nonempty and bounded by
`‖H_{n,p}‖_op`. -/
noncomputable def maxEnergy (n p : ℕ) (C : Set (Matrix (Qubits n) (Qubits n) ℂ))
    (g : PauliString n p → ℝ) : ℝ :=
  sSup ((fun ρ => energy ρ g) '' C)

/-- The unrestricted maximal energy `λ_max(H_{n,p}) := sup_ρ Tr(H_{n,p} ρ)` over all `n`-qubit
states (arXiv:2610.02166, §1.2, p.4, PDF p.7). -/
noncomputable def lambdaMax (n p : ℕ) (g : PauliString n p → ℝ) : ℝ :=
  sSup {e | ∃ ρ : Matrix (Qubits n) (Qubits n) ℂ, WildeQIT.IsDensityOperator ρ ∧ energy ρ g = e}

/-- The ground-state gap `Δ^opt_{n,p}(C_n) := λ_max(H_{n,p}) − E_{n,p}(C_n)`, display (1)
(arXiv:2610.02166, §1.2, p.4, PDF p.7). -/
noncomputable def deltaOpt (n p : ℕ) (C : Set (Matrix (Qubits n) (Qubits n) ℂ))
    (g : PauliString n p → ℝ) : ℝ :=
  lambdaMax n p g - maxEnergy n p C g

/-- The benchmark advantage `Δ^ref_{n,p}(C_n; B_n) := [E_{n,p}(C_n) − E_{n,p}(B_n)]_+`, display (2)
(arXiv:2610.02166, §1.2, p.4, PDF p.7), with `[x]_+ = max{x, 0}`. -/
noncomputable def deltaRef (n p : ℕ) (C B : Set (Matrix (Qubits n) (Qubits n) ℂ))
    (g : PauliString n p → ℝ) : ℝ :=
  max (maxEnergy n p C g - maxEnergy n p B g) 0

end QPSpinProfile


