-- Prove2me | Definitions.Def_GeoQAC_Supplement_outProb
-- name    : GeoQAC_Supplement_outProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:17:45.893826+00:00
-- url     : https://prove2.me/theorems/ec420fc1-a7e2-41b2-95ca-f5d94dd8f5d9
-- title:
--   Output probabilities with an arbitrary ancilla state
-- statement:
--   Let $C$ be a circuit whose $n$ input qubits sit at given positions, every other qubit being an ancilla. Let $\sigma$ be a **density matrix** (positive semidefinite, trace one) on the ancillas, possibly mixed or entangled, independent of the input. On input $x$ the circuit starts in $\rho_x=|x\rangle\langle x|\otimes\sigma$, and measuring a designated output qubit after $C$ gives the bit $g_C(x)$ with
--   $$
--   \Pr[g_C(x)=b]=\sum_{y:\,y_{\mathrm{out}}=b}\big(C\rho_xC^\dagger\big)_{y,y}.
--   $$
--   The **average success** for $f$ is $\Pr_{x,C}[g_C(x)=f(x)]=2^{-n}\sum_x\Pr[g_C(x)=f(x)]$.
--
--   This is the setting of the one-dimensional lower bounds (Theorems 3.22 and 3.23).
--
--   **Formalization Note** The diagonal of a density matrix is real; the definition takes real parts.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), §3.7, p.28; Definition 2.4, p.11; §2.2, p.9

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit

namespace GeoQAC.Supplement

open GeoQAC Matrix
open scoped ComplexOrder

/-!
# Output probabilities with an arbitrary (mixed or entangled) ancilla state

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), §3.7, p.28: "the `n` classical input qubits
may occupy arbitrary positions on the line, with any finite number of ancillas in an
input-independent state, possibly mixed or entangled. We measure one designated output qubit and
write `g_C(x)` for the resulting bit." Definition 2.4, p.11: "Average-case success averages over
uniform `x` as well as the measurement outcome." §2.2, p.9: "A state `ρ` is a positive semidefinite
operator of trace one."

**Formalization Note.**
* The inputs sit at an injective placement `inp`; every other qubit is an ancilla. The ancilla state
  `σ` is any density matrix on the configurations of the non-input qubits (`AncQ inp`), independent
  of `x`.
* The initial state is `ρ_x = |x⟩⟨x| ⊗ σ`; its entry at `(y, y')` is `σ(y|_anc, y'|_anc)` when `y`
  and `y'` both carry `x` on the inputs, and `0` otherwise.
* `outProb C inp σ out x b = Pr[g_C(x) = b] = Σ_{y : y_out = b} (C ρ_x C†)(y, y)` (real part; the
  diagonal of a density matrix is real).
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The non-input qubits. -/
abbrev AncQ {n : ℕ} (inp : Fin n ↪ V) : Type := {v : V // ∀ i, inp i ≠ v}

/-- A density matrix: positive semidefinite with trace one (§2.2, p.9). -/
def IsDensityMatrix {ι : Type} [Fintype ι] (σ : Matrix ι ι ℂ) : Prop :=
  σ.PosSemidef ∧ σ.trace = 1

/-- The initial state `ρ_x = |x⟩⟨x| ⊗ σ` (§3.7, p.28). -/
def initRho {n : ℕ} (inp : Fin n ↪ V) (σ : Matrix (AncQ inp → Bool) (AncQ inp → Bool) ℂ)
    (x : Fin n → Bool) : Matrix (V → Bool) (V → Bool) ℂ :=
  Matrix.of fun y y' =>
    if (∀ i, y (inp i) = x i) ∧ (∀ i, y' (inp i) = x i) then
      σ (fun a => y a.1) (fun a => y' a.1)
    else 0

/-- `Pr[g_C(x) = b]`: the probability that measuring `out` after `C` on `ρ_x` gives `b`. -/
noncomputable def outProb {d n : ℕ} (C : QACCircuit V d) (inp : Fin n ↪ V)
    (σ : Matrix (AncQ inp → Bool) (AncQ inp → Bool) ℂ) (out : V) (x : Fin n → Bool) (b : Bool) :
    ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y : V → Bool => y out = b),
    ((C.matrix * initRho inp σ x * C.matrixᴴ) y y).re

/-- `Pr_{x,C}[g_C(x) = f(x)]`: the success probability averaged over uniform `x` and the
measurement (Definition 2.4, p.11). -/
noncomputable def avgSuccess {d n : ℕ} (C : QACCircuit V d) (inp : Fin n ↪ V)
    (σ : Matrix (AncQ inp → Bool) (AncQ inp → Bool) ℂ) (out : V) (f : (Fin n → Bool) → Bool) : ℝ :=
  (∑ x, outProb C inp σ out x (f x)) / 2 ^ n

end GeoQAC.Supplement


