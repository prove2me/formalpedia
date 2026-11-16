-- Prove2me | Definitions.Def_GeoQAC_Supplement_IsApproxCleanParity
-- name    : GeoQAC_Supplement_IsApproxCleanParity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:21:23.396232+00:00
-- url     : https://prove2.me/theorems/43078202-3866-40c7-a284-b7b66555367b
-- title:
--   $p$-approximate clean implementation of $U_f$
-- statement:
--   Let $C$ act on $n$ control qubits, an accumulator and ancillas in $|0\rangle$. $C$ is a **$p$-approximate clean implementation** of $U_f|x,b\rangle=|x,b\oplus f(x)\rangle$ if for every unit vector $|\phi\rangle$ on the controls and the accumulator
--   $$
--   \big|\big(\langle\phi|U_f^\dagger\otimes\langle0^a|\big)\,C\,|\phi,0^a\rangle\big|^2\ge p .
--   $$
--   This is a squared-fidelity guarantee on the entire output, ancillas included. For $f=\mathrm{PARITY}_n$ it is a $p$-approximate clean parity implementation.
--
--   It is the hypothesis of the exactification theorem B.1.
--
--   **Formalization Note** The logical qubits sit anywhere; the embedding of $\phi$ is built from the published `GeoQAC.load`.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Definition 2.5, p.11; §2.4, p.12

import Mathlib
import Definitions.Def_GeoQAC_IsCleanImpl
import Definitions.Def_DHRUniq_IsUnitVec

namespace GeoQAC.Supplement

open GeoQAC Matrix
open DHRUniq (IsUnitVec)

/-!
# `p`-approximate clean implementation of `U_f`

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), Definition 2.5, p.11: "A `p`-approximate
clean implementation satisfies `|⟨ϕ| U† ⊗ ⟨0^a| C |ϕ, 0^a⟩|² ≥ p` for every `|ϕ⟩`. This is a
squared-fidelity guarantee on the entire output, including the ancillary workspace." The coherent
version of `f` is `U_f|x, b⟩ = |x, b ⊕ f(x)⟩` (p.11).

**Formalization Note.**
* The logical qubits are the controls `ctrl : Fin n ↪ V` and the accumulator `acc ∉ ctrl`, at any
  positions; every other qubit is an ancilla in `|0⟩`. A logical vector `ϕ` is a function on
  `(Fin n → Bool) × Bool` (control string, accumulator bit) and every unit vector is quantified.
* `embedLogical ctrl acc ϕ = Σ_{x,b} ϕ(x,b) |x, b, 0^a⟩`, built from the published `GeoQAC.load`;
  `U_f|ϕ⟩` embedded is `Σ_{x,b} ϕ(x,b) |x, b ⊕ f(x), 0^a⟩`. The fidelity is
  `|⟨(U_f ϕ) ⊗ 0^a | C (ϕ ⊗ 0^a)⟩|²`.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `|ϕ, 0^a⟩ = Σ_{x,b} ϕ(x,b) |x, b, 0^a⟩`: the logical vector `ϕ` on the controls and the
accumulator, `|0⟩` on every ancilla. -/
noncomputable def embedLogical {n : ℕ} (ctrl : Fin n ↪ V) (acc : V)
    (ϕ : (Fin n → Bool) × Bool → ℂ) : (V → Bool) → ℂ :=
  ∑ xb : (Fin n → Bool) × Bool, ϕ xb • basisVec (load ctrl acc xb.1 xb.2)

/-- `(U_f|ϕ⟩) ⊗ |0^a⟩ = Σ_{x,b} ϕ(x,b) |x, b ⊕ f(x), 0^a⟩`. -/
noncomputable def embedLogicalApply {n : ℕ} (ctrl : Fin n ↪ V) (acc : V)
    (f : (Fin n → Bool) → Bool) (ϕ : (Fin n → Bool) × Bool → ℂ) : (V → Bool) → ℂ :=
  ∑ xb : (Fin n → Bool) × Bool, ϕ xb • basisVec (load ctrl acc xb.1 (xor xb.2 (f xb.1)))

/-- `C` is a `p`-approximate clean implementation of `U_f` with controls `ctrl` and accumulator
`acc` (Definition 2.5, p.11): for every logical unit vector `ϕ`,
`|⟨ϕ| U_f† ⊗ ⟨0^a| C |ϕ, 0^a⟩|² ≥ p`. -/
def IsApproxCleanImpl {d n : ℕ} (p : ℝ) (C : QACCircuit V d) (ctrl : Fin n ↪ V) (acc : V)
    (f : (Fin n → Bool) → Bool) : Prop :=
  (∀ i, ctrl i ≠ acc) ∧
  ∀ ϕ : (Fin n → Bool) × Bool → ℂ, IsUnitVec ϕ →
    p ≤ ‖∑ y, star (embedLogicalApply ctrl acc f ϕ y) *
          (C.matrix *ᵥ embedLogical ctrl acc ϕ) y‖ ^ 2

/-- A `p`-approximate clean implementation of the parity unitary `U_⊕n` (Definition 2.5, p.11;
§2.4, p.12). -/
def IsApproxCleanParity {d n : ℕ} (p : ℝ) (C : QACCircuit V d) (ctrl : Fin n ↪ V) (acc : V) :
    Prop :=
  IsApproxCleanImpl p C ctrl acc (parityFn n)

end GeoQAC.Supplement


