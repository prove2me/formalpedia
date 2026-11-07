-- Prove2me | Definitions.Def_GeoQAC_IsNekomataApprox
-- name    : GeoQAC_IsNekomataApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:49.678824+00:00
-- url     : https://prove2.me/theorems/dfa2d4ed-ec7d-4f26-a0a1-6f68c0d867c3
-- title:
--   Nekomata and $p$-approximate nekomata synthesis
-- statement:
--   An **$n$-nekomata** on a target register of $n$ qubits is a state
--   $$
--   |\nu\rangle=\frac{|0^n\rangle|\eta_0\rangle+|1^n\rangle|\eta_1\rangle}{\sqrt2},
--   $$
--   where $|\eta_0\rangle,|\eta_1\rangle$ are normalized states of the auxiliary register; when $\eta_0=\eta_1$ the target register is a cat state.
--
--   A circuit $C$ on $n+a$ qubits started at $|0^{n+a}\rangle$ **synthesizes a $p$-approximate $n$-nekomata** if its output has squared fidelity at least $p$ with some state of this form, including the auxiliary register:
--   $$
--   |\langle\nu|C|0^{n+a}\rangle|^2\ge p .
--   $$
--   Exact synthesis is $p=1$.
--
--   **Formalization Note** The $n$ targets are any injective placement and the auxiliary register is every other qubit. The nekomata vector is required to be a unit vector (automatic for $n\ge1$).
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), §2.4, p.12; Definition 2.6, p.11

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit
import Definitions.Def_DHRUniq_IsUnitVec

namespace GeoQAC

open DHRUniq (IsUnitVec)

open Matrix

/-!
# Nekomata and their approximate synthesis

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), §2.4, p.12: "An n-nekomata allows an
auxiliary state in each branch: |ν⟩ = (|0^n⟩|η_0⟩ + |1^n⟩|η_1⟩)/√2, where |η_0⟩ and |η_1⟩ are
normalized. … A p-approximate nekomata has squared fidelity at least p with some state of this
form, including the auxiliary register." Definition 2.6, p.11: the circuit acts on `n + a` qubits
initialized to `|0^{n+a}⟩`.

**Formalization Note.**
* The `n` targets are `tgt : Fin n ↪ V`, at any positions; the auxiliary register is every other
  qubit. `η_0, η_1` are unit vectors on the auxiliary configurations.
* `nekoVec tgt η₀ η₁` is `(|0^n⟩|η_0⟩ + |1^n⟩|η_1⟩)/√2`, and the nekomata is required to be a unit
  vector (automatic for `n ≥ 1`; it excludes the degenerate `n = 0` sums).
* `p`-approximate synthesis: `|⟨ν| C |0^{n+a}⟩|² ≥ p` for some nekomata `ν`. Exact synthesis is
  `p = 1`, which for unit vectors means `C|0^{n+a}⟩ = e^{iθ}|ν⟩`.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The nekomata vector `(|0^n⟩|η_0⟩ + |1^n⟩|η_1⟩)/√2` with targets `tgt`. -/
noncomputable def nekoVec {n : ℕ} (tgt : Fin n ↪ V)
    (η₀ η₁ : ({v : V // ∀ i, tgt i ≠ v} → Bool) → ℂ) : (V → Bool) → ℂ :=
  fun y => ((Real.sqrt 2)⁻¹ : ℂ) *
    ((if ∀ i, y (tgt i) = false then η₀ (fun v => y v) else 0) +
     (if ∀ i, y (tgt i) = true then η₁ (fun v => y v) else 0))

/-- `C` synthesizes a `p`-approximate `n`-nekomata on the targets `tgt` (§2.4, p.12;
Definition 2.6, p.11): some nekomata state `ν` has `|⟨ν| C |0…0⟩|² ≥ p`. -/
def IsNekomataApprox {d n : ℕ} (p : ℝ) (C : QACCircuit V d) (tgt : Fin n ↪ V) : Prop :=
  ∃ η₀ η₁ : ({v : V // ∀ i, tgt i ≠ v} → Bool) → ℂ,
    IsUnitVec η₀ ∧ IsUnitVec η₁ ∧ IsUnitVec (nekoVec tgt η₀ η₁) ∧
    p ≤ ‖∑ y, star (nekoVec tgt η₀ η₁ y) *
      (C.matrix *ᵥ basisVec (fun _ : V => false)) y‖ ^ 2

end GeoQAC


