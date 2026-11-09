-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
-- name    : QMAPerfectCompleteness_Main_Cyclic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:37.398758+00:00
-- url     : https://prove2.me/theorems/21504e58-d64d-4ba1-aad8-b1925e857343
-- title:
--   The clock, $A=2E$, $\Gamma_z$, the cyclic operator $C_{z,\Gamma}$ and the history vector $|\Omega_z\rangle$ of (3)
-- statement:
--   Fix a verifier with $m$ proof qubits and acceptance operator $E$. Put $A=2E$. Let $\ell$ be the least integer with $\ell\ge 4(m+1)$ such that $\ell+1$ is a power of two. The clock register has basis $|0\rangle,\dots,|\ell\rangle$. For $z\in\{0,1\}^m$ put $\Gamma_z=\langle z|A^\ell|z\rangle$. For a real number $\Gamma$ define the **cyclic operator** and the **history vector** on clock $\otimes$ proof by
--
--   $$
--   C_{z,\Gamma}=\sum_{t=0}^{\ell-1}|t+1\rangle\langle t|\otimes A+|0\rangle\langle\ell|\otimes\Gamma^{-1}|z\rangle\langle z|,
--   \qquad
--   |\Omega_z\rangle=\sum_{t=0}^{\ell}|t\rangle\otimes A^t|z\rangle.
--   $$
--
--   For a verifier over $\mathcal G_2$, $g$ denotes its number of $H\otimes H$ gates, and later $h=2g$. These objects carry the cyclic consistency condition of the source: the closing transition $|\ell\rangle\to|0\rangle$ uses the exact number $\Gamma$. The history vector is not normalized, and $A$ is not a unitary time evolution.
--
--   **Formalization Note** The matrix $A^\ell$ is Hermitian, so its diagonal entry is real, and $\Gamma_z$ is stored as the real part of that entry. The norm on vectors is the Euclidean norm `euclidNorm`, not Mathlib's sup norm. The source's overview writes $\beta=\Gamma^{-1}$ on pp. 4–5; here, as in its §3, the parameter is $\Gamma$. The parameter $\Gamma$ is an arbitrary real; every statement that uses $C_{z,\Gamma}$ has $\Gamma\ge2$ or $\Gamma=a/b$ with $a,b>0$.
-- source:
--   Sabee Grewal, Dorian Rudolph, QMA has perfect completeness, STOC 2027 submission #490 (October 2026), §3.1–3.2, pp. 7–8, Eq. (3)

import Definitions.Def_QMAPerfectCompleteness_Main_Classes

open Matrix
open scoped Kronecker

/-!
# The clock, the numbers `Γ_z`, the cyclic operator and the history vector

Sabee Grewal, Dorian Rudolph, *QMA has perfect completeness*, STOC 2027 submission #490
(October 2026), §3.1–3.2, pp. 7–8, Eq. (3).
-/

namespace QMAPerfectCompleteness.Main

/-- The number `g` of `H ⊗ H` gates of a verifier over `𝒢₂` (position `3` of `gatesG2`). -/
def hhCount (V : Verifier gatesG2) : ℕ := V.gates.countP fun i => i.gate.val == 3

/-- The number of clock qubits, `log₂(ℓ + 1)`: the least `c` with `4(m + 1) + 1 ≤ 2^c`. -/
def clockQubits (m : ℕ) : ℕ := Nat.clog 2 (4 * (m + 1) + 1)

/-- `ℓ`, the least integer with `ℓ ≥ 4(m + 1)` such that `ℓ + 1` is a power of two (p. 7). -/
def ell (m : ℕ) : ℕ := 2 ^ clockQubits m - 1

/-- The clock basis `|0⟩, …, |ℓ⟩`. -/
abbrev Clock (m : ℕ) := Fin (ell m + 1)

/-- The history space `ℋ_C ⊗ ℋ_X`, as a basis. -/
abbrev History {G : GateSet} (V : Verifier G) := Clock V.proofQubits × V.Proof

/-- The Euclidean norm of a complex vector (not Mathlib's default sup norm on `ι → ℂ`). -/
noncomputable def euclidNorm {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖v i‖ ^ 2)

namespace Verifier

variable {G : GateSet} (V : Verifier G)

/-- `A = 2E` (p. 7). -/
noncomputable def doubled : Matrix V.Proof V.Proof ℂ := (2 : ℂ) • V.acceptanceOperator

/-- `Γ_z = ⟨z|A^ℓ|z⟩` (p. 7). `A^ℓ` is Hermitian, so this diagonal entry is real and taking the real
part only changes its type. -/
noncomputable def gamma (z : V.Proof) : ℝ := ((V.doubled ^ ell V.proofQubits) z z).re

/-- The cyclic operator of Eq. (3), for a real parameter `Γ`:
`C_{z,Γ} = ∑_{t=0}^{ℓ-1} |t+1⟩⟨t| ⊗ A + |0⟩⟨ℓ| ⊗ Γ⁻¹ |z⟩⟨z|`. -/
noncomputable def cyclicOp (z : V.Proof) (Γ : ℝ) : Matrix (History V) (History V) ℂ :=
  (∑ t : Fin (ell V.proofQubits), Matrix.single t.succ t.castSucc (1 : ℂ) ⊗ₖ V.doubled) +
    Matrix.single 0 (Fin.last (ell V.proofQubits)) (1 : ℂ) ⊗ₖ
      (((Γ⁻¹ : ℝ) : ℂ) • Matrix.single z z (1 : ℂ))

/-- The unnormalized history vector of Eq. (3): `|Ω_z⟩ = ∑_{t=0}^{ℓ} |t⟩ ⊗ A^t |z⟩`. -/
noncomputable def historyVector (z : V.Proof) : History V → ℂ :=
  fun x => (V.doubled ^ (x.1 : ℕ)) x.2 z

end Verifier

end QMAPerfectCompleteness.Main


