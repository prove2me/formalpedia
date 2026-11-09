-- Prove2me | Definitions.Def_WeldedPath_cpO
-- name    : WeldedPath_cpO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:00:54.701983+00:00
-- url     : https://prove2.me/theorems/2e8ebebb-1be4-4552-bd28-d583dc7c357f
-- title:
--   The compressed permutation oracle $\mathrm{cpO}_x$
-- statement:
--   Fix a queried value $x\in[s]$. For $x\notin\mathrm{Dom}(I)$ let
--   $$
--   |+_{x,I}\rangle=\frac{1}{\sqrt{s-|I|}}\sum_{y\in[s]\setminus\mathrm{Im}(I)}|I[x\to y]\rangle,\qquad \mathrm{pCF}(|\psi_1\rangle,|\psi_2\rangle)=1-|\psi_1\rangle\langle\psi_1|-|\psi_2\rangle\langle\psi_2|+|\psi_1\rangle\langle\psi_2|+|\psi_2\rangle\langle\psi_1| .
--   $$
--   The compression operator $\mathrm{pC}_x=\bigoplus_{I:x\notin\mathrm{Dom}(I)}\mathrm{pCF}(|+_{x,I}\rangle,|I\rangle)|_{\mathcal H_{x,I}}$ swaps the empty record with the uniform superposition of fresh records. The purified oracle $P$ maps $|y\rangle|I\rangle\mapsto|y\oplus I(x)\rangle|I\rangle$ when $x\in\mathrm{Dom}(I)$ and acts as the identity otherwise, and $F|I\rangle=|I^{-1}\rangle$ flips the database. The **compressed permutation query** is
--   $$
--   \mathrm{cpO}_x=\mathrm{pC}_x\,P\,\mathrm{pC}_x^\dagger \ (\text{forward}),\qquad F\,\mathrm{pC}_x\,P\,\mathrm{pC}_x^\dagger F^\dagger\ (\text{inverse}).
--   $$
--
--   **Formalization Note** The answer register is $\{0,1\}^d$ and a value $y\in[s]$ is written as the $d$-bit expansion of its 0-based index. The direct sum over the orthogonal blocks $\mathcal H_{x,I}$ is $1+\sum_I(\mathrm{pCF}(|+_{x,I}\rangle,|I\rangle)-1)$.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), §2.1, pp.10–11, (4)–(8)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_WeldedPath_InjDb

namespace WeldedPath

open InjDb

variable {s : ℕ}

/-- The `d`-bit string of `y ∈ [s]`, written into an answer register `{0,1}^d`.

**Formalization Note.** `y ∈ Fin s` is written as the `d`-bit binary expansion of its 0-based value
(`QAlgorithms.natToBits`, most significant bit first); statements assume `s ≤ 2^d`. Bitwise XOR
`⊕` is addition in `Fin d → Bool`. -/
def encode (d : ℕ) (y : Fin s) : QAlgorithms.Qubits d := QAlgorithms.natToBits d y.1

/-- `|+_{x,I}⟩ = (s − |I|)^{-1/2} Σ_{y ∈ [s] \ Im(I)} |I[x → y]⟩` for `x ∉ Dom(I)`
(Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, arXiv:2611.05912 (sha256 b31400a0…),
p.10). -/
noncomputable def plusState (I : InjDb s) (x : Fin s) : Hil (InjDb s) :=
  ((Real.sqrt ((s - I.size : ℕ) : ℝ))⁻¹ : ℂ) •
    ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), ket (I.addPair x y)

/-- The compression primitive `pCF(|ψ_1⟩, |ψ_2⟩) = 1 − |ψ_1⟩⟨ψ_1| − |ψ_2⟩⟨ψ_2| + |ψ_1⟩⟨ψ_2| +
|ψ_2⟩⟨ψ_1|` (arXiv:2611.05912 (sha256 b31400a0…), p.10). -/
noncomputable def pCF {X : Type*} [Fintype X] (ψ₁ ψ₂ : Hil X) : Hil X →L[ℂ] Hil X :=
  1 - ketBra ψ₁ ψ₁ - ketBra ψ₂ ψ₂ + ketBra ψ₁ ψ₂ + ketBra ψ₂ ψ₁

/-- The permutation compression operator `pC_x = ⨁_{I : x ∉ Dom(I)} pC_{x,I}` (6), with
`pC_{x,I} = pCF(|+_{x,I}⟩, |I⟩)|_{H_{x,I}}` (4)–(5) (arXiv:2611.05912 (sha256 b31400a0…), p.10).

**Formalization Note.** For fixed `x` the spaces `H_{x,I}` (`x ∉ Dom(I)`) form an orthogonal
decomposition of `H(I_s)`, and `pCF(|+_{x,I}⟩, |I⟩) − 1` is supported on `H_{x,I}`, so the direct sum
is `1 + Σ_I (pCF(|+_{x,I}⟩, |I⟩) − 1)`. -/
noncomputable def pC (s : ℕ) (x : Fin s) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  1 + ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I x = none),
    (pCF (plusState I x) (ket I) - 1)

/-- The extended purified oracle `P` for a fixed query `x` (arXiv:2611.05912 (sha256 b31400a0…),
p.11): `|y⟩_Y|I⟩_I ↦ |y ⊕ I(x)⟩_Y|I⟩_I` if `x ∈ Dom(I)`, the identity otherwise. -/
noncomputable def purifiedXor (d : ℕ) (x : Fin s) :
    Hil (QAlgorithms.Qubits d × InjDb s) →L[ℂ] Hil (QAlgorithms.Qubits d × InjDb s) :=
  basisMap fun p => match p.2 x with
    | some y => (p.1 + encode d y, p.2)
    | none => p

/-- The flip operator `F|I⟩ = |I^{-1}⟩` (arXiv:2611.05912 (sha256 b31400a0…), p.11). -/
noncomputable def flipDb (s : ℕ) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  basisMap fun I : InjDb s => I.symm

/-- The ordinary compressed permutation query `cpO_x` (8) (arXiv:2611.05912 (sha256 b31400a0…),
p.11), for a fixed queried value `x`, on the answer register `Y = {0,1}^d` and the database
register: `pC·P·pC†` for a forward query (`inv = false`) and `F·pC·P·pC†·F†` for an inverse query
(`inv = true`). -/
noncomputable def cpO (d : ℕ) (x : Fin s) (inv : Bool) :
    Hil (QAlgorithms.Qubits d × InjDb s) →L[ℂ] Hil (QAlgorithms.Qubits d × InjDb s) :=
  let pc : Hil (QAlgorithms.Qubits d × InjDb s) →L[ℂ] Hil (QAlgorithms.Qubits d × InjDb s) :=
    opTensor 1 (pC s x)
  let core := pc.comp ((purifiedXor d x).comp (ContinuousLinearMap.adjoint pc))
  let fl : Hil (QAlgorithms.Qubits d × InjDb s) →L[ℂ] Hil (QAlgorithms.Qubits d × InjDb s) :=
    opTensor 1 (flipDb s)
  if inv then fl.comp (core.comp (ContinuousLinearMap.adjoint fl)) else core

end WeldedPath


