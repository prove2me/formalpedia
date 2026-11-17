-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_DLamInput
-- name    : TwoFoldOPI_Supplement_DLamInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:58:44.327011+00:00
-- url     : https://prove2.me/theorems/a3110d28-f807-4e37-bfec-a26bffbc05ca
-- title:
--   The public data of an oracle instance from $\mathcal D_\lambda$
-- statement:
--   With $\ell=\lfloor\log_2\lambda\rfloor$, $q=2^{2\ell}$, $M=q-1$, $s=2^{\ell}+1$, $n=2^{\ell}$, $m=M/s$ and $k=\lfloor\rho M\rfloor$, an instance of $\mathcal D_\lambda$ consists of the public description of $C_\lambda=\mathrm{RS}_{\mathbb F_q,\gamma,k}$, the partition $S_1,\dots,S_R$ of $[n]$ and the membership circuits, together with oracle access to $H_1,\dots,H_m:\mathbb F_q^s\to[n]$.
--
--   This input type holds the public data: $\lambda$, the explicit field, the generator $\gamma$ and the class of each symbol of $[n]$. The size parameter is $\lambda$.
--
--   **Formalization Note** The membership circuits are produced by the fixed public program of admissibility and are not stored; the partition is stored because $\lfloor\alpha_rn\rfloor$ need not be computable from real $\alpha_r$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11, Definitions 11.1–11.2, p. 57

import Mathlib
import Definitions.Def_TwoFoldOPI_elemBits

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms

/-- **The public part of an oracle-represented instance from `D_λ`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11, Definition 11.1, p.57: "Let q = 2^{2⌊log λ⌋}, M = q − 1, s = 2^{⌊log λ⌋} + 1,
n = 2^{⌊log λ⌋}, k = ⌊ρM⌋ for a constant rate parameter ρ ∈ (0, 1), and let γ be an arbitrary
generator of F_q^*. We define C_λ = RS_{F_q,γ,k} ⊆ F_q^M"; Definition 11.2, p.57: "The
corresponding oracle-represented code-intersection instance consists of the public descriptions of
C_λ, the partition, and the truncated-load membership circuits from Definition 10.2, together with
quantum oracle access to the H_i's."

The public data: the security parameter `λ`, the explicit field `F` and the generator `γ` (which
with `λ` and the fixed rate describe `C_λ`), and the partition of `[n] = {0, …, n−1}`,
`n = 2^{⌊log₂ λ⌋}`, as the class map `part : [n] → [R]`. `encode` writes `λ` in self-delimiting
binary, the field (`fieldEncode`), `γ` (`elemBits`) and the classes `part 0, …, part (n−1)` in
self-delimiting binary; `scale = λ`.

**Formalization Note.** The membership circuits are not stored: for admissible load data they are
produced from `m` by one fixed public polynomial-time program (Definition 10.9), which a uniform
algorithm for the fixed load data can run itself. The partition is stored because `⌊α_r n⌋` need
not be computable from real `α_r`. The oracles `H_i` are not part of the input. The module holds
the input type with its encoding and size. -/
structure DLamInput (R : ℕ) where
  /-- The security parameter. -/
  lam : ℕ
  /-- The field. -/
  F : AvgCaseTI.FieldPres
  /-- The generator of the multiplicative group. -/
  γ : F.F
  /-- The class of each symbol of `[n]`. -/
  part : Fin (2 ^ Nat.log 2 lam) → Fin R

/-- The bit encoding of the public data. -/
noncomputable def DLamInput.encode {R : ℕ} (x : DLamInput R) : List Bool :=
  LocalHamiltonian.encBin x.lam ++ fieldEncode x.F ++ List.ofFn (elemBits x.F x.γ) ++
    (List.ofFn fun a => LocalHamiltonian.encBin (x.part a).val).flatten

/-- The size parameter `λ`. -/
def DLamInput.scale {R : ℕ} (x : DLamInput R) : ℕ := x.lam

end Supplement

end TwoFoldOPI


