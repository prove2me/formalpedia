-- Prove2me | Definitions.Def_KAQROM_CQ
-- name    : KAQROM_CQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:59.140297+00:00
-- url     : https://prove2.me/theorems/6133c3cb-78ce-4cbc-b527-9322fd3db793
-- title:
--   Classical–quantum states, their trace distance $\tfrac12\|\rho-\sigma\|_1$ and tensor products
-- statement:
--   A **classical–quantum state** with classical register $C$ and quantum register $R$ is
--   $$
--   \rho_{CR}=\sum_{c}|c\rangle\langle c|_C\otimes\rho_c,
--   $$
--   stored by its positive semidefinite blocks $\rho_c=p(c)\,\sigma_{R|c}$, finitely many of them nonzero. Its trace norm is $\|\rho\|_1=\sum_c\|\rho_c\|_1$, and the **trace distance** of two such states is
--   $$
--   D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1=\tfrac12\sum_c\|\rho_c-\sigma_c\|_1 .
--   $$
--   The tensor product of $\rho_{CR}$ and $\sigma_{C'R'}$ has classical register $CC'$ and blocks $\rho_c\otimes\sigma_{c'}$. Partial traces over either factor of a matrix on $R\times R'$ are included.
--
--   These states carry the conditioned prefix views $\omega^{AB}_{m,h}$, $\omega^A_{m,h}$, $\omega^B_{m,h}$ and the states $\Omega_{m,h}$, $\tilde\Omega_{m,h}$ of §5.2.
--
--   **Formalization Note** A state is a finitely supported map from the classical alphabet to matrices, so the alphabet may be an infinite type such as the set of query transcripts. The trace norm of each block is the published `WildeQIT.traceNorm`, $\mathrm{Tr}\sqrt{M^\dagger M}$. For block-diagonal operators the sum of block trace norms is exactly the trace norm.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), §3.2, p.16

import Mathlib
import Definitions.Def_WildeQIT_traceNorm

namespace KAQROM

open Matrix
open scoped Kronecker

/-- A **classical–quantum state** `ρ_{CS} = ∑_c |c⟩⟨c|_C ⊗ ρ_c` with classical register `C` and
quantum register `R`, stored by its (unnormalized, positive semidefinite) blocks `ρ_c = p(c) σ_{S|c}`;
only finitely many blocks are nonzero (§3.2, p.16).

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), §3.2, p.16.

**Formalization Note.** A finitely supported map `C →₀ Matrix R R ℂ` lets the classical alphabet be
an infinite type such as `List (X × Y)` (query transcripts) while every state has finite support. -/
abbrev CQ (C R : Type) := C →₀ Matrix R R ℂ

/-- The trace norm `‖ρ‖₁` of a block-diagonal (classical–quantum) operator: the sum of the trace
norms of its blocks. -/
noncomputable def cqTraceNorm {C R : Type} [Fintype R] [DecidableEq R] (ρ : CQ C R) : ℝ :=
  ρ.sum (fun _ A => WildeQIT.traceNorm A)

/-- The **trace distance** `D(ρ,σ) = ½‖ρ − σ‖₁` of two classical–quantum states with the same
classical register (§3.2, p.16). On states classical on `C` this is exactly the trace distance of
the block-diagonal operators. -/
noncomputable def cqTraceDist {C R : Type} [Fintype R] [DecidableEq R] (ρ σ : CQ C R) : ℝ :=
  (1 / 2 : ℝ) * cqTraceNorm (ρ - σ)

/-- The tensor product `ρ ⊗ σ` of two classical–quantum states: classical register `C × C'`,
quantum register `R × R'`, block `ρ_c ⊗ σ_{c'}` (Kronecker product). -/
noncomputable def cqProd {C C' R R' : Type} (ρ : CQ C R) (σ : CQ C' R') : CQ (C × C') (R × R') :=
  ρ.sum (fun c A => σ.sum (fun c' B => Finsupp.single (c, c') (A ⊗ₖ B)))

/-- The partial trace over the second factor of a matrix on `R × R'`. -/
def ptraceRight {R R' : Type} [Fintype R'] (M : Matrix (R × R') (R × R') ℂ) : Matrix R R ℂ :=
  fun a a' => ∑ b, M (a, b) (a', b)

/-- The partial trace over the first factor of a matrix on `R × R'`. -/
def ptraceLeft {R R' : Type} [Fintype R] (M : Matrix (R × R') (R × R') ℂ) : Matrix R' R' ℂ :=
  fun b b' => ∑ a, M (a, b) (a, b')

end KAQROM


