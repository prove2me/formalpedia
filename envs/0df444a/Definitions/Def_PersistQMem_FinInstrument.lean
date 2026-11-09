-- Prove2me | Definitions.Def_PersistQMem_FinInstrument
-- name    : PersistQMem_FinInstrument
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:37:45.623737+00:00
-- url     : https://prove2.me/theorems/088994e1-31b0-4a4d-9bad-50665190ac3d
-- title:
--   Complete finite instruments with Kraus refinement, recorded channels $N_\rho$ and their adjoints
-- statement:
--   A **complete refined instrument** (§6.2, (21)) with entering memory $\mathbb C^r$, source copy $\mathbb C^D$ and memory bound $K$ is a finite outcome set and, for each outcome $a$, a Kraus operator
--   $$M_a:\mathbb C^r\otimes\mathbb C^D\to\mathbb C^{k_a},\qquad k_a\le K,\qquad \sum_aM_a^*M_a=I_{rD}.$$
--   It acts as the block-diagonal recorded channel $\Phi(Z)=\bigoplus_aM_aZM_a^*$. A **recorded test** is a block-diagonal operator $X=\bigoplus_aX_a$ with $X_a$ on $\mathbb C^{k_a}$.
--
--   For a source state $\rho$ the recorded channel is $N_\rho(A)=\Phi(A\otimes\rho)$ (so $N_0=N_\tau$ and $N_{j,z}=N_{\rho_{j,z}}$, (22)), and its adjoint, defined by $\operatorname{Tr}[XN_\rho(A)]=\operatorname{Tr}[N_\rho^*(X)A]$, is
--   $$N_\rho^*(X)=\operatorname{Tr}_D\Big[\Big(\sum_aM_a^*X_aM_a\Big)(I_r\otimes\rho)\Big].$$
--   A **Hermitian contraction** is a Hermitian $H$ with $-I\preceq H\preceq I$; a recorded Hermitian contraction is one blockwise.
--
--   Every finite instrument can be refined to this form by recording its Kraus index as an extra classical outcome (p.19), which leaves the memory dimension unchanged.
--
--   **Formalization Note** Outcomes form a finite type; $\mathbb C^r\otimes\mathbb C^D$ is indexed by `Fin r × Fin D` (memory left, source right, Kronecker product `⊗ₖ`); the partial trace is the published `WildeQIT.partialTraceRight`. $A\preceq B$ means $B-A$ is positive semidefinite.
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), §5.2, p.14 (PDF p.17); §6.2, (21)–(22), p.19 (PDF p.22); (44), p.23 (PDF p.26)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_PersistQMem_ProfileData

open scoped Matrix ComplexOrder Kronecker

namespace PersistQMem

/-- A **Hermitian contraction** `−I ⪯ H ⪯ I` (Tao, Shen, *Structural Lower Bounds for Quantum
Property Estimation with Persistent Memory*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 6d48ad24…, §5.1, p.13: "A Hermitian contraction satisfies −I ⪯ G ⪯ I").

**Formalization Note.** `A ⪯ B` is `(B − A).PosSemidef`. -/
def IsHermContraction {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) : Prop :=
  H.IsHermitian ∧ (1 - H).PosSemidef ∧ (1 + H).PosSemidef

/-- **A complete finite-outcome instrument with Kraus refinement, (21), p.19.** The entering
memory is `C^r`, the source copy `C^D`; outcome `a` carries one Kraus operator
`M_a : C^r ⊗ C^D → C^{k_a}` with output block dimension `k_a ≤ K`, and completeness
`Σ_a M_a* M_a = I_{rD}` holds (Tao, Shen, STOC 2027 submission, manuscript of 2026-11-03,
sha256 6d48ad24…, §6.2, (21), p.19).

**Formalization Note.** Outcomes form a finite type `ι`. The paper refines every instrument so that
each outcome carries one Kraus operator ("including a classical Kraus index", p.19); this
structure is that refined form. `C^r ⊗ C^D` is indexed by `Fin r × Fin D`: memory is the left
Kronecker factor, the source the right one, throughout. -/
structure FinInstrument (ι : Type) [Fintype ι] (r D K : ℕ) where
  /-- output block dimension `k_a` -/
  k : ι → ℕ
  k_le : ∀ a, k a ≤ K
  /-- Kraus operator `M_a` of outcome `a` -/
  M : (a : ι) → Matrix (Fin (k a)) (Fin r × Fin D) ℂ
  complete : ∑ a, (M a)ᴴ * M a = 1

variable {ι : Type} [Fintype ι] {r D K : ℕ}

/-- A **recorded test** (or recorded operator) `X = ⊕_a X_a`, block diagonal over the outcomes of
`Φ`, with block `X_a` on `C^{k_a}` (§6.2, p.19). -/
abbrev RecTest (Φ : FinInstrument ι r D K) : Type :=
  (a : ι) → Matrix (Fin (Φ.k a)) (Fin (Φ.k a)) ℂ

/-- The recorded channel `N_ρ(A) = Φ(A ⊗ ρ) = ⊕_a M_a (A ⊗ ρ) M_a*` of (22), p.19
(`N_0 = N_τ`, `N_{j,z} = N_{ρ_{j,z}}`). -/
def recChannel (Φ : FinInstrument ι r D K) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ) : RecTest Φ :=
  fun a => Φ.M a * (A ⊗ₖ ρ) * (Φ.M a)ᴴ

/-- The adjoint `N_ρ^*(X) = Tr_D[(Σ_a M_a* X_a M_a)(I_r ⊗ ρ)]` of the recorded channel, defined by
the trace duality `Tr[X N_ρ(A)] = Tr[N_ρ^*(X) A]` (§5.2, p.14; (22), p.19). -/
noncomputable def recAdjoint (Φ : FinInstrument ι r D K) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (X : RecTest Φ) : Matrix (Fin r) (Fin r) ℂ :=
  WildeQIT.partialTraceRight
    ((∑ a, (Φ.M a)ᴴ * X a * Φ.M a) * ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ ρ))

/-- The trace pairing `Tr(Y X) = Σ_a Tr(Y_a X_a)` of two recorded operators. -/
def recTrace (Φ : FinInstrument ι r D K) (Y X : RecTest Φ) : ℂ :=
  ∑ a, (Y a * X a).trace

/-- A **recorded Hermitian contraction** `H = ⊕_a H_a`: every block is a Hermitian contraction
((44), p.23). -/
def IsRecHermContraction (Φ : FinInstrument ι r D K) (H : RecTest Φ) : Prop :=
  ∀ a, IsHermContraction (H a)

end PersistQMem


