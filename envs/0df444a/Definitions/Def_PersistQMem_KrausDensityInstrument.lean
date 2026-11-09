-- Prove2me | Definitions.Def_PersistQMem_KrausDensityInstrument
-- name    : PersistQMem_KrausDensityInstrument
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:47:10.641881+00:00
-- url     : https://prove2.me/theorems/a4abe617-c2e6-4faa-9641-929768ad1647
-- title:
--   One measurable complete instrument in Kraus-density form, and its drift
-- statement:
--   A **measurable complete instrument in Kraus-density form** (§6.6, (68)) with entering memory $\mathbb C^r$, source $\mathbb C^D$ and retained memory $\mathbb C^K$ is a measure $\mu$ on a measurable record space and measurable Kraus fields $a\mapsto M_{a,l}:\mathbb C^r\otimes\mathbb C^D\to\mathbb C^K$ ($l$ in a finite index set) with
--   $$\int\sum_lM_{a,l}^*M_{a,l}\,d\mu(a)=I_{rD}.$$
--   The recorded channel is $N_\rho(A)(a)=\sum_lM_{a,l}(A\otimes\rho)M_{a,l}^*$ (a density in $a$), its adjoint on a recorded test field $H(a)$ is $N_\rho^*(H)=\int\operatorname{Tr}_D[(\sum_lM_{a,l}^*H(a)M_{a,l})(I_r\otimes\rho)]\,d\mu(a)$, and the one-step drift (44) becomes
--   $$d(A,H)=\operatorname{Tr}\big[Af_\alpha(N_\rho^*H)\big]-\int\operatorname{Tr}\big[N_0(A)(a)\,f_\alpha(H(a))\big]\,d\mu(a).$$
--
--   This is the form in which §6.6 states Proposition 6.5 for measurable instruments.
--
--   **Formalization Note** Matrix integrals are entrywise Bochner integrals; completeness asserts integrability of every entry. Every output block is $\mathbb C^K$.
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), §6.6, (68), p.27 (PDF p.30); (44), p.23 (PDF p.26)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_PersistQMem_ProfileData
import Definitions.Def_PersistQMem_drift

open scoped Matrix ComplexOrder Kronecker
open MeasureTheory

namespace PersistQMem

/-- **One measurable complete instrument in Kraus-density form (§6.6, (68), p.27).** Entering memory
`C^r`, source copy `C^D`, retained memory `C^K`, records in a measurable space `X` with reference
measure `μ`; outcome `a` carries the Kraus family `(M_{a,l})_{l ∈ L}`, entrywise measurable in `a`,
with completeness `∫ Σ_l M_{a,l}* M_{a,l} dμ(a) = I_{rD}` (entrywise, integrable) (Tao, Shen,
*Structural Lower Bounds for Quantum Property Estimation with Persistent Memory*, STOC 2027
submission, manuscript of 2026-11-03, sha256 6d48ad24…, §6.6, (68), p.27).

**Formalization Note.** Every output block is `C^K` ("embedded into C^K", p.27); `L` is a finite
Kraus index. -/
structure KrausDensityInstrument (X : Type) [MeasurableSpace X] (μ : Measure X) (L : Type)
    [Fintype L] (r D K : ℕ) where
  M : X → L → Matrix (Fin K) (Fin r × Fin D) ℂ
  measurable : ∀ l o c, Measurable fun a => M a l o c
  complete_integrable : ∀ c c' : Fin r × Fin D,
    Integrable (fun a => (∑ l, (M a l)ᴴ * M a l) c c') μ
  complete : ∀ c c' : Fin r × Fin D,
    ∫ a, (∑ l, (M a l)ᴴ * M a l) c c' ∂μ = (1 : Matrix (Fin r × Fin D) _ ℂ) c c'

variable {X : Type} [MeasurableSpace X] {μ : Measure X} {L : Type} [Fintype L] {r D K : ℕ}

/-- The recorded channel `N_ρ(A)(a) = Σ_l M_{a,l} (A ⊗ ρ) M_{a,l}*` (density with respect to `μ`). -/
noncomputable def densChannel (Φ : KrausDensityInstrument X μ L r D K)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (A : Matrix (Fin r) (Fin r) ℂ) (a : X) :
    Matrix (Fin K) (Fin K) ℂ :=
  ∑ l, Φ.M a l * (A ⊗ₖ ρ) * (Φ.M a l)ᴴ

/-- The adjoint `N_ρ^*(H) = ∫ Tr_D[(Σ_l M_{a,l}* H(a) M_{a,l})(I_r ⊗ ρ)] dμ(a)` on a recorded test
field `H : X → C^{K×K}` (entrywise Bochner integral). -/
noncomputable def densAdjoint (Φ : KrausDensityInstrument X μ L r D K)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (H : X → Matrix (Fin K) (Fin K) ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i i' => ∫ a, WildeQIT.partialTraceRight
    ((∑ l, (Φ.M a l)ᴴ * H a * Φ.M a l) * ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ ρ)) i i' ∂μ

/-- The one-step test drift (44) for a measurable instrument, with the sum over outcomes replaced
by the integral against `μ` (§6.6, p.27):
`d(A, H) = Tr[A f_α(N_ρ^* H)] − ∫ Tr[N_0(A)(a) f_α(H(a))] dμ(a)` (real parts). -/
noncomputable def densDrift (Φ : KrausDensityInstrument X μ L r D K) (α : ℝ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (A : Matrix (Fin r) (Fin r) ℂ)
    (H : X → Matrix (Fin K) (Fin K) ℂ) : ℝ :=
  (A * fAlpha α (densAdjoint Φ ρ H)).trace.re -
    ∫ a, (densChannel Φ (tau D) A a * fAlpha α (H a)).trace.re ∂μ

end PersistQMem


