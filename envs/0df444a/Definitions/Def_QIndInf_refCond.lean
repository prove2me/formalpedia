-- Prove2me | Definitions.Def_QIndInf_refCond
-- name    : QIndInf_refCond
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:29:01.634845+00:00
-- url     : https://prove2.me/theorems/3cbc490d-854e-4acf-8f0e-08b3ce2ca9df
-- title:
--   Conditioned reference states $\mu_{\le i|h<i}$ and $\mu_{<i|h<i}$
-- statement:
--   For a reference family $\mu$ (in the proof, the reference state of the source model), instruments $\mathcal I_1,\dots,\mathcal I_i$ and a history $h_{<i}$, step 2 of the algorithm defines
--
--   $$
--   \mu_{\le i|h<i}=\frac{(\mathcal A_{h<i}\otimes\mathcal M_{\mathcal I_i})(\mu_{\le i})}{\mathrm{Tr}\big[(\mathcal A_{h<i}\otimes\mathcal M_{\mathcal I_i})(\mu_{\le i})\big]}\qquad\text{(Eq. (59))},
--   $$
--
--   a state on $(R_1,\dots,R_i,X_i)$, and step 3 defines $\mu_{<i|h<i}=\mathcal N_i(\mu_{\le i|h<i})$ with $\mathcal N_i=\mathrm{Tr}_{R_iX_i}$ (Eq. (60)).
--
--   These are the reference states from which the learner builds its recovery map $\mathcal R_{\mu_{\le i|h<i},\mathcal N_i}$.
--
--   **Formalization Note** Same index order as the target: (past registers) × (next register × outcome). $\mathcal N_i$ is the published `WildeQIT.partialTraceRight`. The normalization is the trace of the unnormalized operator, as printed; the result is the zero matrix when that trace vanishes.
-- source:
--   Hiroka, Hsieh, Shirakawa, arXiv:2609.36912 (PDF of 2026-11-02), §4.2, algorithm steps 2–3, Eqs. (59)–(60), p.20

import Mathlib
import Definitions.Def_QIndInf_target
import Definitions.Def_WildeQIT_partialTrace

set_option autoImplicit false

namespace QIndInf

open QAlgorithms QAlgorithms.CopyMeasurements

/-- **History-conditioned reference state `μ_{≤i|h<i}`** (Eq. (59)): for a reference family `μ`,
`(A_{h<i} ⊗ M_{I_i})(μ_{≤i}) / Tr[(A_{h<i} ⊗ M_{I_i})(μ_{≤i})]`, a state on `(R₁, …, R_i, X_i)`.

arXiv:2609.36912 (PDF of 2026-11-02), §4.2, step 2 of the algorithm, Eq. (59), p.20.

**Formalization Note.** Same index order as `target`: `(R₁ … R_{i−1}) × (R_i × X_i)`. The
normalization is the trace of the unnormalized operator, as printed; it is the zero matrix when
that trace vanishes (`0⁻¹ = 0`). -/
noncomputable def refCond {n j : ℕ} (μ : (m : ℕ) → Matrix (Regs n m) (Regs n m) ℂ)
    {k : Fin (j + 1) → ℕ} (I : (l : Fin (j + 1)) → QuantumInstrument (Reg n) (Fin (k l)))
    (x : (l : Fin j) → Fin (k l.castSucc)) :
    Matrix (Regs n j × (Reg n × Fin (k (Fin.last j))))
      (Regs n j × (Reg n × Fin (k (Fin.last j)))) ℂ :=
  let Y := measNext (I (Fin.last j))
    (superopTensorId (histOp (pastInstr I) x) (splitLast (μ (j + 1))))
  ((Y.trace.re : ℂ))⁻¹ • Y

/-- **`μ_{<i|h<i}`** (Eq. (60)): `N_i(μ_{≤i|h<i})` with `N_i = Tr_{R_i X_i}` the partial trace
discarding the `i`-th register and its outcome.

arXiv:2609.36912 (PDF of 2026-11-02), §4.2, step 3 of the algorithm, Eq. (60), p.20.

**Formalization Note.** `N_i` is the published `WildeQIT.partialTraceRight` over the factor
`R_i × X_i`. -/
noncomputable def refPast {n j : ℕ} (μ : (m : ℕ) → Matrix (Regs n m) (Regs n m) ℂ)
    {k : Fin (j + 1) → ℕ} (I : (l : Fin (j + 1)) → QuantumInstrument (Reg n) (Fin (k l)))
    (x : (l : Fin j) → Fin (k l.castSucc)) : Matrix (Regs n j) (Regs n j) ℂ :=
  WildeQIT.partialTraceRight (refCond μ I x)

end QIndInf


