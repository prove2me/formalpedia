-- Prove2me | Definitions.Def_LockingAccInfo_conditionalEntropy
-- name    : LockingAccInfo_conditionalEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:02.795465+00:00
-- url     : https://prove2.me/theorems/b39108ac-3b3e-4ab4-a4cf-83964cecf239
-- title:
--   Conditional entropy $H(V|Z)$ of a label given a measurement outcome
-- statement:
--   Let $\rho_{VE}=\sum_vP_V(v)|v\rangle\langle v|\otimes\rho_{E|V=v}$ be a {cq}-state and $M=\{M_z\}_z$ a POVM on $E$ with outcome $Z$. The joint law of $(V,Z)$ is $P_{VZ}(v,z)=P_V(v)\operatorname{tr}(M_z\rho_{E|V=v})$, and
--
--   $$
--   H(V|Z):=H(VZ)-H(Z)
--   $$
--
--   is the entropy of $V$ conditioned on the outcome, in bits.
--
--   **Formalization Note** $M$ is the published finite `Measurement` (any number of outcomes) and the entropies are the published `shannon`. The joint law is the one in the published `accessibleInformation`, so $I(V;Z)=H(V)-H(V|Z)$ for the same measurement.
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, Lemma 5, p.4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

open QAlgorithms (effectProb)
open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, Lemma 5, p.4: "For some fixed POVM M
applied to E, let H(V|Z) be the entropy of V conditioned on the outcome Z", for a {cq}-state
ρVE = Σ_v PV(v)|v⟩⟨v| ⊗ ρE|V=v. The joint law of (V, Z) is
`P(v, z) = PV(v) · tr(Mz ρE|V=v)`, and `H(V|Z) = H(VZ) − H(Z)`.

**Formalization Note.** Entropies are the published `shannon` (bits, `0 log 0 = 0`); `M` is the
published finite POVM `Measurement` (any finite number of outcomes, indexed by `Fin M.outcomes`).
The joint law is the one used by the published `accessibleInformation`, so that
`I(V;Z) = H(V) − H(V|Z)` holds definitionally for the same measurement. -/
noncomputable def conditionalEntropy {V Q : Type} [Fintype V] [Fintype Q] [DecidableEq Q]
    (E : CQData V Q) (M : Measurement Q) : ℝ :=
  let joint : V × Fin M.outcomes → ℝ := fun z => E.prob z.1 * effectProb (M.effect z.2) (E.state z.1)
  shannon joint - shannon (fun z => ∑ v, joint (v, z))

end LockingAccInfo


