-- Prove2me | Definitions.Def_QDSGibbs_Supplement_fermiInfluence
-- name    : QDSGibbs_Supplement_fermiInfluence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:26:57.865528+00:00
-- url     : https://prove2.me/theorems/c5a29f9f-315c-41eb-9281-cb04c0ca60f1
-- title:
--   Fermionic transport norm $\|\cdot\|_{W^F_1}$, fermionic influence $D^F_\Phi(j)$, fermionic DS constant, parity $\Theta$, even mixing time
-- statement:
--   On the Fock space of a finite $\Lambda$ with two modes per site:
--
--   1. The **fermionic transport norm** (7.7) of an even traceless Hermitian $X$: $$\|X\|_{W^F_1}=\frac12\inf\Bigl\{\sum_j\|X_j\|_1: X=\sum_jX_j,\ X_j=X_j^*\in\mathcal A^{\mathrm{ev}}_\Lambda,\ \operatorname{Tr}^F_jX_j=0\Bigr\},$$ with $\operatorname{Tr}^F_j$ the fermionic partial trace (7.4).
--   2. The **fermionic influence** (7.10) $D^F_\Phi(j)=\sup\{\|\Phi(X)\|_{W^F_1}: X=X^*\in\mathcal A^{\mathrm{ev}}_\Lambda,\ \operatorname{Tr}^F_jX=0,\ \|X\|_1=2\}$.
--   3. The **fermionic DS constant** (7.11) $\kappa=\min_j\sum_Ba_B[1-D^F_{\Phi_B}(j)]$.
--   4. The parity automorphism $\Theta(X)=P_\Lambda XP_\Lambda$, and the **even mixing time** $t^{\mathrm{even}}_{\mathrm{mix}}(L,\varepsilon)=\inf\{t\ge0:\sup_\rho\|e^{tL}(\rho)-\sigma\|_1\le\varepsilon\}$, the supremum over even states.
--
--   **Formalization Note** Decompositions are the published `FermiHubbardMix.IsTransportPlan`, and $\operatorname{Tr}^F_j$ is the published `FermiHubbardMix.ptr`. The norm and the influence take values in $[0,\infty]$ (no decomposition gives $\infty$). "$\kappa\ge x$" is recorded as $\sum_Ba_BD^F_{\Phi_B}(j)\le\sum_Ba_B-x$ for every site $j$ (`FermiKappaGe`).
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), (7.4) p.63, (7.7) p.64, (7.10) and (7.11) p.65, parity p.62, Theorem 1.1 p.6

import Mathlib
import Definitions.Def_FermiHubbardMix_w1
import Definitions.Def_QDSGibbs_IsChannel

open scoped Matrix ENNReal

namespace QDSGibbs.Supplement

/-- The **fermionic transport norm** (arXiv:2610.03578, held file sha256 ede55815…, (7.7), p.64;
[BMT26, Definition 12.17]): for even traceless Hermitian `X`,
`‖X‖_{W^F_1} = ½ inf { Σ_j ‖X_j‖₁ : X = Σ_j X_j, X_j = X_j^* ∈ 𝒜^ev_Λ, Tr^F_j X_j = 0 }`.

**Formalization Note** The admissible decompositions are the published
`FermiHubbardMix.IsTransportPlan` (Hermitian, even, zero fermionic reduction
`FermiHubbardMix.ptr ord {j}` at the own site). Valued in `ℝ≥0∞`: an `X` with no decomposition gets
`⊤`, never the junk `0` of a real infimum of the empty set. `‖·‖₁` is the base `traceNorm`. -/
noncomputable def fw1 {Λ : Type} [Fintype Λ] {M : ℕ} (ord : Λ × Fin 2 ≃ Fin M)
    (X : FermiHubbardMix.Op M) : ℝ≥0∞ :=
  ⨅ (Xs : Λ → FermiHubbardMix.Op M) (_ : FermiHubbardMix.IsTransportPlan ord X Xs),
    ENNReal.ofReal (1 / 2 * ∑ j, traceNorm (Xs j))

/-- The **fermionic influence** of a map `Φ` at site `j` (arXiv:2610.03578, (7.10), p.65):
`D^F_Φ(j) = sup { ‖Φ(X)‖_{W^F_1} : X = X^* ∈ 𝒜^ev_Λ, Tr^F_j X = 0, ‖X‖₁ = 2 }`.

**Formalization Note** `Tr^F_j X = 0` is `FermiHubbardMix.ptr ord {j} X = 0` (the published fermionic
partial trace, (7.4)); evenness is `FermiHubbardMix.IsEven`. Valued in `ℝ≥0∞`. -/
noncomputable def fermiInfluence {Λ : Type} [Fintype Λ] {M : ℕ} (ord : Λ × Fin 2 ≃ Fin M)
    (Φ : FermiHubbardMix.Op M → FermiHubbardMix.Op M) (j : Λ) : ℝ≥0∞ :=
  ⨆ (X : FermiHubbardMix.Op M)
    (_ : X.IsHermitian ∧ FermiHubbardMix.IsEven X ∧ FermiHubbardMix.ptr ord {j} X = 0 ∧
      traceNorm X = 2),
    fw1 ord (Φ X)

/-- The fermionic DS constant is at least `x` (arXiv:2610.03578, (7.11), p.65):
`κ := min_j Σ_B a_B [1 − D^F_{Φ_B}(j)] ≥ x`, for a finite family of labels `L` with channels `Φ_z`
and rates `a_z = a`.

**Formalization Note** Written without subtraction under the sum: for every site `j`,
`Σ_z a D^F_{Φ_z}(j) ≤ Σ_z a − x` in `ℝ≥0∞`. This is exactly the real inequality whenever
`Σ_z a − x ≥ 0`, which holds in every use (each site lies in `ℓ^D` cubes of rate `ℓ^{−D}`, so
`Σ_z a ≥ 1 ≥ x`). -/
def FermiKappaGe {Λ : Type} [Fintype Λ] {M : ℕ} {L : Type} (ord : Λ × Fin 2 ≃ Fin M)
    (labels : Finset L) (Φ : L → FermiHubbardMix.Op M → FermiHubbardMix.Op M) (a x : ℝ) : Prop :=
  ∀ j : Λ, ∑ z ∈ labels, ENNReal.ofReal a * fermiInfluence ord (Φ z) j ≤
    ENNReal.ofReal ((∑ _z ∈ labels, a) - x)

/-- The parity automorphism `Θ(X) = P_Λ X P_Λ` (arXiv:2610.03578, p.62), with the published
`FermiHubbardMix.parityOp`. -/
noncomputable def parityConj {M : ℕ} (X : FermiHubbardMix.Op M) : FermiHubbardMix.Op M :=
  FermiHubbardMix.parityOp M * X * FermiHubbardMix.parityOp M

/-- The **even mixing time** `t^even_mix(L, ε) = inf{t ≥ 0 : sup_ρ ‖e^{tL}(ρ) − σ‖₁ ≤ ε}`, the supremum
over even states `ρ` (`Θ(ρ) = ρ`) (arXiv:2610.03578, Theorem 1.1, p.6; (4.15), p.30).

**Formalization Note** `ℝ≥0∞`-valued (`inf ∅ = ⊤`); `e^{tL}` is the base `sexp`. -/
noncomputable def tmixEven {M : ℕ} (L : FermiHubbardMix.Op M → FermiHubbardMix.Op M)
    (σ : FermiHubbardMix.Op M) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ) (_ : 0 ≤ t ∧ ∀ ρ, IsState ρ → FermiHubbardMix.IsEven ρ →
      traceNorm (sexp L t ρ - σ) ≤ ε), ENNReal.ofReal t

end QDSGibbs.Supplement


