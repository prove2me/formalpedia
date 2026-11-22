-- Prove2me | Definitions.Def_PreservePast_Supplement_gaussPopData
-- name    : PreservePast_Supplement_gaussPopData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:31:07.027389+00:00
-- url     : https://prove2.me/theorems/3b08d253-3b58-4e73-b40e-7c19f561968e
-- title:
--   The Gaussian population model: training data, test law, success, Bayes success, and the costs $C_{m sing}$, $C_{m exc}$, $C_{m tot}$
-- statement:
--   In the **Gaussian population model** there are $n$ independent centres $\Theta_j\sim N(0,I_d)$ and labelled data $D=((A_i,X_i))_{i=1}^n$, where the $A_i$ are i.i.d. uniform on $[n]$ and $X_i=\sqrt\rho\,\Theta_{A_i}+\sqrt{1-\rho}\,E_i$ with independent standard Gaussian noises $E_i$, independent of the labels. A fresh uniform test label $a$ generates its query $\sqrt\rho\,\Theta_a+\sqrt{1-\rho}\,E_0$ by the same model. The learner (a retained-state protocol) observes the labelled data but not the centres and predicts the test label from the query.
--
--   This defines the learner's **success**, the **full-training-data Bayes success** $S^\ast_n$, and the costs, in bits,
--   $$C_{\rm sing}=I(X_S;M\mid\Theta,R),\qquad C_{\rm exc}=I(D;M\mid\Theta,R),\qquad C_{\rm tot}=I(D;M\mid R),$$
--   where $X_S$ is the singleton list (`singList`).
--
--   **Formalization Note** The latent variable is $(\Theta,A,E)$ with the product of standard Gaussian laws and the uniform law on label sequences; $n\ge1$ is the instance `NeZero n`.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), §K.3, p.58 (PDF p.60)

import Mathlib
import Definitions.Def_PreservePast_Supplement_gaussShift
import Definitions.Def_PreservePast_Supplement_singList

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace PreservePast.Supplement

/-- The latent variable `(Θ, A, E)` of the Gaussian population model: the `n` centres
`Θ_j ∈ ℝ^d`, the `n` training labels `A_i ∈ [n]` and the `n` noise vectors `E_i ∈ ℝ^d`. -/
abbrev GaussPopLatent (n d : ℕ) : Type :=
  (Fin n → Fin d → ℝ) × (Fin n → Fin n) × (Fin n → Fin d → ℝ)

/-- The law of the latent variable: independent standard Gaussian centres and noises and
independent uniform labels. -/
noncomputable def gaussPopLaw (n d : ℕ) [NeZero n] : Measure (GaussPopLatent n d) :=
  (Measure.pi fun _ : Fin n => stdGauss d).prod
    ((Measure.pi fun _ : Fin n => (PMF.uniformOfFintype (Fin n)).toMeasure).prod
      (Measure.pi fun _ : Fin n => stdGauss d))

instance (n d : ℕ) [NeZero n] : IsProbabilityMeasure (gaussPopLaw n d) := by
  unfold gaussPopLaw; infer_instance

/-- **The labelled training data of the Gaussian population model.** P. Xu, *Information Required
to Preserve Past Learning*, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §K.3,
p.58 (PDF p.60): "Take n independent centers Θ_j ∼ N(0, I_d) and labeled data
D = ((A_i, X_i))_{i=1}^n, where the A_i are iid uniform on [n] and
X_i = √ρ Θ_{A_i} + √(1−ρ) E_i. All centers and noises are independent standard Gaussians,
independent of the labels." -/
noncomputable def gaussPopData {n d : ℕ} (ρ : ℝ) (l : GaussPopLatent n d) :
    Fin n → Fin n × (Fin d → ℝ) :=
  fun i => (l.2.1 i, fun c => Real.sqrt ρ * l.1 (l.2.1 i) c + Real.sqrt (1 - ρ) * l.2.2 i c)

/-- The **test law** given the latent variable: "A fresh uniform test label generates its query
by the same model" (§K.3, p.58): the label `a` is uniform on `[n]` and the query is
`√ρ Θ_a + √(1−ρ) E₀` with a fresh standard Gaussian `E₀`. The joint law of (query, label). -/
noncomputable def gaussPopTest {n d : ℕ} (ρ : ℝ) (l : GaussPopLatent n d) :
    Measure ((Fin d → ℝ) × Fin n) :=
  ∑ a : Fin n, ((n : ENNReal))⁻¹ • (gaussShift d (Real.sqrt ρ) (1 - ρ) (l.1 a)).map (fun z => (z, a))

/-- The **success** of a learner in the Gaussian population model ("the learner observes the
training labels but not the centers"). -/
noncomputable def gaussPopSuccess {n d : ℕ} [NeZero n]
    (π : StateProtocol (Fin n → Fin n × (Fin d → ℝ)) (Fin d → ℝ) (Fin n)) (ρ : ℝ) : ℝ :=
  π.success (gaussPopLaw n d) (gaussPopData ρ) (gaussPopTest ρ)

/-- The **full-training-data Bayes success** `S*_n` (Theorem 16, p.58). -/
noncomputable def gaussPopOptimum (n d : ℕ) [NeZero n] (ρ : ℝ) : ℝ :=
  fullDataOptimum (Out := Fin n) (gaussPopLaw n d) (gaussPopData ρ) (gaussPopTest ρ)

/-- `C_sing = I(X_S; M | Θ, R)` in bits (§K.3, p.58), `X_S` the singleton list `singList`. -/
noncomputable def gaussPopSing {n d : ℕ} [NeZero n]
    (π : StateProtocol (Fin n → Fin n × (Fin d → ℝ)) (Fin d → ℝ) (Fin n)) (ρ : ℝ) : ENNReal :=
  π.info (gaussPopLaw n d) (gaussPopData ρ) (fun l => singList (gaussPopData ρ l)) (fun l => l.1)

/-- `C_exc = I(D; M | Θ, R)` in bits (§K.3, p.58). -/
noncomputable def gaussPopExc {n d : ℕ} [NeZero n]
    (π : StateProtocol (Fin n → Fin n × (Fin d → ℝ)) (Fin d → ℝ) (Fin n)) (ρ : ℝ) : ENNReal :=
  π.info (gaussPopLaw n d) (gaussPopData ρ) (gaussPopData ρ) (fun l => l.1)

/-- `C_tot = I(D; M | R)` in bits (§K.3, p.58). -/
noncomputable def gaussPopTot {n d : ℕ} [NeZero n]
    (π : StateProtocol (Fin n → Fin n × (Fin d → ℝ)) (Fin d → ℝ) (Fin n)) (ρ : ℝ) : ENNReal :=
  π.info (gaussPopLaw n d) (gaussPopData ρ) (gaussPopData ρ) (fun _ => ())

end PreservePast.Supplement


