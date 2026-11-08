-- Prove2me | Definitions.Def_SpencerEight_TransferData
-- name    : SpencerEight_TransferData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:53.824554+00:00
-- url     : https://prove2.me/theorems/839876d3-5d8a-4067-9774-2119509f56b9
-- title:
--   Hypotheses of Lemma 8.15 on $(\Gamma,\mathcal K)$
-- statement:
--   At parameters $(N,\kappa,\eta,w,b,C,(Q_j)_{j\in J})$, this says: $\Gamma\succeq0$ is an $m\times m$ matrix with $\operatorname{tr}\Gamma\le N\eta$; if $b\ne0$ then $\operatorname{rank}\Gamma\le wN$; $\mathcal K$ is Borel; $C\ge0$ and $Q_j\ge0$; and, with $\omega_j:=\operatorname{tr}[\Gamma(I+2\kappa\Gamma)^{-j}]/(N\eta)$,
--   $$-N^{-1}\log\nu(\mathcal K)\le C+\sum_{j\in J}Q_j\omega_j.$$
--
--   **Formalization Note** The last bound is written $e^{-N(C+\sum_jQ_j\omega_j)}\le\nu(\mathcal K)$. This is the same inequality for $N>0$, and it excludes $\nu(\mathcal K)=0$, which Lean's convention $\log0=0$ would otherwise admit.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.15, pp.78–79 (PDF pp.78–79)

import Mathlib
import Definitions.Def_SpencerEight_tiltedGamma
open MeasureTheory

namespace SpencerEight

/-- The data and hypotheses on `(Γ, K)` in Lemma 8.15 (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), pp.78–79 (PDF pp.78–79)) at parameters `(N, κ, η, w, b, C, Q_j)`: `Γ ⪰ 0`, `tr Γ ≤ Nη`, `rank Γ ≤ wN` (needed only when `b ≠ 0`: "When `b = 0` no rank condition is needed"), `K` Borel, `C, Q_j ≥ 0`, and `−N⁻¹ log ν(K) ≤ C + ∑_j Q_j ω_j`, with `ω_j := tr[Γ(I + 2κΓ)^{−j}]/(Nη)`. A separate predicate because the scaling clause of the lemma applies the same hypotheses at replaced parameters.

**Formalization Note** The bound on `ν(K)` is written `e^{−N(C + ∑ Q_j ω_j)} ≤ ν(K)`, the same inequality for `N > 0`. The logarithmic form would make `ν(K) = 0` pass, since `Real.log 0 = 0`. `J` is the finite set of exponents ("finitely many coefficients"). -/
def TransferData {m : ℕ} (N : ℕ) (κ η w b C : ℝ) (J : Finset ℕ) (Q : ℕ → ℝ)
    (Γ : Matrix (Fin m) (Fin m) ℝ) (K : Set (Fin m → ℝ)) : Prop :=
  Γ.PosSemidef ∧ Γ.trace ≤ N * η ∧ (b ≠ 0 → (Γ.rank : ℝ) ≤ w * N) ∧ MeasurableSet K ∧
  0 ≤ C ∧ (∀ j ∈ J, 0 ≤ Q j) ∧
  ENNReal.ofReal (Real.exp (-(N * (C + ∑ j ∈ J, Q j *
      ((Γ * ((1 + (2 * κ) • Γ)⁻¹) ^ j).trace / (N * η)))))) ≤ tiltedGamma κ Γ K

end SpencerEight


