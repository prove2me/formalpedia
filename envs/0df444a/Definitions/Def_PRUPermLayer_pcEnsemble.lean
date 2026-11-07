-- Prove2me | Definitions.Def_PRUPermLayer_pcEnsemble
-- name    : PRUPermLayer_pcEnsemble
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:48.821116+00:00
-- url     : https://prove2.me/theorems/717cc453-2bc6-48db-b555-c679b3420e1e
-- title:
--   Ensemble $PC$: random permutation after an independent randomizer $C \sim D$
-- statement:
--   Let $N = 2^n$ and let $D$ be a distribution on $U(N)$. The ensemble **$PC$** samples a uniformly random permutation $\sigma$ of $[N]$ and, independently, $C \sim D$, and returns the product $P_\sigma C$, which applies $C$ first. As a distribution on $U(N)$,
--   $$
--   PC = \frac{1}{N!}\sum_{\sigma \in S_N} \big(C \mapsto P_\sigma C\big)_{\#} D .
--   $$
--
--   **Formalization Note** The uniform choice of $\sigma$ is a finite average over the symmetric group, so no $\sigma$-algebra on permutations is needed. For a probability measure $D$ the result is a probability measure (checked in the sanity file).
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Lemma 3.1, p.12 (PDF p.14); §2.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_PRUPermLayer_permUnitary
open MeasureTheory
open scoped ENNReal

namespace PRUPermLayer

/-- The ensemble `PC`: the law of `P_σ C` with `σ` uniform on the symmetric group `S_N` and
`C ∼ D` independent of `σ` (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Lemma 3.1, p.12 (PDF p.14): "PC, with P a uniformly random
permutation and C ∼ D independent of P"; §2.2, p.9: "returns their product, which applies L
first"). As a measure, `(1/N!) Σ_σ (C ↦ P_σ C)_* D`.

**Formalization Note** The product is `permUnitary σ * C`: `P` on the left, so `C` is applied
first. The uniform average over the finite group `S_N` is written as a finite sum, which needs no
σ-algebra on permutations. For a probability measure `D` this is a probability measure (checked in
the sanity file). -/
noncomputable def pcEnsemble {n : ℕ} (D : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)) :
    Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :=
  (Fintype.card (Equiv.Perm (Fin (2 ^ n))) : ℝ≥0∞)⁻¹ •
    ∑ σ : Equiv.Perm (Fin (2 ^ n)), D.map (fun C => permUnitary σ * C)

end PRUPermLayer


