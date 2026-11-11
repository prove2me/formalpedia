-- Prove2me | Definitions.Def_RQCMoments_IsStrongDesign
-- name    : RQCMoments_IsStrongDesign
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:10:38.945207+00:00
-- url     : https://prove2.me/theorems/1527f409-8b6f-4fa2-b3ed-e63969435b52
-- title:
--   Strong $\varepsilon$-approximate unitary $(p,q)$-design (relative error)
-- statement:
--   Let $\nu$ be a probability distribution on $U(N)$, $p,q\ge 0$ integers and $\varepsilon\in\mathbb R$. Then $\nu$ is a **strong $\varepsilon$-approximate unitary $(p,q)$-design** (with relative error) if
--   $$
--   (1-\varepsilon)\,\Delta^{(p,q)}_{\mathrm{Haar}}\ \le\ \Delta^{(p,q)}_\nu\ \le\ (1+\varepsilon)\,\Delta^{(p,q)}_{\mathrm{Haar}},
--   $$
--   where for linear maps $\mathcal A\le\mathcal B$ means that $\mathcal B-\mathcal A$ is **completely positive**: for every ancilla dimension $r$, $\mathrm{id}_r\otimes(\mathcal B-\mathcal A)$ maps positive semidefinite matrices to positive semidefinite matrices.
--
--   By Remark 2.3, an "$\varepsilon$-approximate unitary $k$-design" in the paper's own statements (Theorems 3.2 and 4.9) is a strong $\varepsilon$-approximate $(k,k)$-design in this sense.
--
--   Here $U(N)$ is the compact group of $N\times N$ unitary matrices and $\mathrm{Haar}$ its Haar probability measure.
--
--   **Formalization Note** $U(N)$ is the subtype `Matrix.unitaryGroup (Fin N) ℂ` with the Borel $\sigma$-algebra of its subspace topology, and $\mathrm{Haar}$ is the published `QAlgorithms.Schur.unitaryHaar N` (Haar measure normalized to mass one on the whole compact group). Complete positivity is the published `LiuHelsenDesigns.OneD.CompletelyPositive` (positivity of the amplification $\mathrm{id}_r\otimes\Phi$ for every $r$), i.e. the literal CP order, not the Choi-matrix order. No sign condition is placed on $\varepsilon$.
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Definition 2.2, (12); Remark 2.3, pp.13–14 (PDF pp.15–16)

import Mathlib
import Definitions.Def_RQCMoments_twirlPQ
import Definitions.Def_LiuHelsenDesigns_OneD_designs

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

/-- **Definition 2.2** (strong ε-approximate unitary (p,q)-design)
(Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Definition 2.2, (12), p.13; Remark 2.3, p.14).
A probability distribution `ν` on `U(N)` is a strong `ε`-approximate unitary `(p,q)`-design
(with relative error) if `(1 − ε) Δ^{(p,q)}_{Haar} ≤ Δ^{(p,q)}_ν ≤ (1 + ε) Δ^{(p,q)}_{Haar}`,
where `𝒜 ≤ ℬ` means that `ℬ − 𝒜` is completely positive.

**Formalization Note** Complete positivity is the published
`LiuHelsenDesigns.OneD.CompletelyPositive`: `id_r ⊗ Φ` maps positive semidefinite matrices to
positive semidefinite matrices for every ancilla dimension `r`. This is the literal CP order,
not the Choi-matrix order (their equivalence is the content of Lemma 3.1). `ε` is any real
number; no sign condition is imposed. `U(N)` is the subtype `Matrix.unitaryGroup (Fin N) ℂ` with
the Borel σ-algebra of its subspace topology, and Haar is the published
`QAlgorithms.Schur.unitaryHaar N` (Haar measure normalized to mass one on the compact group). By Remark 2.3, the paper's "ε-approximate unitary
k-design" is `IsStrongDesign ν k k ε`. -/
def IsStrongDesign {N : ℕ} (ν : Measure (Matrix.unitaryGroup (Fin N) ℂ)) (p q : ℕ) (ε : ℝ) : Prop :=
  IsProbabilityMeasure ν ∧
  LiuHelsenDesigns.OneD.CompletelyPositive
    (fun X => twirlPQ ν p q X - ((1 - ε : ℝ) : ℂ) • twirlPQ (QAlgorithms.Schur.unitaryHaar N) p q X) ∧
  LiuHelsenDesigns.OneD.CompletelyPositive
    (fun X => ((1 + ε : ℝ) : ℂ) • twirlPQ (QAlgorithms.Schur.unitaryHaar N) p q X - twirlPQ ν p q X)

end RQCMoments


