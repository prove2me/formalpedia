-- Prove2me | Definitions.Def_PRUPermLayer_eta
-- name    : PRUPermLayer_eta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:29:06.421803+00:00
-- url     : https://prove2.me/theorems/c15962c9-f154-473d-bbad-d3c4a451dca5
-- title:
--   DNP failure $\eta_t(D)$
-- statement:
--   For a distribution $D$ on $U(N)$, $N = 2^n$, and $t \ge 1$, the **DNP failure** is the operator norm of an expectation,
--   $$
--   \eta_t(D) = \Big\| \mathop{\mathbb E}_{C\sim D} (C^\dagger)^{\otimes t}\,(I - \Pi_{\mathrm{DNP}})\,C^{\otimes t} \Big\| ,
--   $$
--   with $\Pi_{\mathrm{DNP}}$ the projector onto $\mathrm{DNP}_{N,t}$. It is the largest expected probability, over $t$-register states $\rho$, that $C^{\otimes t}\rho\,(C^\dagger)^{\otimes t}$ is found outside $\mathrm{DNP}_{N,t}$.
--
--   By the compilation lemma (Lemma 3.1), the adaptive security of $PC$ depends on $D$ only through $\eta_t(D)$.
--
--   **Formalization Note** The expectation of the operator is taken entry by entry (each entry is a bounded continuous function of $C$); $\|\cdot\|$ is the spectral norm. The norm is outside the expectation, as printed.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.2, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_PRUPermLayer_projMat
import Definitions.Def_PRUPermLayer_dnpSub
open MeasureTheory

namespace PRUPermLayer

/-- The DNP failure `η_t(D) = ‖E_{C∼D} (C†)^{⊗t} (I − Π_DNP) C^{⊗t}‖` of a distribution `D` on
`U(N)`, `N = 2ⁿ` (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.2, p.10 (PDF p.12)): the operator norm of an expectation, not
the expectation of a norm.

**Formalization Note** The expectation of the matrix is taken entrywise (each entry is a bounded
continuous function of `C`, so integrable for a probability measure); `‖·‖` is the operator norm
`QAlgorithms.specNorm`; `C^{⊗t}` is the published `tensorPow`. -/
noncomputable def eta (n t : ℕ) (D : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)) : ℝ :=
  QAlgorithms.specNorm (Matrix.of fun x y =>
    ∫ C, (ShadowTomography.UpperBound.tensorPow (star (C : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) t *
      (1 - projMat (dnpSub (2 ^ n) t)) *
      ShadowTomography.UpperBound.tensorPow (C : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) t :
        Matrix (Fin t → Fin (2 ^ n)) (Fin t → Fin (2 ^ n)) ℂ) x y ∂D)

end PRUPermLayer


