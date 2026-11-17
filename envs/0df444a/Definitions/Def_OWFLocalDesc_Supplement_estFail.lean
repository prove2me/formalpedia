-- Prove2me | Definitions.Def_OWFLocalDesc_Supplement_estFail
-- name    : OWFLocalDesc_Supplement_estFail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:42:19.143208+00:00
-- url     : https://prove2.me/theorems/58a60328-73af-4309-87be-9bb7c3c45197
-- title:
--   Failure probability of a deterministic tolerance-aware estimator on uniform data (Theorem 4.6)
-- statement:
--   Let $E$ be a deterministic map that receives $(1^n,x,y,d)$, with the tolerance $d$ in binary. Draw the dataset from $D_{0,n}$: $m(n)$ independent uniform $n$-bit points and $m(n)$ independent uniform labels, with repeated points kept. The **failure probability** of $E$ is
--   $$\Pr_{(X,Y)\sim D_{0,n}}\Big[E(1^n,X,Y,d)\notin\big[\mathrm{pSC}^{t(n)}_{\theta_1}(X,Y)-d,\ \mathrm{pSC}^{t(n)}_{\theta_2}(X,Y)+d\big]\Big].$$
--
--   A malformed output counts as a failure. Intervals are taken in $\mathbb Z\cup\{\infty\}$ with $\infty\pm d=\infty$, using the published `OWFLocalDesc.InInterval` and `OWFLocalDesc.decodeOut`.
--
--   **Formalization Note** The probability is the number of failing datasets divided by $2^{m(n)n+m(n)}$. The input is the published `OWFLocalDesc.datasetCode` (which carries $1^n$) followed by `Nat.bits d`.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem 4.6, p.22

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_pSC
import Definitions.Def_OWFLocalDesc_decodeOut
import Definitions.Def_OWFLocalDesc_InInterval
import Definitions.Def_OWFLocalDesc_intervalSucc
set_option autoImplicit false

namespace OWFLocalDesc.Supplement

open OWFLocalDesc

/-- The input `(1ⁿ, x, y, d)` of a tolerance-aware estimator: the code of the dataset (published
`OWFLocalDesc.datasetCode`, which carries `1ⁿ`) followed by the tolerance `d` in binary. -/
def tolInput {m n : ℕ} (x : Fin m → Fin n → Bool) (y : Fin m → Bool) (d : ℕ) : List Bool :=
  QuantumPRC.tupleCode [datasetCode x y, Nat.bits d]

/-- **Failure probability of a deterministic estimator on `D_{0,n}` (Theorem 4.6).** Myrisiotis,
*One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission (held manuscript,
sha256 d818fa43…4c4e), Theorem 4.6, p.22: "its probability of failing to return a value in
[pSC^t_{θ1}(X,Y) − d(n), pSC^t_{θ2}(X,Y) + d(n)] on independent uniform points and labels".

`estFail U E t m θ₁ θ₂ d n` is the fraction of datasets `(x, y)`, with `m(n)` points of `n` bits
and `m(n)` labels, on which the output of the deterministic map `E` on `(1ⁿ, x, y, d)` is
malformed or lies outside `[pSC^{t(n)}_{θ₁}(x,y) − d, pSC^{t(n)}_{θ₂}(x,y) + d]`.

**Formalization Note.** Uniform points and labels, repeated points kept (as the published
`OWFLocalDesc.succUniform`); outputs are read by `OWFLocalDesc.decodeOut` and the window is
`OWFLocalDesc.InInterval` (`∞ ± d = ∞`). The tolerance is passed in binary (`Nat.bits`). -/
noncomputable def estFail (U : Decoder) (E : List Bool → List Bool) (t m : ℕ → ℕ) (θ₁ θ₂ : ℝ)
    (d n : ℕ) : ℝ :=
  open Classical in
  ((Finset.univ.filter fun xy : (Fin (m n) → Fin n → Bool) × (Fin (m n) → Bool) =>
      ¬ ∃ o, decodeOut (E (tolInput xy.1 xy.2 d)) = some o ∧
        InInterval (pSC U (t n) θ₁ xy.1 xy.2) (pSC U (t n) θ₂ xy.1 xy.2) d o).card : ℝ) /
    (2 : ℝ) ^ (m n * n + m n)

end OWFLocalDesc.Supplement


