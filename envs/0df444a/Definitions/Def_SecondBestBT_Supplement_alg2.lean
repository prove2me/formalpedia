-- Prove2me | Definitions.Def_SecondBestBT_Supplement_alg2
-- name    : SecondBestBT_Supplement_alg2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:38:51.120129+00:00
-- url     : https://prove2.me/theorems/de07d333-ea38-4459-9c48-55cab5592edf
-- title:
--   $\mathrm{ALG}_2(\omega;\mathbf r)$, the state transition
-- statement:
--   $\mathrm{ALG}_2(\omega;\mathbf r^{(1)})$ is the output of Algorithm 2 (line 13): either **fail**, or the terminal state
--   $$
--   \big(x(t_{|R|},|R|);\ R[t_{|R|}:]\big),\qquad R=\mathbf r^{(0)}\|\mathbf r^{(1)},
--   $$
--   the threshold allocation at the last buyer value together with the suffix of $R$ starting at the terminal threshold. The canonical execution on a ratio vector $\mathbf r=(r_1,\dots,r_k)$ is $\mathrm{ALG}_2(\omega_0;\mathbf r)$, with $R=(0,r_1,\dots,r_k)$, processing $b=2,\dots,k+1$.
--
--   ALG2 is the compressed form of the greedy construction (Algorithm 1) after a clear step (Lemma 5.1).
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 5.1, Algorithm 2, line 13, p.18

import Mathlib
import Definitions.Def_SecondBestBT_Supplement_alg2Run

open scoped ENNReal

namespace SecondBestBT.Supplement

/-- **ALG2**`(ω; r(1))`, the output of Algorithm 2 (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Section 5.1, Algorithm 2, line 13,
p.18): `fail` (`none`), or the terminal state `(x(t_{|R|}, |R|) ; R[t_{|R|} :])`, the threshold
allocation at the last buyer value together with the suffix of `R = r(0) ∥ r(1)` starting at the
terminal threshold. `ALG2(ω0; r)` is `alg2 α β (baseState α β) r`. -/
noncomputable def alg2 (α β : ℝ) (ω : ℝ × List ℝ≥0∞) (r1 : List ℝ≥0∞) :
    Option (ℝ × List ℝ≥0∞) :=
  (alg2Run α β ω r1).map fun p => (p.1 p.2 (ω.2 ++ r1).length, (ω.2 ++ r1).drop p.2)

end SecondBestBT.Supplement


