-- Prove2me | Definitions.Def_EffRobustLearn_certificate
-- name    : EffRobustLearn_certificate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:40.690885+00:00
-- url     : https://prove2.me/theorems/c363d73b-1f74-4076-8fe1-abb12b07e256
-- title:
--   Corruption certificate $\eta(c,\bar\mu;\bar S_{\mathrm{inp}},S_{\mathrm{ref}})$, explicit form (A.3)
-- statement:
--   For real-valued $c,\bar\mu$, a labeled sample $\bar S_{\mathrm{inp}}$ and a reference sample $S_{\mathrm{ref}}$,
--   $$\eta(c,\bar\mu;\bar S_{\mathrm{inp}},S_{\mathrm{ref}})=\frac1{2|\bar S_{\mathrm{inp}}|}\sum_{(x,y)\in\bar S_{\mathrm{inp}}}\frac{|\bar\mu(x)|+y\bar\mu(x)-2yc(x)}{2+|\bar\mu(x)|+y\bar\mu(x)}-\frac1{2|S_{\mathrm{ref}}|}\sum_{x\in S_{\mathrm{ref}}}\frac{c(x)\bar\mu(x)-1}{1+|\bar\mu(x)|}.$$
--
--   The certificate estimates how many corruptions an adversary would need to turn a clean sample labeled by $c$ into $\bar S_{\mathrm{inp}}$. The objective (3.1) of the algorithm subtracts it from the error.
--
--   **Formalization Note** Real-valued $c$ is the affine extension in the first argument the paper uses in Lemma 3.10. Both denominators are $\ge1$ for $y=\pm1$ and every real $\bar\mu(x)$.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), eq. (A.3), p.30 (PDF p.31)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM

namespace EffRobustLearn

/-- The corruption certificate in the explicit form (A.3), Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.30:
`η(c, μ̄; S̄inp, Sref) = (1/(2|S̄inp|)) ∑_{(x,y)∈S̄inp} (|μ̄(x)| + y μ̄(x) - 2 y c(x)) / (2 + |μ̄(x)| + y μ̄(x))
  - (1/(2|Sref|)) ∑_{x∈Sref} (c(x) μ̄(x) - 1) / (1 + |μ̄(x)|)`.

**Formalization Note.** Both arguments are real-valued: this is the affine extension in `c` the paper uses in Lemma 3.10
(p.32: "We extend η affinely in its first argument through Eq. (A.3)"). A concept enters as `toPM c`. Both denominators are
`≥ 1` for every real `μ̄(x)` and every label `y = ±1`, so no division degenerates. Eq. (A.3), stated as
`EffRobustLearn.eq_A_3`, identifies this with the probabilities of Definition 3.3 (`certificateProb`). -/
noncomputable def certificate {X : Type*} {n m : ℕ} (c μ : X → ℝ)
    (Sinp : Fin n → X × Bool) (Sref : Fin m → X) : ℝ :=
  (1 / (2 * (n : ℝ))) * ∑ i, (|μ (Sinp i).1| + pm (Sinp i).2 * μ (Sinp i).1
      - 2 * pm (Sinp i).2 * c (Sinp i).1) / (2 + |μ (Sinp i).1| + pm (Sinp i).2 * μ (Sinp i).1)
    - (1 / (2 * (m : ℝ))) * ∑ j, (c (Sref j) * μ (Sref j) - 1) / (1 + |μ (Sref j)|)

end EffRobustLearn


