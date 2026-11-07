-- Prove2me | Definitions.Def_EffRobustLearn_certificateProb
-- name    : EffRobustLearn_certificateProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:35:35.554203+00:00
-- url     : https://prove2.me/theorems/b5ae9bf3-c2f5-4cae-914c-a35974a1b42a
-- title:
--   Detection function and the certificate as printed (Definition 3.3)
-- statement:
--   For a concept $c$ and $\bar\mu:X\to[-1,1]$, the detection function is $f_{c,\bar\mu}(x)=\frac{c(x)\bar\mu(x)-1}{1+|\bar\mu(x)|}$, and
--   $$\eta(c,\bar\mu;\bar S_{\mathrm{inp}},S_{\mathrm{ref}})=\Pr_{(x,y)\sim\bar S_{\mathrm{inp}}}[c(x)\ne y\text{ or }\mathrm{Rad}(f_{c,\bar\mu}(x))=1]-\Pr_{x\sim S_{\mathrm{ref}}}[\mathrm{Rad}(f_{c,\bar\mu}(x))=1].$$
--
--   This is the definition eq. (A.3) rewrites explicitly.
--
--   **Formalization Note** Each probability is an exact finite computation: a sample average of a two-point sum over the outcome of $\mathrm{Rad}$.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Definition 3.3, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM
import Definitions.Def_EffRobustLearn_majK

namespace EffRobustLearn

/-- The detection function of Definition 3.3, Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.12:
`f_{c,μ̄}(x) = (c(x) μ̄(x) - 1) / (1 + |μ̄(x)|)`. -/
noncomputable def detection {X : Type*} (c : X → Bool) (μ : X → ℝ) (x : X) : ℝ :=
  (toPM c x * μ x - 1) / (1 + |μ x|)

open Classical in
/-- The corruption certificate as printed in Definition 3.3, p.12:
`η(c, μ̄; S̄inp, Sref) = Pr_{(x,y)∼S̄inp}[c(x) ≠ y or Rad(f_{c,μ̄}(x)) = 1] - Pr_{x∼Sref}[Rad(f_{c,μ̄}(x)) = 1]`.

**Formalization Note.** Each probability is an exact finite computation: the uniform average over the sample of the
two-point sum over the outcome `z` of `Rad(f_{c,μ̄}(x))`. Used only to state (A.3); the rest of the development uses the
explicit form `certificate`. -/
noncomputable def certificateProb {X : Type*} {n m : ℕ} (c : X → Bool) (μ : X → ℝ)
    (Sinp : Fin n → X × Bool) (Sref : Fin m → X) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, ∑ z : Bool, radPmf (detection c μ (Sinp i).1) z *
      (if c (Sinp i).1 ≠ (Sinp i).2 ∨ z = true then 1 else 0)
    - (1 / (m : ℝ)) * ∑ j, ∑ z : Bool, radPmf (detection c μ (Sref j)) z *
      (if z = true then 1 else 0)

end EffRobustLearn


