-- Prove2me | Definitions.Def_OmniMix_HasVRep
-- name    : OmniMix_HasVRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:57.491128+00:00
-- url     : https://prove2.me/theorems/b58063c8-a1c6-40d4-b387-d21bd6b0d372
-- title:
--   V-shaped representation (13)
-- statement:
--   A loss $\ell$ **has the V-shaped representation (13)** with constants $C:\{0,1\}\to\mathbb R$ and density $w:\mathbb R\to[0,+\infty]$ if $w$ is measurable and
--   $$
--   \ell(p,y)=C(y)+\int_0^1 w(v)\,\lambda_v(p,y)\,dv\qquad\text{for all }p\in[0,1],\ y\in\{0,1\}.
--   $$
--   The integral is the Lebesgue integral of a nonnegative function and may equal $+\infty$ (for log loss at $p=0$, $y=1$).
--
--   **Formalization Note** $C$ is real-valued (in the paper's proof $C(y)=(1-y)\ell(0,0)+y\ell(1,1)$, which is finite). $w$ takes values in $[0,+\infty]$, so it is nonnegative by type; the integral is over $[0,1]$ for Lebesgue measure.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Lemma 2.1, §2, p.9, Eq. (13)

import Mathlib
import Definitions.Def_OmniMix_Loss
import Definitions.Def_OmniMix_vLossR

namespace OmniMix

/-- **V-shaped representation (13).** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, Lemma 2.1, §2, p.9, Eq. (13):
"`ℓ(p, y) = C_ℓ(y) + ∫_0^1 w_ℓ(v)λ_v(p, y) dv` for all `p ∈ [0, 1]` and `y ∈ {0, 1}`, where `C_ℓ(y)`
is independent of the prediction and `w_ℓ` is nonnegative and measurable."

`HasVRep ℓ C w` says that `w` is measurable and (13) holds with the constants `C` and density `w`.

**Formalization Note.** `C : {0,1} → ℝ` is real (in the proof, p.33, `C_ℓ(y) = (1−y)ℓ(0,0) + yℓ(1,1)`,
which is finite). The density `w : ℝ → [0, +∞]` is `ℝ≥0∞`-valued, so it is nonnegative by type, and
the integral is the Lebesgue integral `∫⁻` over `[0,1]`, which may be `+∞` (e.g. log loss at
`p = 0`, `y = 1`); it is coerced to `EReal`. -/
def HasVRep (ℓ : Loss) (C : Bool → ℝ) (w : ℝ → ENNReal) : Prop :=
  Measurable w ∧ ∀ (p : unitInterval) (y : Bool),
    ℓ p y = ((C y : ℝ) : EReal) +
      ((∫⁻ v in Set.Icc (0 : ℝ) 1, w v * ENNReal.ofReal (vLossR v p y) : ENNReal) : EReal)

end OmniMix


