-- Prove2me | Definitions.Def_OWFLocalDesc_Supplement_pKT
-- name    : OWFLocalDesc_Supplement_pKT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:41:34.009991+00:00
-- url     : https://prove2.me/theorems/1c4e6d4c-c56a-4c5d-9700-7adf76124de3
-- title:
--   Global public-randomness quantile $\mathrm{pK}^T_{\mathrm{all},\theta}(y\mid E(x))$ (Definition B.1)
-- statement:
--   Fix a global decoder $V$ and a global clock $T=T(n)$, a positive integer-valued function. Draw a uniform public tape $W\in\{0,1\}^T$. For $0<\theta\le1$,
--   $$\mathrm{pK}^T_{\mathrm{all},\theta}(y\mid E(x))=\min\Big\{s\in\mathbb Z_{\ge0} : \Pr_W\big[h^T_W(x,y)\le s\big]\ge\theta\Big\},$$
--   with value $\infty$ when the set is empty.
--
--   This is the global analogue of the pointwise quantile $\mathrm{pSC}^t_\theta$. The program sees the whole point vector, and the tape is drawn before the description is chosen.
--
--   **Formalization Note** The value lies in `ℕ∞`. $T$ is the clock's value at the current point length, used as both the tape length and the step bound, as in the published `OWFLocalDesc.pSC`.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition B.1, p.37

import Mathlib
import Definitions.Def_OWFLocalDesc_Supplement_hT
set_option autoImplicit false

namespace OWFLocalDesc.Supplement

/-- The fraction `Pr_W[h^T_W(x,y) ≤ s]` of global public tapes `W ∈ {0,1}^T` on which some program
of length at most `s` makes `V` output `y` within the clock. -/
noncomputable def globalTapeProb (V : GlobalDecoder) (T : ℕ) {m n : ℕ}
    (x : Fin m → Fin n → Bool) (y : Fin m → Bool) (s : ℕ) : ℝ :=
  open Classical in
  ((Finset.univ.filter fun W : Fin T → Bool => hT V T x y (List.ofFn W) ≤ (s : ℕ∞)).card : ℝ) /
    (2 : ℝ) ^ T

/-- **Global public-randomness quantile `pK^T_{all,θ}(y | E(x))` (Definition B.1).** Myrisiotis,
*One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission (held manuscript,
sha256 d818fa43…4c4e), Definition B.1, p.37: "A global clock is a positive integer-valued function
T = T(n). Fix such a clock and draw a uniform public tape W ∈ {0,1}^T. … For 0 < θ ≤ 1, put
pK^T_{all,θ}(y|E(x)) = min{s ∈ Z≥0 : Pr_W[h^T_W(x,y) ≤ s] ≥ θ}, with value ∞ when the set is
empty."

**Formalization Note.** The value is in `ℕ∞` (`⊤ = ∞` when no `s` qualifies). `T` is the value
of the global clock at the current point length: both the tape length and the step bound, as for
the published `OWFLocalDesc.pSC`. Statements use it only for `0 < θ ≤ 1`. -/
noncomputable def pKT (V : GlobalDecoder) (T : ℕ) (θ : ℝ) {m n : ℕ}
    (x : Fin m → Fin n → Bool) (y : Fin m → Bool) : ℕ∞ :=
  ⨅ (s : ℕ) (_ : θ ≤ globalTapeProb V T x y s), (s : ℕ∞)

end OWFLocalDesc.Supplement


