-- Prove2me | Definitions.Def_EffRobustLearn_gradF
-- name    : EffRobustLearn_gradF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:38:31.335397+00:00
-- url     : https://prove2.me/theorems/d488f147-3ced-450f-b91c-13acc57e6b47
-- title:
--   The objective $F_t$ and its gradient
-- statement:
--   The regularized objective of Algorithm 1 is
--   $$F_t(u)=\alpha\sum_{r=1}^{t-1}\langle g_r,u\rangle-\frac{\|u[\bar S_{\mathrm{inp}}]-\bar\mu_1[\bar S_{\mathrm{inp}}]\|_2^2}{2|\bar S_{\mathrm{inp}}|}-\frac{\|u[S_{\mathrm{ref}}]-\bar\mu_1[S_{\mathrm{ref}}]\|_2^2}{2|S_{\mathrm{ref}}|},$$
--   with $g_r$ from (3.6) at $\bar\mu_r,h_r$. Its gradient is $\alpha\sum_{r<t}g_r$ minus $(u-\bar\mu_1)/|\bar S_{\mathrm{inp}}|$ on input coordinates and $(u-\bar\mu_1)/|S_{\mathrm{ref}}|$ on reference coordinates.
--
--   **Formalization Note** $F_t$ is the closed form of lines 3 and 8. The gradient is written out, and the verification file proves it is the gradient of $F_t$.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Algorithm 1, lines 3, 7, 8, p.14 (PDF p.15); proof of Lemma 3.8, p.16 (PDF p.17)

import Mathlib
import Definitions.Def_EffRobustLearn_gVec
import Definitions.Def_EffRobustLearn_muSeq

namespace EffRobustLearn

/-- The round-`r` vector `g_r` of Algorithm 1, line 8, Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.14: (3.6) at `μ̄_r` and `h_r`. -/
noncomputable def gSeq {X : Type*} {n m : ℕ} (ε : ℝ) (c0 : X → Bool) (c : ℕ → X → Bool)
    (Sinp : Fin n → X × Bool) (Sref : Fin m → X) (r : ℕ) : SampleVec n m :=
  gVec (muSeq c0 c r) (hSeq ε c0 c r) Sinp Sref

/-- The regularized objective of Algorithm 1, lines 3 and 8, p.14, in closed form:
`F_t(u) = α ∑_{r=1}^{t-1} ⟨g_r, u⟩ - ‖u[S̄inp] - μ̄_1[S̄inp]‖²/(2|S̄inp|) - ‖u[Sref] - μ̄_1[Sref]‖²/(2|Sref|)`. -/
noncomputable def objectiveF {X : Type*} {n m : ℕ} (ε : ℝ) (c0 : X → Bool) (c : ℕ → X → Bool)
    (Sinp : Fin n → X × Bool) (Sref : Fin m → X) (t : ℕ) (u : SampleVec n m) : ℝ :=
  alphaStep (numRounds ε) * ∑ r ∈ Finset.Ico 1 t, inner ℝ (gSeq ε c0 c Sinp Sref r) u
    - (∑ i, (u (Sum.inl i) - evalVec (toPM c0) Sinp Sref (Sum.inl i)) ^ 2) / (2 * (n : ℝ))
    - (∑ j, (u (Sum.inr j) - evalVec (toPM c0) Sinp Sref (Sum.inr j)) ^ 2) / (2 * (m : ℝ))

/-- The gradient `∇F_t(u)` written out, as on p.16: `α ∑_{r=1}^{t-1} g_r` minus `(u - μ̄_1)/|S̄inp|` on the input coordinates and
`(u - μ̄_1)/|Sref|` on the reference coordinates.

**Formalization Note.** The verification file proves `HasGradientAt (objectiveF …) (gradF …) u`, so this is the gradient
of `objectiveF`. -/
noncomputable def gradF {X : Type*} {n m : ℕ} (ε : ℝ) (c0 : X → Bool) (c : ℕ → X → Bool)
    (Sinp : Fin n → X × Bool) (Sref : Fin m → X) (t : ℕ) (u : SampleVec n m) : SampleVec n m :=
  alphaStep (numRounds ε) • ∑ r ∈ Finset.Ico 1 t, gSeq ε c0 c Sinp Sref r
    - WithLp.toLp 2 (Sum.elim
        (fun i => (u (Sum.inl i) - evalVec (toPM c0) Sinp Sref (Sum.inl i)) / (n : ℝ))
        fun j => (u (Sum.inr j) - evalVec (toPM c0) Sinp Sref (Sum.inr j)) / (m : ℝ))

/-- `∇F_t(μ̄_t[S])`, the linear objective of Algorithm 1, line 7, p.14. -/
noncomputable def gradAtIterate {X : Type*} {n m : ℕ} (ε : ℝ) (c0 : X → Bool) (c : ℕ → X → Bool)
    (Sinp : Fin n → X × Bool) (Sref : Fin m → X) (t : ℕ) : SampleVec n m :=
  gradF ε c0 c Sinp Sref t (evalVec (muSeq c0 c t) Sinp Sref)

end EffRobustLearn


