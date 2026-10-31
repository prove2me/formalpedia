-- Prove2me | Definitions.Def_SeqExpDiffusion_IsTwoActionForm
-- name    : SeqExpDiffusion_IsTwoActionForm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:44.412705+00:00
-- url     : https://prove2.me/theorems/649359b6-b736-44ec-8708-1c61cc3f9eaf
-- title:
--   Thresholds and constants of (18), fixed by value matching and smooth pasting (17) (corrected)
-- statement:
--   Let $a_i,a_j$ be two actions with $\tilde\beta_i<\tilde\beta_j$, so $a_i$ is preferred at low beliefs, and let $\gamma=(1+\sqrt{1+8r/\tilde\sigma^2})/2$ and $u(\delta)=C^0(1-\delta)^\gamma\delta^{1-\gamma}+C^1(1-\delta)^{1-\gamma}\delta^\gamma$. The quadruple $(\underline\delta,\bar\delta,C^0,C^1)$ is **admissible for (18)** if
--
--   1. $0\le\underline\delta$, $\bar\delta\le1$, $C^0\ge0$, $C^1\ge0$, and $\underline\delta<\hat\delta_{ij}<\bar\delta$, i.e. $\tilde R_j(\underline\delta)<\tilde R_i(\underline\delta)$ and $\tilde R_i(\bar\delta)<\tilde R_j(\bar\delta)$;
--   2. $\underline\delta=0 \iff C^0=0 \iff \tilde R_i\equiv0$, and $\bar\delta=1\iff C^1=0\iff\tilde R_j\equiv0$;
--   3. value matching and smooth pasting (17): if $\underline\delta>0$ then $u(\underline\delta)=\tilde R_i(\underline\delta)$ and $u'(\underline\delta)=\tilde\beta_i$; if $\bar\delta<1$ then $u(\bar\delta)=\tilde R_j(\bar\delta)$ and $u'(\bar\delta)=\tilde\beta_j$.
--
--   **Formalization Note** The page asserts $\underline\delta_{ij},\bar\delta_{ij}\in(0,1)$ and positive constants. This fails when one action pays $0$ at every belief: for $\tilde R_i\equiv0$, $\tilde R_j(\delta)=2\delta-1$, value matching and smooth pasting to $0$ at any $\underline\delta>0$ force $C^0=C^1=0$ (the Wronskian of the two solutions is nonzero), and $u\equiv0$ cannot meet $\tilde R_j$ with slope $2$. Clause 2 is the minimal correction: a threshold reaches the end of $[0,1]$, and its constant vanishes, exactly in that case.
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, Proposition 5 and display (17), p.20 (corrected)

import Mathlib
import Definitions.Def_SeqExpDiffusion_reward
import Definitions.Def_SeqExpDiffusion_gammaOf
import Definitions.Def_SeqExpDiffusion_contValue

namespace SeqExpDiffusion

/-- The thresholds `δ̲ = a`, `δ̄ = b` and constants `C⁰ = C₀`, `C¹ = C₁` of the closed form (18)
for the pair `(a_i, a_j)`, where `a_i` is the left action (`β i < β j`), Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, Proposition 5 and
display (17), p.20 (corrected).

1. `0 ≤ a`, `b ≤ 1`, `C₀ ≥ 0`, `C₁ ≥ 0`, and `a < δ̂_ij < b`, i.e. `R̃_j(a) < R̃_i(a)` and
   `R̃_i(b) < R̃_j(b)`;
2. `a = 0 ↔ C₀ = 0 ↔ R̃_i ≡ 0`, and `b = 1 ↔ C₁ = 0 ↔ R̃_j ≡ 0`;
3. value matching and smooth pasting (17): if `a > 0`, the function
   `u = contValue γ C₀ C₁` has `u(a) = R̃_i(a)` and `u′(a) = R̃_i′ = β i`; if `b < 1`,
   `u(b) = R̃_j(b)` and `u′(b) = β j`.

**Formalization Note** The page asserts `δ̲, δ̄ ∈ (0, 1)` and `C⁰, C¹ > 0`. This fails when one action
pays `0` at every belief (`R̃_i ≡ 0`, `R̃_j(δ) = 2δ − 1` satisfies every assumption; value matching and
smooth pasting to `0` at any `δ̲ > 0` force `C⁰ = C¹ = 0`, since the Wronskian of the two solutions is
nonzero). Clause 2 is the minimal correction: the threshold reaches the end of `[0, 1]`, and the
constant vanishes, exactly in that case. `γ = gammaOf r σ`. -/
def IsTwoActionForm {ι : Type*} (r σ : ℝ) (α β : ι → ℝ) (i j : ι) (a b C₀ C₁ : ℝ) : Prop :=
  0 ≤ a ∧ b ≤ 1 ∧ 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
  reward α β j a < reward α β i a ∧ reward α β i b < reward α β j b ∧
  (a = 0 ↔ C₀ = 0) ∧ (C₀ = 0 ↔ α i = 0 ∧ β i = 0) ∧
  (b = 1 ↔ C₁ = 0) ∧ (C₁ = 0 ↔ α j = 0 ∧ β j = 0) ∧
  (0 < a → contValue (gammaOf r σ) C₀ C₁ a = reward α β i a ∧
    HasDerivAt (contValue (gammaOf r σ) C₀ C₁) (β i) a) ∧
  (b < 1 → contValue (gammaOf r σ) C₀ C₁ b = reward α β j b ∧
    HasDerivAt (contValue (gammaOf r σ) C₀ C₁) (β j) b)

end SeqExpDiffusion


