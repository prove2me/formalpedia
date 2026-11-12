-- Prove2me | Definitions.Def_DictatorsCK_Main_Information
-- name    : DictatorsCK_Main_Information
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:35:03.740033+00:00
-- url     : https://prove2.me/theorems/691daafc-4043-454b-b1fa-95bdbfaa593c
-- title:
--   Sign entropy $\Phi$, mean, conditional entropy $E_\rho$, information $A_\rho$ (nats), gap $G_f$, $M_\rho$, $\mathrm{QLP}$ and $\mathrm{KKh}$
-- statement:
--   Let $H(t)=H_b((1-t)/2)$, $t\in[-1,1]$, be the entropy in nats of a sign-valued variable with mean $t$ (the published `entropy`, $\log2-\psi$), and let $T_\rho$, $0\le\rho\le1$, be the noise operator $(T_\rho h)(y)=\sum_x h(x)\prod_i\frac{1+\rho x_iy_i}{2}$ (the published `noiseOperator ρ`). For a Boolean $f$ on the uniform cube:
--
--   1. $\Phi(t)=\log2-H(t)$ (1.1); $f$ is **nonconstant** if it takes both values; $\mu=\mathbb E f$.
--   2. The **conditional entropy** (2.2) $E_\rho(f)=\mathbb E H(T_\rho f)=2^{-n}\sum_y H((T_\rho f)(y))$.
--   3. The **information** (1.2) $A_\rho(f)=I(f(X);Y_\rho)$ in nats, where $Y_\rho$ flips each coordinate of the uniform $X$ independently with probability $(1-\rho)/2$; it is the published mutual information with crossover $\varepsilon=(1-\rho)/2$, multiplied by $\log2$ to convert bits to nats.
--   4. The **signed gap** (1.3) $G_f(\rho)=A_\rho(f)-\Phi(\rho)$; the Courtade–Kumar inequality is $G_f\le0$.
--   5. For $0\le a\le1$, (3.2) $M_\rho(a)=(1-\rho^2)H(\rho a)-(1-\rho^2a)H(\rho)$.
--   6. (3.5) $\mathrm{QLP}(a)=a^2+1-a$ for $0\le a\le\tfrac12$ and $a^2+2\sqrt2(1-a)^{3/2}-2(1-a)^2$ for $\tfrac12\le a\le1$ (the two formulas agree at $\tfrac12$).
--   7. (3.6) $\mathrm{KKh}(a)=\big(1+\sqrt{1+2(\pi-\sqrt{2\pi})a}\big)^2/(2\pi)$ for $0\le a\le1$.
--
--   The identity $A_\rho(f)=H(\mu)-E_\rho(f)$ of (2.2) is a fact of the paper, not a definition here: the information is the genuine mutual information of the published goal, so milestones about $A_\rho$ speak about the goal's own quantity.
--
--   **Formalization Note.** `info ρ f = ell * mutualInformation ((1 - ρ)/2) f` with `ell = log 2`. Outside their stated domains the scalar functions return Lean's default values; every milestone applies them only inside those domains.
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 1 (PDF 2), (1.1); p. 3 (PDF 4), (1.2), (1.3); p. 8 (PDF 9), (2.2); p. 13 (PDF 14), (3.2); p. 17 (PDF 18), (3.5), (3.6)

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Fourier

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

noncomputable section

/-- `Φ(t) = log 2 − H(t)`, where `H = entropy` is the sign entropy `H(t) = H_b((1 − t)/2)` in nats. -/
def Phi (t : ℝ) : ℝ :=
  Real.log 2 - entropy t

/-- A Boolean function is nonconstant when it takes both values. -/
def IsNonconstant {n : ℕ} (f : Cube n → Bool) : Prop :=
  ∃ x y, f x ≠ f y

/-- The mean `µ = E f` of a Boolean function, read in `{−1, 1}` through `signEncoding`. -/
def mean {n : ℕ} (f : Cube n → Bool) : ℝ :=
  cubeAverage (signEncoding f)

/-- The conditional entropy `E_ρ(f) = E H(T_ρ f) = 2^{−n} ∑_y H((T_ρ f)(y))` (nats), with
`T_ρ = noiseOperator ρ`. -/
def condEntropy {n : ℕ} (ρ : ℝ) (f : Cube n → Bool) : ℝ :=
  cubeAverage (fun y => entropy (noiseOperator ρ (signEncoding f) y))

/-- The information `A_ρ(f) = I(f(X); Y_ρ)` in nats: the mutual information of the published
Courtade–Kumar statement (bits, crossover `ε = (1 − ρ)/2`) multiplied by `log 2`. -/
def info {n : ℕ} (ρ : ℝ) (f : Cube n → Bool) : ℝ :=
  ell * mutualInformation ((1 - ρ) / 2) f

/-- The signed information gap `G_f(ρ) = A_ρ(f) − Φ(ρ)`. -/
def gap {n : ℕ} (f : Cube n → Bool) (ρ : ℝ) : ℝ :=
  info ρ f - Phi ρ

/-- `M_ρ(a) = (1 − ρ^2) H(ρ a) − (1 − ρ^2 a) H(ρ)`, display (3.2). -/
def Mfun (ρ a : ℝ) : ℝ :=
  (1 - ρ ^ 2) * entropy (ρ * a) - (1 - ρ ^ 2 * a) * entropy ρ

/-- `QLP(a)`, display (3.5): `a^2 + 1 − a` on `[0, 1/2]` and
`a^2 + 2√2 (1 − a)^{3/2} − 2 (1 − a)^2` on `[1/2, 1]` (the two branches agree at `1/2`). -/
def QLP (a : ℝ) : ℝ :=
  if a ≤ 1 / 2 then a ^ 2 + 1 - a
  else a ^ 2 + 2 * Real.sqrt 2 * (1 - a) ^ ((3 : ℝ) / 2) - 2 * (1 - a) ^ 2

/-- `KKh(a) = (1 + √(1 + 2(π − √(2π)) a))^2 / (2π)`, display (3.6). -/
def KKh (a : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 2 * (Real.pi - Real.sqrt (2 * Real.pi)) * a)) ^ 2 / (2 * Real.pi)

end

end DictatorsCK.Main


