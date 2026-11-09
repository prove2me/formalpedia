-- Prove2me | Definitions.Def_SemAC02_IsCoinDistinguisher
-- name    : SemAC02_IsCoinDistinguisher
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:43.224996+00:00
-- url     : https://prove2.me/theorems/6c3f7557-b386-4b6f-977f-db3d91bd6161
-- title:
--   Distinguishers for the $\epsilon$-coin problem
-- statement:
--   For $0<\epsilon<1$, the $\epsilon$-coin problem is to distinguish independent samples of a coin of bias $(1-\epsilon)/2$ from independent samples of a coin of bias $(1+\epsilon)/2$. A Boolean function $T:\{0,1\}^m\to\{0,1\}$ is a **distinguisher for the $\epsilon$-coin problem with error at most $\eta$** if
--   $$
--   \Pr_{x\sim\mathrm{Bern}((1-\epsilon)/2)^m}[T(x)=1]\le\eta\quad\text{and}\quad\Pr_{x\sim\mathrm{Bern}((1+\epsilon)/2)^m}[T(x)=0]\le\eta .
--   $$
--   Small-depth monotone distinguishers are the raw material of the approximate-majority gadget.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Definition 8.8, p.66 (PDF p.68)

import Mathlib
import Definitions.Def_SemAC02_bernProb

namespace SemAC02

/-- **Coin problem and distinguishers** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard
Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission), Definition 8.8,
p.66): for `0 < ϵ < 1`, `T : {0,1}^m → {0,1}` is a distinguisher for the `ϵ`-coin problem with
error at most `η` if
`Pr_{x∼Bern((1−ϵ)/2)^m}[T(x) = 1] ≤ η` and `Pr_{x∼Bern((1+ϵ)/2)^m}[T(x) = 0] ≤ η`. -/
def IsCoinDistinguisher (ε η : ℝ) {m : ℕ} (T : (Fin m → Bool) → Bool) : Prop :=
  bernProb ((1 - ε) / 2) T ≤ η ∧ bernProb ((1 + ε) / 2) (fun x => !T x) ≤ η

end SemAC02


