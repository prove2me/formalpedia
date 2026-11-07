-- Prove2me | Definitions.Def_LaconicBarrier_IsBBReduction
-- name    : LaconicBarrier_IsBBReduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:24.064292+00:00
-- url     : https://prove2.me/theorems/30123c33-57a6-40ee-ba45-7f931ffbefcd
-- title:
--   Non-uniform black-box reduction to the $\Gamma$-hardness of a game
-- statement:
--   Let $\{(\mathcal D_x, c_0)\}_{x \in X}$ be a family of two-message games, $(\mathcal C, c)$ a game, $(\mathcal R, F)$ a reduction with advice and $\Gamma(\lambda, n) \ge \lambda$ a bound. $(\mathcal R, F)$ is a **reduction to the $\Gamma$-hardness of $(\mathcal C, c)$** if for every polynomially bounded index sequence $\{x_\lambda \in X\}$ and every possibly unbounded non-uniform family $\{A_\lambda\}$ of randomized response oracles: whenever
--   $$
--   \delta(\lambda) = \mathrm{Adv}_{(\mathcal D_{x_\lambda}, c_0)}(A_\lambda; \lambda)
--   $$
--   is nonnegligible, the reduction $\Gamma$-breaks $(\mathcal C, c)$ run at its target-parameter map: for some polynomial $p$, infinitely often,
--   $$
--   \delta'(\lambda) = \max\Bigl\{0,\ \Pr\bigl[\mathcal R^{A_\lambda}(1^\lambda, x_\lambda, z_\lambda) \text{ wins } \mathcal C(1^{f(1^\lambda,|x_\lambda|)}) : z_\lambda \leftarrow F(1^\lambda, x_\lambda)\bigr] - c\Bigr\} > \frac{1}{p(\Gamma(\lambda, |x_\lambda|))}.
--   $$
--   The reduction and the advice are fixed before the sequence and the adversary; $F$ never sees the adversary. With $\Gamma(\lambda, n) = \lambda$ this is a reduction to $(\mathcal C, c)$.
--
--   **Formalization Note** This is the guarantee only; the syntax (time bound, advice length, query count) is stated by separate definitions.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.13, p.21

import Mathlib
import Definitions.Def_LaconicBarrier_TwoMsg
import Definitions.Def_LaconicBarrier_Reduction_winProb
import Definitions.Def_LaconicBarrier_Breaks

namespace LaconicBarrier

/-- The guarantee of a **non-uniform black-box reduction to the Γ-hardness** of `(C, c)` at its
target-parameter map (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for
Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.13, p.21):
for every polynomially bounded index sequence `{x_λ ∈ X}` and every possibly unbounded non-uniform
family `{A_λ}` of randomized response oracles, if the source advantage
`δ(λ) = Adv_{(D_{x_λ}, c₀)}(A_λ; λ)` is nonnegligible, then the reduction Γ-breaks `(C, c)` run at
`f`: `δ′(λ) = max{0, Pr[R^{A_λ}(1^λ, x_λ, z_λ) wins C(1^{f(1^λ, |x_λ|)}) : z_λ ← F(1^λ, x_λ)] − c}`
exceeds `1/p(Γ(λ, |x_λ|))` infinitely often, for some polynomial `p`.

The reduction `R` and the advice `F` are fixed before the sequence and the adversary; `F` does not
see the adversary. With `Γ(λ, n) = λ` this is "a reduction to `(C, c)`". The syntax (time, advice
length, query count) is stated separately: `Reduction.IsTTime`, `AdviceBounded`,
`Reduction.IsKQuery`. -/
def IsBBReduction (S : TwoMsg) (X : Set (List Bool)) (R : Reduction)
    (F : ℕ → List Bool → PMF (List Bool)) (G : Game) (Γ : ℕ → ℕ → ℕ) : Prop :=
  ∀ xs : ℕ → List Bool, (∀ lam, xs lam ∈ X) →
    (∃ N : Polynomial ℕ, ∀ lam, (xs lam).length ≤ N.eval lam) →
    ∀ A : ℕ → List Bool → PMF (List Bool),
      Breaks (fun lam => lam) (fun lam => S.adv lam (xs lam) (A lam)) →
      Breaks (fun lam => Γ lam (xs lam).length)
        (fun lam => max 0 (R.winProb G (fun _ => A lam) lam (xs lam) (F lam (xs lam)) - G.c))

end LaconicBarrier


