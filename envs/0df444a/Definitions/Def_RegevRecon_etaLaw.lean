-- Prove2me | Definitions.Def_RegevRecon_etaLaw
-- name    : RegevRecon_etaLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:35.013677+00:00
-- url     : https://prove2.me/theorems/431891c8-90ce-4e09-b414-f202bd2b00ba
-- title:
--   The reconstruction recursion: the laws of $\tilde\eta^{(\ell)}$ and the excess $\Psi_\ell$
-- statement:
--   The **reconstruction message** is a random probability vector $\tilde\eta^{(\ell)}$ on $\mathbb F_p$ with $\tilde\eta^{(0)}=e_0$. Given its law at $\ell$, draw $(c_0,\dots,c_{D-1})\sim\Lambda$, set $\gamma_t=c_t/c_0$ and, independently for $t=1,\dots,D-1$, take $U_t\sim\mu$ and $G_t=\tilde\eta_{t,1}^{(\ell)}*\dots*\tilde\eta_{t,k-1}^{(\ell)}$ with independent copies. With $\Gamma_t(s)=\sum_{v\in S}G_t(v-s)$ (47), the next message is
--
--   $$
--   \tilde\eta^{(\ell+1)}(z)\overset d=\frac1N\prod_{t=1}^{D-1}\bigl[e^{-\beta}+(1-e^{-\beta})\Gamma_t(U_t+\gamma_tz)\bigr],\qquad z\in\mathbb F_p,
--   $$
--
--   with $N$ fixed by $\sum_z\tilde\eta^{(\ell+1)}(z)=1$ (48). The **excess** is $\Psi_\ell=E[\tilde\eta^{(\ell)}(0)]-1/p$ (49), the advantage over a uniform guess of guessing the root by sampling from its posterior.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), §7, (47)–(49), pp.19–20

import Mathlib
import Definitions.Def_RegevRecon_Messages

namespace RegevRecon

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- `Γ(s) = Pr_{Z∼G}[Z + s ∈ S] = Σ_{v∈S} G(v − s)`, (47), p.19. -/
noncomputable def gammaFn (S : Finset (ZMod p)) (G : Vec p) (s : ZMod p) : ℝ :=
  ∑ v ∈ S, G (v - s)

/-- The law of one child constraint of the reconstruction recursion, (47), p.19: the pair
`(U_t, G_t)` with `U_t ∼ μ` independent of `G_t = η_{t,1} ∗ ⋯ ∗ η_{t,k−1}`, the `η_{t,h} ∼ P`
independent. -/
noncomputable def branchLaw (k : ℕ) (S : Finset (ZMod p)) (β : ℝ) (P : Law (Vec p)) :
    Law (ZMod p × Vec p) :=
  (Law.ofWeights (channel S β) id).bind fun U =>
    (Law.iid (k - 1) P).map fun ηs => (U, convAll e0 ηs)

/-- The unnormalized product `Π_t [e^{−β} + (1 − e^{−β}) Γ_t(U_t + γ_t z)]`, (48), p.19. -/
noncomputable def etaProduct {D : ℕ} (S : Finset (ZMod p)) (β : ℝ) (γ : Fin (D - 1) → ZMod p)
    (bs : Fin (D - 1) → ZMod p × Vec p) (z : ZMod p) : ℝ :=
  ∏ t, (Real.exp (-β) + (1 - Real.exp (-β)) * gammaFn S (bs t).2 ((bs t).1 + γ t * z))

/-- **The reconstruction message law**, Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), (47)–(48), p.19: `η̃^(0) = e_0`; given `η̃^(ℓ)`, draw one
tuple `c ∼ Λ` with ratios `γ_t`, independent pairs `(U_t, G_t)`, and output the product of (48),
normalized so that its entries sum to `1`.

**Formalization Note** `N = Σ_z Π_t […] > 0` on the support, since every factor is at least `e^{−β}`. -/
noncomputable def etaLaw (k D : ℕ) (S : Finset (ZMod p)) (Λ : PMF (Fin D → (ZMod p)ˣ)) (β : ℝ) :
    ℕ → Law (Vec p)
  | 0 => Law.dirac e0
  | ℓ + 1 => (coeffLaw Λ).bind fun c =>
      (Law.iid (D - 1) (branchLaw k S β (etaLaw k D S Λ β ℓ))).map fun bs z =>
        etaProduct S β (gammaRatio c) bs z / ∑ y, etaProduct S β (gammaRatio c) bs y

/-- **The reconstruction excess** `Ψ_ℓ := E[η̃^(ℓ)(0)] − 1/p`, (49), p.20 (literally, not the norm
form, which is the second identity of (54)). -/
noncomputable def Psi (k D : ℕ) (S : Finset (ZMod p)) (Λ : PMF (Fin D → (ZMod p)ˣ)) (β : ℝ)
    (ℓ : ℕ) : ℝ :=
  (etaLaw k D S Λ β ℓ).expect (fun η => η 0) - (p : ℝ)⁻¹

end RegevRecon


