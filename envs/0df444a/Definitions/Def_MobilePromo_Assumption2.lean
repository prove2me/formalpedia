-- Prove2me | Definitions.Def_MobilePromo_Assumption2
-- name    : MobilePromo_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:50.6786+00:00
-- url     : https://prove2.me/theorems/481cee73-31ee-4671-80b1-2fd99d7eac17
-- title:
--   Assumption 2: identifiability and a positive definite Fisher matrix
-- statement:
--   For the exploration bids $\bar{\boldsymbol b}_l$, the family $\{Q_l^{\bar{\boldsymbol b}_l,\gamma_l}:\gamma_l\in\Gamma_l^{(0)}\}$ is **identifiable**: for $\gamma_l\ne\bar\gamma_l$ in $\Gamma_l^{(0)}$ there is $\boldsymbol d\in\{0,1\}^{k_l}$ with $Q_l^{\bar{\boldsymbol b}_l,\gamma_l}(\boldsymbol d)\ne Q_l^{\bar{\boldsymbol b}_l,\bar\gamma_l}(\boldsymbol d)$. Moreover, for each $\gamma_l\in\Gamma_l^{(0)}$ the Fisher information matrix
--
--   $$
--   [\boldsymbol I_l(\bar{\boldsymbol b}_l,\gamma_l)]_{u,v}=\mathbb E\Bigl[-\frac{\partial^2}{\partial\gamma_{l,u}\partial\gamma_{l,v}}\log Q_l^{\bar{\boldsymbol b}_l,\gamma_l}(\boldsymbol D)\Bigr],\qquad u,v=1,\dots,n_l,
--   $$
--
--   is positive definite. This guarantees that $\gamma_l^{(0)}$ can be estimated from the outcomes of the exploration bids.
--
--   **Formalization Note** The expectation is the finite sum over $\boldsymbol d\in\{0,1\}^{k_l}$ under $Q_l^{\bar{\boldsymbol b}_l,\gamma_l}$. The partial derivatives are ambient `fderiv`s along coordinate vectors; at a point of the open set $\Gamma_l$ they depend only on the curve near that point. Positive definiteness is read at every point of $\Gamma_l^{(0)}$, as in condition (iv) of the proof of Lemma 3 (A9).
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, Assumption 2 and (6), p.12; condition (iv), A9 (PDF 43)

import Mathlib
import Definitions.Def_MobilePromo_Exploration

set_option autoImplicit false

namespace MobilePromo

/-- The Fisher information matrix of (6) (SSRN 3523491, (6), p.12):
`[I_l(b̄_l, γ_l)]_{u,v} = E[-∂²/∂γ_{l,u}∂γ_{l,v} log Q_l^{b̄_l, γ_l}(D)]`, the expectation being the finite
sum over `d ∈ {0,1}^{k_l}` under `Q_l^{b̄_l, γ_l}`.

**Formalization Note** The two partial derivatives are `fderiv`s in the ambient `ℝ^{n_l}` along the
coordinate vectors. At a point of the open set `Γ_l` they only see the curve near that point. -/
noncomputable def fisher (M : Model) (X : Exploration M) (l : Fin M.L) (γl : Param (M.n l)) :
    Matrix (Fin (M.n l)) (Fin (M.n l)) ℝ := fun u v =>
  ∑ d : Fin (X.k l) → Bool, Q M l (X.bbar l) γl d *
    (-(fderiv ℝ (fun g : Param (M.n l) =>
        fderiv ℝ (fun g' : Param (M.n l) => Real.log (Q M l (X.bbar l) g' d)) g
          (EuclideanSpace.single v 1)) γl (EuclideanSpace.single u 1)))

/-- Assumption 2, the statistical assumption, for the given exploration bids (SSRN 3523491,
Assumption 2, p.12): the family `{Q_l^{b̄_l, γ_l} : γ_l ∈ Γ_l⁽⁰⁾}` is identifiable, and the Fisher matrix of
(6) is positive definite at each `γ_l ∈ Γ_l⁽⁰⁾`.

**Formalization Note** The paper says "there exist `k_l` and `b̄_l`" and takes them as the input of the
policy; here they are the parameter `X`. The positive definiteness is read at every point of `Γ_l⁽⁰⁾`,
as in condition (iv) of the proof of Lemma 3 (A9, PDF 43). -/
structure Assumption2 (M : Model) (X : Exploration M) : Prop where
  identifiable : ∀ l, ∀ γ ∈ M.Γ₀ l, ∀ γ' ∈ M.Γ₀ l, γ ≠ γ' →
    ∃ d : Fin (X.k l) → Bool, Q M l (X.bbar l) γ d ≠ Q M l (X.bbar l) γ' d
  fisher_posDef : ∀ l, ∀ γ ∈ M.Γ₀ l, (fisher M X l γ).PosDef

end MobilePromo


