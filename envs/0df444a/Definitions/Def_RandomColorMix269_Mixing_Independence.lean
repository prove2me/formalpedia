-- Prove2me | Definitions.Def_RandomColorMix269_Mixing_Independence
-- name    : RandomColorMix269_Mixing_Independence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:46.613479+00:00
-- url     : https://prove2.me/theorems/f03e793f-677a-421d-8a62-c134b0ea4307
-- title:
--   Definitions 1.2–1.3 — influence matrix, spectral independence and coupling independence
-- statement:
--   Let $\mu$ be a law on $[q]^V$ and let $\tau$ be a feasible pinning on $\Lambda\subseteq V$. The **influence matrix** $\Psi^\tau_\mu$ is indexed by the pairs $u\leftarrow i$ with $u\in V\setminus\Lambda$ and $\mu^\tau(u\leftarrow i)>0$. For two such pairs with $u\ne v$,
--   $$
--   \Psi^\tau_\mu(u\leftarrow i,\,v\leftarrow j)=\mu^\tau(v\leftarrow j\mid u\leftarrow i)-\mu^\tau(v\leftarrow j),
--   $$
--   and every entry with $u=v$ is zero. The law is **$\gamma$-spectrally independent** if $\lambda_{\max}(\Psi^\tau_\mu)\le\gamma$ for every feasible pinning $\tau$ (Definition 1.2, p.3).
--
--   For pinnings $\sigma,\tau$ on the same boundary $\Lambda$, both feasible and differing at exactly one coordinate, the law is **$C$-coupling independent** if
--   $$
--   W_1\big(\mu^\sigma,\mu^\tau\big)\le C,\qquad W_1(\mu,\nu)=\inf_{\text{couplings }(X,Y)}\ \mathbb E\sum_{u\in V}\mathbf 1[X(u)\ne Y(u)],
--   $$
--   where the Hamming cost counts all coordinates, including the pinned coordinate where $\sigma$ and $\tau$ differ (Definition 1.3, pp.3–4).
--
--   **Formalization Note** $\Psi^\tau_\mu$ is not symmetric; with $D=\mathrm{diag}(\mu^\tau(u\leftarrow i))$ the matrix $D^{1/2}\Psi^\tau_\mu D^{-1/2}$, whose off-site entries are $\big(\mu^\tau(u\leftarrow i,v\leftarrow j)-\mu^\tau(u\leftarrow i)\mu^\tau(v\leftarrow j)\big)/\sqrt{\mu^\tau(u\leftarrow i)\mu^\tau(v\leftarrow j)}$, is symmetric with the same eigenvalues. The bound $\lambda_{\max}\le\gamma$ is stated as the quadratic-form inequality for this symmetric matrix. $W_1$ is the published transport distance `MarkovMixing.transportDist` with Hamming cost.
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, pp.3–4, Definitions 1.2 and 1.3

import Definitions.Def_RandomColorMix269_Mixing_Laws

open scoped Classical BigOperators
open Finset
set_option autoImplicit false
noncomputable section

namespace RandomColorMix269.Mixing

/-! Definitions 1.2–1.3, pp.3–4. The symmetric matrix is
D^(1/2) Ψ D^(-1/2), equivalently the off-site covariance divided by
sqrt(p_i p_j). Its quadratic-form bound is exactly λ_max ≤ γ,
including an empty matrix. -/
variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}

def CouplingIndependent (μ : (V → Fin q) → ℝ) (C : ℝ) : Prop :=
  ∀ (Λ : Finset V) (x y : V → Fin q), Feasible μ Λ x → Feasible μ Λ y →
    (Λ.filter fun v => x v ≠ y v).card = 1 →
    MarkovMixing.transportDist (fun a b => (hamming a b : ℝ))
      (SpinGirth5.pin μ Λ x) (SpinGirth5.pin μ Λ y) ≤ C

def InfluenceIndex (μ : (V → Fin q) → ℝ) (Λ : Finset V) :=
  {i : V × Fin q // i.1 ∉ Λ ∧ 0 < oneSite μ i.1 i.2}

instance (μ : (V → Fin q) → ℝ) (Λ : Finset V) : Fintype (InfluenceIndex μ Λ) :=
  inferInstanceAs (Fintype {i : V × Fin q // i.1 ∉ Λ ∧ 0 < oneSite μ i.1 i.2})

def influence (μ : (V → Fin q) → ℝ) (Λ : Finset V) :
    Matrix (InfluenceIndex μ Λ) (InfluenceIndex μ Λ) ℝ :=
  fun i j => if i.val.1 = j.val.1 then 0 else
    twoSite μ i.val.1 j.val.1 i.val.2 j.val.2 / oneSite μ i.val.1 i.val.2 -
      oneSite μ j.val.1 j.val.2

def symmetricInfluence (μ : (V → Fin q) → ℝ) (Λ : Finset V) :
    Matrix (InfluenceIndex μ Λ) (InfluenceIndex μ Λ) ℝ :=
  fun i j => if i.val.1 = j.val.1 then 0 else
    (twoSite μ i.val.1 j.val.1 i.val.2 j.val.2 -
      oneSite μ i.val.1 i.val.2 * oneSite μ j.val.1 j.val.2) /
      Real.sqrt (oneSite μ i.val.1 i.val.2 * oneSite μ j.val.1 j.val.2)

def InfluenceBound (μ : (V → Fin q) → ℝ) (Λ : Finset V) (γ : ℝ) : Prop :=
  ∀ z : InfluenceIndex μ Λ → ℝ,
    (∑ i, ∑ j, z i * symmetricInfluence μ Λ i j * z j) ≤ γ * ∑ i, (z i)^2

def SpectralIndependent (μ : (V → Fin q) → ℝ) (γ : ℝ) : Prop :=
  ∀ (Λ : Finset V) (x : V → Fin q), Feasible μ Λ x →
    InfluenceBound (SpinGirth5.pin μ Λ x) Λ γ

end RandomColorMix269.Mixing


