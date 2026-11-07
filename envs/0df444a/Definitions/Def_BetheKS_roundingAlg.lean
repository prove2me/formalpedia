-- Prove2me | Definitions.Def_BetheKS_roundingAlg
-- name    : BetheKS_roundingAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:36:37.580042+00:00
-- url     : https://prove2.me/theorems/0560bea3-c2d4-4e16-aa45-d9be8f1534cc
-- title:
--   The randomized rounding of Theorem 2.3 and the event that it succeeds
-- statement:
--   Let $c$ be a family of constants and set
--   $$
--   S:=\sum_{i\ge2,\ |\mu_i|>\sqrt d}c_{\mu_i}^2,\qquad m:=|\{i\ge2:|\mu_i|>\sqrt d\}|,\qquad L:=\sqrt{\pi_{\min}S},\qquad M:=\frac{4\sqrt2(r-1)}{L}.
--   $$
--   Given a graph $G_n$, let $U_n\in\mathbb R^{n\times m}$ have orthonormal columns spanning $E_n\cap\mathbf 1^\perp$, put $x_u:=\sqrt n\,U_n(u,\cdot)^{\mathsf T}$ and $f_u:=x_u/\max\{M,\|x_u\|_2\}$, fix $R\in\mathbb R^{r\times m}$ with $R^{\mathsf T}R=I_m$ and $R^{\mathsf T}\mathbf 1=0$, and sample independently over vertices
--   $$
--   \mathbb P(\widehat\sigma_n(u)=b\mid G_n)=\frac{1+(Rf_u)_b}{r},\qquad b\in[r].
--   $$
--   The file defines this law, the joint probability over $G_n\sim\mathrm{SBM}_n(P,\pi)$ and $\widehat\sigma_n$, and the statement **"the rounding achieves overlap $\beta$"**: for every choice the algorithm leaves open, $\mathbb P(\operatorname{ov}(\sigma,\widehat\sigma_n)\ge\beta)\to1$.
--
--   **Formalization Note** "Every choice" means: every exact-size label sequence, every choice of increasing orthonormal eigenbases of $H(\pm\sqrt d,G)$ for each graph, every orthonormal basis $U_n$, every admissible $R$, and every fallback law used when $\dim(E_n\cap\mathbf 1^\perp)\ne m$ (an event App. F excludes asymptotically). The sums over $i\ge2$ are over the informative eigenvalues with multiplicity, one copy of $\mu_1=d$ removed. The algorithm sees the graph and the fixed parameters, never $\sigma$.
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), App. F, proof of Theorem 2.3, p.26

import Mathlib
import Definitions.Def_BetheKS_sbmProb
import Definitions.Def_BetheKS_outlierSpace
import Definitions.Def_BetheKS_centeredOverlap

set_option autoImplicit false

namespace BetheKS

variable {r : ℕ}

/-- The informative eigenvalues other than `µ₁ = d`: the multiset `{µᵢ : i ≥ 2, |µᵢ| > √d}` of
Theorem 2.3, p.5 (with multiplicity; one copy of `d` is removed, the others stay). -/
noncomputable def infAfterFirst (p : SBMParams r) : Multiset ℝ := (informative p).erase p.d

/-- `S := ∑_{i ≥ 2, |µᵢ| > √d} c²_{µᵢ}` (Theorem 2.3, p.5; App. F, p.26). -/
noncomputable def sumS (p : SBMParams r) (c : ℝ → ℝ) : ℝ :=
  ((infAfterFirst p).map (fun μ => c μ ^ 2)).sum

/-- `m := |{i ≥ 2 : |µᵢ| > √d}|` (App. F, p.26). -/
noncomputable def mDim (p : SBMParams r) : ℕ := Multiset.card (infAfterFirst p)

/-- The rounding law of App. F, p.26, given an orthonormal basis `U = (U₁,…,U_m)` of `Eₙ ∩ 1^⊥`
and `R ∈ ℝ^{r×m}`: with `xᵤ := √n Uₙ(u,·)ᵀ`, `L := √(π_min S)`, `M := 4√2 (r−1)/L` and
`fᵤ := xᵤ / max{M, ‖xᵤ‖₂}`, the labels are independent over vertices with
`P(σ̂(u) = b) = (1 + (R fᵤ)_b)/r`. `roundWeight … σh` is the probability of the labeling `σh`. -/
noncomputable def roundWeight (p : SBMParams r) (c : ℝ → ℝ) {n : ℕ}
    (U : Fin (mDim p) → EuclideanSpace ℝ (Fin n)) (R : Matrix (Fin r) (Fin (mDim p)) ℝ)
    (σh : Fin n → Fin r) : ℝ :=
  let L : ℝ := Real.sqrt (piMin p * sumS p c)
  let M : ℝ := 4 * Real.sqrt 2 * ((r : ℝ) - 1) / L
  let x : Fin n → EuclideanSpace ℝ (Fin (mDim p)) := fun u => WithLp.toLp 2 (fun j => Real.sqrt n * U j u)
  let f : Fin n → EuclideanSpace ℝ (Fin (mDim p)) := fun u => (1 / max M ‖x u‖) • x u
  ∏ u, (1 + R.mulVec (fun j => f u j) (σh u)) / r

/-- A matrix `R ∈ ℝ^{r×m}` with `RᵀR = I_m` and `Rᵀ1 = 0` (App. F, p.26). -/
def IsRoundingMatrix (p : SBMParams r) (R : Matrix (Fin r) (Fin (mDim p)) ℝ) : Prop :=
  R.transpose * R = 1 ∧ R.transpose.mulVec (fun _ => (1 : ℝ)) = 0

/-- **The rounding algorithm of Theorem 2.3** — Dong, McKenzie, arXiv:2610.41802 (held version,
sha256 4da41e16…), App. F, p.26: the law of the output `σ̂ₙ` given the graph. When
`dim(Eₙ ∩ 1^⊥) = m`, it is `roundWeight` for the chosen basis `U` of `Eₙ ∩ 1^⊥`; otherwise the fallback
law `fb`.

**Formalization Note.** The algorithm sees only the graph (through the chosen eigenbases `Bp`, `Bm`
of `H(±√d, G)`, the chosen basis `U`, the fixed `R` and the fallback) and the fixed parameters, never
`σ`. On the event `dim(Eₙ ∩ 1^⊥) ≠ m`, which App. F excludes asymptotically, it outputs `fb`. -/
noncomputable def algWeight (p : SBMParams r) (c : ℝ → ℝ) {n : ℕ} {G : SimpleGraph (Fin n)}
    (Bp : IncEigenbasis (bh (Real.sqrt p.d) G)) (Bm : IncEigenbasis (bh (-Real.sqrt p.d) G))
    (U : Fin (mDim p) → EuclideanSpace ℝ (Fin n)) (R : Matrix (Fin r) (Fin (mDim p)) ℝ)
    (fb : (Fin n → Fin r) → ℝ) (σh : Fin n → Fin r) : ℝ :=
  if Module.finrank ℝ ↥(allOutliers p Bp Bm ⊓ (Submodule.span ℝ {onesVec n})ᗮ) = mDim p then
    roundWeight p c U R σh
  else fb σh

/-- `U` is an orthonormal basis of `Eₙ ∩ 1^⊥` whenever that space has dimension `m` (App. F, p.26). -/
def IsBasisChoice (p : SBMParams r) {n : ℕ} {G : SimpleGraph (Fin n)}
    (Bp : IncEigenbasis (bh (Real.sqrt p.d) G)) (Bm : IncEigenbasis (bh (-Real.sqrt p.d) G))
    (U : Fin (mDim p) → EuclideanSpace ℝ (Fin n)) : Prop :=
  Module.finrank ℝ ↥(allOutliers p Bp Bm ⊓ (Submodule.span ℝ {onesVec n})ᗮ) = mDim p →
    Orthonormal ℝ U ∧
      Submodule.span ℝ (Set.range U) = allOutliers p Bp Bm ⊓ (Submodule.span ℝ {onesVec n})ᗮ

/-- `q` is a probability law on labelings `[n] → [r]`. -/
def IsLabelLaw {n : ℕ} (q : (Fin n → Fin r) → ℝ) : Prop :=
  (∀ σh, 0 ≤ q σh) ∧ ∑ σh, q σh = 1

/-- The joint probability that the output `σ̂ ∼ alg(G)` satisfies `E`, for `G ∼ SBMₙ(P, π)` with
labels `σ` and `σ̂` drawn from `alg G` given `G`. -/
noncomputable def jointProb (p : SBMParams r) {n : ℕ} (σ : Fin n → Fin r)
    (alg : SimpleGraph (Fin n) → (Fin n → Fin r) → ℝ) (E : (Fin n → Fin r) → Prop) : ℝ :=
  ∑ ω : EdgeSample n, sampleWeight p σ ω *
    ∑ σh : Fin n → Fin r, alg (graphOf ω) σh * ({σh | E σh} : Set (Fin n → Fin r)).indicator 1 σh

/-- **The App. F rounding achieves centered overlap at least `β` with probability tending to one**,
for every choice the algorithm leaves open (App. F, p.26): every sequence of exact-size label maps
`σₙ` (`n ∈ 𝒩_π`), every choice of increasing orthonormal eigenbases `Bp`, `Bm` of `H(±√d, G)` for each
graph, every choice of the orthonormal basis `U` of `Eₙ ∩ 1^⊥`, every `R` with `RᵀR = I_m`, `Rᵀ1 = 0`,
and every fallback law. The probability is over `Gₙ ∼ SBMₙ(P, π)` and `σ̂ₙ ∼ alg(Gₙ)` jointly. -/
def RoundingSucceeds (p : SBMParams r) (c : ℝ → ℝ) (β : ℝ) : Prop :=
  ∀ σs : ∀ n : ℕ, Fin n → Fin r, IsExactSeq p σs →
  ∀ Bp : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), IncEigenbasis (bh (Real.sqrt p.d) G),
  ∀ Bm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), IncEigenbasis (bh (-Real.sqrt p.d) G),
  ∀ U : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), Fin (mDim p) → EuclideanSpace ℝ (Fin n),
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsBasisChoice p (Bp n G) (Bm n G) (U n G)) →
  ∀ R : Matrix (Fin r) (Fin (mDim p)) ℝ, IsRoundingMatrix p R →
  ∀ fb : ∀ n : ℕ, SimpleGraph (Fin n) → (Fin n → Fin r) → ℝ,
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsLabelLaw (fb n G)) →
    Filter.Tendsto
      (fun n => jointProb p (σs n)
        (fun G => algWeight p c (Bp n G) (Bm n G) (U n G) R (fb n G))
        (fun σh => β ≤ ov p.pi (σs n) σh))
      (sizeFilter p) (nhds 1)

end BetheKS


