-- Prove2me | Definitions.Def_SpinGirth5_starModel
-- name    : SpinGirth5_starModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:48.435747+00:00
-- url     : https://prove2.me/theorems/59d6f447-b49d-4b58-8035-4cda1f843d2d
-- title:
--   The star of §4–§5: leaves, $K_0$, $K_1$, the star law (16), likelihood ratio $L_\rho$, influence matrix $\Psi_i$, Condition 26
-- statement:
--   Let the star have centre $v$ and leaves $N(v)=\{1,\dots,d\}$; a configuration of $N[v]$ is a centre colour together with $d$ leaf colours.
--
--   1. For a distribution $\nu$ on $[q]^{N[v]}$, the **leaves are conditionally independent given the centre** when, for every centre colour $\mathfrak c$, the conditional law of the leaves is the product of its one-leaf marginals.
--   2. In $(\mathbf 1^\perp,\langle\cdot,\cdot\rangle_\nu)$: $K_0:=\operatorname{Ker}(L_{N(v)})$ and $K_1:=\operatorname{Ker}(L_{N(v)}-I)$.
--   3. The **star law** (16): given a multi-spin system $(A,\lambda)$ and leaf laws $p_1,\dots,p_d$ on $[q]$,
--   $$\nu(v\mathfrak c,\sigma)\propto\lambda_{\mathfrak c}\prod_{i=1}^dA_{\mathfrak c,\sigma_i}\,p_i(\sigma_i),\qquad \nu_v(\mathfrak c)=\nu(X_v=\mathfrak c).$$
--   In the paper $\nu=\mu^\tau_{G,N[v]}$ and $p_i=\mu^\tau_{G-v,i}$ (13).
--   4. The **likelihood ratio** (Definition 28) $L_\rho(x)=\nu_{N(v)}(x)/\rho(x)$ with $\rho=\bigotimes_ip_i$.
--   5. $L^{\mathfrak c}_i(\mathfrak a)=A_{\mathfrak c,\mathfrak a}/(Ap_i)(\mathfrak c)$ and the **influence matrix** $\Psi_i(\mathfrak c,\mathfrak d)=\operatorname{Cov}_{p_i}(L^{\mathfrak c}_i,L^{\mathfrak d}_i)$.
--   6. **Condition 26.** $\alpha\ge1$, $\varepsilon\in(0,1]$, the $\alpha$-marginal bound $(Bp_i)(\mathfrak c)\le\alpha/\Delta$ and $(B\nu_v)(\mathfrak c)\le\alpha/\Delta$, and the $\varepsilon$-contraction $\|\operatorname{diag}(\sum_ip_i)^{1/2}B\operatorname{diag}(\nu_v)^{1/2}\|_2^2\le(1-\varepsilon)/\Delta$.
--
--   These are the objects of the Fourier analysis on a star (§4) and of the block estimates of §5.
--
--   **Formalization Note** The centre is `none` and the leaves are `some i`, `i : Fin d`, so configurations are maps `Option (Fin d) → Fin q`. Conditional independence of the leaves is written as $\nu(\mathfrak c,x)\,\nu_v(\mathfrak c)^d=\nu_v(\mathfrak c)\prod_i\nu(X_v=\mathfrak c,X_i=x_i)$. $K_0,K_1$ impose their kernel conditions on $\operatorname{supp}\nu$. The star law is normalized by $\sum_x(\text{weight})$, assumed positive wherever it is used; $L_\rho$ takes Lean's value $0$ off $\operatorname{supp}\rho$, where $\nu_{N(v)}$ vanishes too. The spectral-norm bound of the $\varepsilon$-contraction is a quadratic-form bound, and $\Delta$ is a natural-number parameter.
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, §4, pp.16–17; Eqs. (13), (16), pp.19, 21; Condition 26, p.20; Definition 28, p.21; p.22

import Mathlib
import Definitions.Def_SpinGirth5_Interaction
import Definitions.Def_SpinGirth5_heatBath

/-!
The star of §4–§5 of Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs
with Girth At Least Five*, arXiv:2608.25491: the centre `v` is `none` and the leaves
`N(v) = {1, …, d}` are `some i`, `i : Fin d`. A configuration of `N[v]` is a map
`Option (Fin d) → Fin q`.
-/

namespace SpinGirth5

open Finset Matrix

variable {q d : ℕ}

/-- The leaves `N(v) = {1, …, d}` of the star (all sites but the centre `none`). -/
def leaves (d : ℕ) : Finset (Option (Fin d)) :=
  univ.erase none

/-- The centre marginal `ν_v(c) = ν(X_v = c)`. -/
def centerMarginal (ν : (Option (Fin d) → Fin q) → ℝ) (c : Fin q) : ℝ :=
  ∑ x ∈ univ.filter (fun x : Option (Fin d) → Fin q => x none = c), ν x

/-- The joint mass `ν(X_v = c, X_i = a)` of the centre and the leaf `i`. -/
def centerLeafMarginal (ν : (Option (Fin d) → Fin q) → ℝ) (i : Fin d) (c a : Fin q) : ℝ :=
  ∑ x ∈ univ.filter (fun x : Option (Fin d) → Fin q => x none = c ∧ x (some i) = a), ν x

/-- **Conditional on `X_v`, the leaves `(X_i)_{i∈N(v)}` are independent** (Chen, Liu,
arXiv:2608.25491, §4, p.16: "Assume that, conditional on Xv, the leaves (Xi)i∈N(v) are
independent").

**Formalization Note** Written as `ν(c, x) ν_v(c)^d = ν_v(c) ∏_i ν(X_v = c, X_i = x_i)`, which
for `ν_v(c) > 0` says `ν(x | c) = ∏_i ν(x_i | c)` and is automatic when `ν_v(c) = 0`. -/
def LeavesCondIndep (ν : (Option (Fin d) → Fin q) → ℝ) : Prop :=
  ∀ x : Option (Fin d) → Fin q,
    ν x * centerMarginal ν (x none) ^ d =
      centerMarginal ν (x none) * ∏ i, centerLeafMarginal ν i (x none) (x (some i))

/-- `h ∈ K₀ := Ker(L_{N(v)})` inside `1⊥ ⊆ L²(ν)` (Chen, Liu, arXiv:2608.25491, §4, p.17).

**Formalization Note** Elements of `L²(ν)` are functions on `supp ν`; the kernel condition is
imposed at every configuration of positive mass. -/
def K0 (ν : (Option (Fin d) → Fin q) → ℝ) (h : (Option (Fin d) → Fin q) → ℝ) : Prop :=
  IsCentered ν h ∧ ∀ x, ν x ≠ 0 → lapSum ν (leaves d) h x = 0

/-- `k ∈ K₁ := Ker(L_{N(v)} − I)` inside `1⊥ ⊆ L²(ν)` (Chen, Liu, arXiv:2608.25491, §4, p.17),
with the same support convention as `K0`. -/
def K1 (ν : (Option (Fin d) → Fin q) → ℝ) (k : (Option (Fin d) → Fin q) → ℝ) : Prop :=
  IsCentered ν k ∧ ∀ x, ν x ≠ 0 → lapSum ν (leaves d) k x = k x

/-- The star configuration with centre colour `c` and leaf colours `y`. -/
def joinCfg (c : Fin q) (y : Fin d → Fin q) : Option (Fin d) → Fin q :=
  fun o => Option.elim o c y

/-- The leaf part `x_{N(v)} = (x_i)_{i∈[d]}` of a star configuration. -/
def leafCfg (x : Option (Fin d) → Fin q) : Fin d → Fin q :=
  fun i => x (some i)

/-- The unnormalized star law (16): `λ_c ∏_i A_{c,σ_i} p_i(σ_i)` (Chen, Liu, arXiv:2608.25491,
Eq. (16), p.21: "ν(vc, σ) ∝ λc ∏_i A_{c,σi} pi(σi), ∀c ∈ [q], σ ∈ [q]^d"). -/
noncomputable def starWeight (S : Interaction q) (p : Fin d → Fin q → ℝ)
    (x : Option (Fin d) → Fin q) : ℝ :=
  S.lam (x none) * ∏ i, S.A (x none) (x (some i)) * p i (x (some i))

/-- The **star law** `ν` of (13)/(16), normalized: `ν = μ^τ_{G,N[v]}` with leaf laws
`p_i = μ^τ_{G−v,i}` (Chen, Liu, arXiv:2608.25491, Eqs. (13), (16), pp.19, 21).

**Formalization Note** Any distributions `p_i` on `[q]` and any spin system `(A, λ)` are
allowed; it is a probability law when `0 < ∑_x starWeight S p x`, which every statement
assumes. -/
noncomputable def starDist (S : Interaction q) (p : Fin d → Fin q → ℝ)
    (x : Option (Fin d) → Fin q) : ℝ :=
  starWeight S p x / ∑ y, starWeight S p y

/-- The product law `ρ = ⊗_i p_i` on the leaves. -/
def productLaw (p : Fin d → Fin q → ℝ) (y : Fin d → Fin q) : ℝ :=
  ∏ i, p i (y i)

/-- The likelihood ratio `L_ρ(y) := ν_{N(v)}(y)/ρ(y)` of Definition 28 (Chen, Liu,
arXiv:2608.25491, Definition 28, p.21).

**Formalization Note** Defined on `supp ρ`; off it Lean returns `0`, and `ν_{N(v)}` vanishes
there too, so no statement depends on that value. -/
noncomputable def likelihoodRatio (S : Interaction q) (p : Fin d → Fin q → ℝ)
    (y : Fin d → Fin q) : ℝ :=
  (∑ c, starDist S p (joinCfg c y)) / productLaw p y

/-- The ratio `L^c_i(a) := A_{c,a}/(A p_i)(c)` (Chen, Liu, arXiv:2608.25491, p.22). -/
noncomputable def leafRatio (A : Matrix (Fin q) (Fin q) ℝ) (p : Fin q → ℝ) (c a : Fin q) : ℝ :=
  A c a / (A *ᵥ p) c

/-- The covariance `Cov_p(f, g) = E_p[fg] − E_p[f] E_p[g]` under a distribution `p` on `[q]`. -/
def covAt (p : Fin q → ℝ) (f g : Fin q → ℝ) : ℝ :=
  ∑ a, p a * f a * g a - (∑ a, p a * f a) * ∑ a, p a * g a

/-- The influence matrix `Ψ_i(c, d) := Cov_{p_i}(L^c_i, L^d_i)` (Chen, Liu, arXiv:2608.25491,
p.22), for a leaf law `p = p_i`. -/
noncomputable def Psi (A : Matrix (Fin q) (Fin q) ℝ) (p : Fin q → ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  fun c e => covAt p (leafRatio A p c) (leafRatio A p e)

/-- The **α-marginal bound** of Condition 26: `(B p_i)(c) ≤ α/Δ` and `(B ν_v)(c) ≤ α/Δ` for every
leaf `i` and colour `c` (Chen, Liu, arXiv:2608.25491, Condition 26, p.20). -/
def MarginalBound (S : Interaction q) (p : Fin d → Fin q → ℝ) (νv : Fin q → ℝ) (α : ℝ)
    (Δ : ℕ) : Prop :=
  (∀ i c, (S.B *ᵥ p i) c ≤ α / Δ) ∧ ∀ c, (S.B *ᵥ νv) c ≤ α / Δ

/-- **Condition 26**: `α ≥ 1`, `ε ∈ (0, 1]`, the α-marginal bound, and the ε-contraction
`‖diag(∑_i p_i)^{1/2} B diag(ν_v)^{1/2}‖₂² ≤ (1 − ε)/Δ` (Chen, Liu, arXiv:2608.25491,
Condition 26, p.20).

**Formalization Note** The squared spectral norm bound is written as
`∑_a s(a) (∑_c B_{a,c} √ν_v(c) y(c))² ≤ (1 − ε)/Δ · ∑_c y(c)²` for all `y ∈ ℝ^q`, with
`s = ∑_i p_i`. `Δ` is a natural-number parameter (the maximum degree of the ambient graph). -/
def Condition26 (S : Interaction q) (p : Fin d → Fin q → ℝ) (νv : Fin q → ℝ) (α ε : ℝ)
    (Δ : ℕ) : Prop :=
  1 ≤ α ∧ 0 < ε ∧ ε ≤ 1 ∧ MarginalBound S p νv α Δ ∧
  ∀ y : Fin q → ℝ,
    ∑ a, (∑ i, p i a) * (∑ c, S.B a c * Real.sqrt (νv c) * y c) ^ 2 ≤
      (1 - ε) / Δ * ∑ c, y c ^ 2

end SpinGirth5


