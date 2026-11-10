-- Prove2me | Definitions.Def_TensorRankN2M_ThreeTwoM_N2M
-- name    : TensorRankN2M_ThreeTwoM_N2M
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:16:55.731009+00:00
-- url     : https://prove2.me/theorems/80cede15-78d2-409e-842c-f1476d70a474
-- title:
--   The maps of §4 for a decomposition of ⟨n,2,m⟩: U, J, g, ℓ, L, h, H, Φ and ker(W)/J
-- statement:
--   Fix an $R$-rank decomposition of $\langle n,2,m\rangle$ over $\mathbb F$, with $D,\mathcal B,W,f_i$ as before ($f_i(x)=D(e_{i,0})\mathcal B(x)$, $e_{i,0}$ of shape $n\times 2$). Define:
--
--   - $U\subseteq\mathbb F^{2\times m}$, the matrices whose top row (row $0$) is zero; $\dim U=m$.
--   - $J=f_0(U)\subseteq\mathbb F^R$.
--   - $g(x)=D(e_{0,1})\mathcal B(x)-D(e_{0,0})\mathcal B(e_{0,1}x)$ for $x\in\mathbb F^{2\times m}$, where the first $e_{0,1}$ has shape $n\times 2$ and the second $2\times 2$.
--   - $\ell:U^{n-1}\to\mathbb F^R$, $\ell(u_1,\dots,u_{n-1})=\sum_{1\le i<n} f_i(u_i)$.
--   - $U^{\wedge(n-1)}$, the alternating arrays indexed by $\{1,\dots,n-1\}$ with entries in $U$, and $h:U^{\wedge(n-1)}\to(\mathbb F^R)^{n-1}$ the skew augmentation of $\ell$: $h(c)=(\ell(c_{1,:}),\dots,\ell(c_{n-1,:}))$.
--   - The quotient maps $L(u)=\ell(u)+J$ and $H(c)=h(c)+_{\mathrm{elt}}J$ (componentwise), indexed $1,\dots,n-1$.
--   - $$\Phi:U^{n-1}\oplus U^{\wedge(n-1)}\to \mathbb F^R/J\ \oplus\ (\mathbb F^R/J)^{n-1},\qquad \Phi(u,c)=\big(\ell(u),\ \dots,\ -g(u_i)+h(c)_i,\ \dots\big)_{1\le i<n}+_{\mathrm{elt}}J.$$
--   - $\ker(W)/J$.
--
--   For a decomposition, $f_i(U)$ and $g(U)$ lie in $\ker W$ and $J\subseteq\ker W$ (p. 3), so $\ell$, $L$, $H$ and $\Phi$ take values in $\ker W$, $\ker(W)/J$, $(\ker(W)/J)^{n-1}$ and $\operatorname{im}(L)\oplus(\ker(W)/J)^{n-1}$, which is how the paper writes their codomains. The rank $\operatorname{rk}$ of a map is the dimension of its image.
--
--   **Formalization Note.** The index set $\{1,\dots,n-1\}$ is `Idx n = {i : Fin n // i ≠ 0}`, and $U^{n-1}$ is `Idx n → U 𝔽 m`. The maps `ell`, `L`, `h`, `H`, `Φ` are given the ambient codomains $\mathbb F^R$, $\mathbb F^R/J$, $(\mathbb F^R)^{n-1}$, $(\mathbb F^R/J)^{n-1}$, $(\mathbb F^R/J)\times(\mathbb F^R/J)^{n-1}$; the paper's codomains are subspaces of these, so kernels and ranks are unchanged. `KerWModJ` is $\ker W$ modulo $J\cap\ker W$, which is $\ker(W)/J$ because $J\subseteq\ker W$. `[NeZero n]` makes the index $0$ available.
-- source:
--   Jason Yang, New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra, STOC 2027 submission (manuscript of October 2026, sha256 6c1df229…), p. 3 (U, J, g); p. 4, §4 (for ⟨n,2,m⟩); p. 5 (ℓ, U^{∧(n−1)}, h, L, H, Φ)

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition
import Definitions.Def_TensorRankN2M_ThreeTwoM_Normalization
import Definitions.Def_TensorRankN2M_ThreeTwoM_SkewAugmentation

/-!
# The maps of §4 for a decomposition of ⟨n,2,m⟩: U, J, g, ℓ, L, h, H, Φ, ker W / J

Jason Yang, *New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra*,
STOC 2027 submission (manuscript of October 2026), p. 3 (U, J, g for ⟨2,2,m⟩), p. 4 (§4:
"define U, f_i, g, J similarly"), p. 5 (ℓ, U^{∧(n−1)}, h, L, H, Φ).

Conventions.
* `Idx n = {i : Fin n // i ≠ 0}` is the index set `{1, …, n−1}` of `ℓ`, `h`, `H` and of the last
  `n−1` components of `Φ`; `U^{n−1}` is `Idx n → U`.
* `U 𝔽 m` is the space of `2 × m` matrices whose top row (row `0`) is `0`.
* `J = f_0(U)`; `g(x) = D(e_{0,1})ℬ(x) − D(e_{0,0})ℬ(e_{0,1}x)` with the first `e_{0,1}` of shape
  `n × 2` and the second of shape `2 × 2`.
* `ℓ(u) = ∑_{1≤i<n} f_i(u_i)`, taken with values in `𝔽^R` (the paper's codomain is `ker W`, which
  contains `f_i(U)`); `L(u) = ℓ(u) + J`, `h` is the skew augmentation of `ℓ`, and
  `H(c) = h(c) +elt J`, all with values in `𝔽^R / J` (the paper's `ker W / J`, a subspace of it).
* `Φ(u, c) = (ℓ(u), …, −g(u_i) + h(c)_i, …) +elt J`, with values in
  `(𝔽^R / J) × (𝔽^R / J)^{n−1}` (the paper's codomain `im(L) ⊕ (ker W / J)^{n−1}` is a subspace).
* `KerWModJ d = ker W / J`, realised as `ker W` modulo `J ∩ ker W`.
-/

namespace TensorRankN2M.ThreeTwoM

/-- The index set `{1, …, n−1}` (as the nonzero elements of `Fin n`). -/
abbrev Idx (n : ℕ) [NeZero n] : Type := {i : Fin n // i ≠ 0}

/-- `U`: the space of `2 × m` matrices whose top row (row `0`) is zero (p. 3). -/
def U (𝔽 : Type*) [Field 𝔽] (m : ℕ) : Submodule 𝔽 (Matrix (Fin 2) (Fin m) 𝔽) where
  carrier := {x | ∀ j, x 0 j = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j
    simp [hx j, hy j]
  smul_mem' := by
    intro a x hx j
    simp [hx j]

namespace Decomposition

variable {𝔽 : Type*} [Field 𝔽] {n m R : ℕ} [NeZero n] (d : Decomposition 𝔽 n 2 m R)

/-- `J = f_0(U) ⊆ 𝔽^R` (p. 3). -/
def J : Submodule 𝔽 (Fin R → 𝔽) := (U 𝔽 m).map (d.f 0)

/-- `g(x) = D(e_{0,1})ℬ(x) − D(e_{0,0})ℬ(e_{0,1}x)`; the first `e_{0,1}` has shape `n × 2`, the
second `2 × 2` (p. 3). -/
def g : Matrix (Fin 2) (Fin m) 𝔽 →ₗ[𝔽] (Fin R → 𝔽) :=
  (d.D (Matrix.single 0 1 1)).mulVecLin ∘ₗ d.Bvec -
    (d.D (Matrix.single 0 0 1)).mulVecLin ∘ₗ d.Bvec ∘ₗ
      sandwich (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : 𝔽)) (1 : Matrix (Fin m) (Fin m) 𝔽)

/-- `ℓ : U^{n−1} → 𝔽^R`, `ℓ(u_1, …, u_{n−1}) = ∑_{1≤i<n} f_i(u_i)` (p. 5). -/
def ell : (Idx n → U 𝔽 m) →ₗ[𝔽] (Fin R → 𝔽) :=
  ∑ i : Idx n, d.f i.1 ∘ₗ (U 𝔽 m).subtype ∘ₗ LinearMap.proj i

/-- `L(u) = ℓ(u) + J` (p. 5). -/
def L : (Idx n → U 𝔽 m) →ₗ[𝔽] (Fin R → 𝔽) ⧸ d.J :=
  d.J.mkQ ∘ₗ d.ell

/-- `h : U^{∧(n−1)} → (𝔽^R)^{n−1}`, the skew augmentation of `ℓ` (p. 5). -/
def h : SkewArrays 𝔽 (U 𝔽 m) (Idx n) →ₗ[𝔽] (Idx n → Fin R → 𝔽) :=
  skewAug d.ell

/-- `H(c) = h(c) +elt J`, componentwise (p. 5). -/
def H : SkewArrays 𝔽 (U 𝔽 m) (Idx n) →ₗ[𝔽] (Idx n → (Fin R → 𝔽) ⧸ d.J) :=
  LinearMap.pi fun i => d.J.mkQ ∘ₗ LinearMap.proj i ∘ₗ d.h

/-- `Φ(u, c) = (ℓ(u), …, −g(u_i) + h(c)_i, …_{1≤i<n}) +elt J` (p. 5). -/
def Φ : (Idx n → U 𝔽 m) × SkewArrays 𝔽 (U 𝔽 m) (Idx n) →ₗ[𝔽]
    ((Fin R → 𝔽) ⧸ d.J) × (Idx n → (Fin R → 𝔽) ⧸ d.J) :=
  LinearMap.prod (d.L ∘ₗ LinearMap.fst 𝔽 _ _)
    (LinearMap.pi fun i => d.J.mkQ ∘ₗ
      (-(d.g ∘ₗ (U 𝔽 m).subtype ∘ₗ LinearMap.proj i ∘ₗ LinearMap.fst 𝔽 _ _) +
        LinearMap.proj i ∘ₗ d.h ∘ₗ LinearMap.snd 𝔽 _ _))

/-- `ker(W) / J` (p. 3, p. 4), as `ker W` modulo `J ∩ ker W`. -/
abbrev KerWModJ : Type _ :=
  ↥(LinearMap.ker d.W) ⧸ d.J.comap (LinearMap.ker d.W).subtype

end Decomposition

end TensorRankN2M.ThreeTwoM


