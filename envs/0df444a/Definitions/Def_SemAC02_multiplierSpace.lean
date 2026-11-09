-- Prove2me | Definitions.Def_SemAC02_multiplierSpace
-- name    : SemAC02_multiplierSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:26:59.821313+00:00
-- url     : https://prove2.me/theorems/df98d4d3-5cd2-438d-a074-3c33bab79cbd
-- title:
--   The multiplier space $U$ of (45) and the fibres $\Omega(z)$
-- statement:
--   Let $g_0:\{0,1\}^m\to\{0,1\}$ and $L=\{S\subseteq[m]: g_0(\mathbf 1_S)=1\}$. For $S=(S_1,\dots,S_n)\in L^n$ put $x_S=\prod_{i=1}^n\prod_{j\in S_i}x_{i,j}$, a monomial in the $v=nm$ lifted variables. The **multiplier space** is
--   $$
--   U=\operatorname{span}\Bigl\{x_S: S\in L^n,\ \sum_i|S_i|\le k\Bigr\}\subseteq\mathcal B_v .
--   $$
--   Without the degree cutoff the span is $\operatorname{span}\{x_T:T\in L^n\}$. With $\Omega_0=\{X:g_0(X)=1\}$ and $\Omega_1=\{X:g_0(\overline X)=1\}$, the **fibre** of $z\in\{0,1\}^n$ is $\Omega(z)=\prod_i\Omega_{z_i}$.
--
--   **Formalization Note** $S\in L^n$ is encoded as the set of lifted variables $(i,j)$ with $j\in S_i$, so $x_S$ is `AC02Frege.xMon` of that set and $\sum_i|S_i|$ its cardinality. The gadget enters as a Boolean function; for a circuit $g$ use its evaluation.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §8.2, (45), and pp.64–65, p.64 (PDF p.66)

import Mathlib
import Definitions.Def_AC02Frege_ML

namespace SemAC02

/-- The indicator vector `1_S ∈ {0,1}^m` of `S ⊆ [m]`. -/
def indicatorVec {m : ℕ} (S : Finset (Fin m)) : Fin m → Bool := fun j => decide (j ∈ S)

/-- The support `S_i ⊆ [m]` in block `i` of a set `A` of lifted variables `(i, j)`. -/
def blockSection {n m : ℕ} (A : Finset (Fin n × Fin m)) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => (i, j) ∈ A)

/-- `A ⊆ [n] × [m]`, read as `S = (S_1, …, S_n)` with `S_i` its block sections, lies in `L^n`
(§8.2, p.64): every block section belongs to `L = {S ⊆ [m] : g_0(1_S) = 1}`. -/
def IsLnSupport {n m : ℕ} (g0 : (Fin m → Bool) → Bool) (A : Finset (Fin n × Fin m)) : Prop :=
  ∀ i : Fin n, g0 (indicatorVec (blockSection A i)) = true

instance {n m : ℕ} (g0 : (Fin m → Bool) → Bool) : DecidablePred (IsLnSupport (n := n) g0) :=
  fun A => by unfold IsLnSupport; infer_instance

/-- The **multiplier space** `U` of (45) (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret,
*Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission), §8.2,
(45), p.64): with `L = {S ⊆ [m] : g_0(1_S) = 1}` and `x_S = ∏_{i=1}^n ∏_{j∈S_i} x_{i,j}` for
`S ∈ L^n`,
`U = span{x_S : S ∈ L^n, ∑_i |S_i| ≤ k}` inside `B_v`, `v = nm`.

**Formalization Note** The lifted variables are `Fin n × Fin m`; `S ∈ L^n` is encoded as the set
`A` of variables `(i, j)` with `j ∈ S_i`, so `x_S = AC02Frege.xMon A` and `∑_i |S_i| = |A|`. The
gadget `g_0` is given as a Boolean function; for a circuit `g` use `fun X => g.eval X`. -/
noncomputable def multiplierSpace {m : ℕ} (g0 : (Fin m → Bool) → Bool) (n k : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n × Fin m) (ZMod 2)) :=
  Submodule.span (ZMod 2)
    (AC02Frege.xMon '' {A : Finset (Fin n × Fin m) | A.card ≤ k ∧ IsLnSupport g0 A})

/-- `span{x_T : T ∈ L^n}` (Lemma 8.6, p.65): the multiplier space without degree cutoff. -/
noncomputable def lnSpan {m : ℕ} (g0 : (Fin m → Bool) → Bool) (n : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n × Fin m) (ZMod 2)) :=
  Submodule.span (ZMod 2) (AC02Frege.xMon '' {A : Finset (Fin n × Fin m) | IsLnSupport g0 A})

/-- The fibre `Ω(z) = ∏_i Ω_{z_i}` (§8.2, p.64): `X` lies in `Ω(z)` when every block `X_i` lies in
`Ω_0 = {g_0 = 1}` if `z_i = 0` and in `Ω_1 = {g_1 = 1}`, `g_1(X) = g_0(X̄)`, if `z_i = 1`. -/
def InFiber {n m : ℕ} (g0 : (Fin m → Bool) → Bool) (z : Fin n → Bool)
    (X : Fin n × Fin m → Bool) : Prop :=
  ∀ i : Fin n, if z i then g0 (fun j => !X (i, j)) = true else g0 (fun j => X (i, j)) = true

end SemAC02


