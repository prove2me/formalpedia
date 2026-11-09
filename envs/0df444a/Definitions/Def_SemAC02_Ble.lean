-- Prove2me | Definitions.Def_SemAC02_Ble
-- name    : SemAC02_Ble
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:22.535146+00:00
-- url     : https://prove2.me/theorems/526af2fc-c147-4534-a541-cdcfc12b8746
-- title:
--   The space $\mathcal B_n^{\le k}$, products in $\mathcal B_n$, $f\mathcal B_n^{\le k}$ and $H_n(k)$
-- statement:
--   Let $\mathcal B_n=\mathbb F_2[x_1,\dots,x_n]/\langle x_i^2-x_i\rangle$. Every element has a unique multilinear representative, and its **degree** is the degree of that representative; $\mathcal B_n$ is identified with the functions $\{0,1\}^n\to\mathbb F_2$.
--
--   * $\mathcal B_n^{\le k}$ is the subspace of elements of degree at most $k$, spanned by the monomials $x_A=\prod_{v\in A}x_v$ with $|A|\le k$.
--   * For $f\in\mathcal B_n$, multiplication by $f$ is $p\mapsto fp$ computed in $\mathcal B_n$, and $f\mathcal B_n^{\le k}=\{fp:p\in\mathcal B_n^{\le k}\}$.
--   * $$H_n(k)=\dim\mathcal B_n^{\le k}=\sum_{j=0}^{\min(k,n)}\binom nj.$$
--
--   **Formalization Note** Elements of $\mathcal B_n$ are multilinear polynomials in `MvPolynomial σ (ZMod 2)`; the product is `ML (f * p)` with the published multilinearisation `AC02Frege.ML`. `toF2` sends a Boolean assignment to the corresponding point of $\mathbb F_2^n$.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §2.1, p.15; §4, p.24; Definition 4.15, p.36, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_AC02Frege_ML

namespace SemAC02

open MvPolynomial

/-- The polynomials of degree at most `k` in `B_n` (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–
Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission),
p.15 and §4, p.24): `B_n^{≤k}`, the span of the multilinear monomials `x_A`, `|A| ≤ k`.

**Formalization Note** `B_n` is represented by multilinear polynomials in
`MvPolynomial σ (ZMod 2)` (each element of `B_n` has a unique multilinear representative, whose
degree is the degree of the element, p.15). `B_n^{≤k}` is the submodule spanned by the
monomials `AC02Frege.xMon A` with `A.card ≤ k`; it consists exactly of the multilinear
polynomials of total degree at most `k`. -/
noncomputable def Ble (σ : Type) (k : ℕ) : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  Submodule.span (ZMod 2) (AC02Frege.xMon '' {A : Finset σ | A.card ≤ k})

/-- Multiplication by `f` in `B_n`: `p ↦ ML(f · p)`, the multilinear representative of the
product of the functions `f` and `p`. -/
noncomputable def mulML {σ : Type} (f : MvPolynomial σ (ZMod 2)) :
    MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2) :=
  AC02Frege.ML ∘ₗ LinearMap.mulLeft (ZMod 2) f

/-- The subspace `f B_n^{≤k} = {f p : p ∈ B_n^{≤k}}` of `B_n` (Definition 4.15, p.36). -/
noncomputable def multSpace {σ : Type} (f : MvPolynomial σ (ZMod 2)) (k : ℕ) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  (Ble σ k).map (mulML f)

/-- `H_n(k) = dim B_n^{≤k} = ∑_{j=0}^{min(k,n)} C(n, j)` (p.6, p.24). -/
def Hn (n k : ℕ) : ℕ := ∑ j ∈ Finset.range (min k n + 1), n.choose j

/-- The `𝔽₂`-valued point of the cube corresponding to a Boolean assignment (`true ↦ 1`). -/
def toF2 {V : Type} (x : V → Bool) : V → ZMod 2 := fun v => if x v then 1 else 0

end SemAC02


