-- Prove2me | Definitions.Def_SemAC02_IsRelPseudoRed
-- name    : SemAC02_IsRelPseudoRed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:28:23.706324+00:00
-- url     : https://prove2.me/theorems/e5b31402-bfe1-44ec-89f5-e74537a21661
-- title:
--   $f$-relative pseudo-reduction operators
-- statement:
--   Let $S\subseteq\mathcal B_n$, $0\ne f\in\mathcal B_n$ and $k\ge0$. A **degree-$k$ $f$-relative pseudo-reduction for $S$** is a linear map $R_f:f\mathcal B_n^{\le k}\to W$ into an $\mathbb F_2$-vector space $W$ such that
--
--   1. $R_f(fa)=0$ for every $a\in S$ with $fa\in f\mathcal B_n^{\le k}$;
--   2. for every variable $x$ and every $u\in f\mathcal B_n^{\le k}$ with $xu\in f\mathcal B_n^{\le k}$, if $R_f(u)=0$ then $R_f(xu)=0$.
--
--   Such an operator annihilates every line of a PC derivation from $fS$ that stays inside $f\mathcal B_n^{\le k}$; a non-zero one certifies that $f$ has no such derivation.
--
--   **Formalization Note** Products are in $\mathcal B_n$. `HasNonzeroRelPseudoRed S f k` asserts a non-zero such operator into some $W$ (a type in the lowest universe, which loses nothing: the image of the operator can always be used). The hypothesis $f\ne0$ is stated where the notion is used.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Definition 4.15, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_AC02Frege_ML
import Definitions.Def_SemAC02_Ble

namespace SemAC02

open MvPolynomial

/-- A **degree-`k` `f`-relative pseudo-reduction** for `S` (Alekseev–Gryaznov–Itsykson–Pitassi–
Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027
submission), Definition 4.15, p.36): a linear map `R_f : f B_n^{≤k} → W` such that

* `R_f(f a) = 0` for every `a ∈ S` with `f a ∈ f B_n^{≤k}`;
* for every variable `x` and every `u ∈ f B_n^{≤k}` with `x u ∈ f B_n^{≤k}`, if `R_f(u) = 0` then
  `R_f(x u) = 0`.

**Formalization Note** Products are taken in `B_n` (`mulML`, `ML (X i * u)`). The paper's
standing assumption `f ≠ 0` is a hypothesis wherever the notion is used. -/
def IsRelPseudoRed {σ : Type} (S : Set (MvPolynomial σ (ZMod 2))) (f : MvPolynomial σ (ZMod 2))
    (k : ℕ) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : multSpace f k →ₗ[ZMod 2] W) : Prop :=
  (∀ a ∈ S, ∀ h : mulML f a ∈ multSpace f k, R ⟨mulML f a, h⟩ = 0) ∧
  (∀ (i : σ) (u : multSpace f k) (h : AC02Frege.ML (X i * (u : MvPolynomial σ (ZMod 2))) ∈
      multSpace f k), R u = 0 → R ⟨_, h⟩ = 0)

/-- There is a **non-zero** degree-`k` `f`-relative pseudo-reduction for `S`, into some
`𝔽₂`-vector space `W`. -/
def HasNonzeroRelPseudoRed {σ : Type} (S : Set (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) (k : ℕ) : Prop :=
  ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (R : multSpace f k →ₗ[ZMod 2] W),
    R ≠ 0 ∧ IsRelPseudoRed S f k R

end SemAC02


