-- Prove2me | Definitions.Def_SemAC02_Supplement_IsPseudoRed
-- name    : SemAC02_Supplement_IsPseudoRed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:43:01.606443+00:00
-- url     : https://prove2.me/theorems/513c9aeb-5315-4e11-a2d9-787dc404f5ab
-- title:
--   Pseudo-reduction operators in B_n and in B_{F₀}, and rank(R_{≤k})
-- statement:
--   Let $F$ be a set of polynomials and $W$ an $\mathbb F_2$-vector space. A linear map $R:B^{\le B}\to W$ is a **degree-$B$ pseudo-reduction operator** for $F$ if
--
--   1. $R(f)=0$ for every $f\in F$, and
--   2. for every $p\in B^{\le B}$ and every variable $x_i$ with $\deg(x_ip)\le B$, $R(p)=0\Rightarrow R(x_ip)=0$.
--
--   Here $B^{\le B}$ is either $B_n^{\le B}$ (no background axioms) or $B_{F_0}^{\le B}$ for the $n$-division with parts $V_i$ of size $h$ and $F_0=\{xy:x\neq y\in V_i\}$; in $B_{F_0}$ the degree of an element is the least degree of a representative. $\operatorname{rank}(R_{\le k})$ is the dimension of the image of the restriction of $R$ to $B^{\le k}$.
--
--   These operators are the input of Theorems 4.4 and 4.5.
--
--   **Formalization Note** $B_n^{\le B}$ and $B_{F_0}^{\le B}$ are the published `SemAC02.Ble` and `SemAC02.BleF0` ($B_{F_0}$ as functions on $\Omega$, products with a variable pointwise).
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Definition 4.1, p.25 (PDF p.27); §4, pp.24, 26 (PDF pp.26, 28)

import Mathlib
import Definitions.Def_AC02Frege_ML
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_nDivision

namespace SemAC02.Supplement

open MvPolynomial

/-- A **degree-`B` pseudo-reduction operator** for `F` without background axioms (Alekseev–Gryaznov–
Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript
(STOC 2027 submission), Definition 4.1, p.25, with `F₀ = ∅`): a linear map
`R : B_n^{≤B} → W` into an `𝔽₂`-vector space `W` such that

* `R(f) = 0` for every `f ∈ F` (lying in `B_n^{≤B}`), and
* for every `p ∈ B_n^{≤B}` and every variable `x_i` with `deg(x_i p) ≤ B`,
  `R(p) = 0 ⟹ R(x_i p) = 0` (2).

**Formalization Note** `B_n^{≤B}` is the published `SemAC02.Ble` (multilinear polynomials of
degree `≤ B`); the product `x_i p` is taken in `B_n` (`AC02Frege.ML`), and `deg(x_i p) ≤ B` is
membership in `B_n^{≤B}`. -/
def IsPseudoRed {σ : Type} (F : Set (MvPolynomial σ (ZMod 2))) {B : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] (R : Ble σ B →ₗ[ZMod 2] W) : Prop :=
  (∀ f ∈ F, ∀ hf : f ∈ Ble σ B, R ⟨f, hf⟩ = 0) ∧
  (∀ (p : Ble σ B) (i : σ) (h : AC02Frege.ML (X i * (p : MvPolynomial σ (ZMod 2))) ∈ Ble σ B),
    R p = 0 → R ⟨_, h⟩ = 0)

/-- `rank(R_{≤k}) = dim im(R|_{B_n^{≤k}})` (p.25–26): the dimension of the image of the restriction
of `R : B_n^{≤B} → W` to `B_n^{≤k}`. -/
noncomputable def rankLe {σ : Type} {B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble σ B →ₗ[ZMod 2] W) (k : ℕ) : ℕ :=
  Module.finrank (ZMod 2) ((Submodule.comap (Ble σ B).subtype (Ble σ k)).map R)

/-- A **degree-`B` pseudo-reduction operator** for `F` in `B_{F₀}` for the `n`-division with parts
`V_i = {i} × [h]` and `F₀ = {xy : x ≠ y in the same part}` (Definition 4.1, p.25; §4, p.26):
a linear map `R : B_{F₀}^{≤B} → W` with `R(f̄) = 0` for every `f ∈ F` (with `f̄ ∈ B_{F₀}^{≤B}`)
and `R(p) = 0 ⟹ R(x p) = 0` for every `p ∈ B_{F₀}^{≤B}` and every variable `x` with
`deg(x p) ≤ B` in `B_{F₀}`.

**Formalization Note** `B_{F₀}` is identified with the functions on
`Ω = SemAC02.nDivOmega n h` (the published `restrOmega`, `BleF0`); multiplication by the
variable `x_v` is pointwise multiplication by the coordinate `v`. -/
def IsPseudoRedF0 {n h : ℕ} (F : Set (MvPolynomial (Fin n × Fin h) (ZMod 2))) {B : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] (R : BleF0 n h B →ₗ[ZMod 2] W) : Prop :=
  (∀ f ∈ F, ∀ hf : restrOmega n h f ∈ BleF0 n h B, R ⟨_, hf⟩ = 0) ∧
  (∀ (p : BleF0 n h B) (v : Fin n × Fin h)
    (hv : (fun x : nDivOmega n h => toF2 x.1 v * (p : nDivOmega n h → ZMod 2) x) ∈ BleF0 n h B),
    R p = 0 → R ⟨_, hv⟩ = 0)

/-- `rank(R_{≤k})` for `R : B_{F₀}^{≤B} → W` (p.26): the dimension of the image of the restriction
of `R` to `B_{F₀}^{≤k}`. -/
noncomputable def rankLeF0 {n h B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : BleF0 n h B →ₗ[ZMod 2] W) (k : ℕ) : ℕ :=
  Module.finrank (ZMod 2) ((Submodule.comap (BleF0 n h B).subtype (BleF0 n h k)).map R)

end SemAC02.Supplement


