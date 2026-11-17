-- Prove2me | Definitions.Def_ModFormPIR_Supplement_Lattice
-- name    : ModFormPIR_Supplement_Lattice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:47:05.083628+00:00
-- url     : https://prove2.me/theorems/029ef097-f92e-4ff1-8b32-8b8783ca00df
-- title:
--   Even lattices of determinant $\sqrt q$, coset costs $w_{\mathcal L}$, the exponents $\eta_{\mathcal L}$ and $\eta_q$, and the set $S_d$ of (32)
-- statement:
--   Let $r$ be an even positive integer and $B\in\mathbb R^{r\times r}$ of full rank. The lattice is $\mathcal L=B\mathbb Z^r$, its dual is $\mathcal L^*=\{x\in\mathbb R^r:\langle x,y\rangle\in\mathbb Z\ \forall y\in\mathcal L\}$, and $\det\mathcal L=|\det B|$ (Definition 11.1). $\mathcal L$ is **even** if $\langle x,x\rangle\in2\mathbb Z$ for all $x\in\mathcal L$ (Definition 11.2). For an odd prime $q$ and an even lattice of determinant $\sqrt q$, the group $\mathcal L^*/\mathcal L$ has order $q$.
--
--   For a coset $c\in\mathcal L^*/\mathcal L$, the **cost** is $w_{\mathcal L}(c)=\frac q2\min_{y\in c}\langle y,y\rangle$ (31), and
--
--   $$M_{\mathcal L}(t)=\sum_{c\in\mathcal L^*/\mathcal L}t^{w_{\mathcal L}(c)},\qquad \eta_{\mathcal L}=\frac1{\ln q}\inf_{0<t\le1}\Big(\ln M_{\mathcal L}(t)-\frac{r(q+1)}{24}\ln t\Big)$$
--
--   ((33), (34)). For a generator $a+\mathcal L$ of $\mathcal L^*/\mathcal L$ and $d>0$,
--
--   $$S_d=\bigcup_{u\in\mathbb Z_q\setminus\{0\}}\Big\{z\in\mathbb Z_q^d:\sum_{i=1}^dw_{\mathcal L}(uz_ia)\le\frac{r(q+1)}{24}d\Big\}\qquad(32).$$
--
--   Finally, for a prime $q\equiv3\pmod4$ and $K=(q+1)/4$,
--
--   $$\eta_q=\frac1{\ln q}\inf_{0<t\le1}\ln\Big(t^{-(q+1)/12}\Big(1+2\sum_{u=1}^{K}t^{u^2}+2\sum_{u=K+1}^{(q-1)/2}t^{u^2-qu+qK}\Big)\Big)\qquad(35).$$
--
--   These are the objects of Track 2: Theorem 11.9 builds a cone-delta function supported on $S_d$, $\eta_{\mathcal L}$ is the exponent of the resulting PIR scheme, and $\eta_q$ is its value for the rank-2 lattice of Definition 11.11.
--
--   **Formalization Note** $\mathbb R^r$ is `Fin r → ℝ` with the dot product. $\mathcal L^*/\mathcal L$ is the quotient of $\mathcal L^*$ by $\mathcal L\cap\mathcal L^*$, which is $\mathcal L$ for an even lattice. The minimum in (31) and the infima are real `sInf`s over nonempty sets bounded below by $0$ (the minimum is attained, Definition 11.5); $M_{\mathcal L}$ is a `finsum`, the finite sum since the quotient has $q$ elements. $w_{\mathcal L}(xa)$ for $x\in\mathbb Z_q$ is the cost of the coset of $x_{\mathrm{val}}\cdot a$, which does not depend on the representative of $x$.
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Definitions 11.1, 11.2, 11.5, 11.6 and (31), p.52 (PDF p.56); Theorem 11.9 (32), (33), (34), p.53 (PDF p.57); Corollary 11.13 (35), p.54 (PDF p.58); Main Theorem 5.3, p.21 (PDF p.25)

import Mathlib

open Matrix

set_option autoImplicit false

namespace ModFormPIR

namespace Supplement

/-!
# Even lattices of determinant `√q`, coset costs, the exponents `η_ℒ` and `η_q`, and the set `S_d` of (32)

Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027
submission (manuscript sha256 2442f3db…): Main Theorem 5.3, p.21 (PDF p.25); Definitions 11.1, 11.2, 11.5,
11.6 and (31), p.52 (PDF p.56); Theorem 11.9 with (32), (33), (34), p.53 (PDF p.57); Corollary 11.13 with
(35), p.54 (PDF p.58).

**Formalization Note.**
* `ℝ^r` is `Fin r → ℝ` with the dot product `⬝ᵥ`; `ℒ(B) = Bℤ^r` is the range of `z ↦ B z` on integer
  vectors; the dual `ℒ*` is `{x : ⟨x, y⟩ ∈ ℤ ∀ y ∈ ℒ}` (Definition 11.1, second form); `det ℒ = |det B|`.
* `ℒ*/ℒ` is the quotient of the additive group `ℒ*` by `ℒ ∩ ℒ*` (`addSubgroupOf`), which is `ℒ` itself for an
  even lattice (Proposition 11.3).
* `w_ℒ(c) = (q/2) min_{y ∈ c} ⟨y, y⟩` is written with `sInf`: the set is nonempty (a coset has a
  representative) and bounded below by `0`, and the minimum is attained (Definition 11.5), so `sInf` is the
  minimum. `M_ℒ(t) = ∑_{c ∈ ℒ*/ℒ} t^{w_ℒ(c)}` is a `finsum`; for an even lattice of determinant `√q` the
  quotient has `q` elements (Proposition 11.3), so this is the finite sum.
* `η_ℒ` and `η_q` are `(1/ln q) · inf_{0<t≤1}` of a real function, a real `sInf` over the image of `(0, 1]`.
  The function is `≥ 0` there (in `η_ℒ`, the zero coset has cost `0`, so `M_ℒ(t) ≥ 1`, and `−ln t ≥ 0`; in
  `η_q`, both factors are `≥ 1`), so the infimum is over a nonempty set bounded below.
* For `x ∈ ℤ_q` and `a ∈ ℒ*`, `w_ℒ(x a)` is the cost of the coset of `x.val • a`; it does not depend on the
  representative of `x`, since `q a ∈ ℒ` (`ℒ*/ℒ` has order `q`).
-/

variable {r : ℕ}

/-- Definition 11.1: the lattice `ℒ(B) = Bℤ^r ⊆ ℝ^r`. -/
def lattice (B : Matrix (Fin r) (Fin r) ℝ) : AddSubgroup (Fin r → ℝ) where
  carrier := {x | ∃ z : Fin r → ℤ, B *ᵥ (fun i => (z i : ℝ)) = x}
  add_mem' := by
    rintro _ _ ⟨z, rfl⟩ ⟨z', rfl⟩
    exact ⟨z + z', by rw [← Matrix.mulVec_add]; congr 1; funext i; simp⟩
  zero_mem' := ⟨0, by ext i; simp [Matrix.mulVec, dotProduct]⟩
  neg_mem' := by
    rintro _ ⟨z, rfl⟩
    exact ⟨-z, by rw [← Matrix.mulVec_neg]; congr 1; funext i; simp⟩

/-- Definition 11.1: the dual lattice `ℒ* = {x ∈ ℝ^r : ⟨x, y⟩ ∈ ℤ for all y ∈ ℒ}`. -/
def dual (L : AddSubgroup (Fin r → ℝ)) : AddSubgroup (Fin r → ℝ) where
  carrier := {x | ∀ y ∈ L, ∃ m : ℤ, x ⬝ᵥ y = m}
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨m, hm⟩ := ha y hy
    obtain ⟨m', hm'⟩ := hb y hy
    exact ⟨m + m', by rw [add_dotProduct, hm, hm']; push_cast; ring⟩
  zero_mem' := fun y _ => ⟨0, by simp⟩
  neg_mem' := by
    intro a ha y hy
    obtain ⟨m, hm⟩ := ha y hy
    exact ⟨-m, by rw [neg_dotProduct, hm]; push_cast; ring⟩

/-- Definition 11.2: `ℒ` is even, `⟨x, x⟩ ∈ 2ℤ` for all `x ∈ ℒ`. -/
def IsEvenLattice (L : AddSubgroup (Fin r → ℝ)) : Prop :=
  ∀ x ∈ L, ∃ m : ℤ, x ⬝ᵥ x = 2 * m

/-- §11.2: `ℒ(B) ⊆ ℝ^r` is an even lattice of determinant `√q`: `r` is an even positive integer and `B` has
full rank (Definition 11.1), `ℒ(B)` is even (Definition 11.2), and `|det B| = √q`. -/
def IsEvenLatticeDetSqrt (q : ℕ) (B : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  0 < r ∧ Even r ∧ B.det ≠ 0 ∧ IsEvenLattice (lattice B) ∧ |B.det| = Real.sqrt q

/-- The discriminant group `ℒ*/ℒ`. -/
abbrev DiscGroup (B : Matrix (Fin r) (Fin r) ℝ) : Type :=
  ↥(dual (lattice B)) ⧸ (lattice B).addSubgroupOf (dual (lattice B))

/-- (31): the coset cost `w_ℒ(c) = (q/2) min_{y ∈ c} ⟨y, y⟩`. -/
noncomputable def latCost (q : ℕ) (B : Matrix (Fin r) (Fin r) ℝ) (c : DiscGroup B) : ℝ :=
  ((q : ℝ) / 2) * sInf {s : ℝ | ∃ y : ↥(dual (lattice B)),
    (QuotientAddGroup.mk y : DiscGroup B) = c ∧ s = (y : Fin r → ℝ) ⬝ᵥ (y : Fin r → ℝ)}

/-- (33): `M_ℒ(t) = ∑_{c ∈ ℒ*/ℒ} t^{w_ℒ(c)}`. -/
noncomputable def genML (q : ℕ) (B : Matrix (Fin r) (Fin r) ℝ) (t : ℝ) : ℝ :=
  ∑ᶠ c : DiscGroup B, t ^ latCost q B c

/-- (34), Main Theorem 5.3: `η_ℒ = (1/ln q) inf_{0<t≤1} (ln M_ℒ(t) − (r(q+1)/24) ln t)`. -/
noncomputable def etaL (q : ℕ) (B : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  (1 / Real.log q) *
    sInf ((fun t : ℝ => Real.log (genML q B t) - ((r : ℝ) * ((q : ℝ) + 1) / 24) * Real.log t) ''
      Set.Ioc 0 1)

/-- Definition 11.6: `a + ℒ` generates `ℒ*/ℒ`. -/
def IsCosetGenerator (B : Matrix (Fin r) (Fin r) ℝ) (a : ↥(dual (lattice B))) : Prop :=
  ∀ c : DiscGroup B, ∃ k : ℤ, c = k • (QuotientAddGroup.mk a : DiscGroup B)

/-- (32): `S_d = ⋃_{u ∈ ℤ_q ∖ {0}} {z ∈ ℤ_q^d : ∑_{i=1}^d w_ℒ(u z_i a) ≤ (r(q+1)/24) d}`. -/
def Sd (q : ℕ) (B : Matrix (Fin r) (Fin r) ℝ) (a : ↥(dual (lattice B))) (d : ℕ) :
    Set (Fin d → ZMod q) :=
  {z | ∃ u : ZMod q, u ≠ 0 ∧
    ∑ i : Fin d, latCost q B (QuotientAddGroup.mk ((u * z i).val • a)) ≤
      ((r : ℝ) * ((q : ℝ) + 1) / 24) * d}

/-- (35): for a prime `q ≡ 3 (mod 4)` and `K = (q+1)/4`,
`η_q = (1/ln q) inf_{0<t≤1} ln(t^{−(q+1)/12} (1 + 2∑_{u=1}^{K} t^{u²} + 2∑_{u=K+1}^{(q−1)/2} t^{u²−qu+qK}))`. -/
noncomputable def etaQ (q : ℕ) : ℝ :=
  (1 / Real.log q) *
    sInf ((fun t : ℝ => Real.log (t ^ (-((q : ℝ) + 1) / 12) *
      (1 + 2 * ∑ u ∈ Finset.Icc 1 ((q + 1) / 4), t ^ (u ^ 2) +
        2 * ∑ u ∈ Finset.Icc ((q + 1) / 4 + 1) ((q - 1) / 2),
          t ^ ((u : ℝ) ^ 2 - (q : ℝ) * u + (q : ℝ) * (((q + 1) / 4 : ℕ) : ℝ))))) '' Set.Ioc 0 1)

end Supplement

end ModFormPIR


